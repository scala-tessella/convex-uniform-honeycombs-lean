/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# Periodization: the constants, the box representative, the field identification, box rigidity

Four pieces of Section 7.1 of the paper that are arithmetic or set theory once the geometry is
named.

* **The constants** (Remark 7.2): the coverage hypothesis (C), `R_per ≥ covB + max|τ| + 3/2`,
  supports the three lines of the table — `covB + max|τ| < R_per`, consumed by the lattice
  transport of the coherence lemma; `covB + 1 ≤ R_per − 1/2`, the local structure and the
  generator-equivariance step; and `R_per − 1/2 + 1 < R_per + 8/5`, the slack.
* **The box representative** (condition (P)): rounding half up, `n(c) = ⌊c + 1/2⌋`, leaves a
  remainder `c − n(c)` in `[-1/2, 1/2)`, and the remainder is the same for `c` and `c + k` with
  `k` an integer — coordinatewise, the map `ρ` of the theorem is well defined and constant on
  lattice orbits. (The seam lemma of earlier versions — two coordinates of the closed box with an
  integer difference differ by `-1`, `0` or `1` — is kept for the record; the proof no longer
  needs it.)
* **The field identification** (the step "the development field on the ball"): given the two
  clauses of (P) — every entry within the ball is the translate of a representative carrying the
  translated star, and every translate of a representative within the ball is an entry carrying
  the translated star — the entries within the ball and the vertices of the periodization within
  the ball coincide, and the developed star field is the periodized one there.
* **Box rigidity** (Lemma 7.4): two lattice-periodic honeycombs agreeing on a fundamental box are
  equal, once "the cells at the box vertices" reach every cell up to the lattice.

## Main results

* `ConvexUniformHoneycombs.constants_table` (Remark 7.2).
* `ConvexUniformHoneycombs.remainder_mem`, `ConvexUniformHoneycombs.remainder_add_int` (the box
  representative of condition (P)).
* `ConvexUniformHoneycombs.entries_eq_periodization_on_ball` (the field identification).
* `ConvexUniformHoneycombs.eq_of_periodic_of_agree_on_box` (Lemma 7.4).
-/

namespace ConvexUniformHoneycombs

/-- **Remark 7.2, the constants.** From (C) with `max|τ| ≥ 0`: `covB + max|τ| < R_per`;
`covB + 1 ≤ R_per - 1/2`; and `R_per - 1/2 + 1 < R_per + 8/5`. -/
theorem constants_table {covB maxT rper : ℝ} (hT : 0 ≤ maxT) (hC : covB + maxT + 3 / 2 ≤ rper) :
    covB + maxT < rper ∧ covB + 1 ≤ rper - 1 / 2 ∧ rper - 1 / 2 + 1 < rper + 8 / 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

section BoxRepresentative

/-- Rounding half up: the integer `⌊c + 1/2⌋`. Coordinatewise, the lattice vector `λ(p)` of
condition (P). -/
noncomputable def roundHalfUp (c : ℝ) : ℤ := ⌊c + 1 / 2⌋

/-- **The remainder lies in the half-open box.** `c - ⌊c + 1/2⌋ ∈ [-1/2, 1/2)`. -/
theorem remainder_mem (c : ℝ) : -1 / 2 ≤ c - roundHalfUp c ∧ c - roundHalfUp c < 1 / 2 := by
  unfold roundHalfUp
  have h₁ := Int.floor_le (c + 1 / 2)
  have h₂ := Int.lt_floor_add_one (c + 1 / 2)
  constructor <;> linarith

theorem roundHalfUp_add_int (c : ℝ) (k : ℤ) : roundHalfUp (c + k) = roundHalfUp c + k := by
  unfold roundHalfUp
  rw [show c + k + 1 / 2 = c + 1 / 2 + k by ring, Int.floor_add_intCast]

/-- **The representative is constant on lattice orbits.** Shifting a coordinate by an integer
does not change its remainder, so `ρ(p + λ) = ρ(p)` for every lattice vector `λ`. -/
theorem remainder_add_int (c : ℝ) (k : ℤ) :
    (c + k) - roundHalfUp (c + k) = c - roundHalfUp c := by
  rw [roundHalfUp_add_int]; push_cast; ring

/-- The seam lemma of earlier versions, kept for the record: two coordinates in `[-1/2, 1/2]`
with an integer difference differ by `-1`, `0` or `1`. -/
theorem seam_coefficient {x y : ℝ} (n : ℤ) (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2)
    (h : x - y = n) : n = -1 ∨ n = 0 ∨ n = 1 := by
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  obtain ⟨hy₁, hy₂⟩ := abs_le.mp hy
  have h₁ : (n : ℝ) ≤ 1 := by rw [← h]; linarith
  have h₂ : (-1 : ℝ) ≤ n := by rw [← h]; linarith
  have h₁' : n ≤ 1 := by exact_mod_cast h₁
  have h₂' : -1 ≤ n := by exact_mod_cast h₂
  omega

end BoxRepresentative

section FieldIdentification

variable {L X S : Type*} [AddGroup L] [AddAction L X] [AddAction L S]

/-- **The field identification.** Positions `X` and stars `S` carry the lattice action; `E` is the
set of ball entries, `B` the ball, `V₀` the box representatives, `σ` the developed star field. The
two clauses of condition (P): `down`, every entry within the ball is the translate of a
representative carrying the translated star; `up`, every translate of a representative within the
ball is an entry carrying the translated star. Then the entries within the ball are exactly the
vertices of the periodization `Λ + V₀` within the ball — and by `up` the developed star at each of
them is the periodized one, `σ (l +ᵥ v) = l +ᵥ σ v`. -/
theorem entries_eq_periodization_on_ball (E B V₀ : Set X) (σ : X → S)
    (down : ∀ p ∈ E ∩ B, ∃ v ∈ V₀, ∃ l : L, p = l +ᵥ v ∧ σ p = l +ᵥ σ v)
    (up : ∀ v ∈ V₀, ∀ l : L, l +ᵥ v ∈ B → l +ᵥ v ∈ E ∧ σ (l +ᵥ v) = l +ᵥ σ v) :
    E ∩ B = {p | ∃ v ∈ V₀, ∃ l : L, p = l +ᵥ v} ∩ B := by
  ext p
  constructor
  · rintro ⟨hE, hB⟩
    obtain ⟨v, hv, l, rfl, -⟩ := down p ⟨hE, hB⟩
    exact ⟨⟨v, hv, l, rfl⟩, hB⟩
  · rintro ⟨⟨v, hv, l, rfl⟩, hB⟩
    exact ⟨(up v hv l hB).1, hB⟩

end FieldIdentification

section BoxRigidity

variable {L C : Type*} [AddGroup L] [AddAction L C]

/-- **Lemma 7.4, box rigidity.** Honeycombs are sets of cells `H₁ H₂` invariant under the lattice
`L`; `B` is the set of cells at the box vertices, which reaches every cell up to a lattice
translate. If `H₁` and `H₂` agree on `B`, they are equal. -/
theorem eq_of_periodic_of_agree_on_box {H₁ H₂ B : Set C}
    (h₁ : ∀ (l : L) (c : C), c ∈ H₁ → l +ᵥ c ∈ H₁) (h₂ : ∀ (l : L) (c : C), c ∈ H₂ → l +ᵥ c ∈ H₂)
    (hbox : ∀ c : C, ∃ l : L, l +ᵥ c ∈ B) (hagree : ∀ c ∈ B, c ∈ H₁ ↔ c ∈ H₂) : H₁ = H₂ := by
  -- invariance is an equivalence: translate back by `-l`
  have inv₁ : ∀ (l : L) (c : C), l +ᵥ c ∈ H₁ → c ∈ H₁ := fun l c hc => by
    simpa using h₁ (-l) (l +ᵥ c) hc
  have inv₂ : ∀ (l : L) (c : C), l +ᵥ c ∈ H₂ → c ∈ H₂ := fun l c hc => by
    simpa using h₂ (-l) (l +ᵥ c) hc
  ext c
  obtain ⟨l, hl⟩ := hbox c
  constructor
  · intro hc
    exact inv₂ l c ((hagree _ hl).mp (h₁ l c hc))
  · intro hc
    exact inv₁ l c ((hagree _ hl).mpr (h₂ l c hc))

end BoxRigidity

end ConvexUniformHoneycombs
