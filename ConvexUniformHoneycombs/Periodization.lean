/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# Periodization: the constants, the seam and box rigidity

Three pieces of Section 6.1 of the paper that are arithmetic or set theory once the geometry is
named.

* **The constants** (Remark 6.2): the coverage hypothesis (C), `R_per ≥ covB + max|τ| + 3/2`,
  supports the three inequalities the proof consumes — the seam walks, the local structure with
  its half-unit margin, and the generator equivariance with its `2.6 = 1 + 1.6` reach against the
  `1.6` slack.
* **The seam** (the first step of the proof): two points of the closed fundamental box congruent
  modulo the lattice differ by a `{-1, 0, 1}`-combination of the basis. Coordinatewise: two
  reals of absolute value at most `1/2` whose difference is an integer differ by `-1`, `0` or `1`.
* **Box rigidity** (Lemma 6.5): two lattice-periodic honeycombs agreeing on a fundamental box are
  equal, once "the cells at the box vertices" reach every cell up to the lattice.

## Main results

* `ConvexUniformHoneycombs.constants_chain` (Remark 6.2).
* `ConvexUniformHoneycombs.seam_coefficient` (the seam step).
* `ConvexUniformHoneycombs.eq_of_periodic_of_agree_on_box` (Lemma 6.5).
-/

namespace ConvexUniformHoneycombs

/-- **Remark 6.2, the constants.** From (C) with `max|τ| ≥ 0`: `covB + max|τ| < R_per`;
`covB + 1 ≤ R_per - 1/2`; and `covB + max|τ| + 13/5 ≤ R_per + 11/10 < R_per + 8/5`. -/
theorem constants_chain {covB maxT rper : ℝ} (hT : 0 ≤ maxT) (hC : covB + maxT + 3 / 2 ≤ rper) :
    covB + maxT < rper ∧ covB + 1 ≤ rper - 1 / 2 ∧
      covB + maxT + 13 / 5 ≤ rper + 11 / 10 ∧ rper + 11 / 10 < rper + 8 / 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The seam step.** Two coordinates in `[-1/2, 1/2]` with an integer difference differ by
`-1`, `0` or `1`. -/
theorem seam_coefficient {x y : ℝ} (n : ℤ) (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2)
    (h : x - y = n) : n = -1 ∨ n = 0 ∨ n = 1 := by
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  obtain ⟨hy₁, hy₂⟩ := abs_le.mp hy
  have h₁ : (n : ℝ) ≤ 1 := by rw [← h]; linarith
  have h₂ : (-1 : ℝ) ≤ n := by rw [← h]; linarith
  have h₁' : n ≤ 1 := by exact_mod_cast h₁
  have h₂' : -1 ≤ n := by exact_mod_cast h₂
  omega

section BoxRigidity

variable {L C : Type*} [AddGroup L] [AddAction L C]

/-- **Lemma 6.5, box rigidity.** Honeycombs are sets of cells `H₁ H₂` invariant under the lattice
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
