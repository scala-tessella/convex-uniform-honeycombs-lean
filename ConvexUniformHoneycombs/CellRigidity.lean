/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# Cell rigidity: the Euclidean core

The cell rigidity lemma of the paper (Section 6.1): two placed core cells of the same type that
contain the same edge with the same two face germs there, carrying the same roles, are equal. Its
proof combines three finite facts about the thirteen core cells — certified in the artifact,
`core-cells.txt` — with one piece of Euclidean geometry, which this file proves: **an isometry that
preserves a segment and two distinct planes through it, each with its side, is the identity or the
reflection in the perpendicular bisector plane of the segment.**

In linear form, about the midpoint of the segment: `d` is the direction of the segment; `p₁, p₂` are
the two interior directions — in the two planes, perpendicular to `d`, pointing into the faces —
nonzero and spanning the space together with `d`; and `L` is a linear isometry with `L d = d` (the
endpoints fixed) or `L d = -d` (the endpoints swapped) which maps each `pᵢ` into its plane
`span {d, pᵢ}` on the side of `pᵢ`, that is `⟪L pᵢ, pᵢ⟫ > 0`. Then `L` is the identity, or the
reflection `v ↦ v - (2 / ⟪d, d⟫ * ⟪d, v⟫) • d`.

## Main results

* `ConvexUniformHoneycombs.interior_fixed`: the key step — a map sending `p` into its plane,
  orthogonally to `d`, with the norm of `p` and on the side of `p`, fixes `p`.
* `ConvexUniformHoneycombs.eq_of_fixes_three`: a linear map fixing three spanning vectors is the
  identity.
* `ConvexUniformHoneycombs.bisectorReflection`, with `bisectorReflection_apply`,
  `bisectorReflection_self`, `bisectorReflection_of_orthogonal`, `bisectorReflection_involutive`:
  the reflection in the plane perpendicular to `d`.
* `ConvexUniformHoneycombs.wedge_isometry`: the dichotomy.
-/

namespace ConvexUniformHoneycombs

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The key step.** If `f p` lies in the plane `span {d, p}`, is orthogonal to `d`, has the norm
of `p`, and points to the side of `p` (`⟪f p, p⟫ > 0`), then `f p = p`. -/
theorem interior_fixed {f : V → V} {d p : V} (hd : d ≠ 0) (hp : p ≠ 0) (hpd : ⟪p, d⟫ = 0)
    (hfd : ⟪f p, d⟫ = 0) (hfn : ‖f p‖ = ‖p‖) (hplane : ∃ a b : ℝ, f p = a • d + b • p)
    (hside : 0 < ⟪f p, p⟫) : f p = p := by
  obtain ⟨a, b, hab⟩ := hplane
  have hdd : 0 < ⟪d, d⟫ := real_inner_self_pos.mpr hd
  have hpp : 0 < ⟪p, p⟫ := real_inner_self_pos.mpr hp
  -- the `d`-component vanishes
  have ha : a = 0 := by
    have h : ⟪f p, d⟫ = a * ⟪d, d⟫ + b * ⟪p, d⟫ := by
      rw [hab, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [hfd, hpd, mul_zero, add_zero] at h
    rcases mul_eq_zero.mp h.symm with h0 | h0
    · exact h0
    · exact absurd h0 hdd.ne'
  subst ha
  rw [zero_smul, zero_add] at hab
  -- the `p`-component has absolute value one
  have hb : |b| = 1 := by
    have h : ‖f p‖ = |b| * ‖p‖ := by rw [hab, norm_smul, Real.norm_eq_abs]
    rw [hfn] at h
    have h2 : (|b| - 1) * ‖p‖ = 0 := by rw [sub_mul, one_mul]; linarith
    rcases mul_eq_zero.mp h2 with h0 | h0
    · linarith
    · exact absurd h0 (norm_ne_zero_iff.mpr hp)
  -- and is positive: the side
  have hbpos : 0 < b := by
    have h : ⟪f p, p⟫ = b * ⟪p, p⟫ := by rw [hab, real_inner_smul_left]
    rw [h] at hside
    by_contra hneg
    have hneg : b ≤ 0 := not_lt.mp hneg
    have : b * ⟪p, p⟫ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hpp.le
    linarith
  have hb1 : b = 1 := by rw [abs_of_pos hbpos] at hb; exact hb
  rw [hab, hb1, one_smul]

/-- A map that is linear on triples and fixes three spanning vectors is the identity. -/
theorem eq_of_fixes_three {f : V → V}
    (hf : ∀ (a b c : ℝ) (x y z : V), f (a • x + b • y + c • z) = a • f x + b • f y + c • f z)
    {d p₁ p₂ : V} (hd : f d = d) (h₁ : f p₁ = p₁) (h₂ : f p₂ = p₂)
    (hspan : ∀ v : V, ∃ a b c : ℝ, v = a • d + b • p₁ + c • p₂) (v : V) : f v = v := by
  obtain ⟨a, b, c, rfl⟩ := hspan v
  rw [hf, hd, h₁, h₂]

/-- The reflection in the plane perpendicular to `d` — the perpendicular bisector plane of a segment
of direction `d` centred at the origin. -/
noncomputable def bisectorReflection (d : V) : V →ₗ[ℝ] V :=
  LinearMap.id - (2 / ⟪d, d⟫) • (innerₛₗ ℝ d).smulRight d

theorem bisectorReflection_apply (d v : V) :
    bisectorReflection d v = v - (2 / ⟪d, d⟫ * ⟪d, v⟫) • d := by
  simp only [bisectorReflection, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, innerₛₗ_apply_apply, smul_smul]

theorem bisectorReflection_self {d : V} (hd : d ≠ 0) : bisectorReflection d d = -d := by
  rw [bisectorReflection_apply, div_mul_cancel₀ _ (inner_self_ne_zero.mpr hd), two_smul]
  abel

theorem bisectorReflection_of_orthogonal {d w : V} (h : ⟪d, w⟫ = 0) :
    bisectorReflection d w = w := by
  rw [bisectorReflection_apply, h, mul_zero, zero_smul, sub_zero]

theorem bisectorReflection_involutive {d : V} (hd : d ≠ 0) (v : V) :
    bisectorReflection d (bisectorReflection d v) = v := by
  have hdd : ⟪d, d⟫ ≠ 0 := inner_self_ne_zero.mpr hd
  rw [bisectorReflection_apply, bisectorReflection_apply, inner_sub_right, real_inner_smul_right]
  have h : 2 / ⟪d, d⟫ * (⟪d, v⟫ - 2 / ⟪d, d⟫ * ⟪d, v⟫ * ⟪d, d⟫) = -(2 / ⟪d, d⟫ * ⟪d, v⟫) := by
    field_simp
    ring
  rw [h, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- **The dichotomy.** A linear isometry `L` that fixes or reverses the direction `d` of a
segment and maps each of two interior directions `p₁, p₂` — perpendicular to `d`, spanning the
space with it — into its own plane `span {d, pᵢ}` on its own side is the identity or the
reflection in the plane perpendicular to `d`. -/
theorem wedge_isometry (L : V →ₗᵢ[ℝ] V) {d p₁ p₂ : V} (hd : d ≠ 0) (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hp₁d : ⟪p₁, d⟫ = 0) (hp₂d : ⟪p₂, d⟫ = 0) (hedge : L d = d ∨ L d = -d)
    (hplane₁ : ∃ a b : ℝ, L p₁ = a • d + b • p₁) (hside₁ : 0 < ⟪L p₁, p₁⟫)
    (hplane₂ : ∃ a b : ℝ, L p₂ = a • d + b • p₂) (hside₂ : 0 < ⟪L p₂, p₂⟫)
    (hspan : ∀ v : V, ∃ a b c : ℝ, v = a • d + b • p₁ + c • p₂) :
    (∀ v, L v = v) ∨ (∀ v, L v = bisectorReflection d v) := by
  rcases hedge with hLd | hLd
  · -- the endpoints fixed: `L` fixes `d`, `p₁`, `p₂`
    left
    have h₁ : L p₁ = p₁ :=
      interior_fixed hd hp₁ hp₁d (by rw [← hLd, L.inner_map_map, hp₁d])
        (L.norm_map p₁) hplane₁ hside₁
    have h₂ : L p₂ = p₂ :=
      interior_fixed hd hp₂ hp₂d (by rw [← hLd, L.inner_map_map, hp₂d])
        (L.norm_map p₂) hplane₂ hside₂
    exact eq_of_fixes_three (fun a b c x y z => by simp [map_add, map_smul]) hLd h₁ h₂ hspan
  · -- the endpoints swapped: the bisector reflection composed with `L` fixes `d`, `p₁`, `p₂`
    right
    have hLp₁d : ⟪L p₁, d⟫ = 0 := by
      have h : ⟪L p₁, L d⟫ = ⟪p₁, d⟫ := L.inner_map_map p₁ d
      rw [hLd, inner_neg_right, hp₁d] at h
      linarith
    have hLp₂d : ⟪L p₂, d⟫ = 0 := by
      have h : ⟪L p₂, L d⟫ = ⟪p₂, d⟫ := L.inner_map_map p₂ d
      rw [hLd, inner_neg_right, hp₂d] at h
      linarith
    set ρ := bisectorReflection d with hρ
    have hρ₁ : ρ (L p₁) = L p₁ :=
      bisectorReflection_of_orthogonal (by rw [real_inner_comm]; exact hLp₁d)
    have hρ₂ : ρ (L p₂) = L p₂ :=
      bisectorReflection_of_orthogonal (by rw [real_inner_comm]; exact hLp₂d)
    have hρd : ρ (L d) = d := by rw [hLd, map_neg, bisectorReflection_self hd, neg_neg]
    have h₁ : ρ (L p₁) = p₁ :=
      interior_fixed (f := fun v => ρ (L v)) hd hp₁ hp₁d
        (by show ⟪ρ (L p₁), d⟫ = 0; rw [hρ₁]; exact hLp₁d)
        (by show ‖ρ (L p₁)‖ = ‖p₁‖; rw [hρ₁]; exact L.norm_map p₁)
        (by show ∃ a b : ℝ, ρ (L p₁) = a • d + b • p₁; rw [hρ₁]; exact hplane₁)
        (by show 0 < ⟪ρ (L p₁), p₁⟫; rw [hρ₁]; exact hside₁)
    have h₂ : ρ (L p₂) = p₂ :=
      interior_fixed (f := fun v => ρ (L v)) hd hp₂ hp₂d
        (by show ⟪ρ (L p₂), d⟫ = 0; rw [hρ₂]; exact hLp₂d)
        (by show ‖ρ (L p₂)‖ = ‖p₂‖; rw [hρ₂]; exact L.norm_map p₂)
        (by show ∃ a b : ℝ, ρ (L p₂) = a • d + b • p₂; rw [hρ₂]; exact hplane₂)
        (by show 0 < ⟪ρ (L p₂), p₂⟫; rw [hρ₂]; exact hside₂)
    have hfix : ∀ v, ρ (L v) = v :=
      eq_of_fixes_three (f := fun v => ρ (L v)) (fun a b c x y z => by simp [map_add, map_smul])
        hρd h₁ h₂ hspan
    intro v
    calc L v = ρ (ρ (L v)) := (bisectorReflection_involutive hd (L v)).symm
      _ = ρ v := by rw [hfix v]

end ConvexUniformHoneycombs
