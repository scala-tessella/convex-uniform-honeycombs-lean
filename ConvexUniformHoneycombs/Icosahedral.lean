/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# Identity I2: the pentagon-family edge figure

Identity 4.3 of the paper: with `θ₁` the dodecahedral dihedral, `θ₂` the base–lateral dihedral
of the pentagonal antiprism and `θ₃` the icosidodecahedral dihedral,
`θ₁ + θ₂ + θ₃ = 360°` exactly. The three cosines are `-√r₁`, `-√r₂`, `-√r₃` with
`r₁ = 1/5`, `r₂ = (5 - 2√5)/15`, `r₃ = (5 + 2√5)/15`, certified on exact `ℚ(√5)` models in the
artifact; they enter here as hypotheses together with the obtuseness of the three angles. The
argument is the paper's: `cos (θ₂ + θ₃) = √(r₂ r₃) - √((1-r₂)(1-r₃)) = √(1/45) - √(16/45) =
-√(1/5) = cos θ₁`, and since `2π - (θ₂ + θ₃)` and `θ₁` both lie in `[0, π]`, where the cosine is
injective, `θ₂ + θ₃ = 2π - θ₁`. No interval enters.

## Main result

* `ConvexUniformHoneycombs.identity_I2`.
-/

namespace ConvexUniformHoneycombs

open Real

/-- The radicands of Identity I2. -/
noncomputable def r₂ : ℝ := (5 - 2 * √5) / 15
noncomputable def r₃ : ℝ := (5 + 2 * √5) / 15

theorem sqrt_five_sq : (√5 : ℝ) ^ 2 = 5 := sq_sqrt (by norm_num)

theorem sqrt_five_lt : (√5 : ℝ) < 5 / 2 := by
  rw [show (5 / 2 : ℝ) = √((5 / 2) ^ 2) by rw [sqrt_sq (by norm_num)]]
  exact sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem r₂_pos : 0 < r₂ := by unfold r₂; linarith [sqrt_five_lt]
theorem r₃_pos : 0 < r₃ := by unfold r₃; positivity
theorem r₂_lt_one : r₂ < 1 := by unfold r₂; linarith [sqrt_nonneg (5 : ℝ)]
theorem r₃_lt_one : r₃ < 1 := by unfold r₃; linarith [sqrt_five_lt]

/-- The radical products of the paper: `r₂ r₃ = 1/45` and `(1 - r₂)(1 - r₃) = 16/45`. -/
theorem r₂_mul_r₃ : r₂ * r₃ = 1 / 45 := by
  unfold r₂ r₃
  linear_combination (-4 / 225 : ℝ) * sqrt_five_sq

theorem one_sub_r₂_mul : (1 - r₂) * (1 - r₃) = 16 / 45 := by
  unfold r₂ r₃
  linear_combination (-4 / 225 : ℝ) * sqrt_five_sq

/-- The sine of an obtuse angle with cosine `-√r`, `0 ≤ r ≤ 1`: `√(1 - r)`. -/
theorem sin_of_cos_neg_sqrt {θ r : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ π) (hr : 0 ≤ r) (hc : cos θ = -√r) :
    sin θ = √(1 - r) := by
  rw [sin_eq_sqrt_one_sub_cos_sq hθ.1 hθ.2, hc, neg_sq, sq_sqrt hr]

/-- **Identity I2.** -/
theorem identity_I2 {θ₁ θ₂ θ₃ : ℝ}
    (h₁ : π / 2 < θ₁ ∧ θ₁ < π) (h₂ : π / 2 < θ₂ ∧ θ₂ < π) (h₃ : π / 2 < θ₃ ∧ θ₃ < π)
    (c₁ : cos θ₁ = -√(1 / 5)) (c₂ : cos θ₂ = -√r₂) (c₃ : cos θ₃ = -√r₃) :
    θ₁ + θ₂ + θ₃ = 2 * π := by
  have hpi := pi_pos
  have s₂ : sin θ₂ = √(1 - r₂) :=
    sin_of_cos_neg_sqrt ⟨by linarith, h₂.2.le⟩ r₂_pos.le c₂
  have s₃ : sin θ₃ = √(1 - r₃) :=
    sin_of_cos_neg_sqrt ⟨by linarith, h₃.2.le⟩ r₃_pos.le c₃
  -- cos (θ₂ + θ₃) = √(r₂ r₃) - √((1 - r₂)(1 - r₃)) = √(1/45) - √(16/45)
  have hcos : cos (θ₂ + θ₃) = √(1 / 45) - √(16 / 45) := by
    rw [cos_add, c₂, c₃, s₂, s₃, neg_mul_neg, ← sqrt_mul r₂_pos.le, r₂_mul_r₃,
      ← sqrt_mul (by linarith [r₂_lt_one]), one_sub_r₂_mul]
  -- √(16/45) = 4 √(1/45) and √(1/5) = 3 √(1/45)
  have h16 : √(16 / 45 : ℝ) = 4 * √(1 / 45) := by
    rw [show (16 / 45 : ℝ) = 4 ^ 2 * (1 / 45) by norm_num, sqrt_mul (by norm_num),
      sqrt_sq (by norm_num)]
  have h15 : √(1 / 5 : ℝ) = 3 * √(1 / 45) := by
    rw [show (1 / 5 : ℝ) = 3 ^ 2 * (1 / 45) by norm_num, sqrt_mul (by norm_num),
      sqrt_sq (by norm_num)]
  have hcos' : cos (θ₂ + θ₃) = cos θ₁ := by rw [hcos, c₁, h16, h15]; ring
  -- both 2π - (θ₂ + θ₃) and θ₁ lie in [0, π], where cos is injective
  have hsum : θ₂ + θ₃ = 2 * π - θ₁ := by
    have key : cos (2 * π - (θ₂ + θ₃)) = cos θ₁ := by rw [cos_two_pi_sub, hcos']
    have := injOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, h₁.2.le⟩ key
    linarith
  linarith

end ConvexUniformHoneycombs
