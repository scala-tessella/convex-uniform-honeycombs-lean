/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# The two-tier arithmetic

Proposition 3.1 of the paper: every dihedral angle of the thirteen core cells lies in the lattice
`15°·ℤ + α·ℤ` with `α = arctan √2`, and `α` is irrational in degrees — `cos 2α = -1/3`, so Niven's
theorem applies. Consequently an equation `Σ θᵢ = 360°` between such angles splits into two integer
equations: the `α`-charges cancel and the rational parts sum to `360°` on the `15°` grid. The same
split carries the area equation of Section 5 (`Σ = 720°`) and the window trichotomy of the prism
tail (Proposition 4.5(i)).

Angles are kept in radians: `15°` is `π / 12` and a target of `c · 360°` is `2c · π`.

## Main results

* `ConvexUniformHoneycombs.cos_two_alpha`: `cos (2α) = -1/3`.
* `ConvexUniformHoneycombs.alpha_ne_rat_mul_pi`: `α` is not a rational multiple of `π`.
* `ConvexUniformHoneycombs.two_tier_split`: a lattice sum equal to a rational multiple of `π` has
  zero total `α`-charge, and its rational parts add up exactly.
* `ConvexUniformHoneycombs.barlow_support`: the area equation over tetrahedra and octahedra has
  the unique solution `(8, 6)` (Corollary 5.4).
-/

namespace ConvexUniformHoneycombs

open Real

/-- The irrational generator of the two-tier lattice: `α = arctan √2 ≈ 54.7356°`, half the
tetrahedral bond angle. -/
noncomputable def alpha : ℝ := arctan (√2)

theorem cos_two_alpha : cos (2 * alpha) = -1 / 3 := by
  rw [cos_two_mul, alpha, cos_sq_arctan]
  norm_num

/-- **Niven.** `α` is irrational in degrees: were `α = q π` with `q` rational, `2 cos 2α = -2/3`
would be an algebraic integer, hence an integer. -/
theorem alpha_ne_rat_mul_pi (q : ℚ) : alpha ≠ q * π := by
  intro h
  have hint : IsIntegral ℤ (2 * cos ((2 * q : ℚ) * π)) := isIntegral_two_mul_cos_rat_mul_pi (2 * q)
  have hval : 2 * cos ((2 * q : ℚ) * π) = ((-2 / 3 : ℚ) : ℝ) := by
    have : ((2 * q : ℚ) : ℝ) * π = 2 * alpha := by rw [h]; push_cast; ring
    rw [this, cos_two_alpha]; norm_num
  obtain ⟨k, hk⟩ := (IsIntegral.exists_int_iff_exists_rat hint).mp ⟨_, hval⟩
  rw [hval] at hk
  have hq : (-2 / 3 : ℚ) = k := by exact_mod_cast hk
  have h3 : (3 : ℚ) * k = -2 := by rw [← hq]; norm_num
  have h3z : (3 : ℤ) * k = -2 := by exact_mod_cast h3
  omega

/-- **The split.** Angles `aᵢ · π/12 + bᵢ · α` with integer coefficients summing to `c · π`, `c`
rational, have zero total `α`-charge and rational parts summing to `c · π` exactly:
`Σ aᵢ = 12 c`. -/
theorem two_tier_split {ι : Type*} (s : Finset ι) (a b : ι → ℤ) (c : ℚ)
    (h : ∑ i ∈ s, ((a i : ℝ) * (π / 12) + (b i : ℝ) * alpha) = c * π) :
    ∑ i ∈ s, b i = 0 ∧ ((∑ i ∈ s, a i : ℤ) : ℚ) = 12 * c := by
  have hsum : (∑ i ∈ s, (a i : ℝ)) * (π / 12) + (∑ i ∈ s, (b i : ℝ)) * alpha = c * π := by
    rw [← h, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  have hb : ∑ i ∈ s, b i = 0 := by
    by_contra hne
    have hB : (∑ i ∈ s, (b i : ℝ)) ≠ 0 := by
      have : (∑ i ∈ s, (b i : ℝ)) = ((∑ i ∈ s, b i : ℤ) : ℝ) := by push_cast; rfl
      rw [this]; exact_mod_cast hne
    have hB12 : (12 : ℝ) * ∑ i ∈ s, (b i : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hB
    apply alpha_ne_rat_mul_pi ((12 * c - ∑ i ∈ s, (a i : ℚ)) / (12 * ∑ i ∈ s, (b i : ℚ)))
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hB12]
    linear_combination (12 : ℝ) * hsum
  refine ⟨hb, ?_⟩
  have hB0 : (∑ i ∈ s, (b i : ℝ)) = 0 := by
    have : (∑ i ∈ s, (b i : ℝ)) = ((∑ i ∈ s, b i : ℤ) : ℝ) := by push_cast; rfl
    rw [this, hb]; simp
  rw [hB0] at hsum
  have hpi : π ≠ 0 := pi_ne_zero
  have hA : (∑ i ∈ s, (a i : ℝ)) = 12 * c :=
    mul_right_cancel₀ hpi (by linear_combination 12 * hsum)
  have h2 : ((∑ i ∈ s, a i : ℤ) : ℝ) = ((12 * c : ℚ) : ℝ) := by push_cast; exact hA
  exact_mod_cast h2

/-- **Corollary 5.4, the arithmetic.** In `(rational part, α-charge)` coordinates a tetrahedral
corner has excess `(360°, -6)` and an octahedral corner `(-360°, 8)`; corners tiling the sphere
(excess `(720°, 0)`) with `a` tetrahedra and `b` octahedra force `-6a + 8b = 0` and
`360a - 360b = 720`, whose only solution is `(a, b) = (8, 6)`. -/
theorem barlow_support (a b : ℤ) (hcharge : -6 * a + 8 * b = 0)
    (hrational : 360 * a - 360 * b = 720) : a = 8 ∧ b = 6 := by
  omega

end ConvexUniformHoneycombs
