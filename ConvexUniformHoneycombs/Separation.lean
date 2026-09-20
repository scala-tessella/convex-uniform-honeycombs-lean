/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib
import ConvexUniformHoneycombs.TwoTier

/-!
# The separation constant of the species search

Lemma 5.2 (separation) of the paper: in any edge-to-edge tiling of the sphere by corner figures of
the thirteen core cells, two distinct tiling-vertices are at least the minimum
vertex-to-non-incident-side distance apart, and that minimum is attained by the tetrahedral
corner — the altitude of the equilateral spherical triangle of side `60°`. The sweep over the
thirteen corner figures is an interval computation in the artifact; the value of the tetrahedral
altitude is exact, and this file proves it: **the altitude is `α = arctan √2`**, the very
generator of the two-tier lattice.

The corner figure of the unit regular tetrahedron at a vertex is the spherical triangle spanned by
the three neighbour directions, unit vectors pairwise at `60°`; with explicit coordinates
`a = (1, 0, 0)`, `b = (1/2, √3/2, 0)`, `v = (1/2, √3/6, √6/3)`, the sine of the distance from `v` to
the great circle through `a` and `b` is `|n · v| / |n|` for the normal `n = a × b`, and its square
is `2/3 = sin² α` (from `cos 2α = -1/3`).

## Main results

* `ConvexUniformHoneycombs.tet_unit`, `ConvexUniformHoneycombs.tet_sixty`: the three vectors are
  unit and pairwise at `60°`.
* `ConvexUniformHoneycombs.tet_altitude_sin_sq`: `(n · v)² / (n · n) = 2/3`.
* `ConvexUniformHoneycombs.sin_sq_alpha`, `ConvexUniformHoneycombs.sin_alpha`: `sin² α = 2/3`,
  `sin α = √(2/3)`.
* `ConvexUniformHoneycombs.tet_altitude`: the altitude of the tetrahedral corner, the angle in
  `[0, π/2]` whose sine is `√(2/3)`, is `α`.
-/

namespace ConvexUniformHoneycombs

open Real Matrix

/-- The three neighbour directions of a vertex of the unit regular tetrahedron: the tetrahedral
corner figure, as unit vectors pairwise at `60°`. -/
noncomputable def tetA : Fin 3 → ℝ := ![1, 0, 0]

noncomputable def tetB : Fin 3 → ℝ := ![1 / 2, √3 / 2, 0]

noncomputable def tetV : Fin 3 → ℝ := ![1 / 2, √3 / 6, √6 / 3]

theorem sqrt_three_sq : (√3 : ℝ) ^ 2 = 3 := sq_sqrt (by norm_num)

theorem sqrt_six_sq : (√6 : ℝ) ^ 2 = 6 := sq_sqrt (by norm_num)

/-- The three directions are unit vectors. -/
theorem tet_unit : tetA ⬝ᵥ tetA = 1 ∧ tetB ⬝ᵥ tetB = 1 ∧ tetV ⬝ᵥ tetV = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [tetA, tetB, tetV, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    nlinarith [sqrt_three_sq, sqrt_six_sq]

/-- The three directions are pairwise at `60°`: every inner product is `1/2`. -/
theorem tet_sixty : tetA ⬝ᵥ tetB = 1 / 2 ∧ tetA ⬝ᵥ tetV = 1 / 2 ∧ tetB ⬝ᵥ tetV = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [tetA, tetB, tetV, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    nlinarith [sqrt_three_sq, sqrt_six_sq]

/-- The normal of the side through `a` and `b`. -/
theorem tet_normal : crossProduct tetA tetB = ![0, 0, √3 / 2] := by
  simp only [tetA, tetB, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ext i; fin_cases i <;> simp

/-- **The tetrahedral altitude, squared sine.** The sine of the distance from `v` to the great
circle through `a` and `b` is `|n · v| / |n|`; its square is `2/3`. -/
theorem tet_altitude_sin_sq :
    (crossProduct tetA tetB ⬝ᵥ tetV) ^ 2 / (crossProduct tetA tetB ⬝ᵥ crossProduct tetA tetB)
      = 2 / 3 := by
  rw [tet_normal]
  simp only [tetV, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have h3 := sqrt_three_sq
  have h6 := sqrt_six_sq
  have hs : (0 : ℝ) < √3 := by positivity
  rw [div_eq_iff (by positivity)]
  nlinarith [h3, h6]

/-- `sin² α = 2/3`, from `cos 2α = -1/3`. -/
theorem sin_sq_alpha : sin alpha ^ 2 = 2 / 3 := by
  have h := cos_two_alpha
  rw [cos_two_mul] at h
  linarith [sin_sq_add_cos_sq alpha]

theorem alpha_pos : 0 < alpha := arctan_pos.mpr (by positivity)

theorem alpha_lt_pi_div_two : alpha < π / 2 := arctan_lt_pi_div_two _

/-- `sin α = √(2/3)`. -/
theorem sin_alpha : sin alpha = √(2 / 3) := by
  have hpos : 0 ≤ sin alpha :=
    (sin_pos_of_pos_of_lt_pi alpha_pos (by linarith [alpha_lt_pi_div_two, pi_pos])).le
  rw [← sin_sq_alpha, sqrt_sq hpos]

/-- **The tetrahedral altitude is `α`.** The distance from a vertex of the tetrahedral corner to
its opposite side — the angle in `[0, π/2]` whose sine is `√(2/3)` — is `arctan √2`, the generator
of the two-tier lattice. -/
theorem tet_altitude : arcsin (√(2 / 3)) = alpha := by
  rw [← sin_alpha]
  exact arcsin_sin (by linarith [alpha_pos, pi_pos]) alpha_lt_pi_div_two.le

/-- The same, read off the corner's coordinates: the squared sine of the altitude computed from the
vectors equals `sin² α`. -/
theorem tet_altitude_eq_sin_sq_alpha :
    (crossProduct tetA tetB ⬝ᵥ tetV) ^ 2 / (crossProduct tetA tetB ⬝ᵥ crossProduct tetA tetB)
      = sin alpha ^ 2 := by
  rw [tet_altitude_sin_sq, sin_sq_alpha]

end ConvexUniformHoneycombs
