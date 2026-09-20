/-
Copyright (c) 2026 Mario Càllisto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Càllisto
-/
import Mathlib

/-!
# The antiprism tails: Lemmas A, B and E

Section 4.2 of the paper. The unit antiprism `A_q` has closed-form dihedrals
`cos a₃q(q) = -tan(π/2q)/√3` (base–lateral) and `cos a₃₃(q) = (1 - 4 cos(π/q))/3`
(lateral–lateral); the closed forms are the paper's equation (1), derived there from the coordinate
model, and enter here as the definitions. Three consequences carry the antiprism tail of the
Alphabet Theorem:

* **Lemma A**: `a₃q(q) > 90°` for every `q ≥ 4`;
* **Lemma B**: `a₃₃(q) < 180°` for every `q ≥ 4`;
* **Lemma E**: `2 a₃q(q) + a₃₃(r) ≠ 360°` for all integers `q, r ≥ 4` — the two-parameter family of
  near-coincidences `[A_q(3·q), A_q(q·3), A_r(3·3)]` never closes exactly. The equation reduces to
  `tan(π/2q) = 2 sin(π/2r)`, and the *interleaving* `2 sin(π/4q) < tan(π/2q) < 2 sin(π/(4q-2))`
  places the real solution strictly between `2q - 1` and `2q`, never at an integer.

The interleaving is proved for all real `q ≥ 4` from elementary bounds: `sin x < x`,
`x - x³/6 < sin x`, `1 - x²/2 ≤ cos x`, and `π < 3.15`; the paper's grid check up to `q = 20000`
is thereby superseded.

## Main results

* `ConvexUniformHoneycombs.a3q_gt_pi_div_two` (Lemma A), `ConvexUniformHoneycombs.a33_lt_pi`
  (Lemma B).
* `ConvexUniformHoneycombs.interleave_left`, `ConvexUniformHoneycombs.interleave_right`: the
  interleaving, for real `q ≥ 4`.
* `ConvexUniformHoneycombs.lemma_E`: `2 a₃q(q) + a₃₃(r) ≠ 2π` for all naturals `q, r ≥ 4`.
-/

namespace ConvexUniformHoneycombs

open Real

/-- The base–lateral dihedral of the unit antiprism `A_q`, by its closed form. -/
noncomputable def a3q (q : ℝ) : ℝ := arccos (-(tan (π / (2 * q))) / √3)

/-- The lateral–lateral dihedral of the unit antiprism `A_q`, by its closed form. -/
noncomputable def a33 (q : ℝ) : ℝ := arccos ((1 - 4 * cos (π / q)) / 3)

theorem sqrt_three_gt_one : (1 : ℝ) < √3 := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

section Bounds

variable {q : ℝ} (hq : 4 ≤ q)
include hq

theorem pi_div_two_q_pos : 0 < π / (2 * q) := by positivity

theorem pi_div_two_q_le : π / (2 * q) ≤ π / 8 := by
  apply div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by linarith)

/-- `tan(π/2q)` lies strictly between `0` and `1` for `q ≥ 4`. -/
theorem tan_pi_div_two_q_pos : 0 < tan (π / (2 * q)) :=
  tan_pos_of_pos_of_lt_pi_div_two (pi_div_two_q_pos hq)
    (by linarith [pi_div_two_q_le hq, pi_pos])

theorem tan_pi_div_two_q_lt_one : tan (π / (2 * q)) < 1 := by
  rw [← tan_pi_div_four]
  exact tan_lt_tan_of_nonneg_of_lt_pi_div_two (pi_div_two_q_pos hq).le (by linarith [pi_pos])
    (by linarith [pi_div_two_q_le hq, pi_pos])

/-- The argument of `a3q` lies in `(-1, 0)`. -/
theorem a3q_arg_mem : -1 < -(tan (π / (2 * q))) / √3 ∧ -(tan (π / (2 * q))) / √3 < 0 := by
  have ht := tan_pi_div_two_q_pos hq
  have ht1 := tan_pi_div_two_q_lt_one hq
  have hs := sqrt_three_gt_one
  constructor
  · rw [neg_div, neg_lt_neg_iff, div_lt_one (by linarith)]
    linarith
  · rw [neg_div]
    exact neg_neg_of_pos (div_pos ht (by linarith))

/-- **Lemma A.** `a₃q(q) > 90°` for every `q ≥ 4`: the cosine `-tan(π/2q)/√3` is negative. -/
theorem a3q_gt_pi_div_two : π / 2 < a3q q := by
  unfold a3q
  have := (a3q_arg_mem hq).2
  exact lt_of_not_ge fun h => absurd (arccos_le_pi_div_two.mp h) (not_le.mpr this)

theorem a3q_lt_pi : a3q q < π := by
  unfold a3q
  exact arccos_lt_pi.mpr (a3q_arg_mem hq).1

theorem cos_a3q : cos (a3q q) = -(tan (π / (2 * q))) / √3 := by
  unfold a3q
  exact cos_arccos (a3q_arg_mem hq).1.le ((a3q_arg_mem hq).2.le.trans zero_le_one)

/-- `cos(π/q)` lies in `(0, 1)` for `q ≥ 4`. -/
theorem cos_pi_div_q_mem : 0 < cos (π / q) ∧ cos (π / q) < 1 := by
  have h0 : 0 < π / q := by positivity
  have h4 : π / q ≤ π / 4 :=
    div_le_div_of_nonneg_left pi_pos.le (by norm_num) hq
  constructor
  · exact cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  · rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl (by linarith [pi_pos]) h0

/-- The argument of `a33` lies in `(-1, 1)`. -/
theorem a33_arg_mem : -1 < (1 - 4 * cos (π / q)) / 3 ∧ (1 - 4 * cos (π / q)) / 3 < 1 := by
  obtain ⟨h0, h1⟩ := cos_pi_div_q_mem hq
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]; linarith
  · rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)]; linarith

/-- **Lemma B.** `a₃₃(q) < 180°` for every `q ≥ 4`: the cosine exceeds `-1` since `cos(π/q) < 1`. -/
theorem a33_lt_pi : a33 q < π := by
  unfold a33
  exact arccos_lt_pi.mpr (a33_arg_mem hq).1

theorem a33_pos : 0 < a33 q := by
  unfold a33
  exact arccos_pos.mpr (a33_arg_mem hq).2

theorem cos_a33 : cos (a33 q) = (1 - 4 * cos (π / q)) / 3 := by
  unfold a33
  exact cos_arccos (a33_arg_mem hq).1.le (a33_arg_mem hq).2.le

end Bounds

section Interleaving

/-- **The left inequality**: `2 sin(π/4q) < tan(π/2q)` for real `q ≥ 4` — with `v = π/4q`,
`tan 2v = sin 2v / cos 2v = 2 sin v cos v / cos 2v > 2 sin v`, since `0 < cos 2v < cos v`. -/
theorem interleave_left {q : ℝ} (hq : 4 ≤ q) : 2 * sin (π / (4 * q)) < tan (π / (2 * q)) := by
  set v := π / (4 * q) with hv
  have hv0 : 0 < v := by positivity
  have hv16 : v ≤ π / 16 := div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by linarith)
  have h2v : π / (2 * q) = 2 * v := by rw [hv]; field_simp; ring
  rw [h2v, tan_eq_sin_div_cos, sin_two_mul]
  have hcos2 : 0 < cos (2 * v) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hcosv : cos (2 * v) < cos v :=
    cos_lt_cos_of_nonneg_of_le_pi_div_two hv0.le (by linarith [pi_pos]) (by linarith)
  have hsin : 0 < sin v := sin_pos_of_pos_of_lt_pi hv0 (by linarith [pi_pos])
  rw [lt_div_iff₀ hcos2]
  nlinarith

/-- **The right inequality**: `tan(π/2q) < 2 sin(π/(4q-2))` for real `q ≥ 4`. With `x = π/2q ≤ π/8`
and `y = π/(4q-2)`: `2y ≥ x + x²/π`, `y ≤ 4x/7`, `sin y > y - y³/6`, and
`tan x ≤ x/(1 - x²/2) = x + x³/(2 - x²)`; the constants close with `π < 3.15`. -/
theorem interleave_right {q : ℝ} (hq : 4 ≤ q) : tan (π / (2 * q)) < 2 * sin (π / (4 * q - 2)) := by
  set x := π / (2 * q) with hx
  set y := π / (4 * q - 2) with hy
  have hpi := pi_gt_three
  have hpi' := pi_lt_d2
  have hx0 : 0 < x := by positivity
  have hx8 : x ≤ π / 8 := pi_div_two_q_le hq
  have hq2 : 0 < 4 * q - 2 := by linarith
  have hy0 : 0 < y := by positivity
  -- the two relations between x and y
  have h2y : x + x ^ 2 / π ≤ 2 * y := by
    have e1 : x + x ^ 2 / π = π * (2 * q + 1) / (4 * q ^ 2) := by
      rw [hx]; field_simp; ring
    have e2 : 2 * y = π / (2 * q - 1) := by
      have h2q : (2 * q - 1 : ℝ) ≠ 0 := by linarith
      have h4q : (4 * q - 2 : ℝ) ≠ 0 := by linarith
      rw [hy, mul_div_assoc', div_eq_div_iff h4q h2q]; ring
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [pi_pos]
  have hy47 : y ≤ 4 * x / 7 := by
    rw [hx, hy, div_le_iff₀ hq2]
    rw [show 4 * (π / (2 * q)) / 7 * (4 * q - 2) = π * (4 * q - 2) / (7 * q) * 2 by
      field_simp; ring]
    rw [show π * (4 * q - 2) / (7 * q) * 2 = π * ((8 * q - 4) / (7 * q)) by ring]
    have : (1 : ℝ) ≤ (8 * q - 4) / (7 * q) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [pi_pos]
  -- the elementary bounds
  have hsin : y - y ^ 3 / 6 < sin y := sin_gt_sub_cube hy0
  have hsinx : sin x < x := sin_lt hx0
  have hcosx : 1 - x ^ 2 / 2 ≤ cos x := one_sub_sq_div_two_le_cos
  have hcos0 : 0 < 1 - x ^ 2 / 2 := by nlinarith
  have htan : tan x ≤ x / (1 - x ^ 2 / 2) := by
    rw [tan_eq_sin_div_cos, div_le_div_iff₀ (by linarith) hcos0]
    nlinarith
  -- the numeric close: x/(1 - x²/2) < x + x²/π - (4x/7)³/3, using x ≤ π/8 < 0.394
  have hx394 : x < 0.394 := by linarith
  have hstep : x / (1 - x ^ 2 / 2) < 2 * (y - y ^ 3 / 6) := by
    rw [div_lt_iff₀ hcos0]
    have hy3 : y ^ 3 ≤ (4 * x / 7) ^ 3 := by
      exact pow_le_pow_left₀ hy0.le hy47 3
    have hinv : 0.3174 < 1 / π := by
      rw [lt_div_iff₀ pi_pos]; linarith
    have hx2pi : x ^ 2 * 0.3174 < x ^ 2 / π := by
      rw [div_eq_mul_one_div]
      exact mul_lt_mul_of_pos_left hinv (by positivity)
    nlinarith [sq_nonneg x, pow_pos hx0 3, pow_pos hx0 4, mul_pos hx0 hy0]
  calc tan x ≤ x / (1 - x ^ 2 / 2) := htan
    _ < 2 * (y - y ^ 3 / 6) := hstep
    _ < 2 * sin y := by linarith

end Interleaving

/-- `2 sin(π/2r)` is antitone in `r` on `[1, ∞)`: `π/2r` decreases and lies in `[0, π/2]`. -/
theorem two_sin_antitone {r s : ℝ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    2 * sin (π / (2 * s)) ≤ 2 * sin (π / (2 * r)) := by
  have hs : 1 ≤ s := hr.trans hrs
  have h1 : π / (2 * s) ≤ π / (2 * r) :=
    div_le_div_of_nonneg_left pi_pos.le (by positivity) (by linarith)
  have h2 : π / (2 * r) ≤ π / 2 := div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by linarith)
  have h3 : 0 ≤ π / (2 * s) := by positivity
  have := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) h2 h1
  linarith

/-- **Lemma E.** For all integers `q, r ≥ 4`, `2 a₃q(q) + a₃₃(r) ≠ 360°`. -/
theorem lemma_E (q r : ℕ) (hq : 4 ≤ q) (hr : 4 ≤ r) :
    2 * a3q q + a33 r ≠ 2 * π := by
  intro heq
  have hq' : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hr' : (4 : ℝ) ≤ r := by exact_mod_cast hr
  set A := a3q q with hA
  set B := a33 r with hB
  set t := tan (π / (2 * q)) with ht
  have ht0 := tan_pi_div_two_q_pos hq'
  -- cos B = cos (2π - 2A) = cos 2A = 2 cos² A - 1
  have hcosB : cos B = 2 * t ^ 2 / 3 - 1 := by
    have : B = 2 * π - 2 * A := by linarith
    rw [this, cos_two_pi_sub, cos_two_mul, cos_a3q hq', ht]
    have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp
    rw [h3]; ring
  -- the closed form of cos B, with cos(π/r) = 1 - 2 sin²(π/2r)
  have hcosB' : cos B = (1 - 4 * (1 - 2 * sin (π / (2 * r)) ^ 2)) / 3 := by
    rw [hB, cos_a33 hr']
    have : π / (r : ℝ) = 2 * (π / (2 * r)) := by field_simp
    rw [this, cos_two_mul_eq_one_sub]
  -- hence (2 sin(π/2r))² = t², both sides positive
  have hsq : (2 * sin (π / (2 * r))) ^ 2 = t ^ 2 := by
    have := hcosB.symm.trans hcosB'
    nlinarith
  have hsinr : 0 < sin (π / (2 * r)) :=
    sin_pos_of_pos_of_lt_pi (by positivity) (by
      have : π / (2 * r) ≤ π / 8 := pi_div_two_q_le hr'
      linarith [pi_pos])
  have hE : 2 * sin (π / (2 * r)) = t := (sq_eq_sq₀ (by positivity) ht0.le).mp hsq
  -- the interleaving forbids every integer r
  have hleft := interleave_left hq'
  have hright := interleave_right hq'
  rcases le_or_gt (r : ℝ) (2 * q - 1) with hle | hlt
  · -- r ≤ 2q - 1: h(r) ≥ h(2q - 1) > t
    have h1 : 2 * sin (π / (2 * (2 * q - 1))) ≤ 2 * sin (π / (2 * r)) :=
      two_sin_antitone (by linarith) hle
    have : π / (2 * (2 * (q : ℝ) - 1)) = π / (4 * q - 2) := by ring_nf
    rw [this] at h1
    linarith
  · -- r ≥ 2q: h(r) ≤ h(2q) < t
    have hge : 2 * (q : ℝ) ≤ r := by
      have : (2 * q - 1 : ℝ) < r := hlt
      have hz : ((2 * q - 1 : ℕ) : ℝ) < r := by push_cast [show 1 ≤ 2 * q by omega]; linarith
      have : 2 * q - 1 < r := by exact_mod_cast hz
      have : 2 * q ≤ r := by omega
      exact_mod_cast this
    have h1 : 2 * sin (π / (2 * r)) ≤ 2 * sin (π / (2 * (2 * q))) :=
      two_sin_antitone (by linarith) hge
    have : π / (2 * (2 * (q : ℝ))) = π / (4 * q) := by ring_nf
    rw [this] at h1
    linarith

section Corridors

/-!
### The tail corridors

The corona fixpoint of Section 4.1 runs over an uncapped participant pool: every antiprism `A_q`
with `q > 300` enters through the two *corridors* `(π/2, a₃q(301)]` and `[a₃₃(301), π)`, and every
prism `P_p` with `p > 500` through `[π - 2π/501, π)` (its lateral dihedral) and the value `π/2`
(its base). The corridors contain the dihedrals of every tail cell because `a₃q` is antitone and
`a₃₃` monotone in `q`, and `π - 2π/p` is monotone in `p`.
-/

/-- `a₃q` is antitone on `[4, ∞)`: `tan(π/2q)` decreases with `q`, so the cosine `-tan(π/2q)/√3`
increases and the arccosine decreases. -/
theorem a3q_antitone {q r : ℝ} (hq : 4 ≤ q) (hqr : q ≤ r) : a3q r ≤ a3q q := by
  have hr : 4 ≤ r := hq.trans hqr
  have htan : tan (π / (2 * r)) ≤ tan (π / (2 * q)) := by
    rcases hqr.lt_or_eq with h | h
    · exact (tan_lt_tan_of_nonneg_of_lt_pi_div_two (pi_div_two_q_pos hr).le
        (by linarith [pi_div_two_q_le hq, pi_pos])
        (div_lt_div_of_pos_left pi_pos (by linarith) (by linarith))).le
    · rw [h]
  unfold a3q
  apply arccos_le_arccos
  have hs : (0 : ℝ) < √3 := by positivity
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right htan hs.le

/-- `a₃₃` is monotone on `[4, ∞)`: `cos(π/q)` increases with `q`, so the cosine `(1 - 4 cos(π/q))/3`
decreases and the arccosine increases. -/
theorem a33_monotone {q r : ℝ} (hq : 4 ≤ q) (hqr : q ≤ r) : a33 q ≤ a33 r := by
  have hcos : cos (π / q) ≤ cos (π / r) := by
    apply cos_le_cos_of_nonneg_of_le_pi (div_pos pi_pos (by linarith)).le
    · exact div_le_self pi_pos.le (by linarith)
    · exact div_le_div_of_nonneg_left pi_pos.le (by linarith) hqr
  unfold a33
  apply arccos_le_arccos
  linarith

/-- **The antiprism base corridor.** For every real `q ≥ 301`, `a₃q(q) ∈ (π/2, a₃q(301)]`. -/
theorem a3q_tail_corridor {q : ℝ} (hq : 301 ≤ q) : π / 2 < a3q q ∧ a3q q ≤ a3q 301 :=
  ⟨a3q_gt_pi_div_two (by linarith), a3q_antitone (by norm_num) hq⟩

/-- **The antiprism lateral corridor.** For every real `q ≥ 301`, `a₃₃(q) ∈ [a₃₃(301), π)`. -/
theorem a33_tail_corridor {q : ℝ} (hq : 301 ≤ q) : a33 301 ≤ a33 q ∧ a33 q < π :=
  ⟨a33_monotone (by norm_num) hq, a33_lt_pi (by linarith)⟩

/-- **The prism lateral corridor.** For every real `p ≥ 501`, the lateral dihedral `π - 2π/p` of
`P_p` lies in `[π - 2π/501, π)`. -/
theorem prism_tail_corridor {p : ℝ} (hp : 501 ≤ p) :
    π - 2 * π / 501 ≤ π - 2 * π / p ∧ π - 2 * π / p < π := by
  constructor
  · have : 2 * π / p ≤ 2 * π / 501 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hp
    linarith
  · have : 0 < 2 * π / p := div_pos (by positivity) (by linarith)
    linarith

end Corridors

end ConvexUniformHoneycombs
