/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Estimates on natural log of rationals close to 1
-/

open Filter Finset Set

open scoped Topology BigOperators

namespace Real

theorem artanh_partial_series_bound_aux {y : ℝ} (n : ℕ) (hy₁ : -1 < y) (hy₂ : y < 1) :
    deriv
        (fun x : ℝ =>
          ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) - 1 / 2 * log ((1 + x) / (1 - x)))
        y =
      -(y ^ 2) ^ n / (1 - y ^ 2) :=
  by
  have hF :
      (fun x : ℝ =>
          ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) - 1 / 2 * log ((1 + x) / (1 - x))) =
        fun x =>
          -(1 / 2 * log ((1 + x) / (1 - x)) - ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)) := by
    funext x
    ring
  rw [hF]
  convert (hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range n hy₁ hy₂).neg.deriv using 1
  rw [neg_div]

theorem artanh_partial_series_upper_bound {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) - 1 / 2 * log ((1 + x) / (1 - x))| ≤
      |x| ^ (2 * n + 1) / (1 - x ^ 2) :=
  by
  rw [abs_sub_comm]
  exact sum_range_sub_log_div_le h n

theorem newbound {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |2 * ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) - log ((1 + x) / (1 - x))| ≤
      2 * |x| ^ (2 * n + 1) / (1 - x ^ 2) :=
  by
  rw [show 2 * ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) - log ((1 + x) / (1 - x)) =
        2 * (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1) - 1 / 2 * log ((1 + x) / (1 - x))) by
      ring, abs_mul, abs_two, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (artanh_partial_series_upper_bound h n) zero_le_two

theorem abs_sub_lt_of_approx {a b c ε δ : ℝ} (h₁ : |a - b| ≤ δ) (h₂ : |b - c| < ε - δ) :
    |a - c| < ε := by
  have := (_root_.abs_sub_le a b c).trans_lt (add_lt_add_of_le_of_lt h₁ h₂)
  linarith

-- lemma log_two_near_10 : |log 2 - 836158 / 1206321| ≤ 1/10^10 :=
-- begin
--   suffices : |log 2 - 836158 / 1206321| ≤ 1/17179869184 + (1/10^10 - 1/2^34),
--   { norm_num1 at *,
--     assumption },
--   have t : |(2⁻¹ : ℝ)| = 2⁻¹,
--   { rw abs_of_pos, norm_num },
--   have z := real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : ℝ)| < 1, by { rw t, norm_num }) 34,
--   rw t at z,
--   norm_num1 at z,
--   rw [one_div (2:ℝ), log_inv, ←sub_eq_add_neg, _root_.abs_sub_comm] at z,
--   apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _),
--   simp_rw [sum_range_succ],
--   norm_num,
--   rw abs_of_pos;
--   norm_num
-- end
theorem log_two_near_20 : |log 2 - 48427462327 / 69866059742| < 9 / 10 ^ 21 :=
  by
  have t : |(3⁻¹ : ℝ)| = 3⁻¹ := abs_of_pos (by norm_num1)
  have z := newbound (show |(3⁻¹ : ℝ)| < 1 by rw [t]; norm_num1) 21
  rw [t, _root_.abs_sub_comm] at z 
  norm_num1 at z 
  refine abs_sub_lt_of_approx z ?_
  simp_rw [sum_range_succ, sum_range_zero]
  norm_num1

theorem log_two_gt_d20 : 0.6931471805599453094 < log 2 :=
  (sub_lt_comm.1 (abs_sub_lt_iff.1 log_two_near_20).2).trans_le' (by norm_num1)

theorem log_two_lt_d20 : log 2 < 0.69314718055994530943 :=
  lt_of_lt_of_le (sub_lt_iff_lt_add.1 (abs_sub_lt_iff.1 log_two_near_20).1) (by norm_num)

theorem log_three_div_two_near_20 : |log (3 / 2) - 31251726476 / 77076241213| < 1 / 10 ^ 22 :=
  by
  have t : |(5⁻¹ : ℝ)| = 5⁻¹ := abs_of_pos (by norm_num1)
  have z := newbound (show |(5⁻¹ : ℝ)| < 1 by rw [t]; norm_num1) 17
  rw [t, _root_.abs_sub_comm] at z 
  norm_num1 at z 
  refine abs_sub_lt_of_approx z ?_
  simp_rw [sum_range_succ, sum_range_zero]
  norm_num1

theorem log_four_div_three_near_20 : |log (4 / 3) - 4349275835861 / 15118341573370| < 1 / 10 ^ 26 :=
  by
  have t : |(7⁻¹ : ℝ)| = 7⁻¹ := abs_of_pos (by norm_num1)
  have z := newbound (show |(7⁻¹ : ℝ)| < 1 by rw [t]; norm_num1) 16
  rw [t, _root_.abs_sub_comm] at z 
  norm_num1 at z 
  refine abs_sub_lt_of_approx z ?_
  simp_rw [sum_range_succ, sum_range_zero]
  norm_num1

theorem log_nine_div_eight_near_20 :
    |log (9 / 8) - 26418276175004 / 224296105358295| < 3 / 10 ^ 29 :=
  by
  have t : |(17⁻¹ : ℝ)| = 17⁻¹ := abs_of_pos (by norm_num1)
  have z := newbound (show |(17⁻¹ : ℝ)| < 1 by rw [t]; norm_num1) 12
  rw [t, _root_.abs_sub_comm] at z 
  norm_num1 at z 
  refine abs_sub_lt_of_approx z ?_
  simp_rw [sum_range_succ, sum_range_zero]
  norm_num1

/-- Alternate sharper estimate for `log 2`, built from estimates for nearby small logarithms. -/
theorem log_two_near_20'' : |log 2 - 1148067618206 / 1656311459391| < 5 / 10 ^ 25 :=
  by
  have :
    log 2 - (2 * 4349275835861 / 15118341573370 + 26418276175004 / 224296105358295) =
      2 * (log (2 * 2 / 3) - 4349275835861 / 15118341573370) +
        (log (3 * 3 / (2 * 2 * 2)) - 26418276175004 / 224296105358295) :=
    by
    rw [mul_sub, ← sub_sub, add_sub_assoc', sub_left_inj, mul_div_assoc, sub_add_eq_add_sub,
      sub_left_inj, log_div, log_div, log_mul, log_mul, log_mul, log_mul]
    · ring
    all_goals norm_num
  rw [← sub_add_sub_cancel, this]
  apply (abs_add_three _ _ _).trans_lt _
  rw [abs_mul, abs_two, (by norm_num1 : (3 : ℝ) * 3 = 9), (by norm_num1 : (2 : ℝ) * 2 = 4),
    (by norm_num1 : (4 : ℝ) * 2 = 8)]
  have e₁ := mul_lt_mul_of_pos_left log_four_div_three_near_20 zero_lt_two
  have e₂ := log_nine_div_eight_near_20
  have e₃ :
      |(2 : ℝ) * ((4349275835861 : ℝ) / 15118341573370) +
          (26418276175004 : ℝ) / 224296105358295 -
          (1148067618206 : ℝ) / 1656311459391| < 47 / 10 ^ 26 := by norm_num1
  nlinarith [e₁, e₂, e₃]

theorem log_three_near_20 : |log 3 - 12397791320721 / 11284955983654| < 4 / 10 ^ 26 :=
  by
  have :
    log 3 - (2 * (26418276175004 / 224296105358295) + 3 * (4349275835861 / 15118341573370)) =
      2 * (log (3 ^ 2 / 2 ^ 3) - 26418276175004 / 224296105358295) +
        3 * (log (2 ^ 2 / 3) - 4349275835861 / 15118341573370) :=
    by
    rw [log_div, log_div, log_pow, log_pow, log_pow]
    · ring_nf
    all_goals norm_num
  rw [← sub_add_sub_cancel, this]
  apply (abs_add_three _ _ _).trans_lt _
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num1 : (0 : ℝ) < 2),
    abs_of_pos (by norm_num1 : (0 : ℝ) < 3), (by norm_num1 : (3 : ℝ) ^ 2 = 9),
    (by norm_num1 : (2 : ℝ) ^ 3 = 8), (by norm_num1 : (2 : ℝ) ^ 2 = 4)]
  have e₁ := mul_lt_mul_of_pos_left log_four_div_three_near_20 (by norm_num1 : (0 : ℝ) < 3)
  have e₂ := mul_lt_mul_of_pos_left log_nine_div_eight_near_20 (by norm_num1 : (0 : ℝ) < 2)
  have e₃ :
      |(2 : ℝ) * ((26418276175004 : ℝ) / 224296105358295) +
          3 * ((4349275835861 : ℝ) / 15118341573370) -
          (12397791320721 : ℝ) / 11284955983654| < 7 / 10 ^ 27 := by norm_num1
  nlinarith [e₁, e₂, e₃]

-- the proof does better than this
theorem log_three_gt_d20 : 1.0986122886681096 < log 3 :=
  (sub_lt_comm.1 (abs_sub_lt_iff.1 log_three_near_20).2).trans_le' (by norm_num1)

-- the proof does better than this
theorem log_three_lt_d20 : log 3 < 1.0986122886681097 :=
  lt_of_lt_of_le (sub_lt_iff_lt_add.1 (abs_sub_lt_iff.1 log_three_near_20).1) (by norm_num)

theorem log_64_div_63_near : |log (64 / 63) - 87664200650948 / 5566561694550313| < 4 / 10 ^ 32 :=
  by
  have t : |(127⁻¹ : ℝ)| = 127⁻¹ := abs_of_pos (by norm_num1)
  have z := newbound (show |(127⁻¹ : ℝ)| < 1 by rw [t]; norm_num1) 8
  rw [t, _root_.abs_sub_comm] at z 
  norm_num1 at z 
  refine abs_sub_lt_of_approx z ?_
  simp_rw [sum_range_succ, sum_range_zero]
  rw [abs_of_nonneg] <;> norm_num1

theorem abs_add_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc
    |a + b + c + d| = |(a + b + c) + d| := by ring_nf
    _ ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ |a| + |b| + |c| + |d| := by linarith [abs_add_three a b c]

theorem log_seven_near : |log 7 - 5543595633008 / 2848844606571| < 6 / 10 ^ 24 :=
  by
  have :
    log 7 -
        (-1 * (87664200650948 / 5566561694550313) +
          -2 * (12397791320721 / 11284955983654) +
          6 * (1148067618206 / 1656311459391)) =
      -1 * (log (2 ^ 6 / (3 ^ 2 * 7)) - 87664200650948 / 5566561694550313) +
          -2 * (log 3 - 12397791320721 / 11284955983654) +
        6 * (log 2 - 1148067618206 / 1656311459391) :=
    by
    rw [log_div, log_pow, log_mul, log_pow]
    · ring_nf
    all_goals norm_num
  rw [← sub_add_sub_cancel, this]
  apply (abs_add_four _ _ _ _).trans_lt _
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_one, abs_neg, abs_two, one_mul,
    abs_of_pos (by norm_num1 : (0 : ℝ) < 6),
    (by norm_num1 : (2 ^ 6 : ℝ) / (3 ^ 2 * 7) = 64 / 63)]
  have e₁ := log_64_div_63_near
  have e₂ := mul_lt_mul_of_pos_left log_three_near_20 two_pos
  have e₃ := mul_lt_mul_of_pos_left log_two_near_20'' (by norm_num1 : (0 : ℝ) < 6)
  have e₄ :
      |-1 * ((87664200650948 : ℝ) / 5566561694550313) +
          -2 * ((12397791320721 : ℝ) / 11284955983654) +
          6 * ((1148067618206 : ℝ) / 1656311459391) -
          (5543595633008 : ℝ) / 2848844606571| < 28 / 10 ^ 25 := by norm_num1
  nlinarith [e₁, e₂, e₃, e₄]

theorem log_25_div_24_near : |log (25 / 24) - 7010006310925 / 171721308410023| < 4 / 10 ^ 30 :=
  by
  have t : |(49⁻¹ : ℝ)| = 49⁻¹ := abs_of_pos (by norm_num1)
  have z := newbound (show |(49⁻¹ : ℝ)| < 1 by rw [t]; norm_num1) 9
  rw [t, _root_.abs_sub_comm] at z 
  norm_num1 at z 
  refine abs_sub_lt_of_approx z ?_
  simp_rw [sum_range_succ, sum_range_zero]
  norm_num1

theorem log_five_near : |log 5 - 25218653206049 / 15669230239462| < 2 / 10 ^ 24 :=
  by
  have :
    log 5 -
        (1 / 2 * (7010006310925 / 171721308410023) +
          1 / 2 * (12397791320721 / 11284955983654) +
          3 / 2 * (1148067618206 / 1656311459391)) =
      1 / 2 * (log (5 ^ 2 / (2 ^ 3 * 3)) - 7010006310925 / 171721308410023) +
          1 / 2 * (log 3 - 12397791320721 / 11284955983654) +
        3 / 2 * (log 2 - 1148067618206 / 1656311459391) :=
    by
    rw [log_div, log_pow, log_mul, log_pow]
    · ring_nf
    all_goals norm_num
  rw [← sub_add_sub_cancel, this]
  apply (abs_add_four _ _ _ _).trans_lt _
  rw [abs_mul, abs_mul, abs_mul, abs_div, abs_div, abs_two, abs_one,
    abs_of_pos (by norm_num1 : (0 : ℝ) < 3),
    (by norm_num1 : (5 ^ 2 : ℝ) / (2 ^ 3 * 3) = 25 / 24)]
  have e₁ := mul_lt_mul_of_pos_left log_25_div_24_near (by norm_num1 : (0 : ℝ) < 1 / 2)
  have e₂ := mul_lt_mul_of_pos_left log_three_near_20 (by norm_num1 : (0 : ℝ) < 1 / 2)
  have e₃ := mul_lt_mul_of_pos_left log_two_near_20'' (by norm_num1 : (0 : ℝ) < 3 / 2)
  have e₄ :
      |1 / 2 * ((7010006310925 : ℝ) / 171721308410023) +
          1 / 2 * ((12397791320721 : ℝ) / 11284955983654) +
          3 / 2 * ((1148067618206 : ℝ) / 1656311459391) -
          (25218653206049 : ℝ) / 15669230239462| < 8 / 10 ^ 25 := by norm_num1
  nlinarith [e₁, e₂, e₃, e₄]

-- the proof does better than this
theorem log_five_gt_d20 : 1.609437912434100374 < log 5 :=
  (sub_lt_comm.1 (abs_sub_lt_iff.1 log_five_near).2).trans_le' (by norm_num1)

-- the proof does better than this
theorem log_five_lt_d20 : log 5 < 1.609437912434100375 :=
  lt_of_lt_of_le (sub_lt_iff_lt_add.1 (abs_sub_lt_iff.1 log_five_near).1) (by norm_num)

theorem log_8_div_7_near : |log (8 / 7) - 94488369352 / 707611652173| < 9 / 10 ^ 26 :=
  by
  have t : |(15⁻¹ : ℝ)| = 15⁻¹ := abs_of_pos (by norm_num1)
  have z := newbound (show |(15⁻¹ : ℝ)| < 1 by rw [t]; norm_num1) 11
  rw [t, _root_.abs_sub_comm] at z 
  norm_num1 at z 
  refine abs_sub_lt_of_approx z ?_
  simp_rw [sum_range_succ, sum_range_zero]
  norm_num1

theorem log_16_div_15_near : |log (16 / 15) - 2777280486178 / 43032911774627| < 7 / 10 ^ 28 :=
  by
  have t : |(31⁻¹ : ℝ)| = 31⁻¹ := abs_of_pos (by norm_num1)
  have z := newbound (show |(31⁻¹ : ℝ)| < 1 by rw [t]; norm_num1) 10
  rw [t, _root_.abs_sub_comm] at z 
  norm_num1 at z 
  refine abs_sub_lt_of_approx z ?_
  simp_rw [sum_range_succ, sum_range_zero]
  norm_num1

theorem log_33_div_32_near : |log (33 / 32) - 63667272858575 / 2069023108181113| < 3 / 10 ^ 31 :=
  by
  have t : |(65⁻¹ : ℝ)| = 65⁻¹ := abs_of_pos (by norm_num1)
  have z := newbound (show |(65⁻¹ : ℝ)| < 1 by rw [t]; norm_num1) 9
  rw [t, _root_.abs_sub_comm] at z 
  norm_num1 at z 
  refine abs_sub_lt_of_approx z ?_
  simp_rw [sum_range_succ, sum_range_zero]
  norm_num1

end Real
