/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.MetricSpace.CauSeqFilter
import Mathlib.Tactic

/-!
# Unconditional bounds on the central binomial coefficient from Stirling approximations
-/


noncomputable section

open scoped Topology Real Nat

open Finset Filter Nat Real

theorem centralBinom_ratio {α : Type*} [Field α] [CharZero α] (n : ℕ) :
    (centralBinom (n + 1) : α) / centralBinom n = 4 * ((n + 1 / 2) / (n + 1)) :=
  by
  rw [mul_div_assoc', mul_add, eq_div_iff, ← cast_add_one, div_mul_eq_mul_div, mul_comm, ← cast_mul,
    succ_mul_centralBinom_succ, cast_mul, mul_div_cancel_right₀]
  · rw [Nat.mul_add_one, ← mul_assoc, cast_add, cast_mul]
    norm_num1
    rfl
  · rw [Nat.cast_ne_zero]
    exact centralBinom_ne_zero _
  exact Nat.cast_add_one_ne_zero _

-- ((↑n + 7 / 3) * ↑n + 19 / 12) * ↑n + 1 / 3 ≤ ((↑n + 7 / 3) * ↑n + 5 / 3) * ↑n + 1 / 3

theorem upper_monotone_aux (n : ℕ) :
    ((n : ℝ) + 1 / 2) / (n + 1) ≤ Real.sqrt (n + 1 / 3) / Real.sqrt (n + 1 + 1 / 3) := by
  rw [← Real.sqrt_div]
  refine Real.le_sqrt_of_sq_le ?_
  rw [div_pow, div_le_div_iff₀]
  · ring_nf -- regression: this makes the goal look ugly,
    gcongr _ + _ * ?_ + _ + _
    norm_num1
  all_goals positivity

theorem lower_monotone_aux (n : ℕ) :
    Real.sqrt (n + 1 / 4) / Real.sqrt (n + 1 + 1 / 4) ≤ (n + 1 / 2) / (n + 1) := by
  rw [← Real.sqrt_div, sqrt_le_left, div_pow, div_le_div_iff₀]
  · ring_nf
    gcongr ?_ + _ + _ + _
    norm_num1
  all_goals positivity

/-- an explicit function of the central binomial coefficient which we will show is always less than
√π, to get a lower bound on the central binomial coefficient
-/
def centralBinomialLower (n : ℕ) : ℝ :=
  centralBinom n * Real.sqrt (n + 1 / 4) / (4 : ℝ) ^ n

theorem centralBinomialLower_monotone : Monotone centralBinomialLower := by
  refine monotone_nat_of_le_succ ?_
  intro n
  rw [centralBinomialLower, centralBinomialLower, _root_.pow_succ', ←div_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [le_div_iff₀, mul_assoc, mul_comm, ← div_le_div_iff₀, centralBinom_ratio, mul_comm,
    mul_div_assoc, Nat.cast_add_one]
  refine mul_le_mul_of_nonneg_left (lower_monotone_aux n) (by positivity)
  · positivity
  · rw [Nat.cast_pos]
    exact centralBinom_pos _
  · positivity

/-- an explicit function of the central binomial coefficient which we will show is always more than
√π, to get an upper bound on the central binomial coefficient
-/
def centralBinomialUpper (n : ℕ) : ℝ :=
  centralBinom n * Real.sqrt (n + 1 / 3) / (4 : ℝ) ^ n

theorem centralBinomialUpper_monotone : Antitone centralBinomialUpper :=
  by
  refine antitone_nat_of_succ_le ?_
  intro n
  rw [centralBinomialUpper, centralBinomialUpper, _root_.pow_succ', ← div_div]
    -- regression: I needed to qualify pow_succ
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [div_le_iff₀, mul_assoc, mul_comm _ (_ * _), ← div_le_div_iff₀, mul_comm, mul_div_assoc,
    centralBinom_ratio, Nat.cast_add_one]
  refine mul_le_mul_of_nonneg_left (upper_monotone_aux _) (by positivity)
  · rw [Nat.cast_pos]
    exact centralBinom_pos _
  · positivity
  · positivity

theorem centralBinom_limit :
    Tendsto (fun n => (centralBinom n : ℝ) * Real.sqrt n / (4 : ℝ) ^ n) atTop (𝓝 (√π)⁻¹) := by
  have := Real.pi_pos
  have : (sqrt π)⁻¹ = sqrt π / sqrt π ^ 2 := by
    rw [inv_eq_one_div, sq, ← div_div, div_self]
    positivity
  rw [this]
  have : Tendsto (fun n => Stirling.stirlingSeq (2 * n)) atTop (𝓝 (sqrt π)) := by
    refine Tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi ?_
    exact tendsto_id.const_mul_atTop' two_pos
  refine (this.div (Stirling.tendsto_stirlingSeq_sqrt_pi.pow 2) (by positivity)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  dsimp
  rw [Stirling.stirlingSeq, Stirling.stirlingSeq, centralBinom, two_mul n, cast_add_choose,
    ←two_mul]
  field_simp
  ring_nf
  rw [sq_sqrt, cast_mul, sqrt_mul, sqrt_mul, ← mul_assoc]
  ring_nf -- this was a 7 line rw proof in Lean 3, this one is more principled but hmmm
  rw [sq_sqrt, sq_sqrt, mul_comm n 2, pow_mul (2 : ℝ)]
  ring_nf
  all_goals positivity

theorem centralBinomialUpper_limit : Tendsto centralBinomialUpper atTop (𝓝 (√π)⁻¹) :=
  by
  have : (sqrt π)⁻¹ = (sqrt π)⁻¹ / Real.sqrt 1 := by rw [Real.sqrt_one, div_one]
  have h : Real.sqrt 1 ≠ 0 := sqrt_ne_zero'.2 zero_lt_one
  rw [this]
  refine (centralBinom_limit.div (tendsto_natCast_div_add_atTop (1 / 3 : ℝ)).sqrt h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  dsimp
  rw [sqrt_div (Nat.cast_nonneg _), centralBinomialUpper, div_div, mul_div_assoc',
    div_div_eq_mul_div, mul_right_comm, mul_div_mul_right]
  · positivity

theorem centralBinomialLower_limit : Tendsto centralBinomialLower atTop (𝓝 (√π)⁻¹) := by
  have : (√π)⁻¹ = (√π)⁻¹ / Real.sqrt 1 := by rw [Real.sqrt_one, div_one]
  have h : Real.sqrt 1 ≠ 0 := sqrt_ne_zero'.2 zero_lt_one
  rw [this]
  refine (centralBinom_limit.div (tendsto_natCast_div_add_atTop (1 / 4 : ℝ)).sqrt h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  dsimp
  rw [sqrt_div (Nat.cast_nonneg _), centralBinomialLower, div_div, mul_div_assoc',
    div_div_eq_mul_div, mul_right_comm, mul_div_mul_right]
  · positivity

theorem centralBinomialUpper_bound (n : ℕ) :
    n.centralBinom ≤ 4 ^ n / √(π * (n + 1 / 4)) := by
  have := pi_pos
  have := centralBinomialLower_monotone.ge_of_tendsto centralBinomialLower_limit n
  rwa [sqrt_mul, ← div_div, le_div_iff₀, div_eq_mul_one_div ((4 : ℝ) ^ n : ℝ), ← div_le_iff₀',
    one_div (sqrt π)]
  all_goals positivity

theorem centralBinomialLower_bound (n : ℕ) :
    4 ^ n / √(π * (n + 1 / 3)) ≤ n.centralBinom := by
  have := pi_pos
  have := centralBinomialUpper_monotone.le_of_tendsto centralBinomialUpper_limit n
  rwa [sqrt_mul, ← div_div, div_le_iff₀, div_eq_mul_one_div, ← le_div_iff₀', one_div (sqrt π)]
  all_goals positivity

theorem cexp_eq_tsum {x : ℂ} : Complex.exp x = ∑' i, x ^ i / i ! := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

theorem rexp_eq_tsum {x : ℝ} : Real.exp x = ∑' i, x ^ i / i ! := by
  rw [exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

lemma exp_factorial_bound {x : ℝ} (hx : 0 ≤ x) {n : ℕ} : x ^ n / n ! ≤ exp x := by
  rw [exp_eq_exp_ℝ]
  exact le_hasSum (NormedSpace.expSeries_div_hasSum_exp x) n (fun _ _ => by positivity)

theorem exp_factorial_bound_of_ne_zero {n : ℕ} {x : ℝ} (hx : 0 ≤ x) (hn : n ≠ 0) :
    x ^ n / n ! < exp x := by
  rw [exp_eq_exp_ℝ]
  refine (sum_le_hasSum {n, 0} ?_ (NormedSpace.expSeries_div_hasSum_exp x)).trans_lt' ?_
  · intro x _
    positivity
  rw [sum_pair hn]
  simp

theorem factorial_bound_exp {n : ℕ} : (n / Real.exp 1) ^ n ≤ n ! := by
  rw [div_pow, ← rpow_natCast (exp 1), exp_one_rpow, div_le_iff₀, ← div_le_iff₀']
  · exact exp_factorial_bound (Nat.cast_nonneg _)
  · positivity
  · positivity

theorem factorial_bound_exp_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (n / Real.exp 1) ^ n < n ! := by
  rw [div_pow, ← rpow_natCast (exp 1), exp_one_rpow, div_lt_iff₀, ← div_lt_iff₀']
  · exact exp_factorial_bound_of_ne_zero (Nat.cast_nonneg _) hn
  · positivity
  · positivity

theorem choose_upper_bound {n t : ℕ} : n.choose t ≤ (exp 1 * n / t) ^ t := by
  cases' Nat.eq_zero_or_pos t with h h
  · simp [h]
  refine (Nat.choose_le_pow_div t n).trans ?_
  refine (div_le_div_of_nonneg_left ?_ ?_ factorial_bound_exp).trans ?_
  · positivity
  · positivity
  rw [← div_pow, div_div_eq_mul_div, mul_comm]

theorem choose_upper_bound_of_pos {n t : ℕ} (hn : n ≠ 0) (ht : t ≠ 0) :
    n.choose t < (exp 1 * n / t) ^ t := by
  refine (Nat.choose_le_pow_div t n).trans_lt ?_
  refine (div_lt_div_of_pos_left ?_ ?_ (factorial_bound_exp_of_ne_zero ht)).trans_eq ?_
  · positivity
  · positivity
  rw [← div_pow, div_div_eq_mul_div, mul_comm]

theorem choose_upper_bound' {n t : ℕ} : n.choose t ≤ exp t * (n / t) ^ t :=
  choose_upper_bound.trans_eq <| by rw [mul_div_assoc, mul_pow, ← exp_one_rpow t, rpow_natCast]
