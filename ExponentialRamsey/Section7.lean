/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.MeanInequalities
import ExponentialRamsey.Section6

/-!
# Section 7
-/

namespace SimpleGraph

open scoped BigOperators ExponentialRamsey

open Filter _root_.Finset Nat Real Asymptotics

variable {V : Type*} [DecidableEq V] [Fintype V] {χ : TopEdgeLabelling V (Fin 2)}

variable {k l : ℕ} {ini : BookConfig χ} {i : ℕ}

local syntax "X_" term:max : term
macro_rules
  | `(X_ $i) =>
      `((algorithm $(Lean.mkIdent `μ) $(Lean.mkIdent `k) $(Lean.mkIdent `l)
          $(Lean.mkIdent `ini) $i).X)

local syntax "p_" term:max : term
macro_rules
  | `(p_ $i) =>
      `((algorithm $(Lean.mkIdent `μ) $(Lean.mkIdent `k) $(Lean.mkIdent `l)
          $(Lean.mkIdent `ini) $i).p)

local syntax "h_" term:max : term
macro_rules
  | `(h_ $p) => `(height $(Lean.mkIdent `k) $(Lean.mkIdent `ini).p $p)

local syntax "ℛ" : term
macro_rules
  | `(ℛ) =>
      `(redSteps $(Lean.mkIdent `μ) $(Lean.mkIdent `k) $(Lean.mkIdent `l) $(Lean.mkIdent `ini))

local syntax "ℬ" : term
macro_rules
  | `(ℬ) =>
      `(bigBlueSteps $(Lean.mkIdent `μ) $(Lean.mkIdent `k) $(Lean.mkIdent `l) $(Lean.mkIdent `ini))

local syntax "𝒮" : term
macro_rules
  | `(𝒮) =>
      `(densitySteps $(Lean.mkIdent `μ) $(Lean.mkIdent `k) $(Lean.mkIdent `l) $(Lean.mkIdent `ini))

local syntax "𝒟" : term
macro_rules
  | `(𝒟) =>
      `(degreeSteps $(Lean.mkIdent `μ) $(Lean.mkIdent `k) $(Lean.mkIdent `l) $(Lean.mkIdent `ini))

local syntax "t" : term
macro_rules
  | `(t) =>
      `((redSteps $(Lean.mkIdent `μ) $(Lean.mkIdent `k) $(Lean.mkIdent `l)
          $(Lean.mkIdent `ini)).card)

local syntax "s" : term
macro_rules
  | `(s) =>
      `((densitySteps $(Lean.mkIdent `μ) $(Lean.mkIdent `k) $(Lean.mkIdent `l)
          $(Lean.mkIdent `ini)).card)

local syntax "ε" : term
macro_rules
  | `(ε) => `((($(Lean.mkIdent `k) : ℝ) ^ (-1 / 4 : ℝ)))

theorem seven_two_single (μ₁ : ℝ) (hμ₁ : μ₁ < 1) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ ≤ μ₁ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                    ∀ ini : BookConfig χ,
                      ∀ i ∈ redSteps μ k l ini,
                        2 ^ (-2 * (1 / ((1 - μ) * k))) * (1 - μ) ≤
                          ((X_ (i + 1)).card : ℝ) / (X_ i).card := by
  have h34 : (0 : ℝ) < 3 / 4 := by norm_num1
  have tt : Tendsto (Nat.cast : ℕ → ℝ) _ _ := tendsto_natCast_atTop_atTop
  have := (tendsto_nat_ceil_atTop.comp (tendsto_rpow_atTop h34)).comp tt
  filter_upwards [top_adjuster (tt.eventually_gt_atTop 0),
    top_adjuster (tt.eventually_ge_atTop (2 * (1 / (1 - μ₁)))), this.eventually_ge_atTop 2] with l
    hk₀ hk₁ hk₂ k hlk μ hμu n χ hχ ini i hi
  have hi' : i < finalStep μ k l ini :=
    by
    have := redSteps_subset_redOrDensitySteps hi
    rw [redOrDensitySteps, mem_filter, mem_range] at this
    exact this.1
  rw [le_div_iff₀]
  swap
  · rw [Nat.cast_pos, card_pos]
    exact x_nonempty hi'
  rw [red_applied hi, BookConfig.redStepBasic_x, card_red_neighbors_inter]
  have :
    (1 - μ) * (algorithm μ k l ini i).X.card - 1 ≤
      (1 - blueXRatio μ k l ini i) * (algorithm μ k l ini i).X.card - 1 :=
    by
    rw [sub_le_sub_iff_right]
    refine' mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [sub_le_sub_iff_left]
    exact blueXRatio_le_mu (redSteps_subset_redOrDensitySteps hi)
  refine' this.trans' _
  have : (2 : ℝ) ^ (-2 * (1 / ((1 - μ) * k))) ≤ 1 - 1 / ((1 - μ) * k) :=
    by
    refine' two_approx _ _
    · rw [one_div_nonneg]
      exact mul_nonneg (sub_nonneg_of_le (hμu.trans hμ₁.le)) (Nat.cast_nonneg _)
    rw [← div_div, le_div_iff₀', mul_div_assoc', div_le_iff₀, one_mul]
    · refine' (hk₁ k hlk).trans' _
      exact
        mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (sub_pos_of_lt hμ₁) (sub_le_sub_left hμu _)) zero_lt_two.le
    · exact hk₀ k hlk
    · exact two_pos
  rw [mul_assoc]
  refine' (mul_le_mul_of_nonneg_right this _).trans _
  · exact mul_nonneg (sub_nonneg_of_le (hμu.trans hμ₁.le)) (Nat.cast_nonneg _)
  rw [one_sub_mul, sub_le_sub_iff_left, mul_comm, mul_one_div, mul_div_mul_left, one_le_div,
    Nat.cast_le]
  · refine' (ramseyNumber_lt_of_lt_finalStep hi').le.trans' _
    refine' (ramseyNumber.mono_two le_rfl hk₂).trans_eq' _
    rw [ramseyNumber_two_right]
  · exact hk₀ k hlk
  exact ne_of_gt (sub_pos_of_lt (hμu.trans_lt hμ₁))

theorem seven_two (μ₁ : ℝ) (hμ₁ : μ₁ < 1) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k,
            l ≤ k →
              ∀ μ,
                μ ≤ μ₁ →
                  ∀ n : ℕ,
                    ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                      (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                            χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                        ∀ ini : BookConfig χ,
                          2 ^ f k * (1 - μ) ^ (redSteps μ k l ini).card ≤
                            ∏ i ∈ redSteps μ k l ini,
                              ((algorithm μ k l ini (i + 1)).X.card : ℝ) /
                                (algorithm μ k l ini i).X.card := by
  refine' ⟨fun k => -2 / (1 - μ₁) * 1, _, _⟩
  · refine' IsLittleO.const_mul_left _ _
    suffices (fun k : ℝ => (1 : ℝ)) =o[atTop] fun x : ℝ => x by
      exact this.comp_tendsto tendsto_natCast_atTop_atTop
    simpa only [rpow_one] using isLittleO_one_rpow zero_lt_one
  filter_upwards [seven_two_single μ₁ hμ₁, top_adjuster (eventually_gt_atTop 0)] with l hl hk₀ k
    hlk μ hμu n χ hχ ini
  refine' (Finset.prod_le_prod _ (hl k hlk μ hμu n χ hχ ini)).trans' _
  · intro i hi
    exact mul_nonneg (rpow_nonneg (by norm_num1) _) (sub_nonneg_of_le (hμu.trans hμ₁.le))
  rw [prod_const, mul_pow]
  refine' mul_le_mul_of_nonneg_right _ (pow_nonneg (sub_pos_of_lt (hμu.trans_lt hμ₁)).le _)
  rw [← rpow_natCast, ← rpow_mul]
  swap
  · norm_num1
  refine' rpow_le_rpow_of_exponent_le (by norm_num1) _
  rw [← one_div_mul_one_div, ← mul_assoc, mul_right_comm, mul_one_div, mul_one_div, mul_div_assoc]
  refine' mul_le_mul_of_nonpos_of_nonneg _ (div_le_one_of_le₀ _ (Nat.cast_nonneg _)) _ zero_le_one
  · rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by norm_num1) (sub_pos_of_lt hμ₁) (sub_le_sub_left hμu _)
  · rw [Nat.cast_le]
    exact four_four_red μ hχ ini
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_pos_of_lt (hμu.trans_lt hμ₁)).le

theorem seven_three_aux_one {μ : ℝ} {m : ℕ} (hm : m ≤ finalStep μ k l ini) :
    ∑ i ∈ ℬ ∩ range m, (BookConfig.getBook χ μ (algorithm μ k l ini i).X).1.card +
        (densitySteps μ k l ini ∩ range m).card ≤
      (algorithm μ k l ini m).B.card := by
  induction' m with m ih
  · simp
  rw [range_add_one]
  rw [Nat.succ_le_iff] at hm
  rcases cases_of_lt_finalStep hm with (hir | hib | his | hid)
  · rw [inter_insert_of_notMem, inter_insert_of_notMem, red_applied hir,
      BookConfig.redStepBasic_b]
    · exact ih hm.le
    · exact Finset.disjoint_left.1 redSteps_disjoint_densitySteps hir
    refine' Finset.disjoint_right.1 bigBlueSteps_disjoint_redOrDensitySteps _
    exact redSteps_subset_redOrDensitySteps hir
  · rw [inter_insert_of_mem hib, inter_insert_of_notMem, big_blue_applied hib, sum_insert,
      add_assoc, BookConfig.bigBlueStep_b, card_union_of_disjoint, add_comm, add_le_add_iff_right]
    · exact ih hm.le
    · exact (algorithm μ k l ini m).hXB.symm.mono_right BookConfig.getBook_fst_subset
    · simp
    · intro h
      refine' Finset.disjoint_right.1 bigBlueSteps_disjoint_redOrDensitySteps _ hib
      exact densitySteps_subset_redOrDensitySteps h
  · rw [inter_insert_of_notMem, inter_insert_of_mem his, card_insert_of_notMem,
      density_applied his, BookConfig.densityBoostStepBasic_b, card_insert_of_notMem, ←
      add_assoc, add_le_add_iff_right]
    · exact ih hm.le
    · refine' Finset.disjoint_left.1 (algorithm μ k l ini m).hXB _
      exact BookConfig.getCentralVertex_mem_x _ _ _
    · simp
    refine' Finset.disjoint_right.1 bigBlueSteps_disjoint_redOrDensitySteps _
    exact densitySteps_subset_redOrDensitySteps his
  · have :=
      Finset.disjoint_left.1 degreeSteps_disjoint_bigBlueSteps_union_redOrDensitySteps hid
    rw [mem_union, not_or] at this
    rw [inter_insert_of_notMem this.1, inter_insert_of_notMem, degree_regularisation_applied hid,
      BookConfig.degreeRegularisationStep_b]
    · exact ih hm.le
    intro h
    exact this.2 (densitySteps_subset_redOrDensitySteps h)

theorem seven_three_aux_two {μ : ℝ} :
    ∑ i ∈ ℬ, (BookConfig.getBook χ μ (X_ i)).1.card + s ≤ (endState μ k l ini).B.card := by
  refine' (seven_three_aux_one le_rfl).trans' _
  rw [inter_eq_left.2, inter_eq_left.2]
  · exact densitySteps_subset_redOrDensitySteps.trans (filter_subset _ _)
  · exact filter_subset _ _

theorem seven_three_aux_three {μ : ℝ}
    (hχ : ¬∃ (m : Finset V) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) :
    ∑ i ∈ bigBlueSteps μ k l ini, (BookConfig.getBook χ μ (X_ i)).1.card + s < l := by
  refine' seven_three_aux_two.trans_lt _
  by_contra! hl
  refine' hχ ⟨_, _, (endState μ k l ini).blue_b, _⟩
  simpa using hl

theorem s_lt_l {μ : ℝ}
    (hχ : ¬∃ (m : Finset V) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) :
    (densitySteps μ k l ini).card < l :=
  (seven_three_aux_three hχ).trans_le' le_add_self

theorem seven_three :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ μ₁ : ℝ,
          0 < μ₀ →
            μ₁ < 1 →
              ∀ᶠ l : ℕ in atTop,
                ∀ k,
                  l ≤ k →
                    ∀ μ,
                      μ₀ ≤ μ →
                        μ ≤ μ₁ →
                          ∀ n : ℕ,
                            ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                              (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                    χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                ∀ ini : BookConfig χ,
                                  2 ^ f k * μ ^ (l - (densitySteps μ k l ini).card) ≤
                                    ∏ i ∈ bigBlueSteps μ k l ini,
                                      ((algorithm μ k l ini (i + 1)).X.card : ℝ) /
                                        (algorithm μ k l ini i).X.card := by
  have tt : Tendsto (Nat.cast : ℕ → ℝ) _ _ := tendsto_natCast_atTop_atTop
  refine' ⟨fun k => -k ^ (3 / 4 : ℝ), _, _⟩
  · suffices (fun k : ℝ => -k ^ (3 / 4 : ℝ)) =o[atTop] fun x : ℝ => x by exact this.comp_tendsto tt
    refine' IsLittleO.neg_left _
    simpa only [rpow_one] using isLittleO_rpow_rpow (by norm_num : (3 / 4 : ℝ) < 1)
  intro μ₀ μ₁ hμ₀ hμ₁
  filter_upwards [four_three hμ₀] with l hl k hlk μ hμl hμu n χ hχ ini
  have :
    ∀ i ∈ bigBlueSteps μ k l ini,
      μ ^ (BookConfig.getBook χ μ (algorithm μ k l ini i).X).1.card / 2 ≤
        ((algorithm μ k l ini (i + 1)).X.card : ℝ) / (algorithm μ k l ini i).X.card :=
    by
    intro i hi
    rw [big_blue_applied hi, BookConfig.bigBlueStep_x, le_div_iff₀, div_mul_eq_mul_div]
    · exact BookConfig.getBook_relative_card
    rw [Nat.cast_pos, card_pos]
    refine' x_nonempty _
    rw [bigBlueSteps, mem_filter, mem_range] at hi
    exact hi.1
  refine' (prod_le_prod _ this).trans' _
  · intro i hi
    exact div_nonneg (pow_nonneg (hμ₀.le.trans hμl) _) two_pos.le
  rw [prod_div_distrib, prod_pow_eq_pow_sum, prod_const, div_eq_mul_inv (_ ^ _), ← rpow_natCast 2,
    ← rpow_neg two_pos.le, mul_comm]
  refine'
    mul_le_mul (pow_le_pow_of_le_one (hμ₀.le.trans hμl) (hμu.trans hμ₁.le) _)
      (rpow_le_rpow_of_exponent_le one_le_two
        (neg_le_neg
          ((hl k hlk μ hμl n χ hχ ini).trans
            (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 hlk) (by norm_num1)))))
      (rpow_nonneg two_pos.le _) (pow_nonneg (hμ₀.le.trans hμl) _)
  exact le_tsub_of_add_le_right (seven_three_aux_three hχ).le

theorem height_p_zero {p₀ : ℝ} : height k p₀ p₀ = 1 :=
  height_eq_one le_rfl

/-- The set of moderate steps, S* -/
noncomputable def moderateSteps (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : Finset ℕ :=
  (densitySteps μ k l ini).filter fun i =>
    (height k ini.p (p_ (i + 1)) : ℝ) - height k ini.p (p_ i) ≤ k ^ (1 / 16 : ℝ)

local syntax "𝒮⁺" : term
macro_rules
  | `(𝒮⁺) =>
      `(moderateSteps $(Lean.mkIdent `μ) $(Lean.mkIdent `k) $(Lean.mkIdent `l) $(Lean.mkIdent `ini))

theorem range_filter_odd_eq_union {μ : ℝ} :
    (range (finalStep μ k l ini)).filter Odd =
      redSteps μ k l ini ∪ bigBlueSteps μ k l ini ∪ densitySteps μ k l ini := by
  ext i
  constructor
  · rw [mem_filter, mem_range, and_comm, and_imp]
    exact mem_union_of_odd
  rw [union_right_comm, redSteps_union_densitySteps, redOrDensitySteps, bigBlueSteps,
    ← filter_or, mem_filter, ← and_or_left, mem_filter,
    Nat.not_even_iff_odd, ← and_assoc]
  exact And.left

theorem sum_range_odd_telescope' {k : ℕ} (f : ℕ → ℝ) {c : ℝ} (hc' : ∀ i, f i - f 0 ≤ c) :
    ∑ i ∈ (range k).filter Odd, (f (i + 1) - f (i - 1)) ≤ c := by
  have :
      (range k).filter Odd =
        (range (k / 2)).map ⟨fun i => 2 * i + 1, fun i i' h => by
          dsimp at h
          omega⟩ :=
    by
    ext i
    simp only [mem_filter, mem_range, Finset.mem_map, odd_iff_exists_bit1,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hi, i, rfl⟩
      refine' ⟨i, _, rfl⟩
      suffices 2 * i + 1 < 2 * (k / 2) + 1 by omega
      refine' hi.trans_le _
      rcases Nat.even_or_odd k with hk | hk
      · rw [Nat.two_mul_div_two_of_even hk]
        simp
      rw [Nat.two_mul_div_two_add_one_of_odd hk]
    rintro ⟨i, hi, rfl⟩
    refine' ⟨_, i, rfl⟩
    have hle : 2 * (i + 1) ≤ k :=
      (Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hi)).trans (Nat.mul_div_le k 2)
    omega
  rw [this, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have : ∀ x, f (2 * x + 1 + 1) - f (2 * x + 1 - 1) = f (2 * (x + 1)) - f (2 * x) := by
    intro x
    rw [show 2 * x + 1 + 1 = 2 * (x + 1) by omega, Nat.add_sub_cancel]
  simp only [this]
  rw [sum_range_sub fun x => f (2 * x)]
  dsimp
  exact hc' _

theorem sum_range_odd_telescope {k : ℕ} (f : ℕ → ℝ) {c : ℝ} (hc' : ∀ i, f i ≤ c) (hc : 0 ≤ f 0) :
    ∑ i ∈ (range k).filter Odd, (f (i + 1) - f (i - 1)) ≤ c := by
  refine' sum_range_odd_telescope' _ _
  intro i
  exact (sub_le_self _ hc).trans (hc' _)

-- a merge of eqs 25 and 26
theorem eqn_25_26 :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                ∀ ini : BookConfig χ,
                  ∑ i ∈ (range (finalStep μ k l ini)).filter Odd,
                      (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) ≤
                    2 / ε * log k := by
  filter_upwards [top_adjuster height_upper_bound] with l hl k hlk μ n χ ini
  refine' sum_range_odd_telescope (fun i => h_ (algorithm μ k l ini i).p) _ _
  · intro i
    exact hl k hlk _ colDensity_nonneg _ colDensity_le_one
  exact Nat.cast_nonneg _

theorem eqn_25_26' :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ᶠ l : ℕ in atTop,
          ∀ k,
            l ≤ k →
              ∀ μ,
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    ∀ ini : BookConfig χ,
                      ∑ i ∈ (range (finalStep μ k l ini)).filter Odd,
                          (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) ≤
                        f k := by
  refine' ⟨fun k => 2 / ε * log k, _, eqn_25_26⟩
  simp only [div_mul_eq_mul_div, mul_div_assoc, neg_div]
  refine' IsLittleO.const_mul_left _ _
  simp only [rpow_neg (Nat.cast_nonneg _), div_inv_eq_mul]
  suffices (fun k : ℝ => log k * k ^ (1 / 4 : ℝ)) =o[atTop] fun x : ℝ => x by
    exact this.comp_tendsto tendsto_natCast_atTop_atTop
  refine'
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).mul_isBigO
          (isBigO_refl _ _)).congr'
      EventuallyEq.rfl _
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← rpow_add hx]
  norm_num

-- (28)
theorem height_diff_blue :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ : ℝ,
          0 < μ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k,
                l ≤ k →
                  ∀ μ,
                    μ₀ ≤ μ →
                      ∀ n : ℕ,
                        ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                          (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                            ∀ ini : BookConfig χ,
                              f k ≤
                                ∑ i ∈ bigBlueSteps μ k l ini,
                                  (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) := by
  refine' ⟨fun k => -2 * k ^ (1 / 8 : ℝ) * k ^ (3 / 4 : ℝ), _, _⟩
  · simp only [mul_assoc]
    refine' IsLittleO.const_mul_left _ _
    suffices (fun k : ℝ => k ^ (1 / 8 : ℝ) * k ^ (3 / 4 : ℝ)) =o[atTop] fun x : ℝ => x by
      exact this.comp_tendsto tendsto_natCast_atTop_atTop
    refine' IsLittleO.congr' (isLittleO_rpow_rpow (by norm_num : (7 / 8 : ℝ) < 1)) _ _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← rpow_add hx]
      norm_num
    simpa only [rpow_one] using EventuallyEq.rfl
  intro μ₀ hμ₀
  filter_upwards [four_three hμ₀, six_five_blue μ₀ hμ₀] with l hl₄₃ hl₆₅ k hlk μ hμl n χ hχ ini
  replace hl₄₃ : ((bigBlueSteps μ k l ini).card : ℝ) ≤ k ^ (3 / 4 : ℝ)
  · refine' (hl₄₃ k hlk μ hμl n χ hχ ini).trans _
    exact rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 hlk) (by norm_num1)
  replace hl₆₅ : ∀ i ∈ ℬ, (-2 : ℝ) * k ^ (1 / 8 : ℝ) ≤ h_ (p_ (i + 1)) - h_ (p_ (i - 1))
  · intro i hi
    rw [neg_mul, neg_le, neg_sub, sub_le_comm]
    exact hl₆₅ k hlk μ hμl n χ ini i hi
  refine' (card_nsmul_le_sum _ _ _ hl₆₅).trans' _
  rw [nsmul_eq_mul, mul_comm]
  refine' mul_le_mul_of_nonpos_right hl₄₃ _
  rw [neg_mul, Right.neg_nonpos_iff]
  positivity

theorem red_or_density_height_diff :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ : ℝ,
          0 < μ₀ →
            ∀ᶠ l : ℕ in atTop,
              ∀ k,
                l ≤ k →
                  ∀ μ,
                    μ₀ ≤ μ →
                      ∀ n : ℕ,
                        ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                          (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                            ∀ ini : BookConfig χ,
                              ∑ i ∈ redSteps μ k l ini ∪ densitySteps μ k l ini,
                                  (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) ≤
                                f k := by
  obtain ⟨f₁, hf₁, h'f₁⟩ := eqn_25_26'
  obtain ⟨f₂, hf₂, h'f₂⟩ := height_diff_blue
  refine' ⟨fun k => f₁ k - f₂ k, hf₁.sub hf₂, _⟩
  intro μ₀ hμ₀
  filter_upwards [h'f₁, h'f₂ μ₀ hμ₀] with l h₁ h₂ k hlk μ hμl n χ hχ ini
  clear h'f₁ h'f₂
  specialize h₁ k hlk μ n χ ini
  specialize h₂ k hlk μ hμl n χ hχ ini
  rw [range_filter_odd_eq_union, union_right_comm, redSteps_union_densitySteps,
    sum_union bigBlueSteps_disjoint_redOrDensitySteps.symm, ← redSteps_union_densitySteps, ←
    le_sub_iff_add_le] at h₁
  exact h₁.trans (sub_le_sub_left h₂ _)

theorem red_height_diff :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ : ℝ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    (-2 : ℝ) * k ≤
                      ∑ i ∈ redSteps μ k l ini, (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) := by
  filter_upwards [top_adjuster (eventually_gt_atTop 0), six_five_red, six_five_degree] with l hl₀
    hk hk' k hlk μ n χ hχ ini
  have := four_four_red μ hχ ini
  rw [← @Nat.cast_le ℝ] at this
  refine' (mul_le_mul_of_nonpos_left this (by norm_num1)).trans _
  rw [mul_comm, ← nsmul_eq_mul]
  refine' card_nsmul_le_sum _ _ _ _
  intro i hi
  obtain ⟨hi', hid⟩ := redSteps_sub_one_mem_degree hi
  rw [le_sub_iff_add_le', ← sub_eq_add_neg, ← Nat.cast_two]
  refine' Nat.cast_sub_le.trans _
  rw [Nat.cast_le]
  refine' (hk k hlk μ n χ ini i hi).trans' _
  refine' Nat.sub_le_sub_right _ _
  refine' (hk' k hlk μ n χ ini (i - 1) hid).trans_eq _
  rw [Nat.sub_add_cancel hi']

theorem density_height_diff (μ₁ p₀ : ℝ) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ ≤ μ₁ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                    ∀ ini : BookConfig χ,
                      p₀ ≤ ini.p →
                        ((𝒮 \ 𝒮⁺).card : ℝ) * k ^ (1 / 16 : ℝ) ≤
                          ∑ i ∈ 𝒮, (h_ (p_ (i + 1)) - h_ (p_ (i - 1)) : ℝ) := by
  filter_upwards [six_five_density μ₁ p₀ hμ₁ hp₀, six_five_degree] with l hl hl' k hlk μ hμu n χ hχ
    ini hini
  have : moderateSteps μ k l ini ⊆ densitySteps μ k l ini := filter_subset _ _
  rw [← sum_sdiff this, ← nsmul_eq_mul]
  have :
    (0 : ℝ) ≤
      ∑ i ∈ moderateSteps μ k l ini,
        ((height k ini.p (algorithm μ k l ini (i + 1)).p : ℝ) -
          height k ini.p (algorithm μ k l ini (i - 1)).p) :=
    by
    refine' sum_nonneg _
    intro i hi
    rw [sub_nonneg, Nat.cast_le]
    refine' (hl k hlk μ hμu n χ ini hini i (this hi)).trans' _
    obtain ⟨hi', hid⟩ := densitySteps_sub_one_mem_degree (this hi)
    refine' (hl' k hlk μ n χ ini _ hid).trans _
    rw [Nat.sub_add_cancel hi']
  refine' (le_add_of_nonneg_right this).trans' _
  refine' card_nsmul_le_sum _ _ _ _
  intro x hx
  rw [moderateSteps, ← filter_not, mem_filter, not_le] at hx
  refine' hx.2.le.trans (sub_le_sub_left _ _)
  obtain ⟨hi', hid⟩ := densitySteps_sub_one_mem_degree hx.1
  rw [Nat.cast_le]
  refine' (hl' k hlk μ n χ ini _ hid).trans _
  rw [Nat.sub_add_cancel hi']

theorem seven_five (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p → ((𝒮 \ 𝒮⁺).card : ℝ) ≤ 3 * k ^ (15 / 16 : ℝ) := by
  obtain ⟨f, hf', hf⟩ := red_or_density_height_diff
  filter_upwards [red_height_diff, density_height_diff μ₁ p₀ hμ₁ hp₀,
    top_adjuster (hf'.bound zero_lt_one), hf μ₀ hμ₀, top_adjuster (eventually_gt_atTop 0)] with l
    hr hb hf'' hrb hk' k hlk μ hμl hμu n χ hχ ini hini
  clear hf hf'
  specialize hr k hlk μ n χ hχ ini
  specialize hb k hlk μ hμu n χ hχ ini hini
  specialize hrb k hlk μ hμl n χ hχ ini
  specialize hf'' k hlk
  rw [one_mul, Real.norm_natCast, norm_eq_abs] at hf''
  replace hf'' := le_of_abs_le hf''
  rw [sum_union redSteps_disjoint_densitySteps] at hrb
  have := ((add_le_add hr hb).trans hrb).trans hf''
  rw [← le_sub_iff_add_le', neg_mul, sub_neg_eq_add, ← one_add_mul, add_comm, ← le_div_iff₀,
    mul_div_assoc, div_eq_mul_inv, ← rpow_neg (Nat.cast_nonneg k), mul_comm (k : ℝ), ←
    rpow_add_one] at this
  · refine' this.trans_eq _
    norm_num
  · rw [Nat.cast_ne_zero]
    exact (hk' k hlk).ne'
  refine' rpow_pos_of_pos _ _
  rw [Nat.cast_pos]
  exact hk' k hlk

/-- The parameter `β` of the algorithm. -/
noncomputable def beta (μ : ℝ) (k l : ℕ) (ini : BookConfig χ) : ℝ :=
  if 𝒮⁺ = ∅ then μ else (moderateSteps μ k l ini).card * (∑ i ∈ 𝒮⁺, 1 / blueXRatio μ k l ini i)⁻¹

theorem beta_prop {μ : ℝ} (hS : Finset.Nonempty 𝒮⁺) :
    1 / beta μ k l ini =
      1 / (moderateSteps μ k l ini).card * ∑ i ∈ 𝒮⁺, 1 / blueXRatio μ k l ini i := by
  rw [nonempty_iff_ne_empty] at hS
  rw [beta, if_neg hS, ← one_div_mul_one_div, one_div, one_div, inv_inv]

theorem beta_nonneg {μ : ℝ} (hμ₀ : 0 < μ) : 0 ≤ beta μ k l ini := by
  rw [beta]
  split_ifs
  · exact hμ₀.le
  refine' mul_nonneg (Nat.cast_nonneg _) (inv_nonneg_of_nonneg (sum_nonneg _))
  intro i hi
  rw [one_div]
  refine' inv_nonneg_of_nonneg _
  exact blueXRatio_nonneg

theorem beta_le_μ (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    ∀ ini : BookConfig χ, p₀ ≤ ini.p → beta μ k l ini ≤ μ := by
  filter_upwards [blueXRatio_pos μ₁ p₀ hμ₁ hp₀] with l hβ k hlk μ hμl hμu n χ ini hini
  rw [beta]
  split_ifs
  · rfl
  rw [← div_eq_mul_inv]
  refine' div_le_of_le_mul₀ (sum_nonneg _) (hμ₀.le.trans hμl) _
  · intro i hi
    rw [one_div]
    refine' inv_nonneg_of_nonneg _
    exact blueXRatio_nonneg
  rw [← div_le_iff₀' (hμ₀.trans_le hμl), div_eq_mul_one_div, ← nsmul_eq_mul]
  refine' card_nsmul_le_sum _ _ _ _
  intro i hi
  refine' one_div_le_one_div_of_le _ _
  · exact hβ k hlk μ hμu n χ ini hini _ (filter_subset _ _ hi)
  refine' blueXRatio_le_mu _
  refine' densitySteps_subset_redOrDensitySteps _
  exact filter_subset _ _ hi

theorem beta_le_one (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    ∀ ini : BookConfig χ, p₀ ≤ ini.p → beta μ k l ini < 1 := by
  filter_upwards [beta_le_μ μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl k hlk μ hμl hμu n χ ini hini
  exact (hl k hlk μ hμl hμu n χ ini hini).trans_lt (hμ₁.trans_le' hμu)

theorem my_ineq {α : Type*} {y : Finset α} (hy : y.Nonempty) {f : α → ℝ} (hf : ∀ i ∈ y, 0 < f i) :
    ((y.card : ℝ) * (∑ i ∈ y, 1 / f i)⁻¹) ^ y.card ≤ ∏ i ∈ y, f i := by
  have hy' : 0 < y.card := by rwa [card_pos]
  have hycard_ne : ((y.card : ℝ) ≠ 0) := Nat.cast_ne_zero.2 hy'.ne'
  simp only [one_div]
  rw [← inv_le_inv₀, ← prod_inv_distrib, ← rpow_natCast, ← inv_rpow, mul_inv, inv_inv, ←
    rpow_le_rpow_iff, ← rpow_mul]
  -- `mul_inv_cancel₀` cannot fire before the exponent is exposed, so state the shape it acts on
  change (∏ x ∈ y, (f x)⁻¹) ^ ((y.card : ℝ)⁻¹) ≤
    ((y.card : ℝ)⁻¹ * ∑ x ∈ y, (f x)⁻¹) ^ ((y.card : ℝ) * (y.card : ℝ)⁻¹)
  rw [mul_inv_cancel₀ hycard_ne, rpow_one, mul_sum,
    ← finset_prod_rpow y (fun x => (f x)⁻¹) fun i hi => inv_nonneg_of_nonneg (hf i hi).le]
  refine' geom_mean_le_arith_mean_weighted _ _ _ _ _ _
  · intros; positivity
  · simp only [sum_const, nsmul_eq_mul]
    rw [mul_inv_cancel₀]
    positivity
  · intro i hi
    have := hf i hi
    positivity
  · refine' mul_nonneg (by positivity) (sum_nonneg fun i hi => _)
    have := hf i hi
    positivity
  · refine' prod_nonneg fun i hi => _
    have := hf i hi
    positivity
  · refine' rpow_nonneg (mul_nonneg (by positivity) (sum_nonneg fun i hi => _)) _
    have := hf i hi
    positivity
  · positivity
  · refine' mul_nonneg (by positivity) (inv_nonneg_of_nonneg (sum_nonneg fun i hi => _))
    have := hf i hi
    positivity
  · refine' prod_pos hf
  · refine' pow_pos (mul_pos (by positivity) (inv_pos.2 (sum_pos (fun i hi => _) hy))) _
    have := hf i hi
    positivity

theorem seven_four :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ μ₁ p₀ : ℝ,
          0 < μ₀ →
            μ₁ < 1 →
              0 < p₀ →
                ∀ᶠ l : ℕ in atTop,
                  ∀ k,
                    l ≤ k →
                      ∀ μ,
                        μ₀ ≤ μ →
                          μ ≤ μ₁ →
                            ∀ n : ℕ,
                              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                      χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                  ∀ ini : BookConfig χ,
                                    p₀ ≤ ini.p →
                                      2 ^ f k * beta μ k l ini ^ s ≤
                                        ∏ i ∈ 𝒮,
                                          ((algorithm μ k l ini (i + 1)).X.card : ℝ) /
                                            (algorithm μ k l ini i).X.card := by
  refine' ⟨fun k => (log 2)⁻¹ * (log k * -2 * (3 * k ^ (15 / 16 : ℝ))), _, _⟩
  · refine' IsLittleO.const_mul_left _ _
    simp only [mul_left_comm]
    refine' IsLittleO.const_mul_left _ _
    simp only [mul_comm _ (-2 : ℝ), mul_assoc]
    refine' IsLittleO.const_mul_left _ _
    suffices (fun k : ℝ => log k * k ^ (15 / 16 : ℝ)) =o[atTop] fun x : ℝ => x by
      exact this.comp_tendsto tendsto_natCast_atTop_atTop
    refine'
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).mul_isBigO
            (isBigO_refl _ _)).congr'
        EventuallyEq.rfl _
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← rpow_add hx]
    norm_num
  intro μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀
  filter_upwards [seven_five μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_atTop 0),
    five_three_right μ₁ p₀ hμ₁ hp₀, beta_le_one μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    blueXRatio_pos μ₁ p₀ hμ₁ hp₀] with l hl hk₀ h₅₃ hβ hβ' k hlk μ hμl hμu n χ hχ ini hini
  specialize hl k hlk μ hμl hμu n χ hχ ini hini
  specialize h₅₃ k hlk μ hμu n χ ini hini
  rw [rpow_def_of_pos two_pos, mul_inv_cancel_left₀, mul_assoc, ← rpow_def_of_pos]
  rotate_left
  · rw [Nat.cast_pos]
    exact hk₀ k hlk
  · exact (log_pos one_lt_two).ne'
  have :
    ∀ i ∈ densitySteps μ k l ini,
      ((algorithm μ k l ini (i + 1)).X.card : ℝ) / (algorithm μ k l ini i).X.card =
        blueXRatio μ k l ini i :=
    by
    intro i hi
    rw [density_applied hi, BookConfig.densityBoostStepBasic_x,
      blueXRatio_eq (densitySteps_subset_redOrDensitySteps hi)]
  rw [prod_congr rfl this, rpow_mul (Nat.cast_nonneg k), rpow_neg (Nat.cast_nonneg k), rpow_two,
    ← one_div]
  have : moderateSteps μ k l ini ⊆ densitySteps μ k l ini := filter_subset _ _
  rw [← prod_sdiff this]
  have :
    ((1 : ℝ) / k ^ 2) ^ (3 * (k : ℝ) ^ (15 / 16 : ℝ)) ≤
      ∏ i ∈ densitySteps μ k l ini \ moderateSteps μ k l ini, blueXRatio μ k l ini i :=
    by
    refine' (Finset.prod_le_prod _ fun i hi => h₅₃ i _).trans' _
    · intro i hi
      rw [one_div_nonneg]
      exact pow_nonneg (Nat.cast_nonneg _) _
    · exact sdiff_subset hi
    rw [prod_const, ← rpow_natCast (_ / _)]
    refine' rpow_le_rpow_of_exponent_ge' _ _ (Nat.cast_nonneg _) hl
    · rw [one_div_nonneg]
      exact pow_nonneg (Nat.cast_nonneg _) _
    rw [one_div]
    refine' inv_le_one_of_one_le₀ _
    rw [one_le_sq_iff_one_le_abs, Nat.abs_cast, Nat.one_le_cast, Nat.succ_le_iff]
    exact hk₀ k hlk
  refine'
    mul_le_mul this _ (pow_nonneg (beta_nonneg (hμ₀.trans_le hμl)) _)
      (prod_nonneg fun i _ => blueXRatio_nonneg)
  have :
    beta μ k l ini ^ (densitySteps μ k l ini).card ≤
      beta μ k l ini ^ (moderateSteps μ k l ini).card :=
    by
    refine'
      pow_le_pow_of_le_one (beta_nonneg (hμ₀.trans_le hμl)) _
        (card_le_card (filter_subset _ _))
    exact (hβ _ hlk μ hμl hμu n χ ini hini).le
  refine' this.trans _
  rw [beta]
  split_ifs with h
  · rw [h, prod_empty, card_empty, pow_zero]
  refine' my_ineq (nonempty_iff_ne_empty.2 h) _
  intro i hi
  exact hβ' k hlk μ hμu n χ ini hini i (filter_subset _ _ hi)

theorem seven_seven_aux {α : Type*} [Fintype α] [DecidableEq α] {χ : TopEdgeLabelling α (Fin 2)}
    {p q : ℝ} {X0 X1 Y0 Y1 : Finset α} (hY : Y0 = Y1) (hp : p = colDensity χ 0 X0 Y0)
    (hY' : Y0.Nonempty)
    (h : X1 = X0.filter fun x => (p - q) * Y0.card ≤ (red_neighbors χ x ∩ Y0).card)
    (hX1 : X1.Nonempty) :
    ((X0 \ X1).card / X1.card : ℝ) * q ≤ colDensity χ 0 X1 Y1 - colDensity χ 0 X0 Y0 := by
  cases hY
  have hX : X1 ⊆ X0 := by
    rw [h]
    exact filter_subset _ _
  have : X0.Nonempty := by refine' Nonempty.mono hX hX1
  cases' Finset.eq_empty_or_nonempty (X0 \ X1) with h_1 hX01
  · have : X0 = X1 := by
      rw [sdiff_eq_empty_iff_subset] at h_1
      rwa [Finset.Subset.antisymm_iff, and_iff_right h_1]
    rw [h_1, card_empty, Nat.cast_zero, zero_div, MulZeroClass.zero_mul, this, sub_self]
  have e :
    red_density χ X0 Y0 * X0.card =
      red_density χ (X0 \ X1) Y0 * (X0 \ X1).card + red_density χ X1 Y0 * X1.card :=
    by
    rw [colDensity_eq_average, colDensity_eq_average, colDensity_eq_average,
      div_mul_cancel₀ _ ?_, div_mul_cancel₀ _ ?_, div_mul_cancel₀ _ ?_, sum_sdiff hX]
    · rwa [Nat.cast_ne_zero, ← pos_iff_ne_zero, card_pos]
    · rwa [Nat.cast_ne_zero, ← pos_iff_ne_zero, card_pos]
    · rwa [Nat.cast_ne_zero, ← pos_iff_ne_zero, card_pos]
  have : colDensity χ 0 (X0 \ X1) Y0 ≤ p - q :=
    by
    rw [colDensity_eq_average, div_le_iff₀', ← nsmul_eq_mul]
    rotate_left
    · rwa [Nat.cast_pos, card_pos]
    refine' sum_le_card_nsmul _ _ _ _
    intro x
    rw [h, ← filter_not, mem_filter, not_le]
    rintro ⟨_, h'⟩
    rw [div_le_iff₀]
    · exact h'.le
    rwa [Nat.cast_pos, card_pos]
  have := e.trans_le (add_le_add_left (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)) _)
  rw [div_mul_eq_mul_div, div_le_iff₀, cast_card_sdiff hX, sub_mul, sub_mul, ← hp]
  swap
  · rwa [Nat.cast_pos, card_pos]
  rw [← hp, cast_card_sdiff hX, sub_mul, mul_sub, mul_sub] at this
  linarith only [this]

theorem seven_seven' {μ : ℝ} (hi : i ∈ degreeSteps μ k l ini) (h : (X_ (i + 1)).Nonempty)
    (h' : (algorithm μ k l ini i).Y.Nonempty) :
    ((X_ i \ X_ (i + 1)).card / (X_ (i + 1)).card : ℝ) *
        (k ^ (1 / 8 : ℝ) * αFunction k (h_ (p_ i))) ≤
      p_ (i + 1) - p_ i := by
  refine' seven_seven_aux _ rfl h' _ h
  · rw [degree_regularisation_applied hi, BookConfig.degreeRegularisationStep_Y]
  · rw [degree_regularisation_applied hi, BookConfig.degreeRegularisationStep_x]
    rfl

theorem one_div_k_lt_p (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p → ∀ i, i ≤ finalStep μ k l ini → 1 / (k : ℝ) < p_ i := by
  have h : Tendsto (fun k : ℕ => (1 : ℝ) / k + 3 * k ^ (-1 / 4 : ℝ)) atTop (nhds (0 + 3 * 0)) :=
    by
    refine' Tendsto.add _ _
    · refine' tendsto_const_div_atTop_nhds_zero_nat _
    refine' Tendsto.const_mul _ _
    rw [neg_div]
    refine' (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop
    norm_num
  have : (0 : ℝ) + 3 * 0 < p₀ := by rwa [zero_add, MulZeroClass.mul_zero]
  filter_upwards [six_two μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (h.eventually (eventually_lt_nhds this))] with l hl hl' k hlk μ hμl hμu n χ hχ ini
    hini i hi
  refine' (hl k hlk μ hμl hμu n χ hχ ini hini i hi).trans_lt' _
  rw [lt_sub_iff_add_lt]
  refine' hini.trans_lt' _
  exact hl' k hlk

theorem x_y_nonempty (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          ∀ i,
                            i ≤ finalStep μ k l ini →
                              (algorithm μ k l ini i).X.Nonempty ∧
                                (algorithm μ k l ini i).Y.Nonempty := by
  filter_upwards [one_div_k_lt_p μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl k hlk μ hμl hμu n χ hχ ini hini i
    hi
  have : (0 : ℝ) ≤ 1 / k := by simp
  replace hl : 0 < colDensity _ _ _ _ := (hl k hlk μ hμl hμu n χ hχ ini hini i hi).trans_le' this
  constructor
  · refine' nonempty_of_ne_empty _
    intro h
    rw [h, colDensity_empty_left] at hl
    simp at hl
  · refine' nonempty_of_ne_empty _
    intro h
    rw [h, colDensity_empty_right] at hl
    simp at hl

theorem seven_seven (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          ∀ i,
                            i ∈ 𝒟 →
                              ((X_ i \ X_ (i + 1)).card / (X_ (i + 1)).card : ℝ) *
                                  (k ^ (1 / 8 : ℝ) * αFunction k (h_ (p_ i))) ≤
                                p_ (i + 1) - p_ i := by
  filter_upwards [x_y_nonempty μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl k hlk μ hμl hμu n χ hχ ini hini i hi
  refine' seven_seven' hi _ _
  · refine' (hl k hlk μ hμl hμu n χ hχ ini hini _ _).1
    rw [Nat.add_one_le_iff, ← mem_range]
    exact filter_subset _ _ hi
  refine' Y_nonempty _
  rw [← mem_range]
  exact filter_subset _ _ hi

theorem seven_eight (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          ∀ i : ℕ, i ∈ 𝒟 → ((X_ i).card : ℝ) / k ^ 2 ≤ (X_ (i + 1)).card := by
  have tt : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  have h : (0 : ℝ) < 1 / 8 + (-1 / 4 + 1) := by norm_num
  filter_upwards [seven_seven μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, top_adjuster (eventually_gt_atTop 0),
    top_adjuster (((tendsto_rpow_atTop h).comp tt).eventually_ge_atTop 2),
    x_y_nonempty μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (((tendsto_pow_atTop two_ne_zero).comp tt).eventually_ge_atTop 2)] with l hl hk₀
    hk₂ hX hk₂' k hlk μ hμl hμu n χ hχ ini hini i hi
  specialize hk₀ k hlk
  specialize hl k hlk μ hμl hμu n χ hχ ini hini i hi
  specialize hX k hlk μ hμl hμu n χ hχ ini hini
  have h' :
    (2 : ℝ) / k ^ 2 ≤ k ^ (1 / 8 : ℝ) * αFunction k (height k ini.p (algorithm μ k l ini i).p) :=
    by
    refine'
      (mul_le_mul_of_nonneg_left five_seven_left
            (rpow_nonneg (Nat.cast_nonneg _) _)).trans'
        _
    rw [div_le_iff₀, mul_assoc, div_mul_eq_mul_div, sq, ← mul_assoc, mul_div_cancel_right₀ _ ?_,
      ← rpow_add_one, ← rpow_add' (Nat.cast_nonneg _)]
    · exact hk₂ k hlk
    · norm_num1
    · rwa [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    · rwa [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    · refine' pow_pos _ _
      rwa [Nat.cast_pos]
  have : (algorithm μ k l ini (i + 1)).p - (algorithm μ k l ini i).p ≤ 1 :=
    (sub_le_self _ colDensity_nonneg).trans colDensity_le_one
  have := (mul_le_mul_of_nonneg_left h' (by positivity)).trans (hl.trans this)
  rw [div_mul_eq_mul_div, div_le_iff₀, one_mul] at this
  swap
  · rw [Nat.cast_pos, card_pos]
    refine' (hX _ _).1
    rw [Nat.add_one_le_iff, ← mem_range]
    exact filter_subset _ _ hi
  rw [cast_card_sdiff (x_subset _), sub_mul, sub_le_iff_le_add, mul_div_assoc', mul_comm,
    mul_div_assoc] at this
  swap
  · rw [← mem_range]
    exact filter_subset _ _ hi
  refine' le_of_mul_le_mul_left (this.trans _) two_pos
  rw [two_mul, add_le_add_iff_left]
  refine' mul_le_of_le_one_right (Nat.cast_nonneg _) _
  refine' div_le_one_of_le₀ _ (by positivity)
  exact hk₂' k hlk

theorem log_inequality {x a : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) : x * (log (1 + a) / a) ≤ log (1 + x) :=
  by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp [hxa.antisymm hx]
  set u := x * (log (1 + a) / a) with hu'
  have ha' : 0 < a := lt_of_le_of_ne' (hx.trans hxa) ha
  have ha'' : 0 < log (1 + a) := by
    refine' log_pos _
    simpa using ha'
  have hu : 0 ≤ u := mul_nonneg hx (div_nonneg ha''.le ha'.le)
  have : x * (log (1 + a) / a) ≤ log (1 + a) :=
    by
    rw [mul_div_assoc', div_le_iff₀' ha']
    refine' mul_le_mul_of_nonneg_right hxa ha''.le
  rw [le_log_iff_exp_le]
  swap
  · exact add_pos_of_pos_of_nonneg one_pos hx
  refine' (general_convex_thing hu this ha''.ne').trans_eq _
  rw [add_right_inj, exp_log, add_sub_cancel_left, hu', mul_div_assoc',
    mul_div_cancel₀ _ ha'.ne', mul_div_cancel_right₀ _ ha''.ne']
  exact add_pos_of_pos_of_nonneg one_pos ha'.le

theorem first_ineq : 3 / 4 ≤ log (1 + 1 / 2) / (1 / 2) := by
  rw [div_le_iff₀, div_mul_eq_mul_div, mul_div_assoc, mul_comm, ← log_rpow, le_log_iff_exp_le, ←
    exp_one_rpow]
  refine' (rpow_le_rpow (exp_pos _).le exp_one_lt_d9.le (by norm_num1)).trans _
  all_goals norm_num

theorem q_height_le_p {k : ℕ} {p₀ p : ℝ} (h' : p₀ ≤ p) : qFunction k p₀ (height k p₀ p - 1) ≤ p :=
  by
  rcases lt_or_eq_of_le (@one_le_height k p₀ p) with h | h
  · exact (q_height_lt_p h).le
  · rwa [h, Nat.sub_self, qFunction_zero]

theorem seven_nine_asymp :
    ∀ᶠ y : ℝ in nhds 0, 0 < y → (1 + y ^ 4) ^ (3 / 2 * y⁻¹) ≤ 1 + 2 * y ^ 3 := by
  have := eventually_le_nhds (by norm_num : (0 : ℝ) ^ 3 < 1 / 2 / 2)
  filter_upwards [(Tendsto.pow tendsto_id 3).eventually this] with y hy' hy
  have h₀ : 1 + y ^ 4 ≤ exp (y ^ 4) := by
    rw [add_comm]
    exact add_one_le_exp _
  have h₂ : 0 < 1 + y ^ 4 := by positivity
  refine' (rpow_le_rpow h₂.le h₀ (by positivity)).trans _
  have h₁ : 0 < 1 + 2 * y ^ 3 := by positivity
  rw [← exp_one_rpow, ← rpow_mul (exp_pos _).le, exp_one_rpow, ← le_log_iff_exp_le h₁, mul_comm,
    mul_assoc, pow_succ', inv_mul_cancel_left₀ hy.ne']
  have : 2 * y ^ 3 ≤ 1 / 2 := by
    rw [← le_div_iff₀']
    · exact hy'
    · exact two_pos
  refine' (log_inequality (by positivity) this).trans' _
  refine' (mul_le_mul_of_nonneg_left first_ineq (by positivity)).trans_eq' _
  ring

theorem seven_nine_inner :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ : ℝ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    ∀ i : ℕ,
                      i ∈ degreeSteps μ k l ini →
                        ini.p ≤ p_ i →
                          (h_ (p_ (i + 1)) : ℝ) ≤ h_ (p_ i) + k ^ (1 / 16 : ℝ) →
                            p_ (i + 1) - p_ i ≤ 2 * k ^ (1 / 16 : ℝ) * αFunction k (h_ (p_ i)) := by
  have tt : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  have h16 : (0 : ℝ) < 1 / 16 := by norm_num
  filter_upwards [top_adjuster (eventually_gt_atTop 0), six_five_degree,
    top_adjuster (((tendsto_rpow_atTop h16).comp tt).eventually_ge_atTop 2),
    top_adjuster (((tendsto_rpow_neg_atTop h16).comp tt).eventually seven_nine_asymp)] with l hk₀ hd
    hk16 hε k hlk μ n χ hχ ini i hi hp₁ hp₂
  specialize hk₀ k hlk
  have h₁ : p_ (i + 1) ≤ qFunction k ini.p (h_ (p_ (i + 1))) := height_spec hk₀.ne'
  have h₂ : qFunction k ini.p (h_ (p_ i) - 1) ≤ p_ i := q_height_le_p hp₁
  refine' (sub_le_sub h₁ h₂).trans _
  dsimp
  have :
    height k ini.p (algorithm μ k l ini i).p ≤ height k ini.p (algorithm μ k l ini (i + 1)).p :=
    hd k hlk μ n χ ini i hi
  have :
    qFunction k ini.p (height k ini.p (algorithm μ k l ini (i + 1)).p) -
        qFunction k ini.p (height k ini.p (algorithm μ k l ini i).p - 1) =
      ((1 + k ^ (-1 / 4 : ℝ)) ^ (h_ (p_ (i + 1)) - h_ (p_ i) + 1) - 1) / k ^ (-1 / 4 : ℝ) *
        αFunction k (h_ (p_ i)) :=
    by
    dsimp
    rw [αFunction, div_mul_div_comm, mul_left_comm, mul_div_mul_left, qFunction, qFunction,
      add_sub_add_left_eq_sub, ← sub_div, sub_sub_sub_cancel_right, sub_one_mul, ← pow_add,
      add_right_comm, ← add_tsub_assoc_of_le one_le_height, tsub_add_cancel_of_le this,
      tsub_add_cancel_of_le one_le_height]
    refine' (rpow_pos_of_pos _ _).ne'
    rwa [Nat.cast_pos]
  rw [this]
  refine' mul_le_mul_of_nonneg_right _ (α_nonneg _ _)
  clear this h₁ h₂
  dsimp
  have :
    (1 + (k : ℝ) ^ (-1 / 4 : ℝ)) ^ (h_ (p_ (i + 1)) - h_ (p_ i) + 1) ≤
      (1 + (k : ℝ) ^ (-1 / 4 : ℝ)) ^ (3 / 2 * (k : ℝ) ^ (1 / 16 : ℝ)) :=
    by
    rw [← rpow_natCast]
    refine' rpow_le_rpow_of_exponent_le _ _
    · simp only [le_add_iff_nonneg_right]
      positivity
    rw [Nat.cast_add_one, Nat.cast_sub this]
    rw [← sub_le_iff_le_add'] at hp₂
    rw [add_comm]
    refine' (add_le_add_right hp₂ _).trans _
    suffices 2 ≤ (k : ℝ) ^ (1 / 16 : ℝ) by linarith
    exact hk16 k hlk
  refine' (div_le_div_of_nonneg_right (sub_le_sub_right this _) (by positivity)).trans _
  rw [div_le_iff₀, sub_le_iff_le_add', mul_assoc, ← rpow_add]
  rotate_left
  · positivity
  · positivity
  set y : ℝ := k ^ (-(1 / 16) : ℝ) with hy
  convert_to (1 + y ^ 4) ^ (3 / 2 * y⁻¹) ≤ 1 + 2 * y ^ 3 using 3
  · rw [hy, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg _)]
    norm_num
  · rw [hy, rpow_neg (Nat.cast_nonneg _), inv_inv]
  · rw [hy, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg _)]
    norm_num
  refine' hε k hlk _
  exact rpow_pos_of_pos (Nat.cast_pos.2 hk₀) _

theorem seven_nine (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          ∀ i : ℕ,
                            i ∈ 𝒟 →
                              ini.p ≤ p_ i →
                                (h_ (p_ (i + 1)) : ℝ) ≤ h_ (p_ i) + k ^ (1 / 16 : ℝ) →
                                  (1 - 2 * k ^ (-1 / 16 : ℝ) : ℝ) * (X_ i).card ≤
                                    (X_ (i + 1)).card := by
  filter_upwards [seven_nine_inner, seven_seven μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_atTop 0), x_y_nonempty μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀] with l hl hl' hk₀ hX k
    hlk μ hμl hμu n χ hχ ini hini i hi h₁ h₂
  specialize hl k hlk μ n χ hχ ini i hi h₁ h₂
  specialize hl' k hlk μ hμl hμu n χ hχ ini hini i hi
  have hk₀' : 0 < k := hk₀ k hlk
  have : 0 < αFunction k (height k ini.p (algorithm μ k l ini i).p) :=
    by
    refine' five_seven_left.trans_lt' _
    positivity
  rw [← mul_assoc] at hl'
  have := le_of_mul_le_mul_right (hl'.trans hl) this
  have hi' : i < finalStep μ k l ini := by
    rw [← mem_range]
    exact filter_subset _ _ hi
  rw [div_mul_eq_mul_div, div_le_iff₀, ← le_div_iff₀, ← div_mul_eq_mul_div,
    cast_card_sdiff (x_subset hi')] at this
  rotate_left
  · positivity
  · rw [Nat.cast_pos, card_pos]
    exact (hX k hlk μ hμl hμu n χ hχ ini hini (i + 1) hi').1
  have z :
    (2 : ℝ) * k ^ (1 / 16 : ℝ) / k ^ (1 / 8 : ℝ) * (algorithm μ k l ini (i + 1)).X.card ≤
      (2 : ℝ) * k ^ (-1 / 16 : ℝ) * (algorithm μ k l ini i).X.card :=
    by
    rw [mul_div_assoc, ← rpow_sub]
    swap
    · rwa [Nat.cast_pos]
    norm_num1
    refine' mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Nat.cast_le]
    exact card_le_card (x_subset hi')
  replace this := this.trans z
  rwa [sub_le_comm, ← one_sub_mul] at this

theorem seven_ten (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          (((redOrDensitySteps μ k l ini).filter fun i =>
                                  (h_ (p_ (i - 1)) : ℝ) + k ^ (1 / 16 : ℝ) ≤ h_ (p_ i)).card :
                              ℝ) ≤
                            3 * k ^ (15 / 16 : ℝ) := by
  obtain ⟨f, hf', hf⟩ := red_or_density_height_diff
  filter_upwards [hf μ₀ hμ₀, top_adjuster (hf'.bound zero_lt_one), six_five_red, six_five_degree,
    six_five_density μ₁ p₀ hμ₁ hp₀, top_adjuster (eventually_gt_atTop 0)] with l hl hf'' hr hd hs
    hl₀ k hlk μ hμl hμu n χ hχ ini hini
  clear hf
  specialize hf'' k hlk
  specialize hr k hlk μ n χ ini
  specialize hd k hlk μ n χ ini
  specialize hs k hlk μ hμu n χ ini hini
  rw [one_mul, Real.norm_natCast, norm_eq_abs] at hf''
  replace hf'' := le_of_abs_le hf''
  replace hl := (hl k hlk μ hμl n χ hχ ini).trans hf''
  set q : ℕ → Prop := fun i =>
    (height k ini.p (algorithm μ k l ini (i - 1)).p : ℝ) + k ^ (1 / 16 : ℝ) ≤
      height k ini.p (algorithm μ k l ini i).p
  change (((redOrDensitySteps μ k l ini).filter q).card : ℝ) ≤ _
  have h₁ :
    (-2 : ℝ) * k ≤
      ∑ i ∈ redOrDensitySteps μ k l ini,
        ((height k ini.p (algorithm μ k l ini (i + 1)).p : ℝ) -
          height k ini.p (algorithm μ k l ini i).p) :=
    by
    have := four_four_red μ hχ ini
    rw [← @Nat.cast_le ℝ] at this
    refine' (mul_le_mul_of_nonpos_left this (by norm_num1)).trans _
    rw [mul_comm, ← nsmul_eq_mul, ← redSteps_union_densitySteps,
      sum_union redSteps_disjoint_densitySteps]
    refine' (le_add_of_nonneg_right _).trans' _
    · refine' sum_nonneg _
      intro i hi
      rw [sub_nonneg, Nat.cast_le]
      exact hs i hi
    refine' card_nsmul_le_sum _ _ _ _
    intro i hi
    obtain ⟨hi', hid⟩ := redSteps_sub_one_mem_degree hi
    rw [le_sub_iff_add_le', ← sub_eq_add_neg, ← Nat.cast_two]
    refine' Nat.cast_sub_le.trans _
    rw [Nat.cast_le]
    exact hr _ hi
  have h₂ :
    ((redOrDensitySteps μ k l ini).filter q).card • (k : ℝ) ^ (1 / 16 : ℝ) ≤
      ∑ i ∈ redOrDensitySteps μ k l ini,
        ((height k ini.p (algorithm μ k l ini i).p : ℝ) -
          height k ini.p (algorithm μ k l ini (i - 1)).p) :=
    by
    rw [← sum_filter_add_sum_filter_not _ q]
    refine' (le_add_of_nonneg_right _).trans' _
    · refine' sum_nonneg _
      intro i hi
      rw [sub_nonneg, Nat.cast_le]
      obtain ⟨hi', hid⟩ := redOrDensitySteps_sub_one_mem_degree (filter_subset _ _ hi)
      refine' (hd _ hid).trans_eq _
      rw [Nat.sub_add_cancel hi']
    refine' card_nsmul_le_sum _ _ _ _
    intro i hi
    rw [mem_filter] at hi
    rw [le_sub_iff_add_le']
    exact hi.2
  rw [redSteps_union_densitySteps] at hl
  have := add_le_add h₁ h₂
  simp only [← sum_add_distrib, sub_add_sub_cancel] at this
  replace this := this.trans hl
  rw [← le_sub_iff_add_le', neg_mul, sub_neg_eq_add, ← one_add_mul, add_comm, nsmul_eq_mul,
    ← le_div_iff₀, mul_div_assoc, div_eq_mul_inv (k : ℝ), ← rpow_neg (Nat.cast_nonneg k),
    mul_comm (k : ℝ), ← rpow_add_one] at this
  refine' this.trans_eq _
  · norm_num
  · rw [Nat.cast_ne_zero]
    exact (hl₀ k hlk).ne'
  refine' rpow_pos_of_pos _ _
  rw [Nat.cast_pos]
  exact hl₀ k hlk

/-- `q*` -/
noncomputable def qStar (k : ℕ) (p₀ : ℝ) : ℝ :=
  p₀ + k ^ (1 / 16 : ℝ) * αFunction k 1

theorem qStar_eq (k : ℕ) (p₀ : ℝ) : qStar k p₀ = p₀ + k ^ (-19 / 16 : ℝ) := by
  rcases k.eq_zero_or_pos with (rfl | hk)
  · norm_num [qStar]
  have hk' : 0 < (k : ℝ) := by positivity
  rw [qStar, add_right_inj, α_one, mul_div_assoc', ← rpow_add hk', ← rpow_sub_one hk'.ne']
  norm_num

theorem qStar_le_one : ∀ᶠ k : ℕ in atTop, ∀ inip, inip ≤ 1 → qStar k inip < 2 := by
  filter_upwards [eventually_gt_atTop 1] with k hk inip hinip
  rw [qStar_eq]
  refine'
    (add_lt_add_of_le_of_lt hinip
          (rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hk) (by norm_num1))).trans_eq
      (by norm_num)

theorem quick_calculation : 3 / 4 ≤ log (1 + 2 / 3) / (2 / 3) := by
  rw [le_div_iff₀, le_log_iff_exp_le, ← exp_one_rpow]
  norm_num1
  rw [← sqrt_eq_rpow, sqrt_le_left]
  refine' exp_one_lt_d9.le.trans _
  all_goals norm_num1

theorem height_qStar_le :
    ∀ᶠ k : ℕ in atTop, ∀ inip, (height k inip (qStar k inip) : ℝ) ≤ 2 * k ^ (1 / 16 : ℝ) := by
  have tt : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  have hh₁ : (0 : ℝ) < 1 / 16 := by norm_num
  have hh₂ : (0 : ℝ) < 1 / 4 := by norm_num
  have hh₃ : (0 : ℝ) < 2 / 3 := by norm_num
  have :=
    (((tendsto_rpow_atTop hh₁).const_mul_atTop (zero_lt_two' ℝ)).comp tt).eventually
      (eventually_le_floor (2 / 3) (by norm_num1))
  filter_upwards [((tendsto_rpow_atTop hh₁).comp tt).eventually_ge_atTop (1 / 2 : ℝ),
    eventually_ne_atTop 0, this,
    ((tendsto_rpow_neg_atTop hh₂).comp tt).eventually (eventually_le_nhds hh₃), qStar_le_one] with
    k hk hk₀ hk₂ hk₃ hq inip
  have hk' : (0 : ℝ) < k := by positivity
  dsimp at hk₂
  rw [← mul_assoc, div_mul_eq_mul_div] at hk₂
  rw [← Nat.le_floor_iff]
  swap
  · positivity
  refine' height_min _ _ _
  · exact hk₀
  · rw [ne_eq, Nat.floor_eq_zero, not_lt, ← div_le_iff₀' (zero_lt_two' ℝ)]
    exact hk
  rw [qFunction, qStar, add_le_add_iff_left, α_one, mul_div_assoc']
  refine' div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [le_sub_iff_add_le, ← rpow_natCast]
  refine' (rpow_le_rpow_of_exponent_le _ hk₂).trans' _
  · simp only [le_add_iff_nonneg_right]
    exact (rpow_pos_of_pos hk' _).le
  refine' (add_one_le_exp _).trans _
  rw [mul_comm, ← exp_one_rpow, rpow_mul, exp_one_rpow, rpow_mul]
  rotate_left
  · positivity
  · exact (exp_pos _).le
  refine' rpow_le_rpow (exp_pos _).le _ (rpow_nonneg (Nat.cast_nonneg _) _)
  rw [← le_log_iff_exp_le, log_rpow]
  rotate_left
  · positivity
  · positivity
  rw [← div_le_iff₀', div_div_eq_mul_div, mul_div_assoc]
  swap
  · norm_num
  have : (k : ℝ) ^ (-1 / 4 : ℝ) ≤ 2 / 3 := by rwa [neg_div]
  refine' (log_inequality (by positivity) this).trans' (mul_le_mul_of_nonneg_left _ (by positivity))
  -- the original's `bit1` normalisation left `3 / 4` here, Lean 4's leaves `3 / (2 * 2)`
  exact quick_calculation.trans_eq' (by norm_num1)

-- t ≤ k
-- - α_ (h(q*) + 2) * t ≥ - 2 α₁ * k
-- α_ (h(q*) + 2) * t ≤ 2 α₁ * k
-- α_ (h(q*) + 2) ≤ 2 α₁
-- (1 + ε) ^ (h(q*) + 1)  ≤ 2
-- (1 + ε) ^ (2 * ε^(-1/4) + 1) ≤ 2
-- exp (ε * (2 * ε^(-1/4) + 1)) ≤ 2
theorem min_simpler {x y z w : ℝ} (h : y - w ≤ x) (hw : 0 ≤ w) : -w ≤ min x z - min y z := by
  rcases min_cases x z with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
      rcases min_cases y z with (⟨h₃, h₄⟩ | ⟨h₃, h₄⟩) <;>
    linarith

theorem seven_eleven_red_termwise :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    ∀ i ∈ redSteps μ k l ini,
                      -αFunction k (height k ini.p (qStar k ini.p) + 2) ≤
                        min (p_ (i + 1)) (qStar k ini.p) - min (p_ i) (qStar k ini.p) := by
  filter_upwards [six_five_red, top_adjuster (eventually_ne_atTop 0)] with l h₁ h₀ k hlk μ n χ hχ
    ini i hi
  rcases le_or_gt (height k ini.p (p_ i)) (height k ini.p (qStar k ini.p) + 2) with h | h
  · refine' (min_simpler (six_four_red hi) (α_nonneg _ _)).trans' _
    exact neg_le_neg (α_increasing h)
  have := h₁ k hlk μ n χ ini i hi
  rw [← lt_tsub_iff_right] at h
  have h₁ : qStar k ini.p ≤ p_ (i + 1) := by
    by_contra! h'
    exact (h.trans_le this).not_ge (height_mono (h₀ k hlk) h'.le)
  have h₂ : qStar k ini.p ≤ p_ i := by
    by_contra! h'
    exact (h.trans_le (Nat.sub_le _ _)).not_ge (height_mono (h₀ k hlk) h'.le)
  rw [min_eq_right h₁, min_eq_right h₂, sub_self, Right.neg_nonpos_iff]
  exact α_nonneg _ _

theorem seven_eleven_red :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    -2 * αFunction k 1 * k ≤
                      ∑ i ∈ redSteps μ k l ini,
                        (min (p_ (i + 1)) (qStar k ini.p) - min (p_ i) (qStar k ini.p)) := by
  have h :
    Tendsto (fun k : ℝ => 2 * k ^ (-1 / 4 + 1 / 16 : ℝ) + k ^ (-1 / 4 : ℝ)) atTop
      (nhds (2 * 0 + 0)) :=
    by
    refine' (Tendsto.const_mul _ _).add _
    · norm_num1
      refine' tendsto_rpow_neg_atTop _
      norm_num
    · norm_num1
      refine' tendsto_rpow_neg_atTop _
      norm_num
  rw [MulZeroClass.mul_zero, add_zero] at h
  filter_upwards [top_adjuster height_qStar_le, seven_eleven_red_termwise,
    top_adjuster (eventually_gt_atTop 0),
    top_adjuster
      ((h.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_le_nhds (log_pos one_lt_two)))] with
    l hq hr h₀ h₁ k hlk μ n χ hχ ini
  refine' (card_nsmul_le_sum _ _ _ (hr k hlk μ n χ hχ ini)).trans' _
  rw [nsmul_eq_mul', neg_mul, neg_mul, neg_mul, neg_le_neg_iff]
  refine'
    mul_le_mul _ (Nat.cast_le.2 (four_four_red μ hχ ini)) (Nat.cast_nonneg _)
      (mul_nonneg zero_lt_two.le (α_nonneg _ _))
  rw [α_one, αFunction, mul_div_assoc', mul_comm, Nat.add_succ_sub_one]
  refine' div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right _ (by positivity))
    (Nat.cast_nonneg _)
  rw [add_comm]
  refine' (pow_le_pow_left₀ (by positivity) (add_one_le_exp _) _).trans _
  rw [← exp_one_rpow, ← rpow_natCast, ← rpow_mul (exp_pos _).le, Nat.cast_add_one, exp_one_rpow,
    ← le_log_iff_exp_le zero_lt_two]
  refine' (mul_le_mul_of_nonneg_left (add_le_add_left (hq k hlk ini.p) _) (by positivity)).trans _
  rw [mul_add_one, mul_left_comm, ← rpow_add]
  swap
  · exact Nat.cast_pos.2 (h₀ k hlk)
  exact h₁ k hlk

theorem seven_eleven_red_or_density (μ₁ p₀ : ℝ) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ ≤ μ₁ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                    ∀ ini : BookConfig χ,
                      p₀ ≤ ini.p →
                        -2 * αFunction k 1 * k ≤
                          ∑ i ∈ ℛ ∪ 𝒮,
                            (min (p_ (i + 1)) (qStar k ini.p) - min (p_ i) (qStar k ini.p)) := by
  filter_upwards [seven_eleven_red, six_four_density μ₁ p₀ hμ₁ hp₀] with l h₁ h₂ k hlk μ hμu n χ hχ
    ini hini
  rw [sum_union redSteps_disjoint_densitySteps]
  refine' (h₁ k hlk μ n χ hχ ini).trans _
  rw [le_add_iff_nonneg_right, sum_sub_distrib, sub_nonneg]
  refine' sum_le_sum _
  intro i hi
  refine' min_le_min _ le_rfl
  exact h₂ k hlk μ hμu n χ ini hini i hi

theorem seven_eleven_blue_termwise (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                    ∀ ini : BookConfig χ,
                      ∀ i ∈ ℬ,
                        -(k : ℝ) ^ (1 / 8 : ℝ) *
                            αFunction k
                              (height k ini.p (qStar k ini.p) + ⌊2 * (k : ℝ) ^ (1 / 8 : ℝ)⌋₊) ≤
                          min (p_ (i + 1)) (qStar k ini.p) - min (p_ (i - 1)) (qStar k ini.p) := by
  filter_upwards [six_five_blue μ₀ hμ₀, top_adjuster (eventually_gt_atTop 0)] with l h₁ h₀ k hlk μ
    hμl n χ hχ ini i hi
  have : (0 : ℝ) ≤ k ^ (1 / 8 : ℝ) := by positivity
  rcases
    le_or_gt (height k ini.p (p_ (i - 1)))
      (height k ini.p (qStar k ini.p) + ⌊2 * (k : ℝ) ^ (1 / 8 : ℝ)⌋₊) with h | h
  · refine' (min_simpler (six_four_blue (hμ₀.trans_le hμl) hi) _).trans' _
    · exact mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (α_nonneg _ _)
    rw [neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left (α_increasing h) (by positivity)
  have := h₁ k hlk μ hμl n χ ini i hi
  rw [add_comm, ← Nat.floor_add_natCast, Nat.floor_lt, ← lt_sub_iff_add_lt'] at h
  rotate_left
  · positivity
  · positivity
  have h₁ : qStar k ini.p ≤ p_ (i + 1) := by
    by_contra! h'
    refine' (h.trans_le this).not_ge _
    rw [Nat.cast_le]
    exact height_mono (h₀ k hlk).ne' h'.le
  have h₂ : qStar k ini.p ≤ p_ (i - 1) := by
    by_contra! h'
    refine' (h.trans_le (sub_le_self _ _)).not_ge _
    · positivity
    rw [Nat.cast_le]
    exact height_mono (h₀ k hlk).ne' h'.le
  rw [min_eq_right h₁, min_eq_right h₂, sub_self, neg_mul, Right.neg_nonpos_iff]
  exact mul_nonneg (by positivity) (α_nonneg _ _)

theorem seven_eleven_blue (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              ∀ n : ℕ,
                ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                  (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                        χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                    ∀ ini : BookConfig χ,
                      -αFunction k 1 * k ≤
                        ∑ i ∈ ℬ,
                          (min (p_ (i + 1)) (qStar k ini.p) - min (p_ (i - 1)) (qStar k ini.p)) :=
  by
  have h :
    Tendsto
      (fun k : ℝ => 2 * k ^ (1 / 16 + -1 / 4 : ℝ) + 2 * k ^ (1 / 8 + -1 / 4 : ℝ) - k ^ (-1 / 4 : ℝ))
      atTop (nhds (2 * 0 + 2 * 0 - 0)) :=
    by
    refine' ((Tendsto.const_mul _ _).add (Tendsto.const_mul _ _)).sub _
    · norm_num1
      refine' tendsto_rpow_neg_atTop _
      norm_num
    · norm_num1
      refine' tendsto_rpow_neg_atTop _
      norm_num
    · norm_num1
      refine' tendsto_rpow_neg_atTop _
      norm_num
  rw [MulZeroClass.mul_zero, add_zero, sub_zero] at h
  filter_upwards [top_adjuster height_qStar_le, seven_eleven_blue_termwise μ₀ hμ₀,
    top_adjuster (eventually_gt_atTop 0), top_adjuster (eventually_ge_atTop (2 ^ 8)),
    four_three hμ₀,
    top_adjuster
      ((h.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_le_nhds (log_pos one_lt_two)))] with
    l hq hr h₀ hk2 hb h₁ k hlk μ hμl n χ hχ ini
  refine' (card_nsmul_le_sum _ _ _ (hr k hlk μ hμl n χ hχ ini)).trans' _
  rw [nsmul_eq_mul', neg_mul, neg_mul, neg_mul, neg_le_neg_iff, mul_right_comm, mul_comm _ (k : ℝ)]
  refine' le_of_mul_le_mul_left _ two_pos
  rw [← mul_assoc, mul_left_comm _ _ (αFunction k 1), ← mul_assoc]
  have h' : (0 : ℝ) < k := by
    rw [Nat.cast_pos]
    exact h₀ k hlk
  have : 2 * (k : ℝ) ^ (1 / 8 : ℝ) * (bigBlueSteps μ k l ini).card ≤ k :=
    by
    have :=
      (hb k hlk μ hμl n χ hχ ini).trans
        (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 hlk) (by norm_num1))
    refine' (mul_le_mul_of_nonneg_left this _).trans _
    · positivity
    have : (2 : ℝ) ≤ k ^ (1 / 8 : ℝ) :=
      by
      refine' (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 (hk2 k hlk)) _).trans' _
      · norm_num1
      rw [Nat.cast_pow, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg 2)]
      norm_num1
    rw [mul_assoc, ← rpow_add h']
    refine' (mul_le_mul_of_nonneg_right this _).trans_eq _
    · exact rpow_nonneg (Nat.cast_nonneg _) _
    rw [← rpow_add h']
    norm_num
  refine' mul_le_mul this _ (α_nonneg _ _) (Nat.cast_nonneg _)
  rw [α_one, αFunction, mul_div_assoc', mul_comm]
  refine' div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right _ (by positivity))
    (Nat.cast_nonneg _)
  rw [add_comm]
  refine' (pow_le_pow_left₀ (by positivity) (add_one_le_exp _) _).trans _
  rw [← exp_one_rpow, ← rpow_natCast, ← rpow_mul (exp_pos _).le, exp_one_rpow, ←
    le_log_iff_exp_le zero_lt_two, Nat.cast_sub, Nat.cast_add, Nat.cast_one]
  swap
  · exact one_le_height.trans (Nat.le_add_right _ _)
  refine'
    (mul_le_mul_of_nonneg_left (sub_le_sub_right (add_le_add (hq k hlk ini.p) (Nat.floor_le _)) _)
          _).trans
      _
  · exact mul_nonneg two_pos.le (rpow_nonneg (Nat.cast_nonneg _) _)
  · exact rpow_nonneg (Nat.cast_nonneg _) _
  rw [mul_comm, sub_one_mul, add_mul, mul_assoc, mul_assoc, ← rpow_add h', ← rpow_add h']
  exact h₁ k hlk

theorem seven_eleven_red_or_density_other :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            ∀ n : ℕ,
              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                (¬∃ (m : Finset (Fin n)) (c : Fin 2), χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                  ∀ ini : BookConfig χ,
                    (k : ℝ) ^ (1 / 16 : ℝ) * αFunction k 1 *
                        (((redOrDensitySteps μ k l ini).filter fun i =>
                              (p_ (i - 1) : ℝ) + k ^ (1 / 16 : ℝ) * αFunction k 1 ≤ p_ i ∧
                                p_ (i - 1) ≤ ini.p).card :
                          ℝ) ≤
                      ∑ i ∈ ℛ ∪ 𝒮,
                        (min (p_ i) (qStar k ini.p) - min (p_ (i - 1)) (qStar k ini.p)) := by
  filter_upwards with l k hlk μ n χ hχ ini
  rw [redSteps_union_densitySteps]
  have :
    (k : ℝ) ^ (1 / 16 : ℝ) * αFunction k 1 *
        (((redOrDensitySteps μ k l ini).filter fun i =>
              (p_ (i - 1) : ℝ) + k ^ (1 / 16 : ℝ) * αFunction k 1 ≤ p_ i ∧
                p_ (i - 1) ≤ ini.p).card :
          ℝ) ≤
      ∑ i ∈ (redOrDensitySteps μ k l ini).filter fun i =>
          (p_ (i - 1) : ℝ) + k ^ (1 / 16 : ℝ) * αFunction k 1 ≤ p_ i ∧ p_ (i - 1) ≤ ini.p,
        (min (p_ i) (qStar k ini.p) - min (p_ (i - 1)) (qStar k ini.p)) :=
    by
    rw [mul_comm, ← nsmul_eq_mul]
    refine' card_nsmul_le_sum _ _ _ _
    intro i hi
    simp only [mem_filter] at hi
    have : p_ (i - 1) ≤ qStar k ini.p := by
      rw [qStar_eq]
      refine' hi.2.2.trans _
      rw [le_add_iff_nonneg_right]
      exact rpow_nonneg (Nat.cast_nonneg _) _
    rw [min_eq_left this, le_sub_iff_add_le', le_min_iff, qStar, add_le_add_iff_right]
    exact hi.2
  refine' this.trans _
  refine' sum_le_sum_of_subset_of_nonneg (filter_subset _ _) _
  intro i hi hi'
  rw [sub_nonneg]
  refine' min_le_min _ le_rfl
  have := redOrDensitySteps_sub_one_mem_degree hi
  refine' (six_four_degree this.2).trans _
  rw [Nat.sub_add_cancel this.1]

theorem seven_eleven (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          (((redOrDensitySteps μ k l ini).filter fun i =>
                                  (p_ (i - 1) : ℝ) + k ^ (1 / 16 : ℝ) * αFunction k 1 ≤ p_ i ∧
                                    p_ (i - 1) ≤ ini.p).card :
                              ℝ) ≤
                            4 * k ^ (15 / 16 : ℝ) := by
  filter_upwards [top_adjuster (eventually_gt_atTop 0), seven_eleven_blue μ₀ hμ₀,
    seven_eleven_red_or_density μ₁ p₀ hμ₁ hp₀, seven_eleven_red_or_density_other] with l h₀ hb hr hd
    k hlk μ hμl hμu n χ hχ ini hini
  set X :=
    (redOrDensitySteps μ k l ini).filter fun i =>
      (p_ (i - 1) : ℝ) + k ^ (1 / 16 : ℝ) * αFunction k 1 ≤ p_ i ∧ p_ (i - 1) ≤ ini.p
  specialize hb k hlk μ hμl n χ hχ ini
  specialize hr k hlk μ hμu n χ hχ ini hini
  specialize hd k hlk μ n χ hχ ini
  change _ * (X.card : ℝ) ≤ _ at hd
  have h₁ :
    αFunction k 1 * ((k : ℝ) ^ (1 / 16 : ℝ) * X.card - 3 * k) ≤
      ∑ i ∈ (range (finalStep μ k l ini)).filter Odd,
        (min (p_ (i + 1)) (qStar k ini.p) - min (p_ (i - 1)) (qStar k ini.p)) :=
    by
    rw [range_filter_odd_eq_union, union_right_comm, sum_union]
    swap
    · rw [redSteps_union_densitySteps]
      exact bigBlueSteps_disjoint_redOrDensitySteps.symm
    refine' ((add_le_add_three hr hd hb).trans_eq' _).trans_eq _
    · ring
    rw [add_left_inj, ← sum_add_distrib]
    refine' sum_congr rfl fun x hx => _
    rw [sub_add_sub_cancel]
  have h₂ :
    ∑ i ∈ (range (finalStep μ k l ini)).filter Odd,
        (min (p_ (i + 1)) (qStar k ini.p) - min (p_ (i - 1)) (qStar k ini.p)) ≤
      k ^ (1 / 16 : ℝ) * αFunction k 1 :=
    by
    refine' sum_range_odd_telescope' (fun i => min (p_ i) (qStar k ini.p)) _
    · intro i
      dsimp
      rw [algorithm_zero, qStar, sub_le_iff_le_add']
      have : min ini.p (ini.p + k ^ (1 / 16 : ℝ) * αFunction k 1) = ini.p :=
        by
        rw [min_eq_left_iff, le_add_iff_nonneg_right]
        exact mul_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (α_nonneg _ _)
      rw [this]
      exact min_le_right _ _
  specialize h₀ k hlk
  have h₃ : (k : ℝ) ^ (1 / 16 : ℝ) * αFunction k 1 ≤ αFunction k 1 * k ^ (1 : ℝ) :=
    by
    rw [mul_comm]
    refine' mul_le_mul_of_nonneg_left _ (α_nonneg _ _)
    refine' rpow_le_rpow_of_exponent_le _ _
    · rw [Nat.one_le_cast, Nat.succ_le_iff]
      exact h₀
    norm_num1
  rw [rpow_one] at h₃
  have := le_of_mul_le_mul_left ((h₁.trans h₂).trans h₃) (α_pos k 1 h₀)
  clear h₁ h₂ h₃ hb hr hd
  rw [sub_le_iff_le_add', ← add_one_mul, ← le_div_iff₀' (rpow_pos_of_pos _ _),
    mul_div_assoc, div_eq_mul_inv (k : ℝ), ← rpow_neg (Nat.cast_nonneg k),
    mul_comm (k : ℝ), ← rpow_add_one] at this
  · refine' this.trans_eq _
    norm_num
  · positivity
  · positivity

theorem seven_twelve (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          (((redOrDensitySteps μ k l ini).filter fun i =>
                                  ((X_ i).card : ℝ) <
                                    (1 - 2 * k ^ (-1 / 16 : ℝ)) * (X_ (i - 1)).card).card :
                              ℝ) ≤
                            7 * k ^ (15 / 16 : ℝ) := by
  filter_upwards [seven_nine μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, seven_ten μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    seven_eleven μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, seven_seven μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_atTop 0)] with l h9 h10 h11 h7 hk₀ k hlk μ hμl hμu n χ hχ ini hini
  specialize h7 k hlk μ hμl hμu n χ hχ ini hini
  specialize h9 k hlk μ hμl hμu n χ hχ ini hini
  specialize h10 k hlk μ hμl hμu n χ hχ ini hini
  specialize h11 k hlk μ hμl hμu n χ hχ ini hini
  let f : ℕ → Prop := fun i => ((X_ i).card : ℝ) < (1 - 2 * k ^ (-1 / 16 : ℝ)) * (X_ (i - 1)).card
  change (((redOrDensitySteps μ k l ini).filter f).card : ℝ) ≤ _
  have : (4 : ℝ) * k ^ (15 / 16 : ℝ) + 3 * k ^ (15 / 16 : ℝ) = 7 * k ^ (15 / 16 : ℝ) :=
    by
    rw [← add_mul]
    norm_num
  rw [← filter_union_filter_not_eq (fun i => p_ (i - 1) ≤ ini.p)
      ((redOrDensitySteps μ k l ini).filter f),
    card_union_of_disjoint (disjoint_filter_filter_not _ _ _), filter_filter, filter_filter,
    Nat.cast_add, ← this]
  have hk₀' : 0 < (k : ℝ) := by
    rw [Nat.cast_pos]
    exact hk₀ k hlk
  refine' add_le_add (h11.trans' _) (h10.trans' _)
  · clear h9 h10 this
    rw [Nat.cast_le]
    refine' card_le_card _
    intro i
    simp (config := { contextual := true }) only [f, mem_filter, and_imp, and_true, true_and]
    intro hi₁ hi₂ hi₃
    rw [← le_sub_iff_add_le']
    have hi₁' := redOrDensitySteps_sub_one_mem_degree hi₁
    have := h7 (i - 1) hi₁'.2
    rw [Nat.sub_add_cancel hi₁'.1] at this
    refine' this.trans' _
    rw [← mul_assoc]
    refine'
      mul_le_mul _ (α_increasing one_le_height) (α_nonneg _ _)
        (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (rpow_nonneg (Nat.cast_nonneg _) _))
    rw [← div_le_iff₀ (rpow_pos_of_pos hk₀' _), ← rpow_sub hk₀']
    have hi₄ : i - 1 < finalStep μ k l ini :=
      by
      rw [degreeSteps, mem_filter, mem_range] at hi₁'
      exact hi₁'.2.1
    have hi₅ : i < finalStep μ k l ini :=
      by
      rw [redOrDensitySteps, mem_filter, mem_range] at hi₁
      exact hi₁.1
    have := x_subset hi₄
    rw [Nat.sub_add_cancel hi₁'.1] at this
    rw [le_div_iff₀, cast_card_sdiff this]
    swap
    · rw [Nat.cast_pos, card_pos]
      exact x_nonempty hi₅
    norm_num1
    rw [neg_div] at hi₂
    have h₆ : ((X_ i).card : ℝ) ≤ (X_ (i - 1)).card :=
      by
      rw [Nat.cast_le]
      refine' card_le_card this
    have h₅ : (0 : ℝ) ≤ (X_ i).card := Nat.cast_nonneg _
    have h₇ : (0 : ℝ) ≤ (k : ℝ) ^ (-(1 / 16) : ℝ) := rpow_nonneg hk₀'.le _
    nlinarith only [hi₂, h₆, h₅, h₇]
  · clear h10 h11
    rw [Nat.cast_le]
    refine' card_le_card _
    intro i
    simp (config := { contextual := true }) only [f, mem_filter, and_imp, true_and, not_le]
    intro hi₁ hi₂ hi₃
    have hi₁' := redOrDensitySteps_sub_one_mem_degree hi₁
    by_contra!
    refine' (h9 (i - 1) hi₁'.2 hi₃.le _).not_gt _
    · rw [Nat.sub_add_cancel hi₁'.1]
      exact this.le
    rw [Nat.sub_add_cancel hi₁'.1]
    exact hi₂

theorem seven_six_large_jump_bound (μ₀ μ₁ p₀ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : μ₁ < 1) (hp₀ : 0 < p₀) :
    ∀ᶠ l : ℕ in atTop,
      ∀ k,
        l ≤ k →
          ∀ μ,
            μ₀ ≤ μ →
              μ ≤ μ₁ →
                ∀ n : ℕ,
                  ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                    (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                          χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                      ∀ ini : BookConfig χ,
                        p₀ ≤ ini.p →
                          (((degreeSteps μ k l ini).filter fun i =>
                                  ((X_ (i + 1)).card : ℝ) <
                                    (1 - 2 * k ^ (-1 / 16 : ℝ)) * (X_ i).card).card :
                              ℝ) ≤
                            7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1 := by
  filter_upwards [seven_twelve μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, four_three hμ₀] with l h712 h43 k hlk μ hμl hμu
    n χ hχ ini hini
  specialize h712 k hlk μ hμl hμu n χ hχ ini hini
  specialize h43 k hlk μ hμl n χ hχ ini
  rw [degreeSteps]
  have :
    ((range (finalStep μ k l ini)).filter Even).image Nat.succ ⊆
      (range (finalStep μ k l ini + 1)).filter fun i => ¬Even i :=
    by
    simp only [Finset.subset_iff, mem_filter, mem_image, and_imp, and_assoc,
      mem_range, forall_exists_index, Nat.succ_eq_add_one]
    rintro _ y hy hy' rfl
    simp [hy, hy', parity_simps]
  rw [← Finset.card_image_of_injective _ Nat.succ_injective]
  have :
    (((range (finalStep μ k l ini)).filter Even).filter fun i =>
            ((algorithm μ k l ini (i + 1)).X.card : ℝ) <
              (1 - 2 * k ^ (-1 / 16 : ℝ)) * (algorithm μ k l ini i).X.card).image
        Nat.succ =
      (((range (finalStep μ k l ini)).filter Even).image Nat.succ).filter fun i =>
        ((algorithm μ k l ini i).X.card : ℝ) <
          (1 - 2 * k ^ (-1 / 16 : ℝ)) * (algorithm μ k l ini (i - 1)).X.card :=
    by
    rw [filter_image]
    rfl
  rw [this]
  clear this
  refine' (Nat.cast_le.2 (card_le_card (filter_subset_filter _ this))).trans _
  set f : ℕ → Prop := fun i =>
    ((algorithm μ k l ini i).X.card : ℝ) <
      (1 - 2 * k ^ (-1 / 16 : ℝ)) * (algorithm μ k l ini (i - 1)).X.card
  simp only [Nat.not_even_iff_odd]
  have :
    ((((range (finalStep μ k l ini + 1)).filter Odd).filter f).card : ℝ) ≤
      (((range (finalStep μ k l ini)).filter Odd).filter f).card + 1 :=
    by
    norm_cast
    rw [filter_filter, filter_filter, range_add_one, filter_insert]
    split_ifs
    · exact card_insert_le _ _
    exact Nat.le_succ _
  refine' this.trans (add_le_add_left _ _)
  rw [range_filter_odd_eq_union, union_right_comm, redSteps_union_densitySteps, filter_union]
  refine' (Nat.cast_le.2 (card_union_le _ _)).trans _
  rw [Nat.cast_add]
  refine' add_le_add h712 _
  refine' (rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 hlk) (by norm_num1)).trans' _
  refine' h43.trans' _
  rw [Nat.cast_le]
  exact card_le_card (filter_subset _ _)

theorem seven_six_o :
    (fun k : ℕ =>
        -(2 / log 2 * ((7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1) * log k)) +
          -(4 * (k ^ (-1 / 16 : ℝ) * (3 * k)))) =o[atTop]
      fun i => (i : ℝ) := by
  suffices
    (fun k : ℝ =>
        -(2 / log 2 * ((7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1) * log k)) +
          -(4 * (k ^ (-1 / 16 : ℝ) * (3 * k)))) =o[atTop]
      fun x : ℝ => x
    by exact this.comp_tendsto tendsto_natCast_atTop_atTop
  refine' IsLittleO.add _ _
  · refine' IsLittleO.neg_left _
    refine' IsLittleO.const_mul_left _ _
    have :
      (fun k : ℝ => 7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1) =O[atTop] fun k =>
        k ^ (15 / 16 : ℝ) :=
      by
      refine' IsBigO.add (IsBigO.add _ _) _
      · exact (isBigO_refl _ _).const_mul_left _
      · refine' (isLittleO_rpow_rpow _).isBigO
        norm_num1
      · refine' (isLittleO_one_rpow _).isBigO
        norm_num1
    refine'
      (this.mul_isLittleO (isLittleO_log_rpow_atTop (by norm_num1 : (0 : ℝ) < 1 / 16))).congr'
        EventuallyEq.rfl _
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    rw [← rpow_add hk]
    norm_num
  · refine' IsLittleO.neg_left _
    refine' IsLittleO.const_mul_left _ _
    simp only [mul_left_comm]
    refine' IsLittleO.const_mul_left _ _
    refine' (isLittleO_rpow_rpow (by norm_num1 : (15 / 16 : ℝ) < 1)).congr' _ _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
      rw [← rpow_add_one hk.ne']
      norm_num
    · simpa only [rpow_one] using EventuallyEq.rfl

-- uses k ≥ 4 ^ 16, but this can be weakened a lot by putting an extra factor of 2 in f
theorem seven_six :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ μ₁ p₀ : ℝ,
          0 < μ₀ →
            μ₁ < 1 →
              0 < p₀ →
                ∀ᶠ l : ℕ in atTop,
                  ∀ k,
                    l ≤ k →
                      ∀ μ,
                        μ₀ ≤ μ →
                          μ ≤ μ₁ →
                            ∀ n : ℕ,
                              ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                                (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                      χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                  ∀ ini : BookConfig χ,
                                    p₀ ≤ ini.p →
                                      (2 : ℝ) ^ f k ≤
                                        ∏ i ∈ degreeSteps μ k l ini,
                                          ((algorithm μ k l ini (i + 1)).X.card : ℝ) /
                                            (algorithm μ k l ini i).X.card := by
  have tt : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop
  refine'
    ⟨fun k =>
      -(2 / log 2 * ((7 * k ^ (15 / 16 : ℝ) + k ^ (3 / 4 : ℝ) + 1) * log k)) +
        -(4 * (k ^ (-1 / 16 : ℝ) * (3 * k))),
      seven_six_o, _⟩
  have h16 : (0 : ℝ) < 1 / 16 := by norm_num1
  have h : (0 : ℝ) < 1 / (2 * 2) := by norm_num1
  intro μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀
  filter_upwards [seven_eight μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, seven_six_large_jump_bound μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_atTop 0),
    top_adjuster (((tendsto_rpow_neg_atTop h16).comp tt).eventually (eventually_le_nhds h))] with l
    h78 h₁ hk0 h' k hlk μ hμl hμu n χ hχ ini hini
  specialize h₁ k hlk μ hμl hμu n χ hχ ini hini
  rw [←
    filter_union_filter_not_eq
      (fun i =>
        ((algorithm μ k l ini (i + 1)).X.card : ℝ) <
          (1 - 2 * k ^ (-1 / 16 : ℝ)) * (algorithm μ k l ini i).X.card)
      (degreeSteps μ k l ini),
    prod_union (disjoint_filter_filter_not _ _ _), rpow_add two_pos]
  have hk₀ : (0 : ℝ) < k := by
    rw [Nat.cast_pos]
    exact hk0 k hlk
  refine'
    mul_le_mul _ _ (rpow_nonneg two_pos.le _)
      (prod_nonneg fun i hi => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have :
      ∀ i : ℕ,
        (i ∈
            (degreeSteps μ k l ini).filter fun i =>
              ((algorithm μ k l ini (i + 1)).X.card : ℝ) <
                (1 - 2 * k ^ (-1 / 16 : ℝ)) * (algorithm μ k l ini i).X.card) →
          (1 : ℝ) / k ^ 2 ≤
            ((algorithm μ k l ini (i + 1)).X.card : ℝ) / (algorithm μ k l ini i).X.card :=
      by
      intro i hi
      rw [mem_filter] at hi
      rw [le_div_iff₀', mul_one_div]
      · refine' h78 k hlk μ hμl hμu n χ hχ ini hini i _
        exact hi.1
      rw [Nat.cast_pos, card_pos]
      rw [degreeSteps, mem_filter, mem_range] at hi
      exact x_nonempty hi.1.1
    refine' (Finset.prod_le_prod _ this).trans' _
    · intro i hi
      positivity
    rw [prod_const, ← rpow_natCast, one_div, inv_rpow (sq_nonneg _), ← rpow_two, ←
      rpow_mul (Nat.cast_nonneg _), ← rpow_neg (Nat.cast_nonneg _), ←
      log_le_log_iff (rpow_pos_of_pos two_pos _) (rpow_pos_of_pos hk₀ _), log_rpow two_pos,
      log_rpow hk₀, ← le_div_iff₀ (log_pos one_lt_two), neg_mul, neg_div, neg_le_neg_iff, mul_assoc,
      ← div_mul_eq_mul_div]
    refine' mul_le_mul_of_nonneg_left _ (div_nonneg (zero_lt_two' ℝ).le (log_nonneg one_le_two))
    refine' mul_le_mul_of_nonneg_right h₁ (log_nonneg _)
    rw [Nat.one_le_cast, Nat.succ_le_iff]
    exact hk0 k hlk
  have h₁ : (2 : ℝ) ^ ((-2 : ℝ) * (2 * k ^ (-1 / 16 : ℝ))) ≤ 1 - 2 * k ^ (-1 / 16 : ℝ) :=
    by
    refine' two_approx _ _
    · positivity
    rw [← le_div_iff₀' (zero_lt_two' ℝ), div_div, neg_div]
    exact h' k hlk
  have :
    ∀ i : ℕ,
      (i ∈
          (degreeSteps μ k l ini).filter fun i =>
            ¬((algorithm μ k l ini (i + 1)).X.card : ℝ) <
                (1 - 2 * k ^ (-1 / 16 : ℝ)) * (algorithm μ k l ini i).X.card) →
        (2 : ℝ) ^ ((-2 : ℝ) * (2 * k ^ (-1 / 16 : ℝ))) ≤
          ((algorithm μ k l ini (i + 1)).X.card : ℝ) / (algorithm μ k l ini i).X.card :=
    by
    intro i hi
    rw [mem_filter, not_lt] at hi
    refine' h₁.trans _
    rw [le_div_iff₀]
    · exact hi.2
    rw [Nat.cast_pos, card_pos]
    refine' x_nonempty _
    rw [degreeSteps, mem_filter, mem_range] at hi
    exact hi.1.1
  refine' (Finset.prod_le_prod _ this).trans' _
  · intro i hi
    exact rpow_nonneg two_pos.le _
  rw [prod_const, ← rpow_natCast, ← rpow_mul two_pos.le]
  refine' rpow_le_rpow_of_exponent_le one_le_two _
  rw [neg_mul, neg_mul, neg_le_neg_iff, ← mul_assoc, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num1]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  norm_cast
  refine' (card_le_card (filter_subset _ _)).trans _
  refine' (four_four_degree μ (hk0 k hlk).ne' (hk0 l le_rfl).ne' hχ ini).trans _
  have : 1 ≤ k := by
    rw [Nat.succ_le_iff]
    exact hk0 k hlk
  linarith only [this, hlk]

theorem telescope_x_card (μ : ℝ)
    (h : ini.X.Nonempty) :-- (hp₀ : 0 < p₀) (h : p₀ ≤ ini.p) :
        ((endState μ k l ini).X.card : ℝ) /
        ini.X.card =
      ∏ i ∈ range (finalStep μ k l ini),
        ((algorithm μ k l ini (i + 1)).X.card : ℝ) / (algorithm μ k l ini i).X.card := by
  suffices
    ∀ j ≤ finalStep μ k l ini,
      ((algorithm μ k l ini j).X.card : ℝ) / ini.X.card =
        ∏ i ∈ range j,
          ((algorithm μ k l ini (i + 1)).X.card : ℝ) / (algorithm μ k l ini i).X.card
    by exact this _ le_rfl
  intro j hj
  induction' j with j ih
  · rw [prod_range_zero, algorithm_zero, div_self]
    rwa [Nat.cast_ne_zero, ← pos_iff_ne_zero, card_pos]
  rw [Nat.succ_le_iff] at hj
  rw [prod_range_succ, ← ih hj.le, mul_comm, div_mul_div_cancel₀]
  rw [Nat.cast_ne_zero, ← pos_iff_ne_zero, card_pos]
  exact x_nonempty hj

theorem seven_one_calc {frk fbk fsk fdk μ β : ℝ} {s_ t_ : ℕ} :
    2 ^ frk * 2 ^ fbk * 2 ^ fsk * 2 ^ fdk * μ ^ l * (1 - μ) ^ t_ * (β ^ s_ * (μ ^ s_)⁻¹) =
      2 ^ fbk * (μ ^ l * (μ ^ s_)⁻¹) * (2 ^ frk * (1 - μ) ^ t_) * (2 ^ fsk * β ^ s_) * 2 ^ fdk := by
  ring_nf

set_option maxHeartbeats 400000 in
theorem seven_one (μ₁ : ℝ) (hμ₁ : μ₁ < 1) :
    ∃ f : ℕ → ℝ,
      (f =o[atTop] fun i => (i : ℝ)) ∧
        ∀ μ₀ p₀ : ℝ,
          0 < μ₀ →
            0 < p₀ →
              ∀ᶠ l : ℕ in atTop,
                ∀ k,
                  l ≤ k →
                    ∀ μ,
                      μ₀ ≤ μ →
                        μ ≤ μ₁ →
                          ∀ n : ℕ,
                            ∀ χ : TopEdgeLabelling (Fin n) (Fin 2),
                              (¬∃ (m : Finset (Fin n)) (c : Fin 2),
                                    χ.MonochromaticOf m c ∧ ![k, l] c ≤ m.card) →
                                ∀ ini : BookConfig χ,
                                  p₀ ≤ ini.p →
                                    (2 : ℝ) ^ f k * μ ^ l * (1 - μ) ^ t * (beta μ k l ini / μ) ^ s *
                                        ini.X.card ≤
                                      (endState μ k l ini).X.card := by
  obtain ⟨fr, hfr, hr'⟩ := seven_two μ₁ hμ₁
  obtain ⟨fb, hfb, hb'⟩ := seven_three
  obtain ⟨fs, hfs, hs'⟩ := seven_four
  obtain ⟨fd, hfd, hd'⟩ := seven_six
  refine' ⟨fun i => fr i + fb i + fs i + fd i, ((hfr.add hfb).add hfs).add hfd, _⟩
  intro μ₀ p₀ hμ₀ hp₀
  filter_upwards [hr', hb' μ₀ μ₁ hμ₀ hμ₁, hs' μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀, hd' μ₀ μ₁ p₀ hμ₀ hμ₁ hp₀,
    top_adjuster (eventually_gt_atTop 0)] with l hr hb hs hd hk₀ k hlk μ hμl hμu n χ hχ ini hini
  clear hr' hb' hs' hd'
  specialize hr k hlk μ hμu n χ hχ ini
  specialize hb k hlk μ hμl hμu n χ hχ ini
  specialize hs k hlk μ hμl hμu n χ hχ ini hini
  specialize hd k hlk μ hμl hμu n χ hχ ini hini
  have : ini.X.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h'
    rw [BookConfig.p, h', colDensity_empty_left] at hini
    exact hp₀.not_ge hini
  rw [← le_div_iff₀]
  swap
  · rwa [Nat.cast_pos, card_pos]
  rw [telescope_x_card μ this, ← union_partial_steps, union_comm (redOrDensitySteps μ k l ini),
    prod_union degreeSteps_disjoint_bigBlueSteps_union_redOrDensitySteps.symm,
    prod_union bigBlueSteps_disjoint_redOrDensitySteps, ← redSteps_union_densitySteps,
    prod_union redSteps_disjoint_densitySteps, ← mul_assoc]
  have : (densitySteps μ k l ini).card ≤ l :=
    by
    refine' (four_four_blue_density μ (hk₀ k hlk).ne' (hk₀ l le_rfl).ne' hχ ini).trans' _
    exact Nat.le_add_left _ _
  have :
    (2 : ℝ) ^ (fr k + fb k + fs k + fd k) * μ ^ l * (1 - μ) ^ t * (beta μ k l ini / μ) ^ s =
      2 ^ fb k * μ ^ (l - s) * (2 ^ fr k * (1 - μ) ^ t) * (2 ^ fs k * beta μ k l ini ^ s) *
        2 ^ fd k :=
    by
    rw [pow_sub₀ _ (hμ₀.trans_le hμl).ne' this, div_pow, div_eq_mul_inv, rpow_add two_pos,
      rpow_add two_pos, rpow_add two_pos]
    exact seven_one_calc
  rw [this]
  have :
    (0 : ℝ) ≤
      ∏ i ∈ ℛ, ((algorithm μ k l ini (i + 1)).X.card : ℝ) / ((algorithm μ k l ini i).X.card : ℝ) :=
    by
    refine' prod_nonneg _
    intro i hi
    positivity
  have :
    (0 : ℝ) ≤
      ∏ i ∈ ℬ, ((algorithm μ k l ini (i + 1)).X.card : ℝ) / ((algorithm μ k l ini i).X.card : ℝ) :=
    by
    refine' prod_nonneg _
    intro i hi
    positivity
  have :
    (0 : ℝ) ≤
      ∏ i ∈ 𝒮, ((algorithm μ k l ini (i + 1)).X.card : ℝ) / ((algorithm μ k l ini i).X.card : ℝ) :=
    by
    refine' prod_nonneg _
    intro i hi
    positivity
  refine' mul_le_mul _ hd (rpow_nonneg two_pos.le _) _
  refine'
    mul_le_mul _ hs
      (mul_nonneg (rpow_nonneg two_pos.le _)
        (pow_nonneg (beta_nonneg (hμ₀.trans_le hμl)) _))
      _
  refine'
    mul_le_mul hb hr
      (mul_nonneg (rpow_nonneg two_pos.le _)
        (pow_nonneg (sub_nonneg_of_le (hμu.trans hμ₁.le)) _))
      _
  all_goals positivity

end SimpleGraph
