import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailPhaseCells
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailPrimePolarBudget

/-! The literal arithmetic correction tail retains squared mass of order
`1/(n+1)`. The lower bound survives sufficiently fine normalized smoothing. -/

open MeasureTheory Set Filter
open scoped Topology BigOperators Convolution
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.CHMDDoobGraph
open _root_.Zeta23
noncomputable section
set_option autoImplicit false

private theorem square_exp_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C*Real.exp (-((3/2 : ℝ)*|x|))) (x : ℝ) :
    ‖f x^2‖ ≤ C^2*Real.exp (-(3*|x|)) := by
  calc
    _ = |f x|^2 := by rw [norm_pow, Real.norm_eq_abs]
    _ ≤ (C*Real.exp (-((3/2 : ℝ)*|x|)))^2 := pow_le_pow_left₀ (abs_nonneg _) (hf x) 2
    _ = _ := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring

theorem factorialMuntzCorrectedTail_sq_integrable (n : ℕ) :
    Integrable (fun x : ℝ => factorialMuntzCorrectedTail n x^2) := by
  have hi := (_root_.RHTower.EvenSector.integrable_exp_neg_rate_abs
    (by norm_num : (0 : ℝ) < 3)).const_mul ((12/Real.sqrt ((n+1 : ℕ) : ℝ))^2)
  exact hi.mono' ((factorialMuntzCorrectedTail_measurable n).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall (square_exp_bound (factorialMuntzCorrectedTail_exp_bound n)))

theorem factorialMuntzTailPhaseCell_subset_window (n j : ℕ) (hj0 : n+1 ≤ j)
    (hj1 : j < 2*(n+1)) : factorialMuntzTailPhaseCell n j ⊆ Icc (-Real.log 2) 0 := by
  intro x hx
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjR : (j : ℝ)+1 ≤ 2*((n+1 : ℕ) : ℝ) := by exact_mod_cast hj1
  refine ⟨?_, factorialMuntzTailPhaseCell_nonpos n j hj0 hx⟩
  apply le_trans _ hx.1
  calc
    _ = Real.log (1/2 : ℝ) := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    _ ≤ _ := by
      apply Real.log_le_log (by norm_num)
      apply (le_div_iff₀ (show 0 < (j : ℝ)+1/16 by positivity)).2
      linarith

theorem factorialMuntzTailPhaseCell_disjoint (n i j : ℕ) (hi : n+1 ≤ i) (hij : i < j) :
    Disjoint (factorialMuntzTailPhaseCell n i) (factorialMuntzTailPhaseCell n j) := by
  have hip : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hijR : (i : ℝ)+1 ≤ j := by exact_mod_cast hij
  have hsep : Real.log (((n+1 : ℕ) : ℝ)/(j : ℝ)) <
      Real.log (((n+1 : ℕ) : ℝ)/((i : ℝ)+1/16)) := by
    apply Real.log_lt_log (by positivity)
    exact div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  apply disjoint_left.2
  intro x hx hy
  exact (not_le_of_gt hsep) (hx.1.trans hy.2)

theorem factorialMuntzTailPhaseCell_sq_integral (n j : ℕ) (hj0 : n+1 ≤ j)
    (hj1 : j < 2*(n+1)) :
    (∫ x in factorialMuntzTailPhaseCell n j, factorialMuntzCorrectedTail n x^2) =
      (1/4 : ℝ)*(1/(j : ℝ)-1/((j : ℝ)+1/16)) := by
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hl : Real.log (((n+1 : ℕ) : ℝ)/((j : ℝ)+1/16)) ≤
      Real.log (((n+1 : ℕ) : ℝ)/(j : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left hN.le hjp (by linarith)
  have he : (∫ x in factorialMuntzTailPhaseCell n j, factorialMuntzCorrectedTail n x^2) =
      ∫ x in factorialMuntzTailPhaseCell n j, Real.exp x/(4*((n+1 : ℕ) : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change factorialMuntzCorrectedTail n x^2 = Real.exp x/(4*((n+1 : ℕ) : ℝ))
    rw [factorialMuntzCorrectedTail_on_phaseCell n j hj0 hj1 hx,
      div_pow, mul_pow, Real.sq_sqrt hN.le]
    have hxexp : Real.exp (x/2)^2 = Real.exp x := by
      rw [pow_two, ← Real.exp_add, show x/2+x/2 = x by ring]
    rw [hxexp]
    norm_num
  rw [he, factorialMuntzTailPhaseCell, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hl, intervalIntegral.integral_div, integral_exp,
    Real.exp_log (by positivity), Real.exp_log (by positivity)]
  field_simp

theorem factorialMuntzTailPhaseCell_sq_integral_lower (n j : ℕ) (hj0 : n+1 ≤ j)
    (hj1 : j < 2*(n+1)) :
    1/(256*((n+1 : ℕ) : ℝ)^2) ≤
      ∫ x in factorialMuntzTailPhaseCell n j, factorialMuntzCorrectedTail n x^2 := by
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hjR : (j : ℝ)+1 ≤ 2*((n+1 : ℕ) : ℝ) := by exact_mod_cast hj1
  have hm := mul_le_mul (show (j : ℝ) ≤ 2*((n+1 : ℕ) : ℝ) by linarith)
    (show (j : ℝ)+1/16 ≤ 2*((n+1 : ℕ) : ℝ) by linarith)
      (show 0 ≤ (j : ℝ)+1/16 by positivity) (show 0 ≤ 2*((n+1 : ℕ) : ℝ) by positivity)
  rw [factorialMuntzTailPhaseCell_sq_integral n j hj0 hj1]
  calc
    _ ≤ 1/(64*(j : ℝ)*((j : ℝ)+1/16)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    _ = _ := by field_simp; ring

/-- All `n+1` disjoint cells lie in one fixed logarithmic window. -/
theorem factorialMuntzCorrectedTail_sq_integral_window_lower (n : ℕ) :
    1/(256*((n+1 : ℕ) : ℝ)) ≤
      ∫ x in Icc (-Real.log 2) 0, factorialMuntzCorrectedTail n x^2 := by
  let S := Finset.Ico (n+1) (2*(n+1))
  have hS : ∀ j ∈ S, n+1 ≤ j ∧ j < 2*(n+1) := fun j hj => Finset.mem_Ico.mp hj
  have hpair : Set.Pairwise (S : Set ℕ) (fun i j =>
      Disjoint (factorialMuntzTailPhaseCell n i) (factorialMuntzTailPhaseCell n j)) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact factorialMuntzTailPhaseCell_disjoint n i j (hS i hi).1 h
    · exact (factorialMuntzTailPhaseCell_disjoint n j i (hS j hj).1 h).symm
  have hi := factorialMuntzCorrectedTail_sq_integrable n
  have he := integral_biUnion_finset S (s := factorialMuntzTailPhaseCell n)
    (fun _ _ => measurableSet_Icc) hpair (fun _ _ => hi.integrableOn)
  have hsub : (⋃ j ∈ S, factorialMuntzTailPhaseCell n j) ⊆ Icc (-Real.log 2) 0 := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨j,hx⟩
    rcases mem_iUnion.mp hx with ⟨hj,hx⟩
    exact factorialMuntzTailPhaseCell_subset_window n j (hS j hj).1 (hS j hj).2 hx
  calc
    _ = ∑ j ∈ S, (1/(256*((n+1 : ℕ) : ℝ)^2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : S.card = n+1 := by dsimp [S]; rw [Nat.card_Ico]; omega
      rw [hc]
      field_simp
    _ ≤ ∑ j ∈ S, ∫ x in factorialMuntzTailPhaseCell n j, factorialMuntzCorrectedTail n x^2 :=
      Finset.sum_le_sum fun j hj => factorialMuntzTailPhaseCell_sq_integral_lower n j
        (hS j hj).1 (hS j hj).2
    _ = ∫ x in ⋃ j ∈ S, factorialMuntzTailPhaseCell n j, factorialMuntzCorrectedTail n x^2 := he.symm
    _ ≤ _ := setIntegral_mono_set hi.integrableOn
      (Eventually.of_forall fun x => sq_nonneg (factorialMuntzCorrectedTail n x))
      (Eventually.of_forall fun x hx => hsub hx)

/-- The normalized arithmetic tail cannot lose its squared mass faster than
`1/(n+1)`. This is a lower bound for the literal source. -/
theorem factorialMuntzCorrectedTail_sq_integral_lower (n : ℕ) :
    1/(256*((n+1 : ℕ) : ℝ)) ≤ ∫ x : ℝ, factorialMuntzCorrectedTail n x^2 :=
  (factorialMuntzCorrectedTail_sq_integral_window_lower n).trans
    (setIntegral_le_integral (factorialMuntzCorrectedTail_sq_integrable n)
      (Eventually.of_forall fun x => sq_nonneg (factorialMuntzCorrectedTail n x)))

theorem factorialMuntzSmoothedTail_tendsto_ae (n : ℕ) :
    ∀ᵐ x : ℝ, Tendsto (fun k : ℕ => factorialMuntzSmoothedTail n k x) atTop
      (𝓝 (factorialMuntzCorrectedTail n x)) := by
  have hr : ∀ᶠ k : ℕ in atTop,
      (WeilOneSided.narrowBump k).rOut ≤ 2*(WeilOneSided.narrowBump k).rIn :=
    Eventually.of_forall fun k => by
      apply le_of_eq
      dsimp [WeilOneSided.narrowBump]
      field_simp
      ring
  have ht := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure ℝ)) narrowBump_rOut_tendsto hr
      (factorialMuntzCorrectedTail_integrable n).locallyIntegrable
  simpa only [factorialMuntzSmoothedTail, CHMDDoobGraph.mollifier, convolution_def,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, smul_eq_mul] using ht

theorem factorialMuntzSmoothedTail_sq_integral_tendsto (n : ℕ) :
    Tendsto (fun k : ℕ => ∫ x : ℝ, factorialMuntzSmoothedTail n k x^2) atTop
      (𝓝 (∫ x : ℝ, factorialMuntzCorrectedTail n x^2)) := by
  have hi := (_root_.RHTower.EvenSector.integrable_exp_neg_rate_abs
    (by norm_num : (0 : ℝ) < 3)).const_mul
      ((12*Real.exp (3/2)/Real.sqrt ((n+1 : ℕ) : ℝ))^2)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => (12*Real.exp (3/2)/Real.sqrt ((n+1 : ℕ) : ℝ))^2*
      Real.exp (-(3*|x|))) ?_ ?_ hi ?_
  · exact Eventually.of_forall fun k =>
      ((factorialMuntzSmoothedTail_expDecayTest n k).1.continuous.pow 2).aestronglyMeasurable
  · exact Eventually.of_forall fun k =>
      Eventually.of_forall (square_exp_bound (factorialMuntzSmoothedTail_exp_bound n k))
  · filter_upwards [factorialMuntzSmoothedTail_tendsto_ae n] with x hx
    exact hx.pow 2

/-- Sufficiently fine actual smoothings retain a fixed positive fraction of
the tail mass; every analytic-domain premise is already discharged. -/
theorem factorialMuntzSmoothedTail_sq_integral_eventually_lower (n : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      1/(512*((n+1 : ℕ) : ℝ)) ≤ ∫ x : ℝ, factorialMuntzSmoothedTail n k x^2 := by
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hlt : 1/(512*((n+1 : ℕ) : ℝ)) <
      ∫ x : ℝ, factorialMuntzCorrectedTail n x^2 := by
    apply lt_of_lt_of_le _ (factorialMuntzCorrectedTail_sq_integral_lower n)
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  exact ((tendsto_order.1 (factorialMuntzSmoothedTail_sq_integral_tendsto n)).1 _ hlt).mono
    fun _ hk => hk.le

/-- The prime and pole error is bounded relative to actual source mass by one
constant independent of the factorial index, once smoothing is fine enough. -/
theorem factorialMuntzSmoothedTail_zero_arch_mass_budget (n : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      |(zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
          (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re -
        1/(2*Real.pi)*(∫ r : ℝ,
          ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) r‖^2*EF.gammaBracket r)| ≤
        (512*(factorialMuntzTailPrimeBudget+144*Real.exp 1^2))*
          ∫ x : ℝ, factorialMuntzSmoothedTail n k x^2 := by
  filter_upwards [factorialMuntzSmoothedTail_sq_integral_eventually_lower n] with k hk
  apply (factorialMuntzSmoothedTail_zero_arch_budget n k).trans
  have hC : 0 ≤ factorialMuntzTailPrimeBudget+144*Real.exp 1^2 :=
    add_nonneg factorialMuntzTailPrimeBudget_nonneg (by positivity)
  calc
    _ = (512*(factorialMuntzTailPrimeBudget+144*Real.exp 1^2))*
        (1/(512*((n+1 : ℕ) : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (by positivity)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
