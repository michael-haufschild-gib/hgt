import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.IntegerQuadratureOnOneLogarithmicCell
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.CesaroMeansOfLogarithmicQuadratureErrors
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.GammaAveragesOfTheOrdinaryPrimeError
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.RHTower.ZetaUnitIntervalIntegrals
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# Integer centering of the ordinary-prime wave

Replacing the continuous polar term by the ordinary integer lattice costs
vanishing absolute mean on the positive log ray. The proof sums the unit-cell
quadrature errors using confinement and the translation modulus of the state.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The density-one integer reference wave at the same weights as the prime wave. -/
def integerReferenceWave (Φ : ℝ → ℝ) (t : ℝ) : ℝ := ∑' k : ℕ, continuousIntegerAtom Φ ((k:ℝ)+1) t

private theorem integerAtom_bound {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    |continuousIntegerAtom Φ x t| ≤ (C*Real.exp (2*t))*(1/x^2) := by
  have hx0 := zero_lt_one.trans_le hx
  have hinv : (Real.sqrt x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt hx)
  rw [continuousIntegerAtom,abs_mul,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
  calc _ ≤ 1*(C*Real.exp (2*(t-Real.log x))) := mul_le_mul hinv (hb _) (abs_nonneg _) zero_le_one
    _ = _ := by rw [mul_sub,Real.exp_sub,two_mul (Real.log x),Real.exp_add,Real.exp_log hx0]; ring

private theorem integerCell_bound {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    |integerCellDefect Φ n t| ≤ (2*C*Real.exp (2*t))*(1/(n:ℝ)^2) := by
  let B := (C*Real.exp (2*t))*(1/(n:ℝ)^2)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hn'
  have h : ∀ x ∈ Ioc (n:ℝ) (n+1), |continuousIntegerAtom Φ n t-continuousIntegerAtom Φ x t| ≤ B+B := by
    intro x hx
    apply (abs_sub _ _).trans (add_le_add (integerAtom_bound hC hb hn' _) _)
    apply (integerAtom_bound hC hb (hn'.trans hx.1.le) _).trans
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (sq_pos_of_pos hn0) (pow_le_pow_left₀ hn0.le hx.1.le 2)) (by positivity)
  calc _ ≤ ∫ x in Ioc (n:ℝ) (n+1), |continuousIntegerAtom Φ n t-continuousIntegerAtom Φ x t| := abs_integral_le_integral_abs
    _ ≤ ∫ _x in Ioc (n:ℝ) (n+1), (B+B) := integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (by simp) ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall h))
    _ = _ := by simp [Real.volume_Ioc,B]; ring

private theorem atom_integrableOn_Ici {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (t : ℝ) : IntegrableOn (fun x => continuousIntegerAtom Φ x t) (Ici 1) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) (by norm_num : (0:ℝ)<1)).const_mul (C*Real.exp (2*t))).mono'
    (by unfold continuousIntegerAtom; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : 1 < x := hx
  simpa only [Real.norm_eq_abs,Real.rpow_neg (zero_le_one.trans hx'.le),Real.rpow_ofNat,one_div] using integerAtom_bound hC hb hx'.le t

private theorem cell_sum {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (t : ℝ) :
    HasSum (fun k : ℕ => integerCellDefect Φ (k+1) t)
      (integerReferenceWave Φ t - ∫ x in Ici 1, continuousIntegerAtom Φ x t) := by
  have hi := atom_integrableOn_Ici hc hC hb t
  have hz := Complex.reCLM.hasSum (hasSum_integral_Ico_unit (c := 1) hi.ofReal)
  have hcell : HasSum (fun k : ℕ => ∫ x in Ioc ((k:ℝ)+1) ((k:ℝ)+1+1), continuousIntegerAtom Φ x t)
      (∫ x in Ici 1, continuousIntegerAtom Φ x t) := by
    simpa only [integral_complex_ofReal,Complex.reCLM_apply,Complex.ofReal_re,integral_Ico_eq_integral_Ioc,
      add_comm (1:ℝ)] using hz
  have hbase := (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^2) 1).2
    (Real.summable_one_div_nat_pow.mpr (by norm_num))
  have hs : Summable (fun k : ℕ => continuousIntegerAtom Φ ((k:ℝ)+1) t) :=
    Summable.of_norm_bounded (hbase.mul_left (C*Real.exp (2*t))) fun k => by
      simpa only [Nat.cast_add_one,Real.norm_eq_abs] using integerAtom_bound hC hb (show 1 ≤ (k:ℝ)+1 by positivity) t
  apply (hs.hasSum.sub hcell).congr_fun
  intro k
  have hsub : Ioc ((k:ℝ)+1) ((k:ℝ)+1+1) ⊆ Ici 1 := fun x hx => (by positivity : 1 ≤ (k:ℝ)+1).trans hx.1.le
  simp only [integerCellDefect,Nat.cast_add_one,Pi.sub_apply]
  rw [integral_sub (by simp) (hi.mono_set hsub)]
  simp [Real.volume_Ioc]

/-- The continuous positive-axis density integrates to the precise polar wave. -/
private theorem continuum_atom {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u = 0) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Ici 1, continuousIntegerAtom Φ x t) = Real.exp (t/2)*(∫ u, Real.exp (-u/2)*Φ u) := by
  have h1 : (∫ x in Ici 1, continuousIntegerAtom Φ x t) = ∫ x in Ioi 0, continuousIntegerAtom Φ x t := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun x hx => zero_lt_one.trans_le hx)
    intro x hx
    have hn : x ≤ 1 := le_of_not_ge hx.2
    rw [continuousIntegerAtom,hs _ (sub_nonneg.2 ((Real.log_nonpos hx.1.le hn).trans ht)),mul_zero]
  rw [h1,HTGeometry.integral_Ioi_comp_exp,← integral_const_mul]
  calc _ = ∫ r : ℝ, Real.exp (t/2)*(Real.exp (-(t-r)/2)*Φ (t-r)) := by
           apply integral_congr_ae (Eventually.of_forall fun r => ?_)
           rw [continuousIntegerAtom,Real.log_exp,← Real.exp_half,← Real.exp_neg]
           have he : Real.exp r * Real.exp (-(r/2)) = Real.exp (t/2)*Real.exp (-(t-r)/2) := by
             rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
           rw [← mul_assoc,he,mul_assoc]
    _ = _ := integral_sub_left_eq_self (fun u => Real.exp (t/2)*(Real.exp (-u/2)*Φ u)) volume t

/-- The integer reference replaces the continuous polar term with vanishing
absolute mean on the observation ray. -/
theorem criticalState_integerReference_zero_mean_error {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ u, |Φ u| ≤ C*Real.exp (2*u)) ∧
      (∀ T : ℝ, IntegrableOn (fun t => integerReferenceWave Φ t - Real.exp (t/2)*(∫ u, Real.exp (-u/2)*F u)) (Ioc 0 T)) ∧
      Tendsto (fun T : ℝ => (∫ t in Ioc 0 T, |integerReferenceWave Φ t - Real.exp (t/2)*(∫ u, Real.exp (-u/2)*F u)|)/T) atTop (𝓝 0) := by
  obtain ⟨Φ,hΦ,heq,hs,⟨C,hC,hb⟩,hcell⟩ := criticalState_integerCellDefect hW ht hF
  have hi := hF.2.1.congr heq
  have hz := hcell.comp (tendsto_add_atTop_nat 1)
  have hsum := tendsto_abs_cesaro_of_cell_errors (f := fun k => integerCellDefect Φ (k+1))
    (fun k => (integerCellDefect_L1_le hΦ hi (Nat.succ_pos k)).1) (C := 2*C) (by positivity)
    (fun k t => by simpa only [Nat.cast_add_one] using integerCell_bound hC hb (Nat.succ_pos k) t)
    (by simpa only [Function.comp_def,Nat.cast_add_one] using hz)
  have ha : (∫ u, Real.exp (-u/2)*F u) = ∫ u, Real.exp (-u/2)*Φ u :=
    integral_congr_ae (heq.mono fun u hu => by rw [hu])
  have h (t : ℝ) (ht : 0 ≤ t) : (∑' k, integerCellDefect Φ (k+1) t) =
      integerReferenceWave Φ t - Real.exp (t/2)*(∫ u, Real.exp (-u/2)*F u) := by
    rw [(cell_sum hΦ hC hb t).tsum_eq,continuum_atom hs ht,ha]
  refine ⟨Φ,hΦ,heq,⟨C,hC,hb⟩,fun T => (hsum.1 T).congr_fun (fun t ht => h t ht.1.le) measurableSet_Ioc,hsum.2.congr fun T => ?_⟩
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioc fun t ht => congrArg abs (h t ht.1.le)

/-- Ordinary-prime atoms after subtracting one unit of density at each integer. -/
def integerCentredPrimeWave (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, ((if n.Prime then Real.log n else 0)-1)*continuousIntegerAtom Φ n t

private theorem integerCentredPrimeWave_eq {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (t : ℝ) :
    integerCentredPrimeWave Φ t = (ordinaryPrimeWave Φ t).re - integerReferenceWave Φ t := by
  let a := fun n : ℕ => continuousIntegerAtom Φ n t
  let D := C*Real.exp (2*t)
  let q := fun n : ℕ => Real.log (n:ℝ)*a n
  let P : Set ℕ := {p | p.Prime}
  have ha : Summable a := by
    apply (summable_nat_add_iff 1).1
    have hs := (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^2) 1).2 (Real.summable_one_div_nat_pow.mpr (by norm_num))
    exact Summable.of_norm_bounded (hs.mul_left D) fun k => by
      simpa only [a,D,Real.norm_eq_abs] using integerAtom_bound hC hb (by exact_mod_cast Nat.succ_pos k : (1:ℝ) ≤ (k+1:ℕ)) t
  have hq : Summable (fun p : Nat.Primes => q p) := by
    have hs := GaloisForLFunctions.summable_log_nat_div_sq.comp_injective
      (show Function.Injective (fun p : Nat.Primes => (p:ℕ)) from Subtype.coe_injective)
    apply Summable.of_norm_bounded (hs.mul_left D) fun p => ?_
    have hp : (1:ℝ) ≤ (p:ℕ) := by exact_mod_cast p.property.one_le
    have hl := Real.log_nonneg hp
    rw [Real.norm_eq_abs,show q (p:ℕ) = Real.log (p:ℕ)*a p from rfl,abs_mul,abs_of_nonneg hl]
    calc _ ≤ Real.log (p:ℕ)*(D*(1/(p:ℕ)^2)) := mul_le_mul_of_nonneg_left (integerAtom_bound hC hb hp t) hl
      _ = _ := by dsimp only [Function.comp_apply]; ring
  have hq' : Summable (P.indicator q) := (summable_subtype_iff_indicator).1 hq
  have hpr : ordinaryPrimeWave Φ t = ((∑' n, P.indicator q n : ℝ):ℂ) := by
    rw [← tsum_subtype P q]
    apply HasSum.tsum_eq
    apply (Complex.ofRealCLM.hasSum hq.hasSum).congr_fun
    intro p
    simp only [Complex.ofRealCLM_apply,q,a,continuousIntegerAtom,vonMangoldtAtom,if_pos p.property.two_le,
      ArithmeticFunction.vonMangoldt_apply_prime p.property,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_inv]
    ring
  have hna := ha.sum_add_tsum_nat_add 1
  have ha0 : a 0 = 0 := by simp [a,continuousIntegerAtom]
  have ht : (∑' n, a n) = integerReferenceWave Φ t := by
    simpa only [Finset.sum_range_one,ha0,zero_add,a,Nat.cast_add_one,integerReferenceWave] using hna.symm
  rw [hpr,Complex.ofReal_re,← ht]
  unfold integerCentredPrimeWave
  rw [← hq'.tsum_sub ha]
  apply tsum_congr fun n => ?_
  by_cases hn : n.Prime
  · rw [if_pos hn,Set.indicator_of_mem (show n ∈ P from hn)]; dsimp only [q,a]; ring
  · rw [if_neg hn,Set.indicator_of_notMem (show n ∉ P from hn)]; dsimp only [a]; ring

/-- Unconditionally, failure of RH produces a critical state for which literal
integer centering represents the signed ordinary-prime error in absolute mean. -/
theorem riemannHypothesis_or_integer_centred_prime_error : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧ IsCriticalHalfLineGroundState W₀ F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ Tendsto (fun T : ℝ => (∫ t in Ioc 0 T,
        |(ordinaryPrimeWave Φ t).re - Real.exp (t/2)*(negativeHalfLineLaplace (cx F) (-(1/2))).re -
          integerCentredPrimeWave Φ t|)/T) atTop (𝓝 0) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨Φ,hΦ,heq,⟨C,hC,hb⟩,_,h⟩ := criticalState_integerReference_zero_mean_error hW ht hF
  have hL : negativeHalfLineLaplace (cx F) (-(1/2)) = ((∫ u, Real.exp (-u/2)*F u : ℝ):ℂ) := by
    rw [negativeHalfLineLaplace,← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      simp only [cx,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat]
      congr 2; ring)
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,heq,h.congr fun T => ?_⟩
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [integerCentredPrimeWave_eq hC hb,hL,Complex.ofReal_re]
  congr 1; ring

#print axioms criticalState_integerReference_zero_mean_error
#print axioms riemannHypothesis_or_integer_centred_prime_error

end GaloisForLFunctions.ExclusionOfTheCriticalState
