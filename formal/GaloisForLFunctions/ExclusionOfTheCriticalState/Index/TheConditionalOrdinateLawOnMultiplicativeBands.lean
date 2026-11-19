import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheLogarithmicWallCuspOfAFiniteLayer
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.FiniteLayerKreinStructureAndRigidity

/-!
# The conditional law of critical-line mass on multiplicative bands

The successive-scale differences used in discrete Hardy estimates extract
the mass of each logarithmic cell from the finite-layer tail. Relative to
the mass above its lower cutoff, the ordinate has a Pareto tail of index
one. A sub-inverse reading on one fixed multiplicative band already
excludes a finite nonempty off-line divisor.
-/

open MeasureTheory Set Filter Complex Topology Zeta23
open GaloisForLFunctions GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri GaloisForLFunctions.HTGeometry _root_.RHTower
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
noncomputable section

/-- Total sampled ground-state mass strictly above an absolute ordinate. -/
def ordinateTailMass (F : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∑' q : onLineCopies, if T < |(centredZero q).im| then zeroValueMass F q else 0

/-- Sampled ground-state mass with ordinates in the half-open band (T,U]. -/
def ordinateBandMass (F : ℝ → ℝ) (T U : ℝ) : ℝ :=
  ∑' q : onLineCopies, if T < |(centredZero q).im| ∧ |(centredZero q).im| ≤ U then zeroValueMass F q else 0

/-- Coefficient of the entire finite-layer tail. -/
def ordinateCuspConstant (W : ℝ) (F : ℝ → ℝ) : ℝ :=
  8*criticalAliasCoefficient W*(∫ u : ℝ, F u^2*Real.exp (-(8*u)))/Real.pi

private theorem band_as_difference {F : ℝ → ℝ} (hs : Summable (fun q : onLineCopies => zeroValueMass F q))
    {T U : ℝ} (hTU : T ≤ U) :
    ordinateBandMass F T U = ordinateTailMass F T-ordinateTailMass F U := by
  classical
  let f (q : onLineCopies) := if T < |(centredZero q).im| then zeroValueMass F q else 0
  let g (q : onLineCopies) := if U < |(centredZero q).im| then zeroValueMass F q else 0
  have summ (V : ℝ) : Summable (fun q : onLineCopies =>
      if V < |(centredZero q).im| then zeroValueMass F q else 0) :=
    hs.of_nonneg_of_le (fun q => ite_zero_nonneg (zeroValueMass_nonneg F q))
      (fun q => ite_zero_le (zeroValueMass_nonneg F q))
  change _ = (∑' q, f q) - ∑' q, g q
  rw [←(summ T).tsum_sub (summ U)]
  apply tsum_congr
  intro q
  dsimp only [f,g]
  split_ifs <;> first | ring | exfalso; grind

private theorem constant_pos {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) : 0<ordinateCuspConstant W F := by
  have hf := isConfinedNullVector_of_groundState hW ht hF
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hm : (∫ u : ℝ, F u^2*Real.exp (-(8*u))) = criticalHalfLineExponentialPair F F := by
    unfold criticalHalfLineExponentialPair
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  unfold ordinateCuspConstant
  rw [hm]
  exact div_pos (mul_pos (mul_pos (by norm_num) (criticalAliasCoefficient_positive hW))
    (exponentialPair_self_pos hd hf.2.1)) Real.pi_pos

private theorem scaled_tail {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0<a) :
    Tendsto (fun T : ℝ => T*ordinateTailMass F (a*T)) atTop (𝓝 (ordinateCuspConstant W F/a)) := by
  have h : Tendsto (fun t : ℝ => t*ordinateTailMass F t) atTop (𝓝 (ordinateCuspConstant W F)) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  have hh := (h.comp (tendsto_id.const_mul_atTop ha)).div_const a
  exact hh.congr fun T => by dsimp; field_simp [ha.ne']

/-- Every fixed multiplicative band carries a prescribed share of the
inverse tail, including its exact dimensional constant. -/
theorem critical_ordinate_band_law {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    Tendsto (fun T : ℝ => T*ordinateBandMass F (a*T) (b*T)) atTop
      (𝓝 (ordinateCuspConstant W F*(1/a-1/b))) := by
  have h := (scaled_tail hW ht hF hf ha).sub (scaled_tail hW ht hF hf (ha.trans_le hab))
  have hs := (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_of_groundState hF) hf).1
  rw [show ordinateCuspConstant W F/a - ordinateCuspConstant W F/b =
    ordinateCuspConstant W F*(1/a-1/b) by ring] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  rw [band_as_difference hs (mul_le_mul_of_nonneg_right hab hT),mul_sub]

/-- Given an ordinate above T, the limiting fraction beyond aT equals
1/a. Equivalently the log overshoot has unit exponential tail. -/
theorem critical_ordinate_conditional_tail {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {a : ℝ} (ha : 0<a) :
    Tendsto (fun T : ℝ => ordinateTailMass F (a*T)/ordinateTailMass F T) atTop (𝓝 (1/a)) := by
  let C := ordinateCuspConstant W F
  have h : Tendsto (fun T : ℝ => T*ordinateTailMass F T) atTop (𝓝 C) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  have hc : C≠0 := (constant_pos hW ht hF).ne'
  have H := (scaled_tail hW ht hF hf ha).div h hc
  change Tendsto _ _ (𝓝 ((C/a)/C)) at H
  rw [show (C/a)/C=1/a by field_simp [hc,ha.ne']] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  exact mul_div_mul_left _ _ hT.ne'

/-- The conditional law prices any finite family of multiplicative bands
simultaneously; coefficients may have either sign and bands may overlap. -/
theorem critical_ordinate_step_test {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {ι : Type*} (S : Finset ι) (a b c : ι → ℝ)
    (ha : ∀ i ∈ S, 0<a i ∧ a i≤b i) :
    Tendsto (fun T : ℝ => T*∑ i ∈ S, c i*ordinateBandMass F (a i*T) (b i*T)) atTop
      (𝓝 (ordinateCuspConstant W F*∑ i ∈ S, c i*(1/a i-1/b i))) := by
  have h := tendsto_finsetSum S (fun i hi =>
    (critical_ordinate_band_law hW ht hF hf (ha i hi).1 (ha i hi).2).const_mul (c i))
  simp only [Finset.mul_sum] at *
  convert h using 1
  · funext T
    exact Finset.sum_congr rfl fun i _ => by ring
  · congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- To rule out finite nonempty off-line support, it suffices for each
threshold ground state to have a vanishing subsequence on one band.
The band ratio can depend on the state and be arbitrarily close to one. -/
theorem finite_layer_iff_one_vanishing_band :
    (BacklundConverse.FiniteOffLine → RiemannHypothesis) ↔
      (BacklundConverse.FiniteOffLine → ∀ (W : ℝ) (F : ℝ → ℝ), 0<W →
        (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal) → IsCriticalHalfLineGroundState W F →
        ∃ b : ℝ, 1<b ∧ ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
          Tendsto (fun i => T i*ordinateBandMass F (T i) (b*T i)) atTop (𝓝 0)) := by
  have eqv : (BacklundConverse.FiniteOffLine → RiemannHypothesis) ↔
      (BacklundConverse.FiniteOffLine → ¬ ∃ (W : ℝ) (F : ℝ → ℝ), 0<W ∧
        (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F) :=
    finiteLayer_ecs_b13_tfae.out 0 1
  rw [eqv]
  constructor
  · intro h hf W F hW ht hF
    exact (h hf ⟨W,F,hW,ht,hF⟩).elim
  · intro h hf
    rintro ⟨W,F,hW,ht,hF⟩
    obtain ⟨b,hb,T,hT,hzero⟩ := h hf W F hW ht hF
    have lim := (critical_ordinate_band_law hW ht hF hf (a:=1) zero_lt_one hb.le).comp hT
    simp only [Function.comp_def,one_mul,div_one] at lim
    have hc := mul_pos (constant_pos hW ht hF) (sub_pos.mpr (one_div_lt_one_of_one_lt₀ hb))
    exact hc.ne' (tendsto_nhds_unique lim hzero)

#print axioms critical_ordinate_band_law
#print axioms critical_ordinate_conditional_tail
#print axioms critical_ordinate_step_test
#print axioms finite_layer_iff_one_vanishing_band
end
end GaloisForLFunctions.ExclusionOfTheCriticalState
