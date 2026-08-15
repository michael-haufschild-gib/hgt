import GaloisForLFunctions.RHTower.FrankensteinGammaSixTwoPrimeFlowedScaleCarrier
import GaloisForLFunctions.RHTower.XiHorizontalCollisionGaussHodgePrimeCurrent
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

/-!
# Frankenstein Gamma-six finite linear-flow source carrier

This module replaces the previously isolated bilinear reflected producer with one literal
holomorphic source current.  For a finite Xi divisor window `S`, retain every analytic-multiplicity
copy and flow it through the complete Gamma-six scale:

`sum_q burnolPrimeCharacter (6^n) q`.

Four independent corpus mechanisms meet before scalarization:

* Gauss--Hodge/Burnol holomorphic scale flow identifies powers with the source scale `6^n`;
* Xi multiplicity packets preserve every divisor coefficient;
* functional-equation reflection puts an expanding orientation of every off-line class back in the
  same strip window;
* finite exponential-pencil mean-square rigidity prevents maximal modes from disappearing through
  phase cancellation, including repeated equal modes.

Consequently, subexponential growth of this linear current on one strip window is equivalent to
zero horizontal collision charge.  Requiring it on all real windows, or only natural-height
windows, is equivalent to RH.  All statements are unconditional receiver theorems.  Remaining
producer is a source-side subexponential estimate for this explicit one-variable current.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Coefficient-faithful finite Xi current under the complete Gamma-six horizontal scale flow. -/
def sourceHorizontalGammaSixFiniteLinearFlowCurrent
    (S : Finset XiDivisorSupport) (n : ℕ) : ℂ :=
  ∑ q ∈ xiFiniteMultiplicityCopyPacket S,
    sourceHorizontalGammaSixFlowMode q ^ n

/-- The abstract mode pencil is literally the holomorphic Burnol source current at scale `6^n`. -/
theorem sourceHorizontalGammaSixFiniteLinearFlowCurrent_eq_flowedScale
    (S : Finset XiDivisorSupport) (n : ℕ) :
    sourceHorizontalGammaSixFiniteLinearFlowCurrent S n =
      ∑ q ∈ xiFiniteMultiplicityCopyPacket S,
        burnolPrimeCharacter ((6 : ℝ) ^ n) (q.1 : ℂ) := by
  apply Finset.sum_congr rfl
  intro q hq
  rw [show sourceHorizontalGammaSixFlowMode q ^ n =
      burnolPrimeCharacter ((6 : ℝ) ^ n) (q.1 : ℂ) by
    have h := burnolPrimeCharacter_mul_gammaSixFlow_pow
      (p := (1 : ℝ)) (by norm_num) (q.1 : ℂ) n
    simpa [sourceHorizontalGammaSixFlowMode, burnolPrimeCharacter] using h]

/-- Subexponentiality against every fixed real exponential rate greater than one. -/
def SourceHorizontalGammaSixFiniteLinearFlowSubexponential
    (S : Finset XiDivisorSupport) : Prop :=
  ∀ r : ℝ, 1 < r →
    Tendsto
      (fun n : ℕ => sourceHorizontalGammaSixFiniteLinearFlowCurrent S n / (r : ℂ) ^ n)
      atTop (nhds 0)

/-- Critical-line placement makes every Gamma-six flow mode unimodular, hence the finite current
is subexponential. -/
theorem sourceHorizontalGammaSixFiniteLinearFlowSubexponential_of_onLine
    {S : Finset XiDivisorSupport}
    (hline : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2) :
    SourceHorizontalGammaSixFiniteLinearFlowSubexponential S := by
  intro r hr
  let P := xiFiniteMultiplicityCopyPacket S
  have hmode : ∀ q ∈ P, ‖sourceHorizontalGammaSixFlowMode q‖ = 1 := by
    intro q hq
    rw [norm_sourceHorizontalGammaSixFlowMode,
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2
        (hline q.1 (mem_xiFiniteMultiplicityCopyPacket.mp hq))]
    norm_num
  have hbound (n : ℕ) :
      ‖sourceHorizontalGammaSixFiniteLinearFlowCurrent S n‖ ≤ P.card := by
    rw [sourceHorizontalGammaSixFiniteLinearFlowCurrent]
    calc
      ‖∑ q ∈ P, sourceHorizontalGammaSixFlowMode q ^ n‖ ≤
          ∑ q ∈ P, ‖sourceHorizontalGammaSixFlowMode q ^ n‖ := norm_sum_le _ _
      _ = ∑ _q ∈ P, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [norm_pow, hmode q hq, one_pow]
      _ = P.card := by simp
  apply squeeze_zero_norm'
    (a := fun n : ℕ => (P.card : ℝ) / r ^ n)
  · exact Eventually.of_forall fun n => by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_trans zero_lt_one hr)]
      exact div_le_div_of_nonneg_right (hbound n) (pow_nonneg (by linarith) n)
  · have hpow : Tendsto (fun n : ℕ => (r ^ n)⁻¹) atTop (nhds 0) :=
      (tendsto_pow_atTop_atTop_of_one_lt hr).inv_tendsto_atTop
    simpa [div_eq_mul_inv] using hpow.const_mul (P.card : ℝ)

/-- A finite unit-coefficient pencil with one expanding mode is not subexponential.  Passing to
the maximal-modulus fiber makes equal phases reinforce, while all smaller modes decay. -/
theorem not_subexponential_finiteExponentialPencil_of_expanding_mode
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℂ)
    (hout : ∃ i ∈ s, 1 < ‖b i‖) :
    ¬ ∀ r : ℝ, 1 < r →
      Tendsto
        (fun n : ℕ => finiteExponentialPencil s (fun _ => 1) b n / (r : ℂ) ^ n)
        atTop (nhds 0) := by
  classical
  obtain ⟨i0, hi0, hi0out⟩ := hout
  obtain ⟨imax, himax, hmax⟩ :=
    s.exists_max_image (fun i => ‖b i‖) ⟨i0, hi0⟩
  let r : ℝ := ‖b imax‖
  have hr : 1 < r := hi0out.trans_le (hmax i0 hi0)
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  let D : Finset ι := s.filter (fun i => ‖b i‖ = r)
  have himaxD : imax ∈ D := Finset.mem_filter.mpr ⟨himax, rfl⟩
  have hDsub : D ⊆ s := Finset.filter_subset _ _
  let z : ι → ℂ := fun i => b i / (r : ℂ)
  have hzD : ∀ i ∈ D, ‖z i‖ = 1 := by
    intro i hi
    have hiEq := (Finset.mem_filter.mp hi).2
    dsimp only [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hiEq,
      div_self hr0.ne']
  have hfiber : ∃ u ∈ D.image z,
      finiteExponentialFiberCoefficient D (fun _ => 1) z u ≠ 0 := by
    refine ⟨z imax, Finset.mem_image.mpr ⟨imax, himaxD, rfl⟩, ?_⟩
    rw [finiteExponentialFiberCoefficient]
    have hmem : imax ∈ D.filter (fun i => z i = z imax) := by simp [himaxD]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨imax, hmem⟩)
  have htail : Tendsto
      (finiteExponentialPencil (s \ D) (fun _ => 1) z)
      atTop (nhds 0) := by
    rw [show (0 : ℂ) = ∑ i ∈ s \ D, (0 : ℂ) by simp]
    exact tendsto_finsetSum (s \ D) fun i hi => by
      have hiS := (Finset.mem_sdiff.mp hi).1
      have hiD := (Finset.mem_sdiff.mp hi).2
      have hle : ‖b i‖ ≤ r := hmax i hiS
      have hlt : ‖b i‖ < r := lt_of_le_of_ne hle (fun heq =>
        hiD (Finset.mem_filter.mpr ⟨hiS, heq⟩))
      have hzlt : ‖z i‖ < 1 := by
        dsimp only [z]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
        exact (div_lt_one hr0).2 hlt
      simpa [finiteExponentialPencil] using
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one hzlt
  have hsplit (n : ℕ) :
      finiteExponentialPencil (s \ D) (fun _ => 1) z n +
          finiteExponentialPencil D (fun _ => 1) z n =
        finiteExponentialPencil s (fun _ => 1) z n := by
    unfold finiteExponentialPencil
    exact Finset.sum_sdiff hDsub
  intro hsub
  have hnormalize (n : ℕ) :
      finiteExponentialPencil s (fun _ => 1) z n =
        finiteExponentialPencil s (fun _ => 1) b n / (r : ℂ) ^ n := by
    rw [finiteExponentialPencil, finiteExponentialPencil, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [z]
    rw [div_pow]
    ring
  have hfull : Tendsto (finiteExponentialPencil s (fun _ => 1) z)
      atTop (nhds 0) := by
    rw [funext hnormalize]
    exact hsub r hr
  have hdomzero : Tendsto (finiteExponentialPencil D (fun _ => 1) z)
      atTop (nhds 0) := by
    have hdiff := hfull.sub htail
    have heq :
        (fun n => finiteExponentialPencil s (fun _ => 1) z n -
          finiteExponentialPencil (s \ D) (fun _ => 1) z n) =
          finiteExponentialPencil D (fun _ => 1) z := by
      funext n
      rw [← hsplit n]
      ring
    rw [heq] at hdiff
    simpa using hdiff
  exact (not_tendsto_finiteExponentialPencil_zero_of_fiberCoefficient
    D (fun _ => 1) z hzD hfiber) hdomzero

/-- On a reflection-closed Xi strip window, linear Gamma-six flow is subexponential exactly when
every retained divisor class lies on the critical line. -/
theorem sourceHorizontalGammaSixStripLinearFlowSubexponential_iff
    (T : ℝ) :
    SourceHorizontalGammaSixFiniteLinearFlowSubexponential
        (xiStripWindowDivisorSupportFinset T) ↔
      ∀ rho ∈ xiStripWindowDivisorSupportFinset T,
        (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hsub rho hrho
    by_contra hoff
    let q : XiZeroCopy := xiFirstZeroCopy rho
    have hq : q ∈ xiFiniteMultiplicityCopyPacket
        (xiStripWindowDivisorSupportFinset T) := by
      rw [mem_xiFiniteMultiplicityCopyPacket]
      exact hrho
    have hrate : primeDepthBVWoldXiCenteredRate rho ≠ 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).not.mpr hoff
    have hout : ∃ q' ∈ xiFiniteMultiplicityCopyPacket
        (xiStripWindowDivisorSupportFinset T),
        1 < ‖sourceHorizontalGammaSixFlowMode q'‖ := by
      rcases lt_or_gt_of_ne hrate with hneg | hpos
      · let qr := xiZeroCopyLineConjEquiv q
        have hqr : qr ∈ xiFiniteMultiplicityCopyPacket
            (xiStripWindowDivisorSupportFinset T) := by
          rw [mem_xiFiniteMultiplicityCopyPacket]
          rw [mem_xiStripWindowDivisorSupportFinset,
            Set.Finite.mem_toFinset]
          apply lineReflect_mem_stripZeros
          rw [← Set.Finite.mem_toFinset]
          exact (mem_xiStripWindowDivisorSupportFinset.mp hrho)
        refine ⟨qr, hqr, ?_⟩
        rw [norm_sourceHorizontalGammaSixFlowMode,
          show primeDepthBVWoldXiCenteredRate qr.1 =
            -primeDepthBVWoldXiCenteredRate q.1 by
              exact primeDepthBVWoldXiCenteredRate_reflection q.1]
        change 1 < (6 : ℝ) ^ (-primeDepthBVWoldXiCenteredRate rho / 2)
        exact Real.one_lt_rpow (by norm_num) (by linarith)
      · refine ⟨q, hq, ?_⟩
        rw [norm_sourceHorizontalGammaSixFlowMode]
        change 1 < (6 : ℝ) ^ (primeDepthBVWoldXiCenteredRate rho / 2)
        exact Real.one_lt_rpow (by norm_num) (by linarith)
    apply (not_subexponential_finiteExponentialPencil_of_expanding_mode
      (xiFiniteMultiplicityCopyPacket (xiStripWindowDivisorSupportFinset T))
      sourceHorizontalGammaSixFlowMode hout)
    intro r hr
    have h := hsub r hr
    simpa [sourceHorizontalGammaSixFiniteLinearFlowCurrent,
      finiteExponentialPencil] using h
  · exact sourceHorizontalGammaSixFiniteLinearFlowSubexponential_of_onLine

/-- The linear source criterion is exactly the previously quantized horizontal collision charge. -/
theorem sourceHorizontalGammaSixStripLinearFlowSubexponential_iff_charge_eq_zero
    (T : ℝ) :
    SourceHorizontalGammaSixFiniteLinearFlowSubexponential
        (xiStripWindowDivisorSupportFinset T) ↔
      xiHorizontalCollisionCharge T = 0 := by
  rw [sourceHorizontalGammaSixStripLinearFlowSubexponential_iff,
    xiHorizontalCollisionCharge_eq_zero_iff_stripSupport_onLine]

/-- Global subexponentiality of the coefficient-faithful linear Gamma-six source current is RH. -/
theorem riemannHypothesis_iff_forall_sourceHorizontalGammaSixStripLinearFlowSubexponential :
    RiemannHypothesis ↔
      ∀ T : ℝ,
        SourceHorizontalGammaSixFiniteLinearFlowSubexponential
          (xiStripWindowDivisorSupportFinset T) := by
  rw [riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero]
  exact forall_congr' fun T =>
    (sourceHorizontalGammaSixStripLinearFlowSubexponential_iff_charge_eq_zero T).symm

/-- Natural-height windows are cofinal, so the same source condition only at integer cutoffs is
already equivalent to RH. -/
theorem riemannHypothesis_iff_forall_nat_sourceHorizontalGammaSixStripLinearFlowSubexponential :
    RiemannHypothesis ↔
      ∀ n : ℕ,
        SourceHorizontalGammaSixFiniteLinearFlowSubexponential
          (xiStripWindowDivisorSupportFinset n) := by
  constructor
  · intro hRH n
    exact
      riemannHypothesis_iff_forall_sourceHorizontalGammaSixStripLinearFlowSubexponential.mp
        hRH n
  · intro hsource
    apply riemannHypothesis_of_forall_nat_horizontalCollisionCharge_lt_two
    intro n
    have hzero : xiHorizontalCollisionCharge n = 0 :=
      (sourceHorizontalGammaSixStripLinearFlowSubexponential_iff_charge_eq_zero n).mp
        (hsource n)
    rw [hzero]
    omega

end

end RHTower
