import GaloisForLFunctions.RHTower.SelbergMaassModalMixedLoss
import GaloisForLFunctions.RHTower.SelbergMaassPhaseProductLossLimit

/-!
# Vanishing horizontal mean of the mixed loss for exceptional Maass cusp forms

Let `f` be a Maass cusp eigenform for the principal congruence subgroup `Γ(N+1)` and consider the
vector of its deck-coordinate fields. The mixed loss `lossPair(v, w) = Re⟨v, w⟩ - Re⟨Tv, Tw⟩`
measures the failure of the inversion transfer `T` (for fixed residues `r, s`) to preserve the real
Gram pairing. The module expresses the period mean
`∫_0^1 lossPair(∂_x F, ∂_y F)(t(N+1) + i) dt` of the loss between horizontal and vertical
derivatives on the line `Im z = 1` as the real part of a normalized phase-averaged `L²` pairing of
rescaled derivative readouts, approximates it by Fourier partial sums, and shows that for an
exceptional eigenvalue `λ ∈ (0, 1/4)` every partial pairing has zero real part. Hence the period
mean of the mixed loss vanishes for such forms.

## Main results

- `phasePairExact_re_eq_unitLossMean`: the real part of the exact phase pairing equals the period
  mean of the mixed loss at height one.
- `phasePairPartial_re_eq_zero`: for `λ ∈ (0, 1/4)`, the degree-`M` Fourier partial pairing has
  zero real part, since each diagonal Fourier mode contributes zero loss.
- `tendsto_phasePairPartial`: the Fourier partial pairings converge to the exact pairing.
- `unitLossMean_eq_zero`: for `λ ∈ (0, 1/4)`, the period mean of the mixed loss at height one is
  zero.

## Hypotheses

All results are unconditional statements about an arbitrary Maass cusp eigenform (a nonzero smooth
cuspidal Laplace eigenfunction for `Γ(N+1)`). The vanishing results assume the eigenvalue lies in
the exceptional range `(0, 1/4)`; the existence of such a form is not assumed.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassPhaseProductMean
open GaloisForLFunctions.HTGeometry
open SelbergMaassCongruenceTrace SelbergMaassPhaseRellich SelbergMaassFourierPartial
  SelbergMaassDilationStress SelbergMaassCharacterSeamFlux SelbergMaassTraceEnergy
  SelbergMaassMean SelbergMaassPhaseStress SelbergMaassPhaseProductLimit
  SelbergMaassPhaseProductLossLimit
open SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks
  SelbergMaassCharacterProjection SelbergMaassCharacterFourier SelbergMaassInversionGram
  SelbergMaassUnipotentFourier SelbergMaassCharacterGradient SelbergMaassFourier
  SelbergMaassMixedLoss SelbergMaassSliceRigidity SelbergMaassKernelWronskian
  SelbergMaassModalMixedLoss
noncomputable section

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
  (r s : ZMod (N + 1))

/-- Normalized phase average `(N+1)^(-3) / 2 · ∑_i ⟨S_M H_i, S_M V_i⟩` of the `L²` pairings of the
degree-`M` Fourier partial sums of the rescaled horizontal and vertical derivative readouts. -/
def phasePairPartial (M : ℕ) : ℂ :=
  ((((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2 : ℝ) : ℂ) *
    ∑ i : PhaseIndex N,
      l2Pair
        (fourierPartialSum
          (unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1) M)
        (fourierPartialSum
          (unitRescaledVerticalReadout N f (phaseReadout N r s i) 1) M)

/-- Normalized phase average of the `L²(0,1)` pairings of the full rescaled horizontal and vertical
derivative readouts at height one. -/
def phasePairExact : ℂ :=
  ((((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2 : ℝ) : ℂ) *
    ∑ i : PhaseIndex N,
      l2Pair
        (unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1)
        (unitRescaledVerticalReadout N f (phaseReadout N r s i) 1)

/-- The real part of the exact phase pairing equals the period mean
`∫_0^1 lossPair(∂_x F, ∂_y F)(t(N+1) + i) dt` of the mixed transfer loss at height one. -/
theorem phasePairExact_re_eq_unitLossMean :
    (phasePairExact N f r s).re =
      ∫ t in (0 : ℝ)..1, lossPair N r s
        (sourceDerivative N f 1 (ofComplex (point (t * (N + 1 : ℕ)) 1)))
        (sourceDerivative N f Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1))) := by
  let c : ℝ := ((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2
  let H : PhaseIndex N → ℝ → ℂ := fun i =>
    unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1
  let V : PhaseIndex N → ℝ → ℂ := fun i =>
    unitRescaledVerticalReadout N f (phaseReadout N r s i) 1
  have hH (i : PhaseIndex N) : Continuous (H i) := by
    exact continuous_unitRescaledHorizontalReadout N f (phaseReadout N r s i)
      (by norm_num : (0 : ℝ) < 1)
  have hV (i : PhaseIndex N) : Continuous (V i) := by
    exact continuous_unitRescaledVerticalReadout N f (phaseReadout N r s i)
      (by norm_num : (0 : ℝ) < 1)
  have hInt (i : PhaseIndex N) : IntervalIntegrable (fun t : ℝ =>
      c * ((starRingEnd ℂ) (H i t) * V i t).re) volume 0 1 :=
    (continuous_const.mul (Complex.continuous_re.comp
      ((Complex.conjCLE.continuous.comp (hH i)).mul (hV i)))).intervalIntegrable 0 1
  have hpair (i : PhaseIndex N) :
      (l2Pair (H i) (V i)).re =
      ∫ t in (0 : ℝ)..1, ((starRingEnd ℂ) (H i t) * V i t).re := by
    have hI : IntervalIntegrable (fun t : ℝ =>
        (starRingEnd ℂ) (H i t) * V i t) volume 0 1 :=
      ((Complex.conjCLE.continuous.comp (hH i)).mul (hV i)).intervalIntegrable 0 1
    unfold l2Pair
    change Complex.reCLM (∫ t in (0 : ℝ)..1, (starRingEnd ℂ) (H i t) * V i t) = _
    rw [← Complex.reCLM.intervalIntegral_comp_comm hI]
    apply intervalIntegral.integral_congr
    intro t _
    rfl
  have havg (t : ℝ) :
      c * ∑ i : PhaseIndex N, ((starRingEnd ℂ) (H i t) * V i t).re =
      lossPair N r s
        (sourceDerivative N f 1 (ofComplex (point (t * (N + 1 : ℕ)) 1)))
        (sourceDerivative N f Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1))) := by
    exact phaseAverage_rescaledReadouts_re_eq_loss N f r s t
  unfold phasePairExact
  change (((c : ℂ) * ∑ i : PhaseIndex N, l2Pair (H i) (V i)).re) = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsumre :
      (∑ i : PhaseIndex N, l2Pair (H i) (V i)).re =
        ∑ i : PhaseIndex N, (l2Pair (H i) (V i)).re := by
    simp
  rw [hsumre, Finset.mul_sum]
  simp_rw [hpair, ← intervalIntegral.integral_const_mul]
  have hsumIntegral :
      (∑ i : PhaseIndex N, ∫ t in (0 : ℝ)..1,
        c * ((starRingEnd ℂ) (H i t) * V i t).re) =
      ∫ t in (0 : ℝ)..1, ∑ i : PhaseIndex N,
        c * ((starRingEnd ℂ) (H i t) * V i t).re := by
    symm
    simpa using
      (intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun i t => c * ((starRingEnd ℂ) (H i t) * V i t).re)
        (fun i _ => hInt i))
  rw [hsumIntegral]
  apply intervalIntegral.integral_congr
  intro t _
  change (∑ i : PhaseIndex N, c * ((starRingEnd ℂ) (H i t) * V i t).re) =
    lossPair N r s
      (sourceDerivative N f 1 (ofComplex (point (t * (N + 1 : ℕ)) 1)))
      (sourceDerivative N f Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1)))
  rw [← Finset.mul_sum Finset.univ (fun i =>
    ((starRingEnd ℂ) (H i t) * V i t).re) c]
  exact havg t


private theorem conj_mul_re_eq_mul_conj_re (a b : ℂ) :
    ((starRingEnd ℂ) a * b).re = (a * (starRingEnd ℂ) b).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem diagonal_modal_loss_eq_zero
    (e : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (e : ℝ))
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    lossPair N r s
      ((((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) • coefficientVector N g n y)
      (coefficientHeightVector N g n y) = 0 := by
  have h := real_weighted_diagonal_mixed_eq_zero N r s e g n hy
  unfold lossPair
  unfold coefficientMixedLoss complexLoss at h
  simp only [map_smul, inner_smul_left]
  rw [mul_sub, Complex.sub_re] at h
  exact h

/-- For a Maass cusp eigenform with exceptional eigenvalue in `(0, 1/4)`, every Fourier partial phase
pairing has zero real part, because each diagonal Fourier mode has vanishing mixed loss. -/
theorem phasePairPartial_re_eq_zero
    (e : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (e : ℝ))
    (M : ℕ) : (phasePairPartial N g r s M).re = 0 := by
  let c : ℝ := ((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2
  let H : PhaseIndex N → ℝ → ℂ := fun i =>
    unitRescaledHorizontalReadout N g (phaseReadout N r s i) 1
  let V : PhaseIndex N → ℝ → ℂ := fun i =>
    unitRescaledVerticalReadout N g (phaseReadout N r s i) 1
  have hH (i : PhaseIndex N) (n : ℤ) :
      l2Pair (fourierChar n) (H i) =
        (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
          phaseReadout N r s i (coefficientVector N g n 1) := by
    exact l2Pair_fourierChar_unitRescaledHorizontalReadout N g
      (phaseReadout N r s i) n (by norm_num : (0 : ℝ) < 1)
  have hV (i : PhaseIndex N) (n : ℤ) :
      l2Pair (fourierChar n) (V i) =
        phaseReadout N r s i (coefficientHeightVector N g n 1) := by
    exact l2Pair_fourierChar_unitRescaledVerticalReadout N g
      (phaseReadout N r s i) n (by norm_num : (0 : ℝ) < 1)
  have hdiag (n : ℤ) :
      c * ∑ i : PhaseIndex N,
        ((starRingEnd ℂ) (l2Pair (fourierChar n) (H i)) *
          l2Pair (fourierChar n) (V i)).re = 0 := by
    change phaseAverage N (fun i =>
      ((starRingEnd ℂ) (l2Pair (fourierChar n) (H i)) *
        l2Pair (fourierChar n) (V i)).re) = 0
    calc
      phaseAverage N (fun i =>
          ((starRingEnd ℂ) (l2Pair (fourierChar n) (H i)) *
            l2Pair (fourierChar n) (V i)).re) =
          phaseAverage N (fun i =>
            (phaseReadout N r s i
              ((((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) •
                coefficientVector N g n 1) *
              (starRingEnd ℂ) (phaseReadout N r s i
                (coefficientHeightVector N g n 1))).re) := by
        congr 2
        funext i
        rw [hH, hV, map_smul]
        simp only [smul_eq_mul]
        exact conj_mul_re_eq_mul_conj_re _ _
      _ = lossPair N r s
          ((((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) •
            coefficientVector N g n 1)
          (coefficientHeightVector N g n 1) :=
        phaseAverage_pair N r s _ _
      _ = 0 := diagonal_modal_loss_eq_zero N r s e g n (by norm_num)

  unfold phasePairPartial
  change (((c : ℂ) * ∑ i : PhaseIndex N,
    l2Pair (fourierPartialSum (H i) M) (fourierPartialSum (V i) M)).re) = 0
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsumre :
      (∑ i : PhaseIndex N,
        l2Pair (fourierPartialSum (H i) M) (fourierPartialSum (V i) M)).re =
      ∑ i : PhaseIndex N,
        (l2Pair (fourierPartialSum (H i) M) (fourierPartialSum (V i) M)).re := by
    simp
  rw [hsumre]
  simp_rw [l2Pair_fourierPartialSum_eq_diagonal]
  simp only [Complex.re_sum]
  have hswap :
      (∑ i : PhaseIndex N, c * ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ((starRingEnd ℂ) (l2Pair (fourierChar n) (H i)) *
          l2Pair (fourierChar n) (V i)).re) =
      ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), c * ∑ i : PhaseIndex N,
        ((starRingEnd ℂ) (l2Pair (fourierChar n) (H i)) *
          l2Pair (fourierChar n) (V i)).re := by
    calc
      (∑ i : PhaseIndex N, c * ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ((starRingEnd ℂ) (l2Pair (fourierChar n) (H i)) *
            l2Pair (fourierChar n) (V i)).re) =
          ∑ i : PhaseIndex N, ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), c *
            ((starRingEnd ℂ) (l2Pair (fourierChar n) (H i)) *
              l2Pair (fourierChar n) (V i)).re := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ i : PhaseIndex N, c *
          ((starRingEnd ℂ) (l2Pair (fourierChar n) (H i)) *
            l2Pair (fourierChar n) (V i)).re := by
            rw [Finset.sum_comm]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro n _
            rw [Finset.mul_sum]
  rw [Finset.mul_sum, hswap]
  exact Finset.sum_eq_zero fun n hn => hdiag n


/-- The Fourier partial phase pairings converge to the exact phase pairing as `M → ∞`. -/
theorem tendsto_phasePairPartial :
    Tendsto (phasePairPartial N f r s) atTop (nhds (phasePairExact N f r s)) := by
  classical
  unfold phasePairPartial phasePairExact
  have hsum (I : Finset (PhaseIndex N)) :
      Tendsto (fun M : ℕ => ∑ i ∈ I,
        l2Pair
          (fourierPartialSum
            (unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1) M)
          (fourierPartialSum
            (unitRescaledVerticalReadout N f (phaseReadout N r s i) 1) M)) atTop
        (nhds (∑ i ∈ I,
          l2Pair
            (unitRescaledHorizontalReadout N f (phaseReadout N r s i) 1)
            (unitRescaledVerticalReadout N f (phaseReadout N r s i) 1))) := by
    induction I using Finset.induction_on with
    | empty => simp
    | insert i I hi hI =>
      have hi' := tendsto_l2Pair_fourierPartialSum
        (continuous_unitRescaledHorizontalReadout N f (phaseReadout N r s i)
          (by norm_num : (0 : ℝ) < 1))
        (continuous_unitRescaledVerticalReadout N f (phaseReadout N r s i)
          (by norm_num : (0 : ℝ) < 1))
      simpa [Finset.sum_insert, hi] using hi'.add hI
  simpa only [Finset.sum_const_zero, Finset.sum_const] using
    (hsum Finset.univ).const_mul ((((N + 1 : ℕ) : ℝ)⁻¹ ^ (3 : ℕ) / 2 : ℝ) : ℂ)

/-- For a Maass cusp eigenform for `Γ(N+1)` with exceptional eigenvalue in `(0, 1/4)`, the period
mean of the mixed transfer loss between horizontal and vertical derivatives at height one is zero. -/
theorem unitLossMean_eq_zero
    (e : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (e : ℝ)) :
    ∫ t in (0 : ℝ)..1, lossPair N r s
      (sourceDerivative N g 1 (ofComplex (point (t * (N + 1 : ℕ)) 1)))
      (sourceDerivative N g Complex.I (ofComplex (point (t * (N + 1 : ℕ)) 1))) = 0 := by
  have hlim : Tendsto (fun M : ℕ => (phasePairPartial N g r s M).re) atTop
      (nhds ((phasePairExact N g r s).re)) :=
    Complex.continuous_re.tendsto _ |>.comp (tendsto_phasePairPartial N g r s)
  have hzero : Tendsto (fun M : ℕ => (phasePairPartial N g r s M).re) atTop (nhds 0) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) using 1
    funext M
    exact phasePairPartial_re_eq_zero N r s e g M
  have hexact : (phasePairExact N g r s).re = 0 := tendsto_nhds_unique hlim hzero
  exact (phasePairExact_re_eq_unitLossMean N g r s).symm.trans hexact

end
end GaloisForLFunctions.RHTower.SelbergMaassPhaseProductMean
