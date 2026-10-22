import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureCorrelationBridge
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOriginLogarithmicRemainder

/-!
# Suzuki equation (2.5)

This module proves the exact distributional passage from Suzuki's source screw kernel `g` to the
finite-aperture Weil quadratic form. The proof treats all four terms in equation (2.2): the
Hadamard finite part, scalar delta mass, every visible Mangoldt hinge including a possible endpoint
atom, and the ordinary `C²` remainder curvature. The final theorem is the literal double interval
integral in equation (2.5), identified with the already source-locked four-block form.
-/

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Fixed-aperture version of Suzuki's finite prime hinge sum. Unlike the floor-varying source
presentation, this expression is visibly continuous. -/
noncomputable def suzukiVisiblePrimeHingeKernel (a t : ℝ) : ℝ :=
  ∑ n ∈ suzukiRestrictedWeilIndices a,
    screwPrimeWeight n * max 0 (|t| - Real.log n)

theorem continuous_suzukiVisiblePrimeHingeKernel (a : ℝ) :
    Continuous (suzukiVisiblePrimeHingeKernel a) := by
  unfold suzukiVisiblePrimeHingeKernel
  fun_prop

theorem suzukiVisiblePrimeHingeKernel_eq_screwPrimeSum
    {a t : ℝ} (ht : |t| ≤ 2 * a) :
    suzukiVisiblePrimeHingeKernel a t = screwPrimeSum |t| := by
  have hexp : Real.exp |t| ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr ht
  have hfloor : ⌊Real.exp |t|⌋₊ ≤ ⌊Real.exp (2 * a)⌋₊ := Nat.floor_mono hexp
  have h := screwPrimeSum_eq_sum_max hfloor
  unfold suzukiVisiblePrimeHingeKernel suzukiRestrictedWeilIndices
    RHTower.suzukiVisibleWeilIndices
  exact h.symm

theorem continuous_suzukiOriginRemainder : Continuous suzukiOriginRemainder :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_suzukiOriginRemainder t).continuousAt

/-- The globally continuous, fixed-aperture realization of Suzuki's equation (2.2). It agrees with
the literal floor-varying source screw throughout the difference interval. -/
noncomputable def suzukiApertureScrewExpansion (a t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * |t| * Real.log |t| + suzukiOriginLinearCoeff * |t| +
    suzukiVisiblePrimeHingeKernel a t + suzukiOriginRemainder t

theorem continuous_suzukiApertureScrewExpansion (a : ℝ) :
    Continuous (suzukiApertureScrewExpansion a) := by
  unfold suzukiApertureScrewExpansion
  have h := ((((Real.continuous_mul_log.comp continuous_abs).const_mul (1 / 2)).add
    (continuous_abs.const_mul suzukiOriginLinearCoeff)).add
    (continuous_suzukiVisiblePrimeHingeKernel a)).add continuous_suzukiOriginRemainder
  convert h using 1
  funext t
  simp only [Function.comp_apply, Pi.add_apply]
  ring

theorem suzukiApertureScrewExpansion_eq_source
    {a t : ℝ} (ht : |t| ≤ 2 * a) :
    suzukiApertureScrewExpansion a t = suzukiSourceScrew t := by
  unfold suzukiApertureScrewExpansion
  rw [suzuki_equation_two_two,
    suzukiVisiblePrimeHingeKernel_eq_screwPrimeSum ht]

theorem continuous_suzukiCoreDerivativeCorrelation
    {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Continuous (fun t => screwCrossCorr (deriv u) (deriv u) t) := by
  have h := (continuous_suzukiCoreAutocorrelation_secondDerivative u).neg
  convert h using 1
  funext t
  have hrel := suzukiCoreAutocorrelation_secondDerivative_eq_neg_derivativeCorrelation u t
  change screwCrossCorr (deriv u) (deriv u) t =
    -screwCrossCorr u (deriv (deriv u)) t
  rw [hrel]
  ring

private theorem suzukiCoreAutocorrelation_boundaryData
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    let R := 2 * A.1
    let c := suzukiCoreAutocorrelation u
    let c' := fun t => screwCrossCorr u (deriv u) t
    c R = 0 ∧ c (-R) = 0 ∧ c' R = 0 ∧ c' (-R) = 0 := by
  dsimp only
  have hsep : 2 * u.supportRadius < 2 * A.1 := by
    linarith [u.supportRadius_lt_aperture]
  exact ⟨
    screwCrossCorr_eq_zero_of_support_radius_pos u.support_subset u.support_subset hsep,
    screwCrossCorr_eq_zero_of_support_radius_neg u.support_subset u.support_subset (by
      linarith [hsep]),
    screwCrossCorr_eq_zero_of_support_radius_pos u.support_subset
      (core_deriv_support_subset_radius u) hsep,
    screwCrossCorr_eq_zero_of_support_radius_neg u.support_subset
      (core_deriv_support_subset_radius u) (by linarith [hsep])⟩

/-- The `A|t|` distribution in equation (2.2) contributes exactly the scalar mass `-2A`. -/
theorem suzuki_abs_derivativeCorrelation
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ t in (-(2 * A.1))..(2 * A.1),
      |t| * screwCrossCorr (deriv u) (deriv u) t) =
      -2 * ∫ x : ℝ, u x ^ (2 : ℕ) := by
  let R := 2 * A.1
  let c := suzukiCoreAutocorrelation u
  let c' := fun t => screwCrossCorr u (deriv u) t
  let c'' := fun t => screwCrossCorr u (deriv (deriv u)) t
  have hR : 0 < R := by dsimp [R]; linarith [A.property]
  have hcD : ∀ t, HasDerivAt c (c' t) t := fun t =>
    hasDerivAt_suzukiCoreAutocorrelation u t
  have hc'D : ∀ t, HasDerivAt c' (c'' t) t := fun t =>
    hasDerivAt_suzukiCoreAutocorrelation_derivative u t
  have hc''Cont : Continuous c'' :=
    continuous_suzukiCoreAutocorrelation_secondDerivative u
  obtain ⟨hcR, hcnR, hc'R, hc'nR⟩ := suzukiCoreAutocorrelation_boundaryData A u
  have hatom := neg_integral_abs_mul_secondDeriv hR c c' c'' hcD hc'D hc''Cont
    hcR hcnR hc'R hc'nR
  have hcorr :
      (∫ t in (-R)..R, |t| * screwCrossCorr (deriv u) (deriv u) t) =
        -(∫ t in (-R)..R, |t| * c'' t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [c'']
    rw [suzukiCoreAutocorrelation_secondDerivative_eq_neg_derivativeCorrelation]
    ring
  have hc0 := suzukiCoreAutocorrelation_zero u
  dsimp only [R, c] at hatom hcorr hc0 ⊢
  rw [hcorr, hatom, hc0]

private theorem primePairing_eq_autocorrelation
    {a : ℝ} (u : SuzukiRestrictedWeilCore a) (ell : ℝ) :
    l2Pairing (fun x => u (x + ell)) u = suzukiCoreAutocorrelation u ell ∧
      l2Pairing (fun x => u (x - ell)) u = suzukiCoreAutocorrelation u (-ell) := by
  constructor
  · unfold l2Pairing suzukiCoreAutocorrelation screwCrossCorr
    apply MeasureTheory.integral_congr_ae
    exact ae_of_all _ fun x => by
      change u (x + ell) * u x = u x * u (ell + x)
      rw [add_comm x ell, mul_comm]
  · unfold l2Pairing suzukiCoreAutocorrelation screwCrossCorr
    apply MeasureTheory.integral_congr_ae
    exact ae_of_all _ fun x => by
      change u (x - ell) * u x = u x * u (-ell + x)
      rw [show x - ell = -ell + x by ring, mul_comm]

/-- Complete finite Mangoldt hinge calculation in Suzuki's derivation of equation (2.5). The
non-strict cutoff handles the arithmetically possible endpoint `n = exp(2a)` exactly. -/
theorem suzuki_primeHinge_derivativeCorrelation
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ t in (-(2 * A.1))..(2 * A.1),
      suzukiVisiblePrimeHingeKernel A.1 t *
        screwCrossCorr (deriv u) (deriv u) t) =
      weilPrimeBlock (suzukiRestrictedWeilIndices A.1) u u := by
  classical
  let R := 2 * A.1
  let c := suzukiCoreAutocorrelation u
  let c' := fun t => screwCrossCorr u (deriv u) t
  let c'' := fun t => screwCrossCorr u (deriv (deriv u)) t
  have hcD : ∀ t, HasDerivAt c (c' t) t := fun t =>
    hasDerivAt_suzukiCoreAutocorrelation u t
  have hc'D : ∀ t, HasDerivAt c' (c'' t) t := fun t =>
    hasDerivAt_suzukiCoreAutocorrelation_derivative u t
  have hc''Cont : Continuous c'' :=
    continuous_suzukiCoreAutocorrelation_secondDerivative u
  obtain ⟨hcR, hcnR, hc'R, hc'nR⟩ := suzukiCoreAutocorrelation_boundaryData A u
  have hcorrCont := continuous_suzukiCoreDerivativeCorrelation u
  have hterm : ∀ n ∈ suzukiRestrictedWeilIndices A.1,
      (∫ t in (-R)..R,
        screwPrimeWeight n * max 0 (|t| - Real.log n) *
          screwCrossCorr (deriv u) (deriv u) t) =
        -primePairWeight n *
          (l2Pairing (fun x => u (x + Real.log n)) u +
            l2Pairing (fun x => u (x - Real.log n)) u) := by
    intro n hn
    have hnIcc : n ∈ Finset.Icc 2 ⌊Real.exp R⌋₊ := by
      simpa only [suzukiRestrictedWeilIndices, RHTower.suzukiVisibleWeilIndices, R] using hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hnIcc).1
    have hnposNat : 0 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
    have hnOne : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hell : 0 < Real.log n := Real.log_pos hnOne
    have hnfloor : (n : ℝ) ≤ (⌊Real.exp R⌋₊ : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hnIcc).2
    have hnexp : (n : ℝ) ≤ Real.exp R :=
      hnfloor.trans (Nat.floor_le (Real.exp_pos R).le)
    have hellR : Real.log n ≤ R := (Real.log_le_iff_le_exp hnpos).mpr hnexp
    have hatom := neg_integral_hinge_mul_secondDeriv_of_le hell hellR c c' c''
      hcD hc'D hc''Cont hcR hcnR hc'R hc'nR
    have hcorr :
        (∫ t in (-R)..R, max 0 (|t| - Real.log n) *
          screwCrossCorr (deriv u) (deriv u) t) =
          -(c (Real.log n) + c (-Real.log n)) := by
      calc
        (∫ t in (-R)..R, max 0 (|t| - Real.log n) *
            screwCrossCorr (deriv u) (deriv u) t) =
            -(∫ t in (-R)..R, max 0 (|t| - Real.log n) * c'' t) := by
              rw [← intervalIntegral.integral_neg]
              apply intervalIntegral.integral_congr
              intro t _
              dsimp only [c'']
              rw [suzukiCoreAutocorrelation_secondDerivative_eq_neg_derivativeCorrelation]
              ring
        _ = -(c (Real.log n) + c (-Real.log n)) := hatom
    obtain ⟨hpair, hpairNeg⟩ := primePairing_eq_autocorrelation u (Real.log n)
    calc
      (∫ t in (-R)..R,
          screwPrimeWeight n * max 0 (|t| - Real.log n) *
            screwCrossCorr (deriv u) (deriv u) t) =
          screwPrimeWeight n * (∫ t in (-R)..R,
            max 0 (|t| - Real.log n) *
              screwCrossCorr (deriv u) (deriv u) t) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro t _
            ring
      _ = screwPrimeWeight n * (-(c (Real.log n) + c (-Real.log n))) := by
        rw [hcorr]
      _ = -primePairWeight n *
          (l2Pairing (fun x => u (x + Real.log n)) u +
            l2Pairing (fun x => u (x - Real.log n)) u) := by
            dsimp only [c]
            rw [← hpair, ← hpairNeg]
            unfold screwPrimeWeight primePairWeight
            ring
  have hrewrite :
      (∫ t in (-R)..R,
        suzukiVisiblePrimeHingeKernel A.1 t *
          screwCrossCorr (deriv u) (deriv u) t) =
        ∫ t in (-R)..R, ∑ n ∈ suzukiRestrictedWeilIndices A.1,
          screwPrimeWeight n * max 0 (|t| - Real.log n) *
            screwCrossCorr (deriv u) (deriv u) t := by
    apply intervalIntegral.integral_congr
    intro t _
    unfold suzukiVisiblePrimeHingeKernel
    simp only [Finset.sum_mul]
  rw [hrewrite, intervalIntegral.integral_finsetSum]
  · rw [Finset.sum_congr rfl hterm]
    unfold weilPrimeBlock
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · intro n hn
    have hhinge : Continuous fun t : ℝ => max 0 (|t| - Real.log n) := by fun_prop
    exact ((hhinge.const_mul (screwPrimeWeight n)).mul hcorrCont).intervalIntegrable (-R) R

/-- Suzuki's `C²` remainder contributes exactly the smooth convolution block. -/
theorem suzuki_remainder_derivativeCorrelation
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ t in (-(2 * A.1))..(2 * A.1),
      suzukiOriginRemainder t * screwCrossCorr (deriv u) (deriv u) t) =
      weilSmoothBlock A.1 suzukiOriginRemainderCurvature u u := by
  let R := 2 * A.1
  let c := suzukiCoreAutocorrelation u
  let c' := fun t => screwCrossCorr u (deriv u) t
  let c'' := fun t => screwCrossCorr u (deriv (deriv u)) t
  have hcD : ∀ t, HasDerivAt c (c' t) t := fun t =>
    hasDerivAt_suzukiCoreAutocorrelation u t
  have hc'D : ∀ t, HasDerivAt c' (c'' t) t := fun t =>
    hasDerivAt_suzukiCoreAutocorrelation_derivative u t
  have hc''Cont : Continuous c'' :=
    continuous_suzukiCoreAutocorrelation_secondDerivative u
  obtain ⟨hcR, hcnR, hc'R, hc'nR⟩ := suzukiCoreAutocorrelation_boundaryData A u
  have hatom := neg_integral_suzukiOriginRemainder_mul_secondDeriv c c' c''
    hcD hc'D hc''Cont hcR hcnR hc'R hc'nR
  have hcorr :
      (∫ t in (-R)..R,
        suzukiOriginRemainder t * screwCrossCorr (deriv u) (deriv u) t) =
        -(∫ t in (-R)..R, suzukiOriginRemainder t * c'' t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [c'']
    rw [suzukiCoreAutocorrelation_secondDerivative_eq_neg_derivativeCorrelation]
    ring
  have hdouble := suzukiCoreDoubleIntegral_eq_correlation A u
    continuous_suzukiOriginRemainderCurvature
  have hsmooth :
      weilSmoothBlock A.1 suzukiOriginRemainderCurvature u u =
        -(∫ t in (-R)..R, suzukiOriginRemainderCurvature t * c t) := by
    unfold weilSmoothBlock
    dsimp only [R, c]
    have hmove :
        (∫ x in (-A.1)..A.1,
          (∫ y in (-A.1)..A.1, suzukiOriginRemainderCurvature (x - y) * u y) * u x) =
          ∫ x in (-A.1)..A.1, ∫ y in (-A.1)..A.1,
            suzukiOriginRemainderCurvature (x - y) * u y * u x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [intervalIntegral.integral_mul_const]
    rw [hmove, hdouble]
  dsimp only [R, c] at hatom hcorr hsmooth ⊢
  rw [hcorr, hatom, ← hsmooth]

private theorem suzukiCore_intervalSquare_eq_integral
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ x in (-A.1)..A.1, u x ^ (2 : ℕ)) = ∫ x : ℝ, u x ^ (2 : ℕ) := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hux : u x ≠ 0 := by
    intro hz
    exact hx (by simp [hz])
  have hmem := u.support_subset_aperture hux
  exact ⟨hmem.1, hmem.2.le⟩

/-- One-variable form of Suzuki's equation (2.5), after the exact aperture shear. -/
theorem suzuki_equation_two_five_correlation
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ t in (-(2 * A.1))..(2 * A.1),
      suzukiApertureScrewExpansion A.1 t *
        screwCrossCorr (deriv u) (deriv u) t) =
      suzukiRestrictedWeilForm A.1 u u := by
  let R := 2 * A.1
  let q := fun t => screwCrossCorr (deriv u) (deriv u) t
  let flog := fun t : ℝ => |t| * Real.log |t| * q t
  let fabs := fun t : ℝ => |t| * q t
  let fprime := fun t : ℝ => suzukiVisiblePrimeHingeKernel A.1 t * q t
  let frem := fun t : ℝ => suzukiOriginRemainder t * q t
  have hq : Continuous q := continuous_suzukiCoreDerivativeCorrelation u
  have hlog : Continuous flog := by dsimp only [flog]; fun_prop
  have habs : Continuous fabs := by dsimp only [fabs]; fun_prop
  have hprime : Continuous fprime := by
    exact (continuous_suzukiVisiblePrimeHingeKernel A.1).mul hq
  have hrem : Continuous frem := continuous_suzukiOriginRemainder.mul hq
  have hsplit :
      (∫ t in (-R)..R, suzukiApertureScrewExpansion A.1 t * q t) =
        (1 / 2 : ℝ) * (∫ t in (-R)..R, flog t) +
          suzukiOriginLinearCoeff * (∫ t in (-R)..R, fabs t) +
          (∫ t in (-R)..R, fprime t) + (∫ t in (-R)..R, frem t) := by
    calc
      (∫ t in (-R)..R, suzukiApertureScrewExpansion A.1 t * q t) =
          ∫ t in (-R)..R,
            ((1 / 2 : ℝ) * flog t + suzukiOriginLinearCoeff * fabs t +
              fprime t + frem t) := by
            apply intervalIntegral.integral_congr
            intro t _
            dsimp only [flog, fabs, fprime, frem]
            unfold suzukiApertureScrewExpansion
            ring
      _ = (1 / 2 : ℝ) * (∫ t in (-R)..R, flog t) +
          suzukiOriginLinearCoeff * (∫ t in (-R)..R, fabs t) +
          (∫ t in (-R)..R, fprime t) + (∫ t in (-R)..R, frem t) := by
            have hiLog : IntervalIntegrable (fun t => (1 / 2 : ℝ) * flog t)
                volume (-R) R :=
              (hlog.const_mul (1 / 2 : ℝ)).intervalIntegrable (-R) R
            have hiAbs : IntervalIntegrable
                (fun t => suzukiOriginLinearCoeff * fabs t) volume (-R) R :=
              (habs.const_mul suzukiOriginLinearCoeff).intervalIntegrable (-R) R
            have hiPrime : IntervalIntegrable fprime volume (-R) R :=
              hprime.intervalIntegrable (-R) R
            have hiRem : IntervalIntegrable frem volume (-R) R :=
              hrem.intervalIntegrable (-R) R
            rw [intervalIntegral.integral_add ((hiLog.add hiAbs).add hiPrime) hiRem,
              intervalIntegral.integral_add (hiLog.add hiAbs) hiPrime,
              intervalIntegral.integral_add hiLog hiAbs,
              intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
  have hlogEval := suzuki_equation_two_four_correlation A u
  have habsEval := suzuki_abs_derivativeCorrelation A u
  have hprimeEval := suzuki_primeHinge_derivativeCorrelation A u
  have hremEval := suzuki_remainder_derivativeCorrelation A u
  have hfinite := suzukiWeilFinitePartBlock_eq_energy A u
  have hmass := suzukiCore_intervalSquare_eq_integral A u
  have hmassMul : (∫ x in (-A.1)..A.1, u x * u x) = ∫ x : ℝ, u x ^ (2 : ℕ) := by
    simpa only [pow_two] using hmass
  have hcoeff : suzukiOriginLinearCoeff = suzukiWeilArchimedeanConstant := rfl
  rw [suzukiRestrictedWeilForm_eq_originRemainderFourBlocks, hfinite]
  unfold weilScalarBlock
  dsimp only [R, q, flog, fabs, fprime, frem] at hsplit hlogEval habsEval hprimeEval hremEval ⊢
  rw [hsplit, hlogEval, habsEval, hprimeEval, hremEval, hmassMul, hcoeff]
  ring

/-- Suzuki 2026, equation (2.5), as the literal double interval screw quadratic form on the
source-locked smooth core. Every term on the right is the exact source Weil form, with no free
kernel, cutoff, integrability premise, or endpoint exception. -/
theorem suzuki_equation_two_five
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ x in (-A.1)..A.1, ∫ y in (-A.1)..A.1,
      suzukiSourceScrew (x - y) * deriv u y * deriv u x) =
      suzukiRestrictedWeilForm A.1 u u := by
  have hsource :
      (∫ x in (-A.1)..A.1, ∫ y in (-A.1)..A.1,
        suzukiSourceScrew (x - y) * deriv u y * deriv u x) =
        ∫ x in (-A.1)..A.1, ∫ y in (-A.1)..A.1,
          suzukiApertureScrewExpansion A.1 (x - y) * deriv u y * deriv u x := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply intervalIntegral.integral_congr
    intro y hy
    have hbounds : (-A.1 : ℝ) ≤ A.1 := by linarith [A.property]
    rw [uIcc_of_le hbounds] at hx hy
    have hdiff : |x - y| ≤ 2 * A.1 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    dsimp only
    rw [suzukiApertureScrewExpansion_eq_source hdiff]
  rw [hsource,
    suzukiCoreDerivativeDoubleIntegral_eq_correlation A u
      (continuous_suzukiApertureScrewExpansion A.1),
    suzuki_equation_two_five_correlation A u]

end GaloisForLFunctions.RHTower
