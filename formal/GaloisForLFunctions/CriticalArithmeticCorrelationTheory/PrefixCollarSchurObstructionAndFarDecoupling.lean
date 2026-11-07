import Mathlib.NumberTheory.Bertrand
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UnrestrictedAtomicGardingFailsAndCollarGardingHolds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFarComplementHasAnExplicitRatioInterval
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.QuadraticOverlapConductorResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorEnergiesHavePolynomialBounds
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormNormCosts
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds

/-!
# Sharp two-sided resolution of prefix–collar Schur decoupling at a fixed critical ratio

At a fixed critical ratio `R = lim c_N⁸ / log N > 0`, let
`U_x = normalizedCentredAtomicTest tiltedUnitSpline x c_N N` be the unit-`ℓ²` centered atomic
synthesis and `M = N / linearDefectCutoff c_N` the overlapping top-collar boundary.

1. **Physical tearing on `(conductorSubspace Q₁ N)ᗮ` fails (`4 / 13` Schur obstruction).**
   For the low-packet cutoff `Q₁ = ⌊(log N)^{13/32}⌋₊`, let `q_N` be a prime in
   `(max 2 Q₁, 2 · max 2 Q₁]` and
   `z_N = v_{q_N} - (conductorSubspace Q₁ N).starProjection v_{q_N} ∈ (conductorSubspace Q₁ N)ᗮ`.
   Splitting `z_N = p_N + y_N` across `[1, M]` and `Ioc M N` gives
   `|weilBilin U_{y_N} U_{p_N}|² / (weilQuad U_{p_N} · (weilQuad U_{y_N} + B_R ‖U_{y_N}‖₂²)) → 4 / 13`
   at every `R > 0` and every `B_R ∈ ℝ` (`tendsto_prime_quasimode_prefix_collar_schur_ratio`,
   `not_naive_physical_prefix_collar_schur_decoupling`).

2. **Conductor-adapted splitting on `(conductorSubspace R₁ N)ᗮ` succeeds (`o(1)` Schur decoupling).**
   When conductors up to `R₁ = ⌊N^θ⌋₊` (`θ = 1 / (1 + log log N)⁵`) are kept whole and only the
   far-conductor complement is split at `M`, literal `o(1)` Schur decoupling holds across `M`:
   there exists `B_R ≥ 0` such that for every `ε > 0`, eventually in `N` along `c_N⁸ / log N → R`,
   `|weilBilin U_y U_p|² ≤ ε · weilQuad U_p · (weilQuad U_y + B_R ‖U_y‖₂²)`
   for every `p ∈ (conductorSubspace R₁ N)ᗮ` vanishing above `M` and every `y` vanishing on `[1, M]`
   (`exists_far_prefix_collar_schur_decoupling_below_ratio`,
   `exists_far_prefix_collar_schur_decoupling`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23
open scoped Classical BigOperators RealInnerProductSpace Matrix CompactlySupported

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CompletedArithmeticForms CriticalScaleArithmeticRigidity ArithmeticElectrostatics
  ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory ArithmeticCouplingTheory
  BezoutValuationIncidence SelectiveMultiscaleArithmeticPositivity
  CriticalArithmeticCorrelationTheory.ExplicitShell HTGeometry
  RenormalizedBiarithmeticGeometry ArithmeticEffectivityTheory

/-! ### 1. Polarized Weil bilinear form and centered atomic matrix identities -/

/-- The polarized bilinear form attached to `weilQuad`. -/
def weilBilin (f g : ℝ → ℝ) : ℝ :=
  (weilQuad (fun u => f u + g u) - weilQuad (fun u => f u - g u)) / 4

theorem weilBilin_comm {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    weilBilin f g = weilBilin g f := by
  unfold weilBilin
  have hadd : (fun u => f u + g u) = fun u => g u + f u := funext fun _ => add_comm _ _
  have hsub : (fun u => f u - g u) = fun u => (-1 : ℝ) * (g u - f u) := funext fun _ => by ring
  rw [hadd, hsub, weilQuad_const_mul (hg.sub hf) (hgc.sub hfc) (-1)]
  ring

/-- Translation invariance of the complete Weil quadratic form `weilQuad`. -/
theorem weilQuad_comp_add_right {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (b : ℝ) : weilQuad (fun u => f (u + b)) = weilQuad f := by
  have hfb : ContDiff ℝ 2 (fun u => f (u + b)) := hf.comp (contDiff_id.add contDiff_const)
  have hfbc : HasCompactSupport (fun u => f (u + b)) :=
    hfc.comp_homeomorph (Homeomorph.addRight b)
  have hL2 : (∫ u, f (u + b) ^ 2) = ∫ u, f u ^ 2 :=
    integral_add_right_eq_self (fun u => f u ^ 2) b
  have hlev : levyEnergy (fun u => f (u + b)) = levyEnergy f := by
    unfold levyEnergy
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 1
    have hfn : (fun u => (f (u + b) - f (u + t + b)) ^ 2) =
        fun u => (fun v => (f v - f (v + t)) ^ 2) (u + b) :=
      funext fun u => by dsimp only; congr 2; ring
    rw [hfn]
    exact integral_add_right_eq_self (fun v => (f v - f (v + t)) ^ 2) b
  have hpr : primeSum (fun u => f (u + b)) = primeSum f := primeSum_comp_add_right f b
  have hpole_id (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      2 * coshHalfMoment g ^ 2 - 2 * sinhHalfMoment g ^ 2 =
        2 * (∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) := by
    have ic : Integrable (fun u => g u * Real.cosh (u / 2)) :=
      (hg.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hgc.mul_right
    have is : Integrable (fun u => g u * Real.sinh (u / 2)) :=
      (hg.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hgc.mul_right
    have hplus : coshHalfMoment g + sinhHalfMoment g = ∫ u, g u * Real.exp (u / 2) := by
      unfold coshHalfMoment sinhHalfMoment
      rw [← integral_add ic is]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      rw [Real.cosh_eq, Real.sinh_eq]
      ring
    have hminus : coshHalfMoment g - sinhHalfMoment g = ∫ u, g u * Real.exp (-(u / 2)) := by
      unfold coshHalfMoment sinhHalfMoment
      rw [← integral_sub ic is]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      rw [Real.cosh_eq, Real.sinh_eq]
      ring
    calc 2 * coshHalfMoment g ^ 2 - 2 * sinhHalfMoment g ^ 2
        = 2 * (coshHalfMoment g - sinhHalfMoment g) * (coshHalfMoment g + sinhHalfMoment g) := by ring
      _ = 2 * (∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) := by
          rw [hminus, hplus]
  have hpole : 2 * coshHalfMoment (fun u => f (u + b)) ^ 2 -
      2 * sinhHalfMoment (fun u => f (u + b)) ^ 2 =
      2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 := by
    rw [hpole_id _ hfb.continuous hfbc, hpole_id _ hf.continuous hfc]
    have hneg : (∫ u, f (u + b) * Real.exp (-(u / 2))) =
        Real.exp (b / 2) * ∫ v, f v * Real.exp (-(v / 2)) := by
      have heq : (fun u => f (u + b) * Real.exp (-(u / 2))) =
          fun u => Real.exp (b / 2) * ((fun v => f v * Real.exp (-(v / 2))) (u + b)) := by
        funext u
        dsimp only
        rw [mul_left_comm, ← Real.exp_add]
        congr 2; ring
      rw [heq, integral_const_mul,
        integral_add_right_eq_self (fun v => f v * Real.exp (-(v / 2))) b]
    have hpos : (∫ u, f (u + b) * Real.exp (u / 2)) =
        Real.exp (-(b / 2)) * ∫ v, f v * Real.exp (v / 2) := by
      have heq : (fun u => f (u + b) * Real.exp (u / 2)) =
          fun u => Real.exp (-(b / 2)) * ((fun v => f v * Real.exp (v / 2)) (u + b)) := by
        funext u
        dsimp only
        rw [mul_left_comm, ← Real.exp_add]
        congr 2; ring
      rw [heq, integral_const_mul,
        integral_add_right_eq_self (fun v => f v * Real.exp (v / 2)) b]
    rw [hneg, hpos]
    calc 2 * (Real.exp (b / 2) * ∫ v, f v * Real.exp (-(v / 2))) *
          (Real.exp (-(b / 2)) * ∫ v, f v * Real.exp (v / 2))
        = (Real.exp (b / 2) * Real.exp (-(b / 2))) *
            (2 * (∫ v, f v * Real.exp (-(v / 2))) * (∫ v, f v * Real.exp (v / 2))) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [weilQuad_eq hfb hfbc, weilQuad_eq hf hfc, hL2, hlev, hpr]
  linarith only [hpole]

theorem contDiff_normalizedCentredAtomicTest {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    ContDiff ℝ 2 (normalizedCentredAtomicTest φ x c N) := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  have hg : ContDiff ℝ 2 (atomDilate φ (c / N)) := hφ.comp (contDiff_id.div_const _)
  unfold normalizedCentredAtomicTest centredAtomicTest
  exact contDiff_const.mul ((contDiff_atomicTest hg N x).comp (contDiff_id.add contDiff_const))

theorem hasCompactSupport_normalizedCentredAtomicTest {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    HasCompactSupport (normalizedCentredAtomicTest φ x c N) := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  have hgs : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := by
    intro u hu
    apply hsupp
    intro hm
    exact hu ⟨by simpa only [zero_mul] using (le_div_iff₀ hw).mp hm.1, (div_le_one hw).mp hm.2⟩
  unfold normalizedCentredAtomicTest centredAtomicTest
  exact ((hasCompactSupport_atomicTest hgs N x).comp_homeomorph
    (Homeomorph.addRight (Real.log N))).mul_left

theorem normalizedCentredAtomicTest_add (φ : ℝ → ℝ) (x y : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    normalizedCentredAtomicTest φ (fun n => x n + y n) c N =
      fun u => normalizedCentredAtomicTest φ x c N u + normalizedCentredAtomicTest φ y c N u := by
  funext u
  unfold normalizedCentredAtomicTest centredAtomicTest atomicTest
  simp_rw [add_mul]
  rw [sum_add_distrib]
  ring

theorem normalizedCentredAtomicTest_sub (φ : ℝ → ℝ) (x y : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    normalizedCentredAtomicTest φ (fun n => x n - y n) c N =
      fun u => normalizedCentredAtomicTest φ x c N u - normalizedCentredAtomicTest φ y c N u := by
  funext u
  unfold normalizedCentredAtomicTest centredAtomicTest atomicTest
  simp_rw [sub_mul]
  rw [sum_sub_distrib]
  ring

theorem normalizedCentredAtomicTest_const_mul (φ : ℝ → ℝ) (α : ℝ) (x : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    normalizedCentredAtomicTest φ (fun n => α * x n) c N =
      fun u => α * normalizedCentredAtomicTest φ x c N u := by
  funext u
  unfold normalizedCentredAtomicTest centredAtomicTest atomicTest
  simp_rw [mul_assoc]
  rw [← mul_sum]
  ring

theorem normalizedCentredAtomicTest_horizonProfileVector (φ : ℝ → ℝ) (x : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    normalizedCentredAtomicTest φ (primeHorizonExtension (horizonProfileVector x N)) c N =
      normalizedCentredAtomicTest φ x c N := by
  funext u
  unfold normalizedCentredAtomicTest centredAtomicTest atomicTest
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
  rfl

/-- Unit-`ℓ²` centered atomic synthesis scales `completeWeilEnergy` by `(∫ φ²) / c`. -/
theorem weilQuad_normalizedCentredAtomicTest_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    weilQuad (normalizedCentredAtomicTest φ (primeHorizonExtension x) c N) =
      ((∫ u, φ u ^ 2) / c) * completeWeilEnergy φ c N x := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hNR
  obtain ⟨hg, hgs, _⟩ := atomDilate_facts hφ hsupp hw
  have hf : ContDiff ℝ 2 (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N))) :=
    contDiff_atomicTest hg N _
  have hfc : HasCompactSupport (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N))) :=
    hasCompactSupport_atomicTest hgs N _
  have hcent : ContDiff ℝ 2 (centredAtomicTest φ (primeHorizonExtension x) c N) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hcentc : HasCompactSupport (centredAtomicTest φ (primeHorizonExtension x) c N) :=
    hfc.comp_homeomorph (Homeomorph.addRight (Real.log N))
  have hG : (∫ u, atomDilate φ (c / N) u ^ 2) = (c / N) * ∫ u, φ u ^ 2 :=
    integral_atomDilate_sq hw
  have hGpos : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by rw [hG]; positivity
  have hmat := completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN x
  change completeWeilEnergy φ c N x = _ at hmat
  have hquad_eq : weilQuad (atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N))) =
      ((c / N) * ∫ u, φ u ^ 2) * completeWeilEnergy φ c N x := by
    rw [hmat, hG]
    field_simp [hGpos.ne', hc.ne', hNR.ne', hM.ne']
  change weilQuad (fun u => Real.sqrt N / c * centredAtomicTest φ (primeHorizonExtension x) c N u) = _
  rw [weilQuad_const_mul hcent hcentc, div_pow, Real.sq_sqrt hNR.le]
  change (N : ℝ) / c ^ 2 *
    weilQuad (fun u => atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N)) (u + Real.log N)) = _
  rw [weilQuad_comp_add_right hf hfc, hquad_eq]
  field_simp [hc.ne', hNR.ne']

/-- Polarized identity equating `weilBilin` on `normalizedCentredAtomicTest` with the Euclidean
bilinear form of `completeWeilMatrix`. -/
theorem weilBilin_normalizedCentredAtomicTest_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    weilBilin (normalizedCentredAtomicTest φ (primeHorizonExtension x) c N)
        (normalizedCentredAtomicTest φ (primeHorizonExtension y) c N) =
      ((∫ u, φ u ^ 2) / c) * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ := by
  have hext_add : (fun n => primeHorizonExtension x n + primeHorizonExtension y n) =
      primeHorizonExtension (x + y) := by
    funext n; simp only [primeHorizonExtension, PiLp.add_apply]; split_ifs <;> ring
  have hext_sub : (fun n => primeHorizonExtension x n - primeHorizonExtension y n) =
      primeHorizonExtension (x - y) := by
    funext n; simp only [primeHorizonExtension, PiLp.sub_apply]; split_ifs <;> ring
  unfold weilBilin
  rw [← normalizedCentredAtomicTest_add, ← normalizedCentredAtomicTest_sub, hext_add, hext_sub,
    weilQuad_normalizedCentredAtomicTest_eq hφ hsupp hM hc hN (x + y),
    weilQuad_normalizedCentredAtomicTest_eq hφ hsupp hM hc hN (x - y)]
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  have hpol : completeWeilEnergy φ c N (x + y) - completeWeilEnergy φ c N (x - y) =
      4 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ := by
    unfold completeWeilEnergy
    rw [map_add, map_sub, inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right, hsym y x, real_inner_comm y]
    ring
  rw [← mul_sub, hpol]
  ring

/-! ### 2. The `4 / 13` physical-tearing Schur obstruction on `(conductorSubspace Q₁ N)ᗮ` -/

/-- The low-packet conductor cutoff `Q₁(N) = ⌊(log N)^{13/32}⌋₊`. -/
def lowPacketCutoff (N : ℕ) : ℕ := ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊

/-- A Bertrand prime `q_N ∈ (max 2 (lowPacketCutoff N), 2 · max 2 (lowPacketCutoff N)]`. -/
def primeAboveLowPacket (N : ℕ) : ℕ :=
  (Nat.exists_prime_lt_and_le_two_mul (max 2 (lowPacketCutoff N)) (by positivity)).choose

theorem primeAboveLowPacket_spec (N : ℕ) :
    (primeAboveLowPacket N).Prime ∧
      max 2 (lowPacketCutoff N) < primeAboveLowPacket N ∧
      primeAboveLowPacket N ≤ 2 * max 2 (lowPacketCutoff N) :=
  (Nat.exists_prime_lt_and_le_two_mul (max 2 (lowPacketCutoff N)) (by positivity)).choose_spec

/-- The quasimode in `(conductorSubspace (lowPacketCutoff N) N)ᗮ` obtained by orthogonally
projecting the prime Ramanujan mode `v_{q_N}` off the low conductor subspace. -/
def lowPacketOrthogonalPrimeQuasimode (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  let v := normalizedRamanujanHorizonVector (primeAboveLowPacket N) N
  v - (conductorSubspace (lowPacketCutoff N) N).starProjection v

theorem lowPacketOrthogonalPrimeQuasimode_mem (N : ℕ) :
    lowPacketOrthogonalPrimeQuasimode N ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ := by
  dsimp only [lowPacketOrthogonalPrimeQuasimode]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- Euclidean vector restricting `x` to `[1, M]`. -/
def horizonPrefixVector {N : ℕ} (M : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  horizonProfileVector (fun n => if n ≤ M then primeHorizonExtension x n else 0) N

/-- Euclidean vector restricting `x` to `Ioc M N`. -/
def horizonCollarVector {N : ℕ} (M : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  horizonProfileVector (atomicTailCoefficients M (primeHorizonExtension x)) N

theorem horizonPrefixVector_add_collar {N : ℕ} (M : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    horizonPrefixVector M x + horizonCollarVector M x = x := by
  ext ⟨n, hn⟩
  change (if n ≤ M then primeHorizonExtension x n else 0) +
    (if M < n then primeHorizonExtension x n else 0) = x ⟨n, hn⟩
  rw [primeHorizonExtension_coe x ⟨n, hn⟩]
  by_cases h : n ≤ M
  · rw [if_pos h, if_neg (Nat.not_lt.mpr h), add_zero]
  · rw [if_neg h, if_pos (Nat.lt_of_not_le h), zero_add]

theorem inner_horizonPrefixVector_collar {N : ℕ} (M : ℕ)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪horizonPrefixVector M x, horizonCollarVector M y⟫ = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  refine Finset.sum_eq_zero fun ⟨n, _⟩ _ => ?_
  change (if M < n then primeHorizonExtension y n else 0) *
    (if n ≤ M then primeHorizonExtension x n else 0) = 0
  by_cases h : n ≤ M
  · rw [if_neg (Nat.not_lt.mpr h), zero_mul]
  · rw [if_neg h, mul_zero]

theorem norm_horizonPrefixVector_le {N : ℕ} (M : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖horizonPrefixVector M x‖ ≤ ‖x‖ := by
  have hsq : ‖horizonPrefixVector M x‖ ^ 2 + ‖horizonCollarVector M x‖ ^ 2 = ‖x‖ ^ 2 := by
    have h := norm_add_sq_real (horizonPrefixVector M x) (horizonCollarVector M x)
    rw [horizonPrefixVector_add_collar, inner_horizonPrefixVector_collar, mul_zero, add_zero] at h
    exact h.symm
  nlinarith only [hsq, sq_nonneg ‖horizonCollarVector M x‖, norm_nonneg (horizonPrefixVector M x),
    norm_nonneg x]

theorem norm_horizonCollarVector_le {N : ℕ} (M : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖horizonCollarVector M x‖ ≤ ‖x‖ := by
  have hsq : ‖horizonPrefixVector M x‖ ^ 2 + ‖horizonCollarVector M x‖ ^ 2 = ‖x‖ ^ 2 := by
    have h := norm_add_sq_real (horizonPrefixVector M x) (horizonCollarVector M x)
    rw [horizonPrefixVector_add_collar, inner_horizonPrefixVector_collar, mul_zero, add_zero] at h
    exact h.symm
  nlinarith only [hsq, sq_nonneg ‖horizonPrefixVector M x‖, norm_nonneg (horizonCollarVector M x),
    norm_nonneg x]

theorem primeHorizonExtension_horizonPrefixVector {N M : ℕ} (_hMN : M ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonExtension (horizonPrefixVector M x) =
      fun n => if n ≤ M then primeHorizonExtension x n else 0 := by
  funext n
  by_cases hn : n ∈ Icc 1 N
  · rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    rfl
  · simp only [primeHorizonExtension, hn, ↓reduceDIte, ite_self]

theorem primeHorizonExtension_horizonCollarVector {N M : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonExtension (horizonCollarVector M x) =
      atomicTailCoefficients M (primeHorizonExtension x) := by
  funext n
  by_cases hn : n ∈ Icc 1 N
  · rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    rfl
  · simp only [primeHorizonExtension, atomicTailCoefficients, hn, ↓reduceDIte, ite_self]

private theorem ramanujanLagCoefficient_of_prime {q : ℕ} (hq : q.Prime) (h : ℕ) :
    ramanujanLagCoefficient q h = if q ∣ h then (q : ℝ) - 1 else -1 := by
  unfold ramanujanLagCoefficient
  rw [hq.divisors, sum_pair hq.one_lt.ne, Nat.div_one, Nat.div_self hq.pos]
  have hm_q : moebiusReal q = -1 := by
    unfold moebiusReal
    rw [ArithmeticFunction.moebius_apply_prime hq]
    norm_num
  have hm_1 : moebiusReal 1 = 1 := by
    unfold moebiusReal
    simp
  rw [hm_q, hm_1, if_pos (one_dvd h)]
  split_ifs <;> push_cast <;> ring

private theorem sum_abs_normalizedRamanujanMode_prime_le {q : ℕ} (hq : q.Prime) :
    (∑ j ∈ range q, |normalizedRamanujanMode q j|) ≤ 2 * Real.sqrt (q : ℝ) := by
  have hqt : (q.totient : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.totient_prime hq, Nat.cast_sub hq.one_lt.le, Nat.cast_one]
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    linarith
  have hrange : range q = insert 0 (Ico 1 q) := by
    have := hq.pos
    ext j
    simp only [mem_range, mem_insert, mem_Ico]
    omega
  rw [hrange, sum_insert (by simp)]
  have h0 : |normalizedRamanujanMode q 0| = Real.sqrt ((q : ℝ) - 1) := by
    rw [normalizedRamanujanMode_eq_coefficient hq.pos, ramanujanLagCoefficient_of_prime hq 0,
      if_pos (dvd_zero q), hqt, abs_div, abs_of_pos hq1, abs_of_pos (Real.sqrt_pos.mpr hq1),
      Real.div_sqrt]
  have hrest : (∑ j ∈ Ico 1 q, |normalizedRamanujanMode q j|) = Real.sqrt ((q : ℝ) - 1) := by
    have hterm (j : ℕ) (hj : j ∈ Ico 1 q) :
        |normalizedRamanujanMode q j| = 1 / Real.sqrt ((q : ℝ) - 1) := by
      have hndvd : ¬(q ∣ j) := fun hd =>
        Nat.not_le.mpr (mem_Ico.mp hj).2 (Nat.le_of_dvd (mem_Ico.mp hj).1 hd)
      rw [normalizedRamanujanMode_eq_coefficient hq.pos, ramanujanLagCoefficient_of_prime hq j,
        if_neg hndvd, hqt, abs_div, abs_neg, abs_one, abs_of_pos (Real.sqrt_pos.mpr hq1)]
    rw [sum_congr rfl hterm, sum_const, Nat.card_Ico, nsmul_eq_mul,
      Nat.cast_sub hq.one_lt.le, Nat.cast_one, mul_one_div, Real.div_sqrt]
  rw [h0, hrest]
  have hle : Real.sqrt ((q : ℝ) - 1) ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt (by linarith)
  linarith

/-- For a prime conductor `q > c`, every integer lag `1 ≤ h < c` is coprime to `q`, so
`|ramanujanLagCoefficient q h| = 1` and `|shellCorrection φ c q| ≤ 2 c² / (q - 1)`. -/
private theorem abs_shellCorrection_prime_of_gt {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc1 : 1 ≤ c) {q : ℕ} (hq : q.Prime) (hcq : c < q) :
    |shellCorrection φ c q| ≤ 2 * c ^ 2 / ((q : ℝ) - 1) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hqt : (q.totient : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.totient_prime hq, Nat.cast_sub hq.one_lt.le, Nat.cast_one]
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    linarith
  have hcard : ((Ico 1 ⌈c⌉₊).card : ℝ) ≤ c := by
    rw [Nat.card_Ico, Nat.cast_sub (Nat.one_le_ceil_iff.mpr hc0), Nat.cast_one]
    linarith only [Nat.ceil_lt_add_one hc0.le]
  have hsum : |∑ h ∈ Ico 1 ⌈c⌉₊, ramanujanLagCoefficient q h *
      ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤
      (∫ u, φ u ^ 2) * c ^ 2 := by
    calc _ ≤ ∑ h ∈ Ico 1 ⌈c⌉₊, |ramanujanLagCoefficient q h *
              ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ Ico 1 ⌈c⌉₊, 1 * ((∫ u, φ u ^ 2) * c) := by
          refine sum_le_sum fun h hh => ?_
          have hh0 : 0 < h := (mem_Ico.mp hh).1
          have hhc : (h : ℝ) < c := Nat.lt_ceil.mp (mem_Ico.mp hh).2
          have hndvd : ¬(q ∣ h) := by
            intro hdvd
            have hle : (q : ℝ) ≤ h := by exact_mod_cast Nat.le_of_dvd hh0 hdvd
            linarith
          have hlag : |ramanujanLagCoefficient q h| ≤ 1 := by
            rw [ramanujanLagCoefficient_of_prime hq h, if_neg hndvd]
            norm_num
          have hint : |∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤ (∫ u, φ u ^ 2) * c := by
            have hr0 : 0 < (h : ℝ) / c := div_pos (by exact_mod_cast hh0) hc0
            have hr1 : (h : ℝ) / c ≤ 1 := (div_le_one hc0).mpr hhc.le
            have hh1R : (1 : ℝ) ≤ h := by exact_mod_cast hh0
            have hbd : ∀ u ∈ Set.Ioc ((h : ℝ) / c) 1, ‖shellAutocorr φ u / u‖ ≤ (∫ t, φ t ^ 2) * c := by
              intro u hu
              have hu0 : 0 < u := hr0.trans_le hu.1.le
              rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0]
              calc |shellAutocorr φ u| / u ≤ (∫ t, φ t ^ 2) / ((h : ℝ) / c) :=
                    div_le_div₀ hM.le (abs_shellAutocorr_le hφ hsupp u) hr0 hu.1.le
                _ = (∫ t, φ t ^ 2) * c / h := by rw [div_div_eq_mul_div]
                _ ≤ (∫ t, φ t ^ 2) * c / 1 := div_le_div_of_nonneg_left (by positivity) zero_lt_one hh1R
                _ = (∫ t, φ t ^ 2) * c := div_one _
            have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (C := (∫ t, φ t ^ 2) * c)
              fun u hu => hbd u (by rwa [Set.uIoc_of_le hr1] at hu)
            rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr1)] at hnorm
            calc |∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u|
                ≤ (∫ t, φ t ^ 2) * c * (1 - (h : ℝ) / c) := hnorm
              _ ≤ (∫ t, φ t ^ 2) * c * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              _ = (∫ t, φ t ^ 2) * c := mul_one _
          rw [abs_mul]
          exact mul_le_mul hlag hint (abs_nonneg _) zero_le_one
      _ = ((Ico 1 ⌈c⌉₊).card : ℝ) * ((∫ u, φ u ^ 2) * c) := by
          rw [sum_const, nsmul_eq_mul, one_mul]
      _ ≤ c * ((∫ u, φ u ^ 2) * c) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  rw [shellCorrection, hqt, abs_mul, abs_div, abs_mul, abs_of_pos hM, abs_of_pos hq1, abs_two]
  calc _ ≤ 2 / ((∫ u, φ u ^ 2) * ((q : ℝ) - 1)) * ((∫ u, φ u ^ 2) * c ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp [hM.ne', hq1.ne']

/-- Global polynomial-in-overlap norm bound for `completeWeilMatrix tiltedUnitSpline c N` on
`EuclideanSpace ℝ (PrimeHorizonIndex N)` for `1 ≤ c ≤ log N`. -/
private theorem exists_completeWeilMatrix_global_norm_cost :
    ∃ C_all : ℝ, 0 < C_all ∧ ∀ᶠ N : ℕ in atTop, ∀ {c : ℝ},
      1 ≤ c → c ≤ Real.log (N : ℝ) →
      (∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        |completeWeilEnergy tiltedUnitSpline c N x| ≤
          C_all * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ ^ 2) ∧
      (∀ x y : EuclideanSpace ℝ (PrimeHorizonIndex N),
        |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x, y⟫| ≤
          C_all * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ * ‖y‖) := by
  have hφ_nonneg : ∀ u, 0 ≤ tiltedUnitSpline u := fun _ =>
    RenormalizedIntersectionTheory.tiltedUnitSpline_nonneg _
  obtain ⟨C_neut, hC_neut, hneut⟩ := exists_complete_packet_neutral_norm_cost
    contDiff_tiltedUnitSpline hφ_nonneg tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_E1, hC_E1, hE1⟩ := exists_completedConductorEnergy_polynomial_bound
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos one_pos
  obtain ⟨K_res, hK_res, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  have hres1 := hres 0 le_rfl 2 (by norm_num)
  let C_v : ℝ := 2 * C_E1 + 4 * Real.sqrt K_res + 1
  let C_q : ℝ := 4 * C_neut + 16 * C_v + 1
  have hCv : 0 < C_v := by positivity
  have hCq : 0 < C_q := by positivity
  refine ⟨C_q, hCq, ?_⟩
  have hL_tend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL_sq_div : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 / (N : ℝ)) atTop (𝓝 0) :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).congr fun N => by dsimp only [Function.comp_def]; ring
  have hL6_div : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 6 / (N : ℝ)) atTop (𝓝 0) :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).congr fun N => by dsimp only [Function.comp_def]; ring
  filter_upwards [hres1, eventually_ge_atTop 4, hL_tend.eventually_ge_atTop 36,
    hL_sq_div.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (4 * (Real.exp 1 + 3) ^ 2))),
    hL6_div.eventually (gt_mem_nhds zero_lt_one)]
    with N hresN hN4 hL36 hL2N hL6N
  intro c hc1 hcL
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := by linarith
  have hwidth : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    have hc2 : c ^ 2 ≤ Real.log (N : ℝ) ^ 2 := pow_le_pow_left₀ hc0.le hcL 2
    have hlt := (div_lt_iff₀ hNR).mp hL2N
    have hpos : 0 < 4 * (Real.exp 1 + 3) ^ 2 := by positivity
    have h1 : 4 * (Real.exp 1 + 3) ^ 2 * Real.log (N : ℝ) ^ 2 ≤ (N : ℝ) := by
      have := (lt_div_iff₀ hpos).mp (by
        calc Real.log (N : ℝ) ^ 2 < 1 / (4 * (Real.exp 1 + 3) ^ 2) * (N : ℝ) := hlt
          _ = (N : ℝ) / (4 * (Real.exp 1 + 3) ^ 2) := by ring)
      linarith
    exact (mul_le_mul_of_nonneg_left hc2 hpos.le).trans h1
  have hcN_third : c / (N : ℝ) ≤ 1 / 3 := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have h16 : (64 : ℝ) ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [he1]
    have hw1 : 64 * c ^ 2 ≤ (N : ℝ) :=
      (mul_le_mul_of_nonneg_right h16 (sq_nonneg c)).trans hwidth
    have hc_le : 3 * c ≤ (N : ℝ) := by nlinarith only [hw1, hc1]
    exact (div_le_div_iff₀ hNR (by norm_num)).mpr (by linarith)
  have hlog2_18 : 18 * (1 + Real.log (2 : ℕ)) ≤ Real.log (N : ℝ) := by
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    push_cast; linarith
  let v1 := normalizedRamanujanHorizonVector 1 N
  have hv1_riesz := half_and_three_halves_riesz_of_log_le (Q := 2) (N := N)
    (by omega) (by omega) hlog2_18 (fun m => if m = 1 then 1 else 0)
  have hv1_sum : (∑ m ∈ Icc 1 2, (if m = 1 then (1 : ℝ) else 0) •
      normalizedRamanujanHorizonVector m N) = v1 := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 2), Icc_self, sum_singleton]
    simp [v1]
  have hv1_csum : (∑ m ∈ Icc 1 2, (if m = 1 then (1 : ℝ) else 0) ^ 2) = 1 := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 2), Icc_self, sum_singleton]
    norm_num
  rw [hv1_sum, hv1_csum] at hv1_riesz
  have hv1_norm_le : ‖v1‖ ≤ 2 := by
    have : ‖v1‖ ^ 2 ≤ 2 ^ 2 := by linarith only [hv1_riesz.2]
    nlinarith only [this, norm_nonneg v1]
  have hv1_norm_ge : (1 / 2 : ℝ) ≤ ‖v1‖ ^ 2 := by linarith only [hv1_riesz.1]
  have hr1_sq := hresN 1 one_pos (by rw [Nat.cast_one, Real.rpow_zero]) c hc1 hwidth
  have hBv1_norm : ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1‖ ≤
      C_v * c ^ 3 := by
    have hlogc_le : 1 + Real.log c ≤ 2 * c := by
      have := Real.log_le_sub_one_of_pos hc0
      linarith
    have hrate1 : c ^ 2 * (1 + Real.log c) ^ 3 * Real.log (N : ℝ) ^ (1 / (2 : ℝ)) / Real.log (N : ℝ) ≤
        8 * c ^ 5 := by
      have h1 : (1 + Real.log c) ^ 3 ≤ 8 * c ^ 3 := by
        have := pow_le_pow_left₀ (by linarith [Real.log_nonneg hc1]) hlogc_le 3
        linarith
      have h2 : Real.log (N : ℝ) ^ (1 / (2 : ℝ)) / Real.log (N : ℝ) ≤ 1 := by
        rw [div_le_one hL0]
        calc Real.log (N : ℝ) ^ (1 / (2 : ℝ)) ≤ Real.log (N : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          _ = Real.log (N : ℝ) := Real.rpow_one _
      calc c ^ 2 * (1 + Real.log c) ^ 3 * Real.log (N : ℝ) ^ (1 / (2 : ℝ)) / Real.log (N : ℝ)
          = c ^ 2 * (1 + Real.log c) ^ 3 * (Real.log (N : ℝ) ^ (1 / (2 : ℝ)) / Real.log (N : ℝ)) := by ring
        _ ≤ c ^ 2 * (8 * c ^ 3) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (sq_nonneg c)) h2 (by positivity) (by positivity)
        _ = 8 * c ^ 5 := by ring
    have hrate2 : c ^ 10 * (Real.log (N : ℝ) / (N : ℝ)) ^ 2 ≤ c ^ 5 := by
      have hc10 : c ^ 10 ≤ Real.log (N : ℝ) ^ 10 := pow_le_pow_left₀ hc0.le hcL 10
      have hLN6 : Real.log (N : ℝ) ^ 6 ≤ (N : ℝ) := by
        have := (div_lt_iff₀ hNR).mp hL6N
        linarith
      have hprod : Real.log (N : ℝ) ^ 12 ≤ (N : ℝ) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hLN6 2
        linarith
      have hle1 : c ^ 10 * (Real.log (N : ℝ) / (N : ℝ)) ^ 2 ≤ 1 := by
        calc c ^ 10 * (Real.log (N : ℝ) / (N : ℝ)) ^ 2
            ≤ Real.log (N : ℝ) ^ 10 * (Real.log (N : ℝ) / (N : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_right hc10 (sq_nonneg _)
          _ = Real.log (N : ℝ) ^ 12 / (N : ℝ) ^ 2 := by ring
          _ ≤ 1 := (div_le_one (sq_pos_of_pos hNR)).mpr hprod
      exact hle1.trans (one_le_pow₀ hc1)
    have hc5_le_c6 : c ^ 5 ≤ c ^ 6 := pow_le_pow_right₀ hc1 (by omega)
    have hrsq : ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1 -
        completedConductorEnergy tiltedUnitSpline c 1 • v1‖ ^ 2 ≤ 16 * K_res * c ^ 6 := by
      rw [Nat.cast_one, Real.log_one, add_zero, one_pow, mul_one, mul_one] at hr1_sq
      nlinarith only [hr1_sq, hrate1, hrate2, hc5_le_c6, hK_res]
    have hr_norm : ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1 -
        completedConductorEnergy tiltedUnitSpline c 1 • v1‖ ≤ 4 * Real.sqrt K_res * c ^ 3 := by
      have h0 : 0 ≤ 4 * Real.sqrt K_res * c ^ 3 := by positivity
      have hsq_rhs : (4 * Real.sqrt K_res * c ^ 3) ^ 2 = 16 * K_res * c ^ 6 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hK_res.le]; ring
      nlinarith only [hrsq, hsq_rhs, h0,
        norm_nonneg (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1 -
          completedConductorEnergy tiltedUnitSpline c 1 • v1)]
    have hE1_norm : ‖completedConductorEnergy tiltedUnitSpline c 1 • v1‖ ≤ 2 * C_E1 * c ^ 3 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hc23 : c ^ 2 ≤ c ^ 3 := pow_le_pow_right₀ hc1 (by omega)
      have hb := (hE1 c hc1).trans (mul_le_mul_of_nonneg_left hc23 hC_E1.le)
      calc |completedConductorEnergy tiltedUnitSpline c 1| * ‖v1‖
          ≤ (C_E1 * c ^ 3) * 2 := mul_le_mul hb hv1_norm_le (norm_nonneg _) (by positivity)
        _ = 2 * C_E1 * c ^ 3 := by ring
    have htri : ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1‖ ≤
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1 -
          completedConductorEnergy tiltedUnitSpline c 1 • v1‖ +
        ‖completedConductorEnergy tiltedUnitSpline c 1 • v1‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1 -
          completedConductorEnergy tiltedUnitSpline c 1 • v1)
        (completedConductorEnergy tiltedUnitSpline c 1 • v1)
    have hc3_pos : 0 < c ^ 3 := pow_pos hc0 3
    dsimp only [C_v]
    nlinarith only [htri, hr_norm, hE1_norm, hc3_pos]
  have hneut_vec : ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
      z ∈ (conductorSubspace 1 N)ᗮ →
      |completeWeilEnergy tiltedUnitSpline c N z| ≤
        C_neut * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖z‖ ^ 2 := by
    intro z hz
    let F : ℕ → ℝ := fun n => Real.sqrt (n : ℝ) * primeHorizonExtension z n
    have hpack : packetVector F N = z := by
      ext ⟨n, hn⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      change F n / Real.sqrt (n : ℝ) = z ⟨n, hn⟩
      dsimp only [F]
      rw [primeHorizonExtension_coe z ⟨n, hn⟩, mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hn0).ne']
    have hzero : ∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0 := by
      have hp := poleFunctional_eq_zero_of_mem_conductorSubspace_one_orthogonal hN2 hz
      unfold ArithmeticLorentzianGeometry.poleFunctional at hp
      rw [← hp]
      refine sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      dsimp only [F]
      rw [div_eq_iff hn0.ne']
      calc Real.sqrt n * primeHorizonExtension z n
          = primeHorizonExtension z n / Real.sqrt n * (Real.sqrt n * Real.sqrt n) := by
              field_simp [(Real.sqrt_pos.mpr hn0).ne']
        _ = primeHorizonExtension z n / Real.sqrt n * n := by rw [Real.mul_self_sqrt hn0.le]
    have hb := hneut N c hN1 hc1 hcN_third F hzero
    rwa [hpack] at hb
  have hquad_half : ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      |completeWeilEnergy tiltedUnitSpline c N x| ≤
        (C_q / 2) * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ ^ 2 := by
    intro x
    let u1 := (conductorSubspace 1 N).starProjection x
    let x0 := x - u1
    have hx0_mem : x0 ∈ (conductorSubspace 1 N)ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal x
    have hpyth := norm_starProjection_sq_add_sub_sq (conductorSubspace 1 N) x
    change ‖u1‖ ^ 2 + ‖x0‖ ^ 2 = ‖x‖ ^ 2 at hpyth
    have hu1_le : ‖u1‖ ≤ ‖x‖ := by nlinarith only [hpyth, sq_nonneg ‖x0‖, norm_nonneg u1, norm_nonneg x]
    have hx0_le : ‖x0‖ ≤ ‖x‖ := by nlinarith only [hpyth, sq_nonneg ‖u1‖, norm_nonneg x0, norm_nonneg x]
    obtain ⟨b, -, hu1_eq⟩ := (mem_conductorSubspace_iff (M := 1) (N := N) (x := u1)).mp
      ((conductorSubspace 1 N).starProjection_apply_mem x)
    rw [Icc_self, sum_singleton] at hu1_eq
    have hb_sq : (b 1) ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
      have : ‖u1‖ ^ 2 = (b 1) ^ 2 * ‖v1‖ ^ 2 := by
        rw [hu1_eq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      nlinarith only [this, hv1_norm_ge, hpyth, sq_nonneg ‖x0‖, sq_nonneg (b 1)]
    have hb_abs : |b 1| ≤ 2 * ‖x‖ := by nlinarith only [hb_sq, sq_abs (b 1), abs_nonneg (b 1), norm_nonneg x]
    have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
    have hsplit : completeWeilEnergy tiltedUnitSpline c N x =
        completeWeilEnergy tiltedUnitSpline c N x0 +
          2 * (b 1) * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1, x0⟫ +
          (b 1) ^ 2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1, v1⟫ := by
      have hx_eq : x = x0 + b 1 • v1 := by
        dsimp only [x0, u1, v1] at hu1_eq ⊢
        rw [← hu1_eq]
        abel
      nth_rw 1 [hx_eq]
      unfold completeWeilEnergy
      rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
        hsym x0 v1, real_inner_comm x0]
      simp only [conj_trivial]
      ring
    have h1 : |completeWeilEnergy tiltedUnitSpline c N x0| ≤
        C_neut * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ ^ 2 :=
      (hneut_vec x0 hx0_mem).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hx0_le 2) (by positivity))
    have h2 : |2 * (b 1) * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1, x0⟫| ≤
        4 * C_v * c ^ 3 * ‖x‖ ^ 2 := by
      rw [abs_mul, abs_mul, abs_two]
      calc 2 * |b 1| * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1, x0⟫|
          ≤ 2 * (2 * ‖x‖) * (‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1‖ * ‖x0‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hb_abs zero_le_two)
              (abs_real_inner_le_norm _ _) (abs_nonneg _) (by positivity)
        _ ≤ 4 * ‖x‖ * ((C_v * c ^ 3) * ‖x‖) := by
            have := mul_le_mul hBv1_norm hx0_le (norm_nonneg _) (by positivity)
            nlinarith only [this, norm_nonneg x]
        _ = 4 * C_v * c ^ 3 * ‖x‖ ^ 2 := by ring
    have h3 : |(b 1) ^ 2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1, v1⟫| ≤
        4 * C_v * c ^ 3 * ‖x‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      have hvv : |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1, v1⟫| ≤
          2 * C_v * c ^ 3 :=
        (abs_real_inner_le_norm _ _).trans (by
          have := mul_le_mul hBv1_norm hv1_norm_le (norm_nonneg _) (by positivity)
          linarith)
      calc (b 1) ^ 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1, v1⟫|
          ≤ (2 * ‖x‖ ^ 2) * (2 * C_v * c ^ 3) := mul_le_mul hb_sq hvv (abs_nonneg _) (by positivity)
        _ = 4 * C_v * c ^ 3 * ‖x‖ ^ 2 := by ring
    have hc3_L : c ^ 3 ≤ c ^ 3 * (Real.log (N : ℝ) + 1) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have htri : |completeWeilEnergy tiltedUnitSpline c N x| ≤
        |completeWeilEnergy tiltedUnitSpline c N x0| +
        |2 * (b 1) * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1, x0⟫| +
        |(b 1) ^ 2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1, v1⟫| := by
      rw [hsplit]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hsum_le : C_neut * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ ^ 2 +
        8 * C_v * c ^ 3 * ‖x‖ ^ 2 ≤ (C_q / 2) * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ ^ 2 := by
      have h8 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc3_L (by positivity : 0 ≤ 8 * C_v)) (sq_nonneg ‖x‖)
      have hprod : 0 ≤ c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ ^ 2 := by positivity
      dsimp only [C_q]
      nlinarith only [h8, hprod, hC_neut, hCv]
    linarith only [htri, h1, h2, h3, hsum_le]
  refine ⟨fun x => (hquad_half x).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      (by positivity)) (sq_nonneg _)), fun x y => ?_⟩
  by_cases hxy0 : ‖x‖ = 0 ∨ ‖y‖ = 0
  · rcases hxy0 with hx0 | hy0
    · rw [norm_eq_zero.mp hx0, map_zero, inner_zero_left, abs_zero, norm_zero, mul_zero, zero_mul]
    · rw [norm_eq_zero.mp hy0, inner_zero_right, abs_zero, norm_zero, mul_zero]
  rw [not_or] at hxy0
  have hx_pos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hxy0.1)
  have hy_pos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hxy0.2)
  let x' := ‖x‖⁻¹ • x
  let y' := ‖y‖⁻¹ • y
  have hx'1 : ‖x'‖ = 1 := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hx_pos, inv_mul_cancel₀ hx_pos.ne']
  have hy'1 : ‖y'‖ = 1 := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hy_pos, inv_mul_cancel₀ hy_pos.ne']
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
  have hpol : 4 * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x', y'⟫ =
      completeWeilEnergy tiltedUnitSpline c N (x' + y') -
        completeWeilEnergy tiltedUnitSpline c N (x' - y') := by
    unfold completeWeilEnergy
    rw [map_add, map_sub, inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right, hsym y' x', real_inner_comm y']
    ring
  have hadd_sq : ‖x' + y'‖ ^ 2 + ‖x' - y'‖ ^ 2 = 4 := by
    have h1 := norm_add_sq_real x' y'
    have h2 := norm_sub_sq_real x' y'
    rw [hx'1, hy'1] at h1 h2
    linarith
  have hb_unit : |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x', y'⟫| ≤
      C_q * c ^ 3 * (Real.log (N : ℝ) + 1) := by
    have hp := hquad_half (x' + y')
    have hm := hquad_half (x' - y')
    have h4 : 4 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x', y'⟫| ≤
        |completeWeilEnergy tiltedUnitSpline c N (x' + y')| +
          |completeWeilEnergy tiltedUnitSpline c N (x' - y')| := by
      have := abs_sub (completeWeilEnergy tiltedUnitSpline c N (x' + y'))
        (completeWeilEnergy tiltedUnitSpline c N (x' - y'))
      rw [← hpol, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at this
      exact this
    have hrhs : (C_q / 2) * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x' + y'‖ ^ 2 +
        (C_q / 2) * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x' - y'‖ ^ 2 =
        2 * C_q * c ^ 3 * (Real.log (N : ℝ) + 1) := by
      calc _ = (C_q / 2) * c ^ 3 * (Real.log (N : ℝ) + 1) * (‖x' + y'‖ ^ 2 + ‖x' - y'‖ ^ 2) := by ring
        _ = _ := by rw [hadd_sq]; ring
    have hpos_K : 0 ≤ C_q * c ^ 3 * (Real.log (N : ℝ) + 1) := by positivity
    linarith only [h4, hp, hm, hrhs, hpos_K]
  have hid : ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x, y⟫ =
      ‖x‖ * ‖y‖ * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x', y'⟫ := by
    dsimp only [x', y']
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    field_simp [hx_pos.ne', hy_pos.ne']
  rw [hid, abs_mul, abs_mul, abs_of_pos hx_pos, abs_of_pos hy_pos]
  calc ‖x‖ * ‖y‖ * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x', y'⟫|
      ≤ ‖x‖ * ‖y‖ * (C_q * c ^ 3 * (Real.log (N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hb_unit (by positivity)
    _ = C_q * c ^ 3 * (Real.log (N : ℝ) + 1) * ‖x‖ * ‖y‖ := by ring

/-- Asymptotic `13 / 32` law for `log (primeAboveLowPacket N) / log (log N)`. -/
private theorem tendsto_log_primeAboveLowPacket_div_log_log :
    Tendsto (fun N : ℕ =>
      Real.log (primeAboveLowPacket N : ℝ) / Real.log (Real.log (N : ℝ))) atTop (𝓝 (13 / 32 : ℝ)) := by
  have hL_tend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL_tend : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL_tend
  have hinv : Tendsto (fun N : ℕ => Real.log 4 / Real.log (Real.log (N : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hLL_tend
  have hlo : Tendsto (fun N : ℕ => (13 / 32 : ℝ) - Real.log 4 / Real.log (Real.log (N : ℝ)))
      atTop (𝓝 (13 / 32 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (13 / 32 : ℝ))).sub hinv
  have hhi : Tendsto (fun N : ℕ => (13 / 32 : ℝ) + Real.log 4 / Real.log (Real.log (N : ℝ)))
      atTop (𝓝 (13 / 32 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (13 / 32 : ℝ))).add hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp hL_tend
      |>.eventually_ge_atTop 4, hLL_tend.eventually_gt_atTop 0, hL_tend.eventually_gt_atTop 1]
      with N hQ4 hLL0 hL1
    obtain ⟨hq_pr, hq_gt, _⟩ := primeAboveLowPacket_spec N
    have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans hL1
    have hQ_ge : Real.log (N : ℝ) ^ (13 / 32 : ℝ) / 2 ≤ (primeAboveLowPacket N : ℝ) := by
      have h1 : Real.log (N : ℝ) ^ (13 / 32 : ℝ) - 1 < (lowPacketCutoff N : ℝ) :=
        sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
      have h2 : (lowPacketCutoff N : ℝ) < primeAboveLowPacket N := by
        exact_mod_cast (le_max_right 2 _).trans_lt hq_gt
      change 4 ≤ Real.log (N : ℝ) ^ (13 / 32 : ℝ) at hQ4
      linarith
    have hlog_ge : (13 / 32 : ℝ) * Real.log (Real.log (N : ℝ)) - Real.log 2 ≤
        Real.log (primeAboveLowPacket N : ℝ) := by
      have h := Real.log_le_log (by positivity) hQ_ge
      rw [Real.log_div (by positivity) two_ne_zero, Real.log_rpow hL0] at h
      exact h
    have hlog24 : Real.log 2 ≤ Real.log 4 := Real.log_le_log zero_lt_two (by norm_num)
    have : (13 / 32 : ℝ) * Real.log (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) = 13 / 32 :=
      mul_div_cancel_right₀ _ hLL0.ne'
    rw [← this, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) hLL0.le
  · filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp hL_tend
      |>.eventually_ge_atTop 2, hLL_tend.eventually_gt_atTop 0, hL_tend.eventually_gt_atTop 1]
      with N hQ2 hLL0 hL1
    obtain ⟨hq_pr, _, hq_le⟩ := primeAboveLowPacket_spec N
    have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans hL1
    have hQ_le : (primeAboveLowPacket N : ℝ) ≤ 4 * Real.log (N : ℝ) ^ (13 / 32 : ℝ) := by
      have h1 : (lowPacketCutoff N : ℝ) ≤ Real.log (N : ℝ) ^ (13 / 32 : ℝ) :=
        Nat.floor_le (by positivity)
      have h2 : (max 2 (lowPacketCutoff N) : ℝ) ≤ Real.log (N : ℝ) ^ (13 / 32 : ℝ) := by
        rw [Nat.cast_max, Nat.cast_ofNat]
        exact max_le hQ2 h1
      have h3 : (primeAboveLowPacket N : ℝ) ≤ 2 * (max 2 (lowPacketCutoff N) : ℝ) := by
        exact_mod_cast hq_le
      change 2 ≤ Real.log (N : ℝ) ^ (13 / 32 : ℝ) at hQ2
      linarith
    have hlog_le : Real.log (primeAboveLowPacket N : ℝ) ≤
        (13 / 32 : ℝ) * Real.log (Real.log (N : ℝ)) + Real.log 4 := by
      have h := Real.log_le_log (by exact_mod_cast hq_pr.pos) hQ_le
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hL0] at h
      linarith
    have : (13 / 32 : ℝ) * Real.log (Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ)) = 13 / 32 :=
      mul_div_cancel_right₀ _ hLL0.ne'
    rw [← this, ← add_div]
    exact div_le_div_of_nonneg_right hlog_le hLL0.le

/-- Quantitative norm closeness `|‖normalizedRamanujanHorizonVector m X‖² - 1| ≤ (2 log m + 9) / log X`
whenever `2 ≤ m` and `m * m ≤ X`. -/
private theorem abs_norm_normalizedRamanujanHorizonVector_sq_sub_one_le {m X : ℕ}
    (hm2 : 2 ≤ m) (hmX : m * m ≤ X) :
    |‖normalizedRamanujanHorizonVector m X‖ ^ 2 - 1| ≤
      (2 * Real.log (m : ℝ) + 9) / Real.log (X : ℝ) := by
  let a : ℕ → ℝ := fun k => if k = m then 1 else 0
  have hsum_v : (∑ k ∈ Icc 1 m, a k • normalizedRamanujanHorizonVector k X) =
      normalizedRamanujanHorizonVector m X := by
    rw [sum_eq_single m]
    · simp [a]
    · intro k _ hkm; simp [a, hkm]
    · intro hm_not; exact absurd (mem_Icc.mpr ⟨by omega, le_rfl⟩) hm_not
  have hsum_c : (∑ k ∈ Icc 1 m, a k ^ 2) = 1 := by
    rw [sum_eq_single m]
    · simp [a]
    · intro k _ hkm; simp [a, hkm]
    · intro hm_not; exact absurd (mem_Icc.mpr ⟨by omega, le_rfl⟩) hm_not
  have hb := abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le_two_log hm2 hmX a
  rw [hsum_v, hsum_c, mul_one] at hb
  exact hb

/-- Uniform vector-norm comparison between separated overlap `c' ∈ (0, 1/2]` and unit overlap `1`
on a prime Ramanujan mode `v_q` (`q` prime, `2 ≤ q`, `q^4 ≤ M`). -/
private theorem center_action_prime_mode_le {M q : ℕ} {α : ℝ}
    (hLM0 : 0 < Real.log (M : ℝ)) (hq : q.Prime) (hqL : (q : ℝ) ≤ Real.log (M : ℝ))
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α M)
      (normalizedRamanujanHorizonVector q M)‖ ≤ 36 := by
  have hq_pos : 0 < q := hq.pos
  have hqR_pos : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hq1_ne : q ≠ 1 := hq.one_lt.ne'
  let A_q : ℝ := ∑ j ∈ range q, |normalizedRamanujanMode q j|
  have hA_q0 : 0 ≤ A_q := sum_nonneg fun _ _ => abs_nonneg _
  have hA_q_le : A_q ≤ 2 * Real.sqrt (q : ℝ) := sum_abs_normalizedRamanujanMode_prime_le hq
  have hA_div_LM : A_q ^ 2 / Real.log (M : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hLM0]
    have hsq : A_q ^ 2 ≤ 4 * (q : ℝ) := by
      have h1 := pow_le_pow_left₀ hA_q0 hA_q_le 2
      rw [mul_pow, Real.sq_sqrt hqR_pos.le] at h1
      linarith only [h1]
    linarith only [hsq, hqL]
  have hper : ∑ j ∈ range q, normalizedRamanujanMode q j = 0 := by
    have hm1 : normalizedRamanujanMode 1 = fun _ => 1 := funext fun _ => by
      simp only [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one,
        Nat.cast_one, Real.sqrt_one, div_one]
    have h := periodMean_normalizedRamanujanMode_mul hq_pos zero_lt_one dvd_rfl (one_dvd q) hq_pos
    simp only [hm1, mul_one, if_neg hq1_ne, periodMean] at h
    exact (div_eq_zero_iff.mp h).resolve_right hqR_pos.ne'
  have hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, normalizedRamanujanMode q j| ≤ 2 * A_q :=
    abs_sum_Ico_le_of_periodic hq_pos (normalizedRamanujanMode_periodic hq_pos) hper
  have hunnorm : ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α M)
      (ramanujanHorizonVector q M)‖ ^ 2 ≤ α ^ 2 * (9 * A_q) ^ 2 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => (α / M) *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n - archimedeanCenterKernel n j)) M)
      (horizonProfileVector (ramanujanPoleProfile q) M)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hb := sum_sq_centerCorrection_poleProfile_le hA_q0
      (abs_normalizedRamanujanMode_le hq_pos) hB α M
    refine (le_of_eq ?_).trans (hb.trans (by ring_nf; exact le_rfl))
    simp only [ramanujanPoleProfile, mul_assoc, ← mul_sum]
  have hnorm_sq : ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α M)
      (normalizedRamanujanHorizonVector q M)‖ ^ 2 ≤ 36 ^ 2 := by
    rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, inv_pow, Real.sq_sqrt hLM0.le]
    have hα_sq : α ^ 2 ≤ 1 := by nlinarith only [hα0, hα1]
    have h1 : (Real.log (M : ℝ))⁻¹ * (α ^ 2 * (9 * A_q) ^ 2) ≤ 36 ^ 2 := by
      calc (Real.log (M : ℝ))⁻¹ * (α ^ 2 * (9 * A_q) ^ 2)
          ≤ (Real.log (M : ℝ))⁻¹ * (1 * (81 * A_q ^ 2)) :=
            mul_le_mul_of_nonneg_left (by nlinarith only [hα_sq, sq_nonneg A_q])
              (inv_nonneg.mpr hLM0.le)
        _ = 81 * (A_q ^ 2 / Real.log (M : ℝ)) := by rw [div_eq_mul_inv]; ring
        _ ≤ 81 * 4 := mul_le_mul_of_nonneg_left hA_div_LM (by norm_num)
        _ = 36 ^ 2 := by norm_num
    exact (mul_le_mul_of_nonneg_left hunnorm (inv_nonneg.mpr hLM0.le)).trans h1
  have hnn := norm_nonneg (Matrix.toEuclideanLin (fullWeilCenterMatrix α M)
    (normalizedRamanujanHorizonVector q M))
  nlinarith only [hnorm_sq, hnn]

private theorem cross_action_prime_mode_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM_int : 0 < ∫ u, φ u ^ 2)
    {M q : ℕ} {c' : ℝ} (hM1 : 1 ≤ M) (hLM0 : 0 < Real.log (M : ℝ))
    (hq : q.Prime) (hqL : (q : ℝ) ≤ Real.log (M : ℝ))
    (hc'0 : 0 < c') (hc'hi : c' ≤ 1 / 2) :
    ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M)
      (normalizedRamanujanHorizonVector q M)‖ ≤ 18 * atomCrossErrorConstant φ (1 / 2) := by
  have hc'1 : c' < 1 := by linarith
  have hq_pos : 0 < q := hq.pos
  have hqR_pos : (0 : ℝ) < q := by exact_mod_cast hq_pos
  let A_q : ℝ := ∑ j ∈ range q, |normalizedRamanujanMode q j|
  have hA_q0 : 0 ≤ A_q := sum_nonneg fun _ _ => abs_nonneg _
  have hA_q_le : A_q ≤ 2 * Real.sqrt (q : ℝ) := sum_abs_normalizedRamanujanMode_prime_le hq
  have hA_div_LM : A_q ^ 2 / Real.log (M : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hLM0]
    have hsq : A_q ^ 2 ≤ 4 * (q : ℝ) := by
      have h1 := pow_le_pow_left₀ hA_q0 hA_q_le 2
      rw [mul_pow, Real.sq_sqrt hqR_pos.le] at h1
      linarith only [h1]
    linarith only [hsq, hqL]
  have hunnorm : ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M)
      (ramanujanHorizonVector q M)‖ ^ 2 ≤
      (36 * atomCrossErrorConstant φ c' * A_q * c' ^ 2) ^ 2 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (atomCrossErrorKernel (atomDilate φ (c' / M))) M)
      (horizonProfileVector (ramanujanPoleProfile q) M)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    exact sum_sq_atomCrossError_at_spacing_le hφ hsupp hM_int hc'0 hc'1 hM1 hA_q0
      (fun j _ => abs_normalizedRamanujanMode_le hq_pos j)
  have hconst_le : atomCrossErrorConstant φ c' * c' ^ 2 ≤
      atomCrossErrorConstant φ (1 / 2) * (1 / 4 : ℝ) := by
    unfold atomCrossErrorConstant
    have h2 : c' ^ 2 ≤ 1 / 4 := by nlinarith only [hc'0, hc'hi]
    have hdiv : 1 / ((∫ u, φ u ^ 2) * (1 - c') ^ 2) ≤
        1 / ((∫ u, φ u ^ 2) * (1 - (1 / 2 : ℝ)) ^ 2) :=
      one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (by nlinarith only [hc'0, hc'hi]) hM_int.le)
    have hnum0 : 0 ≤ 38 * (∫ u, |φ u|) ^ 2 := by positivity
    calc 38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - c') ^ 2) * c' ^ 2
        = 38 * (∫ u, |φ u|) ^ 2 * (1 / ((∫ u, φ u ^ 2) * (1 - c') ^ 2)) * c' ^ 2 := by ring
      _ ≤ 38 * (∫ u, |φ u|) ^ 2 * (1 / ((∫ u, φ u ^ 2) * (1 - (1 / 2 : ℝ)) ^ 2)) * (1 / 4) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdiv hnum0) h2 (sq_nonneg _) (by positivity)
      _ = 38 * (∫ u, |φ u|) ^ 2 / ((∫ u, φ u ^ 2) * (1 - (1 / 2 : ℝ)) ^ 2) * (1 / 4) := by ring
  have hsq : ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M)
      (normalizedRamanujanHorizonVector q M)‖ ^ 2 ≤
      (18 * atomCrossErrorConstant φ (1 / 2)) ^ 2 := by
    rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, inv_pow, Real.sq_sqrt hLM0.le]
    have hsub : 36 * atomCrossErrorConstant φ c' * A_q * c' ^ 2 ≤
        9 * atomCrossErrorConstant φ (1 / 2) * A_q := by
      have h1 := mul_le_mul_of_nonneg_right hconst_le hA_q0
      linarith only [h1]
    have hpow := pow_le_pow_left₀ (by have := atomCrossErrorConstant_nonneg φ c'; positivity) hsub 2
    calc (Real.log (M : ℝ))⁻¹ *
          ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M) (ramanujanHorizonVector q M)‖ ^ 2
        ≤ (Real.log (M : ℝ))⁻¹ * (9 * atomCrossErrorConstant φ (1 / 2) * A_q) ^ 2 :=
          mul_le_mul_of_nonneg_left (hunnorm.trans hpow) (inv_nonneg.mpr hLM0.le)
      _ = 81 * atomCrossErrorConstant φ (1 / 2) ^ 2 * (A_q ^ 2 / Real.log (M : ℝ)) := by ring
      _ ≤ 81 * atomCrossErrorConstant φ (1 / 2) ^ 2 * 4 :=
          mul_le_mul_of_nonneg_left hA_div_LM (by positivity)
      _ = (18 * atomCrossErrorConstant φ (1 / 2)) ^ 2 := by ring
  have hc_nn : 0 ≤ 18 * atomCrossErrorConstant φ (1 / 2) := by
    have := atomCrossErrorConstant_nonneg φ (1 / 2); positivity
  have hnn := norm_nonneg (Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M)
    (normalizedRamanujanHorizonVector q M))
  nlinarith only [hsq, hc_nn, hnn]

private theorem pole_action_prime_mode_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM_int : 0 < ∫ u, φ u ^ 2)
    {M q : ℕ} {c_p : ℝ} (hM1 : 1 ≤ M) (hLM0 : 0 < Real.log (M : ℝ))
    (hq : q.Prime) (hqL : (q : ℝ) ≤ Real.log (M : ℝ))
    (hcp0 : 0 < c_p) (hcp1 : c_p ≤ 1) :
    ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c_p M)
      (normalizedRamanujanHorizonVector q M)‖ ≤ 4 * atomPoleMomentErrorConstant φ := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
  have hq_pos : 0 < q := hq.pos
  have hqR_pos : (0 : ℝ) < q := by exact_mod_cast hq_pos
  let A_q : ℝ := ∑ j ∈ range q, |normalizedRamanujanMode q j|
  have hA_q0 : 0 ≤ A_q := sum_nonneg fun _ _ => abs_nonneg _
  have hA_q_le : A_q ≤ 2 * Real.sqrt (q : ℝ) := sum_abs_normalizedRamanujanMode_prime_le hq
  have hA_div_LM : A_q ^ 2 / Real.log (M : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hLM0]
    have hsq : A_q ^ 2 ≤ 4 * (q : ℝ) := by
      have h1 := pow_le_pow_left₀ hA_q0 hA_q_le 2
      rw [mul_pow, Real.sq_sqrt hqR_pos.le] at h1
      linarith only [h1]
    linarith only [hsq, hqL]
  have hd := abs_atomPoleErrorCoefficient_le_at_touching hφ hsupp hM_int hcp0 hcp1 hM1
  have hs := mul_self_le_mul_self (abs_nonneg _) hd
  rw [← sq, sq_abs, ← sq] at hs
  have hunnorm : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c_p M)
      (ramanujanHorizonVector q M)‖ ^ 2 ≤
      4 * (atomPoleMomentErrorConstant φ) ^ 2 * A_q ^ 2 * c_p ^ 4 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c_p M *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) M)
      (horizonProfileVector (ramanujanPoleProfile q) M)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hprof : ∀ j ∈ Icc 1 M, |normalizedRamanujanMode q j| ≤ A_q :=
      fun j _ => abs_normalizedRamanujanMode_le hq_pos j
    calc (∑ n ∈ Icc 1 M, (∑ j ∈ Icc 1 M, atomPoleErrorCoefficient φ c_p M *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * ramanujanPoleProfile q j) ^ 2)
        = ∑ n ∈ Icc 1 M, (atomPoleMomentErrorConstant φ * 0 + atomPoleErrorCoefficient φ c_p M *
            ∑ j ∈ Icc 1 M, (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
              (normalizedRamanujanMode q j / Real.sqrt j)) ^ 2 := by
          refine sum_congr rfl fun n _ => ?_
          rw [mul_zero, zero_add, mul_sum]
          congr 1
          refine sum_congr rfl fun j _ => ?_
          simp only [ramanujanPoleProfile]; ring
      _ = ∑ n ∈ Icc 1 M, (atomPoleErrorCoefficient φ c_p M *
            ∑ j ∈ Icc 1 M, (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
              (normalizedRamanujanMode q j / Real.sqrt j)) ^ 2 := by simp only [mul_zero, zero_add]
      _ ≤ 4 * (atomPoleErrorCoefficient φ c_p M) ^ 2 * A_q ^ 2 * (M : ℝ) ^ 4 :=
          sum_sq_twoPoleKernel_poleProfile_le hA_q0 M hprof _
      _ ≤ 4 * (atomPoleMomentErrorConstant φ * (c_p / M) ^ 2) ^ 2 * A_q ^ 2 * (M : ℝ) ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = 4 * (atomPoleMomentErrorConstant φ) ^ 2 * A_q ^ 2 * c_p ^ 4 := by
          field_simp [hMR.ne']
  have hcp4 : c_p ^ 4 ≤ 1 := pow_le_one₀ hcp0.le hcp1
  have hsq : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c_p M)
      (normalizedRamanujanHorizonVector q M)‖ ^ 2 ≤
      (4 * atomPoleMomentErrorConstant φ) ^ 2 := by
    rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, inv_pow, Real.sq_sqrt hLM0.le]
    calc (Real.log (M : ℝ))⁻¹ *
          ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c_p M) (ramanujanHorizonVector q M)‖ ^ 2
        ≤ (Real.log (M : ℝ))⁻¹ * (4 * (atomPoleMomentErrorConstant φ) ^ 2 * A_q ^ 2 * c_p ^ 4) :=
          mul_le_mul_of_nonneg_left hunnorm (inv_nonneg.mpr hLM0.le)
      _ = 4 * (atomPoleMomentErrorConstant φ) ^ 2 * (A_q ^ 2 / Real.log (M : ℝ)) * c_p ^ 4 := by ring
      _ ≤ 4 * (atomPoleMomentErrorConstant φ) ^ 2 * 4 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA_div_LM (by positivity)) hcp4
            (by positivity) (by positivity)
      _ = (4 * atomPoleMomentErrorConstant φ) ^ 2 := by ring
  have hc_nn : 0 ≤ 4 * atomPoleMomentErrorConstant φ := by
    have := atomPoleMomentErrorConstant_nonneg φ; positivity
  have hnn := norm_nonneg (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c_p M)
    (normalizedRamanujanHorizonVector q M))
  nlinarith only [hsq, hc_nn, hnn]

/-- Uniform vector-norm comparison between separated overlap `c' ∈ (0, 1/2]` and unit overlap `1`
on a prime Ramanujan mode `v_q` (`q` prime, `q ≤ log M`). -/
private theorem exists_prime_mode_separated_sub_one_norm_le :
    ∃ C_sep : ℝ, 0 < C_sep ∧ ∀ᶠ M : ℕ in atTop, ∀ {q : ℕ} {c' : ℝ},
      q.Prime → (q : ℝ) ≤ Real.log (M : ℝ) →
      1 / (512 * Real.exp 2) ≤ c' → c' ≤ 1 / 2 →
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c' M)
          (normalizedRamanujanHorizonVector q M) -
        Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline 1 M)
          (normalizedRamanujanHorizonVector q M)‖ ≤ C_sep := by
  let φ := tiltedUnitSpline
  have hφ : ContDiff ℝ 2 φ := contDiff_tiltedUnitSpline
  have hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0 := tiltedUnitSpline_eq_zero
  have hM_int : 0 < ∫ u, φ u ^ 2 := integral_tiltedUnitSpline_sq_pos
  obtain ⟨K_lip, hK_lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    hasCompactSupport_tiltedUnitSpline hφ (by norm_num)
  have hlip : ∀ u v, |φ u - φ v| ≤ (K_lip : ℝ) * |u - v| := fun u v => by
    simpa only [Real.dist_eq] using hK_lip.dist_le_mul u v
  obtain ⟨C_od, hC_od, hod⟩ := exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace
    hφ hsupp hM_int
  obtain ⟨C_up, hC_up, hup⟩ := exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace
    hφ hsupp hM_int
  let K_sep1 := 4 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2))
  have hlog512_nn : 0 ≤ Real.log (512 * Real.exp 2) :=
    Real.log_nonneg (by have := Real.one_le_exp (zero_le_two (α := ℝ)); linarith)
  let C_total : ℝ := 2 * (Real.log (512 * Real.exp 2) + 4) +
    72 + 18 * atomCrossErrorConstant φ (1 / 2) + 8 * atomPoleMomentErrorConstant φ +
    2 * K_sep1 + 4 * C_od + 2 * C_up + 10
  have hC_tot : 0 < C_total := by
    have := atomCrossErrorConstant_nonneg φ (1 / 2)
    have := atomPoleMomentErrorConstant_nonneg φ
    have : 0 ≤ K_sep1 := by dsimp only [K_sep1]; positivity
    dsimp only [C_total]; positivity
  refine ⟨C_total, hC_tot, ?_⟩
  have hLM : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL4M : Tendsto (fun M : ℕ => Real.log (M : ℝ) ^ 4 / (M : ℝ)) atTop (𝓝 0) :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).congr fun M => by dsimp only [Function.comp_def]; ring
  have hlogL_div : Tendsto (fun M : ℕ => (1 + Real.log (Real.log (M : ℝ))) /
      Real.sqrt (Real.log (M : ℝ))) atTop (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => (1 + Real.log x) / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => 1 / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num))
      have h2 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have hbase := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
        have hcomp := (hbase.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))).const_mul 2
        rw [mul_zero] at hcomp
        refine hcomp.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        dsimp only [Function.comp_def]
        rw [Real.log_rpow hx, pow_one]
        ring
      simpa only [add_zero] using (h1.add h2).congr fun x => by rw [add_div]
    exact (hsub.comp hLM).congr fun M => by
      dsimp only [Function.comp_def]; rw [Real.sqrt_eq_rpow]
  have hrad_nn : 0 ≤ linearNearRowRadius 1 := by
    unfold linearNearRowRadius
    positivity
  have hrad_pos : (0 : ℝ) < 2 * (linearNearRowRadius 1 + 1) := by linarith
  filter_upwards [eventually_ge_atTop 8, hLM.eventually_ge_atTop 64,
    hL4M.eventually (gt_mem_nhds (div_pos one_pos hrad_pos)),
    hL4M.eventually (gt_mem_nhds zero_lt_one),
    hlogL_div.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 36))]
    with M hM8 hLM64 hL4M_rad hL4M_one hLL_small
  intro q c' hq hqL hc'_lo hc'_hi
  have hM1 : 1 ≤ M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM1
  have hLM0 : 0 < Real.log (M : ℝ) := by linarith
  have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) hc'_lo
  have hc'1 : c' < 1 := by linarith
  have hsep : c' / (M : ℝ) < atomSpacing M := by
    apply lt_of_lt_of_le _ (inv_succ_le_atomSpacing hM1)
    rw [div_lt_div_iff₀ hMR (by positivity)]
    have hM8R : (8 : ℝ) ≤ M := by exact_mod_cast hM8
    have hc'M : c' * ((M : ℝ) + 1) ≤ (1 / 2) * ((M : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hc'_hi (by positivity)
    linarith
  have hq2 : 2 ≤ q := hq.two_le
  have hq_pos : 0 < q := hq.pos
  have hqR_pos : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hq4_M : ((q * q : ℕ) + 1 : ℝ) * (linearNearRowRadius 1 + 1) ≤ (M : ℝ) := by
    have hq2_le : ((q * q : ℕ) + 1 : ℝ) ≤ 2 * Real.log (M : ℝ) ^ 4 := by
      have hqR2 : ((q * q : ℕ) : ℝ) ≤ Real.log (M : ℝ) ^ 2 := by
        push_cast; nlinarith only [hqL, hqR_pos]
      have hL2_L4 : Real.log (M : ℝ) ^ 2 ≤ Real.log (M : ℝ) ^ 4 :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have h1L4 : (1 : ℝ) ≤ Real.log (M : ℝ) ^ 4 := one_le_pow₀ (by linarith)
      linarith
    have hlt := (div_lt_iff₀ hMR).mp hL4M_rad
    have hlt' : 2 * (linearNearRowRadius 1 + 1) * Real.log (M : ℝ) ^ 4 < (M : ℝ) := by
      have := (lt_div_iff₀ hrad_pos).mp (by
        calc Real.log (M : ℝ) ^ 4 < 1 / (2 * (linearNearRowRadius 1 + 1)) * (M : ℝ) := hlt
          _ = (M : ℝ) / (2 * (linearNearRowRadius 1 + 1)) := by ring)
      linarith
    have hmul := mul_le_mul_of_nonneg_right hq2_le (by linarith : 0 ≤ linearNearRowRadius 1 + 1)
    linarith
  have hqM : q * q ≤ M := by
    have h1 : ((q * q : ℕ) : ℝ) ≤ ((q * q : ℕ) + 1 : ℝ) * (linearNearRowRadius 1 + 1) := by
      have hrad1 : (1 : ℝ) ≤ linearNearRowRadius 1 + 1 := by linarith
      nlinarith only [hrad1, Nat.cast_nonneg (q * q)]
    exact_mod_cast h1.trans hq4_M
  have hlog_18 : 18 * (1 + Real.log (q : ℝ)) ≤ Real.log (M : ℝ) := by
    have hlogq : Real.log (q : ℝ) ≤ Real.log (Real.log (M : ℝ)) := Real.log_le_log hqR_pos hqL
    have hs := (div_lt_iff₀ (Real.sqrt_pos.mpr hLM0)).mp hLL_small
    have hsq_le : Real.sqrt (Real.log (M : ℝ)) ≤ Real.log (M : ℝ) :=
      Real.sqrt_le_iff.mpr ⟨hLM0.le, by nlinarith only [hLM64]⟩
    linarith
  let v := normalizedRamanujanHorizonVector q M
  have hv_mem : v ∈ conductorSubspace q M :=
    mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨hq_pos, le_rfl⟩)
  have hv_norm : ‖v‖ ≤ 2 := by
    have hb := abs_norm_normalizedRamanujanHorizonVector_sq_sub_one_le hq2 hqM
    have hfrac : (2 * Real.log (q : ℝ) + 9) / Real.log (M : ℝ) ≤ 1 := by
      rw [div_le_one hLM0]; linarith [Real.log_natCast_nonneg q]
    have hsq : ‖v‖ ^ 2 ≤ 2 ^ 2 := by linarith [(abs_le.mp hb).2, hfrac]
    nlinarith only [hsq, norm_nonneg v]
  have hdec_c' := congrArg (fun A => Matrix.toEuclideanLin A v)
    (completeWeilMatrix_eq_decomposition hφ hsupp hM_int hc'0 hM1 hsep)
  have hdec_1 := congrArg (fun A => Matrix.toEuclideanLin A v)
    (completeWeilMatrix_eq_decomposition_at_every_overlap hφ hsupp hM_int one_pos hM1)
  have hone_v : Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex M) (PrimeHorizonIndex M) ℝ) v = v := by
    ext i; change ((1 : Matrix _ _ ℝ) *ᵥ v) i = v i; rw [Matrix.one_mulVec]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hone_v] at hdec_c' hdec_1
  have hdiff : Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v -
      Matrix.toEuclideanLin (completeWeilMatrix φ 1 M) v =
      (completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v +
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v -
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) M) v -
      Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M) v +
      Matrix.toEuclideanLin (separatedCrossErrorMatrix φ 1 M) v +
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c' M) v -
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ 1 M) v -
      (Matrix.toEuclideanLin (overlapMatrix φ 1 M) v - downwardPrimeVector φ 1 M v) +
      upwardPrimeVector φ 1 M v := by
    rw [hdec_c', hdec_1, fullWeilNonRatioMatrix_eq_downward_add_upward hφ hsupp hM_int one_pos hM1 v]
    module
  have hself_fp : |completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1| ≤
      Real.log (512 * Real.exp 2) := by
    rw [completeWeilSelfFinitePart_eq_at_one_sub_log φ hc'0]
    ring_nf
    rw [abs_neg, abs_of_nonpos (Real.log_nonpos hc'0.le hc'1.le)]
    have hlog := Real.log_le_log (by positivity) hc'_lo
    rw [one_div, Real.log_inv] at hlog
    linarith
  have hself_c' : |completeWeilSelfError φ c' M| ≤ 2 := by
    have hb := abs_completeWeilSelfError_le hφ hsupp hM_int hc'0 hc'1 hM1
    have he1 : Real.exp (1 / 2 : ℝ) / 2 ≤ 3 / 2 := by
      have := Real.exp_one_lt_d9
      have hle := Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)
      linarith
    have hdiv : c' / (M : ℝ) ≤ 1 :=
      (div_le_one hMR).mpr (by linarith [show (1 : ℝ) ≤ M by exact_mod_cast hM1])
    have hm := mul_le_mul he1 hdiv (by positivity) (by norm_num)
    linarith
  have hself_1 : |completeWeilSelfError φ 1 M| ≤ 2 := by
    have hw0 : 0 < (1 : ℝ) / M := div_pos one_pos hMR
    have hw1 : (1 : ℝ) / M ≤ 1 := (div_le_one hMR).mpr (by exact_mod_cast hM1)
    have hG : 0 < ∫ u, atomDilate φ ((1 : ℝ) / M) u ^ 2 := by
      rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM_int
    have hlev := abs_levyEnergy_atomDilate_sub_le hφ hsupp hM_int hw0 hw1 hlip
    have heq : completeWeilSelfError φ 1 M =
        (levyEnergy (atomDilate φ ((1 : ℝ) / M)) -
          (Real.log (1 / ((1 : ℝ) / M)) + profileRobin φ) *
            ∫ u, atomDilate φ ((1 : ℝ) / M) u ^ 2) / (∫ u, atomDilate φ ((1 : ℝ) / M) u ^ 2) := by
      rw [completeWeilSelfError, ← completeWeil_self_scalar_identity_all_widths φ one_pos hM1]
      field_simp [hG.ne']; ring
    have hb : |completeWeilSelfError φ 1 M| ≤ Real.exp (1 / 2) / 2 * ((1 : ℝ) / M) := by
      rw [heq, abs_div, abs_of_pos hG, div_le_iff₀ hG]; exact hlev
    have he1 : Real.exp (1 / 2 : ℝ) / 2 ≤ 3 / 2 := by
      have := Real.exp_one_lt_d9
      have hle := Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)
      linarith
    have hm := mul_le_mul he1 hw1 (by positivity) (by norm_num)
    linarith
  have h1_norm : ‖(completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
      completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v‖ ≤
      2 * (Real.log (512 * Real.exp 2) + 4) := by
    rw [norm_smul, Real.norm_eq_abs]
    have habs : |completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M| ≤
        Real.log (512 * Real.exp 2) + 4 := by
      have t1 := abs_add_le (completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1)
        (completeWeilSelfError φ c' M)
      have t2 := abs_sub (completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M) (completeWeilSelfError φ 1 M)
      linarith
    have hc_pos : 0 ≤ Real.log (512 * Real.exp 2) + 4 := by linarith
    calc _ ≤ (Real.log (512 * Real.exp 2) + 4) * 2 :=
          mul_le_mul habs hv_norm (norm_nonneg _) hc_pos
      _ = _ := by ring
  have h2_norm : ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v‖ ≤ 36 :=
    center_action_prime_mode_le hLM0 hq hqL (completeWeilPoleShift_nonneg φ hc'0.le)
      ((completeWeilPoleShift_le hφ.continuous hsupp hM_int hc'0.le).trans hc'1.le)
  have h3_norm : ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) M) v‖ ≤ 36 :=
    center_action_prime_mode_le hLM0 hq hqL (completeWeilPoleShift_nonneg φ zero_le_one)
      (completeWeilPoleShift_le hφ.continuous hsupp hM_int zero_le_one)
  have h4_norm : ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M) v‖ ≤
      18 * atomCrossErrorConstant φ (1 / 2) :=
    cross_action_prime_mode_le hφ hsupp hM_int hM1 hLM0 hq hqL hc'0 hc'_hi
  have h5_norm : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ 1 M) v‖ ≤ 2 * K_sep1 := by
    have hb := norm_separatedCrossErrorMatrix_le hφ hsupp hM_int one_pos hM1 v
    have hK0 : 0 ≤ K_sep1 := by dsimp only [K_sep1]; positivity
    change ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ 1 M) v‖ ≤
      K_sep1 * 1 ^ 2 * ‖v‖ at hb
    nlinarith only [hb, hv_norm, hK0]
  have h6_norm : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c' M) v‖ ≤
      4 * atomPoleMomentErrorConstant φ :=
    pole_action_prime_mode_le hφ hsupp hM_int hM1 hLM0 hq hqL hc'0 hc'1.le
  have h7_norm : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ 1 M) v‖ ≤
      4 * atomPoleMomentErrorConstant φ :=
    pole_action_prime_mode_le hφ hsupp hM_int hM1 hLM0 hq hqL one_pos le_rfl
  have hw1_third : (1 : ℝ) / M ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hMR (by norm_num)]
    have : (8 : ℝ) ≤ M := by exact_mod_cast hM8
    linarith
  have h8_norm : ‖Matrix.toEuclideanLin (overlapMatrix φ 1 M) v - downwardPrimeVector φ 1 M v‖ ≤
      4 * C_od := by
    have hb := hod hq2 hqM hlog_18 le_rfl hw1_third hq4_M hv_mem
    rw [Real.log_one, add_zero, one_pow, one_mul, one_mul] at hb
    have hterm1 : (1 + Real.log (q : ℝ)) * Real.sqrt (1 / Real.log (M : ℝ)) ≤ 1 := by
      rw [Real.sqrt_div zero_le_one, Real.sqrt_one, mul_one_div]
      have hlogq : Real.log (q : ℝ) ≤ Real.log (Real.log (M : ℝ)) := Real.log_le_log hqR_pos hqL
      have hle : (1 + Real.log (q : ℝ)) / Real.sqrt (Real.log (M : ℝ)) ≤
          (1 + Real.log (Real.log (M : ℝ))) / Real.sqrt (Real.log (M : ℝ)) :=
        div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      linarith
    have hterm2 : (q : ℝ) * Real.sqrt (Real.log (M : ℝ) / M) ≤ 1 := by
      have hLM4_M : Real.log (M : ℝ) ^ 4 ≤ M := by
        have hlt := (div_lt_iff₀ hMR).mp hL4M_one
        linarith
      have hLM3_M : Real.log (M : ℝ) ^ 3 ≤ M := by
        have : Real.log (M : ℝ) ^ 3 ≤ Real.log (M : ℝ) ^ 4 :=
          pow_le_pow_right₀ (by linarith) (by omega)
        linarith
      have hsq : ((q : ℝ) * Real.sqrt (Real.log (M : ℝ) / M)) ^ 2 ≤ 1 := by
        rw [mul_pow, Real.sq_sqrt (div_nonneg hLM0.le hMR.le)]
        calc (q : ℝ) ^ 2 * (Real.log (M : ℝ) / M)
            ≤ Real.log (M : ℝ) ^ 2 * (Real.log (M : ℝ) / M) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hqR_pos.le hqL 2) (by positivity)
          _ = Real.log (M : ℝ) ^ 3 / M := by ring
          _ ≤ 1 := (div_le_one hMR).mpr hLM3_M
      nlinarith only [hsq, mul_nonneg hqR_pos.le (Real.sqrt_nonneg (Real.log (M : ℝ) / M))]
    calc _ ≤ C_od * (1 + 1) * 2 :=
          hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hC_od.le)
            hv_norm (norm_nonneg _) (by positivity))
      _ = 4 * C_od := by ring
  have h9_norm : ‖upwardPrimeVector φ 1 M v‖ ≤ 2 * C_up := by
    have hq4_e : ((q * q : ℕ) + 1 : ℝ) * (1 * Real.exp 1 + 1) ≤ M := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hq4_M
      unfold linearNearRowRadius
      have he12 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      have he2_pos : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
      linarith
    have hb := hup hq2 hlog_18 le_rfl hw1_third hq4_e hv_mem
    rw [Real.log_one, add_zero, Real.sqrt_one, mul_one, mul_one] at hb
    calc _ ≤ C_up * 2 := hb.trans (mul_le_mul_of_nonneg_left hv_norm hC_up.le)
      _ = 2 * C_up := by ring
  rw [hdiff]
  have t1 := norm_add_le
    ((completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v +
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v -
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) M) v -
      Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M) v +
      Matrix.toEuclideanLin (separatedCrossErrorMatrix φ 1 M) v +
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c' M) v -
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ 1 M) v -
      (Matrix.toEuclideanLin (overlapMatrix φ 1 M) v - downwardPrimeVector φ 1 M v))
    (upwardPrimeVector φ 1 M v)
  have t2 := norm_sub_le
    ((completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v +
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v -
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) M) v -
      Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M) v +
      Matrix.toEuclideanLin (separatedCrossErrorMatrix φ 1 M) v +
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c' M) v -
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ 1 M) v)
    (Matrix.toEuclideanLin (overlapMatrix φ 1 M) v - downwardPrimeVector φ 1 M v)
  have t3 := norm_sub_le
    ((completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v +
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v -
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) M) v -
      Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M) v +
      Matrix.toEuclideanLin (separatedCrossErrorMatrix φ 1 M) v +
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c' M) v)
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ 1 M) v)
  have t4 := norm_add_le
    ((completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v +
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v -
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) M) v -
      Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M) v +
      Matrix.toEuclideanLin (separatedCrossErrorMatrix φ 1 M) v)
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c' M) v)
  have t5 := norm_add_le
    ((completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v +
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v -
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) M) v -
      Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M) v)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ 1 M) v)
  have t6 := norm_sub_le
    ((completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v +
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v -
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) M) v)
    (Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c' M) v)
  have t7 := norm_sub_le
    ((completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v +
      Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ 1) M) v)
  have t8 := norm_add_le
    ((completeWeilSelfFinitePart φ c' - completeWeilSelfFinitePart φ 1 +
        completeWeilSelfError φ c' M - completeWeilSelfError φ 1 M) • v)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c') M) v)
  dsimp only [C_total]
  linarith only [t1, t2, t3, t4, t5, t6, t7, t8,
    h1_norm, h2_norm, h3_norm, h4_norm, h5_norm, h6_norm, h7_norm, h8_norm, h9_norm]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
