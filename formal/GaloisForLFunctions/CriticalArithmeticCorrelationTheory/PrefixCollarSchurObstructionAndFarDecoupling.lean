import Mathlib.NumberTheory.Bertrand
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UnrestrictedAtomicGardingFailsAndCollarGardingHolds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFarComplementHasAnExplicitRatioInterval
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.QuadraticOverlapConductorResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorEnergiesHavePolynomialBounds
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormNormCosts
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandTopTailBounds

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
      funext fun u => by dsimp only; rw [show u + t + b = u + b + t by ring]
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
        hsym x0 v1, real_inner_comm x0 (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) v1)]
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
      have h2 : (max 2 (lowPacketCutoff N) : ℝ) ≤ Real.log (N : ℝ) ^ (13 / 32 : ℝ) :=
        max_le hQ2 h1
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
    refine (le_of_eq ?_).trans (hb.trans (le_of_eq (by ring)))
    simp only [ramanujanPoleProfile, mul_assoc, ← mul_sum]
  have hnorm_sq : ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α M)
      (normalizedRamanujanHorizonVector q M)‖ ^ 2 ≤ 36 ^ 2 := by
    rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, inv_pow, Real.sq_sqrt hLM0.le]
    have hα_sq : α ^ 2 ≤ 1 := by nlinarith only [hα0, hα1]
    have h1 : (Real.log (M : ℝ))⁻¹ * (α ^ 2 * (9 * A_q) ^ 2) ≤ 36 ^ 2 := by
      have h9 : α ^ 2 * (9 * A_q) ^ 2 ≤ 1 * (81 * A_q ^ 2) := by
        rw [show (9 * A_q) ^ 2 = 81 * A_q ^ 2 by ring]
        exact mul_le_mul_of_nonneg_right hα_sq (by positivity)
      calc (Real.log (M : ℝ))⁻¹ * (α ^ 2 * (9 * A_q) ^ 2)
          ≤ (Real.log (M : ℝ))⁻¹ * (1 * (81 * A_q ^ 2)) :=
            mul_le_mul_of_nonneg_left h9 (inv_nonneg.mpr hLM0.le)
        _ = 81 * (A_q ^ 2 / Real.log (M : ℝ)) := by rw [div_eq_mul_inv]; ring
        _ ≤ 81 * 4 := mul_le_mul_of_nonneg_left hA_div_LM (by norm_num)
        _ ≤ 36 ^ 2 := by norm_num
    exact (mul_le_mul_of_nonneg_left hunnorm (inv_nonneg.mpr hLM0.le)).trans h1
  exact (abs_le_of_sq_le_sq' hnorm_sq (by norm_num)).2

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
      nlinarith only [hrad1, (Nat.cast_nonneg (q * q) : (0 : ℝ) ≤ (q * q : ℕ))]
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
    rw [completeWeilSelfFinitePart_eq_at_one_sub_log φ hc'0, sub_sub_cancel_left,
      abs_neg, abs_of_nonpos (Real.log_nonpos hc'0.le hc'1.le)]
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

/-- Exact horizon reduction of `completeWeilEnergy` for vectors vanishing above `M ≤ N`:
`completeWeilEnergy φ c N x = completeWeilEnergy φ (c * M / N) M x|_M`. -/
theorem completeWeilEnergy_eq_of_vanish_above {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (_hM_int : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {M N : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hvan : ∀ n, M < n → primeHorizonExtension x n = 0) :
    completeWeilEnergy φ c N x =
      completeWeilEnergy φ (c * (M : ℝ) / N) M
        (horizonProfileVector (primeHorizonExtension x) M) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hN1 : 1 ≤ N := hM1.trans hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set c' := c * (M : ℝ) / N
  have hc' : 0 < c' := div_pos (mul_pos hc hM0) hN0
  have hw_eq : c' / (M : ℝ) = c / (N : ℝ) := by
    dsimp only [c']
    field_simp [hM0.ne', hN0.ne']
  set x' := horizonProfileVector (primeHorizonExtension x) M
  have hatom : atomicTest N (primeHorizonExtension x) (atomDilate φ (c / N)) =
      atomicTest M (primeHorizonExtension x') (atomDilate φ (c' / M)) := by
    rw [hw_eq, atomicTest_eq_of_vanish_above hMN hvan]
    funext u
    unfold atomicTest
    refine sum_congr rfl fun n hn => ?_
    rw [primeHorizonExtension_coe x' ⟨n, hn⟩]
    rfl
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN1 x,
    completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc' hM1 x',
    hatom, hw_eq]

/-- Polarized horizon reduction of `completeWeilMatrix` for vectors vanishing above `M ≤ N`. -/
theorem completeWeilMatrix_inner_eq_of_vanish_above {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM_int : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {M N : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hx : ∀ n, M < n → primeHorizonExtension x n = 0)
    (hy : ∀ n, M < n → primeHorizonExtension y n = 0) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ =
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c * (M : ℝ) / N) M)
        (horizonProfileVector (primeHorizonExtension x) M),
        horizonProfileVector (primeHorizonExtension y) M⟫ := by
  set c' := c * (M : ℝ) / N
  set x' := horizonProfileVector (primeHorizonExtension x) M
  set y' := horizonProfileVector (primeHorizonExtension y) M
  have hadd_van : ∀ n, M < n → primeHorizonExtension (x + y) n = 0 := fun n hn => by
    by_cases h : n ∈ Icc 1 N
    · rw [primeHorizonExtension_coe (x + y) ⟨n, h⟩, PiLp.add_apply,
        ← primeHorizonExtension_coe x ⟨n, h⟩, ← primeHorizonExtension_coe y ⟨n, h⟩,
        hx n hn, hy n hn, add_zero]
    · simp [primeHorizonExtension, h]
  have hsub_van : ∀ n, M < n → primeHorizonExtension (x - y) n = 0 := fun n hn => by
    by_cases h : n ∈ Icc 1 N
    · rw [primeHorizonExtension_coe (x - y) ⟨n, h⟩, PiLp.sub_apply,
        ← primeHorizonExtension_coe x ⟨n, h⟩, ← primeHorizonExtension_coe y ⟨n, h⟩,
        hx n hn, hy n hn, sub_zero]
    · simp [primeHorizonExtension, h]
  have hp_add : horizonProfileVector (primeHorizonExtension (x + y)) M = x' + y' := by
    ext ⟨n, hn⟩
    have hnN : n ∈ Icc 1 N := mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
    change primeHorizonExtension (x + y) n = primeHorizonExtension x n + primeHorizonExtension y n
    rw [primeHorizonExtension_coe (x + y) ⟨n, hnN⟩, primeHorizonExtension_coe x ⟨n, hnN⟩,
      primeHorizonExtension_coe y ⟨n, hnN⟩, PiLp.add_apply]
  have hp_sub : horizonProfileVector (primeHorizonExtension (x - y)) M = x' - y' := by
    ext ⟨n, hn⟩
    have hnN : n ∈ Icc 1 N := mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
    change primeHorizonExtension (x - y) n = primeHorizonExtension x n - primeHorizonExtension y n
    rw [primeHorizonExtension_coe (x - y) ⟨n, hnN⟩, primeHorizonExtension_coe x ⟨n, hnN⟩,
      primeHorizonExtension_coe y ⟨n, hnN⟩, PiLp.sub_apply]
  have he1 := completeWeilEnergy_eq_of_vanish_above hφ hsupp hM_int hc hM1 hMN (x + y) hadd_van
  have he2 := completeWeilEnergy_eq_of_vanish_above hφ hsupp hM_int hc hM1 hMN (x - y) hsub_van
  rw [hp_add] at he1
  rw [hp_sub] at he2
  have hsymN := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  have hsymM := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c' M)
  have hpolN : completeWeilEnergy φ c N (x + y) - completeWeilEnergy φ c N (x - y) =
      4 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ := by
    unfold completeWeilEnergy
    rw [map_add, map_sub, inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right, hsymN y x, real_inner_comm y]
    ring
  have hpolM : completeWeilEnergy φ c' M (x' + y') - completeWeilEnergy φ c' M (x' - y') =
      4 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c' M) x', y'⟫ := by
    unfold completeWeilEnergy
    rw [map_add, map_sub, inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right, hsymM y' x', real_inner_comm y']
    ring
  linarith only [he1, he2, hpolN, hpolM]

/-- Exact logarithmic-translation reduction of a `q`-divisible collar spike on `Ioc M N` to a dense
collar profile on `Ioc (M / q) (N / q)` at separated overlap `c * (N / q) / N`. -/
private theorem completeWeilEnergy_collar_spike_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (_hM_int : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {M N q : ℕ} (hq : 0 < q) (hNq1 : 1 ≤ N / q) (A : ℝ) :
    completeWeilEnergy φ c N
        (horizonProfileVector
          (fun n => if M < n ∧ q ∣ n then A * Real.sqrt q / Real.sqrt n else 0) N) =
      completeWeilEnergy φ (c * ((N / q : ℕ) : ℝ) / N) (N / q)
        (horizonProfileVector (fun k => if M / q < k then A / Real.sqrt k else 0) (N / q)) := by
  set Nq := N / q
  set Mq := M / q
  have hN1 : 1 ≤ N := hNq1.trans (Nat.div_le_self N q)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNq0 : (0 : ℝ) < Nq := by exact_mod_cast hNq1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set cq := c * (Nq : ℝ) / N
  have hcq : 0 < cq := div_pos (mul_pos hc hNq0) hN0
  have hw_eq : cq / (Nq : ℝ) = c / (N : ℝ) := by
    dsimp only [cq]
    field_simp [hNq0.ne', hN0.ne']
  set y_sp := horizonProfileVector
    (fun n => if M < n ∧ q ∣ n then A * Real.sqrt q / Real.sqrt n else 0) N
  set x_q := horizonProfileVector (fun k => if Mq < k then A / Real.sqrt k else 0) Nq
  set g := atomDilate φ (c / N)
  have hw : 0 < c / (N : ℝ) := div_pos hc hN0
  obtain ⟨hg, hgs, _⟩ := atomDilate_facts hφ hsupp hw
  have hf_q : ContDiff ℝ 2 (atomicTest Nq (primeHorizonExtension x_q) g) :=
    contDiff_atomicTest hg Nq _
  have hfc_q : HasCompactSupport (atomicTest Nq (primeHorizonExtension x_q) g) :=
    hasCompactSupport_atomicTest hgs Nq _
  have hshift : (fun u => atomicTest N (primeHorizonExtension y_sp) g (u + Real.log q)) =
      atomicTest Nq (primeHorizonExtension x_q) g := by
    funext u
    unfold atomicTest
    have himg_sub : (Icc 1 Nq).image (q * ·) ⊆ Icc 1 N := by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
      obtain ⟨hk1, hkN⟩ := mem_Icc.mp hk
      exact mem_Icc.mpr ⟨by nlinarith, by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hq).mp hkN⟩
    have hzero_off : ∀ n ∈ Icc 1 N, n ∉ (Icc 1 Nq).image (q * ·) →
        primeHorizonExtension y_sp n * g (u + Real.log q - Real.log n) = 0 := by
      intro n hn hnot
      rw [primeHorizonExtension_coe y_sp ⟨n, hn⟩]
      change (if M < n ∧ q ∣ n then A * Real.sqrt q / Real.sqrt n else 0) * _ = 0
      have hndvd : ¬(q ∣ n) := by
        intro ⟨k, hnk⟩
        apply hnot
        refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨?_, ?_⟩, hnk.symm⟩
        · have hn1 := (mem_Icc.mp hn).1
          by_contra hk0
          have : k = 0 := by omega
          rw [this, mul_zero] at hnk
          omega
        · exact (Nat.le_div_iff_mul_le hq).mpr (by rw [mul_comm, ← hnk]; exact (mem_Icc.mp hn).2)
      rw [if_neg (fun h => hndvd h.2), zero_mul]
    rw [← sum_subset himg_sub hzero_off,
      sum_image (fun k₁ _ k₂ _ heq => Nat.eq_of_mul_eq_mul_left hq heq)]
    refine sum_congr rfl fun k hk => ?_
    have hkN_mem : q * k ∈ Icc 1 N := himg_sub (mem_image_of_mem _ hk)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
    rw [primeHorizonExtension_coe y_sp ⟨q * k, hkN_mem⟩, primeHorizonExtension_coe x_q ⟨k, hk⟩]
    change (if M < q * k ∧ q ∣ q * k then A * Real.sqrt q / Real.sqrt ((q * k : ℕ) : ℝ) else 0) *
        g (u + Real.log q - Real.log ((q * k : ℕ) : ℝ)) =
      (if Mq < k then A / Real.sqrt k else 0) * g (u - Real.log k)
    have hiff : (M < q * k ∧ q ∣ q * k) ↔ Mq < k :=
      ⟨fun h => (Nat.div_lt_iff_lt_mul hq).mpr (by rw [mul_comm]; exact h.1),
       fun h => ⟨by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul hq).mp h, dvd_mul_right q k⟩⟩
    have hlog : u + Real.log q - Real.log ((q * k : ℕ) : ℝ) = u - Real.log k := by
      rw [Nat.cast_mul, Real.log_mul hq0.ne' hk0.ne']
      ring
    rw [hlog]
    by_cases hcond : Mq < k
    · rw [if_pos (hiff.mpr hcond), if_pos hcond]
      congr 1
      rw [Nat.cast_mul, Real.sqrt_mul hq0.le]
      field_simp [(Real.sqrt_pos.mpr hq0).ne', (Real.sqrt_pos.mpr hk0).ne']
    · rw [if_neg (fun h => hcond (hiff.mp h)), if_neg hcond, zero_mul]
  have hquad_eq : weilQuad (atomicTest N (primeHorizonExtension y_sp) g) =
      weilQuad (atomicTest Nq (primeHorizonExtension x_q) g) := by
    have hf_sp : ContDiff ℝ 2 (atomicTest N (primeHorizonExtension y_sp) g) :=
      contDiff_atomicTest hg N _
    have hfc_sp : HasCompactSupport (atomicTest N (primeHorizonExtension y_sp) g) :=
      hasCompactSupport_atomicTest hgs N _
    rw [← hshift, weilQuad_comp_add_right hf_sp hfc_sp (Real.log q)]
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN1 y_sp,
    completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hcq hNq1 x_q,
    hw_eq, hquad_eq]

/-- Off-diagonal Gram orthogonality bounds the low-packet projection of `v_{q_N}` by
`O((1 + log q_N) / log N)`. -/
private theorem norm_lowPacketProjection_primeAboveLowPacket_le :
    ∀ᶠ N : ℕ in atTop,
      ‖(conductorSubspace (lowPacketCutoff N) N).starProjection
          (normalizedRamanujanHorizonVector (primeAboveLowPacket N) N)‖ ≤
        18 * (1 + Real.log (primeAboveLowPacket N)) / Real.log N := by
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hN_div : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 / (N : ℝ)) atTop (𝓝 0) :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).congr fun N => by dsimp only [Function.comp_def]; ring
  have hlog_div : Tendsto (fun N : ℕ =>
      9 * (1 + Real.log (4 * Real.log (N : ℝ))) / Real.log (N : ℝ)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => 9 * (1 + Real.log (4 * x)) / x) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => (9 + 9 * Real.log 4) / x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h2 : Tendsto (fun x : ℝ => 9 * (Real.log x / x)) atTop (𝓝 0) := by
        simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 9
      have hsum := h1.add h2
      rw [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.log_mul (by norm_num) hx.ne']
      ring
    exact hsub.comp hL
  filter_upwards [hL.eventually_ge_atTop 16,
    hN_div.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hlog_div.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop 4] with N hL16 hNdiv h9 hN4
  set Q₁ := lowPacketCutoff N
  set q := primeAboveLowPacket N
  obtain ⟨hq_prime, hq_gt, hq_le⟩ := primeAboveLowPacket_spec N
  have hq2 : 2 ≤ q := hq_prime.two_le
  have hQ₁_lt_q : Q₁ < q := (le_max_right 2 Q₁).trans_lt hq_gt
  have hL0 : 0 < Real.log (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq_le_4L : (q : ℝ) ≤ 4 * Real.log (N : ℝ) := by
    have hQ₁_le : (Q₁ : ℝ) ≤ Real.log (N : ℝ) ^ (13 / 32 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg hL0.le _)
    have hrpow_le : Real.log (N : ℝ) ^ (13 / 32 : ℝ) ≤ Real.log (N : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)).trans_eq (Real.rpow_one _)
    have hmax_le : ((max 2 Q₁ : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      rw [Nat.cast_max, Nat.cast_ofNat]
      exact max_le (by linarith) (by linarith)
    have hq_cast : (q : ℝ) ≤ 2 * ((max 2 Q₁ : ℕ) : ℝ) := by exact_mod_cast hq_le
    linarith
  have hqqN : q * q ≤ N := by
    have h1 : ((q * q : ℕ) : ℝ) ≤ 16 * Real.log (N : ℝ) ^ 2 := by
      rw [Nat.cast_mul]
      nlinarith only [hq_le_4L, Nat.cast_nonneg (α := ℝ) q]
    have h2 : 16 * Real.log (N : ℝ) ^ 2 ≤ N := by
      have := (div_lt_iff₀ hN0).mp hNdiv
      linarith
    exact_mod_cast h1.trans h2
  set v := normalizedRamanujanHorizonVector q N
  set u := (conductorSubspace Q₁ N).starProjection v
  by_cases hu0 : ‖u‖ = 0
  · rw [hu0]
    have hq_nn := Real.log_natCast_nonneg q
    positivity
  have hu_pos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu0)
  obtain ⟨c_seq, -, hu_eq⟩ := (mem_conductorSubspace_iff (M := Q₁) (N := N) (x := u)).mp
    ((conductorSubspace Q₁ N).starProjection_apply_mem v)
  let b : ℕ → ℝ := fun m => if m ≤ Q₁ then c_seq m else 0
  have hu_b : u = ∑ m ∈ Icc 1 q, b m • normalizedRamanujanHorizonVector m N := by
    rw [hu_eq]
    have hsub : Icc 1 Q₁ ⊆ Icc 1 q := fun m hm =>
      mem_Icc.mpr ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans hQ₁_lt_q.le⟩
    rw [← sum_subset hsub (fun m hm_q hm_not => by
      have hm1 := (mem_Icc.mp hm_q).1
      have hnot_le : ¬(m ≤ Q₁) := fun hle => hm_not (mem_Icc.mpr ⟨hm1, hle⟩)
      dsimp only [b]
      rw [if_neg hnot_le, zero_smul])]
    refine sum_congr rfl fun m hm => ?_
    dsimp only [b]
    rw [if_pos (mem_Icc.mp hm).2]
  have hb_norm : ∑ m ∈ Icc 1 q, b m ^ 2 ≤ 2 * ‖u‖ ^ 2 := by
    have hgram := (abs_le.mp (abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hq2 hqqN b)).1
    rw [← hu_b] at hgram
    have hcoef_le : 9 * (1 + Real.log q) / Real.log N ≤ 1 / 2 := by
      have hlog_le : Real.log (q : ℝ) ≤ Real.log (4 * Real.log (N : ℝ)) :=
        Real.log_le_log (by exact_mod_cast (show 0 < q by omega)) hq_le_4L
      have hdiv : 9 * (1 + Real.log q) / Real.log N ≤
          9 * (1 + Real.log (4 * Real.log (N : ℝ))) / Real.log N :=
        div_le_div_of_nonneg_right (by linarith) hL0.le
      exact hdiv.trans h9.le
    have hB0 : 0 ≤ ∑ m ∈ Icc 1 q, b m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have hm := mul_le_mul_of_nonneg_right hcoef_le hB0
    linarith only [hgram, hm]
  let a : ℕ → ℝ := fun m => if m = q then 1 else 0
  have hv_a : v = ∑ m ∈ Icc 1 q, a m • normalizedRamanujanHorizonVector m N := by
    have hq_mem : q ∈ Icc 1 q := mem_Icc.mpr ⟨by omega, le_rfl⟩
    rw [sum_eq_single q
      (fun m _ hmq => by dsimp only [a]; rw [if_neg hmq, zero_smul])
      (fun hnot => (hnot hq_mem).elim)]
    dsimp only [a]
    rw [if_pos rfl, one_smul]
  have ha_sq : ∑ m ∈ Icc 1 q, a m ^ 2 = 1 := by
    have hq_mem : q ∈ Icc 1 q := mem_Icc.mpr ⟨by omega, le_rfl⟩
    rw [sum_eq_single q
      (fun m _ hmq => by dsimp only [a]; rw [if_neg hmq]; norm_num)
      (fun hnot => (hnot hq_mem).elim)]
    dsimp only [a]
    rw [if_pos rfl]
    norm_num
  have horth_ab : ∑ m ∈ Icc 1 q, a m * b m = 0 := by
    refine sum_eq_zero fun m _ => ?_
    dsimp only [a, b]
    by_cases hmq : m = q
    · subst hmq
      rw [if_pos rfl, if_neg (Nat.not_le.mpr hQ₁_lt_q), mul_zero]
    · rw [if_neg hmq, zero_mul]
  have hinner_le : |⟪v, u⟫| ≤ 18 * (1 + Real.log q) / Real.log N * ‖u‖ := by
    have hcross := abs_inner_sum_normalizedRamanujanHorizonVector_of_orthog_le hq2 hqqN horth_ab
    rw [← hv_a, ← hu_b, ha_sq, Real.sqrt_one, mul_one] at hcross
    have hsqrt_b : Real.sqrt (∑ m ∈ Icc 1 q, b m ^ 2) ≤ 2 * ‖u‖ := by
      calc Real.sqrt (∑ m ∈ Icc 1 q, b m ^ 2)
          ≤ Real.sqrt (2 * ‖u‖ ^ 2) := Real.sqrt_le_sqrt hb_norm
        _ = Real.sqrt 2 * ‖u‖ := by rw [Real.sqrt_mul zero_le_two, Real.sqrt_sq (norm_nonneg u)]
        _ ≤ 2 * ‖u‖ := mul_le_mul_of_nonneg_right
            (by nlinarith [Real.sq_sqrt (zero_le_two (α := ℝ)), Real.sqrt_nonneg 2])
            (norm_nonneg u)
    have h9_nn : 0 ≤ 9 * (1 + Real.log q) / Real.log N := by
      have := Real.log_natCast_nonneg q; positivity
    exact (hcross.trans (mul_le_mul_of_nonneg_left hsqrt_b h9_nn)).trans_eq (by ring)
  have hvu_eq : ⟪v, u⟫ = ‖u‖ ^ 2 := by
    have horth_u : ⟪v - u, u⟫ = 0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal _ _).mp (Submodule.sub_starProjection_mem_orthogonal v) u
        ((conductorSubspace Q₁ N).starProjection_apply_mem v)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at horth_u
    linarith only [horth_u]
  have hsq_le : ‖u‖ * ‖u‖ ≤ (18 * (1 + Real.log q) / Real.log N) * ‖u‖ := by
    calc ‖u‖ * ‖u‖ = ‖u‖ ^ 2 := (sq ‖u‖).symm
      _ = ⟪v, u⟫ := hvu_eq.symm
      _ ≤ |⟪v, u⟫| := le_abs_self _
      _ ≤ (18 * (1 + Real.log q) / Real.log N) * ‖u‖ := hinner_le
  exact le_of_mul_le_mul_right hsq_le hu_pos

private theorem tendsto_log_c_div_log_log {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => Real.log (c N) / Real.log (Real.log (N : ℝ))) atTop (𝓝 (1 / 8 : ℝ)) := by
  have hLL : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog_rat : Tendsto (fun N : ℕ => Real.log (c N ^ 8 / Real.log (N : ℝ)))
      atTop (𝓝 (Real.log R)) :=
    (Real.continuousAt_log hR.ne').tendsto.comp htend
  have hdiv0 : Tendsto (fun N : ℕ =>
      Real.log (c N ^ 8 / Real.log (N : ℝ)) / Real.log (Real.log (N : ℝ))) atTop (𝓝 0) :=
    hlog_rat.div_atTop hLL
  have hlin := (hdiv0.add_const (1 : ℝ)).const_mul (1 / 8 : ℝ)
  rw [zero_add, mul_one] at hlin
  refine hlin.congr' ?_
  filter_upwards [hc1, hLL.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hcN hLL0 hL0
  dsimp only [Function.comp_def] at hLL0 hL0 ⊢
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
  rw [Real.log_div (pow_pos hc0 8).ne' hL0.ne', Real.log_pow, Nat.cast_ofNat]
  field_simp [hLL0.ne']
  ring

private theorem tendsto_div_log_log_of_abs_sub_le {f g : ℕ → ℝ} {L : ℝ}
    (hg : Tendsto (fun N : ℕ => g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 L))
    {C : ℝ} (hfg : ∀ᶠ N in atTop, |f N - g N| ≤ C) :
    Tendsto (fun N : ℕ => f N / Real.log (Real.log (N : ℝ))) atTop (𝓝 L) := by
  have hLL : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have herr : Tendsto (fun N : ℕ => (f N - g N) / Real.log (Real.log (N : ℝ))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      ((tendsto_const_nhds (x := max 0 C)).div_atTop hLL)
    filter_upwards [hfg, hLL.eventually_gt_atTop 0] with N hb hLL0
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hLL0]
    exact div_le_div_of_nonneg_right (hb.trans (le_max_right 0 C)) hLL0.le
  have hsum := hg.add herr
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hLL.eventually_gt_atTop 0] with N hLL0
  field_simp [hLL0.ne']
  ring

private theorem tameDifferent_prime_le_one {q : ℕ} (hq : q.Prime) :
    |ArithmeticIntersectionTheory.tameDifferent q| ≤ 1 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  unfold ArithmeticIntersectionTheory.tameDifferent
  rw [hq.primeFactors, sum_singleton, abs_div, abs_of_nonneg (Real.log_natCast_nonneg q),
    abs_of_pos hq1, div_le_one hq1]
  exact Real.log_le_sub_one_of_pos hq0

/-- Uniform `L²` synthesis bound for `normalizedCentredAtomicTest`: at overlap `1 ≤ c ≤ N`,
`∫ (normalizedCentredAtomicTest φ x c N)² ≤ (1 + 2e) (∫ φ²) ∑_{n=1}^N x_n²`, with no `c` growth. -/
theorem integral_normalizedCentredAtomicTest_sq_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ}
    (hN1 : 1 ≤ N) (hcN : c ≤ N) (x : ℕ → ℝ) :
    (∫ u, normalizedCentredAtomicTest φ x c N u ^ 2) ≤
      (1 + 2 * Real.exp 1) * (∫ u, φ u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hN0
  let g := atomDilate φ (c / N)
  have hg_cont : Continuous g := hφ.comp (continuous_id.div_const _)
  have hgs : ∀ u, u ∉ Set.Icc 0 (c / (N : ℝ)) → g u = 0 := by
    intro u hu
    apply hsupp
    intro hm
    exact hu ⟨by simpa only [zero_mul] using (le_div_iff₀ hw).mp hm.1, (div_le_one hw).mp hm.2⟩
  have hgc : HasCompactSupport g := hasCompactSupport_of_support_Icc hgs
  have hscale : (∫ u, normalizedCentredAtomicTest φ x c N u ^ 2) =
      ((N : ℝ) / c ^ 2) * ∫ u, atomicTest N x g u ^ 2 := by
    unfold normalizedCentredAtomicTest centredAtomicTest
    simp_rw [mul_pow, div_pow, Real.sq_sqrt hN0.le]
    rw [integral_const_mul]
    exact congrArg (((N : ℝ) / c ^ 2) * ·)
      (integral_add_right_eq_self (fun u => atomicTest N x g u ^ 2) (Real.log N))
  have hatom := integral_atomicTest_sq_le_of_le_horizon hg_cont hgc hc0 hcN hgs x
  rw [integral_atomDilate_sq hw] at hatom
  have hγ : 1 + 2 * Real.exp 1 * c ≤ (1 + 2 * Real.exp 1) * c := by
    nlinarith only [hc1, Real.exp_pos 1]
  have hI0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  rw [hscale]
  calc ((N : ℝ) / c ^ 2) * ∫ u, atomicTest N x g u ^ 2
      ≤ ((N : ℝ) / c ^ 2) * (((c / N) * ∫ u, φ u ^ 2) * ((1 + 2 * Real.exp 1) * c) *
          ∑ n ∈ Icc 1 N, x n ^ 2) :=
        mul_le_mul_of_nonneg_left
          (hatom.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hγ (by positivity)) hS0))
          (by positivity)
    _ = (1 + 2 * Real.exp 1) * (∫ u, φ u ^ 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
        field_simp [hc0.ne', hN0.ne']

private theorem abs_quasimode_energy_sub_le {φ : ℝ → ℝ} {c : ℝ} {N : ℕ}
    {v u : EuclideanSpace ℝ (PrimeHorizonIndex N)} {E_q L_target C_Eq : ℝ}
    (hr_norm : ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) v - E_q • v‖ ≤ 1)
    (hv_norm : ‖v‖ ≤ 2)
    (hEq_sub : |E_q - L_target| ≤ C_Eq)
    (hEq_vsq : |E_q * (‖v‖ ^ 2 - 1)| ≤ 1)
    (hEq_u : |E_q| * ‖u‖ ≤ 1 / 4)
    (hu_norm : ‖u‖ ≤ 1 / 2)
    (hEu_abs : |completeWeilEnergy φ c N u| ≤ 1) :
    |completeWeilEnergy φ c N (v - u) - L_target| ≤ C_Eq + 7 := by
  let r := Matrix.toEuclideanLin (completeWeilMatrix φ c N) v - E_q • v
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  have hBv : Matrix.toEuclideanLin (completeWeilMatrix φ c N) v = E_q • v + r := by
    dsimp only [r]; abel
  have hz_exp : completeWeilEnergy φ c N (v - u) =
      completeWeilEnergy φ c N v -
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) v, u⟫ +
        completeWeilEnergy φ c N u := by
    unfold completeWeilEnergy
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym u v, real_inner_comm u]
    ring
  have hv_exp : completeWeilEnergy φ c N v = E_q * ‖v‖ ^ 2 + ⟪r, v⟫ := by
    unfold completeWeilEnergy
    rw [hBv, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hrv : |⟪r, v⟫| ≤ 2 :=
    (abs_real_inner_le_norm r v).trans
      (by nlinarith only [hr_norm, hv_norm, norm_nonneg r, norm_nonneg v])
  have hBvu : |2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) v, u⟫| ≤ 2 := by
    rw [hBv, inner_add_left, real_inner_smul_left, mul_add]
    have t1 : |2 * (E_q * ⟪v, u⟫)| ≤ 1 := by
      rw [abs_mul, abs_two, abs_mul]
      have hvu : |⟪v, u⟫| ≤ 2 * ‖u‖ :=
        (abs_real_inner_le_norm v u).trans (mul_le_mul_of_nonneg_right hv_norm (norm_nonneg u))
      have hm := mul_le_mul_of_nonneg_left hvu (abs_nonneg E_q)
      linarith only [hm, hEq_u]
    have t2 : |2 * ⟪r, u⟫| ≤ 1 := by
      rw [abs_mul, abs_two]
      have hru : |⟪r, u⟫| ≤ ‖u‖ :=
        (abs_real_inner_le_norm r u).trans (by nlinarith only [hr_norm, norm_nonneg u])
      linarith only [hru, hu_norm]
    exact (abs_add_le _ _).trans (by linarith only [t1, t2])
  have hsplit : completeWeilEnergy φ c N (v - u) - L_target =
      (E_q - L_target) + E_q * (‖v‖ ^ 2 - 1) + ⟪r, v⟫ -
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) v, u⟫ +
        completeWeilEnergy φ c N u := by
    rw [hz_exp, hv_exp]; ring
  rw [hsplit]
  have a1 := abs_add_le
    ((E_q - L_target) + E_q * (‖v‖ ^ 2 - 1) + ⟪r, v⟫ -
      2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) v, u⟫)
    (completeWeilEnergy φ c N u)
  have a2 := abs_sub ((E_q - L_target) + E_q * (‖v‖ ^ 2 - 1) + ⟪r, v⟫)
    (2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) v, u⟫)
  have a3 := abs_add_le ((E_q - L_target) + E_q * (‖v‖ ^ 2 - 1)) ⟪r, v⟫
  have a4 := abs_add_le (E_q - L_target) (E_q * (‖v‖ ^ 2 - 1))
  linarith only [a1, a2, a3, a4, hEq_sub, hEq_vsq, hrv, hBvu, hEu_abs]

private lemma four_pow_nat_le_rpow (k : ℕ) {a b : ℝ} (hab : (4 : ℝ) ^ a ≤ b) {e : ℝ}
    (he : 0 ≤ e) (hke : (k : ℝ) ≤ a * e) : (4 : ℝ) ^ k ≤ b ^ e := by
  have hp := Real.rpow_le_rpow (by positivity) hab he
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)] at hp
  exact ((Real.rpow_natCast 4 k).symm.le.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hke)).trans hp

private lemma global_low_packet_energy_bound_le_one {C_q R c L u_norm E_u : ℝ}
    (hC_q : 0 < C_q) (hR : 0 < R) (hc1 : 1 ≤ c) (hL1 : 1 ≤ L) (hu0 : 0 ≤ u_norm)
    (hL_7_16 : (4 : ℝ) ^ (14 : ℝ) ≤ L ^ (7 / 16 : ℝ))
    (hc2_le : c ^ 2 ≤ (R + 1) * L ^ (1 / 4 : ℝ))
    (hR1_64 : R + 1 ≤ L ^ (1 / 64 : ℝ))
    (hCR_64 : C_q * (R + 1) ≤ L ^ (1 / 64 : ℝ))
    (hu_rpow : u_norm ≤ 1170 / L ^ (63 / 64 : ℝ))
    (hg : |E_u| ≤ C_q * c ^ 3 * (L + 1) * u_norm ^ 2) :
    |E_u| ≤ 1 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  refine hg.trans ?_
  have hc3_le : c ^ 3 ≤ (R + 1) ^ 2 * L ^ (1 / 2 : ℝ) := by
    have hc34 : c ^ 3 ≤ (c ^ 2) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hc1 (by omega)
    have hc4 : (c ^ 2) ^ 2 ≤ ((R + 1) * L ^ (1 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hc2_le 2
    rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hc4
    norm_num at hc4
    exact hc34.trans hc4
  have hL1_le : L + 1 ≤ 2 * L := by linarith only [hL1]
  have hu2_le : u_norm ^ 2 ≤ 1170 ^ 2 / L ^ (63 / 32 : ℝ) := by
    have hp := pow_le_pow_left₀ hu0 hu_rpow 2
    rw [div_pow, ← Real.rpow_natCast (L ^ (63 / 64 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hp
    norm_num at hp; exact hp.trans_eq (by norm_num)
  have hCR_rpow : C_q * (R + 1) ^ 2 ≤ L ^ (2 / 64 : ℝ) := by
    calc C_q * (R + 1) ^ 2 = (C_q * (R + 1)) * (R + 1) := by ring
      _ ≤ L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ) :=
          mul_le_mul hCR_64 hR1_64 (by positivity) (by positivity)
      _ = L ^ (2 / 64 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  calc C_q * c ^ 3 * (L + 1) * u_norm ^ 2
      ≤ C_q * ((R + 1) ^ 2 * L ^ (1 / 2 : ℝ)) * (2 * L) * (1170 ^ 2 / L ^ (63 / 32 : ℝ)) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hc3_le hC_q.le) hL1_le
            (by positivity) (by positivity))
          hu2_le (sq_nonneg _) (by positivity)
    _ = (2 * 1170 ^ 2) * (C_q * (R + 1) ^ 2) * (L ^ (1 / 2 : ℝ) * L / L ^ (63 / 32 : ℝ)) := by ring
    _ ≤ (2 * 1170 ^ 2) * L ^ (2 / 64 : ℝ) * (L ^ (1 / 2 : ℝ) * L / L ^ (63 / 32 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCR_rpow (by norm_num)) (by positivity)
    _ = (2 * 1170 ^ 2) / L ^ (7 / 16 : ℝ) := by
        rw [show (2 * 1170 ^ 2 : ℝ) * L ^ (2 / 64 : ℝ) * (L ^ (1 / 2 : ℝ) * L / L ^ (63 / 32 : ℝ)) =
          (2 * 1170 ^ 2) * (L ^ (2 / 64 : ℝ) * L ^ (1 / 2 : ℝ) * L / L ^ (63 / 32 : ℝ)) by ring,
          ← Real.rpow_add hL0, ← Real.rpow_add_one hL0.ne', ← Real.rpow_sub hL0]
        have hexp : (2 / 64 + 1 / 2 + 1 - 63 / 32 : ℝ) = -(7 / 16) := by norm_num
        rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
    _ ≤ 1 := by
        rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
        exact (by norm_num : (2 * 1170 ^ 2 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans hL_7_16

private lemma full_quasimode_residual_bound_le_one {K_res R c L N_r q_r rn : ℝ}
    (hK_res : 0 < K_res) (hR : 0 < R) (hL1 : 1 ≤ L) (hN0 : 0 < N_r)
    (_hq0 : 0 ≤ q_r) (_hrn0 : 0 ≤ rn)
    (hL_3_16 : (4 : ℝ) ^ (18 : ℝ) ≤ L ^ (3 / 16 : ℝ))
    (hL_7_16 : (4 : ℝ) ^ (42 : ℝ) ≤ L ^ (7 / 16 : ℝ))
    (hc2_le : c ^ 2 ≤ (R + 1) * L ^ (1 / 4 : ℝ))
    (hq_le_4rpow : q_r ≤ 4 * L ^ (13 / 32 : ℝ))
    (hq_le_L : q_r ≤ L)
    (h1q_nn : 0 ≤ 1 + Real.log q_r) (h1q_64 : 1 + Real.log q_r ≤ 65 * L ^ (1 / 64 : ℝ))
    (h1c_nn : 0 ≤ 1 + Real.log c) (h1c_64 : 1 + Real.log c ≤ 65 * L ^ (1 / 64 : ℝ))
    (hKR_64 : K_res * (R + 1) ≤ L ^ (1 / 64 : ℝ))
    (hN_L4_split : 2 * K_res * (R + 1) ^ 5 * L ^ 4 + 32 * L ^ 4 ≤ N_r)
    (hr0' : rn ^ 2 ≤ K_res * (q_r * (1 + Real.log q_r) ^ 2) *
      (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L + c ^ 10 * (L / N_r) ^ 2)) :
    rn ≤ 1 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have ht1 : K_res * (q_r * (1 + Real.log q_r) ^ 2) *
      (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L) ≤ 1 / 2 := by
    have hp2 : (1 + Real.log q_r) ^ 2 ≤ 4225 * L ^ (1 / 32 : ℝ) := by
      have hp := pow_le_pow_left₀ h1q_nn h1q_64 2
      rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 64 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hp
      norm_num at hp; exact hp
    have hp3 : (1 + Real.log c) ^ 3 ≤ 274625 * L ^ (3 / 64 : ℝ) := by
      have hp := pow_le_pow_left₀ h1c_nn h1c_64 3
      rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 64 : ℝ)) 3, ← Real.rpow_mul hL0.le] at hp
      norm_num at hp; exact hp
    calc K_res * (q_r * (1 + Real.log q_r) ^ 2) *
          (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 16 : ℝ) / L)
        ≤ K_res * (4 * L ^ (13 / 32 : ℝ) * (4225 * L ^ (1 / 32 : ℝ))) *
          ((R + 1) * L ^ (1 / 4 : ℝ) * (274625 * L ^ (3 / 64 : ℝ)) * L ^ (1 / 16 : ℝ) / L) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left
              (mul_le_mul hq_le_4rpow hp2 (sq_nonneg _) (by positivity)) hK_res.le)
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul hc2_le hp3 (pow_nonneg h1c_nn 3) (by positivity))
                (by positivity)) hL0.le)
            (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg h1c_nn 3))
              (by positivity)) hL0.le)
            (by positivity)
      _ = (4 * 4225 * 274625) * (K_res * (R + 1)) *
          (L ^ (13 / 32 : ℝ) * L ^ (1 / 32 : ℝ) * L ^ (1 / 4 : ℝ) *
            L ^ (3 / 64 : ℝ) * L ^ (1 / 16 : ℝ) / L) := by ring
      _ ≤ (4 * 4225 * 274625) * L ^ (1 / 64 : ℝ) *
          (L ^ (13 / 32 : ℝ) * L ^ (1 / 32 : ℝ) * L ^ (1 / 4 : ℝ) *
            L ^ (3 / 64 : ℝ) * L ^ (1 / 16 : ℝ) / L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKR_64 (by norm_num))
            (by positivity)
      _ = (4 * 4225 * 274625) / L ^ (3 / 16 : ℝ) := by
          rw [show (4 * 4225 * 274625 : ℝ) * L ^ (1 / 64 : ℝ) *
              (L ^ (13 / 32 : ℝ) * L ^ (1 / 32 : ℝ) * L ^ (1 / 4 : ℝ) *
                L ^ (3 / 64 : ℝ) * L ^ (1 / 16 : ℝ) / L) =
            (4 * 4225 * 274625) * (L ^ (1 / 64 : ℝ) * L ^ (13 / 32 : ℝ) * L ^ (1 / 32 : ℝ) *
              L ^ (1 / 4 : ℝ) * L ^ (3 / 64 : ℝ) * L ^ (1 / 16 : ℝ) / L) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
            ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_sub_one hL0.ne']
          have hexp : (1 / 64 + 13 / 32 + 1 / 32 + 1 / 4 + 3 / 64 + 1 / 16 - 1 : ℝ) =
              -(3 / 16) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le]
          ring
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (Real.rpow_pos_of_pos hL0 _)]
          have hnum : (4 * 4225 * 274625 : ℝ) ≤ (1 / 2 : ℝ) * (4 : ℝ) ^ (18 : ℝ) := by norm_num
          linarith only [hnum, hL_3_16]
  have hK5L4_nn : 0 ≤ 2 * K_res * (R + 1) ^ 5 * L ^ 4 := by positivity
  have hL4_nn : 0 ≤ L ^ 4 := pow_nonneg hL0.le 4
  have ht2 : K_res * (q_r * (1 + Real.log q_r) ^ 2) * (c ^ 10 * (L / N_r) ^ 2) ≤ 1 / 2 := by
    have h1q_L : 1 + Real.log q_r ≤ L := by
      have h65_63 : (65 : ℝ) ≤ L ^ (63 / 64 : ℝ) :=
        (by norm_num : (65 : ℝ) ≤ (4 : ℝ) ^ (42 : ℝ)).trans
          (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
      have hm := mul_le_mul_of_nonneg_right h65_63 (Real.rpow_nonneg hL0.le (1 / 64 : ℝ))
      rw [← Real.rpow_add hL0, show (63 / 64 + 1 / 64 : ℝ) = 1 by norm_num, Real.rpow_one] at hm
      exact h1q_64.trans hm
    have hq_L3 : q_r * (1 + Real.log q_r) ^ 2 ≤ L ^ 3 := by
      have hp2 : (1 + Real.log q_r) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ h1q_nn h1q_L 2
      calc q_r * (1 + Real.log q_r) ^ 2 ≤ L * L ^ 2 :=
            mul_le_mul hq_le_L hp2 (sq_nonneg _) hL0.le
        _ = L ^ 3 := by ring
    have hc10 : c ^ 10 ≤ (R + 1) ^ 5 * L ^ 2 := by
      have hp5 : (c ^ 2) ^ 5 ≤ ((R + 1) * L ^ (1 / 4 : ℝ)) ^ 5 :=
        pow_le_pow_left₀ (sq_nonneg _) hc2_le 5
      rw [← pow_mul, mul_pow, ← Real.rpow_natCast (L ^ (1 / 4 : ℝ)) 5, ← Real.rpow_mul hL0.le] at hp5
      norm_num at hp5
      exact hp5.trans (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_natCast L 2))
        (by positivity))
    have hL4_N : L ^ 4 / N_r ≤ 1 / (2 * K_res * (R + 1) ^ 5) := by
      rw [div_le_div_iff₀ hN0 (by positivity)]
      linarith only [hN_L4_split, hL4_nn,
        (by ring : L ^ 4 * (2 * K_res * (R + 1) ^ 5) = 2 * K_res * (R + 1) ^ 5 * L ^ 4),
        (by ring : 1 * N_r = N_r)]
    have hL3_N : L ^ 3 / N_r ≤ 1 := by
      rw [div_le_one hN0]
      have h34 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by omega)
      linarith only [h34, hN_L4_split, hK5L4_nn, hL4_nn]
    calc K_res * (q_r * (1 + Real.log q_r) ^ 2) * (c ^ 10 * (L / N_r) ^ 2)
        ≤ K_res * L ^ 3 * ((R + 1) ^ 5 * L ^ 2 * (L ^ 2 / N_r ^ 2)) := by
          rw [div_pow]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hq_L3 hK_res.le)
            (mul_le_mul_of_nonneg_right hc10 (by positivity))
            (by positivity) (by positivity)
      _ = K_res * (R + 1) ^ 5 * (L ^ 4 / N_r) * (L ^ 3 / N_r) := by field_simp [hN0.ne']
      _ ≤ K_res * (R + 1) ^ 5 * (1 / (2 * K_res * (R + 1) ^ 5)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL4_N (by positivity)) hL3_N
            (by positivity) (by positivity)
      _ = 1 / 2 := by
          have hne : (R + 1) ^ 5 ≠ 0 := pow_ne_zero 5 (by linarith)
          field_simp [hK_res.ne', hne]
  have hrsq : rn ^ 2 ≤ 1 := by
    rw [mul_add] at hr0'
    linarith only [hr0', ht1, ht2]
  nlinarith only [hrsq, _hrn0]

/-- Full energy asymptotic `E(z_N) / log log N → 9 / 32` along `c_N⁸ / log N → R > 0`. -/
private theorem tendsto_quasimode_full_energy_div_log_log {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      completeWeilEnergy tiltedUnitSpline (c N) N (lowPacketOrthogonalPrimeQuasimode N) /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 (9 / 32 : ℝ)) := by
  obtain ⟨K_res, hK_res, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  obtain ⟨C_q, hC_q, hglob⟩ := exists_completeWeilMatrix_global_norm_cost
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htarget : Tendsto (fun N : ℕ =>
      (Real.log (primeAboveLowPacket N : ℝ) - Real.log (c N)) / Real.log (Real.log (N : ℝ)))
      atTop (𝓝 (9 / 32 : ℝ)) := by
    have hsub := tendsto_log_primeAboveLowPacket_div_log_log.sub
      (tendsto_log_c_div_log_log hR hc1 htend)
    rw [show (13 / 32 : ℝ) - 1 / 8 = 9 / 32 by norm_num] at hsub
    exact hsub.congr fun N => by ring
  have hN_fast : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 4 / (N : ℝ)) atTop (𝓝 0) :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).congr fun N => by dsimp only [Function.comp_def]; ring
  refine tendsto_div_log_log_of_abs_sub_le htarget
    (C := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 9) ?_
  filter_upwards [hc1,
    htend.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    hres (15 / 32) (by norm_num) 16 (by norm_num),
    hglob,
    norm_lowPacketProjection_primeAboveLowPacket_le,
    hN_fast.eventually (gt_mem_nhds (by
      positivity : (0 : ℝ) < 1 / (2 * (K_res * (R + 1) ^ 5 +
        4 * (Real.exp 1 + 3) ^ 2 * (R + 1) + 16)))),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 64) |>.comp hL).eventually_ge_atTop
      (4 + R + 1 + K_res * 8 * (R + 1) + C_q * (R + 1) +
        200 * (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 4) + 128),
    hL.eventually_ge_atTop (4 ^ (96 : ℝ) + 16),
    eventually_ge_atTop 16]
    with N hcN hrat_ub hresN hglobN hu_bd hNf hL_rpow hL_big hN16
  clear hc1 htend hres hglob hL htarget hN_fast
  dsimp only [Function.comp_def] at hrat_ub hNf hL_rpow
  change (4 : ℝ) ^ (96 : ℝ) + 16 ≤ Real.log (N : ℝ) at hL_big
  obtain ⟨hq_prime, hq_gt, hq_le⟩ := primeAboveLowPacket_spec N
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
  set q := primeAboveLowPacket N with hq_def
  set v := normalizedRamanujanHorizonVector q N with hv_def
  set u := (conductorSubspace (lowPacketCutoff N) N).starProjection v with hu_def
  set E_q := completedConductorEnergy tiltedUnitSpline (c N) q with hEq_def
  have hz_eq : lowPacketOrthogonalPrimeQuasimode N = v - u := rfl
  rw [hz_eq]
  have hv0_fn : q * q ≤ N → |‖v‖ ^ 2 - 1| ≤ (2 * Real.log (q : ℝ) + 9) / Real.log (N : ℝ) :=
    abs_norm_normalizedRamanujanHorizonVector_sq_sub_one_le hq_prime.two_le
  have hr0_fn : (q : ℝ) ≤ Real.log (N : ℝ) ^ (15 / 32 : ℝ) →
      4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ N →
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) v - E_q • v‖ ^ 2 ≤
        K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
          (c N ^ 2 * (1 + Real.log (c N)) ^ 3 * Real.log (N : ℝ) ^ (1 / (16 : ℝ)) /
              Real.log (N : ℝ) +
            c N ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
    intro hq15 hNw
    simpa only [Nat.cast_ofNat] using hresN q hq_prime.pos hq15 (c N) hcN hNw
  have hEq_f : E_q = completeWeilSelfFinitePart tiltedUnitSpline 1 + Real.log q +
      ArithmeticIntersectionTheory.tameDifferent q - Real.log (c N) -
      shellCorrection tiltedUnitSpline (c N) q := by
    rw [hEq_def, completedConductorEnergy_eq_sub_shellCorrection hc0 hq_prime.pos,
      completeWeilAdjunctionEnergy_eq_at_one_sub_log tiltedUnitSpline hq_prime.ne_one hc0]
    unfold completeWeilAdjunctionEnergy ramanujanAdjunctionEnergy
    rw [if_neg hq_prime.ne_one]
    ring
  set L := Real.log (N : ℝ) with hL_def
  have hlogq_le_fn : (q : ℝ) ≤ L → Real.log (q : ℝ) ≤ Real.log L :=
    Real.log_le_log (by exact_mod_cast hq_prime.pos)
  have hglobN_fn : c N ≤ L → ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      |completeWeilEnergy tiltedUnitSpline (c N) N x| ≤ C_q * c N ^ 3 * (L + 1) * ‖x‖ ^ 2 :=
    fun hcL => (hglobN hcN hcL).1
  have hQ1_fl : (lowPacketCutoff N : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
    rw [lowPacketCutoff, ← hL_def]
    exact Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  have hlt_fl : L ^ (13 / 32 : ℝ) < (lowPacketCutoff N : ℝ) + 1 := by
    rw [lowPacketCutoff, ← hL_def]
    exact Nat.lt_floor_add_one _
  clear hresN hglobN
  clear_value L q v u E_q
  have h4_le : (4 : ℝ) ^ (96 : ℝ) ≤ L := by linarith only [hL_big]
  have hL_gt1 : 1 < L := lt_of_lt_of_le (by norm_num : (1 : ℝ) < (4 : ℝ) ^ (96 : ℝ)) h4_le
  have hL1 : 1 ≤ L := hL_gt1.le
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc8_le : c N ^ 8 ≤ (R + 1) * L := ((div_lt_iff₀ hL0).mp hrat_ub).le
  have hL_7_16 : (4 : ℝ) ^ (42 : ℝ) ≤ L ^ (7 / 16 : ℝ) := by
    have hp := Real.rpow_le_rpow (by positivity) h4_le (by norm_num : (0 : ℝ) ≤ 7 / 16)
    rw [← Real.rpow_mul (by norm_num)] at hp
    exact hp.trans_eq' (by norm_num)
  have hL_3_16 : (4 : ℝ) ^ (18 : ℝ) ≤ L ^ (3 / 16 : ℝ) := by
    have hp := Real.rpow_le_rpow (by positivity) h4_le (by norm_num : (0 : ℝ) ≤ 3 / 16)
    rw [← Real.rpow_mul (by norm_num)] at hp
    exact hp.trans_eq' (by norm_num)
  have hc2_le : c N ^ 2 ≤ (R + 1) * L ^ (1 / 4 : ℝ) := by
    have hp4 : (c N ^ 2) ^ 4 ≤ ((R + 1) * L ^ (1 / 4 : ℝ)) ^ 4 := by
      rw [← pow_mul, mul_pow, ← Real.rpow_natCast (L ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hL0.le]
      norm_num
      exact hc8_le.trans (mul_le_mul_of_nonneg_right
        (le_self_pow₀ (by linarith) (by norm_num)) hL0.le)
    exact (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) (by norm_num)).mp hp4
  have hKR_nn : 0 ≤ K_res * 8 * (R + 1) := by positivity
  have hCR_nn : 0 ≤ C_q * (R + 1) := by positivity
  have hS0_nn : 0 ≤ |completeWeilSelfFinitePart tiltedUnitSpline 1| := abs_nonneg _
  have hR1_64 : R + 1 ≤ L ^ (1 / 64 : ℝ) := by
    linarith only [hL_rpow, hKR_nn, hCR_nn, hS0_nn]
  have hc_le_9 : c N ≤ L ^ (9 / 32 : ℝ) := by
    have hc2_9 : c N ^ 2 ≤ (L ^ (9 / 32 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (L ^ (9 / 32 : ℝ)) 2, ← Real.rpow_mul hL0.le]
      norm_num
      calc c N ^ 2 ≤ (R + 1) * L ^ (1 / 4 : ℝ) := hc2_le
        _ ≤ L ^ (1 / 64 : ℝ) * L ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hR1_64 (by positivity)
        _ = L ^ (17 / 64 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
        _ ≤ L ^ (9 / 16 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    exact (pow_le_pow_iff_left₀ hc0.le (by positivity) (by norm_num)).mp hc2_9
  have hc_le_L : c N ≤ L :=
    hc_le_9.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one _))
  have h2_le_rpow : (2 : ℝ) ≤ L ^ (13 / 32 : ℝ) :=
    (by norm_num : (2 : ℝ) ≤ (4 : ℝ) ^ 1).trans
      (four_pow_nat_le_rpow (e := 13 / 32) 1 h4_le (by norm_num) (by norm_num))
  have hq_le_4rpow : (q : ℝ) ≤ 4 * L ^ (13 / 32 : ℝ) := by
    have hmax : ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
      rw [Nat.cast_max, Nat.cast_ofNat]; exact max_le h2_le_rpow hQ1_fl
    have hqc : (q : ℝ) ≤ 2 * ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) := by exact_mod_cast hq_le
    linarith
  have hq_gt_rpow : L ^ (13 / 32 : ℝ) < (q : ℝ) := by
    have hq_ge : lowPacketCutoff N + 1 ≤ q := by
      have := (le_max_right 2 (lowPacketCutoff N)).trans_lt hq_gt; omega
    exact hlt_fl.trans_le (by exact_mod_cast hq_ge)
  have hq_le_15 : (q : ℝ) ≤ L ^ (15 / 32 : ℝ) := by
    have h4_16 : (4 : ℝ) ≤ L ^ (2 / 32 : ℝ) :=
      (by norm_num : (4 : ℝ) ≤ (4 : ℝ) ^ 1).trans
        (four_pow_nat_le_rpow (e := 2 / 32) 1 h4_le (by norm_num) (by norm_num))
    calc (q : ℝ) ≤ 4 * L ^ (13 / 32 : ℝ) := hq_le_4rpow
      _ ≤ L ^ (2 / 32 : ℝ) * L ^ (13 / 32 : ℝ) :=
          mul_le_mul_of_nonneg_right h4_16 (by positivity)
      _ = L ^ (15 / 32 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  have hq_le_L : (q : ℝ) ≤ L :=
    hq_le_15.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one _))
  have hlogL_64 : Real.log L ≤ 64 * L ^ (1 / 64 : ℝ) := by
    have hlg := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hL0 (1 / 64 : ℝ))
    rw [Real.log_rpow hL0] at hlg
    linarith [Real.rpow_nonneg hL0.le (1 / 64 : ℝ)]
  have h1_64 : 1 ≤ L ^ (1 / 64 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have h1q_64 : 1 + Real.log q ≤ 65 * L ^ (1 / 64 : ℝ) := by
    have hlq : Real.log (q : ℝ) ≤ Real.log L := hlogq_le_fn hq_le_L
    linarith only [hlq, hlogL_64, h1_64]
  have h1c_64 : 1 + Real.log (c N) ≤ 65 * L ^ (1 / 64 : ℝ) := by
    have hlc : Real.log (c N) ≤ Real.log L := Real.log_le_log hc0 hc_le_L
    linarith only [hlc, hlogL_64, h1_64]
  have hN_L4 : (2 * (K_res * (R + 1) ^ 5 + 4 * (Real.exp 1 + 3) ^ 2 * (R + 1) + 16)) * L ^ 4 ≤ N := by
    have hm := (div_lt_iff₀ hN0).mp hNf
    have hpos : 0 < 2 * (K_res * (R + 1) ^ 5 + 4 * (Real.exp 1 + 3) ^ 2 * (R + 1) + 16) :=
      by positivity
    exact ((le_div_iff₀ hpos).mp (by rw [one_div_mul_eq_div] at hm; exact hm.le)).trans_eq'
      (mul_comm _ _)
  have hN_L4_split : 2 * K_res * (R + 1) ^ 5 * L ^ 4 + 32 * L ^ 4 ≤ N := by
    have hrest0 : 0 ≤ 8 * (Real.exp 1 + 3) ^ 2 * (R + 1) * L ^ 4 := by positivity
    linarith only [hN_L4, hrest0,
      (by ring : (2 * (K_res * (R + 1) ^ 5 + 4 * (Real.exp 1 + 3) ^ 2 * (R + 1) + 16)) * L ^ 4 =
        2 * K_res * (R + 1) ^ 5 * L ^ 4 + 8 * (Real.exp 1 + 3) ^ 2 * (R + 1) * L ^ 4 + 32 * L ^ 4)]
  have hN_width : 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ N := by
    have hc2_L4 : c N ^ 2 ≤ (R + 1) * L ^ 4 :=
      hc2_le.trans (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_natCast L 4))
        (by linarith))
    have hprod := mul_le_mul_of_nonneg_left hc2_L4 (show 0 ≤ 4 * (Real.exp 1 + 3) ^ 2 by positivity)
    have hK0 : 0 ≤ K_res * (R + 1) ^ 5 * L ^ 4 := by positivity
    nlinarith only [hN_L4, hprod, hK0, pow_pos hL0 4]
  have hr_norm : ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) v - E_q • v‖ ≤ 1 := by
    have hKR_64 : K_res * (R + 1) ≤ L ^ (1 / 64 : ℝ) := by
      have hKR1_nn : 0 ≤ K_res * (R + 1) := by positivity
      have hKR_le8 : K_res * (R + 1) ≤ K_res * 8 * (R + 1) := by linarith only [hKR1_nn]
      linarith only [hL_rpow, hKR_le8, hR, hCR_nn, hS0_nn]
    exact full_quasimode_residual_bound_le_one hK_res hR hL1 hN0 (Nat.cast_nonneg q)
      (norm_nonneg _) hL_3_16 hL_7_16 hc2_le hq_le_4rpow hq_le_L
      (by linarith [Real.log_natCast_nonneg q]) h1q_64
      (by linarith [Real.log_nonneg hcN]) h1c_64 hKR_64 hN_L4_split (hr0_fn hq_le_15 hN_width)
  have hqqN : q * q ≤ N := by
    have hq2_L4 : ((q * q : ℕ) : ℝ) ≤ L ^ 4 := by
      rw [Nat.cast_mul]
      have h24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by omega)
      nlinarith only [hq_le_L, h24, Nat.cast_nonneg (α := ℝ) q]
    have hL4_le_N : L ^ 4 ≤ N := by
      have hK5L4_nn : 0 ≤ 2 * K_res * (R + 1) ^ 5 * L ^ 4 := by positivity
      have hL4_nn : 0 ≤ L ^ 4 := pow_nonneg hL0.le 4
      linarith only [hN_L4_split, hK5L4_nn, hL4_nn]
    exact_mod_cast hq2_L4.trans hL4_le_N
  have hv_rpow : |‖v‖ ^ 2 - 1| ≤ 137 / L ^ (63 / 64 : ℝ) := by
    have hv0 := hv0_fn hqqN
    have hnum : 2 * Real.log (q : ℝ) + 9 ≤ 137 * L ^ (1 / 64 : ℝ) := by
      linarith only [h1q_64, h1_64]
    calc |‖v‖ ^ 2 - 1| ≤ (2 * Real.log (q : ℝ) + 9) / L := hv0
      _ ≤ 137 * L ^ (1 / 64 : ℝ) / L := div_le_div_of_nonneg_right hnum hL0.le
      _ = 137 / L ^ (63 / 64 : ℝ) := by
          rw [mul_div_assoc, ← Real.rpow_sub_one hL0.ne']
          have hexp : (1 / 64 - 1 : ℝ) = -(63 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
  have hv_norm : ‖v‖ ≤ 2 := by
    have h137 : 137 / L ^ (63 / 64 : ℝ) ≤ 1 := by
      rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
      exact (by norm_num : (137 : ℝ) ≤ (4 : ℝ) ^ (42 : ℝ)).trans
        (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
    have := (abs_le.mp hv_rpow).2
    nlinarith only [this, h137, norm_nonneg v]
  have hsh_le : |shellCorrection tiltedUnitSpline (c N) q| ≤ 1 := by
    have hc_lt_q : c N < q :=
      hc_le_9.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hL_gt1 (by norm_num)).trans hq_gt_rpow)
    have h := abs_shellCorrection_prime_of_gt contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hcN hq_prime hc_lt_q
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq_prime.two_le
    have hq_half : (q : ℝ) / 2 ≤ (q : ℝ) - 1 := by linarith
    have hden : L ^ (13 / 32 : ℝ) / 2 ≤ (q : ℝ) - 1 := by linarith only [hq_gt_rpow, hq_half]
    calc |shellCorrection tiltedUnitSpline (c N) q|
        ≤ 2 * c N ^ 2 / ((q : ℝ) - 1) := h
      _ ≤ 2 * ((R + 1) * L ^ (1 / 4 : ℝ)) / (L ^ (13 / 32 : ℝ) / 2) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hc2_le zero_le_two)
            (by positivity) hden
      _ ≤ 2 * (L ^ (1 / 64 : ℝ) * L ^ (1 / 4 : ℝ)) / (L ^ (13 / 32 : ℝ) / 2) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR1_64 (by positivity)) zero_le_two)
            (by positivity)
      _ = 4 / L ^ (9 / 64 : ℝ) := by
          rw [show 2 * (L ^ (1 / 64 : ℝ) * L ^ (1 / 4 : ℝ)) / (L ^ (13 / 32 : ℝ) / 2) =
            4 * (L ^ (1 / 64 : ℝ) * L ^ (1 / 4 : ℝ) / L ^ (13 / 32 : ℝ)) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_sub hL0]
          have hexp : (1 / 64 + 1 / 4 - 13 / 32 : ℝ) = -(9 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          exact (by norm_num : (4 : ℝ) ≤ (4 : ℝ) ^ 1).trans
            (four_pow_nat_le_rpow (e := 9 / 64) 1 h4_le (by norm_num) (by norm_num))
  have hEq_sub : |E_q - (Real.log q - Real.log (c N))| ≤
      |completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 := by
    have htame := tameDifferent_prime_le_one hq_prime
    rw [show E_q - (Real.log q - Real.log (c N)) =
      completeWeilSelfFinitePart tiltedUnitSpline 1 +
        ArithmeticIntersectionTheory.tameDifferent q -
        shellCorrection tiltedUnitSpline (c N) q by rw [hEq_f]; ring]
    have t1 := abs_sub
      (completeWeilSelfFinitePart tiltedUnitSpline 1 + ArithmeticIntersectionTheory.tameDifferent q)
      (shellCorrection tiltedUnitSpline (c N) q)
    have t2 := abs_add_le
      (completeWeilSelfFinitePart tiltedUnitSpline 1)
      (ArithmeticIntersectionTheory.tameDifferent q)
    linarith only [t1, t2, htame, hsh_le]
  have hEq_rpow : |E_q| ≤ 2 * L ^ (2 / 64 : ℝ) := by
    have htri : |E_q| ≤ |E_q - (Real.log q - Real.log (c N))| + Real.log q + Real.log (c N) := by
      have a1 := abs_add_le (E_q - (Real.log q - Real.log (c N))) (Real.log q - Real.log (c N))
      rw [sub_add_cancel] at a1
      have a2 := abs_sub (Real.log (q : ℝ)) (Real.log (c N))
      rw [abs_of_nonneg (Real.log_natCast_nonneg q), abs_of_nonneg (Real.log_nonneg hcN)] at a2
      linarith only [a1, a2]
    have hS1 : |completeWeilSelfFinitePart tiltedUnitSpline 1| + 4 ≤ (1 / 200 : ℝ) * L ^ (1 / 64 : ℝ) := by
      linarith only [hL_rpow, hR, hKR_nn, hCR_nn]
    have hsum1 : |E_q| ≤ (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 4) * (130 * L ^ (1 / 64 : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left h1_64
        (show 0 ≤ |completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 by positivity)
      nlinarith only [htri, hEq_sub, h1q_64, h1c_64, hm, h1_64,
        abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1)]
    calc |E_q| ≤ ((1 / 200 : ℝ) * L ^ (1 / 64 : ℝ)) * (130 * L ^ (1 / 64 : ℝ)) :=
          hsum1.trans (mul_le_mul_of_nonneg_right hS1 (by positivity))
      _ ≤ 2 * (L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ)) := by
          rw [show ((1 / 200 : ℝ) * L ^ (1 / 64 : ℝ)) * (130 * L ^ (1 / 64 : ℝ)) =
            (13 / 20) * (L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ)) by ring]
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 2 * L ^ (2 / 64 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  have hEq_vsq : |E_q * (‖v‖ ^ 2 - 1)| ≤ 1 := by
    rw [abs_mul]
    calc |E_q| * |‖v‖ ^ 2 - 1|
        ≤ (2 * L ^ (2 / 64 : ℝ)) * (137 / L ^ (63 / 64 : ℝ)) :=
          mul_le_mul hEq_rpow hv_rpow (abs_nonneg _) (by positivity)
      _ = 274 / L ^ (61 / 64 : ℝ) := by
          rw [show 2 * L ^ (2 / 64 : ℝ) * (137 / L ^ (63 / 64 : ℝ)) =
            274 * (L ^ (2 / 64 : ℝ) / L ^ (63 / 64 : ℝ)) by ring, ← Real.rpow_sub hL0]
          have hexp : (2 / 64 - 63 / 64 : ℝ) = -(61 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          exact (by norm_num : (274 : ℝ) ≤ (4 : ℝ) ^ (42 : ℝ)).trans
            (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
  have hu_rpow : ‖u‖ ≤ 1170 / L ^ (63 / 64 : ℝ) := by
    calc ‖u‖ ≤ 18 * (1 + Real.log q) / L := hu_bd
      _ ≤ 18 * (65 * L ^ (1 / 64 : ℝ)) / L :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1q_64 (by norm_num)) hL0.le
      _ = 1170 / L ^ (63 / 64 : ℝ) := by
          rw [show 18 * (65 * L ^ (1 / 64 : ℝ)) / L = 1170 * (L ^ (1 / 64 : ℝ) / L) by ring,
            ← Real.rpow_sub_one hL0.ne']
          have hexp : (1 / 64 - 1 : ℝ) = -(63 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
  have hu_norm : ‖u‖ ≤ 1 / 2 := by
    refine hu_rpow.trans ?_
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hL0 _)]
    have hnum : (1170 : ℝ) ≤ (1 / 2 : ℝ) * (4 : ℝ) ^ (42 : ℝ) := by norm_num
    have h7 : L ^ (7 / 16 : ℝ) ≤ L ^ (63 / 64 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    nlinarith only [hnum, hL_7_16, h7]
  have hEq_u : |E_q| * ‖u‖ ≤ 1 / 4 := by
    calc |E_q| * ‖u‖
        ≤ (2 * L ^ (2 / 64 : ℝ)) * (1170 / L ^ (63 / 64 : ℝ)) :=
          mul_le_mul hEq_rpow hu_rpow (norm_nonneg _) (by positivity)
      _ = 2340 / L ^ (61 / 64 : ℝ) := by
          rw [show 2 * L ^ (2 / 64 : ℝ) * (1170 / L ^ (63 / 64 : ℝ)) =
            2340 * (L ^ (2 / 64 : ℝ) / L ^ (63 / 64 : ℝ)) by ring, ← Real.rpow_sub hL0]
          have hexp : (2 / 64 - 63 / 64 : ℝ) = -(61 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      _ ≤ 1 / 4 := by
          rw [div_le_iff₀ (Real.rpow_pos_of_pos hL0 _)]
          have hnum : (2340 : ℝ) ≤ (1 / 4 : ℝ) * (4 : ℝ) ^ (42 : ℝ) := by norm_num
          have h7 : L ^ (7 / 16 : ℝ) ≤ L ^ (61 / 64 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
          nlinarith only [hnum, hL_7_16, h7]
  have hEu_abs : |completeWeilEnergy tiltedUnitSpline (c N) N u| ≤ 1 :=
    global_low_packet_energy_bound_le_one hC_q hR hcN hL1 (norm_nonneg u)
      ((by norm_num : (4 : ℝ) ^ (14 : ℝ) ≤ (4 : ℝ) ^ (42 : ℝ)).trans hL_7_16)
      hc2_le hR1_64 (by linarith only [hL_rpow, hR, hKR_nn, hS0_nn]) hu_rpow (hglobN_fn hc_le_L u)
  have hmain := abs_quasimode_energy_sub_le hr_norm hv_norm hEq_sub hEq_vsq hEq_u hu_norm hEu_abs
  linarith only [hmain]

private theorem abs_prefix_quasimode_energy_sub_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) {M N : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N)
    {p_z p_v p_u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    {v' : EuclideanSpace ℝ (PrimeHorizonIndex M)}
    {α E1_q L_target C_E C_sep : ℝ} (hC_sep : 0 ≤ C_sep)
    (hp_sub : p_z = p_v - p_u)
    (hvan_pv : ∀ n, M < n → primeHorizonExtension p_v n = 0)
    (hvan_pu : ∀ n, M < n → primeHorizonExtension p_u n = 0)
    (hpv_eq : horizonProfileVector (primeHorizonExtension p_v) M = α • v')
    (hα_nn : 0 ≤ α) (hα_le1 : α ≤ 1)
    (hrc'_norm : ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c * (M : ℝ) / N) M) v' - E1_q • v'‖ ≤
      C_sep + 1)
    (hv'_norm : ‖v'‖ ≤ 2)
    (hE1_sub : |E1_q - L_target| ≤ C_E)
    (hα_sub1 : |(α ^ 2 - 1) * E1_q| ≤ 1)
    (hE1_v'_sq : |α ^ 2 * (E1_q * (‖v'‖ ^ 2 - 1))| ≤ 1)
    (hBv'_u : 2 * ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c * (M : ℝ) / N) M) v'‖ *
      ‖horizonProfileVector (primeHorizonExtension p_u) M‖ ≤ 2)
    (hEpu_abs : |completeWeilEnergy φ c N p_u| ≤ 1) :
    |completeWeilEnergy φ c N p_z - L_target| ≤ C_E + 2 * C_sep + 7 := by
  let c' := c * (M : ℝ) / N
  let rc' := Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' - E1_q • v'
  let p'_u := horizonProfileVector (primeHorizonExtension p_u) M
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  have hpz_exp : completeWeilEnergy φ c N p_z =
      completeWeilEnergy φ c N p_v -
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p_v, p_u⟫ +
        completeWeilEnergy φ c N p_u := by
    rw [hp_sub]
    unfold completeWeilEnergy
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym p_u p_v, real_inner_comm p_u]
    ring
  have hpv_red : completeWeilEnergy φ c N p_v = α ^ 2 * completeWeilEnergy φ c' M v' := by
    rw [completeWeilEnergy_eq_of_vanish_above hφ hsupp hM_int hc0 hM1 hMN p_v hvan_pv, hpv_eq]
    unfold completeWeilEnergy
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  have hpvu_red : ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p_v, p_u⟫ =
      α * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v', p'_u⟫ := by
    rw [completeWeilMatrix_inner_eq_of_vanish_above hφ hsupp hM_int hc0 hM1 hMN p_v p_u
      hvan_pv hvan_pu, hpv_eq, map_smul, real_inner_smul_left]
  have hv'_exp : completeWeilEnergy φ c' M v' = E1_q * ‖v'‖ ^ 2 + ⟪rc', v'⟫ := by
    have hBv' : Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' = E1_q • v' + rc' := by
      dsimp only [rc']; abel
    unfold completeWeilEnergy
    rw [hBv', inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hrc'_v : |α ^ 2 * ⟪rc', v'⟫| ≤ 2 * C_sep + 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg α)]
    have hα2_1 : α ^ 2 ≤ 1 := by nlinarith only [hα_nn, hα_le1]
    have h1 : |⟪rc', v'⟫| ≤ 2 * (C_sep + 1) :=
      (abs_real_inner_le_norm rc' v').trans
        (by nlinarith only [hrc'_norm, hv'_norm, norm_nonneg rc', norm_nonneg v'])
    nlinarith only [hα2_1, h1, sq_nonneg α, hC_sep]
  have hBpvu_abs : |2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p_v, p_u⟫| ≤ 2 := by
    rw [hpvu_red, ← mul_assoc, abs_mul, abs_mul, abs_two, abs_of_nonneg hα_nn]
    calc 2 * α * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v', p'_u⟫|
        ≤ 2 * 1 * (‖Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v'‖ * ‖p'_u‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hα_le1 zero_le_two)
            (abs_real_inner_le_norm _ _) (abs_nonneg _) (by norm_num)
      _ ≤ 2 := by linarith only [hBv'_u]
  have hsplit : completeWeilEnergy φ c N p_z - L_target =
      (E1_q - L_target) + (α ^ 2 - 1) * E1_q + α ^ 2 * (E1_q * (‖v'‖ ^ 2 - 1)) +
        α ^ 2 * ⟪rc', v'⟫ -
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p_v, p_u⟫ +
        completeWeilEnergy φ c N p_u := by
    rw [hpz_exp, hpv_red, hv'_exp]
    ring
  rw [hsplit]
  have a1 := abs_add_le
    ((E1_q - L_target) + (α ^ 2 - 1) * E1_q + α ^ 2 * (E1_q * (‖v'‖ ^ 2 - 1)) +
      α ^ 2 * ⟪rc', v'⟫ -
      2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p_v, p_u⟫)
    (completeWeilEnergy φ c N p_u)
  have a2 := abs_sub
    ((E1_q - L_target) + (α ^ 2 - 1) * E1_q + α ^ 2 * (E1_q * (‖v'‖ ^ 2 - 1)) +
      α ^ 2 * ⟪rc', v'⟫)
    (2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p_v, p_u⟫)
  have a3 := abs_add_le
    ((E1_q - L_target) + (α ^ 2 - 1) * E1_q + α ^ 2 * (E1_q * (‖v'‖ ^ 2 - 1)))
    (α ^ 2 * ⟪rc', v'⟫)
  have a4 := abs_add_le
    ((E1_q - L_target) + (α ^ 2 - 1) * E1_q)
    (α ^ 2 * (E1_q * (‖v'‖ ^ 2 - 1)))
  linarith only [a1, a2, a3, a4, abs_add_le (E1_q - L_target) ((α ^ 2 - 1) * E1_q),
    hE1_sub, hα_sub1, hE1_v'_sq, hrc'_v, hBpvu_abs, hEpu_abs]

private lemma prefix_quasimode_unit_residual_le_one {K_res L L_M M_real r1_norm : ℝ} {q : ℕ}
    (hK_res : 0 < K_res) (hL0 : 0 < L) (hLM1 : 1 ≤ L_M) (hM0 : 0 < M_real)
    (_hr1_nn : 0 ≤ r1_norm)
    (hLM_31 : (4 : ℝ) ^ (31 : ℝ) ≤ L_M)
    (hLM_ge_half : L / 2 ≤ L_M)
    (hLM_le_L : L_M ≤ L)
    (hKL1 : K_res ≤ L ^ (1 / 64 : ℝ))
    (hq_le_LM_half : (q : ℝ) ≤ L_M ^ (1 / 2 : ℝ))
    (hq_le_LM : (q : ℝ) ≤ L_M)
    (hlogq_LM : 1 + Real.log q ≤ 65 * L_M ^ (1 / 64 : ℝ))
    (hM_ge_2K : 2 * K_res * L ^ 3 ≤ M_real)
    (hM_ge_L3_1 : L ^ 3 ≤ M_real)
    (hr0' : r1_norm ^ 2 ≤ K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
      ((1 : ℝ) ^ 2 * (1 + Real.log (1 : ℝ)) ^ 3 * L_M ^ (1 / (16 : ℝ)) / L_M +
        (1 : ℝ) ^ 10 * (L_M / M_real) ^ 2)) :
    r1_norm ≤ 1 := by
  have hLM0 : 0 < L_M := zero_lt_one.trans_le hLM1
  have hK_LM : K_res ≤ 2 * L_M ^ (1 / 64 : ℝ) := by
    have hp := Real.rpow_le_rpow hL0.le (show L ≤ 2 * L_M by linarith only [hLM_ge_half])
      (by norm_num : (0 : ℝ) ≤ 1 / 64)
    rw [Real.mul_rpow zero_le_two hLM0.le] at hp
    have h2_64 : (2 : ℝ) ^ (1 / 64 : ℝ) ≤ 2 :=
      (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)).trans_eq (Real.rpow_one 2)
    exact hKL1.trans (hp.trans (mul_le_mul_of_nonneg_right h2_64 (by positivity)))
  have hLM_25 : (4 : ℝ) ^ 12 ≤ L_M ^ (25 / 64 : ℝ) :=
    four_pow_nat_le_rpow (e := 25 / 64) 12 hLM_31 (by norm_num) (by norm_num)
  have ht1 : K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
      ((1 : ℝ) ^ 2 * (1 + Real.log (1 : ℝ)) ^ 3 * L_M ^ (1 / (16 : ℝ)) / L_M) ≤ 1 / 2 := by
    rw [Real.log_one]
    have h1q_nn : 0 ≤ 1 + Real.log (q : ℝ) := by linarith [Real.log_natCast_nonneg q]
    have hp2 : (1 + Real.log q) ^ 2 ≤ 4225 * L_M ^ (1 / 32 : ℝ) := by
      have hp := pow_le_pow_left₀ h1q_nn hlogq_LM 2
      rw [mul_pow, ← Real.rpow_natCast (L_M ^ (1 / 64 : ℝ)) 2, ← Real.rpow_mul hLM0.le] at hp
      norm_num at hp; exact hp
    calc K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
          ((1 : ℝ) ^ 2 * (1 + 0) ^ 3 * L_M ^ (1 / 16 : ℝ) / L_M)
        ≤ (2 * L_M ^ (1 / 64 : ℝ)) * (L_M ^ (1 / 2 : ℝ) * (4225 * L_M ^ (1 / 32 : ℝ))) *
          (L_M ^ (1 / 16 : ℝ) / L_M) :=
          mul_le_mul
            (mul_le_mul hK_LM (mul_le_mul hq_le_LM_half hp2 (sq_nonneg _) (by positivity))
              (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (by positivity))
            (le_of_eq (by ring)) (by positivity) (by positivity)
      _ = (2 * 4225) *
          (L_M ^ (1 / 64 : ℝ) * L_M ^ (1 / 2 : ℝ) * L_M ^ (1 / 32 : ℝ) *
            L_M ^ (1 / 16 : ℝ) / L_M) := by ring
      _ = (2 * 4225) / L_M ^ (25 / 64 : ℝ) := by
          rw [← Real.rpow_add hLM0, ← Real.rpow_add hLM0, ← Real.rpow_add hLM0,
            ← Real.rpow_sub_one hLM0.ne']
          have hexp : (1 / 64 + 1 / 2 + 1 / 32 + 1 / 16 - 1 : ℝ) = -(25 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hLM0.le]
          ring
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (Real.rpow_pos_of_pos hLM0 _)]
          have hnum : (2 * 4225 : ℝ) ≤ (1 / 2 : ℝ) * (4 : ℝ) ^ 12 := by norm_num
          linarith only [hnum, hLM_25]
  have ht2 : K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) * ((1 : ℝ) ^ 10 * (L_M / M_real) ^ 2) ≤ 1 / 2 := by
    have hq_log_LM3 : (q : ℝ) * (1 + Real.log q) ^ 2 ≤ L_M ^ 3 := by
      have hlq_LM1 : 1 + Real.log q ≤ L_M := by
        have h65_LM : 65 * L_M ^ (1 / 64 : ℝ) ≤ L_M := by
          have h65 : (65 : ℝ) ≤ L_M ^ (63 / 64 : ℝ) :=
            (by norm_num : (65 : ℝ) ≤ (4 : ℝ) ^ 12).trans
              (hLM_25.trans (Real.rpow_le_rpow_of_exponent_le hLM1 (by norm_num)))
          have hm := mul_le_mul_of_nonneg_right h65 (Real.rpow_nonneg hLM0.le (1 / 64 : ℝ))
          rwa [← Real.rpow_add hLM0, show (63 / 64 + 1 / 64 : ℝ) = 1 by norm_num, Real.rpow_one] at hm
        exact hlogq_LM.trans h65_LM
      have hp2 : (1 + Real.log q) ^ 2 ≤ L_M ^ 2 :=
        pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg q]) hlq_LM1 2
      calc (q : ℝ) * (1 + Real.log q) ^ 2 ≤ L_M * L_M ^ 2 :=
            mul_le_mul hq_le_LM hp2 (by positivity) hLM0.le
        _ = L_M ^ 3 := by ring
    have hLM_M_le : L_M ^ 3 / M_real ≤ 1 / (2 * K_res) := by
      rw [div_le_div_iff₀ hM0 (by positivity)]
      have hLM3_L3 : L_M ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hLM0.le hLM_le_L 3
      have hm := mul_le_mul_of_nonneg_left hLM3_L3 (show 0 ≤ 2 * K_res by positivity)
      linarith only [hm, hM_ge_2K, (by ring : L_M ^ 3 * (2 * K_res) = 2 * K_res * L_M ^ 3),
        (by ring : 1 * M_real = M_real)]
    have hLM2_M : L_M ^ 2 / M_real ≤ 1 := by
      have h23 : L_M ^ 2 ≤ L_M ^ 3 := pow_le_pow_right₀ hLM1 (by omega)
      rw [div_le_one hM0]
      exact h23.trans ((pow_le_pow_left₀ hLM0.le hLM_le_L 3).trans hM_ge_L3_1)
    calc K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) * ((1 : ℝ) ^ 10 * (L_M / M_real) ^ 2)
        ≤ K_res * L_M ^ 3 * (L_M ^ 2 / M_real ^ 2) := by
          rw [one_pow, one_mul, div_pow]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq_log_LM3 hK_res.le)
            (by positivity)
      _ = K_res * (L_M ^ 3 / M_real) * (L_M ^ 2 / M_real) := by field_simp [hM0.ne']
      _ ≤ K_res * (1 / (2 * K_res)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hLM_M_le hK_res.le) hLM2_M
            (by positivity) (by positivity)
      _ = 1 / 2 := by field_simp [hK_res.ne']
  have hr1_sq : r1_norm ^ 2 ≤ 1 := by
    rw [mul_add] at hr0'
    linarith only [hr0', ht1, ht2]
  nlinarith only [hr1_sq, _hr1_nn]

private lemma prefix_quasimode_scalar_closing_bounds
    {L L_M q_r v'_norm E1_q α u_norm p'u_norm Bv'_norm C_sep S1_abs : ℝ}
    (hL1 : 1 ≤ L) (hLM1 : 1 ≤ L_M) (hq1 : 1 ≤ q_r)
    (_hv'0 : 0 ≤ v'_norm) (_hp'u0 : 0 ≤ p'u_norm)
    (hα_nn : 0 ≤ α) (hα_le1 : α ≤ 1) (hα_sq : α ^ 2 = L_M / L)
    (hLM_31 : (4 : ℝ) ^ (31 : ℝ) ≤ L_M)
    (hLM_ge_half : L / 2 ≤ L_M) (hLM_le_L : L_M ≤ L)
    (hL_7_16 : (4 : ℝ) ^ (14 : ℝ) ≤ L ^ (7 / 16 : ℝ))
    (hlogL_64 : Real.log L ≤ 64 * L ^ (1 / 64 : ℝ))
    (hq_le_LM : q_r ≤ L_M)
    (hlogq_LM : 1 + Real.log q_r ≤ 65 * L_M ^ (1 / 64 : ℝ))
    (hLM_diff : L - L_M ≤ 65 * L ^ (1 / 64 : ℝ))
    (hS1_64 : S1_abs + 4 ≤ (1 / 72 : ℝ) * L ^ (1 / 64 : ℝ))
    (hCs_64 : C_sep + 1 ≤ L ^ (1 / 64 : ℝ))
    (hv0 : |v'_norm ^ 2 - 1| ≤ (2 * Real.log q_r + 9) / L_M)
    (hE1_sub : |E1_q - Real.log q_r| ≤ S1_abs + 3)
    (hu_bd : u_norm ≤ 18 * (1 + Real.log q_r) / L)
    (hp'u_le : p'u_norm ≤ u_norm)
    (hBv'_le : Bv'_norm ≤ |E1_q| * v'_norm + (C_sep + 1)) :
    v'_norm ≤ 2 ∧
      |α ^ 2 * (E1_q * (v'_norm ^ 2 - 1))| ≤ 1 ∧
      |(α ^ 2 - 1) * E1_q| ≤ 1 ∧
      u_norm ≤ 1170 / L ^ (63 / 64 : ℝ) ∧
      2 * Bv'_norm * p'u_norm ≤ 2 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLM0 : 0 < L_M := zero_lt_one.trans_le hLM1
  have hq0 : 0 < q_r := zero_lt_one.trans_le hq1
  have hv'_rpow : |v'_norm ^ 2 - 1| ≤ 8 / L_M ^ (1 / 2 : ℝ) := by
    have h1_64 : 1 ≤ L_M ^ (1 / 64 : ℝ) := Real.one_le_rpow hLM1 (by norm_num)
    have hnum1 : 2 * Real.log q_r + 9 ≤ 137 * L_M ^ (1 / 64 : ℝ) := by
      linarith only [hlogq_LM, h1_64]
    have h137_8 : 137 * L_M ^ (1 / 64 : ℝ) ≤ 8 * L_M ^ (1 / 2 : ℝ) := by
      have h137 : (137 / 8 : ℝ) ≤ L_M ^ (31 / 64 : ℝ) :=
        (by norm_num : (137 / 8 : ℝ) ≤ (4 : ℝ) ^ 3).trans
          (four_pow_nat_le_rpow (e := 31 / 64) 3 hLM_31 (by norm_num) (by norm_num))
      have hm := mul_le_mul_of_nonneg_right h137 (Real.rpow_nonneg hLM0.le (1 / 64 : ℝ))
      rw [← Real.rpow_add hLM0] at hm; norm_num at hm
      linarith only [hm]
    calc |v'_norm ^ 2 - 1| ≤ (2 * Real.log q_r + 9) / L_M := hv0
      _ ≤ 8 * L_M ^ (1 / 2 : ℝ) / L_M :=
          div_le_div_of_nonneg_right (hnum1.trans h137_8) hLM0.le
      _ = 8 / L_M ^ (1 / 2 : ℝ) := by
          rw [mul_div_assoc, ← Real.rpow_sub_one hLM0.ne']
          have hexp : (1 / 2 - 1 : ℝ) = -(1 / 2) := by norm_num
          rw [hexp, Real.rpow_neg hLM0.le, ← div_eq_mul_inv]
  have hv'_norm_le2 : v'_norm ≤ 2 := by
    have h8q : 8 / L_M ^ (1 / 2 : ℝ) ≤ 1 := by
      rw [div_le_one (Real.rpow_pos_of_pos hLM0 _)]
      exact (by norm_num : (8 : ℝ) ≤ (4 : ℝ) ^ 2).trans
        (four_pow_nat_le_rpow (e := 1 / 2) 2 hLM_31 (by norm_num) (by norm_num))
    have := (abs_le.mp hv'_rpow).2
    nlinarith only [this, h8q, _hv'0]
  have hE1_rpow : |E1_q| ≤ 2 * L ^ (2 / 64 : ℝ) := by
    have htri : |E1_q| ≤ |E1_q - Real.log q_r| + Real.log q_r := by
      have := abs_add_le (E1_q - Real.log q_r) (Real.log q_r)
      rwa [sub_add_cancel, abs_of_nonneg (Real.log_nonneg hq1)] at this
    have hlq_64 : Real.log q_r ≤ 64 * L ^ (1 / 64 : ℝ) :=
      (Real.log_le_log hq0 (hq_le_LM.trans hLM_le_L)).trans hlogL_64
    have h1_64 : 1 ≤ L ^ (1 / 64 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have hS1_nn : 0 ≤ S1_abs + 3 := by
      linarith only [abs_nonneg (E1_q - Real.log q_r), hE1_sub]
    calc |E1_q| ≤ (S1_abs + 4) * (65 * L ^ (1 / 64 : ℝ)) := by
          have := mul_le_mul_of_nonneg_left h1_64 hS1_nn
          nlinarith only [htri, hE1_sub, hlq_64, this, h1_64, hS1_nn]
      _ ≤ ((1 / 72 : ℝ) * L ^ (1 / 64 : ℝ)) * (65 * L ^ (1 / 64 : ℝ)) :=
          mul_le_mul_of_nonneg_right hS1_64 (by positivity)
      _ ≤ 2 * (L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ)) := by
          rw [show ((1 / 72 : ℝ) * L ^ (1 / 64 : ℝ)) * (65 * L ^ (1 / 64 : ℝ)) =
            (65 / 72) * (L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ)) by ring]
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 2 * L ^ (2 / 64 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  have hE1_v'_sq : |α ^ 2 * (E1_q * (v'_norm ^ 2 - 1))| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg α), abs_mul]
    have hα2_1 : α ^ 2 ≤ 1 := by nlinarith only [hα_nn, hα_le1]
    have hLM_half_L : L ^ (1 / 2 : ℝ) / 2 ≤ L_M ^ (1 / 2 : ℝ) := by
      have hp := Real.rpow_le_rpow (by positivity) hLM_ge_half (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [Real.div_rpow hL0.le zero_le_two] at hp
      have h2_half : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 :=
        (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)).trans_eq (Real.rpow_one 2)
      exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hL0.le _)
        (Real.rpow_pos_of_pos zero_lt_two _) h2_half).trans hp
    have hv'_L : |v'_norm ^ 2 - 1| ≤ 16 / L ^ (1 / 2 : ℝ) :=
      hv'_rpow.trans ((div_le_div_of_nonneg_left (by norm_num)
        (div_pos (Real.rpow_pos_of_pos hL0 _) zero_lt_two) hLM_half_L).trans_eq (by ring))
    have hprod : |E1_q| * |v'_norm ^ 2 - 1| ≤ 1 := by
      calc |E1_q| * |v'_norm ^ 2 - 1|
          ≤ (2 * L ^ (2 / 64 : ℝ)) * (16 / L ^ (1 / 2 : ℝ)) :=
            mul_le_mul hE1_rpow hv'_L (abs_nonneg _) (by positivity)
        _ = 32 / L ^ (15 / 32 : ℝ) := by
            rw [show 2 * L ^ (2 / 64 : ℝ) * (16 / L ^ (1 / 2 : ℝ)) =
              32 * (L ^ (2 / 64 : ℝ) / L ^ (1 / 2 : ℝ)) by ring, ← Real.rpow_sub hL0]
            have hexp : (2 / 64 - 1 / 2 : ℝ) = -(15 / 32) := by norm_num
            rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
        _ ≤ 1 := by
            rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
            exact (by norm_num : (32 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans
              (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
    nlinarith only [hα2_1, hprod, sq_nonneg α,
      mul_nonneg (abs_nonneg E1_q) (abs_nonneg (v'_norm ^ 2 - 1))]
  have hα_sub1 : |(α ^ 2 - 1) * E1_q| ≤ 1 := by
    rw [abs_mul, hα_sq]
    have hdiff_le : |L_M / L - 1| ≤ 65 / L ^ (63 / 64 : ℝ) := by
      have hle0 : L_M / L - 1 ≤ 0 := by have := (div_le_one hL0).mpr hLM_le_L; linarith
      rw [abs_of_nonpos hle0]
      have hge : 1 - L_M / L ≤ 65 * L ^ (1 / 64 : ℝ) / L := by
        rw [show 1 - L_M / L = (L - L_M) / L by field_simp [hL0.ne']]
        exact div_le_div_of_nonneg_right hLM_diff hL0.le
      refine (by linarith only [hge] : -(L_M / L - 1) ≤ 65 * L ^ (1 / 64 : ℝ) / L).trans_eq ?_
      rw [mul_div_assoc, ← Real.rpow_sub_one hL0.ne']
      have hexp : (1 / 64 - 1 : ℝ) = -(63 / 64) := by norm_num
      rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
    calc |L_M / L - 1| * |E1_q|
        ≤ (65 / L ^ (63 / 64 : ℝ)) * (2 * L ^ (2 / 64 : ℝ)) :=
          mul_le_mul hdiff_le hE1_rpow (abs_nonneg _) (by positivity)
      _ = 130 / L ^ (61 / 64 : ℝ) := by
          rw [show (65 / L ^ (63 / 64 : ℝ)) * (2 * L ^ (2 / 64 : ℝ)) =
            130 * (L ^ (2 / 64 : ℝ) / L ^ (63 / 64 : ℝ)) by ring, ← Real.rpow_sub hL0]
          have hexp : (2 / 64 - 63 / 64 : ℝ) = -(61 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          exact (by norm_num : (130 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans
            (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
  have hu_rpow : u_norm ≤ 1170 / L ^ (63 / 64 : ℝ) := by
    have h1q : 1 + Real.log q_r ≤ 65 * L ^ (1 / 64 : ℝ) := by
      have hlq : Real.log q_r ≤ Real.log L :=
        Real.log_le_log hq0 (hq_le_LM.trans hLM_le_L)
      have h1_64 : 1 ≤ L ^ (1 / 64 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith only [hlq, hlogL_64, h1_64]
    calc u_norm ≤ 18 * (1 + Real.log q_r) / L := hu_bd
      _ ≤ 18 * (65 * L ^ (1 / 64 : ℝ)) / L :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1q (by norm_num)) hL0.le
      _ = 1170 / L ^ (63 / 64 : ℝ) := by
          rw [show 18 * (65 * L ^ (1 / 64 : ℝ)) / L = 1170 * (L ^ (1 / 64 : ℝ) / L) by ring,
            ← Real.rpow_sub_one hL0.ne']
          have hexp : (1 / 64 - 1 : ℝ) = -(63 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
  have hBv'_u : 2 * Bv'_norm * p'u_norm ≤ 2 := by
    have hBv'_norm : Bv'_norm ≤ 6 * L ^ (2 / 64 : ℝ) := by
      have h1 : |E1_q| * v'_norm ≤ 4 * L ^ (2 / 64 : ℝ) := by
        calc |E1_q| * v'_norm ≤ (2 * L ^ (2 / 64 : ℝ)) * 2 :=
              mul_le_mul hE1_rpow hv'_norm_le2 _hv'0 (by positivity)
          _ = 4 * L ^ (2 / 64 : ℝ) := by ring
      have h2 : C_sep + 1 ≤ 2 * L ^ (2 / 64 : ℝ) := by
        have h12 : L ^ (1 / 64 : ℝ) ≤ L ^ (2 / 64 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        linarith [Real.rpow_nonneg hL0.le (2 / 64 : ℝ)]
      linarith only [hBv'_le, h1, h2]
    calc 2 * Bv'_norm * p'u_norm
        ≤ 2 * (6 * L ^ (2 / 64 : ℝ)) * (1170 / L ^ (63 / 64 : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hBv'_norm zero_le_two)
            (hp'u_le.trans hu_rpow) _hp'u0 (by positivity)
      _ = 14040 / L ^ (61 / 64 : ℝ) := by
          rw [show 2 * (6 * L ^ (2 / 64 : ℝ)) * (1170 / L ^ (63 / 64 : ℝ)) =
            14040 * (L ^ (2 / 64 : ℝ) / L ^ (63 / 64 : ℝ)) by ring, ← Real.rpow_sub hL0]
          have hexp : (2 / 64 - 63 / 64 : ℝ) = -(61 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      _ ≤ 2 := by
          have h1 : 14040 / L ^ (61 / 64 : ℝ) ≤ 1 := by
            rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
            exact (by norm_num : (14040 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans
              (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
          linarith
  exact ⟨hv'_norm_le2, hE1_v'_sq, hα_sub1, hu_rpow, hBv'_u⟩

/-- Prefix energy asymptotic `E(p_N) / log log N → 13 / 32` along `c_N⁸ / log N → R > 0`. -/
private theorem tendsto_quasimode_prefix_energy_div_log_log {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      completeWeilEnergy tiltedUnitSpline (c N) N
        (horizonPrefixVector (N / linearDefectCutoff (c N)) (lowPacketOrthogonalPrimeQuasimode N)) /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 (13 / 32 : ℝ)) := by
  let φ := tiltedUnitSpline
  have hφ : ContDiff ℝ 2 φ := contDiff_tiltedUnitSpline
  have hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0 := tiltedUnitSpline_eq_zero
  have hM_int : 0 < ∫ u, φ u ^ 2 := integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_sep, hC_sep, hsep_ev⟩ := exists_prime_mode_separated_sub_one_norm_le
  obtain ⟨K_res, hK_res, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  obtain ⟨C_q, hC_q, hglob⟩ := exists_completeWeilMatrix_global_norm_cost
  obtain ⟨M₀_sep, hM₀_sep⟩ := eventually_atTop.mp hsep_ev
  obtain ⟨M₀_res, hM₀_res⟩ := eventually_atTop.mp (hres (1 / 2) (by norm_num) 16 (by norm_num))
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hN_fast : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 4 / (N : ℝ)) atTop (𝓝 0) :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).congr fun N => by dsimp only [Function.comp_def]; ring
  let H := 256 * Real.exp 2 + 4
  have hH_pos : 0 < H := by dsimp only [H]; positivity
  have hlog2H_nn : 0 ≤ Real.log (2 * H) :=
    Real.log_nonneg (by dsimp only [H]; linarith [Real.exp_pos 2])
  refine tendsto_div_log_log_of_abs_sub_le tendsto_log_primeAboveLowPacket_div_log_log
    (C := |completeWeilSelfFinitePart φ 1| + 2 * C_sep + 10) ?_
  filter_upwards [hc1,
    htend.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    hglob,
    norm_lowPacketProjection_primeAboveLowPacket_le,
    hN_fast.eventually (gt_mem_nhds (by
      positivity : 0 < 1 / (4 * H * (R + 1) * ((max 1 M₀_sep : ℝ) + (max 1 M₀_res : ℝ) +
        K_res + 4 * (Real.exp 1 + 3) ^ 2 + 100)))),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 64) |>.comp hL).eventually_ge_atTop
      (4 + R + 1 + C_q * (R + 1) + K_res + C_sep + 72 * (|completeWeilSelfFinitePart φ 1| + 4) +
        Real.log (2 * H) + 64),
    hL.eventually_ge_atTop (4 ^ (32 : ℝ) + 16),
    eventually_ge_atTop 16]
    with N hcN hrat_ub hglobN hu_bd hNf hL_rpow hL_big hN16
  clear hc1 htend hsep_ev hres hglob hL hN_fast
  dsimp only [Function.comp_def] at hrat_ub hNf hL_rpow
  change (4 : ℝ) ^ (32 : ℝ) + 16 ≤ Real.log (N : ℝ) at hL_big
  set L := Real.log (N : ℝ)
  set q := primeAboveLowPacket N
  set Lc := linearDefectCutoff (c N)
  set M := N / Lc
  obtain ⟨hq_prime, hq_gt, hq_le⟩ := primeAboveLowPacket_spec N
  obtain ⟨hLc3, h4c, -, hLcup⟩ := linearDefectCutoff_bounds hcN
  have h4_le : (4 : ℝ) ^ (32 : ℝ) ≤ L := by linarith only [hL_big]
  have hL1 : 1 ≤ L := (lt_of_lt_of_le (by norm_num : (1 : ℝ) < (4 : ℝ) ^ (32 : ℝ)) h4_le).le
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
  have hc8_le : c N ^ 8 ≤ (R + 1) * L := ((div_lt_iff₀ hL0).mp hrat_ub).le
  have hc2_le : c N ^ 2 ≤ (R + 1) * L ^ (1 / 4 : ℝ) := by
    have hp4 : (c N ^ 2) ^ 4 ≤ ((R + 1) * L ^ (1 / 4 : ℝ)) ^ 4 := by
      rw [← pow_mul, mul_pow, ← Real.rpow_natCast (L ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hL0.le]
      norm_num
      exact hc8_le.trans (mul_le_mul_of_nonneg_right
        (le_self_pow₀ (by linarith) (by norm_num)) hL0.le)
    exact (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) (by norm_num)).mp hp4
  have hCR_nn : 0 ≤ C_q * (R + 1) := by positivity
  have hS0_nn : 0 ≤ |completeWeilSelfFinitePart φ 1| := abs_nonneg _
  have hR1_64 : R + 1 ≤ L ^ (1 / 64 : ℝ) := by
    linarith only [hL_rpow, hCR_nn, hK_res, hC_sep, hlog2H_nn, hS0_nn]
  have hc_le_L : c N ≤ L := by
    have hc2_L2 : c N ^ 2 ≤ L ^ 2 := by
      calc c N ^ 2 ≤ (R + 1) * L ^ (1 / 4 : ℝ) := hc2_le
        _ ≤ L ^ (1 / 64 : ℝ) * L ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_right hR1_64 (by positivity)
        _ = L ^ (17 / 64 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
        _ ≤ L ^ 2 := (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq
            (Real.rpow_natCast L 2)
    exact (pow_le_pow_iff_left₀ hc0.le hL0.le (by norm_num)).mp hc2_L2
  have hL_7_16 : (4 : ℝ) ^ (14 : ℝ) ≤ L ^ (7 / 16 : ℝ) := by
    have hp := Real.rpow_le_rpow (by positivity) h4_le (by norm_num : (0 : ℝ) ≤ 7 / 16)
    rw [← Real.rpow_mul (by norm_num)] at hp
    exact hp.trans_eq' (by norm_num)
  have hlogL_64 : Real.log L ≤ 64 * L ^ (1 / 64 : ℝ) := by
    have hlg := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hL0 (1 / 64 : ℝ))
    rw [Real.log_rpow hL0] at hlg
    linarith [Real.rpow_nonneg hL0.le (1 / 64 : ℝ)]
  set K_M := (max 1 M₀_sep : ℝ) + (max 1 M₀_res : ℝ) + K_res + 4 * (Real.exp 1 + 3) ^ 2 + 100
  have hK_M_pos : 100 ≤ K_M := by
    dsimp only [K_M]
    have : 0 ≤ (max 1 M₀_sep : ℝ) + (max 1 M₀_res : ℝ) + K_res + 4 * (Real.exp 1 + 3) ^ 2 := by
      positivity
    linarith
  have hN_big_L4 : (4 * H * (R + 1) * K_M) * L ^ 4 ≤ N := by
    have hm := (div_lt_iff₀ hN0).mp hNf
    have hpos : 0 < 4 * H * (R + 1) * K_M := by positivity
    exact ((le_div_iff₀ hpos).mp (by rw [one_div_mul_eq_div] at hm; exact hm.le)).trans_eq'
      (mul_comm _ _)
  have hLc_le_HL : (Lc : ℝ) ≤ H * L := hLcup.trans (mul_le_mul_of_nonneg_left hc_le_L hH_pos.le)
  have hNLc_lt : (N : ℝ) < ((M : ℝ) + 1) * Lc := by
    exact_mod_cast (by simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (by omega : 0 < Lc))
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hKM_L3_ge : 2 * K_M * L ^ 3 ≤ (2 * (R + 1) * K_M) * L ^ 3 := by
    have hpos : 0 ≤ 2 * K_M * L ^ 3 := by positivity
    have hm := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ R + 1 by linarith only [hR]) hpos
    linarith only [hm, (by ring : (R + 1) * (2 * K_M * L ^ 3) = (2 * (R + 1) * K_M) * L ^ 3),
      (by ring : 1 * (2 * K_M * L ^ 3) = 2 * K_M * L ^ 3)]
  have h2KM_le_L3 : 2 * K_M ≤ 2 * K_M * L ^ 3 :=
    le_mul_of_one_le_right (by positivity) hL3
  have hM_ge_L3 : (2 * (R + 1) * K_M) * L ^ 3 ≤ M := by
    have hdiv_ge : (4 * (R + 1) * K_M) * L ^ 3 ≤ (M : ℝ) + 1 := by
      have h1 : (4 * (R + 1) * K_M) * L ^ 3 * (H * L) ≤ N :=
        (by ring : (4 * (R + 1) * K_M) * L ^ 3 * (H * L) =
          (4 * H * (R + 1) * K_M) * L ^ 4).le.trans hN_big_L4
      have h2 : ((M : ℝ) + 1) * Lc ≤ ((M : ℝ) + 1) * (H * L) :=
        mul_le_mul_of_nonneg_left hLc_le_HL (by positivity)
      exact le_of_mul_le_mul_right (h1.trans (hNLc_lt.le.trans h2)) (mul_pos hH_pos hL0)
    have h1_le : 1 ≤ (2 * (R + 1) * K_M) * L ^ 3 := by
      linarith only [hK_M_pos, h2KM_le_L3, hKM_L3_ge]
    linarith only [hdiv_ge, h1_le]
  have h2KM_le_M : 2 * K_M ≤ M := h2KM_le_L3.trans (hKM_L3_ge.trans hM_ge_L3)
  have h2KML3_le_M : 2 * K_M * L ^ 3 ≤ M := hKM_L3_ge.trans hM_ge_L3
  have hM_sep : M₀_sep ≤ M := by
    have hM0R : (M₀_sep : ℝ) ≤ M := by
      have hm : (M₀_sep : ℝ) ≤ (max 1 M₀_sep : ℝ) := by exact_mod_cast le_max_right 1 M₀_sep
      have hpos_rest : 0 ≤ (max 1 M₀_res : ℝ) + K_res + 4 * (Real.exp 1 + 3) ^ 2 + 100 := by
        positivity
      have hK_nn : 0 ≤ K_M := by linarith only [hK_M_pos]
      dsimp only [K_M] at h2KM_le_M hK_nn
      linarith only [hm, hpos_rest, hK_nn, h2KM_le_M]
    exact_mod_cast hM0R
  have hM_res : M₀_res ≤ M := by
    have hM0R : (M₀_res : ℝ) ≤ M := by
      have hm : (M₀_res : ℝ) ≤ (max 1 M₀_res : ℝ) := by exact_mod_cast le_max_right 1 M₀_res
      have hpos_rest : 0 ≤ (max 1 M₀_sep : ℝ) + K_res + 4 * (Real.exp 1 + 3) ^ 2 + 100 := by
        positivity
      have hK_nn : 0 ≤ K_M := by linarith only [hK_M_pos]
      dsimp only [K_M] at h2KM_le_M hK_nn
      linarith only [hm, hpos_rest, hK_nn, h2KM_le_M]
    exact_mod_cast hM0R
  have hM_width1 : 4 * (Real.exp 1 + 3) ^ 2 * (1 : ℝ) ^ 2 ≤ M := by
    have hpos_rest : 0 ≤ (max 1 M₀_sep : ℝ) + (max 1 M₀_res : ℝ) + K_res + 100 := by positivity
    have hK_nn : 0 ≤ K_M := by linarith only [hK_M_pos]
    dsimp only [K_M] at h2KM_le_M hK_nn
    linarith only [hpos_rest, hK_nn, h2KM_le_M, (by ring : 4 * (Real.exp 1 + 3) ^ 2 * (1 : ℝ) ^ 2 =
      4 * (Real.exp 1 + 3) ^ 2)]
  have hM_ge_2K : 2 * K_res * L ^ 3 ≤ M := by
    have hrest_nn : 0 ≤ 2 * ((max 1 M₀_sep : ℝ) + (max 1 M₀_res : ℝ) +
      4 * (Real.exp 1 + 3) ^ 2 + 100) * L ^ 3 := by positivity
    dsimp only [K_M] at h2KML3_le_M
    linarith only [hrest_nn, h2KML3_le_M,
      (by ring : 2 * ((max 1 M₀_sep : ℝ) + (max 1 M₀_res : ℝ) + K_res +
          4 * (Real.exp 1 + 3) ^ 2 + 100) * L ^ 3 =
        2 * K_res * L ^ 3 + 2 * ((max 1 M₀_sep : ℝ) + (max 1 M₀_res : ℝ) +
          4 * (Real.exp 1 + 3) ^ 2 + 100) * L ^ 3)]
  have hM_ge_L3_1 : L ^ 3 ≤ M := by
    have hm := mul_le_mul_of_nonneg_right hK_M_pos (pow_nonneg hL0.le 3)
    linarith only [hm, h2KML3_le_M, pow_nonneg hL0.le 3]
  have hM2 : 2 ≤ M := by
    have : (100 : ℝ) ≤ M := by linarith only [hK_M_pos, h2KM_le_M]
    exact_mod_cast (show (2 : ℝ) ≤ M by linarith only [this])
  clear_value K_M
  clear hNf
  have hM1 : 1 ≤ M := by omega
  have hMN : M ≤ N := Nat.div_le_self N Lc
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  set L_M := Real.log (M : ℝ)
  have hLM_lower : L - Real.log (2 * H * L) ≤ L_M := by
    have hNM_le_2Lc : (N : ℝ) ≤ 2 * Lc * M := by
      have h2M : (M : ℝ) + 1 ≤ 2 * M := by
        have : (2 : ℝ) ≤ M := by exact_mod_cast hM2
        linarith
      nlinarith only [hNLc_lt.le, h2M, (Nat.cast_nonneg Lc : (0 : ℝ) ≤ Lc)]
    have hN_le : (N : ℝ) ≤ (2 * H * L) * M := by
      calc (N : ℝ) ≤ 2 * Lc * M := hNM_le_2Lc
        _ ≤ 2 * (H * L) * M :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLc_le_HL zero_le_two) hM0.le
        _ = (2 * H * L) * M := by ring
    have hlg := Real.log_le_log hN0 hN_le
    rw [Real.log_mul (by positivity) hM0.ne'] at hlg
    linarith only [hlg]
  have h2HL_rpow : Real.log (2 * H * L) ≤ 65 * L ^ (1 / 64 : ℝ) := by
    rw [Real.log_mul (by positivity) hL0.ne']
    have hl2H : Real.log (2 * H) ≤ L ^ (1 / 64 : ℝ) := by
      linarith only [hL_rpow, hR, hCR_nn, hK_res, hC_sep, hS0_nn]
    linarith only [hl2H, hlogL_64]
  have hLM_ge_half : L / 2 ≤ L_M := by
    have h65 : 65 * L ^ (1 / 64 : ℝ) ≤ L / 2 := by
      have h130 : (130 : ℝ) ≤ L ^ (63 / 64 : ℝ) :=
        (by norm_num : (130 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans
          (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
      have hm := mul_le_mul_of_nonneg_right h130 (Real.rpow_nonneg hL0.le (1 / 64 : ℝ))
      rw [← Real.rpow_add hL0, show (63 / 64 + 1 / 64 : ℝ) = 1 by norm_num, Real.rpow_one] at hm
      linarith only [hm]
    linarith only [hLM_lower, h2HL_rpow, h65]
  have hLM_31 : (4 : ℝ) ^ (31 : ℝ) ≤ L_M := by
    have hdiv : (4 : ℝ) ^ (32 : ℝ) / 2 = 2 * (4 : ℝ) ^ (31 : ℝ) := by
      rw [show (32 : ℝ) = 31 + 1 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]; ring
    linarith only [hLM_ge_half, h4_le, hdiv, Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) 31]
  have hLM1 : 1 ≤ L_M :=
    (Real.one_le_rpow (by norm_num) (by norm_num)).trans hLM_31
  have hLM0 : 0 < L_M := zero_lt_one.trans_le hLM1
  have hLM_le_L : L_M ≤ L := Real.log_le_log hM0 (by exact_mod_cast hMN)
  set c' := c N * (M : ℝ) / N
  have hc'_lo : 1 / (512 * Real.exp 2) ≤ c' := by
    have h32M : (M : ℝ) + 1 ≤ (3 / 2 : ℝ) * M := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM2
      linarith
    have h32H : (3 / 2 : ℝ) * H ≤ 512 * Real.exp 2 := by
      dsimp only [H]; linarith [Real.one_le_exp (zero_le_two (α := ℝ))]
    have hN_le : (N : ℝ) ≤ 512 * Real.exp 2 * c N * M := by
      calc (N : ℝ) ≤ ((M : ℝ) + 1) * Lc := hNLc_lt.le
        _ ≤ ((3 / 2 : ℝ) * M) * (H * c N) :=
            mul_le_mul h32M hLcup (Nat.cast_nonneg _) (by positivity)
        _ = ((3 / 2 : ℝ) * H) * c N * M := by ring
        _ ≤ 512 * Real.exp 2 * c N * M :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h32H hc0.le) hM0.le
    rw [div_le_div_iff₀ (by positivity) hN0]
    nlinarith only [hN_le]
  have hc'_hi : c' ≤ 1 / 2 := by
    have hMLc : (M : ℝ) * Lc ≤ N := by exact_mod_cast Nat.div_mul_le_self N Lc
    dsimp only [c']
    rw [div_le_iff₀ hN0]
    nlinarith only [hMLc, h4c, hM0]
  clear_value M Lc c'
  have hq_pr : q.Prime := hq_prime
  have hq_le_4rpow : (q : ℝ) ≤ 4 * L ^ (13 / 32 : ℝ) := by
    have hQ₁_le : (lowPacketCutoff N : ℝ) ≤ L ^ (13 / 32 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg hL0.le _)
    have h2_le_rpow : (2 : ℝ) ≤ L ^ (13 / 32 : ℝ) :=
      (by norm_num : (2 : ℝ) ≤ (4 : ℝ) ^ 1).trans
        (four_pow_nat_le_rpow (e := 13 / 32) 1 h4_le (by norm_num) (by norm_num))
    have hmax : ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
      rw [Nat.cast_max, Nat.cast_ofNat]; exact max_le h2_le_rpow hQ₁_le
    have hqc : (q : ℝ) ≤ 2 * ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) := by exact_mod_cast hq_le
    linarith
  have hq_le_LM_half : (q : ℝ) ≤ L_M ^ (1 / 2 : ℝ) := by
    have h8_le : (8 : ℝ) ≤ L_M ^ (3 / 32 : ℝ) :=
      (by norm_num : (8 : ℝ) ≤ (4 : ℝ) ^ 2).trans
        (four_pow_nat_le_rpow (e := 3 / 32) 2 hLM_31 (by norm_num) (by norm_num))
    have h2_13 : (2 : ℝ) ^ (13 / 32 : ℝ) ≤ 2 :=
      (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)).trans_eq (Real.rpow_one 2)
    have hL_le_2LM : L ^ (13 / 32 : ℝ) ≤ 2 * L_M ^ (13 / 32 : ℝ) := by
      have hp := Real.rpow_le_rpow hL0.le (show L ≤ 2 * L_M by linarith only [hLM_ge_half])
        (by norm_num : (0 : ℝ) ≤ 13 / 32)
      rw [Real.mul_rpow zero_le_two hLM0.le] at hp
      exact hp.trans (mul_le_mul_of_nonneg_right h2_13 (by positivity))
    calc (q : ℝ) ≤ 4 * L ^ (13 / 32 : ℝ) := hq_le_4rpow
      _ ≤ 4 * (2 * L_M ^ (13 / 32 : ℝ)) := mul_le_mul_of_nonneg_left hL_le_2LM (by norm_num)
      _ = 8 * L_M ^ (13 / 32 : ℝ) := by ring
      _ ≤ L_M ^ (3 / 32 : ℝ) * L_M ^ (13 / 32 : ℝ) :=
          mul_le_mul_of_nonneg_right h8_le (by positivity)
      _ = L_M ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hLM0]; norm_num
  have hq_le_LM : (q : ℝ) ≤ L_M :=
    hq_le_LM_half.trans ((Real.rpow_le_rpow_of_exponent_le hLM1 (by norm_num)).trans_eq
      (Real.rpow_one _))
  have hlogq_LM : 1 + Real.log q ≤ 65 * L_M ^ (1 / 64 : ℝ) := by
    have hlg := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hLM0 (1 / 64 : ℝ))
    rw [Real.log_rpow hLM0] at hlg
    have hlq : Real.log (q : ℝ) ≤ Real.log L_M :=
      Real.log_le_log (by exact_mod_cast hq_pr.pos) hq_le_LM
    have h1_64 : 1 ≤ L_M ^ (1 / 64 : ℝ) := Real.one_le_rpow hLM1 (by norm_num)
    linarith [Real.rpow_nonneg hLM0.le (1 / 64 : ℝ)]
  set v := normalizedRamanujanHorizonVector q N
  set u := (conductorSubspace (lowPacketCutoff N) N).starProjection v
  set z := lowPacketOrthogonalPrimeQuasimode N
  set p_z := horizonPrefixVector M z
  set p_v := horizonPrefixVector M v
  set p_u := horizonPrefixVector M u
  change |completeWeilEnergy φ (c N) N p_z - Real.log (q : ℝ)| ≤ _
  have hp_sub : p_z = p_v - p_u := by
    ext ⟨n, hn⟩
    change (if n ≤ M then primeHorizonExtension (v - u) n else 0) =
      (if n ≤ M then primeHorizonExtension v n else 0) -
      (if n ≤ M then primeHorizonExtension u n else 0)
    rw [primeHorizonExtension_coe (v - u) ⟨n, hn⟩, primeHorizonExtension_coe v ⟨n, hn⟩,
      primeHorizonExtension_coe u ⟨n, hn⟩, PiLp.sub_apply]
    split_ifs <;> ring
  have hvan_pv : ∀ n, M < n → primeHorizonExtension p_v n = 0 := fun n hn => by
    rw [congrFun (primeHorizonExtension_horizonPrefixVector hMN v) n, if_neg (Nat.not_le.mpr hn)]
  have hvan_pu : ∀ n, M < n → primeHorizonExtension p_u n = 0 := fun n hn => by
    rw [congrFun (primeHorizonExtension_horizonPrefixVector hMN u) n, if_neg (Nat.not_le.mpr hn)]
  set v' := normalizedRamanujanHorizonVector q M
  set α := Real.sqrt (L_M / L)
  have hα_nn : 0 ≤ α := Real.sqrt_nonneg _
  have hα_le1 : α ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hL0).mpr hLM_le_L)
  have hα_sq : α ^ 2 = L_M / L := Real.sq_sqrt (div_nonneg hLM0.le hL0.le)
  have hpv_eq : horizonProfileVector (primeHorizonExtension p_v) M = α • v' := by
    ext ⟨n, hn⟩
    have hnN : n ∈ Icc 1 N := mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
    change primeHorizonExtension p_v n = α * ((Real.sqrt L_M)⁻¹ * (normalizedRamanujanMode q n / Real.sqrt n))
    rw [congrFun (primeHorizonExtension_horizonPrefixVector hMN v) n, if_pos (mem_Icc.mp hn).2,
      primeHorizonExtension_coe v ⟨n, hnN⟩]
    change (Real.sqrt L)⁻¹ * (normalizedRamanujanMode q n / Real.sqrt n) = _
    dsimp only [α]
    rw [Real.sqrt_div hLM0.le]
    field_simp [(Real.sqrt_pos.mpr hLM0).ne', (Real.sqrt_pos.mpr hL0).ne']
  set p'_u := horizonProfileVector (primeHorizonExtension p_u) M with hp'u_def
  have hp'u_norm : ‖p'_u‖ ≤ ‖u‖ := by
    have hsq_eq : ‖p'_u‖ ^ 2 = ‖p_u‖ ^ 2 := by
      rw [← sum_primeHorizonExtension_sq p'_u, ← sum_primeHorizonExtension_sq p_u]
      have hsub_M : Icc 1 M ⊆ Icc 1 N := Icc_subset_Icc_right hMN
      rw [← sum_subset hsub_M (fun n hnN hnM => by
        have hn1 := (mem_Icc.mp hnN).1
        have hgt : M < n := Nat.lt_of_not_le fun hle => hnM (mem_Icc.mpr ⟨hn1, hle⟩)
        rw [hvan_pu n hgt]; norm_num)]
      exact sum_congr rfl fun n hn => by rw [primeHorizonExtension_coe p'_u ⟨n, hn⟩]; rfl
    have hpu_u := norm_horizonPrefixVector_le M u
    nlinarith only [hsq_eq, hpu_u, norm_nonneg p'_u, norm_nonneg p_u, norm_nonneg u]
  have hpu_le_u : ‖p_u‖ ≤ ‖u‖ := norm_horizonPrefixVector_le M u
  have hsep_v' :
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' -
        Matrix.toEuclideanLin (completeWeilMatrix φ 1 M) v'‖ ≤ C_sep :=
    hM₀_sep M hM_sep hq_pr hq_le_LM hc'_lo hc'_hi
  set E1_q := completedConductorEnergy φ 1 q with hE1_def
  set r1 := Matrix.toEuclideanLin (completeWeilMatrix φ 1 M) v' - E1_q • v' with hr1_def
  have hr0' : ‖r1‖ ^ 2 ≤ K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
      ((1 : ℝ) ^ 2 * (1 + Real.log (1 : ℝ)) ^ 3 * L_M ^ (1 / (16 : ℝ)) / L_M +
        (1 : ℝ) ^ 10 * (L_M / M) ^ 2) := by
    simpa only [Nat.cast_ofNat] using hM₀_res M hM_res q hq_pr.pos hq_le_LM_half 1 le_rfl hM_width1
  clear hM₀_sep hM₀_res
  have hv0_fn : q * q ≤ M → |‖v'‖ ^ 2 - 1| ≤ (2 * Real.log (q : ℝ) + 9) / L_M :=
    abs_norm_normalizedRamanujanHorizonVector_sq_sub_one_le hq_pr.two_le
  have hEq_f : E1_q = completeWeilSelfFinitePart φ 1 + Real.log q +
      ArithmeticIntersectionTheory.tameDifferent q - shellCorrection φ 1 q := by
    rw [hE1_def, completedConductorEnergy_eq_sub_shellCorrection zero_lt_one hq_pr.pos]
    unfold completeWeilAdjunctionEnergy ramanujanAdjunctionEnergy
    rw [if_neg hq_pr.ne_one]; ring
  have hrc'_decomp : Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' - E1_q • v' =
      (Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' -
        Matrix.toEuclideanLin (completeWeilMatrix φ 1 M) v') + r1 := by
    rw [hr1_def]; abel
  clear_value v u z p_z p_v v' E1_q r1 α L_M q
  have hr1_norm : ‖r1‖ ≤ 1 :=
    prefix_quasimode_unit_residual_le_one hK_res hL0 hLM1 hM0 (norm_nonneg r1) hLM_31
      hLM_ge_half hLM_le_L (by linarith only [hL_rpow, hR, hCR_nn, hC_sep, hlog2H_nn, hS0_nn])
      hq_le_LM_half hq_le_LM hlogq_LM hM_ge_2K hM_ge_L3_1 hr0'
  have hqqM : q * q ≤ M := by
    have hq2_LM : ((q * q : ℕ) : ℝ) ≤ L_M := by
      rw [Nat.cast_mul]
      calc (q : ℝ) * q ≤ L_M ^ (1 / 2 : ℝ) * L_M ^ (1 / 2 : ℝ) :=
            mul_le_mul hq_le_LM_half hq_le_LM_half (by positivity) (by positivity)
        _ = L_M := by rw [← Real.rpow_add hLM0, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
    have hLM_le_M : L_M ≤ M := by
      have hL_L3 : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num)
      exact hLM_le_L.trans (hL_L3.trans hM_ge_L3_1)
    exact_mod_cast hq2_LM.trans hLM_le_M
  have hE1_sub : |E1_q - Real.log q| ≤ |completeWeilSelfFinitePart φ 1| + 3 := by
    have h1_lt_q : (1 : ℝ) < q := by exact_mod_cast hq_pr.one_lt
    have hsh1 : |shellCorrection φ 1 q| ≤ 2 := by
      have h := abs_shellCorrection_prime_of_gt hφ hsupp hM_int le_rfl hq_pr h1_lt_q
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq_pr.two_le
      refine h.trans ?_
      rw [one_pow, mul_one, div_le_iff₀ (by linarith)]
      linarith
    have htame := tameDifferent_prime_le_one hq_pr
    rw [show E1_q - Real.log q = completeWeilSelfFinitePart φ 1 +
      ArithmeticIntersectionTheory.tameDifferent q - shellCorrection φ 1 q by rw [hEq_f]; ring]
    have t1 := abs_sub (completeWeilSelfFinitePart φ 1 + ArithmeticIntersectionTheory.tameDifferent q)
      (shellCorrection φ 1 q)
    have t2 := abs_add_le (completeWeilSelfFinitePart φ 1) (ArithmeticIntersectionTheory.tameDifferent q)
    linarith only [t1, t2, htame, hsh1]
  have hrc'_norm : ‖Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' - E1_q • v'‖ ≤ C_sep + 1 := by
    rw [hrc'_decomp]
    exact (norm_add_le _ _).trans (add_le_add hsep_v' hr1_norm)
  have hBv'_le : ‖Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v'‖ ≤
      |E1_q| * ‖v'‖ + (C_sep + 1) := by
    have hBv' : Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' =
        E1_q • v' + (Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' - E1_q • v') := by abel
    rw [hBv']
    exact (norm_add_le _ _).trans (by rw [norm_smul, Real.norm_eq_abs]; linarith only [hrc'_norm])
  obtain ⟨hv'_norm_le2, hE1_v'_sq, hα_sub1, hu_rpow, hBv'_u⟩ :=
    prefix_quasimode_scalar_closing_bounds hL1 hLM1 (by exact_mod_cast hq_pr.pos)
      (norm_nonneg v') (norm_nonneg p'_u) hα_nn hα_le1 hα_sq hLM_31 hLM_ge_half hLM_le_L
      hL_7_16 hlogL_64 hq_le_LM hlogq_LM (by linarith only [hLM_lower, h2HL_rpow])
      (by linarith only [hL_rpow, hR, hCR_nn, hK_res, hC_sep, hlog2H_nn])
      (by linarith only [hL_rpow, hR, hCR_nn, hK_res, hlog2H_nn, hS0_nn])
      (hv0_fn hqqM) hE1_sub hu_bd hp'u_norm hBv'_le
  have hEpu_abs : |completeWeilEnergy φ (c N) N p_u| ≤ 1 :=
    global_low_packet_energy_bound_le_one hC_q hR hcN hL1 (norm_nonneg p_u) hL_7_16 hc2_le
      hR1_64 (by linarith only [hL_rpow, hR, hK_res, hC_sep, hlog2H_nn, hS0_nn])
      (hpu_le_u.trans hu_rpow) ((hglobN hcN hc_le_L).1 p_u)
  rw [hp'u_def] at hBv'_u
  clear_value p_u p'_u
  exact (abs_prefix_quasimode_energy_sub_le hφ hsupp hM_int hc0 hM1 hMN hC_sep.le hp_sub hvan_pv
    hvan_pu hpv_eq hα_nn hα_le1 hrc'_norm hv'_norm_le2 hE1_sub hα_sub1 hE1_v'_sq hBv'_u hEpu_abs).trans_eq
    (by ring)

/-! #### 2c. Collar energy asymptotic `(1 / 8) log log N` and the `4 / 13` Schur limit -/

private theorem abs_fullWeilCenterMatrix_inner_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM_int : 0 < ∫ u, φ u ^ 2)
    {cq : ℝ} (hcq0 : 0 < cq) {Nq N : ℕ} (hNq1 : 1 ≤ Nq) (hNqN : Nq ≤ N)
    (x_q : EuclideanSpace ℝ (PrimeHorizonIndex Nq)) :
    |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ cq) Nq) x_q, x_q⟫| ≤
      cq * (3 * Real.log (N : ℝ) + 7) * ‖x_q‖ ^ 2 := by
  have hNq0 : (0 : ℝ) < Nq := by exact_mod_cast hNq1
  set α := completeWeilPoleShift φ cq
  have hα0 : 0 ≤ α := completeWeilPoleShift_nonneg φ hcq0.le
  have hα_le : α ≤ cq := completeWeilPoleShift_le hφ.continuous hsupp hM_int hcq0.le
  set a := primeHorizonExtension x_q with ha_def
  have hexp_cent : ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α Nq) x_q, x_q⟫ =
      (α / Nq) * (∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * arithmeticPoleKernel n j) -
      α * ((∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * archimedeanCenterKernel n j) / Nq) := by
    change ⟪Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => (α / Nq) *
        (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) Nq) x_q, x_q⟫ = _
    rw [horizonKernelMatrix_inner, ← ha_def]
    have hterm (n j : ℕ) :
        a n * a j * ((α / Nq) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) =
          (α / Nq) * (a n * a j * arithmeticPoleKernel n j) -
          (α / Nq) * (a n * a j * archimedeanCenterKernel n j) := by ring
    simp only [hterm, sum_sub_distrib, ← mul_sum]
    ring
  have hpole_abs : |∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * arithmeticPoleKernel n j| ≤
      2 * (Nq : ℝ) * (Real.log (Nq : ℝ) + 2) * ‖x_q‖ ^ 2 := by
    rw [arithmeticPoleKernel_quadratic_eq, abs_mul, abs_mul, abs_two]
    have hcs1 : |SelectiveMultiscaleArithmeticPositivity.harmonicSum Nq a| ≤
        Real.sqrt (1 + Real.log (Nq : ℝ)) * ‖x_q‖ := by
      unfold SelectiveMultiscaleArithmeticPositivity.harmonicSum
      have hsq : (∑ k ∈ Icc 1 Nq, |a k| * (1 / Real.sqrt k)) ^ 2 ≤
          (∑ k ∈ Icc 1 Nq, a k ^ 2) * ∑ k ∈ Icc 1 Nq, (1 / Real.sqrt (k : ℝ)) ^ 2 := by
        simpa only [sq_abs] using sum_mul_sq_le_sq_mul_sq (Icc 1 Nq)
          (fun k => |a k|) (fun k => 1 / Real.sqrt (k : ℝ))
      have h1k : (∑ k ∈ Icc 1 Nq, (1 / Real.sqrt (k : ℝ)) ^ 2) ≤ 1 + Real.log (Nq : ℝ) := by
        have heq : (∑ k ∈ Icc 1 Nq, (1 / Real.sqrt (k : ℝ)) ^ 2) =
            ∑ k ∈ Icc 1 Nq, 1 / (k : ℝ) := by
          refine sum_congr rfl fun k hk => ?_
          have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
          rw [div_pow, one_pow, Real.sq_sqrt hk0.le]
        rw [heq]
        exact RHTower.sum_Icc_one_div_le hNq1
      have habs_sum : |∑ k ∈ Icc 1 Nq, a k / Real.sqrt k| ≤
          ∑ k ∈ Icc 1 Nq, |a k| * (1 / Real.sqrt k) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
        rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg (k : ℝ)), div_eq_mul_one_div]
      rw [sum_primeHorizonExtension_sq] at hsq
      have hle_rhs : (∑ k ∈ Icc 1 Nq, |a k| * (1 / Real.sqrt k)) ^ 2 ≤
          (Real.sqrt (1 + Real.log (Nq : ℝ)) * ‖x_q‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by linarith [Real.log_natCast_nonneg Nq]), mul_comm]
        exact hsq.trans (mul_le_mul_of_nonneg_left h1k (sq_nonneg _))
      exact habs_sum.trans ((sq_le_sq₀ (sum_nonneg fun _ _ => by positivity)
        (by positivity)).mp hle_rhs)
    have hcs2 : |∑ k ∈ Icc 1 Nq, a k * Real.sqrt k| ≤ (Nq : ℝ) * ‖x_q‖ := by
      have hsq : (∑ k ∈ Icc 1 Nq, |a k| * Real.sqrt k) ^ 2 ≤
          (∑ k ∈ Icc 1 Nq, a k ^ 2) * ∑ k ∈ Icc 1 Nq, (Real.sqrt (k : ℝ)) ^ 2 := by
        simpa only [sq_abs] using sum_mul_sq_le_sq_mul_sq (Icc 1 Nq)
          (fun k => |a k|) (fun k => Real.sqrt (k : ℝ))
      have hks : (∑ k ∈ Icc 1 Nq, (Real.sqrt (k : ℝ)) ^ 2) ≤ (Nq : ℝ) ^ 2 := by
        calc (∑ k ∈ Icc 1 Nq, (Real.sqrt (k : ℝ)) ^ 2)
            ≤ ∑ _k ∈ Icc 1 Nq, (Nq : ℝ) := by
              refine sum_le_sum fun k hk => ?_
              rw [Real.sq_sqrt (Nat.cast_nonneg k)]
              exact_mod_cast (mem_Icc.mp hk).2
          _ = (Nq : ℝ) ^ 2 := by
              rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, sq]
      have habs_sum : |∑ k ∈ Icc 1 Nq, a k * Real.sqrt k| ≤
          ∑ k ∈ Icc 1 Nq, |a k| * Real.sqrt k := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [sum_primeHorizonExtension_sq] at hsq
      have hle_rhs : (∑ k ∈ Icc 1 Nq, |a k| * Real.sqrt k) ^ 2 ≤ ((Nq : ℝ) * ‖x_q‖) ^ 2 := by
        rw [mul_pow, mul_comm ((Nq : ℝ) ^ 2)]
        exact hsq.trans (mul_le_mul_of_nonneg_left hks (sq_nonneg _))
      exact habs_sum.trans ((sq_le_sq₀ (sum_nonneg fun _ _ => by positivity)
        (by positivity)).mp hle_rhs)
    have hsqrt_le : Real.sqrt (1 + Real.log (Nq : ℝ)) ≤ Real.log (Nq : ℝ) + 2 := by
      have hl0 : 0 ≤ Real.log (Nq : ℝ) := Real.log_natCast_nonneg Nq
      have hsq_in : 1 + Real.log (Nq : ℝ) ≤ (Real.log (Nq : ℝ) + 2) ^ 2 := by
        nlinarith only [hl0, sq_nonneg (Real.log (Nq : ℝ))]
      exact (Real.sqrt_le_sqrt hsq_in).trans_eq (Real.sqrt_sq (by linarith only [hl0]))
    calc 2 * |SelectiveMultiscaleArithmeticPositivity.harmonicSum Nq a| *
          |∑ k ∈ Icc 1 Nq, a k * Real.sqrt k|
        ≤ 2 * (Real.sqrt (1 + Real.log (Nq : ℝ)) * ‖x_q‖) * ((Nq : ℝ) * ‖x_q‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcs1 zero_le_two) hcs2
            (abs_nonneg _) (by positivity)
      _ ≤ 2 * ((Real.log (Nq : ℝ) + 2) * ‖x_q‖) * ((Nq : ℝ) * ‖x_q‖) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hsqrt_le (norm_nonneg _)) zero_le_two)
            (by positivity)
      _ = 2 * (Nq : ℝ) * (Real.log (Nq : ℝ) + 2) * ‖x_q‖ ^ 2 := by ring
  have harch_abs : |(∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * archimedeanCenterKernel n j) / Nq| ≤
      (Real.log (Nq : ℝ) + 3) * ‖x_q‖ ^ 2 := by
    calc |(∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * archimedeanCenterKernel n j) / Nq|
        = |∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * archimedeanCenterKernel n j| / Nq := by
          rw [abs_div, abs_of_pos hNq0]
      _ ≤ (∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, |a n| * |a j| * archimedeanCenterKernel n j) / Nq := by
          refine div_le_div_of_nonneg_right ?_ hNq0.le
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (archimedeanCenterKernel_nonneg n j)]
      _ ≤ (∑ n ∈ Icc 1 Nq, (n : ℝ) / Nq * Real.log n * |a n| ^ 2) +
            3 * ∑ n ∈ Icc 1 Nq, |a n| ^ 2 :=
          collar_quadratic_div_horizon_le hNq1 (fun n => |a n|)
      _ ≤ Real.log (Nq : ℝ) * (∑ n ∈ Icc 1 Nq, a n ^ 2) + 3 * ∑ n ∈ Icc 1 Nq, a n ^ 2 := by
          simp_rw [sq_abs]
          rw [Finset.mul_sum (Icc 1 Nq) (fun n => a n ^ 2) (Real.log (Nq : ℝ))]
          refine add_le_add (sum_le_sum fun n hn => ?_) le_rfl
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
          have hnNq : (n : ℝ) ≤ Nq := by exact_mod_cast (mem_Icc.mp hn).2
          have hr1 : (n : ℝ) / Nq ≤ 1 := (div_le_one hNq0).mpr hnNq
          have hln : Real.log (n : ℝ) ≤ Real.log (Nq : ℝ) := Real.log_le_log hn0 hnNq
          have hprod : (n : ℝ) / Nq * Real.log n ≤ Real.log (Nq : ℝ) :=
            (mul_le_mul hr1 hln (Real.log_natCast_nonneg n) zero_le_one).trans_eq (one_mul _)
          exact mul_le_mul_of_nonneg_right hprod (sq_nonneg _)
      _ = (Real.log (Nq : ℝ) + 3) * ‖x_q‖ ^ 2 := by
          rw [sum_primeHorizonExtension_sq]; ring
  have hlogNq_le : Real.log (Nq : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hNq0 (by exact_mod_cast hNqN)
  rw [hexp_cent]
  have htri := abs_sub
    ((α / Nq) * ∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * arithmeticPoleKernel n j)
    (α * ((∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * archimedeanCenterKernel n j) / Nq))
  have ht1 : |(α / Nq) * ∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * arithmeticPoleKernel n j| ≤
      cq * (2 * Real.log (N : ℝ) + 4) * ‖x_q‖ ^ 2 := by
    rw [abs_mul, abs_div, abs_of_nonneg hα0, abs_of_pos hNq0]
    calc (α / Nq) * |∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * arithmeticPoleKernel n j|
        ≤ (cq / Nq) * (2 * (Nq : ℝ) * (Real.log (Nq : ℝ) + 2) * ‖x_q‖ ^ 2) :=
          mul_le_mul (div_le_div_of_nonneg_right hα_le hNq0.le) hpole_abs
            (abs_nonneg _) (by positivity)
      _ = cq * (2 * Real.log (Nq : ℝ) + 4) * ‖x_q‖ ^ 2 := by
          field_simp [hNq0.ne']; ring
      _ ≤ cq * (2 * Real.log (N : ℝ) + 4) * ‖x_q‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith only [hlogNq_le]) hcq0.le)
            (sq_nonneg _)
  have ht2 : |α * ((∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * archimedeanCenterKernel n j) / Nq)| ≤
      cq * (Real.log (N : ℝ) + 3) * ‖x_q‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg hα0]
    calc α * |(∑ n ∈ Icc 1 Nq, ∑ j ∈ Icc 1 Nq, a n * a j * archimedeanCenterKernel n j) / Nq|
        ≤ cq * ((Real.log (Nq : ℝ) + 3) * ‖x_q‖ ^ 2) :=
          mul_le_mul hα_le harch_abs (abs_nonneg _) hcq0.le
      _ ≤ cq * ((Real.log (N : ℝ) + 3) * ‖x_q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by linarith only [hlogNq_le]) (sq_nonneg _))
            hcq0.le
      _ = cq * (Real.log (N : ℝ) + 3) * ‖x_q‖ ^ 2 := by ring
  linarith only [htri, ht1, ht2]

private theorem completeWeilEnergy_collar_spike_approx {c : ℝ} (hc1 : 1 ≤ c) {N q : ℕ}
    (hq : q.Prime) (h2LN : 2 * linearDefectCutoff c ≤ N) (hNq1 : 1 ≤ N / q)
    (_hMq1 : 1 ≤ (N / linearDefectCutoff c) / q)
    (_hMq_lt : (N / linearDefectCutoff c) / q < N / q)
    (hcq_quarter : c * ((N / q : ℕ) : ℝ) / (N : ℝ) ≤ 1 / 4) (A : ℝ) :
    let φ := tiltedUnitSpline
    let M := N / linearDefectCutoff c
    let Nq := N / q
    let cq := c * (Nq : ℝ) / (N : ℝ)
    let y_sp := horizonProfileVector
      (fun n => if M < n ∧ q ∣ n then A * Real.sqrt q / Real.sqrt n else 0) N
    |completeWeilEnergy φ c N y_sp -
        (Real.log (N : ℝ) - Real.log c + completeWeilSelfFinitePart φ 1 -
          Real.eulerMascheroniConstant) * ‖y_sp‖ ^ 2| ≤
      (topPrimeConstant * c * (1 + Real.log c) +
        cq * (3 * Real.log (N : ℝ) + 7) +
        4 * atomCrossErrorConstant φ cq * cq ^ 2 +
        2 * atomPoleMomentErrorConstant φ * cq ^ 2 + 2) * ‖y_sp‖ ^ 2 := by
  intro φ M Nq cq y_sp
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM_int := integral_tiltedUnitSpline_sq_pos
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  obtain ⟨hLc3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  have hLN : linearDefectCutoff c ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNq0 : (0 : ℝ) < Nq := by exact_mod_cast hNq1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hcq0 : 0 < cq := div_pos (mul_pos hc0 hNq0) hN0
  have hcq1 : cq < 1 := by linarith only [hcq_quarter]
  have hcq_le_Nq : cq ≤ Nq := by linarith only [hcq1, (show (1 : ℝ) ≤ Nq by exact_mod_cast hNq1)]
  have hw_eq : cq / (Nq : ℝ) = c / (N : ℝ) := by
    dsimp only [cq]; field_simp [hNq0.ne', hN0.ne']
  have hsep_q : cq / (Nq : ℝ) < atomSpacing Nq := by
    have hb : cq / (Nq : ℝ) ≤ (1 / ((Nq : ℝ) + 1)) / 2 := by
      have hNq1R : (1 : ℝ) ≤ Nq := by exact_mod_cast hNq1
      have h1 : cq ≤ 1 / 4 := hcq_quarter
      rw [div_le_iff₀ hNq0]
      have h2 : (1 / ((Nq : ℝ) + 1)) / 2 * (Nq : ℝ) = (Nq : ℝ) / (2 * ((Nq : ℝ) + 1)) := by ring
      rw [h2, le_div_iff₀ (by positivity)]
      linarith only [h1, hNq1R, mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * ((Nq : ℝ) + 1))]
    exact hb.trans_lt (by
      linarith only [(atomSpacing_bounds hNq1).1, atomSpacing_pos hNq1])
  set Mq := M / q
  set x_q := horizonProfileVector (fun k => if Mq < k then A / Real.sqrt k else 0) Nq
  have hred : completeWeilEnergy φ c N y_sp = completeWeilEnergy φ cq Nq x_q :=
    completeWeilEnergy_collar_spike_eq (M := M) hφ hsupp hM_int hc0 hq.pos hNq1 A
  have hnorm_eq : ‖y_sp‖ ^ 2 = ‖x_q‖ ^ 2 := by
    rw [← sum_primeHorizonExtension_sq y_sp, ← sum_primeHorizonExtension_sq x_q]
    have himg : (Icc 1 Nq).image (q * ·) ⊆ Icc 1 N := by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
      obtain ⟨hk1, hkN⟩ := mem_Icc.mp hk
      exact mem_Icc.mpr ⟨Nat.mul_pos hq.pos hk1,
        by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hq.pos).mp hkN⟩
    have hzero_off : ∀ n ∈ Icc 1 N, n ∉ (Icc 1 Nq).image (q * ·) →
        primeHorizonExtension y_sp n ^ 2 = 0 := by
      intro n hn hnot
      rw [primeHorizonExtension_coe y_sp ⟨n, hn⟩]
      change (if M < n ∧ q ∣ n then A * Real.sqrt q / Real.sqrt n else 0) ^ 2 = 0
      have hndvd : ¬(q ∣ n) := by
        intro ⟨k, hnk⟩
        apply hnot
        refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨?_, ?_⟩, hnk.symm⟩
        · by_contra hk0
          have hk0' : k = 0 := by omega
          rw [hk0', mul_zero] at hnk
          have := (mem_Icc.mp hn).1
          omega
        · exact (Nat.le_div_iff_mul_le hq.pos).mpr (by rw [mul_comm, ← hnk]; exact (mem_Icc.mp hn).2)
      rw [if_neg (fun h => hndvd h.2), zero_pow (by norm_num)]
    rw [← sum_subset himg hzero_off,
      sum_image (fun k₁ _ k₂ _ heq => Nat.eq_of_mul_eq_mul_left hq.pos heq)]
    refine sum_congr rfl fun k hk => ?_
    have hkN : q * k ∈ Icc 1 N := himg (mem_image_of_mem _ hk)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
    rw [primeHorizonExtension_coe y_sp ⟨q * k, hkN⟩, primeHorizonExtension_coe x_q ⟨k, hk⟩]
    change (if M < q * k ∧ q ∣ q * k then A * Real.sqrt q / Real.sqrt ((q * k : ℕ) : ℝ) else 0) ^ 2 =
      (if Mq < k then A / Real.sqrt k else 0) ^ 2
    have hiff : (M < q * k ∧ q ∣ q * k) ↔ Mq < k :=
      ⟨fun h => (Nat.div_lt_iff_lt_mul hq.pos).mpr (by rw [mul_comm]; exact h.1),
       fun h => ⟨by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul hq.pos).mp h, dvd_mul_right q k⟩⟩
    by_cases hcond : Mq < k
    · rw [if_pos (hiff.mpr hcond), if_pos hcond, Nat.cast_mul, Real.sqrt_mul hq0.le]
      field_simp [(Real.sqrt_pos.mpr hq0).ne', (Real.sqrt_pos.mpr hk0).ne']
    · rw [if_neg (fun h => hcond (hiff.mp h)), if_neg hcond]
  have hdec := completeWeilEnergy_eq_decomposition hφ hsupp hM_int hcq0 hNq1 hsep_q x_q
  rw [renormalizedPrimeEnergy, ← atomicWeilForm_primeHorizonExtension] at hdec
  have hself_log : Real.log (Nq : ℝ) + completeWeilSelfFinitePart φ cq =
      Real.log (N : ℝ) - Real.log c + completeWeilSelfFinitePart φ 1 := by
    rw [completeWeilSelfFinitePart_eq_at_one_sub_log φ hcq0]
    have hrat : (Nq : ℝ) / cq = (N : ℝ) / c := by
      dsimp only [cq]; field_simp [hc0.ne', hNq0.ne', hN0.ne']
    have hlog_eq : Real.log (Nq : ℝ) - Real.log cq = Real.log (N : ℝ) - Real.log c := by
      rw [← Real.log_div hNq0.ne' hcq0.ne', hrat, Real.log_div hN0.ne' hc0.ne']
    linarith only [hlog_eq]
  have hself_err : |completeWeilSelfError φ cq Nq| ≤ 2 := by
    have hb := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM_int hcq0 hNq1 hcq_le_Nq
    have hdiv : cq / (Nq : ℝ) ≤ 1 := (div_le_one hNq0).mpr hcq_le_Nq
    have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have he1 : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
      have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith only [he1, hsq, Real.exp_pos (1 / 2 : ℝ)]
    have hm := mul_le_mul hexp hdiv (by positivity) zero_le_two
    linarith only [hb, hm]
  have hprime_bd : |atomicWeilForm Nq (primeHorizonExtension x_q)| ≤
      topPrimeConstant * c * (1 + Real.log c) * ‖x_q‖ ^ 2 := by
    set w := c / (N : ℝ)
    set g := atomDilate φ w
    have hw : 0 < w := div_pos hc0 hN0
    have hcN_le : c ≤ N := by
      have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN
      linarith only [h4c, hLNR, hc0]
    have hw1 : w ≤ 1 := (div_le_one hN0).mpr hcN_le
    have hg : ContDiff ℝ 2 g := hφ.comp (contDiff_id.div_const _)
    have hgc : HasCompactSupport g := hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
    have hgs := tiltedUnitSpline_atom_support hw
    have hG : 0 < ∫ u, g u ^ 2 := by rw [integral_atomDilate_sq hw]; exact mul_pos hw hM_int
    have hnr0 : nonRatioForm g Nq (primeHorizonExtension x_q) = 0 := by
      apply SuccessorShellArithmetic.nonRatioForm_eq_zero_of_shellRange_eq_zero hgs
      unfold SuccessorShellArithmetic.shellRange
      apply Nat.floor_eq_zero.mpr
      have he1 : Real.exp w - 1 ≤ w * Real.exp w := by
        have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-w)) (Real.exp_pos w).le
        have h2 : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
        linarith only [h, h2]
      have hew : Real.exp w ≤ 3 :=
        (Real.exp_le_exp.mpr hw1).trans (by have := Real.exp_one_lt_d9; linarith)
      have hprod : (Nq : ℝ) * w = cq := by
        dsimp only [w, cq]; field_simp [hN0.ne']
      calc (Nq : ℝ) * (Real.exp w - 1) ≤ (Nq : ℝ) * (w * Real.exp w) :=
            mul_le_mul_of_nonneg_left he1 hNq0.le
        _ = cq * Real.exp w := by rw [← mul_assoc, hprod]
        _ ≤ (1 / 4) * 3 := mul_le_mul hcq_quarter hew (Real.exp_pos w).le (by norm_num)
        _ < 1 := by norm_num
    have hpr_eq : (∫ u, g u ^ 2) * atomicWeilForm Nq (primeHorizonExtension x_q) =
        primeSum (atomicTest Nq (primeHorizonExtension x_q) g) := by
      have h1 := primeSum_atomicTest_eq_ratio_add hg.continuous hgc hgs hw.le Nq
        (primeHorizonExtension x_q)
      rw [hnr0, add_zero] at h1
      exact h1.symm
    have hshift : (fun u => atomicTest N (primeHorizonExtension y_sp) g (u + Real.log q)) =
        atomicTest Nq (primeHorizonExtension x_q) g := by
      funext u
      unfold atomicTest
      have himg : (Icc 1 Nq).image (q * ·) ⊆ Icc 1 N := by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
        obtain ⟨hk1, hkN⟩ := mem_Icc.mp hk
        exact mem_Icc.mpr ⟨Nat.mul_pos hq.pos hk1,
          by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hq.pos).mp hkN⟩
      have hzero_off : ∀ n ∈ Icc 1 N, n ∉ (Icc 1 Nq).image (q * ·) →
          primeHorizonExtension y_sp n * g (u + Real.log q - Real.log n) = 0 := by
        intro n hn hnot
        rw [primeHorizonExtension_coe y_sp ⟨n, hn⟩]
        change (if M < n ∧ q ∣ n then A * Real.sqrt q / Real.sqrt n else 0) * _ = 0
        have hndvd : ¬(q ∣ n) := by
          intro ⟨k, hnk⟩
          apply hnot
          refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨?_, ?_⟩, hnk.symm⟩
          · by_contra hk0
            have hk0' : k = 0 := by omega
            rw [hk0', mul_zero] at hnk
            have := (mem_Icc.mp hn).1
            omega
          · exact (Nat.le_div_iff_mul_le hq.pos).mpr (by rw [mul_comm, ← hnk]; exact (mem_Icc.mp hn).2)
        rw [if_neg (fun h => hndvd h.2), zero_mul]
      rw [← sum_subset himg hzero_off,
        sum_image (fun k₁ _ k₂ _ heq => Nat.eq_of_mul_eq_mul_left hq.pos heq)]
      refine sum_congr rfl fun k hk => ?_
      have hkN : q * k ∈ Icc 1 N := himg (mem_image_of_mem _ hk)
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
      rw [primeHorizonExtension_coe y_sp ⟨q * k, hkN⟩, primeHorizonExtension_coe x_q ⟨k, hk⟩]
      change (if M < q * k ∧ q ∣ q * k then A * Real.sqrt q / Real.sqrt ((q * k : ℕ) : ℝ) else 0) *
          g (u + Real.log q - Real.log ((q * k : ℕ) : ℝ)) =
        (if Mq < k then A / Real.sqrt k else 0) * g (u - Real.log k)
      have hiff : (M < q * k ∧ q ∣ q * k) ↔ Mq < k :=
        ⟨fun h => (Nat.div_lt_iff_lt_mul hq.pos).mpr (by rw [mul_comm]; exact h.1),
         fun h => ⟨by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul hq.pos).mp h, dvd_mul_right q k⟩⟩
      have hlog : u + Real.log q - Real.log ((q * k : ℕ) : ℝ) = u - Real.log k := by
        rw [Nat.cast_mul, Real.log_mul hq0.ne' hk0.ne']; ring
      rw [hlog]
      by_cases hcond : Mq < k
      · rw [if_pos (hiff.mpr hcond), if_pos hcond]; congr 1
        rw [Nat.cast_mul, Real.sqrt_mul hq0.le]
        field_simp [(Real.sqrt_pos.mpr hq0).ne', (Real.sqrt_pos.mpr hk0).ne']
      · rw [if_neg (fun h => hcond (hiff.mp h)), if_neg hcond, zero_mul]
    have hpr_sp : primeSum (atomicTest Nq (primeHorizonExtension x_q) g) =
        primeSum (atomicTest N (primeHorizonExtension y_sp) g) := by
      rw [← hshift, primeSum_comp_add_right]
    have hMltN : M < N := Nat.div_lt_self (by omega) (by omega)
    have hy0 : ∀ n ∈ Icc 1 M, primeHorizonExtension y_sp n = 0 := by
      intro n hn
      have hnN : n ∈ Icc 1 N := mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
        (mem_Icc.mp hn).2.trans (Nat.div_le_self N _)⟩
      rw [primeHorizonExtension_coe y_sp ⟨n, hnN⟩]
      exact if_neg (fun h => Nat.not_lt.mpr (mem_Icc.mp hn).2 h.1)
    have htop := abs_primeSum_top_le hg.continuous hgc hgs hw.le hMltN
      (primeHorizonExtension y_sp) hy0
    have hrow := topPrimeRow_le hc1 hLN
    rw [sum_primeHorizonExtension_sq, hnorm_eq] at htop
    have hprod_bd : (∫ u, g u ^ 2) * |atomicWeilForm Nq (primeHorizonExtension x_q)| ≤
        (∫ u, g u ^ 2) * (topPrimeConstant * c * (1 + Real.log c) * ‖x_q‖ ^ 2) := by
      rw [← abs_of_pos hG, ← abs_mul, hpr_eq, hpr_sp, abs_of_pos hG]
      exact htop.trans ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrow hG.le) (sq_nonneg ‖x_q‖)).trans_eq (mul_assoc _ _ _))
    exact le_of_mul_le_mul_left hprod_bd hG
  have hcent_bd : |⟪Matrix.toEuclideanLin
      (fullWeilCenterMatrix (completeWeilPoleShift φ cq) Nq) x_q, x_q⟫| ≤
      cq * (3 * Real.log (N : ℝ) + 7) * ‖x_q‖ ^ 2 :=
    abs_fullWeilCenterMatrix_inner_le hφ hsupp hM_int hcq0 hNq1 (Nat.div_le_self N q) x_q
  clear_value x_q Mq
  have hcross_bd := abs_fullWeilCrossErrorMatrix_inner_le hφ hsupp hM_int hcq0 hcq1 hNq1 x_q
  have hpole_err_bd := abs_fullWeilPoleErrorMatrix_inner_le hφ hsupp hM_int hcq0 hcq1 hNq1 x_q
  rw [hred, hnorm_eq]
  have hdiff : completeWeilEnergy φ cq Nq x_q -
      (Real.log (N : ℝ) - Real.log c + completeWeilSelfFinitePart φ 1 -
        Real.eulerMascheroniConstant) * ‖x_q‖ ^ 2 =
      -atomicWeilForm Nq (primeHorizonExtension x_q) +
        completeWeilSelfError φ cq Nq * ‖x_q‖ ^ 2 +
        ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ cq) Nq) x_q, x_q⟫ -
        ⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ cq Nq) x_q, x_q⟫ +
        ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ cq Nq) x_q, x_q⟫ := by
    linarith only [hdec, mul_eq_mul_right_iff.mpr (Or.inl hself_log)]
  rw [hdiff]
  have hself_mul : |completeWeilSelfError φ cq Nq * ‖x_q‖ ^ 2| ≤ 2 * ‖x_q‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖x_q‖)]
    exact mul_le_mul_of_nonneg_right hself_err (sq_nonneg _)
  have a1 := abs_add_le
    (-atomicWeilForm Nq (primeHorizonExtension x_q) +
      completeWeilSelfError φ cq Nq * ‖x_q‖ ^ 2 +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ cq) Nq) x_q, x_q⟫ -
      ⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ cq Nq) x_q, x_q⟫)
    ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ cq Nq) x_q, x_q⟫
  have a2 := abs_sub
    (-atomicWeilForm Nq (primeHorizonExtension x_q) +
      completeWeilSelfError φ cq Nq * ‖x_q‖ ^ 2 +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ cq) Nq) x_q, x_q⟫)
    ⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ cq Nq) x_q, x_q⟫
  have a3 := abs_add_le
    (-atomicWeilForm Nq (primeHorizonExtension x_q) +
      completeWeilSelfError φ cq Nq * ‖x_q‖ ^ 2)
    ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ cq) Nq) x_q, x_q⟫
  have a4 := abs_add_le (-atomicWeilForm Nq (primeHorizonExtension x_q))
    (completeWeilSelfError φ cq Nq * ‖x_q‖ ^ 2)
  rw [abs_neg] at a4
  linarith only [a1, a2, a3, a4, hprime_bd, hself_mul, hcent_bd, hcross_bd, hpole_err_bd]

private theorem collar_spike_energy_sub_log_le
    {c L q_r cq H_cut S_h E_sp ysp_sq : ℝ}
    (hc1 : 1 ≤ c) (hL1 : 1 ≤ L) (hq2 : 2 ≤ q_r)
    (hcq0 : 0 < cq) (hcq_quarter : cq ≤ 1 / 4)
    (hS_nn : 0 ≤ S_h) (hysp_nn : 0 ≤ ysp_sq)
    (hlog4H_nn : 0 ≤ Real.log (4 * H_cut))
    (hL_256_big : (4 : ℝ) ^ (14 : ℕ) ≤ L ^ (7 / 32 : ℝ))
    (hc_le_9_64 : c ≤ L ^ (9 / 64 : ℝ))
    (hlogc_64 : Real.log c ≤ L ^ (1 / 64 : ℝ))
    (hq_ge : L ^ (13 / 32 : ℝ) ≤ q_r)
    (hcq_rpow : cq ≤ 1 / L ^ (17 / 64 : ℝ))
    (hCt_64 : |topPrimeConstant| + 1 ≤ L ^ (1 / 64 : ℝ))
    (hCs_64 : |completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.eulerMascheroniConstant| + 1 ≤
      L ^ (1 / 64 : ℝ))
    (hCerr_64 : 4 * atomCrossErrorConstant tiltedUnitSpline (1 / 2) +
      2 * atomPoleMomentErrorConstant tiltedUnitSpline + 4 ≤ L ^ (1 / 64 : ℝ))
    (h4_64 : 4 ≤ L ^ (1 / 64 : ℝ))
    (hlog4H_64 : Real.log (4 * H_cut) ≤ L ^ (1 / 64 : ℝ))
    (hharm_lo : Real.log c ≤ S_h)
    (hharm_hi : S_h ≤ Real.log c + Real.log (4 * H_cut))
    (hysp_sq_eq : ysp_sq = (q_r / ((q_r - 1) * L)) * S_h)
    (hysp_sq_le : ysp_sq ≤ 4 * L ^ (1 / 64 : ℝ) / L)
    (hsp : |E_sp - (L - Real.log c + completeWeilSelfFinitePart tiltedUnitSpline 1 -
        Real.eulerMascheroniConstant) * ysp_sq| ≤
      (topPrimeConstant * c * (1 + Real.log c) +
        cq * (3 * L + 7) +
        4 * atomCrossErrorConstant tiltedUnitSpline cq * cq ^ 2 +
        2 * atomPoleMomentErrorConstant tiltedUnitSpline * cq ^ 2 + 2) * ysp_sq) :
    |E_sp - Real.log c| ≤ Real.log (4 * H_cut) + 6 := by
  let φ := tiltedUnitSpline
  have hM_int := integral_tiltedUnitSpline_sq_pos
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hqm1_pos : 0 < q_r - 1 := by linarith only [hq2]
  have hmain_sub : |(L - Real.log c + completeWeilSelfFinitePart φ 1 -
      Real.eulerMascheroniConstant) * ysp_sq - Real.log c| ≤
      Real.log (4 * H_cut) + 3 := by
    have hL_ysp : L * ysp_sq = S_h + S_h / (q_r - 1) := by
      rw [hysp_sq_eq]; field_simp [hqm1_pos.ne', hL0.ne']; ring
    have hSh_sub : |S_h - Real.log c| ≤ Real.log (4 * H_cut) := by
      rw [abs_le]
      exact ⟨by linarith only [hharm_lo, hlog4H_nn], by linarith only [hharm_hi]⟩
    have hSh_qm1 : |S_h / (q_r - 1)| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hS_nn hqm1_pos.le), div_le_one hqm1_pos]
      have hS_le : S_h ≤ 2 * L ^ (1 / 64 : ℝ) := by
        linarith only [hharm_hi, hlogc_64, hlog4H_64]
      have hqm1_ge : q_r / 2 ≤ q_r - 1 := by linarith only [hq2]
      have h2_le_q2 : 2 * L ^ (1 / 64 : ℝ) ≤ q_r / 2 := by
        have h4_le : 4 * L ^ (1 / 64 : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
          calc 4 * L ^ (1 / 64 : ℝ)
              ≤ L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ) :=
                mul_le_mul_of_nonneg_right h4_64 (Real.rpow_nonneg hL0.le _)
            _ = L ^ (2 / 64 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
            _ ≤ L ^ (13 / 32 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        linarith only [h4_le, hq_ge]
      linarith only [hS_le, h2_le_q2, hqm1_ge]
    have hrem_ysp : |(-Real.log c + completeWeilSelfFinitePart φ 1 -
        Real.eulerMascheroniConstant) * ysp_sq| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg hysp_nn]
      have hc_abs : |-Real.log c + completeWeilSelfFinitePart φ 1 -
          Real.eulerMascheroniConstant| ≤ 2 * L ^ (1 / 64 : ℝ) := by
        have htri : |-Real.log c + completeWeilSelfFinitePart φ 1 -
            Real.eulerMascheroniConstant| ≤
            |Real.log c| + |completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant| := by
          rw [show -Real.log c + completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant =
            -Real.log c + (completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant) by ring]
          exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
        rw [abs_of_nonneg (Real.log_nonneg hc1)] at htri
        linarith only [htri, hlogc_64, hCs_64]
      calc |-Real.log c + completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant| * ysp_sq
          ≤ (2 * L ^ (1 / 64 : ℝ)) * (4 * L ^ (1 / 64 : ℝ) / L) :=
            mul_le_mul hc_abs hysp_sq_le hysp_nn (by positivity)
        _ = 8 / L ^ (31 / 32 : ℝ) := by
            rw [show (2 * L ^ (1 / 64 : ℝ)) * (4 * L ^ (1 / 64 : ℝ) / L) =
              8 * (L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ) / L) by ring,
              ← Real.rpow_add hL0, ← Real.rpow_sub_one hL0.ne']
            have hexp : (1 / 64 + 1 / 64 - 1 : ℝ) = -(31 / 32) := by norm_num
            rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
        _ ≤ 2 := by
            have h1 : 8 / L ^ (31 / 32 : ℝ) ≤ 1 := by
              rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
              exact (by norm_num : (8 : ℝ) ≤ (4 : ℝ) ^ (14 : ℕ)).trans
                (hL_256_big.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
            linarith
    have hrew : (L - Real.log c + completeWeilSelfFinitePart φ 1 -
        Real.eulerMascheroniConstant) * ysp_sq - Real.log c =
        (S_h - Real.log c) + S_h / (q_r - 1) +
          (-Real.log c + completeWeilSelfFinitePart φ 1 -
            Real.eulerMascheroniConstant) * ysp_sq := by
      calc (L - Real.log c + completeWeilSelfFinitePart φ 1 -
            Real.eulerMascheroniConstant) * ysp_sq - Real.log c
          = L * ysp_sq + (-Real.log c + completeWeilSelfFinitePart φ 1 -
            Real.eulerMascheroniConstant) * ysp_sq - Real.log c := by ring
        _ = _ := by rw [hL_ysp]; ring
    rw [hrew]
    have b1 := abs_add_le ((S_h - Real.log c) + S_h / (q_r - 1))
      ((-Real.log c + completeWeilSelfFinitePart φ 1 -
        Real.eulerMascheroniConstant) * ysp_sq)
    have b2 := abs_add_le (S_h - Real.log c) (S_h / (q_r - 1))
    linarith only [b1, b2, hSh_sub, hSh_qm1, hrem_ysp]
  have herr_sp : (topPrimeConstant * c * (1 + Real.log c) +
      cq * (3 * L + 7) +
      4 * atomCrossErrorConstant φ cq * cq ^ 2 +
      2 * atomPoleMomentErrorConstant φ * cq ^ 2 + 2) * ysp_sq ≤ 3 := by
    have ht_top : topPrimeConstant * c * (1 + Real.log c) ≤ 2 * L ^ (11 / 64 : ℝ) := by
      have hCt : topPrimeConstant ≤ |topPrimeConstant| + 1 := by
        linarith [le_abs_self topPrimeConstant]
      have h1lc : 1 + Real.log c ≤ 2 * L ^ (1 / 64 : ℝ) := by
        have h1 : 1 ≤ L ^ (1 / 64 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
        linarith only [h1, hlogc_64]
      calc topPrimeConstant * c * (1 + Real.log c)
          ≤ L ^ (1 / 64 : ℝ) * L ^ (9 / 64 : ℝ) * (2 * L ^ (1 / 64 : ℝ)) := by
            have h1 := mul_le_mul (hCt.trans hCt_64) hc_le_9_64 hc0.le (Real.rpow_nonneg hL0.le _)
            by_cases htp : 0 ≤ topPrimeConstant
            · exact mul_le_mul h1 h1lc (by linarith [Real.log_nonneg hc1]) (by positivity)
            · have hneg : topPrimeConstant * c * (1 + Real.log c) ≤ 0 :=
                mul_nonpos_of_nonpos_of_nonneg
                  (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge htp) hc0.le)
                  (by linarith [Real.log_nonneg hc1])
              exact hneg.trans (by positivity)
        _ = 2 * L ^ (11 / 64 : ℝ) := by
            rw [show L ^ (1 / 64 : ℝ) * L ^ (9 / 64 : ℝ) * (2 * L ^ (1 / 64 : ℝ)) =
              2 * (L ^ (1 / 64 : ℝ) * L ^ (9 / 64 : ℝ) * L ^ (1 / 64 : ℝ)) by ring,
              ← Real.rpow_add hL0, ← Real.rpow_add hL0]
            norm_num
    have ht_cent : cq * (3 * L + 7) ≤ 10 * L ^ (47 / 64 : ℝ) := by
      have h3L7 : 3 * L + 7 ≤ 10 * L := by linarith only [hL1]
      calc cq * (3 * L + 7)
          ≤ (1 / L ^ (17 / 64 : ℝ)) * (10 * L) :=
            mul_le_mul hcq_rpow h3L7 (by positivity) (by positivity)
        _ = 10 * L ^ (47 / 64 : ℝ) := by
            rw [show (1 / L ^ (17 / 64 : ℝ)) * (10 * L) =
              10 * (L ^ (1 : ℝ) / L ^ (17 / 64 : ℝ)) by rw [Real.rpow_one]; ring,
              ← Real.rpow_sub hL0]
            norm_num
    have ht_err : 4 * atomCrossErrorConstant φ cq * cq ^ 2 +
        2 * atomPoleMomentErrorConstant φ * cq ^ 2 + 2 ≤ L ^ (1 / 64 : ℝ) := by
      have hcross_mono : atomCrossErrorConstant φ cq ≤ atomCrossErrorConstant φ (1 / 2) := by
        unfold atomCrossErrorConstant
        refine div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left ?_ hM_int.le)
        exact pow_le_pow_left₀ (by norm_num) (by linarith only [hcq_quarter]) 2
      have hcq2_1 : cq ^ 2 ≤ 1 := by nlinarith only [hcq0, hcq_quarter]
      have hpm_nn : 0 ≤ atomPoleMomentErrorConstant φ := by
        unfold atomPoleMomentErrorConstant; positivity
      have k1 : 4 * atomCrossErrorConstant φ cq * cq ^ 2 ≤
          4 * atomCrossErrorConstant φ (1 / 2) := by
        calc 4 * atomCrossErrorConstant φ cq * cq ^ 2
            ≤ 4 * atomCrossErrorConstant φ (1 / 2) * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hcross_mono (by norm_num)) hcq2_1
                (sq_nonneg _) (mul_nonneg (by norm_num) (atomCrossErrorConstant_nonneg _ _))
          _ = _ := mul_one _
      have k2 : 2 * atomPoleMomentErrorConstant φ * cq ^ 2 ≤
          2 * atomPoleMomentErrorConstant φ :=
        (mul_le_mul_of_nonneg_left hcq2_1 (by positivity)).trans_eq (mul_one _)
      linarith only [k1, k2, hCerr_64]
    have h11_47 : L ^ (11 / 64 : ℝ) ≤ L ^ (47 / 64 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h1_47 : L ^ (1 / 64 : ℝ) ≤ L ^ (47 / 64 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hcoef_tot : topPrimeConstant * c * (1 + Real.log c) +
        cq * (3 * L + 7) +
        4 * atomCrossErrorConstant φ cq * cq ^ 2 +
        2 * atomPoleMomentErrorConstant φ * cq ^ 2 + 2 ≤ 13 * L ^ (47 / 64 : ℝ) := by
      linarith only [ht_top, ht_cent, ht_err, h11_47, h1_47]
    calc (topPrimeConstant * c * (1 + Real.log c) +
          cq * (3 * L + 7) +
          4 * atomCrossErrorConstant φ cq * cq ^ 2 +
          2 * atomPoleMomentErrorConstant φ * cq ^ 2 + 2) * ysp_sq
        ≤ (13 * L ^ (47 / 64 : ℝ)) * (4 * L ^ (1 / 64 : ℝ) / L) := by
          by_cases hpos_c : 0 ≤ topPrimeConstant * c * (1 + Real.log c) +
              cq * (3 * L + 7) + 4 * atomCrossErrorConstant φ cq * cq ^ 2 +
              2 * atomPoleMomentErrorConstant φ * cq ^ 2 + 2
          · exact mul_le_mul hcoef_tot hysp_sq_le hysp_nn (by positivity)
          · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hpos_c) hysp_nn).trans
              (by positivity)
      _ = 52 / L ^ (1 / 4 : ℝ) := by
          rw [show (13 * L ^ (47 / 64 : ℝ)) * (4 * L ^ (1 / 64 : ℝ) / L) =
            52 * (L ^ (47 / 64 : ℝ) * L ^ (1 / 64 : ℝ) / L) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_sub_one hL0.ne']
          have hexp : (47 / 64 + 1 / 64 - 1 : ℝ) = -(1 / 4) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      _ ≤ 3 := by
          have h1 : 52 / L ^ (1 / 4 : ℝ) ≤ 1 := by
            rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
            exact (by norm_num : (52 : ℝ) ≤ (4 : ℝ) ^ (14 : ℕ)).trans
              (hL_256_big.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
          linarith
  have htri := abs_add_le
    (E_sp - (L - Real.log c + completeWeilSelfFinitePart φ 1 -
      Real.eulerMascheroniConstant) * ysp_sq)
    ((L - Real.log c + completeWeilSelfFinitePart φ 1 -
      Real.eulerMascheroniConstant) * ysp_sq - Real.log c)
  rw [sub_add_sub_cancel] at htri
  linarith only [htri, hsp, herr_sp, hmain_sub]

private theorem collar_garding_transfer_abs_sub_le
    {N M : ℕ} {c L B_col H_cut : ℝ}
    {y_z y_sp y_rem : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hc1 : 1 ≤ c) (hL1 : 1 ≤ L) (hBcol_pos : 0 < B_col)
    (hL_3_256 : (4 : ℝ) ^ (15 : ℕ) ≤ L ^ (3 / 256 : ℝ))
    (hc_le_9_64 : c ≤ L ^ (9 / 64 : ℝ))
    (hc_97 : c ≤ L ^ (97 / 256 : ℝ))
    (hlogc_256 : Real.log c ≤ L ^ (1 / 256 : ℝ))
    (hBcol_256 : B_col ≤ L ^ (1 / 256 : ℝ))
    (hlog4H_6_le : Real.log (4 * H_cut) + 6 ≤ L ^ (1 / 256 : ℝ))
    (h3_256 : 3 ≤ L ^ (1 / 256 : ℝ))
    (hy_decomp : y_z = y_sp - y_rem)
    (hvan_lin : ∀ (α β : ℝ) (n : ℕ), n ≤ M →
      primeHorizonExtension (α • y_sp + β • y_rem) n = 0)
    (hgard_col : ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (∀ n, n ≤ M → primeHorizonExtension w n = 0) →
      0 ≤ completeWeilEnergy tiltedUnitSpline c N w + B_col * c * ‖w‖ ^ 2)
    (hysp_sq_le : ‖y_sp‖ ^ 2 ≤ 4 * L ^ (1 / 64 : ℝ) / L)
    (hyrem_sq : ‖y_rem‖ ^ 2 ≤ (8 + 2 * 1170 ^ 2) / L ^ (359 / 256 : ℝ))
    (hEyrem_rpow : |completeWeilEnergy tiltedUnitSpline c N y_rem| ≤ 1 / L ^ (2 / 256 : ℝ))
    (hEsp_approx : |completeWeilEnergy tiltedUnitSpline c N y_sp - Real.log c| ≤
      Real.log (4 * H_cut) + 6) :
    |completeWeilEnergy tiltedUnitSpline c N y_z - Real.log c| ≤ Real.log (4 * H_cut) + 12 := by
  let φ := tiltedUnitSpline
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have h1_64_ge : L ^ (1 / 256 : ℝ) ≤ L ^ (1 / 64 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hBcol_ysp : B_col * c * ‖y_sp‖ ^ 2 ≤ 1 := by
    have hB_64 : B_col ≤ L ^ (1 / 64 : ℝ) := hBcol_256.trans h1_64_ge
    calc B_col * c * ‖y_sp‖ ^ 2
        ≤ L ^ (1 / 64 : ℝ) * L ^ (9 / 64 : ℝ) * (4 * L ^ (1 / 64 : ℝ) / L) :=
          mul_le_mul (mul_le_mul hB_64 hc_le_9_64 hc0.le (by positivity))
            hysp_sq_le (sq_nonneg _) (by positivity)
      _ = 4 / L ^ (53 / 64 : ℝ) := by
          rw [show L ^ (1 / 64 : ℝ) * L ^ (9 / 64 : ℝ) * (4 * L ^ (1 / 64 : ℝ) / L) =
            4 * (L ^ (1 / 64 : ℝ) * L ^ (9 / 64 : ℝ) * L ^ (1 / 64 : ℝ) / L) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_sub_one hL0.ne']
          have hexp : (1 / 64 + 9 / 64 + 1 / 64 - 1 : ℝ) = -(53 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          exact (by norm_num : (4 : ℝ) ≤ (4 : ℝ) ^ (15 : ℕ)).trans
            (hL_3_256.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
  have hBcol_yrem : B_col * c * ‖y_rem‖ ^ 2 ≤ 1 / L ^ (2 / 256 : ℝ) := by
    calc B_col * c * ‖y_rem‖ ^ 2
        ≤ L ^ (1 / 256 : ℝ) * L ^ (97 / 256 : ℝ) *
            ((8 + 2 * 1170 ^ 2) / L ^ (359 / 256 : ℝ)) :=
          mul_le_mul (mul_le_mul hBcol_256 hc_97 hc0.le (by positivity))
            hyrem_sq (sq_nonneg _) (by positivity)
      _ = ((8 + 2 * 1170 ^ 2) / L ^ (259 / 256 : ℝ)) * (1 / L ^ (2 / 256 : ℝ)) := by
          rw [show L ^ (1 / 256 : ℝ) * L ^ (97 / 256 : ℝ) *
              ((8 + 2 * 1170 ^ 2) / L ^ (359 / 256 : ℝ)) =
            (8 + 2 * 1170 ^ 2) *
              (L ^ (1 / 256 : ℝ) * L ^ (97 / 256 : ℝ) / L ^ (359 / 256 : ℝ)) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_sub hL0]
          have hexp : (1 / 256 + 97 / 256 - 359 / 256 : ℝ) = -(261 / 256) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv, div_mul_div_comm, mul_one,
            ← Real.rpow_add hL0]
          norm_num
      _ ≤ 1 * (1 / L ^ (2 / 256 : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          exact (by norm_num : (8 + 2 * 1170 ^ 2 : ℝ) ≤ (4 : ℝ) ^ (15 : ℕ)).trans
            (hL_3_256.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
      _ = 1 / L ^ (2 / 256 : ℝ) := one_mul _
  have hBcol_inner : |B_col * c * ⟪y_sp, y_rem⟫| ≤ 1 := by
    have hcs := abs_real_inner_le_norm y_sp y_rem
    have h1 : |B_col * c * ⟪y_sp, y_rem⟫| ≤ B_col * c * (‖y_sp‖ * ‖y_rem‖) := by
      rw [abs_mul, abs_of_pos (mul_pos hBcol_pos hc0)]
      exact mul_le_mul_of_nonneg_left hcs (by positivity)
    have hrem1 : 1 / L ^ (2 / 256 : ℝ) ≤ 1 :=
      div_le_one_of_le₀ (Real.one_le_rpow hL1 (by norm_num)) (by positivity)
    have hsq : |B_col * c * ⟪y_sp, y_rem⟫| ^ 2 ≤ 1 := by
      calc |B_col * c * ⟪y_sp, y_rem⟫| ^ 2
          ≤ (B_col * c * (‖y_sp‖ * ‖y_rem‖)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = (B_col * c * ‖y_sp‖ ^ 2) * (B_col * c * ‖y_rem‖ ^ 2) := by ring
        _ ≤ 1 * 1 := mul_le_mul hBcol_ysp (hBcol_yrem.trans hrem1) (by positivity) zero_le_one
        _ = 1 := one_mul 1
    nlinarith only [hsq, abs_nonneg (B_col * c * ⟪y_sp, y_rem⟫)]
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  have hquad_lin : ∀ α β : ℝ,
      completeWeilEnergy φ c N (α • y_sp + β • y_rem) +
        B_col * c * ‖α • y_sp + β • y_rem‖ ^ 2 =
      α ^ 2 * (completeWeilEnergy φ c N y_sp + B_col * c * ‖y_sp‖ ^ 2) +
        β ^ 2 * (completeWeilEnergy φ c N y_rem + B_col * c * ‖y_rem‖ ^ 2) +
        2 * α * β * (⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) y_sp, y_rem⟫ +
          B_col * c * ⟪y_sp, y_rem⟫) := by
    intro α β
    have he : completeWeilEnergy φ c N (α • y_sp + β • y_rem) =
        α ^ 2 * completeWeilEnergy φ c N y_sp +
          2 * α * β * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) y_sp, y_rem⟫ +
          β ^ 2 * completeWeilEnergy φ c N y_rem := by
      unfold completeWeilEnergy
      rw [map_add, map_smul, map_smul, inner_add_left, inner_add_right, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
        hsym y_rem y_sp, real_inner_comm y_rem]
      ring
    have hn : ‖α • y_sp + β • y_rem‖ ^ 2 =
        α ^ 2 * ‖y_sp‖ ^ 2 + 2 * α * β * ⟪y_sp, y_rem⟫ + β ^ 2 * ‖y_rem‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [he, hn]; ring
  set t := 1 / L ^ (1 / 256 : ℝ)
  set s := L ^ (1 / 256 : ℝ)
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hL0 _
  have hts : t * s = 1 := one_div_mul_cancel hs_pos.ne'
  have hs2 : s ^ 2 = L ^ (2 / 256 : ℝ) := by
    dsimp only [s]
    rw [← Real.rpow_natCast (L ^ (1 / 256 : ℝ)) 2, ← Real.rpow_mul hL0.le]
    norm_num
  have ht2_sp : t ^ 2 * (completeWeilEnergy φ c N y_sp + B_col * c * ‖y_sp‖ ^ 2) ≤ 1 := by
    have hEsp_up : completeWeilEnergy φ c N y_sp ≤ 2 * s := by
      have h1 : completeWeilEnergy φ c N y_sp ≤ Real.log c + Real.log (4 * H_cut) + 6 := by
        linarith only [(abs_le.mp hEsp_approx).2]
      dsimp only [s]
      linarith only [h1, hlogc_256, hlog4H_6_le]
    have h1_le_s : (1 : ℝ) ≤ s := by dsimp only [s] at *; linarith only [h3_256]
    have hsum_s2 : completeWeilEnergy φ c N y_sp + B_col * c * ‖y_sp‖ ^ 2 ≤ s ^ 2 := by
      calc completeWeilEnergy φ c N y_sp + B_col * c * ‖y_sp‖ ^ 2
          ≤ 2 * s + 1 := add_le_add hEsp_up hBcol_ysp
        _ ≤ 3 * s := by linarith only [h1_le_s]
        _ ≤ s * s := mul_le_mul_of_nonneg_right h3_256 hs_pos.le
        _ = s ^ 2 := (sq s).symm
    calc t ^ 2 * (completeWeilEnergy φ c N y_sp + B_col * c * ‖y_sp‖ ^ 2)
        ≤ t ^ 2 * s ^ 2 := mul_le_mul_of_nonneg_left hsum_s2 (sq_nonneg t)
      _ = (t * s) ^ 2 := (mul_pow t s 2).symm
      _ = 1 := by rw [hts, one_pow]
  have hs2_rem : s ^ 2 * (completeWeilEnergy φ c N y_rem + B_col * c * ‖y_rem‖ ^ 2) ≤ 2 := by
    have hErem_up : completeWeilEnergy φ c N y_rem ≤ 1 / L ^ (2 / 256 : ℝ) :=
      (le_abs_self _).trans hEyrem_rpow
    calc s ^ 2 * (completeWeilEnergy φ c N y_rem + B_col * c * ‖y_rem‖ ^ 2)
        ≤ L ^ (2 / 256 : ℝ) * (1 / L ^ (2 / 256 : ℝ) + 1 / L ^ (2 / 256 : ℝ)) := by
          rw [hs2]
          exact mul_le_mul_of_nonneg_left (add_le_add hErem_up hBcol_yrem) (by positivity)
      _ = 2 := by field_simp [(Real.rpow_pos_of_pos hL0 (2 / 256 : ℝ)).ne']; ring
  have hcross_abs : 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) y_sp, y_rem⟫| ≤ 5 := by
    set X := ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) y_sp, y_rem⟫
    set Y := B_col * c * ⟪y_sp, y_rem⟫
    have hg_plus := hgard_col (t • y_sp + s • y_rem) (hvan_lin t s)
    have hg_minus := hgard_col (t • y_sp + (-s) • y_rem) (hvan_lin t (-s))
    rw [hquad_lin t s] at hg_plus
    rw [hquad_lin t (-s), neg_sq] at hg_minus
    have hm1 : 2 * t * s * (X + Y) = 2 * (X + Y) := by
      calc 2 * t * s * (X + Y) = 2 * (t * s) * (X + Y) := by ring
        _ = 2 * (X + Y) := by rw [hts, mul_one]
    have hm2 : 2 * t * (-s) * (X + Y) = -(2 * (X + Y)) := by
      calc 2 * t * (-s) * (X + Y) = -(2 * (t * s) * (X + Y)) := by ring
        _ = -(2 * (X + Y)) := by rw [hts, mul_one]
    rw [hm1] at hg_plus
    rw [hm2] at hg_minus
    have hXY : 2 * |X + Y| ≤ 3 := by
      rw [← abs_of_pos (zero_lt_two (α := ℝ)), ← abs_mul, abs_le]
      exact ⟨by linarith only [hg_plus, ht2_sp, hs2_rem],
        by linarith only [hg_minus, ht2_sp, hs2_rem]⟩
    have htri' : |X| ≤ |X + Y| + |Y| := by
      calc |X| = |(X + Y) + (-Y)| := by ring_nf
        _ ≤ |X + Y| + |-Y| := abs_add_le _ _
        _ = |X + Y| + |Y| := by rw [abs_neg]
    linarith only [hXY, hBcol_inner, htri']
  have hyz_sub_sp : |completeWeilEnergy φ c N y_z - completeWeilEnergy φ c N y_sp| ≤ 6 := by
    have hdiff : completeWeilEnergy φ c N y_z - completeWeilEnergy φ c N y_sp =
        -(2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) y_sp, y_rem⟫) +
          completeWeilEnergy φ c N y_rem := by
      rw [hy_decomp]
      unfold completeWeilEnergy
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym y_rem y_sp,
        real_inner_comm y_rem]
      ring
    have hErem1 : |completeWeilEnergy φ c N y_rem| ≤ 1 :=
      hEyrem_rpow.trans (div_le_one_of_le₀ (Real.one_le_rpow hL1 (by norm_num)) (by positivity))
    rw [hdiff]
    have htri := abs_add_le
      (-(2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) y_sp, y_rem⟫))
      (completeWeilEnergy φ c N y_rem)
    rw [abs_neg, abs_mul, abs_two] at htri
    linarith only [htri, hcross_abs, hErem1]
  have hfin := abs_add_le
    (completeWeilEnergy φ c N y_z - completeWeilEnergy φ c N y_sp)
    (completeWeilEnergy φ c N y_sp - Real.log c)
  rw [sub_add_sub_cancel] at hfin
  linarith only [hfin, hyz_sub_sp, hEsp_approx]

private theorem collar_quasimode_decomp_and_spike_norm
    {N Lc q : ℕ} (hq_pr : q.Prime) (hLc3 : 3 ≤ Lc)
    {c H_cut : ℝ} (hc0 : 0 < c) (_hH_pos : 0 < H_cut)
    (hL0 : 0 < Real.log (N : ℝ))
    (h256c : 256 * Real.exp 2 * c ≤ Lc) (hLc_le_Hc : (Lc : ℝ) ≤ H_cut * c)
    (hqLc_le_N : 4 * q * Lc ≤ N)
    (hMq1 : 1 ≤ (N / Lc) / q) (hMq_lt_Nq : (N / Lc) / q < N / q)
    (hlogc_64 : Real.log c ≤ Real.log (N : ℝ) ^ (1 / 64 : ℝ))
    (hlog4H_64 : Real.log (4 * H_cut) ≤ Real.log (N : ℝ) ^ (1 / 64 : ℝ))
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    let L := Real.log (N : ℝ)
    let M := N / Lc
    let A_sp : ℝ := Real.sqrt ((q : ℝ) / (((q : ℝ) - 1) * L))
    let B_bg : ℝ := 1 / Real.sqrt (((q : ℝ) - 1) * L)
    let y_sp := horizonProfileVector
      (fun n => if M < n ∧ q ∣ n then A_sp * Real.sqrt q / Real.sqrt n else 0) N
    let y_bg := horizonProfileVector (fun n => if M < n then B_bg / Real.sqrt n else 0) N
    horizonCollarVector M (normalizedRamanujanHorizonVector q N - u) =
        y_sp - (y_bg + horizonCollarVector M u) ∧
      Real.log c ≤ ∑ k ∈ Icc (M / q + 1) (N / q), 1 / (k : ℝ) ∧
      (∑ k ∈ Icc (M / q + 1) (N / q), 1 / (k : ℝ)) ≤ Real.log c + Real.log (4 * H_cut) ∧
      ‖y_sp‖ ^ 2 =
        ((q : ℝ) / (((q : ℝ) - 1) * L)) * ∑ k ∈ Icc (M / q + 1) (N / q), 1 / (k : ℝ) ∧
      ‖y_sp‖ ^ 2 ≤ 4 * L ^ (1 / 64 : ℝ) / L := by
  intro L M A_sp B_bg y_sp y_bg
  have hq2 : 2 ≤ q := hq_pr.two_le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq_pr.pos
  have hqm1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    linarith
  have hLc_pos : (0 : ℝ) < Lc := by exact_mod_cast (show 0 < Lc by omega)
  set Nq := N / q
  set Mq := M / q
  have hNq1 : 1 ≤ Nq := by omega
  have hNq0 : (0 : ℝ) < Nq := by exact_mod_cast hNq1
  set v := normalizedRamanujanHorizonVector q N
  have hy_decomp : horizonCollarVector M (v - u) = y_sp - (y_bg + horizonCollarVector M u) := by
    have hqt : (q.totient : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.totient_prime hq_pr, Nat.cast_sub hq_pr.one_lt.le, Nat.cast_one]
    ext ⟨n, hn⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    change (if M < n then primeHorizonExtension (v - u) n else 0) =
      (if M < n ∧ q ∣ n then A_sp * Real.sqrt q / Real.sqrt n else 0) -
        ((if M < n then B_bg / Real.sqrt n else 0) +
          (if M < n then primeHorizonExtension u n else 0))
    rw [primeHorizonExtension_coe (v - u) ⟨n, hn⟩, primeHorizonExtension_coe u ⟨n, hn⟩, PiLp.sub_apply]
    by_cases hMn : M < n
    · rw [if_pos hMn, if_pos hMn, if_pos hMn]
      change v ⟨n, hn⟩ - u ⟨n, hn⟩ = _
      change (Real.sqrt L)⁻¹ * (normalizedRamanujanMode q n / Real.sqrt n) - u ⟨n, hn⟩ = _
      rw [normalizedRamanujanMode_eq_coefficient hq_pr.pos,
        ramanujanLagCoefficient_of_prime hq_pr n, hqt]
      by_cases hdvd : q ∣ n
      · have hMdiv : M < n ∧ q ∣ n := ⟨hMn, hdvd⟩
        rw [if_pos hMdiv, if_pos hdvd]
        dsimp only [A_sp, B_bg]
        rw [Real.sqrt_div hq0.le, Real.sqrt_mul hqm1_pos.le, div_mul_eq_mul_div,
          Real.mul_self_sqrt hq0.le]
        field_simp [(Real.sqrt_pos.mpr hqm1_pos).ne', (Real.sqrt_pos.mpr hL0).ne',
          (Real.sqrt_pos.mpr hn0).ne']
        ring
      · have hnotMdiv : ¬(M < n ∧ q ∣ n) := fun h => hdvd h.2
        rw [if_neg hnotMdiv, if_neg hdvd]
        dsimp only [B_bg]
        rw [Real.sqrt_mul hqm1_pos.le]
        field_simp [(Real.sqrt_pos.mpr hqm1_pos).ne', (Real.sqrt_pos.mpr hL0).ne',
          (Real.sqrt_pos.mpr hn0).ne']
        ring
    · rw [if_neg hMn, if_neg (fun h => hMn h.1), if_neg hMn, if_neg hMn]; ring
  have hharm_lo : Real.log c ≤ ∑ k ∈ Icc (Mq + 1) Nq, 1 / (k : ℝ) := by
    have hlo := RHTower.Sieve.log_sub_le_sum_Icc_one_div (m := Mq + 1) (n := Nq)
      (by omega) (by omega)
    refine le_trans ?_ hlo
    have hNq_succ : (N : ℝ) / q ≤ (Nq : ℝ) + 1 := by
      rw [div_le_iff₀ hq0]
      have hlt : N < q * (Nq + 1) := by
        simpa only [Nq, Nat.mul_comm] using Nat.lt_mul_div_succ N hq_pr.pos
      have : (N : ℝ) ≤ ((q * (Nq + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
      push_cast at this
      linarith only [this]
    have hMq_succ : (((Mq + 1 : ℕ) : ℝ)) * c ≤ (N : ℝ) / q := by
      have hMq_le : (Mq : ℝ) ≤ (M : ℝ) / q :=
        (le_div_iff₀ hq0).mpr (by exact_mod_cast Nat.div_mul_le_self M q)
      have hM_le : (M : ℝ) ≤ (N : ℝ) / (2 * c) := by
        have hMLc : (M : ℝ) * Lc ≤ N := by exact_mod_cast Nat.div_mul_le_self N Lc
        have h2c_Lc : 2 * c ≤ Lc := by
          have hm := mul_le_mul_of_nonneg_right (Real.one_le_exp (zero_le_two (α := ℝ))) hc0.le
          linarith only [h256c, hm]
        rw [le_div_iff₀ (by positivity)]
        exact (mul_le_mul_of_nonneg_left h2c_Lc (Nat.cast_nonneg M)).trans hMLc
      have h1_le : 1 ≤ (N : ℝ) / (2 * c * q) := by
        rw [one_le_div (by positivity)]
        have h2cq : 2 * c * q ≤ 4 * (q : ℝ) * Lc := by
          have hm := mul_le_mul_of_nonneg_right (Real.one_le_exp (zero_le_two (α := ℝ))) hc0.le
          have h2c_Lc : 2 * c ≤ Lc := by linarith only [h256c, hm]
          nlinarith only [h2c_Lc, hq0, hLc_pos]
        exact h2cq.trans (by exact_mod_cast hqLc_le_N)
      push_cast
      calc ((Mq : ℝ) + 1) * c ≤ ((M : ℝ) / q + 1) * c :=
            mul_le_mul_of_nonneg_right (by linarith only [hMq_le]) hc0.le
        _ ≤ ((N : ℝ) / (2 * c) / q + (N : ℝ) / (2 * c * q)) * c :=
            mul_le_mul_of_nonneg_right
              (add_le_add (div_le_div_of_nonneg_right hM_le hq0.le) h1_le) hc0.le
        _ = (N : ℝ) / q := by field_simp [hc0.ne', hq0.ne']; ring
    have hlog_le := Real.log_le_log (by positivity) (hMq_succ.trans hNq_succ)
    rw [Real.log_mul (by positivity) hc0.ne'] at hlog_le
    linarith only [hlog_le]
  have hharm_hi : ∑ k ∈ Icc (Mq + 1) Nq, 1 / (k : ℝ) ≤ Real.log c + Real.log (4 * H_cut) := by
    have hhi := RHTower.Sieve.sum_Icc_one_div_le_log_sub (m := Mq + 1) (n := Nq)
      (by omega) (by omega)
    have hsub1 : (((Mq + 1 : ℕ) : ℝ) - 1) = (Mq : ℝ) := by push_cast; ring
    rw [hsub1] at hhi
    refine hhi.trans ?_
    have hNq_le : (Nq : ℝ) ≤ 4 * H_cut * c * Mq := by
      have hNq_div : (Nq : ℝ) ≤ (N : ℝ) / q :=
        (le_div_iff₀ hq0).mpr (by exact_mod_cast Nat.div_mul_le_self N q)
      have hN_le_2M : (N : ℝ) ≤ 2 * H_cut * c * M := by
        have hlt : N < Lc * (M + 1) := by
          simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (by omega : 0 < Lc)
        have hM1_2M : ((M + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
          have hM_ge1 : 1 ≤ M := le_trans hMq1 (Nat.div_le_self M q)
          push_cast; exact_mod_cast (show M + 1 ≤ 2 * M by omega)
        have h1 : (N : ℝ) ≤ (Lc : ℝ) * (2 * M) := by
          have hc : (N : ℝ) ≤ ((Lc * (M + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
          rw [Nat.cast_mul] at hc
          exact hc.trans (mul_le_mul_of_nonneg_left hM1_2M hLc_pos.le)
        calc (N : ℝ) ≤ (Lc : ℝ) * (2 * M) := h1
          _ ≤ (H_cut * c) * (2 * M) :=
              mul_le_mul_of_nonneg_right hLc_le_Hc (by positivity)
          _ = 2 * H_cut * c * M := by ring
      have hM_le_2qMq : (M : ℝ) ≤ 2 * q * Mq := by
        have hlt : M < q * (Mq + 1) := by
          simpa only [Mq, Nat.mul_comm] using Nat.lt_mul_div_succ M hq_pr.pos
        have hMq1_2 : ((Mq + 1 : ℕ) : ℝ) ≤ 2 * (Mq : ℝ) := by
          push_cast; exact_mod_cast (show Mq + 1 ≤ 2 * Mq by omega)
        have hc : (M : ℝ) ≤ ((q * (Mq + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
        rw [Nat.cast_mul] at hc
        exact hc.trans ((mul_le_mul_of_nonneg_left hMq1_2 hq0.le).trans_eq (by ring))
      calc (Nq : ℝ) ≤ (N : ℝ) / q := hNq_div
        _ ≤ (2 * H_cut * c * M) / q := div_le_div_of_nonneg_right hN_le_2M hq0.le
        _ ≤ (2 * H_cut * c * (2 * q * Mq)) / q :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hM_le_2qMq (by positivity)) hq0.le
        _ = 4 * H_cut * c * Mq := by field_simp [hq0.ne']; ring
    have hMq0 : (0 : ℝ) < Mq := by exact_mod_cast hMq1
    have hlog := Real.log_le_log hNq0 hNq_le
    rw [Real.log_mul (by positivity) hMq0.ne', Real.log_mul (by positivity) hc0.ne'] at hlog
    linarith only [hlog]
  have hysp_sq_eq : ‖y_sp‖ ^ 2 =
      ((q : ℝ) / (((q : ℝ) - 1) * L)) * ∑ k ∈ Icc (Mq + 1) Nq, 1 / (k : ℝ) := by
    set x_q := horizonProfileVector (fun k => if Mq < k then A_sp / Real.sqrt k else 0) Nq
    have hnorm_eq : ‖y_sp‖ ^ 2 = ‖x_q‖ ^ 2 := by
      rw [← sum_primeHorizonExtension_sq y_sp, ← sum_primeHorizonExtension_sq x_q]
      have himg : (Icc 1 Nq).image (q * ·) ⊆ Icc 1 N := by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
        obtain ⟨hk1, hkN⟩ := mem_Icc.mp hk
        exact mem_Icc.mpr ⟨Nat.mul_pos hq_pr.pos hk1,
          by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hq_pr.pos).mp hkN⟩
      have hzero_off : ∀ n ∈ Icc 1 N, n ∉ (Icc 1 Nq).image (q * ·) →
          primeHorizonExtension y_sp n ^ 2 = 0 := by
        intro n hn hnot
        rw [primeHorizonExtension_coe y_sp ⟨n, hn⟩]
        change (if M < n ∧ q ∣ n then A_sp * Real.sqrt q / Real.sqrt n else 0) ^ 2 = 0
        have hndvd : ¬(q ∣ n) := by
          intro ⟨k, hnk⟩
          apply hnot
          refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨?_, ?_⟩, hnk.symm⟩
          · by_contra hk0
            have hk0' : k = 0 := by omega
            rw [hk0', mul_zero] at hnk
            have := (mem_Icc.mp hn).1
            omega
          · exact (Nat.le_div_iff_mul_le hq_pr.pos).mpr
              (by rw [mul_comm, ← hnk]; exact (mem_Icc.mp hn).2)
        rw [if_neg (fun h => hndvd h.2), zero_pow (by norm_num)]
      rw [← sum_subset himg hzero_off,
        sum_image (fun k₁ _ k₂ _ heq => Nat.eq_of_mul_eq_mul_left hq_pr.pos heq)]
      refine sum_congr rfl fun k hk => ?_
      have hkN : q * k ∈ Icc 1 N := himg (mem_image_of_mem _ hk)
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
      rw [primeHorizonExtension_coe y_sp ⟨q * k, hkN⟩, primeHorizonExtension_coe x_q ⟨k, hk⟩]
      change (if M < q * k ∧ q ∣ q * k then A_sp * Real.sqrt q / Real.sqrt ((q * k : ℕ) : ℝ) else 0) ^ 2 =
        (if Mq < k then A_sp / Real.sqrt k else 0) ^ 2
      have hiff : (M < q * k ∧ q ∣ q * k) ↔ Mq < k :=
        ⟨fun h => (Nat.div_lt_iff_lt_mul hq_pr.pos).mpr (by rw [mul_comm]; exact h.1),
         fun h => ⟨by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul hq_pr.pos).mp h, dvd_mul_right q k⟩⟩
      by_cases hcond : Mq < k
      · rw [if_pos (hiff.mpr hcond), if_pos hcond, Nat.cast_mul, Real.sqrt_mul hq0.le]
        field_simp [(Real.sqrt_pos.mpr hq0).ne', (Real.sqrt_pos.mpr hk0).ne']
      · rw [if_neg (fun h => hcond (hiff.mp h)), if_neg hcond]
    rw [hnorm_eq, ← sum_primeHorizonExtension_sq x_q]
    have hsplit : Icc 1 Nq = Icc 1 Mq ∪ Icc (Mq + 1) Nq := by
      ext k; simp only [mem_union, mem_Icc]; omega
    rw [hsplit, sum_union (disjoint_left.mpr fun k h1 h2 => by
      simp only [mem_Icc] at h1 h2; omega)]
    have hz1 : ∑ k ∈ Icc 1 Mq, primeHorizonExtension x_q k ^ 2 = 0 := by
      refine sum_eq_zero fun k hk => ?_
      have hkN : k ∈ Icc 1 Nq := mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans hMq_lt_Nq.le⟩
      rw [primeHorizonExtension_coe x_q ⟨k, hkN⟩]
      change (if Mq < k then A_sp / Real.sqrt k else 0) ^ 2 = 0
      rw [if_neg (Nat.not_lt.mpr (mem_Icc.mp hk).2), zero_pow (by norm_num)]
    rw [hz1, zero_add, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨hk_lo, hk_hi⟩ := mem_Icc.mp hk
    have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 Mq) hk_lo
    have hkN : k ∈ Icc 1 Nq := mem_Icc.mpr ⟨hk1, hk_hi⟩
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    rw [primeHorizonExtension_coe x_q ⟨k, hkN⟩]
    change (if Mq < k then A_sp / Real.sqrt k else 0) ^ 2 = _
    rw [if_pos (Nat.lt_of_succ_le hk_lo), div_pow, Real.sq_sqrt hk0.le]
    dsimp only [A_sp]
    rw [Real.sq_sqrt (by positivity), div_eq_mul_one_div (_ / _)]
  have hysp_sq_le : ‖y_sp‖ ^ 2 ≤ 4 * L ^ (1 / 64 : ℝ) / L := by
    have hqqm1 : (q : ℝ) / ((q : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ hqm1_pos]
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      linarith
    have hS_le : ∑ k ∈ Icc (Mq + 1) Nq, 1 / (k : ℝ) ≤ 2 * L ^ (1 / 64 : ℝ) := by
      linarith only [hharm_hi, hlogc_64, hlog4H_64]
    rw [hysp_sq_eq, div_mul_eq_div_div]
    calc ((q : ℝ) / ((q : ℝ) - 1)) / L * ∑ k ∈ Icc (Mq + 1) Nq, 1 / (k : ℝ)
        ≤ (2 / L) * (2 * L ^ (1 / 64 : ℝ)) :=
          mul_le_mul (div_le_div_of_nonneg_right hqqm1 hL0.le) hS_le
            (sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = 4 * L ^ (1 / 64 : ℝ) / L := by ring
  exact ⟨hy_decomp, hharm_lo, hharm_hi, hysp_sq_eq, hysp_sq_le⟩

private theorem collar_quasimode_rem_norm_sq_le
    {N Lc q : ℕ} (hq_pr : q.Prime) (hN1 : 1 ≤ N) (hLc3 : 3 ≤ Lc)
    {c H_cut : ℝ} (hc0 : 0 < c) (hH_pos : 0 < H_cut)
    (hL1 : 1 ≤ Real.log (N : ℝ))
    (hLc_le_Hc : (Lc : ℝ) ≤ H_cut * c)
    (h1H : 1 + Real.log H_cut ≤ Real.log (N : ℝ) ^ (1 / 256 : ℝ))
    (hlogc_256 : Real.log c ≤ Real.log (N : ℝ) ^ (1 / 256 : ℝ))
    (hlogL_64 : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ (1 / 64 : ℝ))
    (hq_ge : Real.log (N : ℝ) ^ (13 / 32 : ℝ) ≤ q)
    (hq_le_2 : (q : ℝ) ≤ 2 * Real.log (N : ℝ) ^ (13 / 32 : ℝ))
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu_bd : ‖u‖ ≤ 18 * (1 + Real.log q) / Real.log (N : ℝ)) :
    let L := Real.log (N : ℝ)
    let M := N / Lc
    let B_bg : ℝ := 1 / Real.sqrt (((q : ℝ) - 1) * L)
    let y_bg := horizonProfileVector (fun n => if M < n then B_bg / Real.sqrt n else 0) N
    ‖y_bg + horizonCollarVector M u‖ ^ 2 ≤ (8 + 2 * 1170 ^ 2) / L ^ (359 / 256 : ℝ) := by
  intro L M B_bg y_bg
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hMN : M ≤ N := Nat.div_le_self N Lc
  have hq2 : 2 ≤ q := hq_pr.two_le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq_pr.pos
  have hqm1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    linarith
  set y_u := horizonCollarVector M u
  have hybg_sq : ‖y_bg‖ ^ 2 ≤ 4 / L ^ (359 / 256 : ℝ) := by
    rw [← sum_primeHorizonExtension_sq y_bg]
    have hsub_sum : ∑ n ∈ Icc 1 N, primeHorizonExtension y_bg n ^ 2 =
        B_bg ^ 2 * ∑ n ∈ Ioc M N, 1 / (n : ℝ) := by
      have hsplit : Icc 1 N = Icc 1 M ∪ Ioc M N := by
        clear_value M
        ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
      rw [hsplit, sum_union (disjoint_left.mpr fun n h1 h2 => by
        clear_value M
        simp only [mem_Icc] at h1; simp only [mem_Ioc] at h2; omega)]
      have hz1 : ∑ n ∈ Icc 1 M, primeHorizonExtension y_bg n ^ 2 = 0 := by
        refine sum_eq_zero fun n hn => ?_
        have hnN : n ∈ Icc 1 N := mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
        rw [primeHorizonExtension_coe y_bg ⟨n, hnN⟩]
        change (if M < n then B_bg / Real.sqrt n else 0) ^ 2 = 0
        rw [if_neg (Nat.not_lt.mpr (mem_Icc.mp hn).2), zero_pow (by norm_num)]
      rw [hz1, zero_add, mul_sum]
      refine sum_congr rfl fun n hn => ?_
      obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hn
      have hn1 : 1 ≤ n := Nat.succ_le_of_lt ((Nat.zero_le M).trans_lt hn_lo)
      have hnN : n ∈ Icc 1 N := mem_Icc.mpr ⟨hn1, hn_hi⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [primeHorizonExtension_coe y_bg ⟨n, hnN⟩]
      change (if M < n then B_bg / Real.sqrt n else 0) ^ 2 = _
      rw [if_pos hn_lo, div_pow, Real.sq_sqrt hn0.le, div_eq_mul_one_div]
    have hinv_le : ∑ n ∈ Ioc M N, 1 / (n : ℝ) ≤ 2 * L ^ (1 / 256 : ℝ) := by
      have h1 := sum_inv_Ioc_le hMN hN1
      have hNM1 : (N : ℝ) / ((M : ℝ) + 1) ≤ H_cut * c := by
        rw [div_le_iff₀ (by positivity)]
        have hLc0 : 0 < Lc := lt_of_lt_of_le (by norm_num) hLc3
        have hlt : N < Lc * (M + 1) := by
          simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N hLc0
        have hc : (N : ℝ) ≤ ((Lc * (M + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hc
        exact hc.trans (mul_le_mul_of_nonneg_right hLc_le_Hc (by positivity))
      have hlog_diff : Real.log (N : ℝ) - Real.log ((M : ℝ) + 1) ≤
          Real.log H_cut + Real.log c := by
        rw [← Real.log_div hN0.ne' (by positivity), ← Real.log_mul hH_pos.ne' hc0.ne']
        exact Real.log_le_log (by positivity) hNM1
      linarith only [h1, hlog_diff, h1H, hlogc_256]
    have hB_sq : B_bg ^ 2 ≤ 2 / L ^ (45 / 32 : ℝ) := by
      dsimp only [B_bg]
      rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
      have hqm1_ge : L ^ (13 / 32 : ℝ) / 2 ≤ (q : ℝ) - 1 := by
        have hq_half : (q : ℝ) / 2 ≤ (q : ℝ) - 1 := by
          have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
          linarith
        linarith only [hq_ge, hq_half]
      calc 1 / (((q : ℝ) - 1) * L)
          ≤ 1 / ((L ^ (13 / 32 : ℝ) / 2) * L) :=
            div_le_div_of_nonneg_left zero_le_one (by positivity)
              (mul_le_mul_of_nonneg_right hqm1_ge hL0.le)
        _ = 2 / L ^ (45 / 32 : ℝ) := by
            rw [show (L ^ (13 / 32 : ℝ) / 2) * L = (L ^ (13 / 32 : ℝ) * L) / 2 by ring,
              one_div_div, ← Real.rpow_add_one hL0.ne']
            norm_num
    rw [hsub_sum]
    calc B_bg ^ 2 * ∑ n ∈ Ioc M N, 1 / (n : ℝ)
        ≤ (2 / L ^ (45 / 32 : ℝ)) * (2 * L ^ (1 / 256 : ℝ)) :=
          mul_le_mul hB_sq hinv_le (sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = 4 / L ^ (359 / 256 : ℝ) := by
          rw [show (2 / L ^ (45 / 32 : ℝ)) * (2 * L ^ (1 / 256 : ℝ)) =
            4 * (L ^ (1 / 256 : ℝ) / L ^ (45 / 32 : ℝ)) by ring, ← Real.rpow_sub hL0]
          have hexp : (1 / 256 - 45 / 32 : ℝ) = -(359 / 256) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
  have hyu_sq : ‖y_u‖ ^ 2 ≤ 1170 ^ 2 / L ^ (63 / 32 : ℝ) := by
    have h1q : 1 + Real.log q ≤ 65 * L ^ (1 / 64 : ℝ) := by
      have hq_2L : (q : ℝ) ≤ 2 * L :=
        hq_le_2.trans (mul_le_mul_of_nonneg_left
          ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L)) zero_le_two)
      have hlq : Real.log (q : ℝ) ≤ Real.log (2 * L) := Real.log_le_log hq0 hq_2L
      rw [Real.log_mul two_ne_zero hL0.ne'] at hlq
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      have h1_64 : 1 ≤ L ^ (1 / 64 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith only [hlq, hlog2, hlogL_64, h1_64]
    have hu_rpow : ‖u‖ ≤ 1170 / L ^ (63 / 64 : ℝ) := by
      calc ‖u‖ ≤ 18 * (1 + Real.log q) / L := hu_bd
        _ ≤ 18 * (65 * L ^ (1 / 64 : ℝ)) / L :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1q (by norm_num)) hL0.le
        _ = 1170 / L ^ (63 / 64 : ℝ) := by
            rw [show 18 * (65 * L ^ (1 / 64 : ℝ)) / L = 1170 * (L ^ (1 / 64 : ℝ) / L) by ring,
              ← Real.rpow_sub_one hL0.ne']
            have hexp : (1 / 64 - 1 : ℝ) = -(63 / 64) := by norm_num
            rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
    have hp := pow_le_pow_left₀ (norm_nonneg y_u)
      ((norm_horizonCollarVector_le M u).trans hu_rpow) 2
    rw [div_pow, ← Real.rpow_natCast (L ^ (63 / 64 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hp
    have hp' : ‖y_u‖ ^ 2 ≤ 1170 ^ 2 / L ^ (63 / 32 : ℝ) := by norm_num at hp ⊢; exact hp
    exact hp'
  have htri : ‖y_bg + y_u‖ ^ 2 ≤ 2 * ‖y_bg‖ ^ 2 + 2 * ‖y_u‖ ^ 2 := by
    have h1 := norm_add_le y_bg y_u
    have h2 : (‖y_bg‖ + ‖y_u‖) ^ 2 ≤ 2 * ‖y_bg‖ ^ 2 + 2 * ‖y_u‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖y_bg‖ - ‖y_u‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hu' : 1170 ^ 2 / L ^ (63 / 32 : ℝ) ≤ 1170 ^ 2 / L ^ (359 / 256 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hL0 _)
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  calc ‖y_bg + y_u‖ ^ 2 ≤ 2 * (4 / L ^ (359 / 256 : ℝ)) + 2 * (1170 ^ 2 / L ^ (359 / 256 : ℝ)) := by
        linarith only [htri, hybg_sq, hyu_sq, hu']
    _ = (8 + 2 * 1170 ^ 2) / L ^ (359 / 256 : ℝ) := by ring

private theorem tendsto_quasimode_collar_energy_div_log_log {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      completeWeilEnergy tiltedUnitSpline (c N) N
        (horizonCollarVector (N / linearDefectCutoff (c N))
          (lowPacketOrthogonalPrimeQuasimode N)) /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 (1 / 8 : ℝ)) := by
  let φ := tiltedUnitSpline
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hM_int := integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_q, hC_q, hglob⟩ := exists_completeWeilMatrix_global_norm_cost
  obtain ⟨B_g, a_R, κ_R, hBg0, ha_pos, hκ_pos, hgard⟩ :=
    exists_collar_atomic_garding_along_critical_curve hR hc1 htend
  let H_cut : ℝ := 256 * Real.exp 2 + 4
  have hH_pos : 0 < H_cut := by dsimp only [H_cut]; positivity
  have h4H_ge1 : 1 ≤ 4 * H_cut := by dsimp only [H_cut]; linarith [Real.exp_pos 2]
  have hlog4H_nn : 0 ≤ Real.log (4 * H_cut) := Real.log_nonneg h4H_ge1
  let B_col : ℝ := (B_g + 1) * (1 + 2 * Real.exp 1)
  have hBcol_pos : 0 < B_col := by dsimp only [B_col]; positivity
  let C_top_abs : ℝ := |topPrimeConstant| + 1
  have hCtop_pos : 0 < C_top_abs := by dsimp only [C_top_abs]; positivity
  let C_self_abs : ℝ := |completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant| + 1
  have hCself_pos : 0 < C_self_abs := by dsimp only [C_self_abs]; positivity
  let C_err_half : ℝ := 4 * atomCrossErrorConstant φ (1 / 2) + 2 * atomPoleMomentErrorConstant φ + 4
  have hCerr_pos : 0 < C_err_half := by
    dsimp only [C_err_half]
    have h1 := atomCrossErrorConstant_nonneg φ (1 / 2)
    have h2 : 0 ≤ atomPoleMomentErrorConstant φ := by
      unfold atomPoleMomentErrorConstant
      positivity
    linarith
  have hL_tend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrat_lt : ∀ᶠ N in atTop, c N ^ 8 / Real.log (N : ℝ) < R + 1 :=
    htend.eventually (gt_mem_nhds (by linarith))
  have hL_pow4 : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 4 / (N : ℝ)) atTop (𝓝 0) :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).congr fun N => by dsimp only [Function.comp_def]; ring
  have hlog_rpow : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) /
      Real.log (N : ℝ) ^ (1 / 256 : ℝ)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 256 : ℝ)) atTop (𝓝 0) :=
      (tendsto_log_div_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 256)).congr' (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
        rfl)
    exact hsub.comp hL_tend
  refine tendsto_div_log_log_of_abs_sub_le (g := fun N => Real.log (c N))
    (tendsto_log_c_div_log_log hR hc1 htend)
    (C := Real.log (4 * H_cut) + 12) ?_
  filter_upwards [hc1, hrat_lt, hglob, hgard, norm_lowPacketProjection_primeAboveLowPacket_le,
    eventually_ge_atTop 16,
    hL_tend.eventually_ge_atTop ((4 : ℝ) ^ (1280 : ℝ)),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 256)).comp hL_tend).eventually_ge_atTop
      (R + 1 + C_q * (R + 1) + B_col * (R + 1) + C_top_abs * (R + 1) +
        C_self_abs + C_err_half + 4 * H_cut + Real.log (4 * H_cut) + 4096),
    hL_pow4.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (64 * H_cut ^ 2 * (R + 1)))),
    hlog_rpow.eventually (gt_mem_nhds zero_lt_one)]
    with N hcN hratN hglobN hgardN hu_bd hN16 hL_big hL_256 hL4_N hlogL_rpow
  clear hc1 htend hglob hgard hL_tend hrat_lt hL_pow4 hlog_rpow
  dsimp only [Function.comp_def] at hL_256 hlogL_rpow
  change (4 : ℝ) ^ (1280 : ℝ) ≤ Real.log (N : ℝ) at hL_big
  set L := Real.log (N : ℝ)
  have hL1 : 1 ≤ L := (Real.one_le_rpow (by norm_num) (by norm_num)).trans hL_big
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
  have hCR_nn : 0 ≤ C_q * (R + 1) := by positivity
  have hBR_nn : 0 ≤ B_col * (R + 1) := by positivity
  have hTR_nn : 0 ≤ C_top_abs * (R + 1) := by positivity
  have h1_64_ge : L ^ (1 / 256 : ℝ) ≤ L ^ (1 / 64 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hL_rpow : R + 1 + C_q * (R + 1) + B_col * (R + 1) + C_top_abs * (R + 1) +
      C_self_abs + C_err_half + 4 * H_cut + Real.log (4 * H_cut) + 4096 ≤ L ^ (1 / 64 : ℝ) :=
    hL_256.trans h1_64_ge
  have hL_3_256 : (4 : ℝ) ^ (15 : ℕ) ≤ L ^ (3 / 256 : ℝ) :=
    four_pow_nat_le_rpow (e := 3 / 256) 15 hL_big (by norm_num) (by norm_num)
  have hL_256_big : (4 : ℝ) ^ (14 : ℕ) ≤ L ^ (7 / 32 : ℝ) :=
    (by norm_num : (4 : ℝ) ^ (14 : ℕ) ≤ (4 : ℝ) ^ (15 : ℕ)).trans
      (hL_3_256.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
  have hc8_le : c N ^ 8 ≤ (R + 1) * L := (div_lt_iff₀ hL0).mp hratN |>.le
  have hR1_256 : R + 1 ≤ L ^ (1 / 256 : ℝ) := by
    linarith only [hL_256, hCR_nn, hBR_nn, hTR_nn, hCself_pos, hCerr_pos, hH_pos, hlog4H_nn]
  have hR1_64 : R + 1 ≤ L ^ (1 / 64 : ℝ) := hR1_256.trans h1_64_ge
  have hc_le_9_64 : c N ≤ L ^ (9 / 64 : ℝ) := by
    have hp8 : c N ^ 8 ≤ (L ^ (9 / 64 : ℝ)) ^ 8 := by
      rw [← Real.rpow_natCast (L ^ (9 / 64 : ℝ)) 8, ← Real.rpow_mul hL0.le]
      have hexp2 : (1 / 64 : ℝ) + 1 = 65 / 64 := by norm_num
      have h65_72 : L ^ (65 / 64 : ℝ) ≤ L ^ (9 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      calc c N ^ 8 ≤ (R + 1) * L := hc8_le
        _ ≤ L ^ (1 / 64 : ℝ) * L := mul_le_mul_of_nonneg_right hR1_64 hL0.le
        _ = L ^ (65 / 64 : ℝ) := by rw [← Real.rpow_add_one hL0.ne', hexp2]
        _ ≤ L ^ ((9 / 64 : ℝ) * (8 : ℕ)) := by norm_num; exact h65_72
    exact (pow_le_pow_iff_left₀ hc0.le (Real.rpow_nonneg hL0.le _) (by omega)).mp hp8
  have hc3_rpow : c N ^ 3 ≤ L ^ (97 / 256 : ℝ) := by
    have hp8 : (c N ^ 3) ^ 8 ≤ (L ^ (97 / 256 : ℝ)) ^ 8 := by
      have h83 : (c N ^ 3) ^ 8 = (c N ^ 8) ^ 3 := by ring
      rw [h83, ← Real.rpow_natCast (L ^ (97 / 256 : ℝ)) 8, ← Real.rpow_mul hL0.le]
      have hc8_257 : c N ^ 8 ≤ L ^ (257 / 256 : ℝ) := by
        calc c N ^ 8 ≤ (R + 1) * L := hc8_le
          _ ≤ L ^ (1 / 256 : ℝ) * L := mul_le_mul_of_nonneg_right hR1_256 hL0.le
          _ = L ^ (257 / 256 : ℝ) := by rw [← Real.rpow_add_one hL0.ne']; norm_num
      have h3 : (c N ^ 8) ^ 3 ≤ (L ^ (257 / 256 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hc8_257 3
      rw [← Real.rpow_natCast (L ^ (257 / 256 : ℝ)) 3, ← Real.rpow_mul hL0.le] at h3
      exact h3.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
    exact (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hL0.le _) (by omega)).mp hp8
  have hc_le_L : c N ≤ L :=
    hc_le_9_64.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hlogL_256 : Real.log L ≤ L ^ (1 / 256 : ℝ) :=
    (div_lt_iff₀ (Real.rpow_pos_of_pos hL0 _)).mp hlogL_rpow |>.le.trans_eq (one_mul _)
  have hlogc_256 : Real.log (c N) ≤ L ^ (1 / 256 : ℝ) :=
    (Real.log_le_log hc0 hc_le_L).trans hlogL_256
  have hlogL_64 : Real.log L ≤ L ^ (1 / 64 : ℝ) := hlogL_256.trans h1_64_ge
  have hlogc_64 : Real.log (c N) ≤ L ^ (1 / 64 : ℝ) := hlogc_256.trans h1_64_ge
  set Q₁ := lowPacketCutoff N
  set q := primeAboveLowPacket N
  obtain ⟨hq_prime, hq_gt, hq_le⟩ := primeAboveLowPacket_spec N
  have hq_pr : q.Prime := hq_prime
  have hq2 : 2 ≤ q := hq_pr.two_le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq_pr.pos
  have hqm1_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    linarith
  have hQ₁_ge4 : 4 ≤ Q₁ := by
    dsimp only [Q₁, lowPacketCutoff]
    refine Nat.le_floor ?_
    exact (by norm_num : (4 : ℝ) ≤ (4 : ℝ) ^ (1 : ℕ)).trans
      (four_pow_nat_le_rpow (e := 13 / 32) 1 hL_big (by norm_num) (by norm_num))
  have hq_ge : L ^ (13 / 32 : ℝ) ≤ q := by
    have hlt : Q₁ < q := (le_max_right 2 Q₁).trans_lt hq_gt
    have hfl := (Nat.lt_floor_add_one (L ^ (13 / 32 : ℝ))).le
    have hle : (Q₁ : ℝ) + 1 ≤ q := by exact_mod_cast hlt
    exact hfl.trans hle
  have hq_le_2 : (q : ℝ) ≤ 2 * L ^ (13 / 32 : ℝ) := by
    have hmax : max 2 Q₁ = Q₁ := max_eq_right (by omega)
    rw [hmax] at hq_le
    have hQ_le : (Q₁ : ℝ) ≤ L ^ (13 / 32 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL0.le _)
    have hq_cast : (q : ℝ) ≤ 2 * Q₁ := by exact_mod_cast hq_le
    linarith only [hq_cast, hQ_le]
  set Lc := linearDefectCutoff (c N)
  obtain ⟨hLc3, h4c, h256c, hLc_up⟩ := linearDefectCutoff_bounds hcN
  have hLc_le_Hc : (Lc : ℝ) ≤ H_cut * c N := by
    dsimp only [H_cut]; linarith only [hLc_up, hcN]
  have hLc_pos : (0 : ℝ) < Lc := by exact_mod_cast (show 0 < Lc by omega)
  have hN_L4_split : 64 * H_cut ^ 2 * (R + 1) * L ^ 4 ≤ (N : ℝ) := by
    have hlt := (div_lt_iff₀ hN0).mp hL4_N
    have hpos : 0 < 64 * H_cut ^ 2 * (R + 1) := by positivity
    have h1 := (lt_div_iff₀ hpos).mp (by
      calc L ^ 4 < 1 / (64 * H_cut ^ 2 * (R + 1)) * (N : ℝ) := hlt
        _ = (N : ℝ) / (64 * H_cut ^ 2 * (R + 1)) := by ring)
    linarith only [h1]
  have h2LN : 2 * Lc ≤ N := by
    have h1 : (2 * (Lc : ℝ)) ≤ 2 * H_cut * L := by
      have hm := mul_le_mul_of_nonneg_left hc_le_L hH_pos.le
      linarith only [hLc_le_Hc, hm]
    have h2 : 2 * H_cut * L ≤ 64 * H_cut ^ 2 * (R + 1) * L ^ 4 := by
      have hL14 : L ≤ L ^ 4 := le_self_pow₀ hL1 (by omega)
      have hcoef : 2 * H_cut ≤ 64 * H_cut ^ 2 * (R + 1) := by
        have hH1 : 1 ≤ H_cut := by dsimp only [H_cut]; linarith [Real.exp_pos 2]
        have hHH : H_cut ≤ H_cut ^ 2 := le_self_pow₀ hH1 (by omega)
        have hm := mul_le_mul (show (2 : ℝ) ≤ 64 * (R + 1) by linarith) hHH hH_pos.le (by positivity)
        linarith only [hm]
      exact (mul_le_mul hcoef hL14 hL0.le (by positivity)).trans_eq (by ring)
    exact_mod_cast (show ((2 * Lc : ℕ) : ℝ) ≤ N by push_cast; exact (h1.trans h2).trans hN_L4_split)
  have hcN_le_N : c N ≤ N := by
    have hLNR : (Lc : ℝ) ≤ N := by exact_mod_cast (show Lc ≤ N by omega)
    linarith only [h4c, hLNR, hc0]
  set M := N / Lc
  have hMN : M ≤ N := Nat.div_le_self N Lc
  set Nq := N / q
  set Mq := M / q
  have hqLc_le_N : 4 * q * Lc ≤ N := by
    have hq_2L : (q : ℝ) ≤ 2 * L :=
      hq_le_2.trans (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L)) zero_le_two)
    have h1 : 4 * (q : ℝ) * Lc ≤ 8 * H_cut * L ^ 2 := by
      calc 4 * (q : ℝ) * Lc ≤ 4 * (2 * L) * (H_cut * L) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hq_2L (by norm_num))
              (hLc_le_Hc.trans (mul_le_mul_of_nonneg_left hc_le_L hH_pos.le))
              hLc_pos.le (by positivity)
        _ = 8 * H_cut * L ^ 2 := by ring
    have h2 : 8 * H_cut * L ^ 2 ≤ 64 * H_cut ^ 2 * (R + 1) * L ^ 4 := by
      have hL24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by omega)
      have hH1 : 1 ≤ H_cut := by dsimp only [H_cut]; linarith [Real.exp_pos 2]
      have hHH : H_cut ≤ H_cut ^ 2 := le_self_pow₀ hH1 (by omega)
      have hcoef : 8 * H_cut ≤ 64 * H_cut ^ 2 * (R + 1) := by
        have hm := mul_le_mul (show (8 : ℝ) ≤ 64 * (R + 1) by linarith) hHH hH_pos.le (by positivity)
        linarith only [hm]
      exact (mul_le_mul hcoef hL24 (sq_nonneg _) (by positivity)).trans_eq (by ring)
    exact_mod_cast (show ((4 * q * Lc : ℕ) : ℝ) ≤ N by push_cast; exact (h1.trans h2).trans hN_L4_split)
  have hMq4 : 4 ≤ Mq := by
    dsimp only [Mq, M]
    rw [Nat.div_div_eq_div_mul]
    exact (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) hq_pr.pos)).mpr
      (by linarith [Nat.mul_comm Lc q])
  have hMq1 : 1 ≤ Mq := by omega
  have hMq_lt_Nq : Mq < Nq := by
    have h3M_le_N : 3 * M ≤ N := by
      have hMLc : M * Lc ≤ N := Nat.div_mul_le_self N Lc
      have h3 : M * 3 ≤ M * Lc := Nat.mul_le_mul_left M hLc3
      linarith
    have hqMq_le_M : q * Mq ≤ M := Nat.mul_div_le M q
    have hM_ge1 : 1 ≤ M := le_trans hMq1 (Nat.div_le_self M q)
    have hN_lt : N < q * (Nq + 1) := by
      simpa only [Nq, Nat.mul_comm] using Nat.lt_mul_div_succ N hq_pr.pos
    have hlt_mul : q * (Mq + 1) ≤ q * Nq := by
      have hlt : q * (Mq + 1) < q * (Nq + 1) := by
        calc q * (Mq + 1) = q * Mq + q := by ring
          _ ≤ 2 * (q * Mq) := by have := Nat.mul_le_mul_left q hMq1; linarith
          _ ≤ 2 * M := by linarith
          _ < 3 * M := by linarith
          _ ≤ N := h3M_le_N
          _ < q * (Nq + 1) := hN_lt
      have h1 : Mq + 1 < Nq + 1 := Nat.lt_of_mul_lt_mul_left hlt
      exact Nat.mul_le_mul_left q (by omega)
    exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_left hlt_mul hq_pr.pos)
  have hNq1 : 1 ≤ Nq := by omega
  have hNq0 : (0 : ℝ) < Nq := by exact_mod_cast hNq1
  set cq := c N * (Nq : ℝ) / N
  have hcq_le_cq_div : cq ≤ c N / q := by
    dsimp only [cq]
    have hNq_le : (Nq : ℝ) ≤ (N : ℝ) / q :=
      (le_div_iff₀ hq0).mpr (by exact_mod_cast Nat.div_mul_le_self N q)
    calc c N * (Nq : ℝ) / N ≤ c N * ((N : ℝ) / q) / N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNq_le hc0.le) hN0.le
      _ = c N / q := by field_simp [hN0.ne', hq0.ne']
  have hcq_rpow : cq ≤ 1 / L ^ (17 / 64 : ℝ) := by
    calc cq ≤ c N / q := hcq_le_cq_div
      _ ≤ L ^ (9 / 64 : ℝ) / L ^ (13 / 32 : ℝ) :=
          div_le_div₀ (Real.rpow_nonneg hL0.le _) hc_le_9_64 (Real.rpow_pos_of_pos hL0 _) hq_ge
      _ = 1 / L ^ (17 / 64 : ℝ) := by
          rw [← Real.rpow_sub hL0]
          have hexp : (9 / 64 - 13 / 32 : ℝ) = -(17 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, one_div]
  have hcq_quarter : cq ≤ 1 / 4 := by
    refine hcq_rpow.trans ?_
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hL0 _) (by norm_num), one_mul, one_mul]
    exact (by norm_num : (4 : ℝ) ≤ (4 : ℝ) ^ (1 : ℕ)).trans
      (four_pow_nat_le_rpow (e := 17 / 64) 1 hL_big (by norm_num) (by norm_num))
  -- Decompose `y_z = y_sp - y_rem` on `Ioc M N`.
  set v := normalizedRamanujanHorizonVector q N
  set u := (conductorSubspace Q₁ N).starProjection v
  set z := lowPacketOrthogonalPrimeQuasimode N
  set y_z := horizonCollarVector M z
  change |completeWeilEnergy φ (c N) N y_z - Real.log (c N)| ≤ _
  set A_sp : ℝ := Real.sqrt ((q : ℝ) / (((q : ℝ) - 1) * L))
  set B_bg : ℝ := 1 / Real.sqrt (((q : ℝ) - 1) * L)
  set y_sp := horizonProfileVector
    (fun n => if M < n ∧ q ∣ n then A_sp * Real.sqrt q / Real.sqrt n else 0) N
  set y_bg := horizonProfileVector (fun n => if M < n then B_bg / Real.sqrt n else 0) N
  set y_u := horizonCollarVector M u
  set y_rem := y_bg + y_u
  have hlog4H_64 : Real.log (4 * H_cut) ≤ L ^ (1 / 64 : ℝ) := by
    linarith only [hL_rpow, hR, hCR_nn, hBR_nn, hTR_nn, hCself_pos, hCerr_pos, hH_pos]
  obtain ⟨hy_decomp, hharm_lo, hharm_hi, hysp_sq_eq, hysp_sq_le⟩ :=
    collar_quasimode_decomp_and_spike_norm hq_pr hLc3 hc0 hH_pos hL0 h256c hLc_le_Hc
      hqLc_le_N hMq1 hMq_lt_Nq hlogc_64 hlog4H_64 u
  have hy_decomp' : y_z = y_sp - y_rem := by
    dsimp only [y_z, z, lowPacketOrthogonalPrimeQuasimode, y_sp, y_rem, y_bg, y_u,
      A_sp, B_bg, M, Lc, q, Q₁, L, v, u]
    exact hy_decomp
  have hysp_sq_le' : ‖y_sp‖ ^ 2 ≤ 4 * L ^ (1 / 64 : ℝ) / L := hysp_sq_le
  -- Evaluate `completeWeilEnergy φ (c N) N y_sp` up to `Real.log (4 * H_cut) + 6`.
  have hEsp_approx : |completeWeilEnergy φ (c N) N y_sp - Real.log (c N)| ≤
      Real.log (4 * H_cut) + 6 := by
    have hsp := completeWeilEnergy_collar_spike_approx hcN hq_pr h2LN hNq1 hMq1 hMq_lt_Nq
      hcq_quarter A_sp
    dsimp only at hsp
    have hcq0 : 0 < cq := div_pos (mul_pos hc0 hNq0) hN0
    have hCt_64 : |topPrimeConstant| + 1 ≤ L ^ (1 / 64 : ℝ) := by
      have h1 : C_top_abs ≤ C_top_abs * (R + 1) :=
        le_mul_of_one_le_right hCtop_pos.le (by linarith)
      dsimp only [C_top_abs] at h1
      linarith only [h1, hL_rpow, hR, hCR_nn, hBR_nn, hCself_pos, hCerr_pos, hH_pos, hlog4H_nn]
    have hCs_64 : |completeWeilSelfFinitePart φ 1 - Real.eulerMascheroniConstant| + 1 ≤
        L ^ (1 / 64 : ℝ) := by
      dsimp only [C_self_abs] at hL_rpow
      linarith only [hL_rpow, hR, hCR_nn, hBR_nn, hTR_nn, hCerr_pos, hH_pos, hlog4H_nn]
    have hCerr_64 : 4 * atomCrossErrorConstant φ (1 / 2) +
        2 * atomPoleMomentErrorConstant φ + 4 ≤ L ^ (1 / 64 : ℝ) := by
      dsimp only [C_err_half] at hL_rpow
      linarith only [hL_rpow, hR, hCR_nn, hBR_nn, hTR_nn, hCself_pos, hH_pos, hlog4H_nn]
    have h4_64 : (4 : ℝ) ≤ L ^ (1 / 64 : ℝ) := by
      linarith only [hL_rpow, hR, hCR_nn, hBR_nn, hTR_nn, hCself_pos, hCerr_pos, hH_pos, hlog4H_nn]
    exact collar_spike_energy_sub_log_le hcN hL1 (by exact_mod_cast hq2) hcq0 hcq_quarter
      (sum_nonneg fun _ _ => by positivity) (sq_nonneg _) hlog4H_nn hL_256_big hc_le_9_64 hlogc_64
      hq_ge hcq_rpow hCt_64 hCs_64 hCerr_64 h4_64 hlog4H_64 hharm_lo hharm_hi hysp_sq_eq
      hysp_sq_le hsp
  -- Bound `y_rem = y_bg + y_u` and transfer `y_sp` to `y_z` via Collar Gårding.
  have h1H : 1 + Real.log H_cut ≤ L ^ (1 / 256 : ℝ) := by
    have hH_le_4H : Real.log H_cut ≤ Real.log (4 * H_cut) :=
      Real.log_le_log hH_pos (by linarith only [hH_pos])
    linarith only [hL_256, hR, hCR_nn, hBR_nn, hTR_nn, hCself_pos, hCerr_pos, hH_pos, hH_le_4H]
  have hyrem_sq : ‖y_rem‖ ^ 2 ≤ (8 + 2 * 1170 ^ 2) / L ^ (359 / 256 : ℝ) :=
    collar_quasimode_rem_norm_sq_le hq_pr hN1 hLc3 hc0 hH_pos hL1 hLc_le_Hc h1H hlogc_256
      hlogL_64 hq_ge hq_le_2 hu_bd
  clear_value y_z z v
  have hvan_lin : ∀ (α β : ℝ) (n : ℕ), n ≤ M →
      primeHorizonExtension (α • y_sp + β • y_rem) n = 0 := by
    intro α β n hnM
    by_cases hn : n ∈ Icc 1 N
    · rw [primeHorizonExtension_coe _ ⟨n, hn⟩, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply,
        PiLp.add_apply]
      have hnot : ¬(M < n) := Nat.not_lt.mpr hnM
      change α * (if M < n ∧ q ∣ n then A_sp * Real.sqrt q / Real.sqrt n else 0) +
        β * ((if M < n then B_bg / Real.sqrt n else 0) +
          (if M < n then primeHorizonExtension u n else 0)) = 0
      rw [if_neg (fun h => hnot h.1), if_neg hnot, if_neg hnot]
      ring
    · simp only [primeHorizonExtension, hn, ↓reduceDIte]
  have hgard_col : ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (∀ n, n ≤ M → primeHorizonExtension w n = 0) →
      0 ≤ completeWeilEnergy φ (c N) N w + B_col * c N * ‖w‖ ^ 2 := by
    intro w hw0
    have htail_eq : atomicTailCoefficients M (primeHorizonExtension w) = primeHorizonExtension w := by
      funext n
      unfold atomicTailCoefficients
      by_cases h : M < n
      · rw [if_pos h]
      · rw [if_neg h, hw0 n (Nat.not_lt.mp h)]
    have hg0 := hgardN (primeHorizonExtension w)
    dsimp only at hg0
    rw [htail_eq] at hg0
    let U_w := normalizedCentredAtomicTest φ (primeHorizonExtension w) (c N) N
    have hpos_lhs : 0 ≤ κ_R * topCollarSeventhMass M N (primeHorizonExtension w) +
        a_R * ∫ u, U_w u ^ 2 * Real.exp (-(8 * u)) :=
      add_nonneg (mul_nonneg hκ_pos.le (topCollarSeventhMass_nonneg M N _))
        (mul_nonneg ha_pos.le
          (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
    have hg1 : 0 ≤ weilQuad U_w + B_g * ∫ u, U_w u ^ 2 := hpos_lhs.trans hg0
    have hUw_L2_nn : 0 ≤ ∫ u, U_w u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hUw_L2 : (∫ u, U_w u ^ 2) ≤ (1 + 2 * Real.exp 1) * (∫ u, φ u ^ 2) * ‖w‖ ^ 2 :=
      (integral_normalizedCentredAtomicTest_sq_le hφ.continuous hsupp hcN hN1 hcN_le_N _).trans_eq
        (by rw [sum_primeHorizonExtension_sq])
    have hBg_le : B_g * ∫ u, U_w u ^ 2 ≤ B_col * (∫ u, φ u ^ 2) * ‖w‖ ^ 2 := by
      calc B_g * ∫ u, U_w u ^ 2
          ≤ (B_g + 1) * ∫ u, U_w u ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hUw_L2_nn
        _ ≤ (B_g + 1) * ((1 + 2 * Real.exp 1) * (∫ u, φ u ^ 2) * ‖w‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hUw_L2 (by positivity)
        _ = B_col * (∫ u, φ u ^ 2) * ‖w‖ ^ 2 := by dsimp only [B_col]; ring
    have hg2 : 0 ≤ ((∫ u, φ u ^ 2) / c N) * completeWeilEnergy φ (c N) N w +
        B_col * (∫ u, φ u ^ 2) * ‖w‖ ^ 2 := by
      have hwq := weilQuad_normalizedCentredAtomicTest_eq hφ hsupp hM_int hc0 hN1 w
      change weilQuad U_w = ((∫ u, φ u ^ 2) / c N) * completeWeilEnergy φ (c N) N w at hwq
      linarith only [hg1, hBg_le, hwq]
    have hm := mul_le_mul_of_nonneg_left hg2 (div_nonneg hc0.le hM_int.le)
    rw [mul_zero] at hm
    refine hm.trans_eq ?_
    dsimp only [φ]
    field_simp [hc0.ne', hM_int.ne']
  clear_value y_rem y_sp y_bg y_u u M Lc Q₁ q Nq Mq
  have hEyrem_rpow : |completeWeilEnergy φ (c N) N y_rem| ≤ 1 / L ^ (2 / 256 : ℝ) := by
    have hg := (hglobN hcN hc_le_L).1 y_rem
    refine hg.trans ?_
    have hL1_le : L + 1 ≤ 2 * L := by linarith only [hL1]
    have hCq_256 : C_q ≤ L ^ (1 / 256 : ℝ) := by
      have h1 : C_q ≤ C_q * (R + 1) := le_mul_of_one_le_right hC_q.le (by linarith)
      linarith only [h1, hL_256, hR, hBR_nn, hTR_nn, hCself_pos, hCerr_pos, hH_pos, hlog4H_nn]
    calc C_q * c N ^ 3 * (L + 1) * ‖y_rem‖ ^ 2
        ≤ L ^ (1 / 256 : ℝ) * L ^ (97 / 256 : ℝ) * (2 * L) *
            ((8 + 2 * 1170 ^ 2) / L ^ (359 / 256 : ℝ)) :=
          mul_le_mul
            (mul_le_mul (mul_le_mul hCq_256 hc3_rpow (by positivity) (by positivity))
              hL1_le (by positivity) (by positivity))
            hyrem_sq (sq_nonneg _) (by positivity)
      _ = (2 * (8 + 2 * 1170 ^ 2)) / L ^ (5 / 256 : ℝ) := by
          rw [show L ^ (1 / 256 : ℝ) * L ^ (97 / 256 : ℝ) * (2 * L) *
              ((8 + 2 * 1170 ^ 2) / L ^ (359 / 256 : ℝ)) =
            (2 * (8 + 2 * 1170 ^ 2)) *
              (L ^ (1 / 256 : ℝ) * L ^ (97 / 256 : ℝ) * L / L ^ (359 / 256 : ℝ)) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_add_one hL0.ne', ← Real.rpow_sub hL0]
          have hexp : (1 / 256 + 97 / 256 + 1 - 359 / 256 : ℝ) = -(5 / 256) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      _ = ((2 * (8 + 2 * 1170 ^ 2)) / L ^ (3 / 256 : ℝ)) * (1 / L ^ (2 / 256 : ℝ)) := by
          rw [div_mul_div_comm, mul_one, ← Real.rpow_add hL0]
          norm_num
      _ ≤ 1 * (1 / L ^ (2 / 256 : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          exact (by norm_num : (2 * (8 + 2 * 1170 ^ 2) : ℝ) ≤ (4 : ℝ) ^ (15 : ℕ)).trans hL_3_256
      _ = 1 / L ^ (2 / 256 : ℝ) := one_mul _
  have hBcol_256 : B_col ≤ L ^ (1 / 256 : ℝ) := by
    have h1 : B_col ≤ B_col * (R + 1) := le_mul_of_one_le_right hBcol_pos.le (by linarith)
    linarith only [h1, hL_256, hR, hCR_nn, hTR_nn, hCself_pos, hCerr_pos, hH_pos, hlog4H_nn]
  have hc_97 : c N ≤ L ^ (97 / 256 : ℝ) := (le_self_pow₀ hcN (by norm_num)).trans hc3_rpow
  have hlog4H_6_le : Real.log (4 * H_cut) + 6 ≤ L ^ (1 / 256 : ℝ) := by
    linarith only [hL_256, hR, hCR_nn, hBR_nn, hTR_nn, hCself_pos, hCerr_pos, hH_pos]
  have h3_256 : (3 : ℝ) ≤ L ^ (1 / 256 : ℝ) := by
    linarith only [hL_256, hR, hCR_nn, hBR_nn, hTR_nn, hCself_pos, hCerr_pos, hH_pos, hlog4H_nn]
  exact collar_garding_transfer_abs_sub_le hcN hL1 hBcol_pos hL_3_256 hc_le_9_64 hc_97 hlogc_256
    hBcol_256 hlog4H_6_le h3_256 hy_decomp' hvan_lin hgard_col hysp_sq_le' hyrem_sq hEyrem_rpow
    hEsp_approx

private theorem tendsto_c_mul_quasimode_collar_norm_sq_zero {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      c N * ‖horizonCollarVector (N / linearDefectCutoff (c N))
        (lowPacketOrthogonalPrimeQuasimode N)‖ ^ 2) atTop (𝓝 0) := by
  let H_cut : ℝ := 256 * Real.exp 2 + 4
  have hH_pos : 0 < H_cut := by dsimp only [H_cut]; positivity
  have hL_tend : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrat_lt : ∀ᶠ N in atTop, c N ^ 8 / Real.log (N : ℝ) < R + 1 :=
    htend.eventually (gt_mem_nhds (by linarith))
  have hlog_rpow : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) /
      Real.log (N : ℝ) ^ (1 / 64 : ℝ)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 64 : ℝ)) atTop (𝓝 0) :=
      (tendsto_log_div_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 64)).congr' (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
        rfl)
    exact hsub.comp hL_tend
  have hrpow_zero : Tendsto (fun N : ℕ =>
      (32 + 2 * 1170 ^ 2) / Real.log (N : ℝ) ^ (7 / 16 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-(7 / 16 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 16)
    have h2 := (h1.comp hL_tend).const_mul (32 + 2 * 1170 ^ 2)
    rw [mul_zero] at h2
    exact h2.congr fun N => by
      dsimp only [Function.comp_def]
      rw [Real.rpow_neg (Real.log_natCast_nonneg N), ← div_eq_mul_inv]
  refine squeeze_zero_norm' ?_ hrpow_zero
  filter_upwards [hc1, hrat_lt, norm_lowPacketProjection_primeAboveLowPacket_le,
    eventually_ge_atTop 16,
    hL_tend.eventually_ge_atTop ((4 : ℝ) ^ (96 : ℝ)),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 64)).comp hL_tend).eventually_ge_atTop
      (R + 1 + 1 + |Real.log H_cut| + 64),
    hlog_rpow.eventually (gt_mem_nhds zero_lt_one)]
    with N hcN hratN hu_bd hN16 hL_big hL_64 hlogL_64
  clear hc1 htend hL_tend hrat_lt hlog_rpow hrpow_zero
  dsimp only [Function.comp_def] at hL_64 hlogL_64
  change (4 : ℝ) ^ (96 : ℝ) ≤ Real.log (N : ℝ) at hL_big
  set L := Real.log (N : ℝ)
  have hL1 : 1 ≤ L := (Real.one_le_rpow (by norm_num) (by norm_num)).trans hL_big
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
  rw [Real.norm_of_nonneg (mul_nonneg hc0.le (sq_nonneg _))]
  have hR1_64 : R + 1 ≤ L ^ (1 / 64 : ℝ) := by
    linarith only [hL_64, abs_nonneg (Real.log H_cut)]
  have hc_le_9_64 : c N ≤ L ^ (9 / 64 : ℝ) := by
    have hp8 : c N ^ 8 ≤ (L ^ (9 / 64 : ℝ)) ^ 8 := by
      rw [← Real.rpow_natCast (L ^ (9 / 64 : ℝ)) 8, ← Real.rpow_mul hL0.le]
      calc c N ^ 8 ≤ (R + 1) * L := (div_lt_iff₀ hL0).mp hratN |>.le
        _ ≤ L ^ (1 / 64 : ℝ) * L := mul_le_mul_of_nonneg_right hR1_64 hL0.le
        _ = L ^ (65 / 64 : ℝ) := by rw [← Real.rpow_add_one hL0.ne']; norm_num
        _ ≤ L ^ ((9 / 64 : ℝ) * (8 : ℕ)) := by
            norm_num; exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    exact (pow_le_pow_iff_left₀ hc0.le (Real.rpow_nonneg hL0.le _) (by omega)).mp hp8
  have hc_le_L : c N ≤ L :=
    hc_le_9_64.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hlogL_le : Real.log L ≤ L ^ (1 / 64 : ℝ) :=
    ((div_lt_iff₀ (Real.rpow_pos_of_pos hL0 _)).mp hlogL_64).le.trans_eq (one_mul _)
  have hlogc_le : Real.log (c N) ≤ L ^ (1 / 64 : ℝ) :=
    (Real.log_le_log hc0 hc_le_L).trans hlogL_le
  set Lc := linearDefectCutoff (c N)
  obtain ⟨hLc3, _, _, hLc_up⟩ := linearDefectCutoff_bounds hcN
  have hLc_le_Hc : (Lc : ℝ) ≤ H_cut * c N := by dsimp only [H_cut]; linarith only [hLc_up, hcN]
  set M := N / Lc
  have hMN : M ≤ N := Nat.div_le_self N Lc
  have hinv_le : ∑ n ∈ Ioc M N, 1 / (n : ℝ) ≤ 2 * L ^ (1 / 64 : ℝ) := by
    have h1 := sum_inv_Ioc_le hMN hN1
    have hNM1 : (N : ℝ) / ((M : ℝ) + 1) ≤ H_cut * c N := by
      rw [div_le_iff₀ (by positivity)]
      have hLc0 : 0 < Lc := lt_of_lt_of_le (by norm_num) hLc3
      have hlt : N < Lc * (M + 1) := by
        simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N hLc0
      have hc : (N : ℝ) ≤ ((Lc * (M + 1) : ℕ) : ℝ) := by exact_mod_cast hlt.le
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hc
      exact hc.trans (mul_le_mul_of_nonneg_right hLc_le_Hc (by positivity))
    have hlog_diff : Real.log (N : ℝ) - Real.log ((M : ℝ) + 1) ≤
        Real.log H_cut + Real.log (c N) := by
      rw [← Real.log_div hN0.ne' (by positivity), ← Real.log_mul hH_pos.ne' hc0.ne']
      exact Real.log_le_log (by positivity) hNM1
    have h1H : 1 + Real.log H_cut ≤ L ^ (1 / 64 : ℝ) := by
      linarith only [hL_64, hR, le_abs_self (Real.log H_cut)]
    linarith only [h1, hlog_diff, h1H, hlogc_le]
  clear_value M Lc
  set q := primeAboveLowPacket N
  obtain ⟨hq_prime, _, hq_le⟩ := primeAboveLowPacket_spec N
  have hq_pr : q.Prime := hq_prime
  have hq2 : 2 ≤ q := hq_pr.two_le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq_pr.pos
  have h2_rpow : (2 : ℝ) ≤ L ^ (13 / 32 : ℝ) :=
    (by norm_num : (2 : ℝ) ≤ (4 : ℝ) ^ (1 : ℕ)).trans
      (four_pow_nat_le_rpow (e := 13 / 32) 1 hL_big (by norm_num) (by norm_num))
  have hq_le_4 : (q : ℝ) ≤ 4 * L ^ (13 / 32 : ℝ) := by
    have hQ : (lowPacketCutoff N : ℝ) ≤ L ^ (13 / 32 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg hL0.le _)
    have hmax : ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
      rw [Nat.cast_max, Nat.cast_ofNat]; exact max_le h2_rpow hQ
    have hqc : (q : ℝ) ≤ 2 * ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) := by exact_mod_cast hq_le
    linarith only [hqc, hmax, h2_rpow]
  set v := normalizedRamanujanHorizonVector q N
  set u := (conductorSubspace (lowPacketCutoff N) N).starProjection v
  have hcol_sub : horizonCollarVector M (lowPacketOrthogonalPrimeQuasimode N) =
      horizonCollarVector M v - horizonCollarVector M u := by
    ext ⟨n, hn⟩
    change (if M < n then primeHorizonExtension (v - u) n else 0) =
      (if M < n then primeHorizonExtension v n else 0) -
        (if M < n then primeHorizonExtension u n else 0)
    rw [primeHorizonExtension_coe (v - u) ⟨n, hn⟩, primeHorizonExtension_coe v ⟨n, hn⟩,
      primeHorizonExtension_coe u ⟨n, hn⟩, PiLp.sub_apply]
    split_ifs <;> ring
  have hyv_sq : ‖horizonCollarVector M v‖ ^ 2 ≤ (q : ℝ) / L * ∑ n ∈ Ioc M N, 1 / (n : ℝ) := by
    rw [← sum_primeHorizonExtension_sq]
    have hsplit : Icc 1 N = Icc 1 M ∪ Ioc M N := by
      ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    rw [hsplit, sum_union (disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_Icc] at h1; simp only [mem_Ioc] at h2; omega)]
    have hz1 : ∑ n ∈ Icc 1 M, primeHorizonExtension (horizonCollarVector M v) n ^ 2 = 0 := by
      refine sum_eq_zero fun n hn => ?_
      have hnN : n ∈ Icc 1 N := mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
      rw [primeHorizonExtension_coe _ ⟨n, hnN⟩]
      change (if M < n then primeHorizonExtension v n else 0) ^ 2 = 0
      rw [if_neg (Nat.not_lt.mpr (mem_Icc.mp hn).2), zero_pow (by norm_num)]
    rw [hz1, zero_add, mul_sum]
    refine sum_le_sum fun n hn => ?_
    obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hn
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt ((Nat.zero_le M).trans_lt hn_lo)
    have hnN : n ∈ Icc 1 N := mem_Icc.mpr ⟨hn1, hn_hi⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [primeHorizonExtension_coe _ ⟨n, hnN⟩]
    change (if M < n then primeHorizonExtension v n else 0) ^ 2 ≤ _
    rw [if_pos hn_lo, primeHorizonExtension_coe v ⟨n, hnN⟩]
    change ((Real.sqrt (Real.log (N : ℝ)))⁻¹ * (normalizedRamanujanMode q n / Real.sqrt n)) ^ 2 ≤ _
    have hmode_sq : normalizedRamanujanMode q n ^ 2 ≤ q := by
      have hqt : (q.totient : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.totient_prime hq_pr, Nat.cast_sub hq_pr.one_lt.le, Nat.cast_one]
      have hqm1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
        have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
        linarith
      rw [normalizedRamanujanMode_eq_coefficient hq_pr.pos,
        ramanujanLagCoefficient_of_prime hq_pr n, hqt, div_pow,
        Real.sq_sqrt (by linarith)]
      by_cases hdvd : q ∣ n
      · rw [if_pos hdvd, sq, mul_div_cancel_right₀ _ (by linarith)]
        linarith
      · rw [if_neg hdvd, neg_sq, one_pow]
        exact (div_le_one_of_le₀ hqm1 (by linarith)).trans (by linarith)
    rw [mul_pow, inv_pow, Real.sq_sqrt hL0.le, div_pow, Real.sq_sqrt hn0.le, ← div_eq_inv_mul,
      div_div]
    calc normalizedRamanujanMode q n ^ 2 / ((n : ℝ) * L)
        ≤ (q : ℝ) / ((n : ℝ) * L) := div_le_div_of_nonneg_right hmode_sq (by positivity)
      _ = (q : ℝ) / L * (1 / (n : ℝ)) := by ring
  clear_value v
  have hyv_rpow : c N * ‖horizonCollarVector M v‖ ^ 2 ≤ 8 / L ^ (7 / 16 : ℝ) := by
    calc c N * ‖horizonCollarVector M v‖ ^ 2
        ≤ L ^ (9 / 64 : ℝ) * (((4 * L ^ (13 / 32 : ℝ)) / L) * (2 * L ^ (1 / 64 : ℝ))) :=
          mul_le_mul hc_le_9_64
            (hyv_sq.trans (mul_le_mul (div_le_div_of_nonneg_right hq_le_4 hL0.le) hinv_le
              (sum_nonneg fun _ _ => by positivity) (by positivity)))
            (sq_nonneg _) (by positivity)
      _ = 8 / L ^ (7 / 16 : ℝ) := by
          rw [show L ^ (9 / 64 : ℝ) * (((4 * L ^ (13 / 32 : ℝ)) / L) * (2 * L ^ (1 / 64 : ℝ))) =
            8 * (L ^ (9 / 64 : ℝ) * L ^ (13 / 32 : ℝ) * L ^ (1 / 64 : ℝ) / L) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_sub_one hL0.ne']
          have hexp : (9 / 64 + 13 / 32 + 1 / 64 - 1 : ℝ) = -(7 / 16) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
  have hyu_rpow : c N * ‖horizonCollarVector M u‖ ^ 2 ≤ 1170 ^ 2 / L ^ (7 / 16 : ℝ) := by
    have h1q : 1 + Real.log q ≤ 65 * L ^ (1 / 64 : ℝ) := by
      have hq_4L : (q : ℝ) ≤ 4 * L :=
        hq_le_4.trans (mul_le_mul_of_nonneg_left
          ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
          (by norm_num))
      have hlq : Real.log (q : ℝ) ≤ Real.log (4 * L) := Real.log_le_log hq0 hq_4L
      rw [Real.log_mul (by norm_num) hL0.ne'] at hlq
      have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
        have := Real.log_two_lt_d9
        linarith
      have h1_64 : 1 ≤ L ^ (1 / 64 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith only [hlq, hlog4, hlogL_le, h1_64]
    have hu_rpow : ‖u‖ ≤ 1170 / L ^ (63 / 64 : ℝ) := by
      calc ‖u‖ ≤ 18 * (1 + Real.log q) / L := hu_bd
        _ ≤ 18 * (65 * L ^ (1 / 64 : ℝ)) / L :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1q (by norm_num)) hL0.le
        _ = 1170 / L ^ (63 / 64 : ℝ) := by
            rw [show 18 * (65 * L ^ (1 / 64 : ℝ)) / L = 1170 * (L ^ (1 / 64 : ℝ) / L) by ring,
              ← Real.rpow_sub_one hL0.ne']
            have hexp : (1 / 64 - 1 : ℝ) = -(63 / 64) := by norm_num
            rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
    clear_value u q
    have hp := pow_le_pow_left₀ (norm_nonneg (horizonCollarVector M u))
      ((norm_horizonCollarVector_le M u).trans hu_rpow) 2
    rw [div_pow, ← Real.rpow_natCast (L ^ (63 / 64 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hp
    have hp' : ‖horizonCollarVector M u‖ ^ 2 ≤ 1170 ^ 2 / L ^ (63 / 32 : ℝ) := by
      norm_num at hp ⊢; exact hp
    calc c N * ‖horizonCollarVector M u‖ ^ 2
        ≤ L ^ (9 / 64 : ℝ) * (1170 ^ 2 / L ^ (63 / 32 : ℝ)) :=
          mul_le_mul hc_le_9_64 hp' (sq_nonneg _) (by positivity)
      _ = 1170 ^ 2 / L ^ (117 / 64 : ℝ) := by
          rw [show L ^ (9 / 64 : ℝ) * (1170 ^ 2 / L ^ (63 / 32 : ℝ)) =
            1170 ^ 2 * (L ^ (9 / 64 : ℝ) / L ^ (63 / 32 : ℝ)) by ring, ← Real.rpow_sub hL0]
          have hexp : (9 / 64 - 63 / 32 : ℝ) = -(117 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, ← div_eq_mul_inv]
      _ ≤ 1170 ^ 2 / L ^ (7 / 16 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hL0 _)
            (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have htri_sq : ‖horizonCollarVector M (lowPacketOrthogonalPrimeQuasimode N)‖ ^ 2 ≤
      2 * ‖horizonCollarVector M v‖ ^ 2 + 2 * ‖horizonCollarVector M u‖ ^ 2 := by
    rw [hcol_sub]
    have h1 := norm_sub_le (horizonCollarVector M v) (horizonCollarVector M u)
    have h2 : (‖horizonCollarVector M v‖ + ‖horizonCollarVector M u‖) ^ 2 ≤
        2 * ‖horizonCollarVector M v‖ ^ 2 + 2 * ‖horizonCollarVector M u‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖horizonCollarVector M v‖ - ‖horizonCollarVector M u‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hm := mul_le_mul_of_nonneg_left htri_sq hc0.le
  rw [mul_add, mul_left_comm (c N) 2, mul_left_comm (c N) 2] at hm
  calc c N * ‖horizonCollarVector M (lowPacketOrthogonalPrimeQuasimode N)‖ ^ 2
      ≤ 2 * (8 / L ^ (7 / 16 : ℝ)) + 2 * (1170 ^ 2 / L ^ (7 / 16 : ℝ)) :=
        hm.trans (add_le_add (mul_le_mul_of_nonneg_left hyv_rpow zero_le_two)
          (mul_le_mul_of_nonneg_left hyu_rpow zero_le_two))
    _ ≤ (32 + 2 * 1170 ^ 2) / L ^ (7 / 16 : ℝ) := by
        rw [show 2 * (8 / L ^ (7 / 16 : ℝ)) + 2 * (1170 ^ 2 / L ^ (7 / 16 : ℝ)) =
          (16 + 2 * 1170 ^ 2) / L ^ (7 / 16 : ℝ) by ring]
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- **The `4 / 13` physical-tearing Schur limit on `(conductorSubspace (lowPacketCutoff N) N)ᗮ`.**
Along any critical schedule `c_N ≥ 1` with `c_N⁸ / log N → R > 0`, splitting
`z_N = lowPacketOrthogonalPrimeQuasimode N ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ` across
`M_N = N / linearDefectCutoff (c_N)` into `p_N = horizonPrefixVector M_N z_N` and
`y_N = horizonCollarVector M_N z_N` forces the normalized prefix–collar Schur ratio to converge
to `4 / 13` for every collar `L²` shift `B_R ∈ ℝ`. -/
theorem tendsto_prime_quasimode_prefix_collar_schur_ratio {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) (B_R : ℝ) :
    Tendsto (fun N : ℕ =>
      let M := N / linearDefectCutoff (c N)
      let z := lowPacketOrthogonalPrimeQuasimode N
      let U_p := normalizedCentredAtomicTest tiltedUnitSpline
        (primeHorizonExtension (horizonPrefixVector M z)) (c N) N
      let U_y := normalizedCentredAtomicTest tiltedUnitSpline
        (primeHorizonExtension (horizonCollarVector M z)) (c N) N
      weilBilin U_y U_p ^ 2 /
        (weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2)))
      atTop (𝓝 (4 / 13 : ℝ)) := by
  let φ := tiltedUnitSpline
  have hφ := contDiff_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_eq_zero
  have hI₂ := integral_tiltedUnitSpline_sq_pos
  set I₂ := ∫ u, φ u ^ 2
  set LL : ℕ → ℝ := fun N => Real.log (Real.log (N : ℝ))
  have hLL_tend : Tendsto LL atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hE_full := tendsto_quasimode_full_energy_div_log_log hR hc1 htend
  have hE_pre := tendsto_quasimode_prefix_energy_div_log_log hR hc1 htend
  have hE_col := tendsto_quasimode_collar_energy_div_log_log hR hc1 htend
  have hnorm_col := tendsto_c_mul_quasimode_collar_norm_sq_zero hR hc1 htend
  have hcross_lim : Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
        (horizonCollarVector (N / linearDefectCutoff (c N)) (lowPacketOrthogonalPrimeQuasimode N)),
        horizonPrefixVector (N / linearDefectCutoff (c N)) (lowPacketOrthogonalPrimeQuasimode N)⟫ /
        LL N) atTop (𝓝 (-(1 / 8 : ℝ))) := by
    have hlin := ((hE_full.sub hE_pre).sub hE_col).div_const 2
    rw [show ((9 / 32 : ℝ) - 13 / 32 - 1 / 8) / 2 = -(1 / 8) by norm_num] at hlin
    refine hlin.congr fun N => ?_
    set M := N / linearDefectCutoff (c N)
    set z := lowPacketOrthogonalPrimeQuasimode N
    set p := horizonPrefixVector M z
    set y := horizonCollarVector M z
    have hz_add : p + y = z := horizonPrefixVector_add_collar M z
    have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ (c N) N)
    change ((completeWeilEnergy φ (c N) N z / LL N -
        completeWeilEnergy φ (c N) N p / LL N -
        completeWeilEnergy φ (c N) N y / LL N) / 2) =
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) y, p⟫ / LL N
    clear_value M z p y
    have hpol : completeWeilEnergy φ (c N) N z =
        completeWeilEnergy φ (c N) N p + completeWeilEnergy φ (c N) N y +
          2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) y, p⟫ := by
      rw [← hz_add]
      unfold completeWeilEnergy
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym p y,
        real_inner_comm p (Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) y)]
      ring
    rw [hpol]
    ring
  have hshift_lim : Tendsto (fun N : ℕ =>
      (c N / I₂) * B_R *
        (∫ u, normalizedCentredAtomicTest φ
          (primeHorizonExtension (horizonCollarVector (N / linearDefectCutoff (c N))
            (lowPacketOrthogonalPrimeQuasimode N))) (c N) N u ^ 2) / LL N) atTop (𝓝 0) := by
    have hub : Tendsto (fun N : ℕ =>
        (|B_R| * (1 + 2 * Real.exp 1)) *
          (c N * ‖horizonCollarVector (N / linearDefectCutoff (c N))
            (lowPacketOrthogonalPrimeQuasimode N)‖ ^ 2) * (1 / LL N)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => 1 / LL N) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hLL_tend
      simpa only [mul_zero] using (hnorm_col.const_mul (|B_R| * (1 + 2 * Real.exp 1))).mul h1
    refine squeeze_zero_norm' ?_ hub
    have hLN_zero : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop).congr fun N => by dsimp only [Function.comp_def]; ring
    filter_upwards [hc1, htend.eventually (gt_mem_nhds (by linarith : R < R + 1)),
      hLL_tend.eventually_gt_atTop 0, eventually_ge_atTop 3,
      hLN_zero.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (R + 1)))]
      with N hcN hratN hLL0 hN3 hLN
    have hN1 : 1 ≤ N := by omega
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hc0 : 0 < c N := zero_lt_one.trans_le hcN
    have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hcN_le_N : c N ≤ N := by
      have hc8 : c N ≤ c N ^ 8 := le_self_pow₀ hcN (by omega)
      have h1 : c N ^ 8 ≤ (R + 1) * Real.log (N : ℝ) := ((div_lt_iff₀ hL0).mp hratN).le
      have h2 : (R + 1) * Real.log (N : ℝ) ≤ N := by
        have hlt := (div_lt_iff₀ hN0).mp hLN
        have hpos : 0 < R + 1 := by linarith
        linarith [(lt_div_iff₀ hpos).mp (by
          calc Real.log (N : ℝ) < 1 / (R + 1) * N := hlt
            _ = (N : ℝ) / (R + 1) := by ring)]
      exact hc8.trans (h1.trans h2)
    set y := horizonCollarVector (N / linearDefectCutoff (c N))
      (lowPacketOrthogonalPrimeQuasimode N)
    set U_y := normalizedCentredAtomicTest φ (primeHorizonExtension y) (c N) N
    have hUy_nn : 0 ≤ ∫ u, U_y u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hUy_le : (∫ u, U_y u ^ 2) ≤ (1 + 2 * Real.exp 1) * I₂ * ‖y‖ ^ 2 :=
      (integral_normalizedCentredAtomicTest_sq_le hφ.continuous hsupp hcN hN1 hcN_le_N _).trans_eq
        (by rw [sum_primeHorizonExtension_sq])
    change ‖(c N / I₂) * B_R * (∫ u, U_y u ^ 2) / LL N‖ ≤
      (|B_R| * (1 + 2 * Real.exp 1)) * (c N * ‖y‖ ^ 2) * (1 / LL N)
    clear_value y U_y
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos (div_pos hc0 hI₂),
      abs_of_nonneg hUy_nn, abs_of_pos hLL0]
    calc c N / I₂ * |B_R| * (∫ u, U_y u ^ 2) / LL N
        ≤ c N / I₂ * |B_R| * ((1 + 2 * Real.exp 1) * I₂ * ‖y‖ ^ 2) / LL N :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hUy_le (by positivity)) hLL0.le
      _ = (|B_R| * (1 + 2 * Real.exp 1)) * (c N * ‖y‖ ^ 2) * (1 / LL N) := by
          field_simp [hI₂.ne', hLL0.ne']
  have hnum_lim : Tendsto (fun N : ℕ =>
      (⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
        (horizonCollarVector (N / linearDefectCutoff (c N)) (lowPacketOrthogonalPrimeQuasimode N)),
        horizonPrefixVector (N / linearDefectCutoff (c N)) (lowPacketOrthogonalPrimeQuasimode N)⟫ /
        LL N) ^ 2) atTop (𝓝 ((1 / 64 : ℝ))) := by
    rw [show (1 / 64 : ℝ) = (-(1 / 8 : ℝ)) ^ 2 by norm_num]
    exact hcross_lim.pow 2
  have hden_lim : Tendsto (fun N : ℕ =>
      (completeWeilEnergy φ (c N) N
        (horizonPrefixVector (N / linearDefectCutoff (c N))
          (lowPacketOrthogonalPrimeQuasimode N)) / LL N) *
      (completeWeilEnergy φ (c N) N
        (horizonCollarVector (N / linearDefectCutoff (c N))
          (lowPacketOrthogonalPrimeQuasimode N)) / LL N +
        (c N / I₂) * B_R *
          (∫ u, normalizedCentredAtomicTest φ
            (primeHorizonExtension (horizonCollarVector (N / linearDefectCutoff (c N))
              (lowPacketOrthogonalPrimeQuasimode N))) (c N) N u ^ 2) / LL N))
      atTop (𝓝 ((13 / 256 : ℝ))) := by
    rw [show (13 / 256 : ℝ) = (13 / 32 : ℝ) * ((1 / 8 : ℝ) + 0) by norm_num]
    exact hE_pre.mul (hE_col.add hshift_lim)
  have hquot_lim : Tendsto (fun N : ℕ =>
      (⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
        (horizonCollarVector (N / linearDefectCutoff (c N)) (lowPacketOrthogonalPrimeQuasimode N)),
        horizonPrefixVector (N / linearDefectCutoff (c N)) (lowPacketOrthogonalPrimeQuasimode N)⟫ /
        LL N) ^ 2 /
      ((completeWeilEnergy φ (c N) N
        (horizonPrefixVector (N / linearDefectCutoff (c N))
          (lowPacketOrthogonalPrimeQuasimode N)) / LL N) *
      (completeWeilEnergy φ (c N) N
        (horizonCollarVector (N / linearDefectCutoff (c N))
          (lowPacketOrthogonalPrimeQuasimode N)) / LL N +
        (c N / I₂) * B_R *
          (∫ u, normalizedCentredAtomicTest φ
            (primeHorizonExtension (horizonCollarVector (N / linearDefectCutoff (c N))
              (lowPacketOrthogonalPrimeQuasimode N))) (c N) N u ^ 2) / LL N)))
      atTop (𝓝 (4 / 13 : ℝ)) := by
    rw [show (4 / 13 : ℝ) = (1 / 64 : ℝ) / (13 / 256) by norm_num]
    exact hnum_lim.div hden_lim (by norm_num)
  refine hquot_lim.congr' ?_
  filter_upwards [hc1, hLL_tend.eventually_gt_atTop 0, eventually_ge_atTop 1]
    with N hcN hLL0 hN1
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
  set M := N / linearDefectCutoff (c N)
  set z := lowPacketOrthogonalPrimeQuasimode N
  set p := horizonPrefixVector M z
  set y := horizonCollarVector M z
  set U_p := normalizedCentredAtomicTest φ (primeHorizonExtension p) (c N) N
  set U_y := normalizedCentredAtomicTest φ (primeHorizonExtension y) (c N) N
  have hbil := weilBilin_normalizedCentredAtomicTest_eq hφ hsupp hI₂ hc0 hN1 y p
  have hqp := weilQuad_normalizedCentredAtomicTest_eq hφ hsupp hI₂ hc0 hN1 p
  have hqy := weilQuad_normalizedCentredAtomicTest_eq hφ hsupp hI₂ hc0 hN1 y
  change (⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) y, p⟫ / LL N) ^ 2 /
      ((completeWeilEnergy φ (c N) N p / LL N) *
        (completeWeilEnergy φ (c N) N y / LL N +
          (c N / I₂) * B_R * (∫ u, U_y u ^ 2) / LL N)) =
    weilBilin U_y U_p ^ 2 / (weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2))
  change weilBilin U_y U_p = (I₂ / c N) * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) y, p⟫
    at hbil
  change weilQuad U_p = (I₂ / c N) * completeWeilEnergy φ (c N) N p at hqp
  change weilQuad U_y = (I₂ / c N) * completeWeilEnergy φ (c N) N y at hqy
  clear_value M z p y U_p U_y
  rw [hbil, hqp, hqy]
  field_simp [hI₂.ne', hc0.ne', hLL0.ne']

/-- **Refutation of naive physical prefix–collar Schur decoupling on `(conductorSubspace Q₁ N)ᗮ`.**
Along any critical schedule `c_N ≥ 1` with `c_N⁸ / log N → R > 0`, no shift `B_R ∈ ℝ` makes the
physical split `z = horizonPrefixVector M z + horizonCollarVector M z` across
`M = N / linearDefectCutoff (c_N)` satisfy `o(1)` Schur decoupling on
`(conductorSubspace (lowPacketCutoff N) N)ᗮ`. -/
theorem not_naive_physical_prefix_collar_schur_decoupling {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) (B_R : ℝ) :
    ¬(∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ z ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ,
          let M := N / linearDefectCutoff (c N)
          let U_p := normalizedCentredAtomicTest tiltedUnitSpline
            (primeHorizonExtension (horizonPrefixVector M z)) (c N) N
          let U_y := normalizedCentredAtomicTest tiltedUnitSpline
            (primeHorizonExtension (horizonCollarVector M z)) (c N) N
          weilBilin U_y U_p ^ 2 ≤
            ε * weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2)) := by
  intro hdec
  have hrat := (tendsto_prime_quasimode_prefix_collar_schur_ratio hR hc1 htend B_R).eventually
    (lt_mem_nhds (by norm_num : (3 / 13 : ℝ) < 4 / 13))
  have hE_pre := (tendsto_quasimode_prefix_energy_div_log_log hR hc1 htend).eventually
    (lt_mem_nhds (by norm_num : (0 : ℝ) < 13 / 32))
  have hLL_pos := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_gt_atTop 0
  obtain ⟨N, hdecN, hratN, hpreN, hcN, hLL0, hN1⟩ :=
    ((hdec (2 / 13) (by norm_num)).and
      (hrat.and (hE_pre.and (hc1.and (hLL_pos.and (eventually_ge_atTop 1)))))).exists
  dsimp only [Function.comp_def] at hratN hLL0
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
  have hI₂ := integral_tiltedUnitSpline_sq_pos
  set M := N / linearDefectCutoff (c N)
  set z := lowPacketOrthogonalPrimeQuasimode N
  set U_p := normalizedCentredAtomicTest tiltedUnitSpline
    (primeHorizonExtension (horizonPrefixVector M z)) (c N) N
  set U_y := normalizedCentredAtomicTest tiltedUnitSpline
    (primeHorizonExtension (horizonCollarVector M z)) (c N) N
  have hspec := hdecN z (lowPacketOrthogonalPrimeQuasimode_mem N)
  dsimp only at hspec
  have hEp_pos : 0 < completeWeilEnergy tiltedUnitSpline (c N) N (horizonPrefixVector M z) :=
    (div_pos_iff_of_pos_right hLL0).mp hpreN
  have hQp_pos : 0 < weilQuad U_p := by
    rw [weilQuad_normalizedCentredAtomicTest_eq contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      hI₂ hc0 hN1]
    exact mul_pos (div_pos hI₂ hc0) hEp_pos
  have hden_pos : 0 < weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2) := by
    by_contra hle
    have hnp : weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2) ≤ 0 := not_lt.mp hle
    have hq_np : weilBilin U_y U_p ^ 2 /
        (weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2)) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hnp
    linarith only [hratN, hq_np]
  have hle_2_13 : weilBilin U_y U_p ^ 2 /
      (weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2)) ≤ 2 / 13 := by
    rw [div_le_iff₀ hden_pos]
    linarith only [hspec, (by ring : (2 / 13 : ℝ) * (weilQuad U_p *
      (weilQuad U_y + B_R * ∫ u, U_y u ^ 2)) =
      (2 / 13 : ℝ) * weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2))]
  linarith only [hratN, hle_2_13]

/-! ### 3. Conductor-adapted `o(1)` prefix–collar Schur decoupling on `(conductorSubspace R₁ N)ᗮ` -/

/-- Sub-polynomial far-conductor cutoff `R₁(N) = ⌊N^{1 / (1 + log log N)⁵}⌋₊`. -/
def farConductorCutoff (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ (1 / (1 + Real.log (Real.log (N : ℝ))) ^ 5)⌋₊

private theorem sq_le_four_mul_of_forall_pos {A X Y : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : ∀ γ : ℝ, 0 < γ → A ≤ γ * X + γ⁻¹ * Y) :
    A ^ 2 ≤ 4 * X * Y := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · rw [← hA0, zero_pow two_ne_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hX) hY
  by_contra hlt
  push Not at hlt
  set δ := A ^ 2 - 4 * X * Y
  have hδ : 0 < δ := sub_pos.mpr hlt
  set X' := X + δ / (8 * (Y + 1))
  have hX' : 0 < X' := by positivity
  have hγ := h (A / (2 * X')) (div_pos hApos (by positivity))
  have h1 : A / (2 * X') * X ≤ A / 2 := by
    have hx : X ≤ X' := le_add_of_nonneg_right (by positivity)
    calc A / (2 * X') * X ≤ A / (2 * X') * X' := mul_le_mul_of_nonneg_left hx (by positivity)
      _ = A / 2 := by field_simp [hX'.ne']
  have h2 : (A / (2 * X'))⁻¹ * Y = 2 * X' * Y / A := by field_simp [hApos.ne', hX'.ne']
  have h3 : A / 2 ≤ 2 * X' * Y / A := by linarith only [hγ, h1, h2]
  have h4 : A / 2 * A ≤ 2 * X' * Y := (le_div_iff₀ hApos).mp h3
  have h5 : 4 * X' * Y < 4 * X * Y + δ := by
    have hYle : Y ≤ Y + 1 := by linarith
    have hYp : 0 < Y + 1 := by positivity
    have hd : δ / (8 * (Y + 1)) * Y ≤ δ / 8 := by
      calc δ / (8 * (Y + 1)) * Y ≤ δ / (8 * (Y + 1)) * (Y + 1) :=
            mul_le_mul_of_nonneg_left hYle (by positivity)
        _ = δ / 8 := by field_simp [hYp.ne']
    dsimp only [X']
    linarith only [hd, hδ, (by ring : 4 * (X + δ / (8 * (Y + 1))) * Y =
      4 * X * Y + 4 * (δ / (8 * (Y + 1)) * Y))]
  dsimp only [δ] at h5
  linarith only [h4, h5, (by ring : A ^ 2 = 2 * (A / 2 * A))]

private theorem weilQuad_eq_arch_sub_prime_add_pole_moments {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    weilQuad f = archForm f - primeSum f +
      2 * (∫ u, f u * Real.exp (-(u / 2))) * (∫ u, f u * Real.exp (u / 2)) := by
  have ic : Integrable (fun u => f u * Real.cosh (u / 2)) :=
    (hf.continuous.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hfc.mul_right
  have is : Integrable (fun u => f u * Real.sinh (u / 2)) :=
    (hf.continuous.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hfc.mul_right
  have hplus : coshHalfMoment f + sinhHalfMoment f = ∫ u, f u * Real.exp (u / 2) := by
    unfold coshHalfMoment sinhHalfMoment
    rw [← integral_add ic is]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hminus : coshHalfMoment f - sinhHalfMoment f = ∫ u, f u * Real.exp (-(u / 2)) := by
    unfold coshHalfMoment sinhHalfMoment
    rw [← integral_sub ic is]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hpole : 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 =
      2 * (∫ u, f u * Real.exp (-(u / 2))) * (∫ u, f u * Real.exp (u / 2)) := by
    rw [← hminus, ← hplus]
    ring
  have h1 := weilQuad_eq hf hfc
  have h2 := archForm_eq_levyEnergy hf hfc
  linarith only [h1, h2, hpole]

private theorem weilBilin_split_eq {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    weilBilin f g =
      (archForm (fun u => f u + g u) - archForm (fun u => f u - g u)) / 4 -
        (primeSum (fun u => f u + g u) - primeSum (fun u => f u - g u)) / 4 +
        ((∫ u, f u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) +
          (∫ u, g u * Real.exp (-(u / 2))) * (∫ u, f u * Real.exp (u / 2))) := by
  have if_m : Integrable (fun u => f u * Real.exp (-(u / 2))) :=
    (hf.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have ig_m : Integrable (fun u => g u * Real.exp (-(u / 2))) :=
    (hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have if_p : Integrable (fun u => f u * Real.exp (u / 2)) :=
    (hf.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have ig_p : Integrable (fun u => g u * Real.exp (u / 2)) :=
    (hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have ham : (∫ u, (f u + g u) * Real.exp (-(u / 2))) =
      (∫ u, f u * Real.exp (-(u / 2))) + ∫ u, g u * Real.exp (-(u / 2)) := by
    simp_rw [add_mul]; exact integral_add if_m ig_m
  have hsm : (∫ u, (f u - g u) * Real.exp (-(u / 2))) =
      (∫ u, f u * Real.exp (-(u / 2))) - ∫ u, g u * Real.exp (-(u / 2)) := by
    simp_rw [sub_mul]; exact integral_sub if_m ig_m
  have hap : (∫ u, (f u + g u) * Real.exp (u / 2)) =
      (∫ u, f u * Real.exp (u / 2)) + ∫ u, g u * Real.exp (u / 2) := by
    simp_rw [add_mul]; exact integral_add if_p ig_p
  have hsp : (∫ u, (f u - g u) * Real.exp (u / 2)) =
      (∫ u, f u * Real.exp (u / 2)) - ∫ u, g u * Real.exp (u / 2) := by
    simp_rw [sub_mul]; exact integral_sub if_p ig_p
  unfold weilBilin
  rw [weilQuad_eq_arch_sub_prime_add_pole_moments (hf.add hg) (hfc.add hgc),
    weilQuad_eq_arch_sub_prime_add_pole_moments (hf.sub hg) (hfc.sub hgc),
    ham, hsm, hap, hsp]
  ring

private theorem archBilin_ordered_sq_le {f g : ℝ → ℝ} {b : ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) :
    ((archForm (fun u => f u + g u) - archForm (fun u => f u - g u)) / 4) ^ 2 ≤
      4 * Real.pi ^ 2 * (∫ u, f u ^ 2) * (∫ u, g u ^ 2) := by
  have hfg : ∀ u, f u * g u = 0 := fun u => by
    by_cases h : b ≤ u
    · rw [hleft u h, zero_mul]
    · rw [hright u (le_of_not_ge h), mul_zero]
  let ng : ℝ → ℝ := fun u => (-1 : ℝ) * g u
  have hng : ContDiff ℝ 2 ng := contDiff_const.mul hg
  have hngc : HasCompactSupport ng := hgc.mul_left
  have hfng : ∀ u, f u * ng u = 0 := fun u => by
    dsimp only [ng]; rw [mul_left_comm, hfg u, mul_zero]
  have hplus : archForm (fun u => f u + g u) = archForm f + archForm g +
      2 * (-∫ x in Set.Ioi (0 : ℝ),
        archLevyDensity x * ArithmeticIndexDescent.sourceCollarCorrelation f g x) := by
    rw [archForm_add_eq hf hfc hg hgc,
      ArithmeticIndexDescent.archCross_eq_neg_sourceCollar_of_disjoint hf hfc hg hgc hfg]
  have hsc_neg : ∀ x : ℝ, ArithmeticIndexDescent.sourceCollarCorrelation f ng x =
      -ArithmeticIndexDescent.sourceCollarCorrelation f g x := fun x => by
    unfold ArithmeticIndexDescent.sourceCollarCorrelation
    have heq : (fun u => f u * ng (u + x) + f (u + x) * ng u) =
        fun u => -(f u * g (u + x) + f (u + x) * g u) :=
      funext fun u => by dsimp only [ng]; ring
    rw [heq, integral_neg]
  have hminus : archForm (fun u => f u - g u) = archForm f + archForm g -
      2 * (-∫ x in Set.Ioi (0 : ℝ),
        archLevyDensity x * ArithmeticIndexDescent.sourceCollarCorrelation f g x) := by
    have hsub_eq : (fun u => f u - g u) = fun u => f u + ng u :=
      funext fun u => by dsimp only [ng]; ring
    have harch_ng : archForm ng = archForm g := by
      dsimp only [ng]; rw [archForm_const_mul hg hgc (-1)]; ring
    have hint_neg : (∫ x in Set.Ioi (0 : ℝ),
        archLevyDensity x * ArithmeticIndexDescent.sourceCollarCorrelation f ng x) =
        -∫ x in Set.Ioi (0 : ℝ),
          archLevyDensity x * ArithmeticIndexDescent.sourceCollarCorrelation f g x := by
      simp_rw [hsc_neg, mul_neg]
      exact integral_neg _
    rw [hsub_eq, archForm_add_eq hf hfc hng hngc,
      ArithmeticIndexDescent.archCross_eq_neg_sourceCollar_of_disjoint hf hfc hng hngc hfng,
      harch_ng, hint_neg]
    ring
  have hpol : (archForm (fun u => f u + g u) - archForm (fun u => f u - g u)) / 4 =
      -∫ x in Set.Ioi (0 : ℝ),
        archLevyDensity x * ArithmeticIndexDescent.sourceCollarCorrelation f g x := by
    rw [hplus, hminus]; ring
  set S := |∫ x in Set.Ioi (0 : ℝ),
    archLevyDensity x * ArithmeticIndexDescent.sourceCollarCorrelation f g x|
  have hsq : ((archForm (fun u => f u + g u) - archForm (fun u => f u - g u)) / 4) ^ 2 = S ^ 2 := by
    rw [hpol, neg_sq, sq_abs]
  rw [hsq]
  have hIf0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hIg0 : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h4pi : 4 * Real.pi ^ 2 * (∫ u, f u ^ 2) * (∫ u, g u ^ 2) =
      4 * (Real.pi * ∫ u, f u ^ 2) * (Real.pi * ∫ u, g u ^ 2) := by ring
  rw [h4pi]
  refine sq_le_four_mul_of_forall_pos (abs_nonneg _)
    (mul_nonneg Real.pi_pos.le hIf0) (mul_nonneg Real.pi_pos.le hIg0) fun γ hγ => ?_
  set r := Real.sqrt γ
  have hr : 0 < r := Real.sqrt_pos.mpr hγ
  have hord := ArithmeticIndexDescent.abs_sourceGammaCollar_le_of_ordered
    (f := fun u => r * f u) (g := fun u => r⁻¹ * g u)
    (continuous_const.mul hf.continuous) hfc.mul_left
    (continuous_const.mul hg.continuous) hgc.mul_left
    (fun u hu => by rw [hleft u hu, mul_zero])
    (fun u hu => by rw [hright u hu, mul_zero])
  have hsc_scale : ∀ x : ℝ,
      ArithmeticIndexDescent.sourceCollarCorrelation (fun u => r * f u) (fun u => r⁻¹ * g u) x =
        ArithmeticIndexDescent.sourceCollarCorrelation f g x := fun x => by
    unfold ArithmeticIndexDescent.sourceCollarCorrelation
    congr 1
    funext u
    have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    calc r * f u * (r⁻¹ * g (u + x)) + r * f (u + x) * (r⁻¹ * g u)
        = (r * r⁻¹) * (f u * g (u + x) + f (u + x) * g u) := by ring
      _ = f u * g (u + x) + f (u + x) * g u := by rw [hrr, one_mul]
  simp_rw [hsc_scale] at hord
  have hr2 : r ^ 2 = γ := Real.sq_sqrt hγ.le
  have hmf : sectionMass (fun u => r * f u) = γ * ∫ u, f u ^ 2 := by
    change (∫ u, (r * f u) ^ 2) = γ * ∫ u, f u ^ 2
    simp_rw [mul_pow, hr2]
    exact integral_const_mul γ _
  have hmg : sectionMass (fun u => r⁻¹ * g u) = γ⁻¹ * ∫ u, g u ^ 2 := by
    change (∫ u, (r⁻¹ * g u) ^ 2) = γ⁻¹ * ∫ u, g u ^ 2
    simp_rw [mul_pow, inv_pow, hr2]
    exact integral_const_mul γ⁻¹ _
  rw [hmf, hmg] at hord
  linarith only [hord, (by ring : Real.pi * (γ * (∫ u, f u ^ 2) + γ⁻¹ * (∫ u, g u ^ 2)) =
    γ * (Real.pi * ∫ u, f u ^ 2) + γ⁻¹ * (Real.pi * ∫ u, g u ^ 2))]

private theorem collar_pole_sum_sq_le_topCollarSeventhMass {N M : ℕ} (hN1 : 1 ≤ N) (hMN : M ≤ N)
    {x : ℕ → ℝ} (hx : ∀ n, n ≤ M → x n = 0) :
    (∑ n ∈ Icc 1 N, x n / Real.sqrt n) ^ 2 ≤ topCollarSeventhMass M N x := by
  have hsplit : ∑ n ∈ Icc 1 N, x n / Real.sqrt n =
      ∑ n ∈ Icc 1 M, x n / Real.sqrt n + ∑ n ∈ Ioc M N, x n / Real.sqrt n := by
    have hdisj : Icc 1 N = Icc 1 M ∪ Ioc M N := by
      ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    rw [hdisj, sum_union]
    exact disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_Icc] at h1; simp only [mem_Ioc] at h2; omega
  have hpre0 : ∑ n ∈ Icc 1 M, x n / Real.sqrt n = 0 :=
    sum_eq_zero fun n hn => by rw [hx n (mem_Icc.mp hn).2, zero_div]
  rw [hsplit, hpre0, zero_add]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hfac : ∑ n ∈ Ioc M N, x n / Real.sqrt n =
      ∑ n ∈ Ioc M N, (Real.sqrt n / N) * (((N : ℝ) / n) * x n) := by
    refine sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    calc x n / Real.sqrt n = (Real.sqrt n / (Real.sqrt n * Real.sqrt n)) * x n := by
          field_simp [hsn]
      _ = (Real.sqrt n / n) * x n := by rw [Real.mul_self_sqrt hn0.le]
      _ = (Real.sqrt n / N) * (((N : ℝ) / n) * x n) := by field_simp [hNR.ne', hn0.ne']
  rw [hfac]
  have hcs := sum_mul_sq_le_sq_mul_sq (Ioc M N) (fun n : ℕ => Real.sqrt n / (N : ℝ))
    (fun n : ℕ => ((N : ℝ) / n) * x n)
  have h1 : ∑ n ∈ Ioc M N, (Real.sqrt n / (N : ℝ)) ^ 2 ≤ 1 := by
    have hterm : ∀ n ∈ Ioc M N, (Real.sqrt n / (N : ℝ)) ^ 2 ≤ 1 / (N : ℝ) := fun n hn => by
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp hn).2
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      calc (n : ℝ) / (N : ℝ) ^ 2 ≤ (N : ℝ) / (N : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hnN (sq_nonneg _)
        _ = 1 / (N : ℝ) := by field_simp [hNR.ne']
    have hsub : Ioc M N ⊆ Icc 1 N := fun n hn =>
      mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
    calc ∑ n ∈ Ioc M N, (Real.sqrt n / (N : ℝ)) ^ 2
        ≤ ∑ n ∈ Ioc M N, (1 : ℝ) / N := sum_le_sum hterm
      _ ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / N :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          field_simp [hNR.ne']
  have h2 : ∑ n ∈ Ioc M N, (((N : ℝ) / n) * x n) ^ 2 ≤ topCollarSeventhMass M N x := by
    unfold topCollarSeventhMass
    refine sum_le_sum fun n hn => ?_
    obtain ⟨hMn, hnN⟩ := mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 1 ≤ n by omega)
    have hge1 : (1 : ℝ) ≤ (N : ℝ) / n := (one_le_div hn0).mpr (by exact_mod_cast hnN)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hge1 (by norm_num : 2 ≤ 7)) (sq_nonneg _)
  exact hcs.trans ((mul_le_mul h1 h2 (sum_nonneg fun _ _ => sq_nonneg _) zero_le_one).trans_eq
    (one_mul _))

private theorem primeBilin_prefix_collar_eq {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ}
    (h2LN : 2 * linearDefectCutoff c ≤ N) {x_p x_y : ℕ → ℝ}
    (hp_supp : ∀ n, N / linearDefectCutoff c < n → x_p n = 0)
    (hy_supp : ∀ n, n ≤ N / linearDefectCutoff c → x_y n = 0) :
    let M := N / linearDefectCutoff c
    let g := atomDilate tiltedUnitSpline (c / N)
    let f_p := atomicTest N x_p g
    let f_y := atomicTest N x_y g
    let Bn := ⌊(N : ℝ) * Real.exp (c / N)⌋₊
    let K := primeOrderCutoff N (c / N)
    let F := atomicTest Bn (fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv K M x_p n) g
    (primeSum (fun u => f_p u + f_y u) - primeSum (fun u => f_p u - f_y u)) / 4 =
      ∫ u, f_y u * F u := by
  intro M g f_p f_y Bn K F
  let x_plus : ℕ → ℝ := fun n => x_p n + x_y n
  let x_minus : ℕ → ℝ := fun n => x_p n - x_y n
  have h_at_plus : atomicTest N x_plus g = fun u => f_p u + f_y u := by
    funext u; dsimp only [f_p, f_y, x_plus]; unfold atomicTest
    simp_rw [add_mul]; rw [sum_add_distrib]
  have h_at_minus : atomicTest N x_minus g = fun u => f_p u - f_y u := by
    funext u; dsimp only [f_p, f_y, x_minus]; unfold atomicTest
    simp_rw [sub_mul]; rw [sum_sub_distrib]
  have h_pre_plus : atomicTest M x_plus g = atomicTest M x_p g := by
    funext u; unfold atomicTest
    refine sum_congr rfl fun n hn => ?_
    dsimp only [x_plus]
    rw [hy_supp n (mem_Icc.mp hn).2, add_zero]
  have h_pre_minus : atomicTest M x_minus g = atomicTest M x_p g := by
    funext u; unfold atomicTest
    refine sum_congr rfl fun n hn => ?_
    dsimp only [x_minus]
    rw [hy_supp n (mem_Icc.mp hn).2, sub_zero]
  have h_tail_plus : atomicTailCoefficients M x_plus = x_y := by
    funext n; unfold atomicTailCoefficients; dsimp only [x_plus]
    by_cases h : M < n
    · rw [if_pos h, hp_supp n h, zero_add]
    · rw [if_neg h, hy_supp n (Nat.not_lt.mp h)]
  have h_tail_minus : atomicTailCoefficients M x_minus = fun n => (-1 : ℝ) * x_y n := by
    funext n; unfold atomicTailCoefficients; dsimp only [x_minus]
    by_cases h : M < n
    · rw [if_pos h, hp_supp n h]; ring
    · rw [if_neg h, hy_supp n (Nat.not_lt.mp h), mul_zero]
  have h_fy_neg : atomicTest N (fun n => (-1 : ℝ) * x_y n) g = fun u => (-1 : ℝ) * f_y u := by
    funext u; dsimp only [f_y]; unfold atomicTest
    simp_rw [mul_assoc]; rw [← mul_sum]
  have h_F_plus : atomicTest Bn (fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv K M x_plus n) g = F :=
    congrArg (fun a => atomicTest Bn a g) (funext fun n =>
      congrArg (topWeight ((M : ℝ) / 2) Bn n * ·) (primeConv_congr (fun m hm => by
        dsimp only [x_plus]; rw [hy_supp m (mem_Icc.mp hm).2, add_zero]) n))
  have h_F_minus : atomicTest Bn (fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv K M x_minus n) g = F :=
    congrArg (fun a => atomicTest Bn a g) (funext fun n =>
      congrArg (topWeight ((M : ℝ) / 2) Bn n * ·) (primeConv_congr (fun m hm => by
        dsimp only [x_minus]; rw [hy_supp m (mem_Icc.mp hm).2, sub_zero]) n))
  have hp1 := primeSum_prefix_top_split hc1 h2LN x_plus
  have hp2 := primeSum_prefix_top_split hc1 h2LN x_minus
  change primeSum (atomicTest N x_plus g) =
    primeSum (atomicTest M x_plus g) + primeSum (atomicTest N (atomicTailCoefficients M x_plus) g) +
      2 * ∫ u, atomicTest N (atomicTailCoefficients M x_plus) g u *
        atomicTest Bn (fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv K M x_plus n) g u at hp1
  change primeSum (atomicTest N x_minus g) =
    primeSum (atomicTest M x_minus g) + primeSum (atomicTest N (atomicTailCoefficients M x_minus) g) +
      2 * ∫ u, atomicTest N (atomicTailCoefficients M x_minus) g u *
        atomicTest Bn (fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv K M x_minus n) g u at hp2
  rw [h_at_plus, h_pre_plus, h_tail_plus, h_F_plus] at hp1
  rw [h_at_minus, h_pre_minus, h_tail_minus, h_fy_neg, h_F_minus,
    primeSum_const_mul (-1) f_y] at hp2
  have hint_neg : (∫ u, ((-1 : ℝ) * f_y u) * F u) = -∫ u, f_y u * F u := by
    have heq : (fun u => ((-1 : ℝ) * f_y u) * F u) = fun u => -(f_y u * F u) :=
      funext fun u => by ring
    rw [heq, integral_neg]
  rw [hint_neg] at hp2
  change primeSum (fun u => f_p u + f_y u) =
    primeSum (atomicTest M x_p g) + primeSum f_y + 2 * ∫ u, f_y u * F u at hp1
  linarith only [hp1, hp2, (by ring : (-1 : ℝ) ^ 2 * primeSum f_y = primeSum f_y)]

private theorem poleBilin_prefix_collar_sq_le {c κ_R Qy : ℝ} {N M : ℕ}
    (hc1 : 1 ≤ c) (hcN : c ≤ N) (hκR : 0 < κ_R) (hN1 : 1 ≤ N) (hMN : M ≤ N)
    (hML : (M : ℝ) * linearDefectCutoff c ≤ N)
    {x_p x_y : ℕ → ℝ}
    (hp_supp : ∀ n, M < n → x_p n = 0)
    (hy_supp : ∀ n, n ≤ M → x_y n = 0)
    (hp_pole_sum : ∑ n ∈ Icc 1 N, x_p n / Real.sqrt n = 0)
    (hS7_le_Qy : κ_R * topCollarSeventhMass M N x_y ≤ Qy) :
    let w := c / (N : ℝ)
    let g := atomDilate tiltedUnitSpline w
    let f_p := atomicTest N x_p g
    let f_y := atomicTest N x_y g
    let I₁ := ∫ u, tiltedUnitSpline u
    let I₂ := ∫ u, tiltedUnitSpline u ^ 2
    let P := ∑ n ∈ Icc 1 M, x_p n ^ 2
    let poleBilin :=
      (∫ u, f_p u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) +
        (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_p u * Real.exp (u / 2))
    (((N : ℝ) / c ^ 2) * poleBilin) ^ 2 ≤
      (Real.exp 2 * I₁ ^ 4 / (κ_R * I₂)) * ((I₂ / c) * P) * Qy := by
  dsimp only
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hI₂ : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  set I₁ := ∫ u, tiltedUnitSpline u
  set I₂ := ∫ u, tiltedUnitSpline u ^ 2
  set w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  set g := atomDilate tiltedUnitSpline w
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hgs := tiltedUnitSpline_atom_support hw
  set f_p := atomicTest N x_p g
  set f_y := atomicTest N x_y g
  set P := ∑ n ∈ Icc 1 M, x_p n ^ 2
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨_, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  have hAp0 : (∫ u, f_p u * Real.exp (-(u / 2))) = 0 := by
    rw [SelectiveMultiscaleArithmeticPositivity.integral_atomicTest_mul_exp_neg_half
      hg.continuous hgs N x_p, hp_pole_sum, mul_zero]
  have hint_g : (∫ u, g u) = w * I₁ := by
    have h := Measure.integral_comp_div (fun u => tiltedUnitSpline u) w
    simp only [smul_eq_mul, abs_of_pos hw] at h
    exact h
  have ig : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have igm : Integrable (fun u => g u * Real.exp (-(u / 2))) :=
    (hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have igp : Integrable (fun u => g u * Real.exp (u / 2)) :=
    (hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hg_nonneg : ∀ u, 0 ≤ g u := fun _ =>
    RenormalizedIntersectionTheory.tiltedUnitSpline_nonneg _
  have hAg_nn : 0 ≤ ∫ u, g u * Real.exp (-(u / 2)) :=
    integral_nonneg fun u => mul_nonneg (hg_nonneg u) (Real.exp_pos _).le
  have hAg_le : (∫ u, g u * Real.exp (-(u / 2))) ≤ w * I₁ := by
    rw [← hint_g]
    refine integral_mono igm ig fun u => ?_
    by_cases hu : u ∈ Set.Icc 0 w
    · exact mul_le_of_le_one_right (hg_nonneg u)
        (Real.exp_le_one_iff.mpr (by linarith [hu.1]))
    · have hg0 : g u = 0 := hgs u hu
      rw [hg0, zero_mul]
  have hBg_nn : 0 ≤ ∫ u, g u * Real.exp (u / 2) :=
    integral_nonneg fun u => mul_nonneg (hg_nonneg u) (Real.exp_pos _).le
  have hBg_le : (∫ u, g u * Real.exp (u / 2)) ≤ Real.exp 1 * (w * I₁) := by
    rw [← hint_g, ← integral_const_mul]
    refine integral_mono igp (ig.const_mul (Real.exp 1)) fun u => ?_
    dsimp only
    by_cases hu : u ∈ Set.Icc 0 w
    · calc g u * Real.exp (u / 2) ≤ g u * Real.exp 1 :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by linarith [hu.2, hw1])) (hg_nonneg u)
        _ = Real.exp 1 * g u := mul_comm _ _
    · have hg0 : g u = 0 := hgs u hu
      rw [hg0, zero_mul, mul_zero]
  have hAy_sq : (∫ u, f_y u * Real.exp (-(u / 2))) ^ 2 ≤ (w * I₁) ^ 2 * (Qy / κ_R) := by
    rw [SelectiveMultiscaleArithmeticPositivity.integral_atomicTest_mul_exp_neg_half
      hg.continuous hgs N x_y, mul_pow]
    have h1 : (∫ u, g u * Real.exp (-(u / 2))) ^ 2 ≤ (w * I₁) ^ 2 :=
      pow_le_pow_left₀ hAg_nn hAg_le 2
    have h2 : (∑ n ∈ Icc 1 N, x_y n / Real.sqrt n) ^ 2 ≤ Qy / κ_R :=
      (collar_pole_sum_sq_le_topCollarSeventhMass hN1 hMN hy_supp).trans
        ((le_div_iff₀ hκR).mpr (by linarith only [hS7_le_Qy, mul_comm κ_R (topCollarSeventhMass M N x_y)]))
    exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
  have hBp_sq : (∫ u, f_p u * Real.exp (u / 2)) ^ 2 ≤
      Real.exp 2 * (w * I₁) ^ 2 * ((N : ℝ) ^ 2 / c) * P := by
    rw [SelectiveMultiscaleArithmeticPositivity.integral_atomicTest_mul_exp_half
      hg.continuous hgs N x_p, mul_pow]
    have h1 : (∫ u, g u * Real.exp (u / 2)) ^ 2 ≤ Real.exp 2 * (w * I₁) ^ 2 := by
      have hp2 := pow_le_pow_left₀ hBg_nn hBg_le 2
      have he2 : (Real.exp 1 * (w * I₁)) ^ 2 = Real.exp 2 * (w * I₁) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; norm_num
      exact hp2.trans_eq he2
    have hsum_M : ∑ n ∈ Icc 1 N, x_p n * Real.sqrt n = ∑ n ∈ Icc 1 M, x_p n * Real.sqrt n := by
      refine (Finset.sum_subset (Icc_subset_Icc_right hMN) fun n hn hnot => ?_).symm
      have hgt : M < n := Nat.lt_of_not_le fun hle => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, hle⟩)
      rw [hp_supp n hgt, zero_mul]
    rw [hsum_M]
    have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 M) x_p (fun n : ℕ => Real.sqrt n)
    have hM_sum : ∑ n ∈ Icc 1 M, (Real.sqrt n) ^ 2 ≤ (M : ℝ) ^ 2 := by
      have hterm : ∀ n ∈ Icc 1 M, (Real.sqrt n) ^ 2 ≤ (M : ℝ) := fun n hn => by
        rw [Real.sq_sqrt (Nat.cast_nonneg n)]
        exact_mod_cast (mem_Icc.mp hn).2
      calc ∑ n ∈ Icc 1 M, (Real.sqrt n) ^ 2 ≤ ∑ _n ∈ Icc 1 M, (M : ℝ) := sum_le_sum hterm
        _ = (M : ℝ) ^ 2 := by
            rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    have hMc_le : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 / c := by
      rw [le_div_iff₀ hc0]
      have hMc : (M : ℝ) * c ≤ N := by
        have h4 : (M : ℝ) * (4 * c) ≤ (M : ℝ) * linearDefectCutoff c :=
          mul_le_mul_of_nonneg_left h4c (Nat.cast_nonneg M)
        have h1c : (M : ℝ) * c ≤ (M : ℝ) * (4 * c) := by
          have : 0 ≤ 3 * ((M : ℝ) * c) := by positivity
          linarith only [this, (by ring : (M : ℝ) * (4 * c) - (M : ℝ) * c = 3 * ((M : ℝ) * c))]
        exact (h1c.trans h4).trans hML
      have hsq_Mc : ((M : ℝ) * c) ^ 2 ≤ (N : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hMc 2
      have hc_sq : c ≤ c ^ 2 := le_self_pow₀ hc1 two_ne_zero
      have hm := mul_le_mul_of_nonneg_left hc_sq (sq_nonneg (M : ℝ))
      linarith only [hm, hsq_Mc, (by ring : ((M : ℝ) * c) ^ 2 = (M : ℝ) ^ 2 * c ^ 2)]
    have h2 : (∑ n ∈ Icc 1 M, x_p n * Real.sqrt n) ^ 2 ≤ ((N : ℝ) ^ 2 / c) * P := by
      have hP_M : P * ∑ n ∈ Icc 1 M, (Real.sqrt n) ^ 2 ≤ P * ((N : ℝ) ^ 2 / c) :=
        mul_le_mul_of_nonneg_left (hM_sum.trans hMc_le) hP0
      linarith only [hcs, hP_M, mul_comm P ((N : ℝ) ^ 2 / c)]
    exact (mul_le_mul h1 h2 (sq_nonneg _) (by positivity)).trans_eq (by ring)
  rw [hAp0, zero_mul, zero_add, mul_assoc, mul_pow, mul_pow]
  have hQy0 : 0 ≤ Qy := (mul_nonneg hκR.le (topCollarSeventhMass_nonneg M N x_y)).trans hS7_le_Qy
  have hprod := mul_le_mul hAy_sq hBp_sq (sq_nonneg _) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hprod (sq_nonneg ((N : ℝ) / c ^ 2))
  refine hmul.trans_eq ?_
  dsimp only [w]
  field_simp [hc0.ne', hNR.ne', hκR.ne', hI₂.ne']

private theorem windowSum_fh_algebraic_le
    {N_r c L h lam β K'_r HM C_β R₀ I₂ P Fh_int WS : ℝ}
    (hc1 : 1 ≤ c) (hNR : 0 < N_r) (hL1 : 1 ≤ L)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hlam1 : 1 ≤ lam) (hβ0 : 0 ≤ β)
    (hK'1 : 1 ≤ K'_r) (hHM0 : 0 ≤ HM) (hR₀0 : 0 < R₀) (hI₂ : 0 < I₂) (hP0 : 0 ≤ P)
    (hc_R₀ : c ≤ R₀ * L ^ (1 / 8 : ℝ))
    (hlam_eq : lam = L ^ (3 / 16 : ℝ))
    (hh_eq : h = Real.exp (-lam) / L)
    (hexp_N : 2 * (Real.log 4 + 4) * c * L * Real.exp (lam + β) ≤ N_r)
    (hHM_le : HM ≤ 1 + L)
    (hhL_le2 : h * (1 + L) ≤ 2)
    (hlogK' : Real.log K'_r ≤ β + 1)
    (hβ_le : β ≤ C_β * lam ^ 2)
    (hFh_mass : Fh_int ≤ ((c / N_r) * I₂) * (splineWindowConstant * ((c / N_r) / h ^ 2)) * WS)
    (hWS : ((c / N_r) / h ^ 2) * WS ≤
      (8 * Real.exp 2 * c * (1 + Real.log (2 * K'_r) + 4 * h ^ 2 * HM) +
        48 * Real.exp 1 * c * h * HM +
        2 * (β + 1 + (Real.log 4 + 4)) *
          (Real.exp 2 * c * (β + 1 + (Real.log 4 + 4)) +
            ((c / N_r) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)))) * P) :
    (N_r / c ^ 2) * Fh_int ≤
      (splineWindowConstant * R₀ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) *
        (C_β + 1 + (Real.log 4 + 4)) ^ 2) * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hswc0 : 0 ≤ splineWindowConstant := by unfold splineWindowConstant; positivity
  have hlog4 : 1 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  set w := c / N_r
  set ΛK : ℝ := β + 1 + (Real.log 4 + 4)
  have hΛK1 : 1 ≤ ΛK := by dsimp only [ΛK]; linarith only [hβ0, hlog4]
  set ΨK : ℝ := (Real.log 4 + 4) * (2 * Real.exp β)
  set C_B : ℝ := C_β + 1 + (Real.log 4 + 4)
  have hwhΨ : (w / h) * ΨK ≤ 1 := by
    have hid : (w / h) * ΨK = (2 * (Real.log 4 + 4) * c * L * Real.exp (lam + β)) / N_r := by
      dsimp only [w, ΨK]
      rw [hh_eq, Real.exp_neg, Real.exp_add]
      field_simp [hNR.ne', hL0.ne', (Real.exp_pos lam).ne']
    rw [hid]
    exact (div_le_one hNR).mpr hexp_N
  have hhH : h * HM ≤ 2 := (mul_le_mul_of_nonneg_left hHM_le hh0.le).trans hhL_le2
  have hh2H : h ^ 2 * HM ≤ 2 := by
    calc h ^ 2 * HM = h * (h * HM) := by ring
      _ ≤ 1 * 2 := mul_le_mul hh1 hhH (mul_nonneg hh0.le hHM0) zero_le_one
      _ = 2 := one_mul 2
  have hL2K : Real.log (2 * K'_r) ≤ ΛK + 1 := by
    have hK0 : 0 < K'_r := zero_lt_one.trans_le hK'1
    rw [Real.log_mul two_ne_zero hK0.ne']
    have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    dsimp only [ΛK]
    linarith only [hl2, hlogK', hlog4]
  have hΛ2_ge : ΛK ≤ ΛK ^ 2 := le_self_pow₀ hΛK1 two_ne_zero
  have hΛ1_ge : 1 ≤ ΛK ^ 2 := one_le_pow₀ hΛK1
  have hPc : 8 * Real.exp 2 * c * (1 + Real.log (2 * K'_r) + 4 * h ^ 2 * HM) +
      48 * Real.exp 1 * c * h * HM +
      2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK) ≤
      c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2 := by
    have t1 : 1 + Real.log (2 * K'_r) + 4 * h ^ 2 * HM ≤ 11 * ΛK ^ 2 := by
      linarith only [hL2K, hh2H, hΛ2_ge, hΛ1_ge, hΛK1]
    have t1' := mul_le_mul_of_nonneg_left t1 (by positivity : 0 ≤ 8 * Real.exp 2 * c)
    have t2 : 48 * Real.exp 1 * c * h * HM ≤ 96 * Real.exp 1 * c * ΛK ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_left hhH (by positivity : 0 ≤ 48 * Real.exp 1 * c)
      have a2 := mul_le_mul_of_nonneg_left hΛ1_ge (by positivity : 0 ≤ 96 * Real.exp 1 * c)
      linarith only [a1, a2, (by ring : 48 * Real.exp 1 * c * h * HM =
        48 * Real.exp 1 * c * (h * HM))]
    have t3 : 2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK) ≤
        (2 * Real.exp 2 + 2) * c * ΛK ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_left hwhΨ (by linarith only [hΛK1] : 0 ≤ 2 * ΛK)
      have a2 : ΛK ^ 2 ≤ c * ΛK ^ 2 := le_mul_of_one_le_left (by positivity) hc1
      linarith only [a1, a2, hΛ2_ge,
        (by ring : 2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK) =
          2 * Real.exp 2 * c * ΛK ^ 2 + 2 * ΛK * ((w / h) * ΨK)),
        (by ring : (2 * Real.exp 2 + 2) * c * ΛK ^ 2 =
          2 * Real.exp 2 * c * ΛK ^ 2 + 2 * (c * ΛK ^ 2))]
    have hcΛ : 0 ≤ (10 * Real.exp 2 + 4 * Real.exp 1 + 8) * (c * ΛK ^ 2) := by positivity
    linarith only [t1', t2, t3, hcΛ]
  have hΛK_ub : ΛK ≤ C_B * lam ^ 2 := by
    have hl2 : 1 ≤ lam ^ 2 := one_le_pow₀ hlam1
    have h1 : 1 + (Real.log 4 + 4) ≤ (1 + (Real.log 4 + 4)) * lam ^ 2 :=
      le_mul_of_one_le_right (by linarith only [hlog4]) hl2
    dsimp only [ΛK, C_B]
    linarith only [hβ_le, h1]
  have hΛK_sq : ΛK ^ 2 ≤ C_B ^ 2 * lam ^ 4 := by
    have hp2 := pow_le_pow_left₀ (by linarith only [hΛK1]) hΛK_ub 2
    exact hp2.trans_eq (by ring)
  have hclam4 : c * lam ^ 4 ≤ R₀ * L ^ (31 / 32 : ℝ) := by
    have hlam4 : lam ^ 4 = L ^ (3 / 4 : ℝ) := by
      rw [hlam_eq, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    rw [hlam4]
    calc c * L ^ (3 / 4 : ℝ)
        ≤ (R₀ * L ^ (1 / 8 : ℝ)) * L ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right hc_R₀ (by positivity)
      _ = R₀ * L ^ (7 / 8 : ℝ) := by rw [mul_assoc, ← Real.rpow_add hL0]; norm_num
      _ ≤ R₀ * L ^ (31 / 32 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)) hR₀0.le
  have hWS' : (w / h ^ 2) * WS ≤
      (R₀ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 * L ^ (31 / 32 : ℝ)) * P := by
    refine hWS.trans (mul_le_mul_of_nonneg_right ?_ hP0)
    calc 8 * Real.exp 2 * c * (1 + Real.log (2 * K'_r) + 4 * h ^ 2 * HM) +
          48 * Real.exp 1 * c * h * HM +
          2 * ΛK * (Real.exp 2 * c * ΛK + (w / h) * ΨK)
        ≤ c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2 := hPc
      _ ≤ c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * (C_B ^ 2 * lam ^ 4) :=
          mul_le_mul_of_nonneg_left hΛK_sq (by positivity)
      _ = (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 * (c * lam ^ 4) := by ring
      _ ≤ (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 * (R₀ * L ^ (31 / 32 : ℝ)) :=
          mul_le_mul_of_nonneg_left hclam4 (by positivity)
      _ = R₀ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 * L ^ (31 / 32 : ℝ) := by ring
  have hmul := mul_le_mul_of_nonneg_left hFh_mass (div_nonneg hNR.le (sq_nonneg c))
  have hid : (N_r / c ^ 2) * ((w * I₂) * (splineWindowConstant * (w / h ^ 2)) * WS) =
      (I₂ / c) * splineWindowConstant * ((w / h ^ 2) * WS) := by
    dsimp only [w]; field_simp [hc0.ne', hNR.ne']
  rw [hid] at hmul
  calc (N_r / c ^ 2) * Fh_int
      ≤ (I₂ / c) * splineWindowConstant *
          ((R₀ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 * L ^ (31 / 32 : ℝ)) * P) :=
        hmul.trans (mul_le_mul_of_nonneg_left hWS' (by positivity))
    _ = (splineWindowConstant * R₀ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2) *
          L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) := by ring

private theorem prime_amgm_pairing_sq_le
    {N_r c L I₂ P Qy C_high C_ws R₀ C_tr lam T h fy_int Fh_int F_int LM_fy HM_fy cross_int : ℝ}
    (hc0 : 0 < c) (hNR : 0 < N_r) (hL0 : 0 < L) (hI₂ : 0 < I₂) (hP0 : 0 ≤ P) (hQy0 : 0 ≤ Qy)
    (hChigh : 0 < C_high) (hCws0 : 0 ≤ C_ws) (hR₀0 : 0 < R₀) (hCtr0 : 0 ≤ C_tr) (hlam0 : 0 < lam)
    (hL2_fy_le : (N_r / c ^ 2) * fy_int ≤ Qy)
    (hLM_fy_le : (N_r / c ^ 2) * LM_fy ≤ Qy)
    (hHM_fy : (lam / 2) * ((N_r / c ^ 2) * HM_fy) ≤ C_high * Qy)
    (hFh_bound : (N_r / c ^ 2) * Fh_int ≤ C_ws * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P))
    (hF_low : (T * h) ^ 2 * ((N_r / c ^ 2) * F_int) ≤
      4 * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P))
    (hF_high : (8 * C_high / lam) * ((N_r / c ^ 2) * F_int) ≤
      16 * C_high * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P))
    (hpair_all : ∀ γ lam_p : ℝ, 0 < γ → 0 < lam_p →
      2 * |cross_int| ≤
        γ * fy_int + γ⁻¹ * Fh_int +
          γ * LM_fy + γ⁻¹ * ((T * h) ^ 2 * F_int) +
          lam_p * HM_fy + lam_p⁻¹ * (4 * F_int)) :
    ((N_r / c ^ 2) * cross_int) ^ 2 ≤
      3 * (C_ws + 4 * R₀ * C_tr + 16 * C_high * R₀ * C_tr + 1) *
        L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy := by
  set C_pr : ℝ := C_ws + 4 * R₀ * C_tr + 16 * C_high * R₀ * C_tr + 1
  have hCpr : 0 < C_pr := by dsimp only [C_pr]; positivity
  set X_pr : ℝ := 3 * Qy
  set Y_pr : ℝ := C_pr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)
  have hApr : 0 ≤ 2 * |(N_r / c ^ 2) * cross_int| := by positivity
  have hsq4 := sq_le_four_mul_of_forall_pos hApr (by positivity : 0 ≤ X_pr)
    (by positivity : 0 ≤ Y_pr) fun γ hγ => ?_
  · have h4_eq : (2 * |(N_r / c ^ 2) * cross_int|) ^ 2 = 4 * ((N_r / c ^ 2) * cross_int) ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    rw [h4_eq] at hsq4
    dsimp only [X_pr, Y_pr] at hsq4
    linarith only [hsq4, (by ring : 4 * (3 * Qy) * (C_pr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)) =
      4 * (3 * C_pr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy))]
  · set lam_p : ℝ := γ * (lam / 2) / C_high
    have hlamp : 0 < lam_p := by dsimp only [lam_p]; positivity
    have hpair := hpair_all γ lam_p hγ hlamp
    have hmul := mul_le_mul_of_nonneg_left hpair (div_nonneg hNR.le (sq_nonneg c))
    have hlhs : (N_r / c ^ 2) * (2 * |cross_int|) = 2 * |(N_r / c ^ 2) * cross_int| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hNR.le (sq_nonneg c))]; ring
    rw [hlhs] at hmul
    have ht1 : (N_r / c ^ 2) * (γ * fy_int) ≤ γ * Qy := by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hL2_fy_le hγ.le
    have ht2 : (N_r / c ^ 2) * (γ * LM_fy) ≤ γ * Qy := by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hLM_fy_le hγ.le
    have ht3 : (N_r / c ^ 2) * (lam_p * HM_fy) ≤ γ * Qy := by
      have hid : (N_r / c ^ 2) * (lam_p * HM_fy) =
          (γ / C_high) * ((lam / 2) * ((N_r / c ^ 2) * HM_fy)) := by
        dsimp only [lam_p]; ring
      rw [hid]
      calc (γ / C_high) * ((lam / 2) * ((N_r / c ^ 2) * HM_fy))
          ≤ (γ / C_high) * (C_high * Qy) := mul_le_mul_of_nonneg_left hHM_fy (by positivity)
        _ = γ * Qy := by field_simp [hChigh.ne']
    have ht4 : (N_r / c ^ 2) * (γ⁻¹ * Fh_int) ≤
        γ⁻¹ * (C_ws * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)) := by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hFh_bound (inv_nonneg.mpr hγ.le)
    have ht5 : (N_r / c ^ 2) * (γ⁻¹ * ((T * h) ^ 2 * F_int)) ≤
        γ⁻¹ * (4 * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)) := by
      have hid : (N_r / c ^ 2) * (γ⁻¹ * ((T * h) ^ 2 * F_int)) =
          γ⁻¹ * ((T * h) ^ 2 * ((N_r / c ^ 2) * F_int)) := by ring
      rw [hid]; exact mul_le_mul_of_nonneg_left hF_low (inv_nonneg.mpr hγ.le)
    have ht6 : (N_r / c ^ 2) * (lam_p⁻¹ * (4 * F_int)) ≤
        γ⁻¹ * (16 * C_high * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)) := by
      have hid : (N_r / c ^ 2) * (lam_p⁻¹ * (4 * F_int)) =
          γ⁻¹ * ((8 * C_high / lam) * ((N_r / c ^ 2) * F_int)) := by
        dsimp only [lam_p]; field_simp [hγ.ne', hlam0.ne', hChigh.ne']; ring
      rw [hid]; exact mul_le_mul_of_nonneg_left hF_high (inv_nonneg.mpr hγ.le)
    have hextra : 0 ≤ γ⁻¹ * (1 * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)) := by positivity
    dsimp only [X_pr, Y_pr, C_pr]
    linarith only [hmul, ht1, ht2, ht3, ht4, ht5, ht6, hextra,
      (by ring : (N_r / c ^ 2) *
        (γ * fy_int + γ⁻¹ * Fh_int + γ * LM_fy + γ⁻¹ * ((T * h) ^ 2 * F_int) +
          lam_p * HM_fy + lam_p⁻¹ * (4 * F_int)) =
        (N_r / c ^ 2) * (γ * fy_int) + (N_r / c ^ 2) * (γ⁻¹ * Fh_int) +
          (N_r / c ^ 2) * (γ * LM_fy) + (N_r / c ^ 2) * (γ⁻¹ * ((T * h) ^ 2 * F_int)) +
          (N_r / c ^ 2) * (lam_p * HM_fy) + (N_r / c ^ 2) * (lam_p⁻¹ * (4 * F_int))),
      (by ring : γ⁻¹ * ((C_ws + 4 * R₀ * C_tr + 16 * C_high * R₀ * C_tr + 1) *
          L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)) =
        γ⁻¹ * (C_ws * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)) +
          γ⁻¹ * (4 * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)) +
          γ⁻¹ * (16 * C_high * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)) +
          γ⁻¹ * (1 * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P)))]

private def collarDecouplingShift (B_g a_R : ℝ) : ℝ :=
  2 * B_g +
    (2 * vonMangoldtThreeHalvesMass +
      (2 * vonMangoldtThreeHalvesMass) ^ 2 * Real.exp 8 / (a_R / 2)) +
    (6 + 2 / (a_R / 2)) + 1

private theorem collarDecouplingShift_nonneg {B_g a_R : ℝ} (hBg0 : 0 ≤ B_g) (haR : 0 < a_R) :
    0 ≤ collarDecouplingShift B_g a_R := by
  unfold collarDecouplingShift
  have hCv0 : 0 ≤ 2 * vonMangoldtThreeHalvesMass :=
    mul_nonneg zero_le_two vonMangoldtThreeHalvesMass_nonneg
  positivity

private theorem collar_shifted_energy_and_scale_bounds
    {c B_g a_R κ_R : ℝ} {N M : ℕ}
    (hc0 : 0 < c) (hcN : c ≤ N) (hBg0 : 0 ≤ B_g) (haR : 0 < a_R) (hκR : 0 < κ_R) (hN1 : 1 ≤ N)
    {x_p x_y : ℕ → ℝ} (hy_supp : ∀ n, n ≤ M → x_y n = 0)
    (hgard_x :
      let y_t := atomicTailCoefficients M x_y
      let U_t := normalizedCentredAtomicTest tiltedUnitSpline y_t c N
      κ_R * topCollarSeventhMass M N x_y + a_R * (∫ u, U_t u ^ 2 * Real.exp (-(8 * u))) ≤
        weilQuad U_t + B_g * ∫ u, U_t u ^ 2) :
    let g := atomDilate tiltedUnitSpline (c / N)
    let f_p := atomicTest N x_p g
    let f_y := atomicTest N x_y g
    let U_p := normalizedCentredAtomicTest tiltedUnitSpline x_p c N
    let U_y := normalizedCentredAtomicTest tiltedUnitSpline x_y c N
    let Qy := weilQuad U_y + collarDecouplingShift B_g a_R * ∫ u, U_y u ^ 2
    (∫ u, U_y u ^ 2) ≤ Qy ∧
      0 ≤ Qy ∧
      κ_R * topCollarSeventhMass M N x_y ≤ Qy ∧
      archForm U_y ≤ 2 * Qy ∧
      ((N : ℝ) / c ^ 2) * (∫ u, f_y u ^ 2) = (∫ u, U_y u ^ 2) ∧
      ((N : ℝ) / c ^ 2) * archForm f_y = archForm U_y ∧
      weilBilin U_y U_p = ((N : ℝ) / c ^ 2) * weilBilin f_p f_y := by
  intro g f_p f_y U_p U_y Qy
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have haR2 : 0 < a_R / 2 := half_pos haR
  let C_v : ℝ := 2 * vonMangoldtThreeHalvesMass
  have hCv0 : 0 ≤ C_v := mul_nonneg zero_le_two vonMangoldtThreeHalvesMass_nonneg
  let B_prime : ℝ := C_v + C_v ^ 2 * Real.exp 8 / (a_R / 2)
  have hBpr0 : 0 ≤ B_prime := by dsimp only [B_prime]; positivity
  let B_pole : ℝ := 6 + 2 / (a_R / 2)
  have hBpo0 : 0 ≤ B_pole := by dsimp only [B_pole]; positivity
  set w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgs := tiltedUnitSpline_atom_support hw
  have hfp : ContDiff ℝ 2 f_p := contDiff_atomicTest hg N x_p
  have hfpc : HasCompactSupport f_p := hasCompactSupport_atomicTest hgs N x_p
  have hfy : ContDiff ℝ 2 f_y := contDiff_atomicTest hg N x_y
  have hfyc : HasCompactSupport f_y := hasCompactSupport_atomicTest hgs N x_y
  have hUp : ContDiff ℝ 2 U_p :=
    contDiff_normalizedCentredAtomicTest contDiff_tiltedUnitSpline hc0 hN1 x_p
  have hUpc : HasCompactSupport U_p :=
    hasCompactSupport_normalizedCentredAtomicTest tiltedUnitSpline_eq_zero hc0 hN1 x_p
  have hUy : ContDiff ℝ 2 U_y :=
    contDiff_normalizedCentredAtomicTest contDiff_tiltedUnitSpline hc0 hN1 x_y
  have hUyc : HasCompactSupport U_y :=
    hasCompactSupport_normalizedCentredAtomicTest tiltedUnitSpline_eq_zero hc0 hN1 x_y
  have hy_tail : atomicTailCoefficients M x_y = x_y := by
    funext n; unfold atomicTailCoefficients
    by_cases h : M < n
    · exact if_pos h
    · rw [if_neg h, hy_supp n (Nat.not_lt.mp h)]
  have hgard_y := hgard_x
  dsimp only at hgard_y
  rw [hy_tail] at hgard_y
  change κ_R * topCollarSeventhMass M N x_y +
      a_R * (∫ u, U_y u ^ 2 * Real.exp (-(8 * u))) ≤
    weilQuad U_y + B_g * ∫ u, U_y u ^ 2 at hgard_y
  have hUy_le1 : ∀ u, 1 < u → U_y u = 0 := by
    intro u hu1
    dsimp only [U_y, normalizedCentredAtomicTest, centredAtomicTest]
    suffices h0 : atomicTest N x_y g (u + Real.log N) = 0 by rw [h0, mul_zero]
    unfold atomicTest
    refine sum_eq_zero fun n hn => ?_
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn1 hnN
    have hnot : u + Real.log N - Real.log n ∉ Set.Icc 0 w := fun hm => by linarith [hm.2, hw1]
    exact mul_eq_zero_of_right _ (hgs _ hnot)
  set I_Uy : ℝ := ∫ u, U_y u ^ 2
  set W8_Uy : ℝ := ∫ u, U_y u ^ 2 * Real.exp (-(8 * u))
  set S7_y : ℝ := topCollarSeventhMass M N x_y
  have hIUy0 : 0 ≤ I_Uy := integral_nonneg fun _ => sq_nonneg _
  have hW80 : 0 ≤ W8_Uy := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hS70 : 0 ≤ S7_y := topCollarSeventhMass_nonneg M N x_y
  have hBR_eq : collarDecouplingShift B_g a_R = 2 * B_g + B_prime + B_pole + 1 := rfl
  have hQy_ge_g : weilQuad U_y + B_g * I_Uy + I_Uy ≤ Qy := by
    dsimp only [Qy]
    rw [hBR_eq]
    have hextra : 0 ≤ (B_g + B_prime + B_pole) * I_Uy := by positivity
    linarith only [hextra]
  have hIUy_le_Qy : I_Uy ≤ Qy := by
    have h0 : 0 ≤ κ_R * S7_y + a_R * W8_Uy := by positivity
    linarith only [h0, hgard_y, hQy_ge_g]
  have hQy0 : 0 ≤ Qy := hIUy0.trans hIUy_le_Qy
  have hS7_le_Qy : κ_R * S7_y ≤ Qy := by
    have h0 : 0 ≤ a_R * W8_Uy := by positivity
    linarith only [h0, hgard_y, hQy_ge_g, hIUy0]
  have harchUy_le : archForm U_y ≤ 2 * Qy := by
    have hpr := (le_abs_self _).trans
      (abs_primeSum_le_exponential_mass_of_le_one_explicit haR2 hUy.continuous hUyc hUy_le1)
    have hpo := two_mul_sinhHalfMoment_sq_le_exponential_mass_explicit haR2 hUy.continuous hUyc hUy_le1
    have hwq : weilQuad U_y = archForm U_y - primeSum U_y +
        (2 * coshHalfMoment U_y ^ 2 - 2 * sinhHalfMoment U_y ^ 2) := by
      have h1 := weilQuad_eq hUy hUyc
      have h2 := archForm_eq_levyEnergy hUy hUyc
      linarith only [h1, h2]
    have hcosh0 : 0 ≤ 2 * coshHalfMoment U_y ^ 2 := by positivity
    have hkS0 : 0 ≤ κ_R * S7_y := by positivity
    change primeSum U_y ≤ (a_R / 2) * W8_Uy + B_prime * I_Uy at hpr
    change 2 * sinhHalfMoment U_y ^ 2 ≤ (a_R / 2) * W8_Uy + B_pole * I_Uy at hpo
    have hcomb : archForm U_y ≤ 2 * weilQuad U_y + (B_g + B_prime + B_pole) * I_Uy := by
      linarith only [hwq, hpr, hpo, hcosh0, hgard_y, hkS0]
    have hrem : 0 ≤ (3 * B_g + B_prime + B_pole + 2) * I_Uy := by positivity
    dsimp only [Qy]
    rw [hBR_eq]
    linarith only [hcomb, hrem]
  have hL2_fy_scale : ((N : ℝ) / c ^ 2) * (∫ u, f_y u ^ 2) = I_Uy := by
    dsimp only [I_Uy, U_y, normalizedCentredAtomicTest, centredAtomicTest, f_y, g]
    simp_rw [mul_pow, div_pow, Real.sq_sqrt hNR.le]
    rw [integral_const_mul, integral_add_right_eq_self (fun u => atomicTest N x_y
      (atomDilate tiltedUnitSpline (c / N)) u ^ 2) (Real.log N)]
  have harch_fy_scale : ((N : ℝ) / c ^ 2) * archForm f_y = archForm U_y := by
    have hcent_cd : ContDiff ℝ 2 (centredAtomicTest tiltedUnitSpline x_y c N) :=
      hfy.comp (contDiff_id.add contDiff_const)
    have hcent_cs : HasCompactSupport (centredAtomicTest tiltedUnitSpline x_y c N) :=
      hfyc.comp_homeomorph (Homeomorph.addRight (Real.log N))
    have harch_cent : archForm (centredAtomicTest tiltedUnitSpline x_y c N) = archForm f_y := by
      have hint_eq : (∫ u, centredAtomicTest tiltedUnitSpline x_y c N u ^ 2) = ∫ u, f_y u ^ 2 := by
        change (∫ u, f_y (u + Real.log N) ^ 2) = ∫ u, f_y u ^ 2
        exact integral_add_right_eq_self (fun u => f_y u ^ 2) (Real.log N)
      rw [archForm_eq_levyEnergy hcent_cd hcent_cs, archForm_eq_levyEnergy hfy hfyc, hint_eq]
      congr 1
      unfold levyEnergy centredAtomicTest
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      congr 1
      have hfn : (fun u => (f_y (u + Real.log N) - f_y (u + t + Real.log N)) ^ 2) =
          fun u => (fun v => (f_y v - f_y (v + t)) ^ 2) (u + Real.log N) :=
        funext fun u => by rw [show u + t + Real.log (N : ℝ) = u + Real.log (N : ℝ) + t by ring]
      rw [hfn]
      exact integral_add_right_eq_self (fun v => (f_y v - f_y (v + t)) ^ 2) (Real.log N)
    have hfn_Uy : U_y = fun u => (Real.sqrt N / c) * centredAtomicTest tiltedUnitSpline x_y c N u := rfl
    rw [hfn_Uy, archForm_const_mul hcent_cd hcent_cs, div_pow, Real.sq_sqrt hNR.le, harch_cent]
  have hbil_scale : weilBilin U_y U_p = ((N : ℝ) / c ^ 2) * weilBilin f_p f_y := by
    rw [weilBilin_comm hUy hUyc hUp hUpc]
    unfold weilBilin
    have hadd_fn : (fun u => U_p u + U_y u) =
        fun u => (Real.sqrt N / c) * ((fun v => f_p v + f_y v) (u + Real.log N)) :=
      funext fun u => by dsimp only [U_p, U_y, normalizedCentredAtomicTest, centredAtomicTest, f_p, f_y, g]; ring
    have hsub_fn : (fun u => U_p u - U_y u) =
        fun u => (Real.sqrt N / c) * ((fun v => f_p v - f_y v) (u + Real.log N)) :=
      funext fun u => by dsimp only [U_p, U_y, normalizedCentredAtomicTest, centredAtomicTest, f_p, f_y, g]; ring
    have hsh_add : ContDiff ℝ 2 (fun u => (fun v => f_p v + f_y v) (u + Real.log N)) :=
      (hfp.add hfy).comp (contDiff_id.add contDiff_const)
    have hshc_add : HasCompactSupport (fun u => (fun v => f_p v + f_y v) (u + Real.log N)) :=
      (hfpc.add hfyc).comp_homeomorph (Homeomorph.addRight (Real.log N))
    have hsh_sub : ContDiff ℝ 2 (fun u => (fun v => f_p v - f_y v) (u + Real.log N)) :=
      (hfp.sub hfy).comp (contDiff_id.add contDiff_const)
    have hshc_sub : HasCompactSupport (fun u => (fun v => f_p v - f_y v) (u + Real.log N)) :=
      (hfpc.sub hfyc).comp_homeomorph (Homeomorph.addRight (Real.log N))
    rw [hadd_fn, hsub_fn,
      weilQuad_const_mul hsh_add hshc_add, weilQuad_const_mul hsh_sub hshc_sub,
      weilQuad_comp_add_right (f := fun v => f_p v + f_y v) (hfp.add hfy) (hfpc.add hfyc),
      weilQuad_comp_add_right (f := fun v => f_p v - f_y v) (hfp.sub hfy) (hfpc.sub hfyc),
      div_pow, Real.sq_sqrt hNR.le]
    ring
  exact ⟨hIUy_le_Qy, hQy0, hS7_le_Qy, harchUy_le, hL2_fy_scale, harch_fy_scale, hbil_scale⟩

private theorem primeBilin_prefix_collar_sq_le
    {C_ψ c₀ R₀ C_β Qy c h T lam β : ℝ} {N K' : ℕ}
    (hCψ : 0 ≤ C_ψ) (hR₀0 : 0 < R₀) (hCβ0 : 0 ≤ C_β) (hQy0 : 0 ≤ Qy)
    (hc1 : 1 ≤ c) (hcN : c ≤ N) (h2LN : 2 * linearDefectCutoff c ≤ N) (hN1 : 1 ≤ N)
    (hL1 : 1 ≤ Real.log (N : ℝ))
    (hc_R₀ : c ≤ R₀ * Real.log (N : ℝ) ^ (1 / 8 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ))
    (hlam_eq : lam = Real.log (N : ℝ) ^ (3 / 16 : ℝ)) (hlam1 : 1 ≤ lam)
    (hh_eq : h = Real.exp (-lam) / Real.log (N : ℝ)) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hT0 : 0 < T)
    (hlogT_eq : Real.log T = lam)
    (hTh_eq : T * h = 1 / Real.log (N : ℝ))
    (hhL_le2 : h * (1 + Real.log (N : ℝ)) ≤ 2)
    (hlam_half : lam / 2 ≤ lam - factorialSpanGammaOffset)
    (hK'1 : 1 ≤ K') (hpnt' : 4 * C_ψ * pntRate c₀ K' ≤ h ^ 2)
    (hlogK' : Real.log (K' : ℝ) ≤ β + 1) (hK'le : (K' : ℝ) ≤ 2 * Real.exp β)
    (hβ_le : β ≤ C_β * lam ^ 2) (hβ0 : 0 ≤ β)
    (hlogL_132 : 1 * Real.log (N : ℝ) ^ (0 : ℝ) * (1 + Real.log (Real.log (N : ℝ))) ^ 1 ≤
      Real.log (N : ℝ) ^ (1 / 32 : ℝ))
    (hQ5 : (|Real.log (2 * (Real.log 4 + 4))| + 4 + C_β) * Real.log (N : ℝ) ^ (3 / 8 : ℝ) *
      (1 + Real.log (Real.log (N : ℝ))) ^ 1 ≤ Real.log (N : ℝ) ^ (1 : ℝ))
    {x_p x_y : ℕ → ℝ}
    (hp_supp : ∀ n, N / linearDefectCutoff c < n → x_p n = 0)
    (hy_supp : ∀ n, n ≤ N / linearDefectCutoff c → x_y n = 0)
    (hsigma0 : prefixPoleMoment (N / linearDefectCutoff c) x_p = 0)
    (hFh_mass :
      let w := c / (N : ℝ)
      let M := N / linearDefectCutoff c
      let Bn := ⌊(N : ℝ) * Real.exp w⌋₊
      let K := primeOrderCutoff N w
      let V_pr : ℕ → ℝ := fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv K M x_p n
      (∫ u, atomicTest Bn V_pr (smoothedBump (atomDilate tiltedUnitSpline w) h) u ^ 2) ≤
        (w * ∫ u, tiltedUnitSpline u ^ 2) * (splineWindowConstant * (w / h ^ 2)) *
          windowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x_p h)
    (hF_mass :
      let w := c / (N : ℝ)
      let M := N / linearDefectCutoff c
      let Bn := ⌊(N : ℝ) * Real.exp w⌋₊
      let K := primeOrderCutoff N w
      let V_pr : ℕ → ℝ := fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv K M x_p n
      (∫ u, atomicTest Bn V_pr (atomDilate tiltedUnitSpline w) u ^ 2) ≤
        (w * ∫ u, tiltedUnitSpline u ^ 2) *
          ((1 + 2 * Real.exp 1 * (w * Bn)) *
            (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) *
          ∑ n ∈ Icc 1 M, x_p n ^ 2)
    (hL2_fy_le : ((N : ℝ) / c ^ 2) *
      (∫ u, atomicTest N x_y (atomDilate tiltedUnitSpline (c / N)) u ^ 2) ≤ Qy)
    (hL2_fy_scale : ((N : ℝ) / c ^ 2) *
      (∫ u, atomicTest N x_y (atomDilate tiltedUnitSpline (c / N)) u ^ 2) =
      ∫ u, normalizedCentredAtomicTest tiltedUnitSpline x_y c N u ^ 2)
    (harch_fy_scale : ((N : ℝ) / c ^ 2) *
      archForm (atomicTest N x_y (atomDilate tiltedUnitSpline (c / N))) =
      archForm (normalizedCentredAtomicTest tiltedUnitSpline x_y c N))
    (hIUy_le_Qy : (∫ u, normalizedCentredAtomicTest tiltedUnitSpline x_y c N u ^ 2) ≤ Qy)
    (harchUy_le : archForm (normalizedCentredAtomicTest tiltedUnitSpline x_y c N) ≤ 2 * Qy) :
    let L := Real.log (N : ℝ)
    let I₂ := ∫ u, tiltedUnitSpline u ^ 2
    let P := ∑ n ∈ Icc 1 (N / linearDefectCutoff c), x_p n ^ 2
    let C_high : ℝ := 2 + factorialSpanGammaOffset + Real.log 2
    let C_B : ℝ := C_β + 1 + (Real.log 4 + 4)
    let C_tr : ℝ := (1 + 2 * Real.exp 2) *
      (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))
    let C_ws : ℝ := splineWindowConstant * R₀ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2
    let C_pr : ℝ := C_ws + 4 * R₀ * C_tr + 16 * C_high * R₀ * C_tr + 1
    let g := atomDilate tiltedUnitSpline (c / N)
    let f_p := atomicTest N x_p g
    let f_y := atomicTest N x_y g
    (((N : ℝ) / c ^ 2) * ((primeSum (fun u => f_p u + f_y u) - primeSum (fun u => f_p u - f_y u)) / 4)) ^ 2 ≤
      3 * C_pr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy := by
  intro L I₂ P C_high C_B C_tr C_ws C_pr g f_p f_y
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hG₀ : 0 ≤ factorialSpanGammaOffset := factorialSpanGammaOffset_nonneg
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 1 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hswc0 : 0 ≤ splineWindowConstant := by unfold splineWindowConstant; positivity
  have hChigh : 0 < C_high := by dsimp only [C_high]; positivity
  have hCtr0 : 0 ≤ C_tr := by
    have h1 : 1 ≤ 8 * Real.exp 1 * (256 * Real.exp 2 + 4) := by
      have := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
      have := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
    have := Real.log_nonneg h1
    dsimp only [C_tr]; positivity
  have hCws0 : 0 ≤ C_ws := by dsimp only [C_ws]; positivity
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam1
  obtain ⟨hLc3, _, -, _⟩ := linearDefectCutoff_bounds hc1
  set M := N / linearDefectCutoff c
  have hMN : M ≤ N := Nat.div_le_self _ _
  have hM1 : 1 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
  set w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgs := tiltedUnitSpline_atom_support hw
  have hfy : ContDiff ℝ 2 f_y := contDiff_atomicTest hg N x_y
  have hfyc : HasCompactSupport f_y := hasCompactSupport_atomicTest hgs N x_y
  set Bn := ⌊(N : ℝ) * Real.exp w⌋₊
  set K := primeOrderCutoff N w
  set V_pr : ℕ → ℝ := fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv K M x_p n
  set F := atomicTest Bn V_pr g
  set Fh := atomicTest Bn V_pr (smoothedBump g h)
  have hpr_eq : (primeSum (fun u => f_p u + f_y u) - primeSum (fun u => f_p u - f_y u)) / 4 =
      ∫ u, f_y u * F u :=
    primeBilin_prefix_collar_eq hc1 h2LN hp_supp hy_supp
  dsimp only at hFh_mass hF_mass
  change (∫ u, Fh u ^ 2) ≤ (w * I₂) * (splineWindowConstant * (w / h ^ 2)) *
    windowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x_p h at hFh_mass
  change (∫ u, F u ^ 2) ≤ (w * I₂) *
    ((1 + 2 * Real.exp 1 * (w * Bn)) *
      (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) * P at hF_mass
  have hFh_bound : ((N : ℝ) / c ^ 2) * (∫ u, Fh u ^ 2) ≤
      C_ws * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) := by
    have hexp_N : 2 * (Real.log 4 + 4) * c * L * Real.exp (lam + β) ≤ N :=
      far_exp_le (Real.exp_log hNR) hc1 hcL hL1 (by norm_num : (0 : ℝ) < 3 / 16) hlam_eq
        hCβ0 hβ_le (by simpa only [show (2 : ℝ) * (3 / 16) = 3 / 8 by norm_num] using hQ5)
    have hwB : w * Bn ≤ Real.exp 1 * c := by
      have hBn_le : (Bn : ℝ) ≤ N * Real.exp w := Nat.floor_le (by positivity)
      have hwN : w * N = c := by dsimp only [w]; field_simp [hNR.ne']
      calc w * Bn ≤ w * (N * Real.exp w) := mul_le_mul_of_nonneg_left hBn_le hw.le
        _ = c * Real.exp w := by rw [← mul_assoc, hwN]
        _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hc0.le
        _ = Real.exp 1 * c := mul_comm _ _
    have hAB : ((M : ℝ) / 2) ≤ Bn := by
      have h1 : (N : ℝ) ≤ Bn := by
        exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hNR.le (Real.one_le_exp hw.le))
      have h2 : (M : ℝ) ≤ N := by exact_mod_cast hMN
      linarith only [h1, h2]
    have hLK' : shortOrderWeight K' ≤ β + 1 + (Real.log 4 + 4) := by
      have := shortOrderWeight_le hK'1; linarith only [this, hlogK']
    have hΨK' : ∑ k ∈ range K', (ArithmeticFunction.vonMangoldt k : ℝ) ≤
        (Real.log 4 + 4) * (2 * Real.exp β) :=
      (sum_vonMangoldt_range_le K').trans
        (mul_le_mul_of_nonneg_left hK'le (zero_le_one.trans hlog4))
    have hWS := windowSumBound_div_le (M := M) x_p hh0 hh1 hCψ hpnt' hw.le hc0.le hwB
      (by positivity) hAB hLK' hΨK'
    rw [hsigma0, show 8 * Real.exp 2 * c * (0 : ℝ) ^ 2 = 0 by ring, zero_add] at hWS
    have hHM_le : prefixHarmonic M ≤ 1 + L := by
      have h1 := RHTower.sum_Icc_one_div_le hM1
      have h2 : Real.log (M : ℝ) ≤ L :=
        Real.log_le_log (by exact_mod_cast hM1) (by exact_mod_cast hMN)
      unfold prefixHarmonic; linarith only [h1, h2]
    have hHM0 : 0 ≤ prefixHarmonic M := sum_nonneg fun _ _ => by positivity
    exact windowSum_fh_algebraic_le hc1 hNR hL1 hh0 hh1 hlam1 hβ0 (by exact_mod_cast hK'1)
      hHM0 hR₀0 hI₂ hP0 hc_R₀ hlam_eq hh_eq hexp_N hHM_le hhL_le2 hlogK' hβ_le hFh_mass hWS
  have hF_scale : ((N : ℝ) / c ^ 2) * (∫ u, F u ^ 2) ≤
      ((I₂ / c) * P) * (C_tr * c * (1 + L) * (1 + Real.log c)) := by
    have htr := translate_factor_le hc1 h2LN
    change (1 + 2 * Real.exp 1 * (w * Bn)) *
        (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4))) ≤
      C_tr * c * (1 + L) * (1 + Real.log c) at htr
    have hF' : (∫ u, F u ^ 2) ≤ (w * I₂) * (C_tr * c * (1 + L) * (1 + Real.log c)) * P :=
      hF_mass.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htr (by positivity)) hP0)
    have hmul := mul_le_mul_of_nonneg_left hF' (div_nonneg hNR.le (sq_nonneg c))
    refine hmul.trans_eq ?_
    dsimp only [w]; field_simp [hc0.ne', hNR.ne']
  have hHM_fy : (lam / 2) * (((N : ℝ) / c ^ 2) * highFourierMass f_y T) ≤ C_high * Qy := by
    have hband := archForm_ge_high_band hfy hfyc (T := T) (R := T) hT0 le_rfl
    rw [sub_self, zero_mul, add_zero, hlogT_eq] at hband
    have hlow_le : lowFourierMass f_y T ≤ ∫ u, f_y u ^ 2 :=
      lowFourierMass_le_integral_sq hfy hfyc T
    have hHM_nn : 0 ≤ highFourierMass f_y T := highFourierMass_nonneg f_y T
    have h1 : (lam / 2) * highFourierMass f_y T ≤
        archForm f_y + (factorialSpanGammaOffset + Real.log 2) * ∫ u, f_y u ^ 2 := by
      have hm1 := mul_le_mul_of_nonneg_right hlam_half hHM_nn
      have hm2 := mul_le_mul_of_nonneg_left hlow_le
        (by positivity : 0 ≤ factorialSpanGammaOffset + Real.log 2)
      linarith only [hband, hm1, hm2]
    have hmul := mul_le_mul_of_nonneg_left h1 (div_nonneg hNR.le (sq_nonneg c))
    have hid : ((N : ℝ) / c ^ 2) *
        (archForm f_y + (factorialSpanGammaOffset + Real.log 2) * ∫ u, f_y u ^ 2) =
        ((N : ℝ) / c ^ 2) * archForm f_y +
          (factorialSpanGammaOffset + Real.log 2) * (((N : ℝ) / c ^ 2) * ∫ u, f_y u ^ 2) := by ring
    rw [← mul_left_comm (lam / 2), hid, harch_fy_scale, hL2_fy_scale] at hmul
    have h2 := mul_le_mul_of_nonneg_left hIUy_le_Qy
      (by positivity : 0 ≤ factorialSpanGammaOffset + Real.log 2)
    dsimp only [C_high]
    linarith only [hmul, harchUy_le, h2]
  have hLM_fy_le : ((N : ℝ) / c ^ 2) * lowFourierMass f_y T ≤ Qy := by
    have hlm := mul_le_mul_of_nonneg_left (lowFourierMass_le_integral_sq hfy hfyc T)
      (div_nonneg hNR.le (sq_nonneg c))
    rw [hL2_fy_scale] at hlm
    exact hlm.trans hIUy_le_Qy
  have hpair_all : ∀ γ lam_p : ℝ, 0 < γ → 0 < lam_p →
      2 * |∫ u, f_y u * F u| ≤
        γ * (∫ u, f_y u ^ 2) + γ⁻¹ * (∫ u, Fh u ^ 2) +
          γ * lowFourierMass f_y T + γ⁻¹ * ((T * h) ^ 2 * ∫ u, F u ^ 2) +
          lam_p * highFourierMass f_y T + lam_p⁻¹ * (4 * ∫ u, F u ^ 2) :=
    fun γ lam_p hγ hlamp =>
      two_mul_abs_integral_mul_atomicTest_le hfy hfyc hg hgs Bn V_pr hh0 hγ hlamp
  rw [hpr_eq]
  set fy_int : ℝ := ∫ u, f_y u ^ 2
  set Fh_int : ℝ := ∫ u, Fh u ^ 2
  set F_int : ℝ := ∫ u, F u ^ 2
  set LM_fy : ℝ := lowFourierMass f_y T
  set HM_fy : ℝ := highFourierMass f_y T
  set cross_int : ℝ := ∫ u, f_y u * F u
  change ((N : ℝ) / c ^ 2) * fy_int ≤ Qy at hL2_fy_le
  change ((N : ℝ) / c ^ 2) * LM_fy ≤ Qy at hLM_fy_le
  change (lam / 2) * (((N : ℝ) / c ^ 2) * HM_fy) ≤ C_high * Qy at hHM_fy
  change ((N : ℝ) / c ^ 2) * Fh_int ≤ C_ws * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) at hFh_bound
  change ((N : ℝ) / c ^ 2) * F_int ≤
    ((I₂ / c) * P) * (C_tr * c * (1 + L) * (1 + Real.log c)) at hF_scale
  change ∀ γ lam_p : ℝ, 0 < γ → 0 < lam_p →
    2 * |cross_int| ≤ γ * fy_int + γ⁻¹ * Fh_int + γ * LM_fy + γ⁻¹ * ((T * h) ^ 2 * F_int) +
      lam_p * HM_fy + lam_p⁻¹ * (4 * F_int) at hpair_all
  change (((N : ℝ) / c ^ 2) * cross_int) ^ 2 ≤
    3 * (C_ws + 4 * R₀ * C_tr + 16 * C_high * R₀ * C_tr + 1) *
      L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy
  have hlogc_le_logL : Real.log c ≤ Real.log L := Real.log_le_log hc0 hcL
  change 1 * L ^ (0 : ℝ) * (1 + Real.log L) ^ 1 ≤ L ^ (1 / 32 : ℝ) at hlogL_132
  clear hFh_mass hF_mass hL2_fy_scale harch_fy_scale hIUy_le_Qy harchUy_le hpr_eq
  clear_value fy_int Fh_int F_int LM_fy HM_fy cross_int F Fh V_pr K Bn M w g f_p f_y L I₂ P C_high C_B C_tr C_ws C_pr
  have h1_add_L : 1 + L ≤ 2 * L := by linarith only [hL1]
  have h1_add_logc_nn : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hF_low : (T * h) ^ 2 * (((N : ℝ) / c ^ 2) * F_int) ≤
      4 * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) := by
    have hlogc_2L : 1 + Real.log c ≤ 2 * L := by
      have hl := Real.log_le_sub_one_of_pos hL0
      linarith only [hlogc_le_logL, hl, hL1]
    have hprod_4L2 : (1 + L) * (1 + Real.log c) ≤ 4 * L ^ 2 := by
      calc (1 + L) * (1 + Real.log c) ≤ (2 * L) * (2 * L) :=
            mul_le_mul h1_add_L hlogc_2L h1_add_logc_nn (by positivity)
        _ = 4 * L ^ 2 := by ring
    have hc_31 : c ≤ R₀ * L ^ (31 / 32 : ℝ) :=
      hc_R₀.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)) hR₀0.le)
    have h1 := mul_le_mul_of_nonneg_left hF_scale (sq_nonneg (T * h))
    rw [hTh_eq] at h1
    calc (1 / L) ^ 2 * (((N : ℝ) / c ^ 2) * F_int)
        ≤ (1 / L) ^ 2 * (((I₂ / c) * P) * (C_tr * c * (1 + L) * (1 + Real.log c))) := h1
      _ = ((I₂ / c) * P) * (C_tr * c * (((1 + L) * (1 + Real.log c)) / L ^ 2)) := by
          field_simp [hL0.ne']
      _ ≤ ((I₂ / c) * P) * (C_tr * (R₀ * L ^ (31 / 32 : ℝ)) * 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (div_nonneg hI₂.le hc0.le) hP0)
          have hq : ((1 + L) * (1 + Real.log c)) / L ^ 2 ≤ 4 :=
            (div_le_iff₀ (by positivity)).mpr hprod_4L2
          calc C_tr * c * (((1 + L) * (1 + Real.log c)) / L ^ 2)
              ≤ C_tr * (R₀ * L ^ (31 / 32 : ℝ)) * 4 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hc_31 hCtr0) hq
                  (div_nonneg (mul_nonneg (by linarith only [hL1]) h1_add_logc_nn) (sq_nonneg L))
                  (by positivity)
      _ = 4 * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) := by ring
  have hF_high : (8 * C_high / lam) * (((N : ℝ) / c ^ 2) * F_int) ≤
      16 * C_high * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) := by
    have hlogc_132 : 1 + Real.log c ≤ L ^ (1 / 32 : ℝ) := by
      have h1 : 1 + Real.log L ≤ L ^ (1 / 32 : ℝ) := by
        simpa only [one_mul, Real.rpow_zero, pow_one] using hlogL_132
      linarith only [hlogc_le_logL, h1]
    have hexp_id : L ^ (1 / 8 : ℝ) * L * L ^ (1 / 32 : ℝ) = L ^ (31 / 32 : ℝ) * lam := by
      rw [hlam_eq, show L ^ (1 / 8 : ℝ) * L = L ^ (1 / 8 : ℝ) * L ^ (1 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      norm_num
    have hnum : c * (1 + L) * (1 + Real.log c) ≤ 2 * R₀ * L ^ (31 / 32 : ℝ) * lam := by
      calc c * (1 + L) * (1 + Real.log c)
          ≤ (R₀ * L ^ (1 / 8 : ℝ)) * (2 * L) * L ^ (1 / 32 : ℝ) :=
            mul_le_mul (mul_le_mul hc_R₀ h1_add_L (by linarith only [hL1]) (by positivity))
              hlogc_132 h1_add_logc_nn (by positivity)
        _ = 2 * R₀ * (L ^ (1 / 8 : ℝ) * L * L ^ (1 / 32 : ℝ)) := by ring
        _ = 2 * R₀ * L ^ (31 / 32 : ℝ) * lam := by rw [hexp_id]; ring
    have h1 := mul_le_mul_of_nonneg_left hF_scale (by positivity : 0 ≤ 8 * C_high / lam)
    calc (8 * C_high / lam) * (((N : ℝ) / c ^ 2) * F_int)
        ≤ (8 * C_high / lam) * (((I₂ / c) * P) * (C_tr * c * (1 + L) * (1 + Real.log c))) := h1
      _ ≤ (8 * C_high / lam) * (((I₂ / c) * P) *
            (C_tr * (2 * R₀ * L ^ (31 / 32 : ℝ) * lam))) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (div_nonneg hI₂.le hc0.le) hP0))
            (by positivity)
          calc C_tr * c * (1 + L) * (1 + Real.log c)
              = C_tr * (c * (1 + L) * (1 + Real.log c)) := by ring
            _ ≤ C_tr * (2 * R₀ * L ^ (31 / 32 : ℝ) * lam) :=
                mul_le_mul_of_nonneg_left hnum hCtr0
      _ = 16 * C_high * R₀ * C_tr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) := by
          field_simp [hlam0.ne']
  exact prime_amgm_pairing_sq_le hc0 hNR hL0 hI₂ hP0 hQy0 hChigh hCws0 hR₀0 hCtr0 hlam0
    hL2_fy_le hLM_fy_le hHM_fy hFh_bound hF_low hF_high hpair_all

/-- **Scale-uniform far-conductor prefix–collar Schur decoupling below `R_max`.**
Below any critical ratio `R_max > 0`, there exists `B_R ≥ 0` (depending only on `R_max`) such that
for every `ε > 0`, eventually in `N`, whenever `1 ≤ c`, `c⁸ ≤ R_max log N`,
`p ∈ (conductorSubspace (farConductorCutoff N) N)ᗮ` vanishes above `M = N / linearDefectCutoff c`,
and `y` vanishes on `[1, M]`, the unit-`ℓ²` centered atomic syntheses `U_p` and `U_y` satisfy
`weilBilin U_y U_p ^ 2 ≤ ε · weilQuad U_p · (weilQuad U_y + B_R ∫ U_y²)`. -/
theorem exists_far_prefix_collar_schur_decoupling_below_ratio {R_max : ℝ} (hR : 0 < R_max) :
    ∃ B_R : ℝ, 0 ≤ B_R ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ {c : ℝ}, 1 ≤ c → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
        ∀ p y : EuclideanSpace ℝ (PrimeHorizonIndex N),
          p ∈ (conductorSubspace (farConductorCutoff N) N)ᗮ →
          (∀ n, N / linearDefectCutoff c < n → primeHorizonExtension p n = 0) →
          (∀ n, n ≤ N / linearDefectCutoff c → primeHorizonExtension y n = 0) →
          let U_p := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension p) c N
          let U_y := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension y) c N
          weilBilin U_y U_p ^ 2 ≤
            ε * weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2) := by
  obtain ⟨B_g, a_R, κ_R, hBg0, haR, hκR, hgard_ev⟩ := exists_collar_atomic_garding_below_ratio hR
  let B_R : ℝ := collarDecouplingShift B_g a_R
  refine ⟨B_R, collarDecouplingShift_nonneg hBg0 haR, fun ε hε => ?_⟩
  obtain ⟨C_ψ, c₀, t₀, hCψ, hc₀, ht₀1, hpnt⟩ := exists_vonMangoldtAtom_window_error
  have hI₂ : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  set I₂ := ∫ u, tiltedUnitSpline u ^ 2
  set I₁ := ∫ u, tiltedUnitSpline u
  set D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  set G₀ := factorialSpanGammaOffset
  have hG₀ : 0 ≤ G₀ := factorialSpanGammaOffset_nonneg
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 1 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hswc0 : 0 ≤ splineWindowConstant := by unfold splineWindowConstant; positivity
  set C_high : ℝ := 2 + G₀ + Real.log 2
  have hChigh : 0 < C_high := by positivity
  set R₀ : ℝ := max 1 R_max
  have hR₀1 : 1 ≤ R₀ := le_max_left _ _
  have hRmax_R₀ : R_max ≤ R₀ := le_max_right _ _
  have hR₀0 : 0 < R₀ := zero_lt_one.trans_le hR₀1
  set C_β : ℝ := 1 + 25 / c₀ ^ 2 + |Real.log t₀|
  have hCβ1 : 1 ≤ C_β := by
    have : 0 ≤ 25 / c₀ ^ 2 + |Real.log t₀| := by positivity
    dsimp only [C_β]; linarith
  set C_B : ℝ := C_β + 1 + (Real.log 4 + 4)
  set C_tr : ℝ := (1 + 2 * Real.exp 2) *
    (Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4))
  have hCtr0 : 0 ≤ C_tr := by
    have h1 : 1 ≤ 8 * Real.exp 1 * (256 * Real.exp 2 + 4) := by
      have := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
      have := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
    have := Real.log_nonneg h1
    dsimp only [C_tr]; positivity
  set C_ws : ℝ := splineWindowConstant * R₀ * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2
  have hCws0 : 0 ≤ C_ws := by dsimp only [C_ws]; positivity
  set C_pr : ℝ := C_ws + 4 * R₀ * C_tr + 16 * C_high * R₀ * C_tr + 1
  have hCpr : 0 < C_pr := by dsimp only [C_pr]; positivity
  set C_arch : ℝ := 4 * Real.pi ^ 2
  have hCarch0 : 0 ≤ C_arch := by positivity
  set C_pole : ℝ := Real.exp 2 * I₁ ^ 4 / (κ_R * I₂)
  have hCpole0 : 0 ≤ C_pole := by positivity
  set C_tot : ℝ := 3 * (C_arch + 3 * C_pr + C_pole)
  have hCtot : 0 < C_tot := by positivity
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLN_zero : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).congr fun N => by dsimp only [Function.comp_def]; ring
  set H_cut : ℝ := 2 * (256 * Real.exp 2 + 4)
  have hHcut : 0 < H_cut := by dsimp only [H_cut]; positivity
  filter_upwards [hgard_ev, eventually_far_complement_margin hR, eventually_ge_atTop 3,
    hLlim.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 16)).comp hLlim).eventually_ge_atTop
      (2 * G₀ + 2 + Real.log (4 * C_ψ + 1)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow (by norm_num : (0 : ℝ) < 3 / 16) 1 1),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow (by norm_num : (0 : ℝ) < 1 / 32) 1 1),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow (by norm_num : (1 / 8 : ℝ) < 1) 0 R₀),
    hLN_zero.eventually (gt_mem_nhds (one_div_pos.mpr hHcut)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow (by norm_num : (3 / 8 : ℝ) < 1) 1
      (|Real.log (2 * (Real.log 4 + 4))| + 4 + C_β)),
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow (by norm_num : (0 : ℝ) < 1) 5 1),
    (Real.tendsto_log_atTop.comp hLlim).eventually_ge_atTop 4096,
    hLlim.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (31 / 32 : ℝ) < 1) 5 (8 * D * C_tot / ε))]
    with N hgard hfar hN3 hL1 hC0 hlogL_316 hlogL_132 hRL hLN_small hQ5 hpoly5 hLL4096 hdecay
  clear hgard_ev hLlim hLN_zero
  dsimp only [Function.comp_def] at hL1 hC0 hLL4096
  intro c hc1 hc8 p y hp_orth hp_supp hy_supp
  set L := Real.log (N : ℝ)
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc_R₀ : c ≤ R₀ * L ^ (1 / 8 : ℝ) := by
    have hR₀8 : R₀ ≤ R₀ ^ 8 := le_self_pow₀ hR₀1 (by omega)
    have hL8 : (L ^ (1 / 8 : ℝ)) ^ 8 = L := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have hpow : c ^ 8 ≤ (R₀ * L ^ (1 / 8 : ℝ)) ^ 8 := by
      rw [mul_pow, hL8]
      have h1 : R_max * L ≤ R₀ * L := mul_le_mul_of_nonneg_right hRmax_R₀ hL0.le
      have h2 : R₀ * L ≤ R₀ ^ 8 * L := mul_le_mul_of_nonneg_right hR₀8 hL0.le
      linarith only [hc8, h1, h2]
    exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow
  have hcL : c ≤ L := by
    have hRL' : R₀ * L ^ (1 / 8 : ℝ) ≤ L := by
      simpa only [pow_zero, mul_one, Real.rpow_one] using hRL
    exact hc_R₀.trans hRL'
  obtain ⟨hLc3, h4c, -, hLcup⟩ := linearDefectCutoff_bounds hc1
  have h2LN : 2 * linearDefectCutoff c ≤ N := by
    have hLN_lt : L < 1 / H_cut * N := (div_lt_iff₀ hNR).mp hLN_small
    have hHL : H_cut * L ≤ N := by
      have hm := mul_lt_mul_of_pos_left hLN_lt hHcut
      rw [← mul_assoc, mul_one_div_cancel hHcut.ne', one_mul] at hm
      exact hm.le
    have h2Lc : (2 * linearDefectCutoff c : ℝ) ≤ N := by
      push_cast
      have h1 : 2 * (linearDefectCutoff c : ℝ) ≤ H_cut * c := by
        dsimp only [H_cut]; linarith only [hLcup]
      have h2 : H_cut * c ≤ H_cut * L := mul_le_mul_of_nonneg_left hcL hHcut.le
      linarith only [h1, h2, hHL]
    exact_mod_cast h2Lc
  have hLN_nat : linearDefectCutoff c ≤ N := by omega
  set M := N / linearDefectCutoff c
  have hMN : M ≤ N := Nat.div_le_self _ _
  have hM1 : 1 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
  have hML : (M : ℝ) * linearDefectCutoff c ≤ N := by exact_mod_cast Nat.div_mul_le_self N _
  set θ : ℝ := 1 / (1 + Real.log L) ^ 5
  have ht5_pos : 0 < (1 + Real.log L) ^ 5 := by
    have := Real.log_nonneg hL1; positivity
  have hθ_hi : θ ≤ 1 / 4096 := by
    dsimp only [θ]
    refine one_div_le_one_div_of_le (by norm_num) ?_
    have h1 : (4096 : ℝ) ≤ 1 + Real.log L := by linarith only [hLL4096]
    exact h1.trans (le_self_pow₀ (by linarith only [h1]) (by omega))
  have hθL_ge1 : 1 ≤ θ * L := by
    have hp : (1 + Real.log L) ^ 5 ≤ L := by
      simpa only [one_mul, Real.rpow_zero, Real.rpow_one] using hpoly5
    dsimp only [θ]
    rw [one_div_mul_eq_div]
    exact (one_le_div ht5_pos).mpr hp
  have hR1_ge1 : 1 ≤ farConductorCutoff N := by
    unfold farConductorCutoff
    refine Nat.le_floor ?_
    rw [Nat.cast_one]
    change (1 : ℝ) ≤ (N : ℝ) ^ θ
    rw [Real.rpow_def_of_pos hNR]
    exact Real.one_le_exp (by linarith only [hθL_ge1, (by ring : L * θ = θ * L)])
  have hp1 : p ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hp_orth v (conductorSubspace_mono hR1_ge1 N hv)
  set x_p := primeHorizonExtension p
  set x_y := primeHorizonExtension y
  set w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hNR
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN_nat
    linarith only [h4c, hLNR, hc0]
  set g := atomDilate tiltedUnitSpline w
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hgs := tiltedUnitSpline_atom_support hw
  have hmass_g : (∫ u, g u ^ 2) = w * I₂ := integral_atomDilate_sq hw
  set f_p := atomicTest N x_p g
  set f_y := atomicTest N x_y g
  have hfp : ContDiff ℝ 2 f_p := contDiff_atomicTest hg N x_p
  have hfpc : HasCompactSupport f_p := hasCompactSupport_atomicTest hgs N x_p
  have hfy : ContDiff ℝ 2 f_y := contDiff_atomicTest hg N x_y
  have hfyc : HasCompactSupport f_y := hasCompactSupport_atomicTest hgs N x_y
  set U_p := normalizedCentredAtomicTest tiltedUnitSpline x_p c N
  set U_y := normalizedCentredAtomicTest tiltedUnitSpline x_y c N
  set Qy : ℝ := weilQuad U_y + B_R * ∫ u, U_y u ^ 2
  obtain ⟨hIUy_le_Qy, hQy0, hS7_le_Qy, harchUy_le, hL2_fy_scale, harch_fy_scale, hbil_scale⟩ :=
    collar_shifted_energy_and_scale_bounds (x_p := x_p) hc0 hcN hBg0 haR hκR hN1 hy_supp
      (hgard hc1 hc8 x_y)
  set P : ℝ := ∑ n ∈ Icc 1 M, x_p n ^ 2
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hfp_M : f_p = atomicTest M x_p g := by
    funext u; dsimp only [f_p]; unfold atomicTest
    refine (Finset.sum_subset (Icc_subset_Icc_right hMN) fun n hn hnot => ?_).symm
    have hgt : M < n := Nat.lt_of_not_le fun hle => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, hle⟩)
    rw [hp_supp n hgt, zero_mul]
  have hsep : w < atomSpacing M := by
    have hLR : (0 : ℝ) < linearDefectCutoff c := by exact_mod_cast (show 0 < linearDefectCutoff c by omega)
    have hwN : w * N = c := by dsimp only [w]; field_simp [hNR.ne']
    have hwM : w * M ≤ c / linearDefectCutoff c := by
      rw [le_div_iff₀ hLR]
      calc w * M * linearDefectCutoff c = w * ((M : ℝ) * linearDefectCutoff c) := by ring
        _ ≤ w * N := mul_le_mul_of_nonneg_left hML hw.le
        _ = c := hwN
    have hfour : 4 * w * M ≤ 1 := by
      have hl : 4 * (c / (linearDefectCutoff c : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc, div_le_one hLR]; exact h4c
      have hm := mul_le_mul_of_nonneg_left hwM (by norm_num : (0 : ℝ) ≤ 4)
      linarith only [hm, hl, (by ring : 4 * (w * M) = 4 * w * M)]
    have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have hbound : w ≤ (1 / ((M : ℝ) + 1)) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_div_iff₀ (by positivity : (0 : ℝ) < M + 1)]
      have h0 : 0 ≤ 2 * w * ((M : ℝ) - 1) := mul_nonneg (by positivity) (sub_nonneg.mpr hM1R)
      linarith only [hfour, h0, (by ring : w * 2 * ((M : ℝ) + 1) = 4 * w * M - 2 * w * ((M : ℝ) - 1))]
    have h1 := (atomSpacing_bounds hM1).1
    have hp_sp := atomSpacing_pos hM1
    linarith only [hbound, h1, hp_sp]
  -- (A) Ordered Gamma cross bound
  set archBilin : ℝ := (archForm (fun u => f_p u + f_y u) - archForm (fun u => f_p u - f_y u)) / 4
  have harch_sq : (((N : ℝ) / c ^ 2) * archBilin) ^ 2 ≤ C_arch * ((I₂ / c) * P) * Qy := by
    let x_plus : ℕ → ℝ := fun n => x_p n + x_y n
    obtain ⟨boundary, hleft0, hright0⟩ := atomicTest_prefix_tail_ordered hgs hM1 hsep N x_plus
    have hpre_eq : atomicTest M x_plus g = f_p := by
      rw [hfp_M]; funext u; unfold atomicTest
      refine sum_congr rfl fun n hn => ?_
      dsimp only [x_plus]; rw [hy_supp n (mem_Icc.mp hn).2, add_zero]
    have htail_eq : atomicTailCoefficients M x_plus = x_y := by
      funext n; unfold atomicTailCoefficients; dsimp only [x_plus]
      by_cases h : M < n
      · rw [if_pos h, hp_supp n h, zero_add]
      · rw [if_neg h, hy_supp n (Nat.not_lt.mp h)]
    have hleft : ∀ u, boundary ≤ u → f_p u = 0 := by rw [← hpre_eq]; exact hleft0
    have hright : ∀ u, u ≤ boundary → f_y u = 0 := by
      dsimp only [f_y]; rw [← htail_eq]; exact hright0
    have hfp_L2 : (∫ u, f_p u ^ 2) = (w * I₂) * P := by
      rw [hfp_M, integral_atomicTest_sq hg hgc hgs hsep, hmass_g, mul_comm]
    have hord := archBilin_ordered_sq_le hfp hfpc hfy hfyc hleft hright
    change archBilin ^ 2 ≤ C_arch * (∫ u, f_p u ^ 2) * (∫ u, f_y u ^ 2) at hord
    rw [hfp_L2] at hord
    have hmul := mul_le_mul_of_nonneg_left hord (sq_nonneg ((N : ℝ) / c ^ 2))
    have hid : ((N : ℝ) / c ^ 2) ^ 2 * (C_arch * ((w * I₂) * P) * ∫ u, f_y u ^ 2) =
        C_arch * ((I₂ / c) * P) * (((N : ℝ) / c ^ 2) * ∫ u, f_y u ^ 2) := by
      dsimp only [w]; field_simp [hc0.ne', hNR.ne']
    rw [← mul_pow, hid, hL2_fy_scale] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left hIUy_le_Qy (by positivity))
  -- (B) Pole cross bound
  set poleBilin : ℝ :=
    (∫ u, f_p u * Real.exp (-(u / 2))) * (∫ u, f_y u * Real.exp (u / 2)) +
      (∫ u, f_y u * Real.exp (-(u / 2))) * (∫ u, f_p u * Real.exp (u / 2))
  have hp_pole_sum : ∑ n ∈ Icc 1 N, x_p n / Real.sqrt n = 0 :=
    poleFunctional_eq_zero_of_mem_conductorSubspace_one_orthogonal hN2 hp1
  have hsigma0 : prefixPoleMoment M x_p = 0 := by
    unfold prefixPoleMoment
    rw [← hp_pole_sum]
    refine Finset.sum_subset (Icc_subset_Icc_right hMN) fun n hn hnot => ?_
    have hgt : M < n := Nat.lt_of_not_le fun hle => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, hle⟩)
    rw [hp_supp n hgt, zero_div]
  have hpole_sq : (((N : ℝ) / c ^ 2) * poleBilin) ^ 2 ≤ C_pole * ((I₂ / c) * P) * Qy :=
    poleBilin_prefix_collar_sq_le hc1 hcN hκR hN1 hMN hML hp_supp hy_supp hp_pole_sum hS7_le_Qy
  -- (C) Prime cross bound
  set primeBilin : ℝ := (primeSum (fun u => f_p u + f_y u) - primeSum (fun u => f_p u - f_y u)) / 4
  have hprime_sq : (((N : ℝ) / c ^ 2) * primeBilin) ^ 2 ≤
      3 * C_pr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy := by
    have hlogL_le : Real.log L ≤ L ^ (3 / 16 : ℝ) := by
      have h1 : 1 + Real.log L ≤ L ^ (3 / 16 : ℝ) := by
        simpa only [one_mul, Real.rpow_zero, pow_one] using hlogL_316
      linarith only [h1]
    obtain ⟨h, T, lam, β, K', hlam_eq, hlam1, hh_eq, hh0, hh1, hT0, _hlogT_ge, hlogT_eq,
      hTh_eq, hhL_le2, hlam_half, hK'1, ht₀', hpnt', hlogK', hK'le, hβ_le, hβ0⟩ :=
      exists_far_parameters hCψ hc₀ ht₀1 hL1 hC0 hlogL_le
    obtain ⟨hFh_mass, hF_mass⟩ := translate_masses_le hCψ hc₀ hpnt hc1 h2LN x_p hh0 hh1 hK'1 ht₀'
    exact primeBilin_prefix_collar_sq_le hCψ hR₀0 (by linarith only [hCβ1]) hQy0 hc1 hcN h2LN hN1
      hL1 hc_R₀ hcL hlam_eq hlam1 hh_eq hh0 hh1 hT0 hlogT_eq hTh_eq hhL_le2 hlam_half hK'1 hpnt'
      hlogK' hK'le hβ_le hβ0 hlogL_132 hQ5 hp_supp hy_supp hsigma0 hFh_mass hF_mass
      (hL2_fy_scale.le.trans hIUy_le_Qy) hL2_fy_scale harch_fy_scale hIUy_le_Qy harchUy_le
  -- (D) Prefix Weil energy lower bound and `o(1)` conclusion
  have hQp_ge : (θ * L / (8 * D)) * ((I₂ / c) * P) ≤ weilQuad U_p := by
    have hS7_p0 : topCollarSeventhMass M N x_p = 0 := by
      unfold topCollarSeventhMass
      refine sum_eq_zero fun n hn => ?_
      rw [hp_supp n (mem_Ioc.mp hn).1]; ring
    have hf_p := hfar c θ hc1 hc8 le_rfl hθ_hi p hp_orth
    change (θ * L / (8 * D)) * P + (c * farMargin R_max) * topCollarSeventhMass M N x_p ≤
      completeWeilEnergy tiltedUnitSpline c N p at hf_p
    rw [hS7_p0, mul_zero, add_zero] at hf_p
    have hqp := weilQuad_normalizedCentredAtomicTest_eq contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero hI₂ hc0 hN1 p
    change weilQuad U_p = (I₂ / c) * completeWeilEnergy tiltedUnitSpline c N p at hqp
    rw [hqp]
    exact (mul_le_mul_of_nonneg_left hf_p (div_nonneg hI₂.le hc0.le)).trans_eq' (by ring)
  have hsp_bil : weilBilin U_y U_p =
      ((N : ℝ) / c ^ 2) * archBilin - ((N : ℝ) / c ^ 2) * primeBilin +
        ((N : ℝ) / c ^ 2) * poleBilin := by
    have hsp := weilBilin_split_eq hfp hfpc hfy hfyc
    change weilBilin f_p f_y = archBilin - primeBilin + poleBilin at hsp
    rw [hbil_scale, hsp]
    ring
  set bil_val : ℝ := weilBilin U_y U_p
  set Up_quad : ℝ := weilQuad U_p
  set a := ((N : ℝ) / c ^ 2) * archBilin
  set b := ((N : ℝ) / c ^ 2) * primeBilin
  set d := ((N : ℝ) / c ^ 2) * poleBilin
  change bil_val = a - b + d at hsp_bil
  change a ^ 2 ≤ C_arch * ((I₂ / c) * P) * Qy at harch_sq
  change d ^ 2 ≤ C_pole * ((I₂ / c) * P) * Qy at hpole_sq
  change b ^ 2 ≤ 3 * C_pr * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy at hprime_sq
  change (θ * L / (8 * D)) * ((I₂ / c) * P) ≤ Up_quad at hQp_ge
  change bil_val ^ 2 ≤ ε * Up_quad * Qy
  change (8 * D * C_tot / ε) * L ^ (31 / 32 : ℝ) * (1 + Real.log L) ^ 5 ≤ L ^ (1 : ℝ) at hdecay
  have hθ_def : θ = 1 / (1 + Real.log L) ^ 5 := rfl
  have hCtot_def : C_tot = 3 * (C_arch + 3 * C_pr + C_pole) := rfl
  clear hgard hfar hIUy_le_Qy hS7_le_Qy harchUy_le hL2_fy_scale harch_fy_scale hbil_scale
    hfp_M hsigma0 hp_pole_sum hp_orth hp1 hp_supp hy_supp hpnt
  clear_value bil_val Up_quad a b d archBilin primeBilin poleBilin Qy U_p U_y f_p f_y g w
    x_p x_y P θ M L I₂ I₁ D G₀ C_high R₀ C_β C_B C_tr C_ws C_pr C_arch C_pole C_tot H_cut
  have hIP0 : 0 ≤ (I₂ / c) * P := mul_nonneg (div_nonneg hI₂.le hc0.le) hP0
  have hbil_tot : bil_val ^ 2 ≤ C_tot * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy := by
    rw [hsp_bil]
    have hcs3 : (a - b + d) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + d ^ 2) := by
      linarith only [sq_nonneg (a + b), sq_nonneg (a - d), sq_nonneg (b + d),
        (by ring : 3 * (a ^ 2 + b ^ 2 + d ^ 2) - (a - b + d) ^ 2 =
          (a + b) ^ 2 + (a - d) ^ 2 + (b + d) ^ 2)]
    have hL31_ge1 : 1 ≤ L ^ (31 / 32 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have ha_le : a ^ 2 ≤ C_arch * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy :=
      harch_sq.trans (by
        have hm := mul_le_mul_of_nonneg_left hL31_ge1
          (mul_nonneg (mul_nonneg hCarch0 hIP0) hQy0)
        linarith only [hm, (by ring : C_arch * ((I₂ / c) * P) * Qy * 1 =
          C_arch * ((I₂ / c) * P) * Qy),
          (by ring : C_arch * ((I₂ / c) * P) * Qy * L ^ (31 / 32 : ℝ) =
            C_arch * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy)])
    have hd_le : d ^ 2 ≤ C_pole * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy :=
      hpole_sq.trans (by
        have hm := mul_le_mul_of_nonneg_left hL31_ge1
          (mul_nonneg (mul_nonneg hCpole0 hIP0) hQy0)
        linarith only [hm, (by ring : C_pole * ((I₂ / c) * P) * Qy * 1 =
          C_pole * ((I₂ / c) * P) * Qy),
          (by ring : C_pole * ((I₂ / c) * P) * Qy * L ^ (31 / 32 : ℝ) =
            C_pole * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy)])
    rw [hCtot_def]
    linarith only [hcs3, ha_le, hprime_sq, hd_le]
  have hcoef_le : C_tot * L ^ (31 / 32 : ℝ) ≤ ε * (θ * L / (8 * D)) := by
    have hd1 : (8 * D * C_tot / ε) * L ^ (31 / 32 : ℝ) * (1 + Real.log L) ^ 5 ≤ L := by
      simpa only [Real.rpow_one] using hdecay
    have hd2 : (8 * D * C_tot / ε) * L ^ (31 / 32 : ℝ) ≤ θ * L := by
      rw [hθ_def, one_div_mul_eq_div, le_div_iff₀ ht5_pos]
      exact hd1
    have hd3 := mul_le_mul_of_nonneg_left hd2 (div_nonneg hε.le (by positivity : 0 ≤ 8 * D))
    have hid1 : (ε / (8 * D)) * ((8 * D * C_tot / ε) * L ^ (31 / 32 : ℝ)) =
        C_tot * L ^ (31 / 32 : ℝ) := by field_simp [hε.ne', hD.ne']
    have hid2 : (ε / (8 * D)) * (θ * L) = ε * (θ * L / (8 * D)) := by ring
    linarith only [hd3, hid1, hid2]
  calc bil_val ^ 2
      ≤ C_tot * L ^ (31 / 32 : ℝ) * ((I₂ / c) * P) * Qy := hbil_tot
    _ ≤ (ε * (θ * L / (8 * D))) * ((I₂ / c) * P) * Qy :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef_le hIP0) hQy0
    _ = ε * ((θ * L / (8 * D)) * ((I₂ / c) * P)) * Qy := by ring
    _ ≤ ε * Up_quad * Qy :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQp_ge hε.le) hQy0

/-- **Conductor-adapted `o(1)` prefix–collar Schur decoupling along a fixed critical ratio.**
Along any critical schedule `c_N ≥ 1` with `c_N⁸ / log N → R > 0`, there exists `B_R ≥ 0` such
that for every `ε > 0`, eventually in `N`, every prefix `p ∈ (conductorSubspace R₁ N)ᗮ`
(`R₁ = farConductorCutoff N`) vanishing above `M = N / linearDefectCutoff (c_N)` and every collar
vector `y` vanishing on `[1, M]` satisfy
`weilBilin U_y U_p ^ 2 ≤ ε · weilQuad U_p · (weilQuad U_y + B_R ∫ U_y²)`. -/
theorem exists_far_prefix_collar_schur_decoupling {c : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (htend : Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 R)) :
    ∃ B_R : ℝ, 0 ≤ B_R ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ p y : EuclideanSpace ℝ (PrimeHorizonIndex N),
        p ∈ (conductorSubspace (farConductorCutoff N) N)ᗮ →
        (∀ n, N / linearDefectCutoff (c N) < n → primeHorizonExtension p n = 0) →
        (∀ n, n ≤ N / linearDefectCutoff (c N) → primeHorizonExtension y n = 0) →
        let U_p := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension p) (c N) N
        let U_y := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension y) (c N) N
        weilBilin U_y U_p ^ 2 ≤
          ε * weilQuad U_p * (weilQuad U_y + B_R * ∫ u, U_y u ^ 2) := by
  obtain ⟨B_R, hBR0, hdec⟩ :=
    exists_far_prefix_collar_schur_decoupling_below_ratio (R_max := R + 1) (by linarith)
  refine ⟨B_R, hBR0, fun ε hε => ?_⟩
  filter_upwards [hdec ε hε, hc1, htend.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    eventually_ge_atTop 3] with N hN hcN hrat hN3 p y hp_orth hp_supp hy_supp
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  exact hN hcN ((div_lt_iff₀ hL0).mp hrat).le p y hp_orth hp_supp hy_supp

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_prime_quasimode_prefix_collar_schur_ratio
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.not_naive_physical_prefix_collar_schur_decoupling
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_far_prefix_collar_schur_decoupling_below_ratio
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_far_prefix_collar_schur_decoupling
