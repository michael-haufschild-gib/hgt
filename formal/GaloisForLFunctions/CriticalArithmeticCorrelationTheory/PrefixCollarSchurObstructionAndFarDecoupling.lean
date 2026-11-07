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
  dsimp only [Function.comp_def] at hrat_ub hNf hL_rpow hL_big
  set L := Real.log (N : ℝ)
  let q := primeAboveLowPacket N
  obtain ⟨hq_prime, hq_gt, hq_le⟩ := primeAboveLowPacket_spec N
  have h4_le : (4 : ℝ) ^ (96 : ℝ) ≤ L := by linarith only [hL_big]
  have hL1 : 1 ≤ L := by linarith [Real.rpow_nonneg (zero_le_four (α := ℝ)) 96]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc0 : 0 < c N := zero_lt_one.trans_le hcN
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
  have hR1_64 : R + 1 ≤ L ^ (1 / 64 : ℝ) := by
    linarith only [hL_rpow, hR, hK_res, hC_q,
      abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1)]
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
  have h2_le_rpow : (2 : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
    have hp := Real.rpow_le_rpow (by positivity) h4_le (by norm_num : (0 : ℝ) ≤ 1 / 96)
    rw [← Real.rpow_mul (by norm_num)] at hp
    norm_num at hp
    exact (by norm_num : (2 : ℝ) ≤ 4).trans
      (hp.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
  have hq_le_4rpow : (q : ℝ) ≤ 4 * L ^ (13 / 32 : ℝ) := by
    have hQ1 : (lowPacketCutoff N : ℝ) ≤ L ^ (13 / 32 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg hL0.le _)
    have hmax : ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
      rw [Nat.cast_max, Nat.cast_ofNat]; exact max_le h2_le_rpow hQ1
    have hqc : (q : ℝ) ≤ 2 * ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) := by exact_mod_cast hq_le
    linarith
  have hq_gt_rpow : L ^ (13 / 32 : ℝ) < (q : ℝ) := by
    have hlt_fl := Nat.lt_floor_add_one (L ^ (13 / 32 : ℝ))
    have hq_ge : lowPacketCutoff N + 1 ≤ q := by
      have := (le_max_right 2 (lowPacketCutoff N)).trans_lt hq_gt; omega
    exact hlt_fl.trans_le (by exact_mod_cast hq_ge)
  have hq_le_15 : (q : ℝ) ≤ L ^ (15 / 32 : ℝ) := by
    have h4_16 : (4 : ℝ) ≤ L ^ (2 / 32 : ℝ) := by
      have hp := Real.rpow_le_rpow (by positivity) h4_le (by norm_num : (0 : ℝ) ≤ 2 / 32)
      rw [← Real.rpow_mul (by norm_num)] at hp
      exact (by norm_num : (4 : ℝ) ≤ 4 ^ (6 : ℝ)).trans (hp.trans_eq' (by norm_num))
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
    have hlq : Real.log (q : ℝ) ≤ Real.log L :=
      Real.log_le_log (by exact_mod_cast hq_prime.pos) hq_le_L
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
  have hN_width : 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ N := by
    have hc2_L4 : c N ^ 2 ≤ (R + 1) * L ^ 4 :=
      hc2_le.trans (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_natCast L 4))
        (by linarith))
    have hprod := mul_le_mul_of_nonneg_left hc2_L4 (show 0 ≤ 4 * (Real.exp 1 + 3) ^ 2 by positivity)
    have hK0 : 0 ≤ K_res * (R + 1) ^ 5 * L ^ 4 := by positivity
    nlinarith only [hN_L4, hprod, hK0, pow_pos hL0 4]
  let v := normalizedRamanujanHorizonVector q N
  let u := (conductorSubspace (lowPacketCutoff N) N).starProjection v
  let E_q := completedConductorEnergy tiltedUnitSpline (c N) q
  have hr_norm : ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) v - E_q • v‖ ≤ 1 := by
    have hr0 := hresN q hq_prime.pos hq_le_15 (c N) hcN hN_width
    have ht1 : K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
        (c N ^ 2 * (1 + Real.log (c N)) ^ 3 * L ^ (1 / (16 : ℝ)) / L) ≤ 1 / 2 := by
      have hp2 : (1 + Real.log q) ^ 2 ≤ 65 ^ 2 * L ^ (2 / 64 : ℝ) := by
        have hp := pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg q]) h1q_64 2
        rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 64 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hp
        norm_num at hp; exact hp
      have hp3 : (1 + Real.log (c N)) ^ 3 ≤ 65 ^ 3 * L ^ (3 / 64 : ℝ) := by
        have hp := pow_le_pow_left₀ (by linarith [Real.log_nonneg hcN]) h1c_64 3
        rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 64 : ℝ)) 3, ← Real.rpow_mul hL0.le] at hp
        norm_num at hp; exact hp
      have hKR_64 : K_res * (R + 1) ≤ L ^ (1 / 64 : ℝ) := by
        linarith only [hL_rpow, hR, hK_res, hC_q,
          abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1)]
      calc K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
            (c N ^ 2 * (1 + Real.log (c N)) ^ 3 * L ^ (1 / 16 : ℝ) / L)
          ≤ K_res * (4 * L ^ (13 / 32 : ℝ) * (65 ^ 2 * L ^ (2 / 64 : ℝ))) *
            ((R + 1) * L ^ (1 / 4 : ℝ) * (65 ^ 3 * L ^ (3 / 64 : ℝ)) * L ^ (1 / 16 : ℝ) / L) :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left (mul_le_mul hq_le_4rpow hp2 (by positivity) (by positivity))
                hK_res.le)
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul hc2_le hp3 (by positivity) (by positivity))
                  (by positivity)) hL0.le)
              (by positivity) (by positivity)
        _ = (4 * 65 ^ 5) * (K_res * (R + 1)) *
            (L ^ (13 / 32 : ℝ) * L ^ (2 / 64 : ℝ) * L ^ (1 / 4 : ℝ) *
              L ^ (3 / 64 : ℝ) * L ^ (1 / 16 : ℝ) / L) := by ring
        _ ≤ (4 * 65 ^ 5) * L ^ (1 / 64 : ℝ) *
            (L ^ (13 / 32 : ℝ) * L ^ (2 / 64 : ℝ) * L ^ (1 / 4 : ℝ) *
              L ^ (3 / 64 : ℝ) * L ^ (1 / 16 : ℝ) / L) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKR_64 (by norm_num))
              (by positivity)
        _ = (4 * 65 ^ 5) / L ^ (3 / 16 : ℝ) := by
            rw [show (4 * 65 ^ 5 : ℝ) * L ^ (1 / 64 : ℝ) *
                (L ^ (13 / 32 : ℝ) * L ^ (2 / 64 : ℝ) * L ^ (1 / 4 : ℝ) *
                  L ^ (3 / 64 : ℝ) * L ^ (1 / 16 : ℝ) / L) =
              (4 * 65 ^ 5) * (L ^ (1 / 64 : ℝ) * L ^ (13 / 32 : ℝ) * L ^ (2 / 64 : ℝ) *
                L ^ (1 / 4 : ℝ) * L ^ (3 / 64 : ℝ) * L ^ (1 / 16 : ℝ) / L) by ring,
              ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
              ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_sub_one hL0.ne']
            have hexp : (1 / 64 + 13 / 32 + 2 / 64 + 1 / 4 + 3 / 64 + 1 / 16 - 1 : ℝ) =
                -(3 / 16) := by norm_num
            rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
        _ ≤ 1 / 2 := by
            rw [div_le_iff₀ (Real.rpow_pos_of_pos hL0 _)]
            have hnum : (4 * 65 ^ 5 : ℝ) ≤ (1 / 2 : ℝ) * (4 : ℝ) ^ (18 : ℝ) := by norm_num
            nlinarith only [hnum, hL_3_16]
    have ht2 : K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) * (c N ^ 10 * (L / N) ^ 2) ≤ 1 / 2 := by
      have h1q_L : 1 + Real.log q ≤ L := by
        have h65_63 : (65 : ℝ) ≤ L ^ (63 / 64 : ℝ) :=
          (by norm_num : (65 : ℝ) ≤ (4 : ℝ) ^ (42 : ℝ)).trans
            (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
        have hm := mul_le_mul_of_nonneg_right h65_63 (Real.rpow_nonneg hL0.le (1 / 64 : ℝ))
        rw [← Real.rpow_add hL0] at hm; norm_num at hm; rw [Real.rpow_one] at hm
        exact h1q_64.trans hm
      have hq_L3 : (q : ℝ) * (1 + Real.log q) ^ 2 ≤ L ^ 3 := by
        have hp2 : (1 + Real.log q) ^ 2 ≤ L ^ 2 :=
          pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg q]) h1q_L 2
        calc (q : ℝ) * (1 + Real.log q) ^ 2 ≤ L * L ^ 2 :=
              mul_le_mul hq_le_L hp2 (by positivity) hL0.le
          _ = L ^ 3 := by ring
      have hc10 : c N ^ 10 ≤ (R + 1) ^ 5 * L ^ 2 := by
        have hp5 : (c N ^ 2) ^ 5 ≤ ((R + 1) * L ^ (1 / 4 : ℝ)) ^ 5 :=
          pow_le_pow_left₀ (sq_nonneg _) hc2_le 5
        rw [← pow_mul, mul_pow, ← Real.rpow_natCast (L ^ (1 / 4 : ℝ)) 5, ← Real.rpow_mul hL0.le] at hp5
        norm_num at hp5
        exact hp5.trans (mul_le_mul_of_nonneg_left
          ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_natCast L 2))
          (by positivity))
      have hL4_N : L ^ 4 / N ≤ 1 / (2 * K_res * (R + 1) ^ 5) := by
        rw [div_le_div_iff₀ hN0 (by positivity)]
        have hpos_rest : 0 ≤ 4 * (Real.exp 1 + 3) ^ 2 * (R + 1) + 16 := by positivity
        nlinarith [hN_L4, hpos_rest, pow_pos hL0 4]
      have hL3_N : L ^ 3 / N ≤ 1 := by
        rw [div_le_one hN0]
        have h34 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by omega)
        have hpos_rest : 0 ≤ K_res * (R + 1) ^ 5 + 4 * (Real.exp 1 + 3) ^ 2 * (R + 1) := by positivity
        nlinarith [h34, hN_L4, hpos_rest, pow_pos hL0 4]
      calc K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) * (c N ^ 10 * (L / N) ^ 2)
          ≤ K_res * L ^ 3 * ((R + 1) ^ 5 * L ^ 2 * (L ^ 2 / N ^ 2)) := by
            rw [div_pow]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hq_L3 hK_res.le)
              (mul_le_mul_of_nonneg_right hc10 (by positivity)) (by positivity) (by positivity)
        _ = K_res * (R + 1) ^ 5 * (L ^ 4 / N) * (L ^ 3 / N) := by field_simp [hN0.ne']; ring
        _ ≤ K_res * (R + 1) ^ 5 * (1 / (2 * K_res * (R + 1) ^ 5)) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hL4_N (by positivity)) hL3_N
              (by positivity) (by positivity)
        _ = 1 / 2 := by
            have hne : (R + 1) ^ 5 ≠ 0 := pow_ne_zero 5 (by linarith)
            field_simp [hK_res.ne', hne]
    have hrsq : ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) v - E_q • v‖ ^ 2 ≤ 1 := by
      have hr0' : ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) v - E_q • v‖ ^ 2 ≤
          K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
            (c N ^ 2 * (1 + Real.log (c N)) ^ 3 * L ^ (1 / (16 : ℝ)) / L +
              c N ^ 10 * (L / N) ^ 2) := by
        simpa only [Nat.cast_ofNat] using hr0
      rw [mul_add] at hr0'
      linarith only [hr0', ht1, ht2]
    nlinarith only [hrsq,
      norm_nonneg (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) v - E_q • v)]
  have hqqN : q * q ≤ N := by
    have hq2_L4 : ((q * q : ℕ) : ℝ) ≤ L ^ 4 := by
      rw [Nat.cast_mul]
      have h24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by omega)
      nlinarith only [hq_le_L, h24, Nat.cast_nonneg (α := ℝ) q]
    have hL4_le_N : L ^ 4 ≤ N := by
      have hpos_rest : 0 ≤ K_res * (R + 1) ^ 5 + 4 * (Real.exp 1 + 3) ^ 2 * (R + 1) := by positivity
      nlinarith [hN_L4, hpos_rest, pow_pos hL0 4]
    exact_mod_cast hq2_L4.trans hL4_le_N
  have hv_rpow : |‖v‖ ^ 2 - 1| ≤ 137 / L ^ (63 / 64 : ℝ) := by
    have hv0 := abs_norm_normalizedRamanujanHorizonVector_sq_sub_one_le hq_prime.two_le hqqN
    have hnum : 2 * Real.log (q : ℝ) + 9 ≤ 137 * L ^ (1 / 64 : ℝ) := by
      linarith only [h1q_64, h1_64]
    calc |‖v‖ ^ 2 - 1| ≤ (2 * Real.log (q : ℝ) + 9) / L := hv0
      _ ≤ 137 * L ^ (1 / 64 : ℝ) / L := div_le_div_of_nonneg_right hnum hL0.le
      _ = 137 / L ^ (63 / 64 : ℝ) := by
          rw [mul_div_assoc, ← Real.rpow_sub_one hL0.ne']
          have hexp : (1 / 64 - 1 : ℝ) = -(63 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
  have hv_norm : ‖v‖ ≤ 2 := by
    have h137 : 137 / L ^ (63 / 64 : ℝ) ≤ 1 := by
      rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
      exact (by norm_num : (137 : ℝ) ≤ (4 : ℝ) ^ (42 : ℝ)).trans
        (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
    have := (abs_le.mp hv_rpow).2
    nlinarith only [this, h137, norm_nonneg v]
  have hsh_le : |shellCorrection tiltedUnitSpline (c N) q| ≤ 1 := by
    have hc_lt_q : c N < q :=
      hc_le_9.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hL1 (by norm_num)).trans hq_gt_rpow)
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
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          have hp := Real.rpow_le_rpow (by positivity) h4_le (by norm_num : (0 : ℝ) ≤ 9 / 64)
          rw [← Real.rpow_mul (by norm_num)] at hp
          exact (by norm_num : (4 : ℝ) ≤ (4 : ℝ) ^ (27 / 2 : ℝ)).trans hp
  have hEq_sub : |E_q - (Real.log q - Real.log (c N))| ≤
      |completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 := by
    have hEq_f : E_q = completeWeilSelfFinitePart tiltedUnitSpline 1 + Real.log q +
        ArithmeticIntersectionTheory.tameDifferent q - Real.log (c N) -
        shellCorrection tiltedUnitSpline (c N) q := by
      dsimp only [E_q]
      rw [completedConductorEnergy_eq_sub_shellCorrection hc0 hq_prime.pos,
        completeWeilAdjunctionEnergy_eq_at_one_sub_log tiltedUnitSpline hq_prime.ne_one hc0]
      unfold completeWeilAdjunctionEnergy ramanujanAdjunctionEnergy
      rw [if_neg hq_prime.ne_one]
      ring
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
      linarith only [hL_rpow, hR, hK_res, hC_q]
    have hsum1 : |E_q| ≤ (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 4) * (130 * L ^ (1 / 64 : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left h1_64
        (show 0 ≤ |completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 by positivity)
      nlinarith only [htri, hEq_sub, h1q_64, h1c_64, hm, h1_64,
        abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1)]
    calc |E_q| ≤ ((1 / 200 : ℝ) * L ^ (1 / 64 : ℝ)) * (130 * L ^ (1 / 64 : ℝ)) :=
          hsum1.trans (mul_le_mul_of_nonneg_right hS1 (by positivity))
      _ ≤ 2 * (L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ)) := by
          have : (130 / 200 : ℝ) ≤ 2 := by norm_num
          nlinarith [Real.rpow_nonneg hL0.le (1 / 64 : ℝ)]
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
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
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
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
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
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
      _ ≤ 1 / 4 := by
          rw [div_le_iff₀ (Real.rpow_pos_of_pos hL0 _)]
          have hnum : (2340 : ℝ) ≤ (1 / 4 : ℝ) * (4 : ℝ) ^ (42 : ℝ) := by norm_num
          have h7 : L ^ (7 / 16 : ℝ) ≤ L ^ (61 / 64 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
          nlinarith only [hnum, hL_7_16, h7]
  have hEu_abs : |completeWeilEnergy tiltedUnitSpline (c N) N u| ≤ 1 := by
    have hg := (hglobN hcN hc_le_L).1 u
    refine hg.trans ?_
    have hc3_le : c N ^ 3 ≤ (R + 1) ^ 2 * L ^ (1 / 2 : ℝ) := by
      have hc34 : c N ^ 3 ≤ (c N ^ 2) ^ 2 := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hcN (by omega)
      have hc4 : (c N ^ 2) ^ 2 ≤ ((R + 1) * L ^ (1 / 4 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) hc2_le 2
      rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hc4
      norm_num at hc4
      exact hc34.trans hc4
    have hL1_le : L + 1 ≤ 2 * L := by linarith only [hL1]
    have hu2_le : ‖u‖ ^ 2 ≤ 1170 ^ 2 / L ^ (63 / 32 : ℝ) := by
      have hp := pow_le_pow_left₀ (norm_nonneg u) hu_rpow 2
      rw [div_pow, ← Real.rpow_natCast (L ^ (63 / 64 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hp
      norm_num at hp; exact hp.trans_eq (by norm_num)
    have hCR_rpow : C_q * (R + 1) ^ 2 ≤ L ^ (2 / 64 : ℝ) := by
      have h1 : C_q * (R + 1) ≤ L ^ (1 / 64 : ℝ) := by
        linarith only [hL_rpow, hR, hC_q, hK_res,
          abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1)]
      calc C_q * (R + 1) ^ 2 = (C_q * (R + 1)) * (R + 1) := by ring
        _ ≤ L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ) := mul_le_mul h1 hR1_64 (by positivity) (by positivity)
        _ = L ^ (2 / 64 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
    calc C_q * c N ^ 3 * (L + 1) * ‖u‖ ^ 2
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
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          exact (by norm_num : (2 * 1170 ^ 2 : ℝ) ≤ (4 : ℝ) ^ (42 : ℝ)).trans hL_7_16
  exact (abs_quasimode_energy_sub_le hr_norm hv_norm hEq_sub hEq_vsq hEq_u hu_norm hEu_abs).trans_eq
    (by ring)

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
  dsimp only [Function.comp_def] at hrat_ub hNf hL_rpow hL_big
  set L := Real.log (N : ℝ)
  let q := primeAboveLowPacket N
  let Lc := linearDefectCutoff (c N)
  let M := N / Lc
  obtain ⟨hq_prime, hq_gt, hq_le⟩ := primeAboveLowPacket_spec N
  obtain ⟨hLc3, h4c, -, hLcup⟩ := linearDefectCutoff_bounds hcN
  have h4_le : (4 : ℝ) ^ (32 : ℝ) ≤ L := by linarith only [hL_big]
  have hL1 : 1 ≤ L := by linarith [Real.rpow_nonneg (zero_le_four (α := ℝ)) 32]
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
  have hR1_64 : R + 1 ≤ L ^ (1 / 64 : ℝ) := by
    linarith only [hL_rpow, hR, hC_q, hK_res, hC_sep, hlog2H_nn,
      abs_nonneg (completeWeilSelfFinitePart φ 1)]
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
  let K_M := (max 1 M₀_sep : ℝ) + (max 1 M₀_res : ℝ) + K_res + 4 * (Real.exp 1 + 3) ^ 2 + 100
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
  have hM_ge_L3 : (2 * (R + 1) * K_M) * L ^ 3 ≤ M := by
    have hdiv_ge : (4 * (R + 1) * K_M) * L ^ 3 ≤ (M : ℝ) + 1 := by
      have h1 : (4 * (R + 1) * K_M) * L ^ 3 * (H * L) ≤ N :=
        (by ring : _ = (4 * H * (R + 1) * K_M) * L ^ 4).trans_le hN_big_L4
      have h2 : ((M : ℝ) + 1) * Lc ≤ ((M : ℝ) + 1) * (H * L) :=
        mul_le_mul_of_nonneg_left hLc_le_HL (by positivity)
      exact le_of_mul_le_mul_right (h1.trans (hNLc_lt.le.trans h2)) (mul_pos hH_pos hL0)
    have h1_le : 1 ≤ (2 * (R + 1) * K_M) * L ^ 3 := by
      have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
      nlinarith [hR, hK_M_pos, hL3]
    linarith only [hdiv_ge, h1_le]
  have hM_sep : M₀_sep ≤ M := by
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    have hM0R : (M₀_sep : ℝ) ≤ M := by
      have hm : (M₀_sep : ℝ) ≤ (max 1 M₀_sep : ℝ) := by exact_mod_cast le_max_right 1 M₀_sep
      have hpos_rest : 0 ≤ (max 1 M₀_res : ℝ) + K_res + 4 * (Real.exp 1 + 3) ^ 2 + 100 := by
        positivity
      dsimp only [K_M] at hM_ge_L3
      nlinarith [hR, hL3, hm, hpos_rest, hM_ge_L3]
    exact_mod_cast hM0R
  have hM_res : M₀_res ≤ M := by
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    have hM0R : (M₀_res : ℝ) ≤ M := by
      have hm : (M₀_res : ℝ) ≤ (max 1 M₀_res : ℝ) := by exact_mod_cast le_max_right 1 M₀_res
      have hpos_rest : 0 ≤ (max 1 M₀_sep : ℝ) + K_res + 4 * (Real.exp 1 + 3) ^ 2 + 100 := by
        positivity
      dsimp only [K_M] at hM_ge_L3
      nlinarith [hR, hL3, hm, hpos_rest, hM_ge_L3]
    exact_mod_cast hM0R
  have hM2 : 2 ≤ M := by
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    have : (100 : ℝ) ≤ M := by nlinarith [hR, hK_M_pos, hL3, hM_ge_L3]
    exact_mod_cast (show (2 : ℝ) ≤ M by linarith)
  have hM1 : 1 ≤ M := by omega
  have hMN : M ≤ N := Nat.div_le_self N Lc
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  let L_M := Real.log (M : ℝ)
  have hLM_lower : L - Real.log (2 * H * L) ≤ L_M := by
    have hNM_le_2Lc : (N : ℝ) ≤ 2 * Lc * M := by
      have h2M : (M : ℝ) + 1 ≤ 2 * M := by
        have : (2 : ℝ) ≤ M := by exact_mod_cast hM2; linarith
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
      linarith only [hL_rpow, hR, hC_q, hK_res, hC_sep, abs_nonneg (completeWeilSelfFinitePart φ 1)]
    linarith only [hl2H, hlogL_64]
  have hLM_ge_half : L / 2 ≤ L_M := by
    have h65 : 65 * L ^ (1 / 64 : ℝ) ≤ L / 2 := by
      have h130 : (130 : ℝ) ≤ L ^ (63 / 64 : ℝ) :=
        (by norm_num : (130 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans
          (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
      have hm := mul_le_mul_of_nonneg_right h130 (Real.rpow_nonneg hL0.le (1 / 64 : ℝ))
      rw [← Real.rpow_add hL0] at hm; norm_num at hm; rw [Real.rpow_one] at hm
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
  let c' := c N * (M : ℝ) / N
  have hc'_lo : 1 / (512 * Real.exp 2) ≤ c' := by
    have h32M : (M : ℝ) + 1 ≤ (3 / 2 : ℝ) * M := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM2; linarith
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
  have hq_le_4rpow : (q : ℝ) ≤ 4 * L ^ (13 / 32 : ℝ) := by
    have hQ₁_le : (lowPacketCutoff N : ℝ) ≤ L ^ (13 / 32 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg hL0.le _)
    have h2_le_rpow : (2 : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
      have hp := Real.rpow_le_rpow (by positivity) h4_le (by norm_num : (0 : ℝ) ≤ 1 / 32)
      rw [← Real.rpow_mul (by norm_num)] at hp; norm_num at hp
      exact hp.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
    have hmax : ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) ≤ L ^ (13 / 32 : ℝ) := by
      rw [Nat.cast_max, Nat.cast_ofNat]; exact max_le h2_le_rpow hQ₁_le
    have hqc : (q : ℝ) ≤ 2 * ((max 2 (lowPacketCutoff N) : ℕ) : ℝ) := by exact_mod_cast hq_le
    linarith
  have hq_le_LM_half : (q : ℝ) ≤ L_M ^ (1 / 2 : ℝ) := by
    have h8_le : (8 : ℝ) ≤ L_M ^ (3 / 32 : ℝ) := by
      have hp := Real.rpow_le_rpow (by positivity) hLM_31 (by norm_num : (0 : ℝ) ≤ 3 / 32)
      rw [← Real.rpow_mul (by norm_num)] at hp
      exact (by norm_num : (8 : ℝ) ≤ (4 : ℝ) ^ (93 / 32 : ℝ)).trans hp
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
      Real.log_le_log (by exact_mod_cast hq_prime.pos) hq_le_LM
    have h1_64 : 1 ≤ L_M ^ (1 / 64 : ℝ) := Real.one_le_rpow hLM1 (by norm_num)
    linarith [Real.rpow_nonneg hLM0.le (1 / 64 : ℝ)]
  let v := normalizedRamanujanHorizonVector q N
  let u := (conductorSubspace (lowPacketCutoff N) N).starProjection v
  let z := lowPacketOrthogonalPrimeQuasimode N
  let p_z := horizonPrefixVector M z
  let p_v := horizonPrefixVector M v
  let p_u := horizonPrefixVector M u
  have hp_sub : p_z = p_v - p_u := by
    ext ⟨n, hn⟩
    change (if n ≤ M then primeHorizonExtension (v - u) n else 0) =
      (if n ≤ M then primeHorizonExtension v n else 0) -
      (if n ≤ M then primeHorizonExtension u n else 0)
    rw [primeHorizonExtension_coe (v - u) ⟨n, hn⟩, primeHorizonExtension_coe v ⟨n, hn⟩,
      primeHorizonExtension_coe u ⟨n, hn⟩, PiLp.sub_apply]
    split_ifs <;> ring
  have hvan_pv : ∀ n, M < n → primeHorizonExtension p_v n = 0 := fun n hn => by
    rw [primeHorizonExtension_horizonPrefixVector hMN v n, if_neg (Nat.not_le.mpr hn)]
  have hvan_pu : ∀ n, M < n → primeHorizonExtension p_u n = 0 := fun n hn => by
    rw [primeHorizonExtension_horizonPrefixVector hMN u n, if_neg (Nat.not_le.mpr hn)]
  let v' := normalizedRamanujanHorizonVector q M
  let α := Real.sqrt (L_M / L)
  have hα_nn : 0 ≤ α := Real.sqrt_nonneg _
  have hα_le1 : α ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hL0).mpr hLM_le_L)
  have hα_sq : α ^ 2 = L_M / L := Real.sq_sqrt (div_nonneg hLM0.le hL0.le)
  have hpv_eq : horizonProfileVector (primeHorizonExtension p_v) M = α • v' := by
    ext ⟨n, hn⟩
    have hnN : n ∈ Icc 1 N := mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hMN⟩
    change primeHorizonExtension p_v n = α * ((Real.sqrt L_M)⁻¹ * (normalizedRamanujanMode q n / Real.sqrt n))
    rw [primeHorizonExtension_horizonPrefixVector hMN v n, if_pos (mem_Icc.mp hn).2,
      primeHorizonExtension_coe v ⟨n, hnN⟩]
    change (Real.sqrt L)⁻¹ * (normalizedRamanujanMode q n / Real.sqrt n) = _
    dsimp only [α]
    rw [Real.sqrt_div hLM0.le]
    field_simp [(Real.sqrt_pos.mpr hLM0).ne', (Real.sqrt_pos.mpr hL0).ne']
  let p'_u := horizonProfileVector (primeHorizonExtension p_u) M
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
  have hsep_v' := hM₀_sep M hM_sep hq_prime hq_le_LM hc'_lo hc'_hi
  have hM_width1 : 4 * (Real.exp 1 + 3) ^ 2 * (1 : ℝ) ^ 2 ≤ M := by
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    dsimp only [K_M] at hM_ge_L3
    nlinarith [hR, hK_res, hL3, hM_ge_L3]
  let E1_q := completedConductorEnergy φ 1 q
  let r1 := Matrix.toEuclideanLin (completeWeilMatrix φ 1 M) v' - E1_q • v'
  have hr1_norm : ‖r1‖ ≤ 1 := by
    have hr0 := hM₀_res M hM_res q hq_prime.pos hq_le_LM_half 1 le_rfl hM_width1
    have hK_LM : K_res ≤ 2 * L_M ^ (1 / 64 : ℝ) := by
      have hKL1 : K_res ≤ L ^ (1 / 64 : ℝ) := by
        linarith only [hL_rpow, hR, hC_q, hC_sep, hlog2H_nn,
          abs_nonneg (completeWeilSelfFinitePart φ 1)]
      have hp := Real.rpow_le_rpow hL0.le (show L ≤ 2 * L_M by linarith only [hLM_ge_half])
        (by norm_num : (0 : ℝ) ≤ 1 / 64)
      rw [Real.mul_rpow zero_le_two hLM0.le] at hp
      have h2_64 : (2 : ℝ) ^ (1 / 64 : ℝ) ≤ 2 :=
        (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)).trans_eq (Real.rpow_one 2)
      exact hKL1.trans (hp.trans (mul_le_mul_of_nonneg_right h2_64 (by positivity)))
    have hLM_25 : (4 : ℝ) ^ (12 : ℝ) ≤ L_M ^ (25 / 64 : ℝ) := by
      have hp := Real.rpow_le_rpow (by positivity) hLM_31 (by norm_num : (0 : ℝ) ≤ 25 / 64)
      rw [← Real.rpow_mul (by norm_num)] at hp
      exact (by norm_num : (4 : ℝ) ^ (12 : ℝ) ≤ (4 : ℝ) ^ (775 / 64 : ℝ)).trans hp
    have ht1 : K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
        ((1 : ℝ) ^ 2 * (1 + Real.log (1 : ℝ)) ^ 3 * L_M ^ (1 / (16 : ℝ)) / L_M) ≤ 1 / 2 := by
      rw [Real.log_one]
      have hp2 : (1 + Real.log q) ^ 2 ≤ 65 ^ 2 * L_M ^ (2 / 64 : ℝ) := by
        have hp := pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg q]) hlogq_LM 2
        rw [mul_pow, ← Real.rpow_natCast (L_M ^ (1 / 64 : ℝ)) 2, ← Real.rpow_mul hLM0.le] at hp
        norm_num at hp; exact hp
      calc K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
            ((1 : ℝ) ^ 2 * (1 + 0) ^ 3 * L_M ^ (1 / 16 : ℝ) / L_M)
          ≤ (2 * L_M ^ (1 / 64 : ℝ)) * (L_M ^ (1 / 2 : ℝ) * (65 ^ 2 * L_M ^ (2 / 64 : ℝ))) *
            (L_M ^ (1 / 16 : ℝ) / L_M) :=
            mul_le_mul
              (mul_le_mul hK_LM (mul_le_mul hq_le_LM_half hp2 (by positivity) (by positivity))
                (by positivity) (by positivity))
              (le_of_eq (by ring)) (by positivity) (by positivity)
        _ = (2 * 65 ^ 2) *
            (L_M ^ (1 / 64 : ℝ) * L_M ^ (1 / 2 : ℝ) * L_M ^ (2 / 64 : ℝ) *
              L_M ^ (1 / 16 : ℝ) / L_M) := by ring
        _ = (2 * 65 ^ 2) / L_M ^ (25 / 64 : ℝ) := by
            rw [← Real.rpow_add hLM0, ← Real.rpow_add hLM0, ← Real.rpow_add hLM0,
              ← Real.rpow_sub_one hLM0.ne']
            have hexp : (1 / 64 + 1 / 2 + 2 / 64 + 1 / 16 - 1 : ℝ) = -(25 / 64) := by norm_num
            rw [hexp, Real.rpow_neg hLM0.le, div_eq_mul_inv]
        _ ≤ 1 / 2 := by
            rw [div_le_iff₀ (Real.rpow_pos_of_pos hLM0 _)]
            have hnum : (2 * 65 ^ 2 : ℝ) ≤ (1 / 2 : ℝ) * (4 : ℝ) ^ (12 : ℝ) := by norm_num
            nlinarith only [hnum, hLM_25]
    have ht2 : K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) * ((1 : ℝ) ^ 10 * (L_M / M) ^ 2) ≤ 1 / 2 := by
      have hq_log_LM3 : (q : ℝ) * (1 + Real.log q) ^ 2 ≤ L_M ^ 3 := by
        have hlq_LM1 : 1 + Real.log q ≤ L_M := by
          have h65_LM : 65 * L_M ^ (1 / 64 : ℝ) ≤ L_M := by
            have h65 : (65 : ℝ) ≤ L_M ^ (63 / 64 : ℝ) :=
              (by norm_num : (65 : ℝ) ≤ (4 : ℝ) ^ (12 : ℝ)).trans
                (hLM_25.trans (Real.rpow_le_rpow_of_exponent_le hLM1 (by norm_num)))
            have hm := mul_le_mul_of_nonneg_right h65 (Real.rpow_nonneg hLM0.le (1 / 64 : ℝ))
            rw [← Real.rpow_add hLM0] at hm; norm_num at hm; rwa [Real.rpow_one] at hm
          exact hlogq_LM.trans h65_LM
        have hp2 : (1 + Real.log q) ^ 2 ≤ L_M ^ 2 :=
          pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg q]) hlq_LM1 2
        calc (q : ℝ) * (1 + Real.log q) ^ 2 ≤ L_M * L_M ^ 2 :=
              mul_le_mul hq_le_LM hp2 (by positivity) hLM0.le
          _ = L_M ^ 3 := by ring
      have hM_ge_2K : 2 * K_res * L ^ 3 ≤ M := by
        dsimp only [K_M] at hM_ge_L3
        have hpos_rest : 0 ≤ (max 1 M₀_sep : ℝ) + (max 1 M₀_res : ℝ) +
          4 * (Real.exp 1 + 3) ^ 2 + 100 := by positivity
        nlinarith [hR, hK_res, pow_pos hL0 3, hpos_rest, hM_ge_L3]
      have hLM_M_le : L_M ^ 3 / M ≤ 1 / (2 * K_res) := by
        rw [div_le_div_iff₀ hM0 (by positivity)]
        have hLM3_L3 : L_M ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hLM0.le hLM_le_L 3
        nlinarith only [hLM3_L3, hM_ge_2K, hK_res]
      have hLM2_M : L_M ^ 2 / M ≤ 1 := by
        have h23 : L_M ^ 2 ≤ L_M ^ 3 := pow_le_pow_right₀ hLM1 (by omega)
        have hM_ge_L3_1 : L ^ 3 ≤ M := by nlinarith [hR, hK_M_pos, pow_pos hL0 3, hM_ge_L3]
        rw [div_le_one hM0]
        exact h23.trans ((pow_le_pow_left₀ hLM0.le hLM_le_L 3).trans hM_ge_L3_1)
      calc K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) * ((1 : ℝ) ^ 10 * (L_M / M) ^ 2)
          ≤ K_res * L_M ^ 3 * (L_M ^ 2 / M ^ 2) := by
            rw [one_pow, one_mul, div_pow]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq_log_LM3 hK_res.le)
              (by positivity)
        _ = K_res * (L_M ^ 3 / M) * (L_M ^ 2 / M) := by field_simp [hM0.ne']; ring
        _ ≤ K_res * (1 / (2 * K_res)) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hLM_M_le hK_res.le) hLM2_M
              (by positivity) (by positivity)
        _ = 1 / 2 := by field_simp [hK_res.ne']
    have hr1_sq : ‖r1‖ ^ 2 ≤ 1 := by
      have hr0' : ‖r1‖ ^ 2 ≤ K_res * ((q : ℝ) * (1 + Real.log q) ^ 2) *
          ((1 : ℝ) ^ 2 * (1 + Real.log (1 : ℝ)) ^ 3 * L_M ^ (1 / (16 : ℝ)) / L_M +
            (1 : ℝ) ^ 10 * (L_M / M) ^ 2) := by
        simpa only [Nat.cast_ofNat] using hr0
      rw [mul_add] at hr0'
      linarith only [hr0', ht1, ht2]
    nlinarith only [hr1_sq, norm_nonneg r1]
  have hqqM : q * q ≤ M := by
    have hq2_LM : ((q * q : ℕ) : ℝ) ≤ L_M := by
      rw [Nat.cast_mul]
      calc (q : ℝ) * q ≤ L_M ^ (1 / 2 : ℝ) * L_M ^ (1 / 2 : ℝ) :=
            mul_le_mul hq_le_LM_half hq_le_LM_half (by positivity) (by positivity)
        _ = L_M := by rw [← Real.rpow_add hLM0]; norm_num; exact Real.rpow_one _
    have hLM_le_M : L_M ≤ M := by
      have hL_L3 : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num)
      have hL3_M : L ^ 3 ≤ M := by nlinarith [hR, hK_M_pos, pow_pos hL0 3, hM_ge_L3]
      exact hLM_le_L.trans (hL_L3.trans hL3_M)
    exact_mod_cast hq2_LM.trans hLM_le_M
  have hv'_rpow : |‖v'‖ ^ 2 - 1| ≤ 8 / L_M ^ (1 / 2 : ℝ) := by
    have hv0 := abs_norm_normalizedRamanujanHorizonVector_sq_sub_one_le hq_prime.two_le hqqM
    have h1_64 : 1 ≤ L_M ^ (1 / 64 : ℝ) := Real.one_le_rpow hLM1 (by norm_num)
    have hnum1 : 2 * Real.log (q : ℝ) + 9 ≤ 137 * L_M ^ (1 / 64 : ℝ) := by
      linarith only [hlogq_LM, h1_64]
    have h137_8 : 137 * L_M ^ (1 / 64 : ℝ) ≤ 8 * L_M ^ (1 / 2 : ℝ) := by
      have hp := Real.rpow_le_rpow (by positivity) hLM_31 (by norm_num : (0 : ℝ) ≤ 31 / 64)
      rw [← Real.rpow_mul (by norm_num)] at hp
      have h137 : (137 / 8 : ℝ) ≤ L_M ^ (31 / 64 : ℝ) :=
        (by norm_num : (137 / 8 : ℝ) ≤ (4 : ℝ) ^ (961 / 64 : ℝ)).trans hp
      have hm := mul_le_mul_of_nonneg_right h137 (Real.rpow_nonneg hLM0.le (1 / 64 : ℝ))
      rw [← Real.rpow_add hLM0] at hm; norm_num at hm
      linarith only [hm]
    calc |‖v'‖ ^ 2 - 1| ≤ (2 * Real.log (q : ℝ) + 9) / L_M := hv0
      _ ≤ 8 * L_M ^ (1 / 2 : ℝ) / L_M :=
          div_le_div_of_nonneg_right (hnum1.trans h137_8) hLM0.le
      _ = 8 / L_M ^ (1 / 2 : ℝ) := by
          rw [mul_div_assoc, ← Real.rpow_sub_one hLM0.ne']
          have hexp : (1 / 2 - 1 : ℝ) = -(1 / 2) := by norm_num
          rw [hexp, Real.rpow_neg hLM0.le, div_eq_mul_inv]
  have hv'_norm_le2 : ‖v'‖ ≤ 2 := by
    have h8q : 8 / L_M ^ (1 / 2 : ℝ) ≤ 1 := by
      rw [div_le_one (Real.rpow_pos_of_pos hLM0 _)]
      have hp := Real.rpow_le_rpow (by positivity) hLM_31 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [← Real.rpow_mul (by norm_num)] at hp
      exact (by norm_num : (8 : ℝ) ≤ (4 : ℝ) ^ (31 / 2 : ℝ)).trans hp
    have := (abs_le.mp hv'_rpow).2
    nlinarith only [this, h8q, norm_nonneg v']
  have hE1_sub : |E1_q - Real.log q| ≤ |completeWeilSelfFinitePart φ 1| + 3 := by
    have h1_lt_q : (1 : ℝ) < q := by exact_mod_cast hq_prime.one_lt
    have hsh1 : |shellCorrection φ 1 q| ≤ 2 := by
      have h := abs_shellCorrection_prime_of_gt hφ hsupp hM_int le_rfl hq_prime h1_lt_q
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq_prime.two_le
      refine h.trans ?_
      rw [one_pow, mul_one, div_le_iff₀ (by linarith)]
      linarith
    have hEq_f : E1_q = completeWeilSelfFinitePart φ 1 + Real.log q +
        ArithmeticIntersectionTheory.tameDifferent q - shellCorrection φ 1 q := by
      dsimp only [E1_q]
      rw [completedConductorEnergy_eq_sub_shellCorrection zero_lt_one hq_prime.pos]
      unfold completeWeilAdjunctionEnergy ramanujanAdjunctionEnergy
      rw [if_neg hq_prime.ne_one]; ring
    have htame := tameDifferent_prime_le_one hq_prime
    rw [show E1_q - Real.log q = completeWeilSelfFinitePart φ 1 +
      ArithmeticIntersectionTheory.tameDifferent q - shellCorrection φ 1 q by rw [hEq_f]; ring]
    have t1 := abs_sub (completeWeilSelfFinitePart φ 1 + ArithmeticIntersectionTheory.tameDifferent q)
      (shellCorrection φ 1 q)
    have t2 := abs_add_le (completeWeilSelfFinitePart φ 1) (ArithmeticIntersectionTheory.tameDifferent q)
    linarith only [t1, t2, htame, hsh1]
  have hE1_rpow : |E1_q| ≤ 2 * L ^ (2 / 64 : ℝ) := by
    have htri : |E1_q| ≤ |E1_q - Real.log q| + Real.log q := by
      have := abs_add_le (E1_q - Real.log q) (Real.log q)
      rwa [sub_add_cancel, abs_of_nonneg (Real.log_natCast_nonneg q)] at this
    have hlq_64 : Real.log (q : ℝ) ≤ 64 * L ^ (1 / 64 : ℝ) :=
      (Real.log_le_log (by exact_mod_cast hq_prime.pos) (hq_le_LM.trans hLM_le_L)).trans hlogL_64
    have hS1 : |completeWeilSelfFinitePart φ 1| + 4 ≤ (1 / 72 : ℝ) * L ^ (1 / 64 : ℝ) := by
      linarith only [hL_rpow, hR, hC_q, hK_res, hC_sep, hlog2H_nn]
    have h1_64 : 1 ≤ L ^ (1 / 64 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    calc |E1_q| ≤ (|completeWeilSelfFinitePart φ 1| + 4) * (65 * L ^ (1 / 64 : ℝ)) := by
          have := mul_le_mul_of_nonneg_left h1_64
            (show 0 ≤ |completeWeilSelfFinitePart φ 1| + 3 by positivity)
          nlinarith only [htri, hE1_sub, hlq_64, this, h1_64,
            abs_nonneg (completeWeilSelfFinitePart φ 1)]
      _ ≤ ((1 / 72 : ℝ) * L ^ (1 / 64 : ℝ)) * (65 * L ^ (1 / 64 : ℝ)) :=
          mul_le_mul_of_nonneg_right hS1 (by positivity)
      _ ≤ 2 * (L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ)) := by
          have : (65 / 72 : ℝ) ≤ 2 := by norm_num
          nlinarith [Real.rpow_nonneg hL0.le (1 / 64 : ℝ)]
      _ = 2 * L ^ (2 / 64 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  have hrc'_norm : ‖Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' - E1_q • v'‖ ≤ C_sep + 1 := by
    rw [show Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' - E1_q • v' =
      (Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' -
        Matrix.toEuclideanLin (completeWeilMatrix φ 1 M) v') + r1 by dsimp only [r1]; abel]
    exact (norm_add_le _ _).trans (add_le_add hsep_v' hr1_norm)
  have hE1_v'_sq : |α ^ 2 * (E1_q * (‖v'‖ ^ 2 - 1))| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg α), abs_mul]
    have hα2_1 : α ^ 2 ≤ 1 := by nlinarith only [hα_nn, hα_le1]
    have hLM_half_L : L ^ (1 / 2 : ℝ) / 2 ≤ L_M ^ (1 / 2 : ℝ) := by
      have hp := Real.rpow_le_rpow (by positivity) hLM_ge_half (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [Real.div_rpow hL0.le zero_le_two] at hp
      have h2_half : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 :=
        (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)).trans_eq (Real.rpow_one 2)
      exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hL0.le _)
        (Real.rpow_pos_of_pos zero_lt_two _) h2_half).trans hp
    have hv'_L : |‖v'‖ ^ 2 - 1| ≤ 16 / L ^ (1 / 2 : ℝ) :=
      hv'_rpow.trans ((div_le_div_of_nonneg_left (by norm_num)
        (div_pos (Real.rpow_pos_of_pos hL0 _) zero_lt_two) hLM_half_L).trans_eq (by ring))
    have hprod : |E1_q| * |‖v'‖ ^ 2 - 1| ≤ 1 := by
      calc |E1_q| * |‖v'‖ ^ 2 - 1|
          ≤ (2 * L ^ (2 / 64 : ℝ)) * (16 / L ^ (1 / 2 : ℝ)) :=
            mul_le_mul hE1_rpow hv'_L (abs_nonneg _) (by positivity)
        _ = 32 / L ^ (15 / 32 : ℝ) := by
            rw [show 2 * L ^ (2 / 64 : ℝ) * (16 / L ^ (1 / 2 : ℝ)) =
              32 * (L ^ (2 / 64 : ℝ) / L ^ (1 / 2 : ℝ)) by ring, ← Real.rpow_sub hL0]
            have hexp : (2 / 64 - 1 / 2 : ℝ) = -(15 / 32) := by norm_num
            rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
        _ ≤ 1 := by
            rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
            exact (by norm_num : (32 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans
              (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
    nlinarith only [hα2_1, hprod, sq_nonneg α, mul_nonneg (abs_nonneg E1_q) (abs_nonneg (‖v'‖ ^ 2 - 1))]
  have hα_sub1 : |(α ^ 2 - 1) * E1_q| ≤ 1 := by
    rw [abs_mul, hα_sq]
    have hdiff_le : |L_M / L - 1| ≤ 65 / L ^ (63 / 64 : ℝ) := by
      have hle0 : L_M / L - 1 ≤ 0 := by have := (div_le_one hL0).mpr hLM_le_L; linarith
      rw [abs_of_nonpos hle0]
      have hge : 1 - L_M / L ≤ 65 * L ^ (1 / 64 : ℝ) / L := by
        rw [show 1 - L_M / L = (L - L_M) / L by field_simp [hL0.ne']]
        exact div_le_div_of_nonneg_right (by linarith only [hLM_lower, h2HL_rpow]) hL0.le
      refine (by linarith only [hge] : -(L_M / L - 1) ≤ 65 * L ^ (1 / 64 : ℝ) / L).trans_eq ?_
      rw [mul_div_assoc, ← Real.rpow_sub_one hL0.ne']
      have hexp : (1 / 64 - 1 : ℝ) = -(63 / 64) := by norm_num
      rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
    calc |L_M / L - 1| * |E1_q|
        ≤ (65 / L ^ (63 / 64 : ℝ)) * (2 * L ^ (2 / 64 : ℝ)) :=
          mul_le_mul hdiff_le hE1_rpow (abs_nonneg _) (by positivity)
      _ = 130 / L ^ (61 / 64 : ℝ) := by
          rw [show (65 / L ^ (63 / 64 : ℝ)) * (2 * L ^ (2 / 64 : ℝ)) =
            130 * (L ^ (2 / 64 : ℝ) / L ^ (63 / 64 : ℝ)) by ring, ← Real.rpow_sub hL0]
          have hexp : (2 / 64 - 63 / 64 : ℝ) = -(61 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          exact (by norm_num : (130 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans
            (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
  have hu_rpow : ‖u‖ ≤ 1170 / L ^ (63 / 64 : ℝ) := by
    have h1q : 1 + Real.log q ≤ 65 * L ^ (1 / 64 : ℝ) := by
      have hlq : Real.log (q : ℝ) ≤ Real.log L :=
        Real.log_le_log (by exact_mod_cast hq_prime.pos) (hq_le_LM.trans hLM_le_L)
      have h1_64 : 1 ≤ L ^ (1 / 64 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith only [hlq, hlogL_64, h1_64]
    calc ‖u‖ ≤ 18 * (1 + Real.log q) / L := hu_bd
      _ ≤ 18 * (65 * L ^ (1 / 64 : ℝ)) / L :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1q (by norm_num)) hL0.le
      _ = 1170 / L ^ (63 / 64 : ℝ) := by
          rw [show 18 * (65 * L ^ (1 / 64 : ℝ)) / L = 1170 * (L ^ (1 / 64 : ℝ) / L) by ring,
            ← Real.rpow_sub_one hL0.ne']
          have hexp : (1 / 64 - 1 : ℝ) = -(63 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
  have hBv'_u : 2 * ‖Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v'‖ * ‖p'_u‖ ≤ 2 := by
    let rc' := Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' - E1_q • v'
    have hBv' : Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v' = E1_q • v' + rc' := by
      dsimp only [rc']; abel
    have hBv'_norm : ‖Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v'‖ ≤
        6 * L ^ (2 / 64 : ℝ) := by
      rw [hBv']
      have h1 : ‖E1_q • v'‖ ≤ 4 * L ^ (2 / 64 : ℝ) := by
        rw [norm_smul, Real.norm_eq_abs]
        calc |E1_q| * ‖v'‖ ≤ (2 * L ^ (2 / 64 : ℝ)) * 2 :=
              mul_le_mul hE1_rpow hv'_norm_le2 (norm_nonneg _) (by positivity)
          _ = 4 * L ^ (2 / 64 : ℝ) := by ring
      have h2 : C_sep + 1 ≤ 2 * L ^ (2 / 64 : ℝ) := by
        have hCs : C_sep + 1 ≤ L ^ (1 / 64 : ℝ) := by
          linarith only [hL_rpow, hR, hC_q, hK_res, hlog2H_nn,
            abs_nonneg (completeWeilSelfFinitePart φ 1)]
        have h12 : L ^ (1 / 64 : ℝ) ≤ L ^ (2 / 64 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        linarith [Real.rpow_nonneg hL0.le (2 / 64 : ℝ)]
      exact (norm_add_le _ _).trans (add_le_add h1 (hrc'_norm.trans h2) |>.trans_eq (by ring))
    calc 2 * ‖Matrix.toEuclideanLin (completeWeilMatrix φ c' M) v'‖ * ‖p'_u‖
        ≤ 2 * (6 * L ^ (2 / 64 : ℝ)) * (1170 / L ^ (63 / 64 : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hBv'_norm zero_le_two)
            (hp'u_norm.trans hu_rpow) (norm_nonneg _) (by positivity)
      _ = 14040 / L ^ (61 / 64 : ℝ) := by
          rw [show 2 * (6 * L ^ (2 / 64 : ℝ)) * (1170 / L ^ (63 / 64 : ℝ)) =
            14040 * (L ^ (2 / 64 : ℝ) / L ^ (63 / 64 : ℝ)) by ring, ← Real.rpow_sub hL0]
          have hexp : (2 / 64 - 63 / 64 : ℝ) = -(61 / 64) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
      _ ≤ 2 := by
          have h1 : 14040 / L ^ (61 / 64 : ℝ) ≤ 1 := by
            rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
            exact (by norm_num : (14040 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans
              (hL_7_16.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)))
          linarith
  have hEpu_abs : |completeWeilEnergy φ (c N) N p_u| ≤ 1 := by
    have hg := (hglobN hcN hc_le_L).1 p_u
    refine hg.trans ?_
    have hc3_le : c N ^ 3 ≤ (R + 1) ^ 2 * L ^ (1 / 2 : ℝ) := by
      have hc34 : c N ^ 3 ≤ (c N ^ 2) ^ 2 := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hcN (by omega)
      have hc4 : (c N ^ 2) ^ 2 ≤ ((R + 1) * L ^ (1 / 4 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) hc2_le 2
      rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hc4
      norm_num at hc4
      exact hc34.trans hc4
    have hL1_le : L + 1 ≤ 2 * L := by linarith only [hL1]
    have hpu2_le : ‖p_u‖ ^ 2 ≤ 1170 ^ 2 / L ^ (63 / 32 : ℝ) := by
      have hp := pow_le_pow_left₀ (norm_nonneg p_u)
        ((norm_horizonPrefixVector_le M u).trans hu_rpow) 2
      rw [div_pow, ← Real.rpow_natCast (L ^ (63 / 64 : ℝ)) 2, ← Real.rpow_mul hL0.le] at hp
      norm_num at hp; exact hp.trans_eq (by norm_num)
    have hCR_rpow : C_q * (R + 1) ^ 2 ≤ L ^ (2 / 64 : ℝ) := by
      have h1 : C_q * (R + 1) ≤ L ^ (1 / 64 : ℝ) := by
        linarith only [hL_rpow, hR, hC_q, hK_res, hC_sep, hlog2H_nn,
          abs_nonneg (completeWeilSelfFinitePart φ 1)]
      calc C_q * (R + 1) ^ 2 = (C_q * (R + 1)) * (R + 1) := by ring
        _ ≤ L ^ (1 / 64 : ℝ) * L ^ (1 / 64 : ℝ) := mul_le_mul h1 hR1_64 (by positivity) (by positivity)
        _ = L ^ (2 / 64 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
    calc C_q * c N ^ 3 * (L + 1) * ‖p_u‖ ^ 2
        ≤ C_q * ((R + 1) ^ 2 * L ^ (1 / 2 : ℝ)) * (2 * L) * (1170 ^ 2 / L ^ (63 / 32 : ℝ)) :=
          mul_le_mul
            (mul_le_mul (mul_le_mul_of_nonneg_left hc3_le hC_q.le) hL1_le
              (by positivity) (by positivity))
            hpu2_le (sq_nonneg _) (by positivity)
      _ = (2 * 1170 ^ 2) * (C_q * (R + 1) ^ 2) * (L ^ (1 / 2 : ℝ) * L / L ^ (63 / 32 : ℝ)) := by ring
      _ ≤ (2 * 1170 ^ 2) * L ^ (2 / 64 : ℝ) * (L ^ (1 / 2 : ℝ) * L / L ^ (63 / 32 : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hCR_rpow (by norm_num)) (by positivity)
      _ = (2 * 1170 ^ 2) / L ^ (7 / 16 : ℝ) := by
          rw [show (2 * 1170 ^ 2 : ℝ) * L ^ (2 / 64 : ℝ) * (L ^ (1 / 2 : ℝ) * L / L ^ (63 / 32 : ℝ)) =
            (2 * 1170 ^ 2) * (L ^ (2 / 64 : ℝ) * L ^ (1 / 2 : ℝ) * L / L ^ (63 / 32 : ℝ)) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_add_one hL0.ne', ← Real.rpow_sub hL0]
          have hexp : (2 / 64 + 1 / 2 + 1 - 63 / 32 : ℝ) = -(7 / 16) := by norm_num
          rw [hexp, Real.rpow_neg hL0.le, div_eq_mul_inv]
      _ ≤ 1 := by
          rw [div_le_one (Real.rpow_pos_of_pos hL0 _)]
          exact (by norm_num : (2 * 1170 ^ 2 : ℝ) ≤ (4 : ℝ) ^ (14 : ℝ)).trans hL_7_16
  exact (abs_prefix_quasimode_energy_sub_le hφ hsupp hM_int hc0 hM1 hMN hC_sep.le hp_sub hvan_pv
    hvan_pu hpv_eq hα_nn hα_le1 hrc'_norm hv'_norm_le2 hE1_sub hα_sub1 hE1_v'_sq hBv'_u hEpu_abs).trans_eq
    (by ring)



end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
