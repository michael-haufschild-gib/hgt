import GaloisForLFunctions.RHTower.WeilMarkovPrimitiveHyperplane
import GaloisForLFunctions.RHTower.EulerMaclaurinCountertermQuadratureAndOneSidedPBAP
import GaloisForLFunctions.RHTower.CCMRiemannKernelBartaSources
import GaloisForLFunctions.RHTower.RiemannKernelGroundStateZeroIdentity
import GaloisForLFunctions.RHTower.WeilShiftPairLandau
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# Prime atoms and pole in the Φ ground-state coordinates

These identities are unconditional. They retain each von Mangoldt atom separately. The
archimedean-plus-prime ground-state cancellation is not asserted here.
-/

open MeasureTheory
open Complex
open Zeta23

namespace RHTower

noncomputable section

def phiDoobTest (v : ℝ → ℝ) (x : ℝ) : ℝ := riemannKernelReal x * v x

def phiDoobCoshMass (v : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, phiDoobTest v x * Real.cosh (x / 2)

def phiDoobSinhMass (v : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, phiDoobTest v x * Real.sinh (x / 2)

theorem contDiff_phiDoobTest {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 2 (phiDoobTest v) :=
  contDiff_riemannKernelReal.mul hv

theorem hasCompactSupport_phiDoobTest {v : ℝ → ℝ} (hv : HasCompactSupport v) :
    HasCompactSupport (phiDoobTest v) :=
  hv.mul_left

theorem phiDoobTest_odd {v : ℝ → ℝ} (hv : ∀ x, v (-x) = -v x) (x : ℝ) :
    phiDoobTest v (-x) = -phiDoobTest v x := by
  simp only [phiDoobTest, riemannKernelReal, abs_neg, hv x]
  ring

/-- Φ is in the left radical of the *zero-side* Weil form, unconditionally. -/
theorem W_riemannPhiKernel_left (g : ℝ → ℂ) :
    zetaZeroConfig.W riemannPhiKernel g = 0 := by
  unfold ZeroConfig.W
  have hterm (ρ : zetaZeroConfig.carrier) :
      zetaZeroConfig.Wsummand riemannPhiKernel g ρ = 0 := by
    unfold ZeroConfig.Wsummand
    rw [(paperFT_riemannPhiKernel_gammaOf ρ).1]
    ring
  have heq : (fun ρ : zetaZeroConfig.carrier =>
      zetaZeroConfig.Wsummand riemannPhiKernel g ρ) = fun _ => 0 := funext hterm
  rw [heq]
  simp

/-- The right polar exponential moment of Φ has mass `1/2`. -/
theorem integral_riemannKernelReal_exp_half :
    (∫ x : ℝ, riemannKernelReal x * Real.exp (x / 2)) = 1 / 2 := by
  have hξ : riemannPhiTransform 1 = (1 / 2 : ℂ) := by
    rw [riemannPhiTransform_eq_xi, xi_one]
  have hcast : ((∫ x : ℝ, riemannKernelReal x * Real.exp (x / 2) : ℝ) : ℂ) =
      riemannPhiTransform 1 := by
    rw [← integral_complex_ofReal]
    unfold riemannPhiTransform
    congr 1
    funext x
    rw [riemannPhiKernel_eq_ofReal]
    have he : Complex.exp (((1 : ℂ) - 1 / 2) * (x : ℂ)) =
        (Real.exp (x / 2) : ℂ) := by
      rw [show ((1 : ℂ) - 1 / 2) * (x : ℂ) = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_exp]
    rw [he]
    push_cast
    ring
  have h := hcast.trans hξ
  exact Complex.ofReal_injective (by simpa using h)

theorem integrable_riemannKernelReal_mul_exp (c : ℝ) :
    Integrable (fun x : ℝ => riemannKernelReal x * Real.exp (c * x)) := by
  have h := RiemannKernelGroundState.integrable_cexp_mul_riemannPhiKernel
    (((c + 1 / 2 : ℝ) : ℂ))
  refine h.re.congr (Filter.Eventually.of_forall fun x => ?_)
  have he : Complex.exp (((((c + 1 / 2 : ℝ) : ℂ)) - 1 / 2) * (x : ℂ)) =
      (Real.exp (c * x) : ℂ) := by
    rw [show (((((c + 1 / 2 : ℝ) : ℂ)) - 1 / 2) * (x : ℂ)) =
      (((c * x : ℝ) : ℂ)) by push_cast; ring, Complex.ofReal_exp]
  dsimp only
  rw [he, riemannPhiKernel_eq_ofReal, ← Complex.ofReal_mul]
  change Real.exp (c * x) * riemannKernelReal x = _
  ring

/-- The symmetric Φ-weighted mass is exactly `1/2`. -/
theorem integral_riemannKernelReal_cosh_half :
    (∫ x : ℝ, riemannKernelReal x * Real.cosh (x / 2)) = 1 / 2 := by
  have hplus : Integrable (fun x : ℝ => riemannKernelReal x * Real.exp (x / 2)) := by
    convert integrable_riemannKernelReal_mul_exp (1 / 2) using 1; ring
  have hminus : Integrable (fun x : ℝ => riemannKernelReal x * Real.exp (-(x / 2))) := by
    convert integrable_riemannKernelReal_mul_exp (-(1 / 2)) using 1; ring
  have heven : ∀ x, riemannKernelReal (-x) = riemannKernelReal x := by
    intro x
    simp [riemannKernelReal]
  calc
    (∫ x : ℝ, riemannKernelReal x * Real.cosh (x / 2)) =
        ∫ x : ℝ, (riemannKernelReal x * Real.exp (x / 2) +
          riemannKernelReal x * Real.exp (-(x / 2))) / 2 := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [Real.cosh_eq]
          ring
    _ = ((∫ x : ℝ, riemannKernelReal x * Real.exp (x / 2)) +
          (∫ x : ℝ, riemannKernelReal x * Real.exp (-(x / 2)))) / 2 := by
          rw [integral_div, integral_add hplus hminus]
    _ = 1 / 2 := by
          rw [← integral_mul_exp_half_of_even heven, integral_riemannKernelReal_exp_half]
          ring

theorem phiDoobCoshMass_eq_zero_of_odd {v : ℝ → ℝ}
    (hv : ∀ x, v (-x) = -v x) : phiDoobCoshMass v = 0 :=
  coshHalfMoment_eq_zero_of_odd (phiDoobTest_odd hv)

/-- The exact pole, including both hyperbolic moments, for `f = Φv`. -/
theorem phiDoob_pole {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    (weilPoleTerm (EF.weilTest (fun x => (phiDoobTest v x : ℂ))
      (fun x => (phiDoobTest v x : ℂ)))).re =
      2 * phiDoobCoshMass v ^ 2 - 2 * phiDoobSinhMass v ^ 2 := by
  have hf : Continuous (phiDoobTest v) := continuous_riemannKernelReal.mul hv
  simpa only [coshHalfMoment, sinhHalfMoment, phiDoobCoshMass, phiDoobSinhMass] using
    re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hf
      (hasCompactSupport_phiDoobTest hvc)

/-- On odd `v`, the pole is the negative sinh-moment square. -/
theorem phiDoob_pole_odd {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) :
    (weilPoleTerm (EF.weilTest (fun x => (phiDoobTest v x : ℂ))
      (fun x => (phiDoobTest v x : ℂ)))).re =
      -2 * phiDoobSinhMass v ^ 2 := by
  rw [phiDoob_pole hv hvc, phiDoobCoshMass_eq_zero_of_odd hodd]
  ring

/-- Odd Markov/Weil comparison in Φ coordinates, retaining pole sign. -/
theorem phiDoob_markov_eq_W_add_odd_sinh_sq {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      (zetaZeroConfig.W (fun x => (phiDoobTest v x : ℂ))
        (fun x => (phiDoobTest v x : ℂ))).re +
      2 * phiDoobSinhMass v ^ 2 := by
  have hf : ContDiff ℝ 2 (fun x => (phiDoobTest v x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_phiDoobTest hv)
  have hfc : HasCompactSupport (fun x => (phiDoobTest v x : ℂ)) :=
    (hasCompactSupport_phiDoobTest hvc).comp_left Complex.ofReal_zero
  rw [markovEnergy_eq_W_sub hf hfc, phiDoob_pole_odd hv.continuous hvc hodd]
  ring

/-- The exact arithmetic form for `Φv`, before its ground-state cancellation. -/
theorem phiDoob_markov_eq_levy_sub_prime {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      EF.gammaBracket 0 * (∫ x : ℝ, phiDoobTest v x ^ 2) +
        (NonnegativeCone.jumpEnergy (phiDoobTest v)).toReal -
        primeBlindCounterterm (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (realWeilTestFn (phiDoobTest v) (contDiff_phiDoobTest hv)
            (hasCompactSupport_phiDoobTest hvc)) :=
  markovEnergy_real_eq_levy_sub_counterterm (contDiff_phiDoobTest hv)
    (hasCompactSupport_phiDoobTest hvc)

/-- Ground-state jump algebra at any shift. The two diagonal terms are retained. -/
theorem phiDoob_jump_shift_identity (v : ℝ → ℝ) (t x : ℝ) :
    (phiDoobTest v x - phiDoobTest v (x + t)) ^ 2 =
      riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) ^ 2 +
      riemannKernelReal x * (riemannKernelReal x - riemannKernelReal (x + t)) * v x ^ 2 +
      riemannKernelReal (x + t) * (riemannKernelReal (x + t) - riemannKernelReal x) *
        v (x + t) ^ 2 := by
  unfold phiDoobTest
  ring

/-- A single prime atom's full Φ-weighted difference square. -/
def phiDoobPrimeJump (v : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n) *
    (v x - v (x + Real.log n)) ^ 2

def phiDoobPrimeDiagonal (v : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n) *
    (v x ^ 2 + v (x + Real.log n) ^ 2)

def phiDoobPrimeCross (v : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  2 * vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n) *
    v x * v (x + Real.log n)

/-- Atomwise Doob expansion; no prime cross-term is dropped. -/
theorem phiDoobPrimeJump_eq_diagonal_sub_cross (v : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    phiDoobPrimeJump v n x =
      phiDoobPrimeDiagonal v n x - phiDoobPrimeCross v n x := by
  unfold phiDoobPrimeJump phiDoobPrimeDiagonal phiDoobPrimeCross
  ring

theorem vonMangoldtAtom_nonneg (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_refl 0

theorem phiDoobPrimeJump_nonneg (v : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ phiDoobPrimeJump v n x := by
  unfold phiDoobPrimeJump
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos x).le)
      (riemannKernelReal_pos (x + Real.log n)).le)
    (sq_nonneg _)

/-- Every finite set of prime atoms retains its cross-term exactly. -/
theorem phiDoobPrimeJump_sum_eq_diagonal_sub_cross (v : ℝ → ℝ) (s : Finset ℕ) (x : ℝ) :
    (∑ n ∈ s, phiDoobPrimeJump v n x) =
      ∑ n ∈ s, (phiDoobPrimeDiagonal v n x - phiDoobPrimeCross v n x) := by
  simp_rw [phiDoobPrimeJump_eq_diagonal_sub_cross]

private theorem hasCompactSupport_phiDoob_shift {v : ℝ → ℝ}
    (hv : HasCompactSupport v) (t : ℝ) : HasCompactSupport (fun x => v (x + t)) := by
  exact hv.comp_homeomorph (Homeomorph.addRight t)

theorem integrable_phiDoobPrimeDiagonal {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) (n : ℕ) :
    Integrable (phiDoobPrimeDiagonal v n) := by
  have hshift := hasCompactSupport_phiDoob_shift hvc (Real.log n)
  have hsq : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx
    simp [hx]
  have hshift_sq : HasCompactSupport (fun x => v (x + Real.log n) ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hshift ⊢
    filter_upwards [hshift] with x hx
    simp [hx]
  have hs : HasCompactSupport (phiDoobPrimeDiagonal v n) := by
    unfold phiDoobPrimeDiagonal
    exact (hsq.add hshift_sq).mul_left
  have hc : Continuous (phiDoobPrimeDiagonal v n) := by
    unfold phiDoobPrimeDiagonal
    exact (((continuous_const.mul continuous_riemannKernelReal).mul
      (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
      ((hv.pow 2).add ((hv.comp (continuous_id.add continuous_const)).pow 2)))
  exact hc.integrable_of_hasCompactSupport hs

theorem integrable_phiDoobPrimeCross {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) (n : ℕ) :
    Integrable (phiDoobPrimeCross v n) := by
  have hs : HasCompactSupport (phiDoobPrimeCross v n) := by
    unfold phiDoobPrimeCross
    exact hvc.mul_left.mul_right
  have hc : Continuous (phiDoobPrimeCross v n) := by
    unfold phiDoobPrimeCross
    exact ((((continuous_const.mul continuous_riemannKernelReal).mul
      (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul hv).mul
      (hv.comp (continuous_id.add continuous_const)))
  exact hc.integrable_of_hasCompactSupport hs

/-- The integral of every prime jump is its two diagonals minus its full cross-term. -/
theorem integral_phiDoobPrimeJump_eq_diagonal_sub_cross {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) (n : ℕ) :
    (∫ x : ℝ, phiDoobPrimeJump v n x) =
      (∫ x : ℝ, phiDoobPrimeDiagonal v n x) -
        (∫ x : ℝ, phiDoobPrimeCross v n x) := by
  simp_rw [phiDoobPrimeJump_eq_diagonal_sub_cross]
  exact integral_sub (integrable_phiDoobPrimeDiagonal hv hvc n)
    (integrable_phiDoobPrimeCross hv hvc n)

/-- The actual Mangoldt coefficients satisfy the summability needed for the
noncompact Φ pairing; no truncation of the prime series is assumed. -/
theorem summable_vonMangoldt_abs_div_sq :
    Summable (fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)| / (n : ℝ) ^ 2) := by
  have h := WeilOneSided.summable_vonMangoldt_rpow (s := 2) (by norm_num)
  convert h using 1
  ext n
  by_cases hn : 2 ≤ n
  · simp [hn, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      div_eq_mul_inv]
    exact Or.inl rfl
  · have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl <;> simp [hn]

/-- Absolute convergence of every Mangoldt atom in the noncompact mixed
correlation with Φ and a compact real test. -/
theorem summable_mixed_vonMangoldt_primeSeries {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    Summable (fun n : ℕ =>
      (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
        (crossCorr riemannKernelReal H (Real.log n) +
          crossCorr riemannKernelReal H (-Real.log n))) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  obtain ⟨R, hR0, hR⟩ := exists_vanish_of_hasCompactSupport hHc
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, |H x| ≤ M := by
    obtain ⟨M, hM⟩ := hH.bounded_above_of_compact_support hHc
    exact ⟨M, fun x => by rw [← Real.norm_eq_abs]; exact hM x⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hdecay (y : ℝ) : |crossCorr riemannKernelReal H y| ≤
      M * C * (2 * R) * Real.exp (2 * R) * Real.exp (-(2 * |y|)) := by
    refine abs_integral_mul_translate_le hC0 hM0 hR0 (fun t => ?_) hM hR y
    rw [abs_of_pos (riemannKernelReal_pos t)]
    refine (hC t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    nlinarith [abs_nonneg t]
  exact (summable_atomPairing_of_decay summable_vonMangoldt_abs_div_sq hdecay).1

/-- The full prime sum in the mixed pairing `(Φ, Φv²)` is absolutely summable
and equals an integral against the Φ-smoothed Mangoldt source. -/
theorem phiDoob_mixed_prime_pairing_eq_integral {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2))) =
      ∫ x : ℝ, phiDoobTest (fun y => v y ^ 2) x *
        weightKernelTransform (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) x := by
  have hv2c : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx
    simp [hx]
  exact atomPairing_riemannKernel_eq_integral summable_vonMangoldt_abs_div_sq
    (continuous_riemannKernelReal.mul (hv.pow 2))
    (hasCompactSupport_phiDoobTest hv2c)

/-- The complete Mangoldt prime pairing of the cutoff Φ against `Φv²` has an
exponentially small truncation error. -/
theorem phiDoob_mixed_prime_cutoff_bound {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr (truncatedRiemannKernelReal L) (phiDoobTest (fun x => v x ^ 2))) -
        atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr riemannKernelReal (phiDoobTest (fun x => v x ^ 2)))| ≤
        K * Real.exp (-(2 * (L - 1))) := by
  have hv2c : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx
    simp [hx]
  exact exists_abs_atomPairing_truncated_sub_le summable_vonMangoldt_abs_div_sq
    (continuous_riemannKernelReal.mul (hv.pow 2))
    (hasCompactSupport_phiDoobTest hv2c)

/-- The full real Mangoldt prime pairing passes to the noncompact Φ limit. -/
theorem tendsto_mixed_vonMangoldt_prime_pairing {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    Filter.Tendsto (fun L : ℝ =>
      atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (truncatedRiemannKernelReal L) H)) Filter.atTop
      (nhds (atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr riemannKernelReal H))) := by
  obtain ⟨K, -, hK⟩ := exists_abs_atomPairing_truncated_sub_le
    summable_vonMangoldt_abs_div_sq hH hHc
  exact tendsto_of_abs_sub_le hK

/-- Complex Weil convolution equals the real mixed correlation, even when its
left input is noncompact. -/
theorem weilTest_real_crossCorr_eq (F H : ℝ → ℝ) (y : ℝ) :
    EF.weilTest (fun x => (F x : ℂ)) (fun x => (H x : ℂ)) y =
      (crossCorr F H y : ℂ) := by
  unfold EF.weilTest convolution EF.tilde crossCorr
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', Complex.conj_ofReal]
  rw [show -(y - t) = t - y by ring]
  push_cast
  ring

/-- The complex prime sum in the mixed explicit formula is the real atom pairing. -/
theorem vonMangoldtPrimeSum_real_crossCorr (F H : ℝ → ℝ) :
    (∑' n : ℕ,
      ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
        else 0 : ℝ) : ℂ) *
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (H x : ℂ)) (Real.log n) +
         EF.weilTest (fun x => (F x : ℂ)) (fun x => (H x : ℂ)) (-Real.log n))) =
      (atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr F H) : ℂ) := by
  unfold atomPairing
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [weilTest_real_crossCorr_eq F H, weilTest_real_crossCorr_eq F H]
  push_cast
  ring

/-- Polarized compact-test explicit formula; both inputs may differ. -/
theorem zeta_W_eq_weilFullFunctional_mixed {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    zetaZeroConfig.W f g =
      weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f g) := by
  rw [weilFullFunctional_vonMangoldt]
  set k := EF.weilTest f g with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hg.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hgc
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig k hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hg.continuous hfc hgc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT k (gammaOf ρ)) =
        fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f g ρ := by
    ext ρ
    simp only [ZeroConfig.Wsummand, hk, hfac, mul_assoc]
  rw [ZeroConfig.W, ← hterm, heq]

/-- Fourier factorization remains valid with noncompact Φ in the left slot. -/
theorem paperFT_mixed_riemannPhiKernel {H : ℝ → ℂ}
    (hH : Continuous H) (hHc : HasCompactSupport H) (z : ℂ) :
    paperFT (EF.weilTest riemannPhiKernel H) z =
      paperFT riemannPhiKernel z *
        (starRingEnd ℂ) (paperFT H ((starRingEnd ℂ) z)) := by
  rw [← EF.paperFT_tilde]
  unfold EF.weilTest
  apply paperFT_convolution
  · have hi := RiemannKernelGroundState.integrable_cexp_mul_riemannPhiKernel
      (1 / 2 + I * z)
    refine hi.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [show (1 / 2 + I * z - 1 / 2) * (x : ℂ) = I * z * x by ring]
    ring
  · exact ((EF.continuous_tilde hH).mul (by fun_prop)).integrable_of_hasCompactSupport
      (EF.hasCompactSupport_tilde hHc).mul_right

/-- The mixed gamma integrand is absolutely integrable although Φ is not compactly supported. -/
theorem integrable_mixed_riemannPhiKernel_gamma {H : ℝ → ℂ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) :
    Integrable (fun r : ℝ => paperFT (EF.weilTest riemannPhiKernel H) r *
      (EF.gammaBracket r : ℂ)) := by
  have hHt : ContDiff ℝ 2 (EF.tilde H) := by
    unfold EF.tilde
    exact Complex.conjCLE.contDiff.comp (hH.comp (contDiff_id.neg))
  have hHtc : HasCompactSupport (EF.tilde H) := EF.hasCompactSupport_tilde hHc
  have hmu := EF.integrable_paperFT_mul_mu hHt hHtc gammaFacts
  have hΦi : Integrable riemannPhiKernel := by
    simpa using RiemannKernelGroundState.integrable_cexp_mul_riemannPhiKernel (1 / 2)
  have hΦbound (r : ℝ) :
      ‖paperFT riemannPhiKernel r‖ ≤ ∫ x : ℝ, ‖riemannPhiKernel x‖ := by
    unfold paperFT
    calc
      ‖∫ x : ℝ, riemannPhiKernel x * Complex.exp (I * (r : ℂ) * x)‖ ≤
          ∫ x : ℝ, ‖riemannPhiKernel x * Complex.exp (I * (r : ℂ) * x)‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ x : ℝ, ‖riemannPhiKernel x‖ := by
        congr 1
        funext x
        rw [norm_mul, Complex.norm_exp]
        simp
  have hcont : Continuous (fun r : ℝ => paperFT riemannPhiKernel r) :=
    WeilHerglotz.continuous_paperFT_real hΦi
  have hprod : Integrable (fun r : ℝ =>
      paperFT riemannPhiKernel r *
        (paperFT (EF.tilde H) r * (mu r : ℂ))) :=
    hmu.bdd_mul hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hΦbound)
  have hgamma (r : ℝ) : (EF.gammaBracket r : ℂ) = (2 * Real.pi : ℂ) * (mu r : ℂ) := by
    simp only [EF.gammaBracket, mu]
    push_cast
    field_simp
  have hprod' := hprod.const_mul (2 * Real.pi : ℂ)
  refine hprod'.congr (Filter.Eventually.of_forall fun r => ?_)
  change (2 * Real.pi : ℂ) *
      (paperFT riemannPhiKernel r * (paperFT (EF.tilde H) r * (mu r : ℂ))) =
    paperFT (EF.weilTest riemannPhiKernel H) r * (EF.gammaBracket r : ℂ)
  rw [paperFT_mixed_riemannPhiKernel hH.continuous hHc,
    ← EF.paperFT_tilde, hgamma]
  ring

/-- The zero side of the compact mixed test `(Φχ_L,H)` is bounded by the
near-radical tail energy times the fixed test energy. -/
theorem norm_W_truncatedRiemannKernel_mixed_le {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) (L : ℝ) :
    ‖zetaZeroConfig.W (truncatedRiemannKernel L) (fun x => (H x : ℂ))‖ ≤
      5 / 4 * zeroSumZ * (truncatedRiemannTailEnergy L * testEnergy H) := by
  obtain ⟨Λ, -, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set E := truncatedRiemannTailEnergy L with hE
  set F := testEnergy H with hF
  have hE0 : 0 ≤ E := truncatedRiemannTailEnergy_nonneg L
  have hF0 : 0 ≤ F := testEnergy_nonneg H
  have hbound (ρ : zetaZeroConfig.carrier) :
      ‖zetaZeroConfig.Wsummand (truncatedRiemannKernel L)
          (fun x => (H x : ℂ)) ρ‖ ≤
        (zetaZeroConfig.mult ρ : ℝ) *
          ((E * F) / (1 + |(ρ : ℂ).im|) ^ 2) := by
    obtain ⟨hΦ, -⟩ := truncatedRiemannKernel_zero_bound L hΛ ρ
    obtain ⟨-, hG⟩ := test_zero_bound hH hHc ρ
    set D := 1 + |(ρ : ℂ).im| with hD
    have hD0 : 0 < D := by positivity
    have hprod : ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖ *
        ‖paperFT (fun x => (H x : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
          E * F / D ^ 2 := by
      have h := mul_le_mul hΦ hG
        (mul_nonneg hD0.le (norm_nonneg _)) hE0
      apply (le_div_iff₀ (sq_pos_of_pos hD0)).2
      nlinarith
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
  exact (summable_and_norm_tsum_le_of_zeroBound
    (mul_nonneg hE0 hF0) hbound).2

/-- The mixed zero sum of a cutoff Φ and fixed compact real test tends to zero. -/
theorem tendsto_W_truncatedRiemannKernel_mixed {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) :
    Filter.Tendsto (fun L : ℝ =>
      zetaZeroConfig.W (truncatedRiemannKernel L) (fun x => (H x : ℂ)))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K : ℝ := 5 / 4 * zeroSumZ * testEnergy H with hK
  have hK0 : 0 ≤ K := by
    have := zeroSumZ_nonneg
    have := testEnergy_nonneg H
    positivity
  obtain ⟨L₀, hL₀⟩ := WeilSpectral.exists_truncatedRiemannTailEnergy_le
    (δ := ε / (K + 1)) (by positivity)
  refine ⟨L₀, fun L hL => ?_⟩
  have hb := norm_W_truncatedRiemannKernel_mixed_le hH hHc L
  have hE := hL₀ L hL
  have hKlt : K / (K + 1) < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < K + 1)).2
    linarith
  have hfinal : K * truncatedRiemannTailEnergy L < ε := by
    calc
      K * truncatedRiemannTailEnergy L ≤ K * (ε / (K + 1)) :=
        mul_le_mul_of_nonneg_left hE hK0
      _ = ε * (K / (K + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hKlt hε
      _ = ε := by ring
  rw [dist_zero_right]
  have hb' : ‖zetaZeroConfig.W (truncatedRiemannKernel L)
      (fun x => (H x : ℂ))‖ ≤ K * truncatedRiemannTailEnergy L := by
    convert hb using 1
    ring
  exact lt_of_le_of_lt hb' hfinal

/-- The cutoff kernels are dominated pointwise by Φ, uniformly in the cutoff. -/
theorem norm_truncatedRiemannKernel_le_riemannPhiKernel (L x : ℝ) :
    ‖truncatedRiemannKernel L x‖ ≤ ‖riemannPhiKernel x‖ := by
  rw [truncatedRiemannKernel_eq, riemannPhiKernel_eq_ofReal,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (truncatedRiemannKernelReal_nonneg L x),
    abs_of_pos (riemannKernelReal_pos x)]
  unfold truncatedRiemannKernelReal
  have hcut := bulkCutoff_le_one L x
  nlinarith [riemannKernelReal_pos x]

/-- Φ cutoff converges in every paper Fourier/Laplace coordinate, including
the pole coordinates and all zero ordinates. -/
theorem tendsto_paperFT_truncatedRiemannKernel (z : ℂ) :
    Filter.Tendsto (fun L : ℝ => paperFT (truncatedRiemannKernel L) z)
      Filter.atTop (nhds (paperFT riemannPhiKernel z)) := by
  have hΦexp : Integrable (fun x : ℝ =>
      riemannPhiKernel x * Complex.exp (I * z * x)) := by
    have hi := RiemannKernelGroundState.integrable_cexp_mul_riemannPhiKernel
      (1 / 2 + I * z)
    refine hi.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [show (1 / 2 + I * z - 1 / 2) * (x : ℂ) = I * z * x by ring]
    ring
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := Filter.atTop)
    (F := fun L : ℝ => fun x : ℝ =>
      truncatedRiemannKernel L x * Complex.exp (I * z * x))
    (f := fun x : ℝ => riemannPhiKernel x * Complex.exp (I * z * x))
    (fun x : ℝ => ‖riemannPhiKernel x * Complex.exp (I * z * x)‖)
    (Filter.Eventually.of_forall fun L =>
      ((continuous_truncatedRiemannKernel L).mul (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun L => Filter.Eventually.of_forall fun x => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_truncatedRiemannKernel_le_riemannPhiKernel L x) (norm_nonneg _))
    hΦexp.norm
    (Filter.Eventually.of_forall fun x => by
      have heq : ∀ᶠ L : ℝ in Filter.atTop,
          truncatedRiemannKernel L x * Complex.exp (I * z * x) =
            riemannPhiKernel x * Complex.exp (I * z * x) := by
        filter_upwards [Filter.eventually_ge_atTop (|x| + 1)] with L hL
        rw [truncatedRiemannKernel_eq, truncatedRiemannKernelReal,
          bulkCutoff_eq_one (by linarith), mul_one, riemannPhiKernel_eq_ofReal]
      exact tendsto_const_nhds.congr' (heq.mono fun L hL => hL.symm))
  simpa only [paperFT] using h

/-- Both pole coordinates of the mixed Weil convolution pass to Φ. -/
theorem tendsto_mixed_riemannPhiKernel_pole {H : ℝ → ℂ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    Filter.Tendsto
      (fun L : ℝ => weilPoleTerm (EF.weilTest (truncatedRiemannKernel L) H))
      Filter.atTop (nhds (weilPoleTerm (EF.weilTest riemannPhiKernel H))) := by
  have hlim (z : ℂ) : Filter.Tendsto
      (fun L : ℝ => paperFT (EF.weilTest (truncatedRiemannKernel L) H) z)
      Filter.atTop (nhds (paperFT (EF.weilTest riemannPhiKernel H) z)) := by
    have h := (tendsto_paperFT_truncatedRiemannKernel z).mul_const
      ((starRingEnd ℂ) (paperFT H ((starRingEnd ℂ) z)))
    convert h using 1
    · funext L
      exact EF.paperFT_weilTest (continuous_truncatedRiemannKernel L)
        hH (hasCompactSupport_truncatedRiemannKernel L) hHc z
    · rw [paperFT_mixed_riemannPhiKernel hH hHc z]
  unfold weilPoleTerm
  exact (hlim (I / 2)).add (hlim (-I / 2))

/-- The entire complex Mangoldt prime term converges under Φ cutoff. -/
theorem tendsto_mixed_riemannPhiKernel_primeSum {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    Filter.Tendsto
      (fun L : ℝ => ∑' n : ℕ,
        ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
          else 0 : ℝ) : ℂ) *
          (EF.weilTest (truncatedRiemannKernel L) (fun x => (H x : ℂ)) (Real.log n) +
           EF.weilTest (truncatedRiemannKernel L) (fun x => (H x : ℂ)) (-Real.log n)))
      Filter.atTop
      (nhds (∑' n : ℕ,
        ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
          else 0 : ℝ) : ℂ) *
          (EF.weilTest riemannPhiKernel (fun x => (H x : ℂ)) (Real.log n) +
           EF.weilTest riemannPhiKernel (fun x => (H x : ℂ)) (-Real.log n)))) := by
  have hreal := tendsto_mixed_vonMangoldt_prime_pairing hH hHc
  have hcast := (Complex.continuous_ofReal.tendsto _).comp hreal
  convert hcast using 1
  · funext L
    rw [show truncatedRiemannKernel L =
      (fun x => (truncatedRiemannKernelReal L x : ℂ)) by
        funext x; exact truncatedRiemannKernel_eq L x]
    exact vonMangoldtPrimeSum_real_crossCorr (truncatedRiemannKernelReal L) H
  · congr 1
    rw [show riemannPhiKernel = (fun x => (riemannKernelReal x : ℂ)) by
      funext x; exact riemannPhiKernel_eq_ofReal x]
    exact vonMangoldtPrimeSum_real_crossCorr riemannKernelReal H

/-- The archimedean gamma integral of the compact mixed tests converges to
the absolutely integrable gamma integral of the noncompact Φ pairing. -/
theorem tendsto_mixed_riemannPhiKernel_gamma_integral {H : ℝ → ℂ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) :
    Filter.Tendsto
      (fun L : ℝ => ∫ r : ℝ,
        paperFT (EF.weilTest (truncatedRiemannKernel L) H) r *
          (EF.gammaBracket r : ℂ)) Filter.atTop
      (nhds (∫ r : ℝ, paperFT (EF.weilTest riemannPhiKernel H) r *
        (EF.gammaBracket r : ℂ))) := by
  have hHt : ContDiff ℝ 2 (EF.tilde H) := by
    unfold EF.tilde
    exact Complex.conjCLE.contDiff.comp (hH.comp (contDiff_id.neg))
  have hHtc : HasCompactSupport (EF.tilde H) := EF.hasCompactSupport_tilde hHc
  have hmu := EF.integrable_paperFT_mul_mu hHt hHtc gammaFacts
  have hgamma (r : ℝ) : (EF.gammaBracket r : ℂ) = (2 * Real.pi : ℂ) * (mu r : ℂ) := by
    simp only [EF.gammaBracket, mu]
    push_cast
    field_simp
  set G : ℝ → ℂ := fun r => paperFT (EF.tilde H) r * (EF.gammaBracket r : ℂ)
    with hG
  have hGi : Integrable G := by
    have h := hmu.const_mul (2 * Real.pi : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [hG, hgamma]
    ring

  have hΦi : Integrable riemannPhiKernel := by
    simpa using RiemannKernelGroundState.integrable_cexp_mul_riemannPhiKernel (1 / 2)
  set C : ℝ := ∫ x : ℝ, ‖riemannPhiKernel x‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hΦLbound (L r : ℝ) : ‖paperFT (truncatedRiemannKernel L) r‖ ≤ C := by
    have hLi : Integrable (fun x : ℝ =>
        truncatedRiemannKernel L x * Complex.exp (I * (r : ℂ) * x)) :=
      ((continuous_truncatedRiemannKernel L).mul (by fun_prop)).integrable_of_hasCompactSupport
        (hasCompactSupport_truncatedRiemannKernel L).mul_right
    unfold paperFT
    calc
      ‖∫ x : ℝ, truncatedRiemannKernel L x * Complex.exp (I * (r : ℂ) * x)‖ ≤
          ∫ x : ℝ, ‖truncatedRiemannKernel L x * Complex.exp (I * (r : ℂ) * x)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ C := by
        rw [hC]
        apply integral_mono hLi.norm hΦi.norm
        intro x
        dsimp only
        rw [norm_mul, Complex.norm_exp]
        have hre : (I * (r : ℂ) * (x : ℂ)).re = 0 := by simp
        rw [hre, Real.exp_zero, mul_one]
        exact norm_truncatedRiemannKernel_le_riemannPhiKernel L x
  have hmeas : ∀ᶠ L : ℝ in Filter.atTop,
      AEStronglyMeasurable (fun r : ℝ => paperFT (truncatedRiemannKernel L) r * G r) :=
    Filter.Eventually.of_forall fun L =>
      (WeilHerglotz.continuous_paperFT_real
        (continuous_truncatedRiemannKernel L |>.integrable_of_hasCompactSupport
          (hasCompactSupport_truncatedRiemannKernel L))).aestronglyMeasurable.mul
        hGi.aestronglyMeasurable
  have hdom : ∀ᶠ L : ℝ in Filter.atTop, ∀ᵐ r : ℝ,
      ‖paperFT (truncatedRiemannKernel L) r * G r‖ ≤ C * ‖G r‖ :=
    Filter.Eventually.of_forall fun L => Filter.Eventually.of_forall fun r => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hΦLbound L r) (norm_nonneg _)
  have hpoint : ∀ᵐ r : ℝ,
      Filter.Tendsto (fun L : ℝ => paperFT (truncatedRiemannKernel L) r * G r)
        Filter.atTop (nhds (paperFT riemannPhiKernel r * G r)) :=
    Filter.Eventually.of_forall fun r =>
      (tendsto_paperFT_truncatedRiemannKernel r).mul_const (G r)
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := Filter.atTop)
    (F := fun L : ℝ => fun r : ℝ => paperFT (truncatedRiemannKernel L) r * G r)
    (f := fun r : ℝ => paperFT riemannPhiKernel r * G r)
    (fun r : ℝ => C * ‖G r‖) hmeas hdom (hGi.norm.const_mul C) hpoint
  convert h using 1
  · funext L
    apply integral_congr_ae
    filter_upwards with r
    rw [EF.paperFT_weilTest (continuous_truncatedRiemannKernel L)
      hH.continuous (hasCompactSupport_truncatedRiemannKernel L) hHc,
      ← EF.paperFT_tilde, hG]
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards with r
    rw [paperFT_mixed_riemannPhiKernel hH.continuous hHc,
      ← EF.paperFT_tilde, hG]
    ring

/-- Noncompact mixed explicit formula for Riemann's kernel and a compact real
`C²` test. Its zero side vanishes because `Φ̂` vanishes at every zeta zero.
The gamma integral and complete Mangoldt prime sum are genuine convergent terms. -/
theorem mixed_explicit_formula_riemannPhiKernel {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) :
    weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest riemannPhiKernel (fun x => (H x : ℂ))) = 0 := by
  let g : ℝ → ℂ := fun x => (H x : ℂ)
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp hH
  have hgc : HasCompactSupport g := hHc.comp_left Complex.ofReal_zero
  have hzero := tendsto_W_truncatedRiemannKernel_mixed hH hHc
  have hpole := tendsto_mixed_riemannPhiKernel_pole hg.continuous hgc
  have hprime := tendsto_mixed_riemannPhiKernel_primeSum hH.continuous hHc
  have harch := tendsto_mixed_riemannPhiKernel_gamma_integral hg hgc
  have hfull : Filter.Tendsto
      (fun L : ℝ => weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (truncatedRiemannKernel L) g)) Filter.atTop
      (nhds (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest riemannPhiKernel g))) := by
    simpa only [weilFullFunctional, weilPoleTerm, g] using
      ((hpole.sub hprime).add (harch.const_mul (1 / (2 * Real.pi) : ℂ)))
  have hzero' : Filter.Tendsto
      (fun L : ℝ => weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (truncatedRiemannKernel L) g)) Filter.atTop (nhds 0) := by
    refine hzero.congr' (Filter.Eventually.of_forall fun L => ?_)
    exact (zeta_W_eq_weilFullFunctional_mixed
      (contDiff_nearRadicalTest L _) (hasCompactSupport_truncatedRiemannKernel L)
      hg hgc)
  exact tendsto_nhds_unique hfull hzero'

/-- The noncompact mixed explicit formula at the Doob diagonal test `Φv²`. -/
theorem phiDoob_mixed_explicit_formula {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest riemannPhiKernel
        (fun x => (phiDoobTest (fun y => v y ^ 2) x : ℂ))) = 0 := by
  have hv2c : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx
    simp [hx]
  exact mixed_explicit_formula_riemannPhiKernel
    (contDiff_phiDoobTest (hv.pow 2)) (hasCompactSupport_phiDoobTest hv2c)

/-- For odd `v`, a prime step crossing the origin carries the reflected value `-v(-x)`. -/
theorem phiDoobPrimeCross_reflected {v : ℝ → ℝ}
    (hodd : ∀ x, v (-x) = -v x) (n : ℕ) (x : ℝ) :
    phiDoobPrimeCross v n (x - Real.log n) =
      -2 * vonMangoldtAtom n * riemannKernelReal (Real.log n - x) *
        riemannKernelReal x * v (Real.log n - x) * v x := by
  unfold phiDoobPrimeCross
  rw [show x - Real.log n = -(Real.log n - x) by ring,
    show -(Real.log n - x) + Real.log n = x by ring]
  rw [show riemannKernelReal (-(Real.log n - x)) =
    riemannKernelReal (Real.log n - x) by simp [riemannKernelReal, abs_sub_comm],
    hodd (Real.log n - x)]
  ring

/-- The origin-crossing prime jump is a reflected *sum* square for odd `v`. -/
theorem phiDoobPrimeJump_reflected {v : ℝ → ℝ}
    (hodd : ∀ x, v (-x) = -v x) (n : ℕ) (x : ℝ) :
    phiDoobPrimeJump v n (x - Real.log n) =
      vonMangoldtAtom n * riemannKernelReal (Real.log n - x) *
        riemannKernelReal x * (v (Real.log n - x) + v x) ^ 2 := by
  unfold phiDoobPrimeJump
  rw [show x - Real.log n = -(Real.log n - x) by ring,
    show -(Real.log n - x) + Real.log n = x by ring]
  rw [show riemannKernelReal (-(Real.log n - x)) =
    riemannKernelReal (Real.log n - x) by simp [riemannKernelReal, abs_sub_comm],
    hodd (Real.log n - x)]
  ring

end

end RHTower
