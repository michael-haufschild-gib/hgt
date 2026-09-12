import GaloisForLFunctions.RHTower.MobiusThetaNativeCriticalEuler

/-!
# Original native jet boundary with both critical contacts

The native raising equations admit logarithmic multiplication on both
prime-anchored collars. Pairing those equations with an arbitrary Schwartz
test yields the complete raised boundary: both logarithmic collars, both
original finite prefixes, both causal currents, and their exact Xi-jet
contacts. The opposite raising signs force a sum of Euler contributions.

The first contact reads the Fourier test at zero and the second reads the
original test at zero. The prime cutoff and native depth remain unchanged.
This is a source identity; it does not assert fixed Gamma/BV reader equality.
-/

set_option autoImplicit false
open Complex MeasureTheory ArithmeticFunction Filter Topology FourierTransform
open scoped SchwartzMap
noncomputable section
namespace RHTower
namespace NativeJetBalance

private def evenLift (f : ℝ → ℂ) (x : ℝ) : ℂ := f |x|
private def logWeight (f : ℝ → ℂ) (x : ℝ) : ℂ := (Real.log |x| : ℂ) * f x

private theorem evenLift_integrable {f : ℝ → ℂ} (hf : IntegrableOn f (Set.Ioi 0)) :
    Integrable (evenLift f) := by
  have hp : IntegrableOn (evenLift f) (Set.Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [evenLift, abs_of_pos hx]) measurableSet_Ioi
  have hn : IntegrableOn (evenLift f) (Set.Iio 0) :=
    (deningerEvenPreimage_integrableOn_Iio hf).congr_fun
      (fun x hx => by rw [evenLift, abs_of_neg hx]) measurableSet_Iio
  exact deningerIntegrable_of_rays hp hn

private theorem logPrefix_integrable (h : DeningerMeyerSource) (p : ℕ) :
    Integrable (fun x : ℝ => ∑ n ∈ Finset.range p,
      (Real.log (n : ℝ) : ℂ) * (((moebius n : ℤ) : ℂ) *
        deningerAdiabaticEvenLogPullDilation h n x)) := by
  apply integrable_finsetSum (Finset.range p)
  intro n _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact ((deningerAdiabaticEvenLogPullDilation_integrable h hn).const_mul _).const_mul _

private theorem firstPrefix_integrable (k p : ℕ) (m : ℕ+) :
    Integrable (evenLift (mobiusThetaNativeLogPrefix k p m)) := by
  change Integrable (fun x : ℝ => mobiusThetaNativeLogPrefix k p m |x|)
  simpa only [mobiusThetaNativeLogPrefix,
    deningerAdiabaticEvenLogPullDilation, mobiusThetaNativeMeyerSource_toSource]
    using logPrefix_integrable (mobiusThetaNativeMeyerSource k m) p

private theorem secondPrefix_integrable (k p : ℕ) (m : ℕ+) :
    Integrable (evenLift (mobiusThetaNativeSecondLogPrefix k p m)) := by
  exact logPrefix_integrable (mobiusThetaNativeSecondCollarSource k m) p

private theorem first_abs (k p : ℕ) (m : ℕ+) (x : ℝ) :
    mobiusThetaNativeCollarTail k p m |x| = mobiusThetaNativeCollarTail k p m x := by
  simp only [mobiusThetaNativeCollarTail, abs_abs]

private theorem second_abs (k p : ℕ) (m : ℕ+) (x : ℝ) :
    mobiusThetaNativeSecondCollarTail k p m |x| = mobiusThetaNativeSecondCollarTail k p m x := by
  simp only [mobiusThetaNativeSecondCollarTail, deningerAdiabaticEvenLogPullDilation, abs_abs]

private theorem first_raise_ae (k p : ℕ) (m : ℕ+) :
    mobiusThetaNativeCollarTail (k+1) p m =ᵐ[volume] fun x =>
      (I * (m : ℂ)) * (logWeight (mobiusThetaNativeCollarTail k p m) x -
        evenLift (mobiusThetaNativeEulerCurrent k m) x - evenLift (mobiusThetaNativeLogPrefix k p m) x) := by
  filter_upwards [deningerCompl_zero_ae_univ] with x hx
  have hxmem : x ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := hx.mpr (Set.mem_univ x)
  have hx0 : x ≠ 0 := by simpa using hxmem
  simpa only [first_abs, logWeight, evenLift] using
    mobiusThetaNativeCollarTail_succ_euler k p m (abs_pos.mpr hx0)

private theorem second_raise_ae (k p : ℕ) (m : ℕ+) :
    mobiusThetaNativeSecondCollarTail (k+1) p m =ᵐ[volume] fun x =>
      (-(I * (m : ℂ))) * (logWeight (mobiusThetaNativeSecondCollarTail k p m) x -
        evenLift (mobiusThetaNativeSecondEulerCurrent k m) x -
          evenLift (mobiusThetaNativeSecondLogPrefix k p m) x) := by
  filter_upwards [deningerCompl_zero_ae_univ] with x hx
  have hxmem : x ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := hx.mpr (Set.mem_univ x)
  have hx0 : x ≠ 0 := by simpa using hxmem
  simpa only [second_abs, logWeight, evenLift] using
    mobiusThetaNativeSecondCollarTail_succ_euler k p m (abs_pos.mpr hx0)

private theorem logWeight_integrable_of_raise {A A' E L : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hA' : Integrable A') (hE : Integrable E) (hL : Integrable L)
    (hr : A' =ᵐ[volume] fun x => c * (logWeight A x - E x - L x)) :
    Integrable (logWeight A) := by
  have hi : Integrable (fun x => c⁻¹ * A' x + E x + L x) :=
    ((hA'.const_mul c⁻¹).add hE).add hL
  apply hi.congr
  filter_upwards [hr] with x hx
  rw [hx, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  ring

end NativeJetBalance
open NativeJetBalance

/-- The original prime-anchored first collar admits logarithmic multiplication. -/
theorem mobiusThetaNativeCollarTail_log_integrable (k p : ℕ) (m : ℕ+) :
    Integrable (fun x : ℝ => (Real.log |x| : ℂ) * mobiusThetaNativeCollarTail k p m x) := by
  exact logWeight_integrable_of_raise
    (mul_ne_zero I_ne_zero (show (m : ℂ) ≠ 0 by exact_mod_cast m.ne_zero))
    (mobiusThetaNativeCollarTail_integrable (k+1) p m)
    (evenLift_integrable (mobiusThetaNativeEulerCurrent_integrable k m))
    (firstPrefix_integrable k p m) (first_raise_ae k p m)

/-- The unchanged second collar admits its logarithmic multiplication at every native depth. -/
theorem mobiusThetaNativeSecondCollarTail_log_integrable (k p : ℕ) (m : ℕ+) :
    Integrable (fun x : ℝ => (Real.log |x| : ℂ) * mobiusThetaNativeSecondCollarTail k p m x) := by
  exact logWeight_integrable_of_raise
    (neg_ne_zero.mpr (mul_ne_zero I_ne_zero (show (m : ℂ) ≠ 0 by exact_mod_cast m.ne_zero)))
    (mobiusThetaNativeSecondCollarTail_integrable (k+1) p m)
    (evenLift_integrable (mobiusThetaNativeSecondEulerCurrent_integrable k m))
    (secondPrefix_integrable k p m) (second_raise_ae k p m)

/-- A test folded onto the positive ray, retaining both orientations. -/
def mobiusThetaNativeEvenTest (φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := φ + 𝓕 (𝓕 φ)

namespace NativeJetBalance

private def pairing (f : ℝ → ℂ) (φ : SchwartzMap ℝ ℂ) : ℂ := ∫ x : ℝ, f x * φ x

private theorem testIntegrable {f : ℝ → ℂ} (hf : Integrable f) (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => f x * φ x) := by
  apply hf.mul_bdd φ.continuous.aestronglyMeasurable
  apply ae_of_all
  intro x
  simpa only [pow_zero, one_mul, iteratedDeriv_zero] using φ.le_seminorm' ℝ 0 0 x

private theorem distribution_pairing {f : ℝ → ℂ} (hf : Integrable f) (φ : SchwartzMap ℝ ℂ) :
    deningerL1Distribution hf φ = pairing f φ := by
  rw [deningerL1Distribution_apply]
  apply integral_congr_ae
  exact ae_of_all _ fun x => mul_comm (φ x) (f x)

private theorem fold_pair {f : ℝ → ℂ} (hf : IntegrableOn f (Set.Ioi 0))
    (φ : SchwartzMap ℝ ℂ) :
    pairing (evenLift f) φ = ∫ x in Set.Ioi (0 : ℝ), f x * mobiusThetaNativeEvenTest φ x := by
  have hfull := testIntegrable (evenLift_integrable hf) φ
  have href := testIntegrable (evenLift_integrable hf) (𝓕 (𝓕 φ))
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hfull.integrableOn hfull.integrableOn
  have hn := integral_comp_neg_Ioi (0 : ℝ) (fun x => evenLift f x * φ x)
  simp only [neg_zero] at hn
  have hnfun : (fun x : ℝ => evenLift f (-x) * φ (-x)) =
      fun x : ℝ => evenLift f x * (𝓕 (𝓕 φ)) x := by
    funext x
    simp only [evenLift, abs_neg, deningerFourierSq_apply]
  change (∫ x : ℝ, evenLift f x * φ x) = _
  rw [← hsplit, ← hn, hnfun, ← integral_add href.integrableOn hfull.integrableOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  change evenLift f x * (𝓕 (𝓕 φ)) x + evenLift f x * φ x = _
  simp only [evenLift, abs_of_pos (Set.mem_Ioi.mp hx), mobiusThetaNativeEvenTest,
    _root_.add_apply]
  ring

private theorem evenTest_zero (φ : SchwartzMap ℝ ℂ) :
    mobiusThetaNativeEvenTest φ 0 = 2 * φ 0 := by
  simp only [mobiusThetaNativeEvenTest, _root_.add_apply, deningerFourierSq_apply, neg_zero]
  ring

private theorem first_contact (k : ℕ) (m : ℕ+) (φ : SchwartzMap ℝ ℂ) :
    pairing (evenLift (mobiusThetaNativeEulerCurrent k m)) φ =
      (∑' n : ℕ, deningerCausalTerm
        (deningerMobiusPreimage (mobiusThetaNativeCollarSource k m)) (mobiusThetaNativeEvenTest φ) n) +
      (2 * ((m : ℂ)⁻¹ * iteratedDeriv k XiC (mobiusThetaNativeMassParameter m))) * φ 0 := by
  have hc := mobiusThetaNativeEulerCurrent_pairing_contact k m (mobiusThetaNativeEvenTest φ)
  rw [← fold_pair (mobiusThetaNativeEulerCurrent_integrable k m) φ, evenTest_zero] at hc
  linear_combination -hc

private theorem second_contact (k : ℕ) (m : ℕ+) (φ : SchwartzMap ℝ ℂ) :
    pairing (evenLift (mobiusThetaNativeSecondEulerCurrent k m)) φ =
      (∑' n : ℕ, deningerCausalTerm
        (deningerMobiusPreimage (DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m)))
          (mobiusThetaNativeEvenTest φ) n) +
      (2 * ((m : ℂ)⁻¹ * iteratedDeriv k XiC (I / 2))) * φ 0 := by
  have hc := mobiusThetaNativeSecondEulerCurrent_pairing_contact k m (mobiusThetaNativeEvenTest φ)
  rw [← fold_pair (mobiusThetaNativeSecondEulerCurrent_integrable k m) φ, evenTest_zero] at hc
  linear_combination -hc

private theorem pairing_raise {A A' E L : ℝ → ℂ} {c : ℂ}
    (hlog : Integrable (logWeight A)) (hE : Integrable E) (hL : Integrable L)
    (hr : A' =ᵐ[volume] fun x => c * (logWeight A x - E x - L x))
    (φ : SchwartzMap ℝ ℂ) :
    pairing A' φ = c * (pairing (logWeight A) φ - pairing E φ - pairing L φ) := by
  have he : (fun x : ℝ => A' x * φ x) =ᵐ[volume]
      fun x => c * ((logWeight A x * φ x - E x * φ x) - L x * φ x) := by
    filter_upwards [hr] with x hx
    rw [hx]
    ring
  unfold pairing
  rw [integral_congr_ae he, integral_const_mul,
    integral_sub (f := fun x => logWeight A x * φ x - E x * φ x)
      (g := fun x => L x * φ x)
      ((testIntegrable hlog φ).sub (testIntegrable hE φ)) (testIntegrable hL φ),
    integral_sub (testIntegrable hlog φ) (testIntegrable hE φ)]

end NativeJetBalance

/-- The full original raised boundary retains both logarithmic collars, both prefixes and both critical contacts. -/
theorem mobiusThetaNativeFullCollarBoundary_succ_contact
    (k p : ℕ) (m : ℕ+) (φ : SchwartzMap ℝ ℂ) :
    mobiusThetaNativeFullCollarBoundary (k+1) p m φ =
      (I * (m : ℂ)) *
        (((∫ x : ℝ, ((Real.log |x| : ℂ) * mobiusThetaNativeCollarTail k p m x) * (𝓕 φ) x) +
          (∫ x : ℝ, ((Real.log |x| : ℂ) * mobiusThetaNativeSecondCollarTail k p m x) * φ x)) -
        ((∑' n : ℕ, deningerCausalTerm
          (deningerMobiusPreimage (mobiusThetaNativeCollarSource k m))
            (mobiusThetaNativeEvenTest (𝓕 φ)) n) +
          (∑' n : ℕ, deningerCausalTerm
            (deningerMobiusPreimage (DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m)))
              (mobiusThetaNativeEvenTest φ) n)) -
        ((∫ x : ℝ, mobiusThetaNativeLogPrefix k p m |x| * (𝓕 φ) x) +
          (∫ x : ℝ, mobiusThetaNativeSecondLogPrefix k p m |x| * φ x)) -
        ((2 * ((m : ℂ)⁻¹ * iteratedDeriv k XiC (mobiusThetaNativeMassParameter m))) * (𝓕 φ) 0 +
          (2 * ((m : ℂ)⁻¹ * iteratedDeriv k XiC (I / 2))) * φ 0)) := by
  change deningerL1Distribution (mobiusThetaNativeCollarTail_integrable (k+1) p m) (𝓕 φ) -
    deningerL1Distribution (mobiusThetaNativeSecondCollarTail_integrable (k+1) p m) φ = _
  rw [distribution_pairing, distribution_pairing,
    pairing_raise (mobiusThetaNativeCollarTail_log_integrable k p m)
      (evenLift_integrable (mobiusThetaNativeEulerCurrent_integrable k m))
      (firstPrefix_integrable k p m) (first_raise_ae k p m),
    pairing_raise (mobiusThetaNativeSecondCollarTail_log_integrable k p m)
      (evenLift_integrable (mobiusThetaNativeSecondEulerCurrent_integrable k m))
      (secondPrefix_integrable k p m) (second_raise_ae k p m),
    first_contact, second_contact]
  dsimp only [pairing, logWeight, evenLift]
  ring

end RHTower
