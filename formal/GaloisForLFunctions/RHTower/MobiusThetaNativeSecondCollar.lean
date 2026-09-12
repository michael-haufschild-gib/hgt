import GaloisForLFunctions.RHTower.MobiusThetaNativePrefixMass
import GaloisForLFunctions.RHTower.DeningerAdiabaticTransgression
import GaloisForLFunctions.RHTower.DeningerCommutatorBoundaryKernel

/-!
# Original second collar and retained finite-prefix transgression

The existing collar exchange of every original native internal jet has an absolutely
summable radial Mobius expansion with both native powers retained. The whole second
prime-anchored tail is integrable. Its distribution boundary differs from the existing
all-integer commutator by exactly the Fourier boundary of the original finite prefix.

The exchanged source has native Mellin parameter `-v + I * (1 - 1/m)`, with the
original Jacobian `1/m`. This is holomorphic Mellin reflection, not identification
with the Hermitian fixed Gamma/BV reader. The source-derived distribution comparison
does not assert vanishing of the commutator, prefix boundary or fixed physical defect.
-/

set_option autoImplicit false
open Complex MeasureTheory ArithmeticFunction FourierTransform
open scoped SchwartzMap
noncomputable section
namespace RHTower

/-- The second collar is the existing exchange of the unchanged native source. -/
def mobiusThetaNativeSecondCollarSource (k : ℕ) (m : ℕ+) : DeningerMeyerSource :=
  deningerMeyerCollarExchange (mobiusThetaNativeMeyerSource k m)

/-- The exact radial exchange carries both the arithmetic and physical-coordinate powers. -/
theorem mobiusThetaNativeSecondCollar_term
    (k n : ℕ) (m : ℕ+) {x : ℝ} (hx : x ≠ 0) :
    ((moebius n : ℤ) : ℂ) *
      deningerAdiabaticEvenLogPullDilation (mobiusThetaNativeSecondCollarSource k m) n x =
    ((-1 : ℂ) ^ k * ((|x| : ℝ) : ℂ) ^ ((m : ℕ) - 1)) *
      (((moebius n : ℤ) : ℂ) * (n : ℂ) ^ ((m : ℕ) - 1) *
        deningerLogPull (mobiusThetaNativeCollarSource k m) ((n : ℝ) * |x|)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < (n : ℝ) * |x| := mul_pos hnR (abs_pos.mpr hx)
  have hd : (((m : ℕ) - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ (m : ℕ) from m.pos), Nat.cast_one]
  have he : (Real.exp (((m : ℝ) - 1) * Real.log ((n : ℝ) * |x|)) : ℂ) =
      (n : ℂ) ^ ((m : ℕ) - 1) * ((|x| : ℝ) : ℂ) ^ ((m : ℕ) - 1) := by
    rw [← hd, Real.exp_nat_mul, Real.exp_log hr]
    push_cast
    rw [mul_pow]
  change ((moebius n : ℤ) : ℂ) *
    deningerCollarFun (mobiusThetaNativeCollarSource k m) (Real.log ((n : ℝ) * |x|)) = _
  rw [mobiusThetaNativeCollarSource_collar, he]
  change _ = _ * (((moebius n : ℤ) : ℂ) * _ *
    mobiusThetaNativeCollarSource k m (Real.log ((n : ℝ) * |x|)))
  ring

/-- Absolute admission of the whole weighted arithmetic tail, at every positive native depth. -/
theorem summable_norm_mobiusThetaNativeSecondCollar_weighted
    (k p : ℕ) (m : ℕ+) {x : ℝ} (hx : x ≠ 0) :
    Summable (fun j : ℕ => ‖((moebius (p + j) : ℤ) : ℂ) *
      ((p + j : ℕ) : ℂ) ^ ((m : ℕ) - 1) *
        deningerLogPull (mobiusThetaNativeCollarSource k m)
          (((p + j : ℕ) : ℝ) * |x|)‖) := by
  have hs := (deningerMobiusRay_summable
    (DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m)).property
    (abs_pos.mpr hx)).norm
  have ht : Summable (fun j : ℕ => ‖((moebius (p + j) : ℤ) : ℂ) *
      deningerAdiabaticEvenLogPullDilation (mobiusThetaNativeSecondCollarSource k m)
        (p + j) x‖) := by
    simpa only [deningerAdiabaticEvenLogPullDilation, Nat.add_comm] using
      (_root_.summable_nat_add_iff p).2 hs
  simp_rw [mobiusThetaNativeSecondCollar_term k _ m hx, norm_mul] at ht
  have hcx : ((|x| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hx).ne'
  have hc : ‖(-1 : ℂ) ^ k‖ * ‖((|x| : ℝ) : ℂ) ^ ((m : ℕ) - 1)‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr (pow_ne_zero _ (by norm_num)))
      (norm_ne_zero_iff.mpr (pow_ne_zero _ hcx))
  simpa only [norm_mul] using (summable_mul_left_iff hc).mp ht

/-- The complete original second radial collar, retaining the original prime cutoff. -/
def mobiusThetaNativeSecondCollarTail (k p : ℕ) (m : ℕ+) (x : ℝ) : ℂ :=
  ∑' j : ℕ, ((moebius (p + j) : ℤ) : ℂ) *
    deningerAdiabaticEvenLogPullDilation (mobiusThetaNativeSecondCollarSource k m) (p + j) x

theorem mobiusThetaNativeSecondCollarTail_eq_weighted
    (k p : ℕ) (m : ℕ+) {x : ℝ} (hx : x ≠ 0) :
    mobiusThetaNativeSecondCollarTail k p m x =
      ((-1 : ℂ) ^ k * ((|x| : ℝ) : ℂ) ^ ((m : ℕ) - 1)) *
        ∑' j : ℕ, ((moebius (p + j) : ℤ) : ℂ) *
          ((p + j : ℕ) : ℂ) ^ ((m : ℕ) - 1) *
            deningerLogPull (mobiusThetaNativeCollarSource k m)
              (((p + j : ℕ) : ℝ) * |x|) := by
  simp_rw [mobiusThetaNativeSecondCollarTail, mobiusThetaNativeSecondCollar_term k _ m hx]
  exact tsum_mul_left

private def collarPrefix (h : DeningerMeyerSource) (p : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range p, ((moebius n : ℤ) : ℂ) *
    deningerAdiabaticEvenLogPullDilation h n x

private def collarTail (h : DeningerMeyerSource) (p : ℕ) (x : ℝ) : ℂ :=
  ∑' j : ℕ, ((moebius (p + j) : ℤ) : ℂ) *
    deningerAdiabaticEvenLogPullDilation h (p + j) x

private theorem prefix_integrable (h : DeningerMeyerSource) (p : ℕ) :
    Integrable (collarPrefix h p) := by
  apply integrable_finsetSum
  intro n _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (deningerAdiabaticEvenLogPullDilation_integrable h hn).const_mul _

private theorem collarTail_eq_sub_ae (h : DeningerMeyerSource) (p : ℕ) :
    collarTail h p =ᵐ[volume] (fun x =>
      deningerEvenPreimage (DeningerMeyerSource.toSource h) x - collarPrefix h p x) := by
  filter_upwards [deningerCompl_zero_ae_univ] with x hx
  have hxmem : x ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := hx.mpr (Set.mem_univ x)
  have hx0 : x ≠ 0 := by simpa using hxmem
  have hs := deningerMobiusRay_summable (DeningerMeyerSource.toSource h).property
    (abs_pos.mpr hx0)
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  simpa only [collarPrefix, collarTail, deningerEvenPreimage, deningerMobiusPreimage,
    deningerAdiabaticEvenLogPullDilation, Nat.add_comm] using hs.sum_add_tsum_nat_add p

private theorem collarTail_integrable (h : DeningerMeyerSource) (p : ℕ) :
    Integrable (collarTail h p) :=
  ((deningerEvenPreimage_integrable (DeningerMeyerSource.toSource h).property).sub
    (prefix_integrable h p)).congr (collarTail_eq_sub_ae h p).symm

/-- Absolute integrability of the whole second original radial collar. -/
theorem mobiusThetaNativeSecondCollarTail_integrable (k p : ℕ) (m : ℕ+) :
    Integrable (mobiusThetaNativeSecondCollarTail k p m) :=
  collarTail_integrable (mobiusThetaNativeSecondCollarSource k m) p

private theorem collarTail_distribution (h : DeningerMeyerSource) (p : ℕ) :
    deningerL1Distribution (collarTail_integrable h p) =
      deningerPreimageDistribution (DeningerMeyerSource.toSource h) -
        deningerL1Distribution (prefix_integrable h p) := by
  have hfull := deningerEvenPreimage_integrable (DeningerMeyerSource.toSource h).property
  have hprefix := prefix_integrable h p
  calc
    _ = deningerL1Distribution (hfull.sub hprefix) :=
      deningerL1Distribution_congr _ _ (collarTail_eq_sub_ae h p)
    _ = _ := by
      change (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 1)
        (MeasureTheory.Integrable.toL1 _ (hfull.sub hprefix)) =
          (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 1)
            (MeasureTheory.Integrable.toL1 _ hfull) -
          (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 1)
            (MeasureTheory.Integrable.toL1 _ hprefix)
      rw [MeasureTheory.Integrable.toL1_sub, map_sub]

/-- The complete two-collar boundary of the original prime-anchored source. -/
def mobiusThetaNativeFullCollarBoundary (k p : ℕ) (m : ℕ+) : 𝓢'(ℝ, ℂ) :=
  𝓕 (deningerL1Distribution (mobiusThetaNativeCollarTail_integrable k p m)) -
    deningerL1Distribution (mobiusThetaNativeSecondCollarTail_integrable k p m)

/-- The boundary of the retained finite prefix, on both actual native collars. -/
def mobiusThetaNativePrefixBoundary (k p : ℕ) (m : ℕ+) : 𝓢'(ℝ, ℂ) :=
  𝓕 (deningerL1Distribution (prefix_integrable (mobiusThetaNativeMeyerSource k m) p)) -
    deningerL1Distribution (prefix_integrable (mobiusThetaNativeSecondCollarSource k m) p)

/-- The original boundary differs from the all-integer commutator by exactly its full prefix. -/
theorem mobiusThetaNativeFullCollarBoundary_eq_commutator_sub_prefix
    (k p : ℕ) (m : ℕ+) :
    mobiusThetaNativeFullCollarBoundary k p m =
      deningerMobiusCommutator (DeningerMeyerSource.toSource (mobiusThetaNativeMeyerSource k m)) -
        mobiusThetaNativePrefixBoundary k p m := by
  have hfirst : deningerL1Distribution (mobiusThetaNativeCollarTail_integrable k p m) =
      deningerPreimageDistribution (DeningerMeyerSource.toSource (mobiusThetaNativeMeyerSource k m)) -
        deningerL1Distribution (prefix_integrable (mobiusThetaNativeMeyerSource k m) p) :=
    collarTail_distribution (mobiusThetaNativeMeyerSource k m) p
  have hsecond := collarTail_distribution (mobiusThetaNativeSecondCollarSource k m) p
  change deningerL1Distribution (mobiusThetaNativeSecondCollarTail_integrable k p m) = _ at hsecond
  rw [mobiusThetaNativeFullCollarBoundary, hfirst, hsecond, deningerFourier_sub,
    mobiusThetaNativePrefixBoundary, deningerMobiusCommutator]
  simp only [mobiusThetaNativeSecondCollarSource, deningerMeyerCollarExchange_toSource]
  abel

/-- The existing Gamma transgression of the unchanged source retains the complete prefix boundary. -/
theorem mobiusThetaNativeFullCollarBoundary_gamma_transgression
    (k p : ℕ) (m : ℕ+) :
    deningerAdiabaticGammaBoundary (mobiusThetaNativeMeyerSource k m) -
      mobiusThetaNativeFullCollarBoundary k p m =
        deningerAdiabaticGreenStokesTransgression (mobiusThetaNativeMeyerSource k m) +
          mobiusThetaNativePrefixBoundary k p m := by
  rw [mobiusThetaNativeFullCollarBoundary_eq_commutator_sub_prefix,
    deningerAdiabaticGreenStokesTransgression]
  abel

/-- The native Mellin reflection induced by the original collar exchange. -/
def mobiusThetaNativeCollarDualParameter (m : ℕ+) (v : ℂ) : ℂ :=
  -v + I * ((1 - (m : ℝ)⁻¹ : ℝ) : ℂ)

theorem mobiusThetaNativeCollarDualParameter_centered (m : ℕ+) (v : ℂ) :
    (m : ℂ) * mobiusThetaCenteredParameter (mobiusThetaNativeCollarDualParameter m v) =
      1 - (m : ℂ) * mobiusThetaCenteredParameter v := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hshift : I * (I * ((1 - (m : ℝ)⁻¹ : ℝ) : ℂ)) = (m : ℂ)⁻¹ - 1 := by
    push_cast
    calc
      _ = I ^ 2 * (1 - (m : ℂ)⁻¹) := by ring
      _ = _ := by rw [I_sq]; ring
  have hid : I * (-v + I * ((1 - (m : ℝ)⁻¹ : ℝ) : ℂ)) =
      -I * v + ((m : ℂ)⁻¹ - 1) := by
    rw [mul_add, mul_neg, hshift]
    ring
  dsimp only [mobiusThetaNativeCollarDualParameter, mobiusThetaCenteredParameter]
  calc
    _ = (m : ℂ) * ((m : ℂ)⁻¹ - (1 / 2 + I * v)) := by rw [hid]; ring
    _ = _ := by rw [mul_sub, mul_inv_cancel₀ hm]

/-- The whole exchanged source has the shifted native Xi transform, with absolute admission. -/
theorem mobiusThetaNativeSecondCollarSource_mellin_data
    (k : ℕ) (m : ℕ+) {v : ℂ}
    (hv : |(mobiusThetaNativeCollarDualParameter m v).im| < 1) :
    Integrable (fun t : ℝ =>
      Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter v) * (t : ℂ)) *
        ((DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m) :
          SchwartzMap ℝ ℂ)) t) ∧
    (∫ t : ℝ,
      Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter v) * (t : ℂ)) *
        ((DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m) :
          SchwartzMap ℝ ℂ)) t) =
      (m : ℂ)⁻¹ * iteratedDeriv k XiC (mobiusThetaNativeCollarDualParameter m v) := by
  have hdata := mobiusThetaNativeCollarSource_mellin_data k m hv
  have heq : (fun t : ℝ =>
      Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter v) * (t : ℂ)) *
        ((DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m) :
          SchwartzMap ℝ ℂ)) t) =
      fun t : ℝ =>
        Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter
          (mobiusThetaNativeCollarDualParameter m v)) * ((-t : ℝ) : ℂ)) *
            mobiusThetaNativeCollarSource k m (-t) := by
    funext t
    change Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter v) * (t : ℂ)) *
      ((Real.exp (-t) : ℂ) * mobiusThetaNativeCollarSource k m (-t)) = _
    rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add,
      mobiusThetaNativeCollarDualParameter_centered]
    congr 2
    push_cast
    ring
  rw [heq]
  refine ⟨hdata.1.comp_neg, ?_⟩
  exact (integral_neg_eq_self
    (fun t : ℝ => Complex.exp (((m : ℂ) *
      mobiusThetaCenteredParameter (mobiusThetaNativeCollarDualParameter m v)) *
        (t : ℂ)) * mobiusThetaNativeCollarSource k m t)
    volume).trans hdata.2

end RHTower
