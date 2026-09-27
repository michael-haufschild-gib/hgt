import GaloisForLFunctions.RHTower.ThetaFinitePrimeAtomPolarization

/-!
# Exact ground coordinates for real compact physical sources

Dividing a smooth compact real function by the positive theta source gives a
compact Schwartz profile. Its ground mass is exactly the physical square
integral. Matched physical translates saturate the cross-correlation mass
bound at their translation lag.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

def thetaCompactRealGroundProfile (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) : 𝓢(ℝ, ℝ) :=
  (show HasCompactSupport (fun x => f x * (thetaCuspFullSource x)⁻¹) from hc.mul_right).toSchwartzMap
    (hf.mul (contDiff_thetaCuspFullSource.inv (fun x =>
      (show 0 < thetaCuspFullSource x from thetaCuspTiltSource.pos x).ne')))

@[simp] theorem thetaCompactRealGroundProfile_apply (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (x : ℝ) :
    thetaCompactRealGroundProfile f hf hc x = f x / thetaCuspFullSource x := by
  rfl

theorem thetaCompactRealGroundProfile_reconstruct (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (x : ℝ) :
    thetaCuspFullSource x * thetaCompactRealGroundProfile f hf hc x = f x := by
  rw [thetaCompactRealGroundProfile_apply]
  exact mul_div_cancel₀ _ (show thetaCuspFullSource x ≠ 0 from (thetaCuspTiltSource.pos x).ne')

theorem support_thetaCompactRealGroundProfile (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    Function.support (thetaCompactRealGroundProfile f hf hc) = Function.support f := by
  ext x
  have hk : thetaCuspFullSource x ≠ 0 := (thetaCuspTiltSource.pos x).ne'
  simp only [Function.mem_support, thetaCompactRealGroundProfile_apply,
    div_ne_zero_iff]
  exact ⟨And.left, fun hx => ⟨hx, hk⟩⟩

theorem hasCompactSupport_thetaCompactRealGroundProfile (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    HasCompactSupport (thetaCompactRealGroundProfile f hf hc) := by
  apply hc.mono
  rw [support_thetaCompactRealGroundProfile]

theorem thetaGroundNormSq_compactRealGroundProfile (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    thetaGroundNormSq (thetaComplexify (thetaCompactRealGroundProfile f hf hc)) =
      ∫ x : ℝ, f x ^ 2 := by
  unfold thetaGroundNormSq
  apply integral_congr_ae
  filter_upwards with x
  simp only [thetaGroundNormDensity, thetaComplexify_apply, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, ← mul_pow, thetaCompactRealGroundProfile_reconstruct]

theorem thetaGroundShiftCross_matched_physical_translate
    (f g : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (d : ℝ)
    (hmatch : ∀ x, g (x + d) = f x) :
    thetaGroundShiftCross (thetaCompactRealGroundProfile f hf hfc)
        (thetaCompactRealGroundProfile g hg hgc) d =
      thetaGroundNormSq (thetaComplexify (thetaCompactRealGroundProfile f hf hfc)) := by
  rw [thetaGroundShiftCross, thetaGroundNormSq_compactRealGroundProfile]
  simp_rw [thetaCompactRealGroundProfile_reconstruct, hmatch, ← pow_two]

theorem thetaGroundNormSq_matched_physical_translate
    (f g : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (d : ℝ)
    (hmatch : ∀ x, g (x + d) = f x) :
    thetaGroundNormSq (thetaComplexify (thetaCompactRealGroundProfile g hg hgc)) =
      thetaGroundNormSq (thetaComplexify (thetaCompactRealGroundProfile f hf hfc)) := by
  rw [thetaGroundNormSq_compactRealGroundProfile, thetaGroundNormSq_compactRealGroundProfile,
    ← integral_add_right_eq_self (fun x : ℝ => g x ^ 2) d]
  simp_rw [hmatch]

end RHTower.ThetaSourceWard
