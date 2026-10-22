import GaloisForLFunctions.RHTower.ThetaArithmeticModulusObstruction
import GaloisForLFunctions.RHTower.CCM.CCMThetaThreeEnergyComparison

/-!
# Modulus contraction fails in the literal smooth CCM source space

Compact theta profiles reconstruct strict-interior CCM sources. The complete
arithmetic modulus obstruction therefore applies to the actual restricted
Weil quadratic, with equal physical mass and every scalar shift. No negative
quadratic value is inferred from this comparison.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

/-- Reconstruction in the direction opposite to division by the theta ground source. -/
def ccmThetaSourceOfCompactRealProfile (a : SuzukiPositiveAperture)
    (phi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Ioo (-a.1) a.1) : CCMComplexSmoothInteriorSource a where
  toFun x := (thetaCuspFullSource x : ℂ) * (phi x : ℂ)
  smooth := (Complex.ofRealCLM.contDiff.comp contDiff_thetaCuspFullSource).mul
    (Complex.ofRealCLM.contDiff.comp (phi.smooth ⊤))
  hasCompactSupport := hc.mono (by
    intro x hx hz
    exact hx (by simp only [hz, Complex.ofReal_zero, mul_zero]))
  tsupport_subset := by
    apply (closure_mono (show Function.support
      (fun x => (thetaCuspFullSource x : ℂ) * (phi x : ℂ)) ⊆ Function.support phi from ?_)).trans hs
    intro x hx hz
    exact hx (by simp only [hz, Complex.ofReal_zero, mul_zero])

@[simp] theorem ccmThetaSourceOfCompactRealProfile_apply
    (a : SuzukiPositiveAperture) (phi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Ioo (-a.1) a.1) (x : ℝ) :
    ccmThetaSourceOfCompactRealProfile a phi hc hs x =
      (thetaCuspFullSource x : ℂ) * (phi x : ℂ) := rfl

theorem ccmThetaGroundProfile_ofCompactRealProfile
    (a : SuzukiPositiveAperture) (phi : 𝓢(ℝ, ℝ)) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Ioo (-a.1) a.1) :
    ccmThetaGroundProfile (ccmThetaSourceOfCompactRealProfile a phi hc hs) =
      thetaComplexify phi := by
  ext x
  rw [ccmThetaGroundProfile_apply, ccmThetaSourceOfCompactRealProfile_apply,
    thetaComplexify_apply]
  have hk : (thetaCuspFullSource x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (thetaCuspTiltSource.pos x).ne'
  field_simp

/-- The full restricted Weil form admits a smooth compact modulus-increase witness.
One fixed pair defeats every scalar mass shift. -/
theorem exists_ccmSmooth_modulus_increase :
    ∃ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a),
      (∀ x, v x = (‖u x‖ : ℂ)) ∧
      ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 =
        ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 ∧
      ∀ c : ℝ,
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector +
            c * ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 <
          ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector +
            c * ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 := by
  obtain ⟨f, g, hfc, hgc, habs, hmass, hlt⟩ :=
    exists_compact_thetaArithmetic_modulus_increase
  have hcompact : IsCompact (tsupport f ∪ tsupport g) := hfc.union hgc
  obtain ⟨A, hA, hbound⟩ := hcompact.isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hfsub : tsupport f ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inl hx))
  have hgsub : tsupport g ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inr hx))
  let u := ccmThetaSourceOfCompactRealProfile a f hfc hfsub
  let v := ccmThetaSourceOfCompactRealProfile a g hgc hgsub
  have hu : ccmThetaGroundProfile u = thetaComplexify f :=
    ccmThetaGroundProfile_ofCompactRealProfile a f hfc hfsub
  have hv : ccmThetaGroundProfile v = thetaComplexify g :=
    ccmThetaGroundProfile_ofCompactRealProfile a g hgc hgsub
  have hmu : ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 =
      thetaGroundNormSq (thetaComplexify f) := by
    rw [← thetaGroundNormSq_ccmProfile_eq_physical, hu]
  have hmv : ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 =
      thetaGroundNormSq (thetaComplexify g) := by
    rw [← thetaGroundNormSq_ccmProfile_eq_physical, hv]
  refine ⟨a, u, v, ?_, ?_, ?_⟩
  · intro x
    change (thetaCuspFullSource x : ℂ) * (g x : ℂ) =
      (‖(thetaCuspFullSource x : ℂ) * (f x : ℂ)‖ : ℂ)
    rw [habs, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (show 0 < thetaCuspFullSource x from thetaCuspTiltSource.pos x),
      Complex.ofReal_mul]
  · rw [hmu, hmv]
    exact hmass
  · intro c
    rw [ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic,
      ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic, hu, hv, hmu, hmv]
    exact hlt c

theorem not_ccmSmooth_modulus_contracts (c : ℝ) :
    ¬ ∀ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a),
      (∀ x, v x = (‖u x‖ : ℂ)) →
        ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector +
            c * ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 ≤
          ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector +
            c * ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 := by
  obtain ⟨a, u, v, habs, _, hlt⟩ := exists_ccmSmooth_modulus_increase
  intro h
  exact (not_le_of_gt (hlt c)) (h a u v habs)

/-- A local continuous potential has a finite quadratic pairing on each compact source. -/
def ccmSmoothLocalPotentialEnergy {a : SuzukiPositiveAperture}
    (V : C(ℝ, ℝ)) (u : CCMComplexSmoothInteriorSource a) : ℝ :=
  ∫ x : ℝ, V x * ‖u x‖ ^ 2

theorem integrable_ccmSmoothLocalPotentialDensity {a : SuzukiPositiveAperture}
    (V : C(ℝ, ℝ)) (u : CCMComplexSmoothInteriorSource a) :
    Integrable (fun x : ℝ => V x * ‖u x‖ ^ 2) := by
  apply (V.continuous.mul (u.continuous.norm.pow 2)).integrable_of_hasCompactSupport
  apply u.hasCompactSupport.mono
  intro x hx hz
  exact hx (by simp [hz])

/-- The same compact pair obstructs modulus contraction after every continuous local potential.
Thus a local multiplication correction cannot remove the arithmetic cross obstruction. -/
theorem exists_ccmSmooth_modulus_increase_all_local_potentials :
    ∃ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a),
      (∀ x, v x = (‖u x‖ : ℂ)) ∧
      ∀ V : C(ℝ, ℝ),
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector +
            ccmSmoothLocalPotentialEnergy V u <
          ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector +
            ccmSmoothLocalPotentialEnergy V v := by
  obtain ⟨a, u, v, habs, _, hlt⟩ := exists_ccmSmooth_modulus_increase
  refine ⟨a, u, v, habs, fun V => ?_⟩
  have heq : ccmSmoothLocalPotentialEnergy V u = ccmSmoothLocalPotentialEnergy V v := by
    unfold ccmSmoothLocalPotentialEnergy
    apply integral_congr_ae
    filter_upwards with x
    rw [habs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [heq]
  have hzero := hlt 0
  linarith

end RHTower
