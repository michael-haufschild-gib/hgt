import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFirstOverlapStepHoldsAtEveryBlockSize
import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstOverlapWindowHasAPositiveWeilFloorAtEveryBlockSize

/-!
# One certified floor in the continuum and on windows

The constant `1/50000` applies to every aperture at most `1881/5000`.
The corresponding finite windows have ratio at most `10609/5000` and
prime cutoff at least two. The same certificate supplies step-packet
positivity, the charge-free neutral gap and the index of the dressed middle.
-/

noncomputable section

open Finset Matrix MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-- Restricting the support preserves the certified real Weil floor. -/
theorem weilFloor_of_aperture_le_firstStep {A : ℝ} (hA : A ≤ 1881 / 5000) :
    WeilFloor A (1 / 50000) := by
  have h := WeilFloor.of_even_of_odd evenWeilFloor_firstStep
    (oddWeilFloor_firstStep.mono (by norm_num))
  intro F hF hs
  exact h F hF (hs.trans fun x hx =>
    ⟨by linarith only [hx.1, hA], by linarith only [hx.2, hA]⟩)

/-- The same support restriction gives the complex floor, with no parity condition. -/
theorem complexWeilFloor_of_aperture_le_firstStep {A : ℝ} (hA : A ≤ 1881 / 5000)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Icc (-A) A) :
    (1 / 50000 : ℝ) * (∫ x, ‖f x‖ ^ 2) ≤ (Zeta23.zetaZeroConfig.W f f).re :=
  WindowTowerOfSpecZ.zetaZeroConfig_re_W_ge_at_aperture_1881_over_5000 hf
    (hs.trans fun x hx =>
      ⟨by linarith only [hx.1, hA], by linarith only [hx.2, hA]⟩)

/-- The continuum certificate: real tests, complex tests and the closed-form ground energy. -/
theorem firstStep_continuum_certificate (A : _root_.RHTower.SuzukiPositiveAperture)
    (hA : A.1 ≤ 1881 / 5000) :
    WeilFloor A.1 (1 / 50000) ∧
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A.1) A.1 →
      (1 / 50000 : ℝ) * (∫ x, ‖f x‖ ^ 2) ≤ (Zeta23.zetaZeroConfig.W f f).re) ∧
    (1 / 50000 : ℝ) ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy A :=
  ⟨weilFloor_of_aperture_le_firstStep hA,
    fun _ hf hs => complexWeilFloor_of_aperture_le_firstStep hA hf hs,
    WindowTowerOfSpecZ.one_div_50000_le_groundEnergy_of_aperture_le_1881_over_5000 hA⟩

/-- The discrete certificate, uniform in block size and every cutoff `Q ≥ 2`. -/
theorem firstStep_window_certificate {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hJ : 5000 * (R + J) ≤ 10609 * R) :
    (∀ σ : ℕ → ℝ, (1 / 50000 : ℝ) * ∑ j ∈ range J, σ j ^ 2 ≤
      packetForm Q (stepPacket R J σ)) ∧
    (∀ σ : ℕ → ℝ, (1 / 50000 : ℝ) * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l)) ∧
    (∀ z : Fin J → ℝ, ∑ i, z i = 0 →
      1 / 50000 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z)) ∧
    HasGap (neutralWindow Q R J) (1 / 50000) ∧
    (R ≤ J → hermNegIndex ((neutralWindow Q R J).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) = 1) :=
  ⟨WindowTowerOfSpecZ.packetForm_stepPacket_ge_of_first_overlap hR hJ hQ,
    WindowTowerOfSpecZ.sum_blockMatrix_ge_of_first_overlap hR hJ hQ,
    neutralWindow_floor_firstStep hQ hR hJ,
    hasGap_neutralWindow_firstStep hQ hR hJ,
    fun hRJ => hermNegIndex_neutralWindow_firstStep hQ hR hRJ hJ⟩

/-- Both end attractions retain one bound state and the full signed Green inequality. -/
theorem firstStep_dressed_certificate {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) :
    hermNegIndex ((dressedMiddle Q R a b).map (↑) :
      Matrix (Fin (R + a)) (Fin (R + a)) ℂ) = 1 ∧
    (∀ e : Fin a ⊕ Fin b → ℝ,
      (endCoupling Q R a b *ᵥ e) ⬝ᵥ
          (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) +
          1 / 50000 * (e ⬝ᵥ e) ≤
        e ⬝ᵥ (endForm Q R a b *ᵥ e) +
          (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 /
            bindingEnergy (R + a)) :=
  ⟨hermNegIndex_dressedMiddle_firstStep hQ hR ha hb,
    greenForm_firstStep hQ hR ha hb⟩

#print axioms firstStep_continuum_certificate
#print axioms firstStep_window_certificate
#print axioms firstStep_dressed_certificate

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
