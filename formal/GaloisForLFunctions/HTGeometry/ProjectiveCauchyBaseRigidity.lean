import GaloisForLFunctions.HTGeometry.BlockDiagonalAnnihilator
import GaloisForLFunctions.HTGeometry.SignedCauchyJetDetection
import GaloisForLFunctions.HTGeometry.ProjectiveCauchyDensityControl

/-!
# Rigidity of the projective Cauchy powers

The base kernel of the Nevanlinna jet expansion is a Cauchy power on the projective real line.  It
vanishes at the point at infinity, and on the real points it is literally the affine Cauchy jet
kernel, so a packet annihilating it on the reals annihilates the affine jet form.

Rigidity therefore transfers from the affine statement: at distinct upper-half-plane nodes, against
a measure of infinite support, an almost-everywhere vanishing real part forces every coefficient to
vanish.  The point at infinity contributes nothing, since the kernel is zero there.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- **Rigidity of the projective Cauchy powers, node-indexed form.**  On the real points the
projective Cauchy power is the affine Cauchy jet kernel, so the affine detection theorem applies. -/
theorem projectiveCauchyPower_coeff_eq_zero_of_ae_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : Measure ℝ} (hsupp : ν.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ)
    (hzero : ∀ᵐ r : ℝ ∂ν,
      (∑ i, ∑ j : Fin (n i),
        c i j * projectiveCauchyPower (x i) j.1 (r : OnePoint ℝ)).re = 0) :
    ∀ i j, c i j = 0 := by
  refine cauchyJet_coeff_eq_zero_of_ae_re hsupp x hx hupper n c ?_
  filter_upwards [hzero] with r hr
  rw [cauchyJetForm]
  simpa using hr

/-- **Rigidity of the projective Cauchy powers, packet form.**  The same statement with the jet
coordinates flattened into the sigma index used by the kernel control maps. -/
theorem projectiveCauchyPower_sigma_coeff_eq_zero_of_ae_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : Measure ℝ} (hsupp : ν.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (d : (Σ i, Fin (n i)) → ℂ)
    (hzero : ∀ᵐ r : ℝ ∂ν,
      (∑ k : Σ i, Fin (n i),
        d k * projectiveCauchyPower (x k.1) k.2.1 (r : OnePoint ℝ)).re = 0) :
    ∀ k, d k = 0 := by
  have hcoeff := projectiveCauchyPower_coeff_eq_zero_of_ae_re hsupp x hx hupper n
    (fun i j => d ⟨i, j⟩) ?_
  · rintro ⟨i, j⟩
    exact hcoeff i j
  · filter_upwards [hzero] with r hr
    rwa [Fintype.sum_sigma] at hr

end

end GaloisForLFunctions.HTGeometry
