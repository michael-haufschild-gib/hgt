import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonOperator

/-!
# The Poisson operator intertwines Fourier with multiplicative inversion

Meyer's space is stable under the Fourier transform: an even function stays even, the value at the
origin of the transform is the second constraint, and the value at the origin of the double
transform is the first, by Fourier inversion.

For such a function the Poisson sum is half the lattice trace, and the scaled Poisson identity for
the lattice trace becomes

`Zf(a) = a⁻¹·Z(𝓕f)(a⁻¹)`.

So the Poisson operator carries the Fourier involution to multiplicative inversion — the source of
the functional equation in this picture, and the reason the two boundary constraints of Meyer's
space are exactly the two that make the identity boundary-term free.

* `deningerMeyerCap_fourierSCLM` : **Meyer's space is stable under the Fourier transform.**
* `deningerPoissonValue_fourier_reflection` : **`Zf(a) = a⁻¹Z(𝓕f)(a⁻¹)`.**
-/

open scoped Real SchwartzMap FourierTransform
open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## Stability of Meyer's space under Fourier -/

theorem fourierSCLM_even {f : 𝓢(ℝ, ℂ)} (hf : ∀ x : ℝ, f (-x) = f x) (x : ℝ) :
    fourierSCLM f (-x) = fourierSCLM f x := by
  have hfun : (fun y : ℝ => (f : ℝ → ℂ) (-y)) = (f : ℝ → ℂ) := funext hf
  have h1 : 𝓕 (f : ℝ → ℂ) (-x) = 𝓕⁻ (f : ℝ → ℂ) x :=
    (Real.fourierInv_eq_fourier_neg (f : ℝ → ℂ) x).symm
  have h2 : 𝓕⁻ (f : ℝ → ℂ) = 𝓕 (fun y : ℝ => (f : ℝ → ℂ) (-y)) :=
    Real.fourierInv_eq_fourier_comp_neg (f : ℝ → ℂ)
  show 𝓕 (f : ℝ → ℂ) (-x) = 𝓕 (f : ℝ → ℂ) x
  rw [h1, h2, hfun]

theorem fourierSCLM_fourierSCLM_zero (f : 𝓢(ℝ, ℂ)) :
    fourierSCLM (fourierSCLM f) 0 = f 0 := by
  have hinv : 𝓕⁻ (𝓕 (f : ℝ → ℂ)) = (f : ℝ → ℂ) :=
    f.continuous.fourierInv_fourier_eq f.integrable (𝓕 f).integrable
  have hval : 𝓕⁻ (𝓕 (f : ℝ → ℂ)) 0 = 𝓕 (𝓕 (f : ℝ → ℂ)) (-0) :=
    Real.fourierInv_eq_fourier_neg (𝓕 (f : ℝ → ℂ)) 0
  show 𝓕 (𝓕 (f : ℝ → ℂ)) 0 = f 0
  rw [neg_zero] at hval
  rw [← hval, hinv]

/-- **Meyer's space is stable under the Fourier transform.** -/
theorem deningerMeyerCap_fourierSCLM {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) :
    fourierSCLM f ∈ DeningerMeyerCap := by
  obtain ⟨he, h0, hF⟩ := (deningerMeyerCap_mem_iff f).mp hf
  have hFs : fourierSCLM f 0 = 0 := by
    have hcle : (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) f) = fourierSCLM f := by
      rw [FourierTransform.fourierCLE_apply, fourierSCLM_eq]
    rw [← hcle]
    exact hF
  refine (deningerMeyerCap_mem_iff _).mpr ⟨fourierSCLM_even he, hFs, ?_⟩
  have hcle : (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) (fourierSCLM f))
      = fourierSCLM (fourierSCLM f) := by
    rw [FourierTransform.fourierCLE_apply, fourierSCLM_eq]
    rfl
  rw [hcle, fourierSCLM_fourierSCLM_zero, h0]

/-! ## The reflection identity -/

/-- **The Poisson operator carries the Fourier involution to multiplicative inversion.** -/
theorem deningerPoissonValue_fourier_reflection {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap)
    {a : ℝ} (ha : 0 < a) :
    deningerPoissonValue f a
      = ((a⁻¹ : ℝ) : ℂ) * deningerPoissonValue (fourierSCLM f) a⁻¹ := by
  obtain ⟨he, h0, _⟩ := (deningerMeyerCap_mem_iff f).mp hf
  have hFmem := deningerMeyerCap_fourierSCLM hf
  obtain ⟨heF, h0F, _⟩ := (deningerMeyerCap_mem_iff _).mp hFmem
  have hainv : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha
  have hhalf := deningerPoissonValue_eq_half_latticeTrace he h0 ha.ne'
  have hhalfF : ccmRationalArchimedeanLatticeTrace (fourierSCLM f) a⁻¹
      = 2 * deningerPoissonValue (fourierSCLM f) a⁻¹ :=
    deningerPoissonValue_eq_half_latticeTrace heF h0F hainv.ne'
  have hpoisson := ccmRationalArchimedeanLatticeTrace_poisson f ha
  have hfourier : ccmRationalArchimedeanLatticeTrace (𝓕 f) a⁻¹
      = ccmRationalArchimedeanLatticeTrace (fourierSCLM f) a⁻¹ := by
    rw [fourierSCLM_eq]
  rw [hfourier, hhalfF, hhalf] at hpoisson
  have hcast : ((a⁻¹ : ℝ) : ℂ) = (a : ℂ)⁻¹ := by
    push_cast
    ring
  rw [hcast]
  linear_combination hpoisson / 2

end RHTower

end
