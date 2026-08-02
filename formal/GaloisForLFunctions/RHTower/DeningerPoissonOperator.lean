import GaloisForLFunctions.RHTower.DeningerRadialNuclear
import GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzPoisson
import GaloisForLFunctions.HTGeometry.SchwartzEulerOperator

/-!
# The Poisson operator on Meyer's space: values and decay

The Poisson operator of the card is `Zf(a) = ∑_{n≥1} f(na)`.  For an even Schwartz function
vanishing at the origin it is half the full integer lattice trace, so the signed Poisson estimates
already proved for that trace apply to it: with `f(0) = 0` and `f̂(0) = 0` the sum decays faster
than every power of `a` at both multiplicative ends.

Meyer's space is stable under the Euler operator — the generator of the multiplicative flow — so
the same estimates apply to every multiplicative derivative of `Zf`, which is what the membership
in the radial space needs.

* `deningerPoissonValue` : the Poisson sum.
* `deningerPoissonValue_eq_half_latticeTrace` : **it is half the lattice trace.**
* `deningerMeyerCap_eulerSCLM` : **Meyer's space is stable under the Euler operator.**
* `norm_deningerPoissonValue_le_large`, `_small` : **arbitrary-power decay at both ends.**
-/

open scoped Real SchwartzMap FourierTransform
open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## Stability of Meyer's space under the Euler operator -/

/-- **Meyer's space is stable under the Euler operator.**  The value at the origin is killed by
the factor `x`, the parity is preserved, and the Fourier rule `𝓕(θf) = −𝓕f − θ𝓕f` sends the
Fourier constraint to itself. -/
theorem deningerMeyerCap_eulerSCLM {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) :
    eulerSCLM f ∈ DeningerMeyerCap := by
  obtain ⟨he, h0, hF⟩ := (deningerMeyerCap_mem_iff f).mp hf
  have hFs : fourierSCLM f 0 = 0 := by
    have hcle : (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) f) = fourierSCLM f := by
      rw [FourierTransform.fourierCLE_apply, fourierSCLM_eq]
    rw [← hcle]
    exact hF
  refine (deningerMeyerCap_mem_iff _).mpr ⟨eulerSCLM_even he, eulerSCLM_apply_zero f, ?_⟩
  have hcle : (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) (eulerSCLM f))
      = fourierSCLM (eulerSCLM f) := by
    rw [FourierTransform.fourierCLE_apply, fourierSCLM_eq]
  rw [hcle, fourierSCLM_eulerSCLM_zero, hFs, neg_zero]

/-! ## The Poisson sum -/

/-- **The Poisson operator of the card**, `Zf(a) = ∑_{n≥1} f(na)`. -/
def deningerPoissonValue (f : 𝓢(ℝ, ℂ)) (a : ℝ) : ℂ := ∑' n : ℕ, f (a * ((n : ℝ) + 1))

theorem summable_deningerPoissonTerm (f : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : a ≠ 0) :
    Summable fun n : ℕ => f (a * ((n : ℝ) + 1)) := by
  have hZ : Summable fun n : ℤ => f (a * (n : ℝ)) :=
    ccmRationalArchimedeanLatticeTrace_summable f ha
  have hinj : Function.Injective (fun n : ℕ => ((n : ℤ) + 1)) := by
    intro m n hmn
    have h1 : (m : ℤ) + 1 = (n : ℤ) + 1 := hmn
    have h2 : (m : ℤ) = (n : ℤ) := by omega
    exact_mod_cast h2
  have hcomp := hZ.comp_injective hinj
  refine hcomp.congr fun n => ?_
  show f (a * (((n : ℤ) + 1 : ℤ) : ℝ)) = f (a * ((n : ℝ) + 1))
  push_cast
  ring_nf

/-- The negative half of the lattice repeats the positive half, for an even function. -/
theorem tsum_neg_eq_of_even {f : 𝓢(ℝ, ℂ)} (he : ∀ x : ℝ, f (-x) = f x) (a : ℝ) :
    (∑' n : ℕ, f (a * ((-((n : ℝ) + 1)) : ℝ))) = ∑' n : ℕ, f (a * ((n : ℝ) + 1)) := by
  refine tsum_congr fun n => ?_
  have hneg : a * ((-((n : ℝ) + 1)) : ℝ) = -(a * ((n : ℝ) + 1)) := by ring
  rw [hneg, he]

/-- **The Poisson sum is half the lattice trace**, for an even function vanishing at the
origin. -/
theorem deningerPoissonValue_eq_half_latticeTrace {f : 𝓢(ℝ, ℂ)}
    (he : ∀ x : ℝ, f (-x) = f x) (h0 : f 0 = 0) {a : ℝ} (ha : a ≠ 0) :
    ccmRationalArchimedeanLatticeTrace f a = 2 * deningerPoissonValue f a := by
  have hsum := summable_deningerPoissonTerm f ha
  have hnat : Summable fun n : ℕ => f (a * ((n : ℤ) : ℝ)) := by
    have hshift : Summable fun n : ℕ => f (a * (((n + 1 : ℕ) : ℤ) : ℝ)) := by
      refine hsum.congr fun n => ?_
      push_cast
      ring_nf
    exact (summable_nat_add_iff 1).mp hshift
  have hneg : Summable fun n : ℕ => f (a * ((-((n : ℤ) + 1) : ℤ) : ℝ)) := by
    refine hsum.congr fun n => ?_
    have hval : a * ((-((n : ℤ) + 1) : ℤ) : ℝ) = -(a * ((n : ℝ) + 1)) := by
      push_cast
      ring
    rw [hval, he]
  have hsplit := tsum_of_nat_of_neg_add_one (f := fun n : ℤ => f (a * (n : ℝ))) hnat hneg
  rw [ccmRationalArchimedeanLatticeTrace, hsplit]
  have hpos : (∑' n : ℕ, f (a * ((n : ℤ) : ℝ))) = deningerPoissonValue f a := by
    rw [deningerPoissonValue]
    have hzero := hnat.tsum_eq_zero_add
    rw [hzero]
    have hfirst : f (a * (((0 : ℕ) : ℤ) : ℝ)) = 0 := by
      have : a * (((0 : ℕ) : ℤ) : ℝ) = 0 := by push_cast; ring
      rw [this, h0]
    rw [hfirst, zero_add]
    refine tsum_congr fun n => ?_
    push_cast
    ring_nf
  have hnegsum : (∑' n : ℕ, f (a * ((-((n : ℤ) + 1) : ℤ) : ℝ))) = deningerPoissonValue f a := by
    rw [deningerPoissonValue]
    refine tsum_congr fun n => ?_
    have hval : a * ((-((n : ℤ) + 1) : ℤ) : ℝ) = -(a * ((n : ℝ) + 1)) := by
      push_cast
      ring
    rw [hval, he]
  rw [hpos, hnegsum]
  ring

/-! ## Two-ended decay of the Poisson sum -/

/-- **Arbitrary-power decay of the Poisson sum at the large end**, from the vanishing of the value
at the origin. -/
theorem norm_deningerPoissonValue_le_large {f : 𝓢(ℝ, ℂ)} (he : ∀ x : ℝ, f (-x) = f x)
    (h0 : f 0 = 0) (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖deningerPoissonValue f a‖
      ≤ ccmRationalArchimedeanDecayConstant f N
        / a ^ ccmRationalArchimedeanDecayExponent N / 2 := by
  have hhalf := deningerPoissonValue_eq_half_latticeTrace he h0 ha.ne'
  have hbound := ccmRationalArchimedeanLatticeTrace_large_bound f h0 N ha
  rw [hhalf, norm_mul] at hbound
  have hnorm : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm] at hbound
  linarith [hbound]

/-- **Arbitrary-power decay of the Poisson sum at the small end**, from the vanishing of the
Fourier transform at the origin: this is the signed Poisson estimate. -/
theorem norm_deningerPoissonValue_le_small {f : 𝓢(ℝ, ℂ)} (he : ∀ x : ℝ, f (-x) = f x)
    (h0 : f 0 = 0) (hF : (𝓕 (f : ℝ → ℂ)) 0 = 0) (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ‖deningerPoissonValue f a‖
      ≤ ccmRationalArchimedeanDecayConstant (𝓕 f) N
        * a ^ (ccmRationalArchimedeanDecayExponent N - 1) / 2 := by
  have hhalf := deningerPoissonValue_eq_half_latticeTrace he h0 ha.ne'
  have hbound := ccmRationalArchimedeanLatticeTrace_small_bound f hF N ha
  rw [hhalf, norm_mul] at hbound
  have hnorm : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm] at hbound
  linarith [hbound]

end RHTower

end
