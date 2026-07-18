import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Real functionals on a complex jet space

A complex jet space `σ → ℂ` carries two linear structures.  Annihilation arguments produce a
*real*-linear functional, while the Cauchy-jet detectors consume a *complex* coefficient packet.
This module supplies the dictionary between them.

Every real-linear functional on a finite complex jet space is the real part of a complex pairing,

```text
φ v = Re (∑ s, c s * v s),
```

with the coefficients recovered by testing on the two real directions of each coordinate,

```text
c s = φ (single s 1) - I * φ (single s I).
```

Consequently a real-linear functional vanishes exactly when its coefficient packet does, which is
what converts "no real functional annihilates the range" into a statement the signed Cauchy-jet
detector can refute.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The complex coefficient packet of a real-linear functional on a complex jet space. -/
def realFunctionalCoefficients (φ : (σ → ℂ) →ₗ[ℝ] ℝ) (s : σ) : ℂ :=
  (φ (Pi.single s 1) : ℂ) - Complex.I * (φ (Pi.single s Complex.I) : ℂ)

omit [Fintype σ] in
/-- On a single coordinate direction the coefficient pairing reproduces the functional. -/
theorem re_realFunctionalCoefficients_mul (φ : (σ → ℂ) →ₗ[ℝ] ℝ) (s : σ) (z : ℂ) :
    (realFunctionalCoefficients φ s * z).re = φ (Pi.single s z) := by
  have hz : Pi.single s z =
      z.re • (Pi.single s (1 : ℂ) : σ → ℂ) +
        z.im • (Pi.single s (Complex.I : ℂ) : σ → ℂ) := by
    funext r
    by_cases h : r = s
    · subst h
      simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne h]
  rw [hz, map_add, map_smul, map_smul, realFunctionalCoefficients]
  simp only [smul_eq_mul]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

/-- **Real functionals are real parts of complex pairings.**  Every real-linear functional on a
finite complex jet space is the real part of the pairing with its coefficient packet. -/
theorem re_sum_realFunctionalCoefficients (φ : (σ → ℂ) →ₗ[ℝ] ℝ) (v : σ → ℂ) :
    (∑ s, realFunctionalCoefficients φ s * v s).re = φ v := by
  rw [Complex.re_sum]
  have hdecomp : v = ∑ s, Pi.single s (v s) := (Finset.univ_sum_single v).symm
  calc
    ∑ s, (realFunctionalCoefficients φ s * v s).re
        = ∑ s, φ (Pi.single s (v s)) := by
          refine Finset.sum_congr rfl ?_
          intro s _
          exact re_realFunctionalCoefficients_mul φ s (v s)
    _ = φ (∑ s, Pi.single s (v s)) := (map_sum φ _ _).symm
    _ = φ v := by rw [← hdecomp]

/-- A real-linear functional whose coefficient packet vanishes is zero. -/
theorem eq_zero_of_realFunctionalCoefficients_eq_zero
    {φ : (σ → ℂ) →ₗ[ℝ] ℝ} (h : ∀ s, realFunctionalCoefficients φ s = 0) :
    φ = 0 := by
  apply LinearMap.ext
  intro v
  rw [← re_sum_realFunctionalCoefficients φ v]
  simp [h]

/-- **Surjectivity from coefficient rigidity.**  A real-linear map into a finite complex jet space
is surjective as soon as the only coefficient packet pairing to zero with its whole range is the
zero packet. -/
theorem surjective_of_forall_coefficients_eq_zero
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (L : X →ₗ[ℝ] (σ → ℂ))
    (h : ∀ c : σ → ℂ, (∀ u : X, (∑ s, c s * L u s).re = 0) → ∀ s, c s = 0) :
    Function.Surjective L := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨φ, hφne, hφzero⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  have hker : ∀ u : X, φ (L u) = 0 := by
    intro u
    have hmem : φ (L u) ∈ (LinearMap.range L).map φ :=
      Submodule.mem_map_of_mem ⟨u, rfl⟩
    rw [hφzero] at hmem
    simpa using hmem
  have hcoeff : ∀ s, realFunctionalCoefficients φ s = 0 := by
    apply h
    intro u
    rw [re_sum_realFunctionalCoefficients φ (L u)]
    exact hker u
  exact hφne (eq_zero_of_realFunctionalCoefficients_eq_zero hcoeff)

end

end GaloisForLFunctions.HTGeometry
