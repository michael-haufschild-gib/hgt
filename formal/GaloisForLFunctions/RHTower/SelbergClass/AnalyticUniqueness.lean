import GaloisForLFunctions.RHTower.SelbergClass.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Uniqueness of Selberg analytic continuation

Two pole-safe continuations agreeing in the Dirichlet-series half-plane agree as meromorphic
functions.  The proof cross-multiplies their entire regularizations, applies the analytic identity
principle, and then cancels away from `s = 1`.  No value at the possible pole is asserted.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- Agreement on the half-plane `Re(s) > 1` uniquely determines a pole-safe Selberg continuation
up to codiscrete equality. -/
theorem SelbergAnalyticContinuation.eventuallyEq_of_eqOn_rightHalfPlane
    (A B : SelbergAnalyticContinuation)
    (h : ∀ s : ℂ, 1 < s.re → A.value s = B.value s) :
    A.value =ᶠ[codiscrete ℂ] B.value := by
  let f : ℂ → ℂ := fun s ↦ A.regularized s * (s - 1) ^ B.poleOrder
  let g : ℂ → ℂ := fun s ↦ B.regularized s * (s - 1) ^ A.poleOrder
  have hf : AnalyticOnNhd ℂ f univ := A.regularized.analytic.mul fun z _ ↦ by fun_prop
  have hg : AnalyticOnNhd ℂ g univ := B.regularized.analytic.mul fun z _ ↦ by fun_prop
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have htwo : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by norm_num
  have hlocal : f =ᶠ[nhds (2 : ℂ)] g := by
    filter_upwards [hopen.mem_nhds htwo] with s hs
    have hs1 : s - 1 ≠ 0 := by
      intro heq
      have : s = 1 := sub_eq_zero.mp heq
      subst s
      norm_num at hs
    have hv := h s hs
    rw [SelbergAnalyticContinuation.value, SelbergAnalyticContinuation.value,
      div_eq_div_iff (pow_ne_zero _ hs1) (pow_ne_zero _ hs1)] at hv
    exact hv
  have hcross : f = g := hf.eq_of_eventuallyEq hg hlocal
  have haway : (singleton (1 : ℂ))ᶜ ∈ codiscrete ℂ :=
    compl_mem_codiscrete_iff.mpr ⟨isClosed_singleton, subsingleton_singleton.isDiscrete⟩
  filter_upwards [haway] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
  rw [SelbergAnalyticContinuation.value, SelbergAnalyticContinuation.value,
    div_eq_div_iff (pow_ne_zero _ hs1) (pow_ne_zero _ hs1)]
  exact congrFun hcross s

/-- Two extended Selberg-class data with the same coefficients represent the same meromorphic
function, independently of their chosen pole regularizations. -/
theorem ExtendedSelbergClass.eventuallyEq_value_of_coeff_eq
    (F G : ExtendedSelbergClass) (hcoeff : F.coeff = G.coeff) :
    F =ᶠ[codiscrete ℂ] G := by
  apply F.continuation.eventuallyEq_of_eqOn_rightHalfPlane G.continuation
  intro s hs
  rw [← F.lSeries_eq_value s hs, ← G.lSeries_eq_value s hs, hcoeff]

end

end RHTower
