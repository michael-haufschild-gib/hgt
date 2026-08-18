/-
# Equal divisors force an entire nonvanishing quotient

Two entire functions with the same analytic order at every point, neither identically zero, differ
by an entire nonvanishing factor.  The raw quotient `f / g` has meromorphic order zero everywhere
but the wrong value at each zero of `g`; filling those removable singularities with the meromorphic
normal form `toMeromorphicNFOn` produces the honest entire factor, and the product identity extends
from a neighbourhood of one point where `g` does not vanish by the identity theorem.

This is the divisor-matching half of every Hadamard-type factorization: once a canonical product
with the prescribed divisor is available, this lemma produces the zero-free cofactor.
-/
import Mathlib

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.EntireQuotient

/-- The raw quotient of two entire functions, before filling removable singularities. -/
def rawQuotient (f g : ℂ → ℂ) : ℂ → ℂ := f / g

/-- The removable-singularity-filled quotient. -/
def entireQuotient (f g : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (rawQuotient f g) Set.univ

theorem rawQuotient_meromorphic {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ) :
    MeromorphicOn (rawQuotient f g) Set.univ :=
  hf.meromorphicOn.div hg.meromorphicOn

theorem rawQuotient_order_zero {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z) (z : ℂ) :
    meromorphicOrderAt (rawQuotient f g) z = 0 := by
  rw [rawQuotient,
    meromorphicOrderAt_div (hf z (Set.mem_univ _)).meromorphicAt
      (hg z (Set.mem_univ _)).meromorphicAt,
    (hf z (Set.mem_univ _)).meromorphicOrderAt_eq,
    (hg z (Set.mem_univ _)).meromorphicOrderAt_eq, ← horder z]
  simp [hford z]

theorem entireQuotient_analytic {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z) :
    AnalyticOnNhd ℂ (entireQuotient f g) Set.univ := by
  intro z hz
  have hNF := meromorphicNFOn_toMeromorphicNFOn (rawQuotient f g) Set.univ hz
  apply hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn (rawQuotient_meromorphic hf hg) hz,
    rawQuotient_order_zero hf hg hford horder]

theorem entireQuotient_ne_zero {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z) (z : ℂ) :
    entireQuotient f g z ≠ 0 := by
  have hNF := meromorphicNFOn_toMeromorphicNFOn (rawQuotient f g) Set.univ (Set.mem_univ z)
  apply hNF.meromorphicOrderAt_eq_zero_iff.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn (rawQuotient_meromorphic hf hg) (Set.mem_univ z),
    rawQuotient_order_zero hf hg hford horder]

theorem entireQuotient_mul {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    {z₀ : ℂ} (hz₀ : g z₀ ≠ 0) :
    entireQuotient f g * g = f := by
  have hraw_an : AnalyticAt ℂ (rawQuotient f g) z₀ :=
    (hf z₀ (Set.mem_univ _)).div (hg z₀ (Set.mem_univ _)) hz₀
  have hQraw : entireQuotient f g =ᶠ[𝓝 z₀] rawQuotient f g := by
    have hlocal := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
      (rawQuotient_meromorphic hf hg) (Set.mem_univ z₀)
    have heq : toMeromorphicNFAt (rawQuotient f g) z₀ = rawQuotient f g :=
      toMeromorphicNFAt_eq_self.mpr hraw_an.meromorphicNFAt
    rw [heq] at hlocal
    exact hlocal
  have hgne : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 :=
    (hg z₀ (Set.mem_univ _)).continuousAt.eventually_ne hz₀
  have hlocal : entireQuotient f g * g =ᶠ[𝓝 z₀] f := by
    filter_upwards [hQraw, hgne] with z hq hp
    simp only [Pi.mul_apply]
    rw [hq, rawQuotient, Pi.div_apply, div_mul_cancel₀ _ hp]
  exact ((entireQuotient_analytic hf hg hford horder).mul hg).eq_of_eventuallyEq hf hlocal

/-- **Equal divisors force an entire nonvanishing quotient.**  Two entire functions with the same
analytic order at every point, neither identically zero, differ by an entire nonvanishing factor. -/
theorem exists_entire_nonvanishing_quotient {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    {z₀ : ℂ} (hz₀ : g z₀ ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ z, h z ≠ 0) ∧ (∀ z, f z = h z * g z) := by
  have hAn := entireQuotient_analytic hf hg hford horder
  refine ⟨entireQuotient f g, fun z => (hAn z (Set.mem_univ z)).differentiableAt,
    entireQuotient_ne_zero hf hg hford horder, fun z => ?_⟩
  have := congrFun (entireQuotient_mul hf hg hford horder hz₀) z
  simpa only [Pi.mul_apply] using this.symm

end GaloisForLFunctions.EntireQuotient

namespace GaloisForLFunctions.EntireQuotient

/-- The quotient is analytic as soon as the raw quotient has nonnegative order everywhere. -/
theorem entireQuotient_analytic_of_nonneg {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hord : ∀ z, 0 ≤ meromorphicOrderAt (rawQuotient f g) z) :
    AnalyticOnNhd ℂ (entireQuotient f g) Set.univ := by
  intro z hz
  have hNF := meromorphicNFOn_toMeromorphicNFOn (rawQuotient f g) Set.univ hz
  apply hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn (rawQuotient_meromorphic hf hg) hz]
  exact hord z

/-- The product identity, given analyticity of the filled quotient. -/
theorem entireQuotient_mul_of_analytic {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hQ : AnalyticOnNhd ℂ (entireQuotient f g) Set.univ)
    {z₀ : ℂ} (hz₀ : g z₀ ≠ 0) :
    entireQuotient f g * g = f := by
  have hraw_an : AnalyticAt ℂ (rawQuotient f g) z₀ :=
    (hf z₀ (Set.mem_univ _)).div (hg z₀ (Set.mem_univ _)) hz₀
  have hQraw : entireQuotient f g =ᶠ[𝓝 z₀] rawQuotient f g := by
    have hlocal := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
      (rawQuotient_meromorphic hf hg) (Set.mem_univ z₀)
    have heq : toMeromorphicNFAt (rawQuotient f g) z₀ = rawQuotient f g :=
      toMeromorphicNFAt_eq_self.mpr hraw_an.meromorphicNFAt
    rw [heq] at hlocal
    exact hlocal
  have hgne : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 :=
    (hg z₀ (Set.mem_univ _)).continuousAt.eventually_ne hz₀
  have hlocal : entireQuotient f g * g =ᶠ[𝓝 z₀] f := by
    filter_upwards [hQraw, hgne] with z hq hp
    simp only [Pi.mul_apply]
    rw [hq, rawQuotient, Pi.div_apply, div_mul_cancel₀ _ hp]
  exact (hQ.mul hg).eq_of_eventuallyEq hf hlocal

theorem analyticOrderAt_id_zero : analyticOrderAt (fun z : ℂ => z) 0 = 1 := by
  have han : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  refine han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero rfl ?_
  rw [deriv_id'']
  exact one_ne_zero

theorem analyticOrderAt_monomial (m : ℕ) :
    analyticOrderAt (fun z : ℂ => z ^ m) 0 = (m : ℕ∞) := by
  have hfun : (fun z : ℂ => z ^ m) = (fun z : ℂ => z) ^ m := by
    funext z
    rw [Pi.pow_apply]
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  rw [hfun, analyticOrderAt_pow hid, analyticOrderAt_id_zero]
  simp

theorem analyticOrderAt_monomial_of_ne_zero {m : ℕ} {w : ℂ} (hw : w ≠ 0) :
    analyticOrderAt (fun z : ℂ => z ^ m) w = 0 := by
  refine (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z ^ m) w).analyticOrderAt_eq_zero.mpr ?_
  exact pow_ne_zero m hw

/-- **Splitting off the monomial at the origin.**  Every entire function that is nowhere locally
zero is `z ^ m` times an entire function that does not vanish at the origin, with `m` the order of
vanishing there. -/
theorem exists_monomial_factorization {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Set.univ ∧ g 0 ≠ 0 ∧
      (∀ z, analyticOrderAt g z = analyticOrderAt f z ∨ z = 0) ∧
      ∀ z, f z = z ^ (analyticOrderAt f 0).toNat * g z := by
  classical
  set m : ℕ := (analyticOrderAt f 0).toNat with hm
  set P : ℂ → ℂ := fun z => z ^ m with hP
  have hPan : AnalyticOnNhd ℂ P Set.univ := fun z _ => by fun_prop
  have hordraw : ∀ z, meromorphicOrderAt (rawQuotient f P) z
      = meromorphicOrderAt f z - meromorphicOrderAt P z := by
    intro z
    rw [rawQuotient, meromorphicOrderAt_div (hf z (Set.mem_univ _)).meromorphicAt
      (hPan z (Set.mem_univ _)).meromorphicAt]
  have hordP : ∀ z, z ≠ 0 → meromorphicOrderAt P z = 0 := by
    intro z hz
    rw [(hPan z (Set.mem_univ _)).meromorphicOrderAt_eq, hP,
      analyticOrderAt_monomial_of_ne_zero hz]
    rfl
  have hnn : ∀ z, 0 ≤ meromorphicOrderAt (rawQuotient f P) z := by
    intro z
    rw [hordraw z]
    by_cases hz : z = 0
    · subst hz
      rw [(hf 0 (Set.mem_univ _)).meromorphicOrderAt_eq, (hPan 0 (Set.mem_univ _)).meromorphicOrderAt_eq,
        hP, analyticOrderAt_monomial m, hm]
      have hfin := hford 0
      rw [← ENat.coe_toNat hfin]
      simp
    · rw [hordP z hz, sub_zero, (hf z (Set.mem_univ _)).meromorphicOrderAt_eq]
      simp
  have hQan := entireQuotient_analytic_of_nonneg hf hPan hnn
  have hQzero : meromorphicOrderAt (entireQuotient f P) 0 = 0 := by
    rw [entireQuotient, meromorphicOrderAt_toMeromorphicNFOn (rawQuotient_meromorphic hf hPan) (Set.mem_univ 0),
      hordraw 0, (hf 0 (Set.mem_univ _)).meromorphicOrderAt_eq,
      (hPan 0 (Set.mem_univ _)).meromorphicOrderAt_eq, hP, analyticOrderAt_monomial m, hm]
    have hfin := hford 0
    rw [← ENat.coe_toNat hfin]
    simp
  have hQ0 : entireQuotient f P 0 ≠ 0 := by
    have hNF := meromorphicNFOn_toMeromorphicNFOn (rawQuotient f P) Set.univ (Set.mem_univ 0)
    exact hNF.meromorphicOrderAt_eq_zero_iff.mp hQzero
  have hmul := entireQuotient_mul_of_analytic hf hPan hQan (z₀ := 1) (by simp [hP])
  refine ⟨entireQuotient f P, hQan, hQ0, ?_, fun z => ?_⟩
  · intro z
    by_cases hz : z = 0
    · exact Or.inr hz
    · refine Or.inl ?_
      have hPz : analyticOrderAt P z = 0 := by
        rw [hP, analyticOrderAt_monomial_of_ne_zero hz]
      calc analyticOrderAt (entireQuotient f P) z
          = analyticOrderAt (entireQuotient f P) z + analyticOrderAt P z := by
            rw [hPz, add_zero]
        _ = analyticOrderAt (entireQuotient f P * P) z :=
            (analyticOrderAt_mul (hQan z (Set.mem_univ _)) (hPan z (Set.mem_univ _))).symm
        _ = analyticOrderAt f z := by rw [hmul]
  · have := congrFun hmul z
    simp only [Pi.mul_apply] at this
    rw [← this, hP]
    ring

end GaloisForLFunctions.EntireQuotient
