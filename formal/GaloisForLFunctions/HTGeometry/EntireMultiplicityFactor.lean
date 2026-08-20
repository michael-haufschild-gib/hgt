import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Peeling prescribed multiplicities at finitely many points

An entire function whose analytic order at `c` is exactly `n` factors as `(z − c)^n` times an
entire function nonvanishing at `c`; iterating over a finite node set with a multiplicity function
gives the global factorization

```text
f z = (∏_{c ∈ pts} (z − c)^{m c}) · g z,      g c ≠ 0 for every c ∈ pts.
```

Unlike a constant-multiplicity version this keeps the *exact* order at each node, which is what
makes the cofactor nonvanishing there — the property needed when the nodes lie on the boundary of a
contour and have to be removed from it.
-/

open Complex

noncomputable section

namespace RHTower

/-- **Peeling a zero of exact order.**  An entire function whose analytic order at `c` is exactly
`n` is `(z − c)^n` times an entire function that does not vanish at `c`. -/
theorem exists_entire_factor_of_analyticOrderAt_eq
    {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z) (c : ℂ) (n : ℕ)
    (horder : analyticOrderAt f c = (n : ℕ∞)) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧ g c ≠ 0 ∧ ∀ z, f z = (z - c) ^ n * g z := by
  classical
  obtain ⟨g₀, hg₀, hg₀ne, hlocal⟩ := ((hf c).analyticOrderAt_eq_natCast).mp horder
  set g : ℂ → ℂ := fun z => if z = c then g₀ z else f z * ((z - c) ^ n)⁻¹ with hgdef
  have hg : ∀ z, AnalyticAt ℂ g z := by
    intro z
    by_cases hz : z = c
    · subst z
      apply hg₀.congr
      filter_upwards [hlocal] with w hw
      by_cases hwc : w = c
      · simp [hgdef, hwc]
      · simp only [hgdef, if_neg hwc]
        rw [hw, smul_eq_mul]
        field_simp [sub_ne_zero.mpr hwc]
    · have hU : {w : ℂ | w ≠ c} ∈ nhds z := IsOpen.mem_nhds isOpen_ne hz
      have hquot : AnalyticAt ℂ (fun w => f w * ((w - c) ^ n)⁻¹) z :=
        (hf z).mul (((analyticAt_id.sub analyticAt_const).pow n).inv
          (pow_ne_zero n (sub_ne_zero.mpr hz)))
      apply hquot.congr
      filter_upwards [hU] with w hw
      simp [hgdef, hw]
  refine ⟨g, hg, by simpa [hgdef] using hg₀ne, ?_⟩
  intro z
  by_cases hz : z = c
  · subst z
    have := hlocal.self_of_nhds
    simpa [hgdef, smul_eq_mul] using this
  · simp only [hgdef, if_neg hz]
    field_simp [sub_ne_zero.mpr hz]

/-- **Simultaneous peeling at finitely many points.**  Prescribing at each point of a finite set the
exact analytic order of `f`, the corresponding monomial product divides `f` and the cofactor is
nonzero at every one of those points. -/
theorem exists_entire_multiplicity_factor
    {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z) (pts : Finset ℂ) (m : ℂ → ℕ)
    (horder : ∀ c ∈ pts, analyticOrderAt f c = ((m c : ℕ) : ℕ∞)) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧ (∀ c ∈ pts, g c ≠ 0) ∧
      ∀ z, f z = (∏ c ∈ pts, (z - c) ^ (m c)) * g z := by
  classical
  induction pts using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, by simp, fun z => by simp⟩
  | @insert a pts ha ih =>
      obtain ⟨g, hg, hga, hfg⟩ := exists_entire_factor_of_analyticOrderAt_eq hf a (m a)
        (horder a (Finset.mem_insert_self a pts))
      have hfun : f = (fun z : ℂ => (z - a) ^ (m a)) * g := by
        funext z; simpa using hfg z
      have horder_g : ∀ c ∈ pts, analyticOrderAt g c = ((m c : ℕ) : ℕ∞) := by
        intro c hc
        have hac : a ≠ c := fun hac => ha (hac ▸ hc)
        have hfactor : AnalyticAt ℂ (fun z : ℂ => (z - a) ^ (m a)) c := by fun_prop
        have hfactor_ne : ((c : ℂ) - a) ^ (m a) ≠ 0 :=
          pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hac))
        have hfactor_order : analyticOrderAt (fun z : ℂ => (z - a) ^ (m a)) c = 0 :=
          hfactor.analyticOrderAt_eq_zero.mpr hfactor_ne
        have heq : analyticOrderAt f c = analyticOrderAt g c := by
          rw [hfun, analyticOrderAt_mul hfactor (hg c), hfactor_order, zero_add]
        rw [← heq]
        exact horder c (Finset.mem_insert_of_mem hc)
      obtain ⟨h, hh, hhne, hgh⟩ := ih hg horder_g
      refine ⟨h, hh, ?_, ?_⟩
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc'
        · intro hzero
          exact hga (by rw [hgh c, hzero, mul_zero])
        · exact hhne c hc'
      · intro z
        rw [hfg z, hgh z, Finset.prod_insert ha]
        ring

/-- The node product is analytic. -/
theorem analyticAt_multiplicityFactor (pts : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => ∏ c ∈ pts, (w - c) ^ (m c)) z := by
  classical
  induction pts using Finset.induction_on with
  | empty => simpa using analyticAt_const
  | @insert a pts ha ih =>
      have : (fun w : ℂ => ∏ c ∈ insert a pts, (w - c) ^ (m c))
          = fun w : ℂ => ((w - a) ^ (m a)) * ∏ c ∈ pts, (w - c) ^ (m c) := by
        funext w; rw [Finset.prod_insert ha]
      rw [this]
      exact (((analyticAt_id.sub analyticAt_const).pow (m a))).mul ih

/-- Away from its nodes the product does not vanish. -/
theorem multiplicityFactor_ne_zero (pts : Finset ℂ) (m : ℂ → ℕ) {z : ℂ} (hz : z ∉ pts) :
    (∏ c ∈ pts, (z - c) ^ (m c)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun c hc => pow_ne_zero _ (sub_ne_zero.mpr ?_)
  intro h
  exact hz (h ▸ hc)

/-- A nonvanishing analytic factor does not change the analytic order. -/
theorem analyticOrderAt_eq_of_factor_ne_zero {f g q : ℂ → ℂ} {z : ℂ}
    (hq : AnalyticAt ℂ q z) (hg : AnalyticAt ℂ g z)
    (hfq : ∀ w, f w = q w * g w) (hqz : q z ≠ 0) :
    analyticOrderAt f z = analyticOrderAt g z := by
  have hfun : f = q * g := by funext w; simpa using hfq w
  rw [hfun, analyticOrderAt_mul hq hg, hq.analyticOrderAt_eq_zero.mpr hqz, zero_add]

end RHTower

end
