import Mathlib

/-!
# Entire approximation of a simple pole on a closed half plane

A simple pole sitting strictly to the left of the line `Re s = 1` can be approximated *uniformly on
the whole closed half plane* `Re s ≥ 1` by an entire function, with an exponentially small error:

```text
‖ 1/(s-a) - truncPole a T s ‖  ≤  e^{-T(1 - Re a)} / (1 - Re a) .
```

The approximant is the truncated Laplace transform `∫_0^T e^{-t(s-a)} dt = (1 - e^{-T(s-a)})/(s-a)`,
which is entire because the numerator vanishes at `s = a`.  This is the exact half-plane analogue of
the elementary step in Runge's theorem, and it is the mechanism by which Andersson's Lemma 1
(Arakelyan approximation on `Re s ≥ 1`) is elementary for functions with only finitely many poles:
a rational function with all poles strictly to the left of the line is uniformly approximable on the
closed half plane by entire functions.

Uniform approximability on the *closed, unbounded* half plane is what distinguishes this from the
usual compact-open Runge statements, and it is exactly what the Mellin representation of Andersson's
Lemma 1 consumes.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The truncated Laplace transform of a simple pole: an entire approximant. -/
def truncPole (a : ℂ) (T : ℝ) : ℂ → ℂ :=
  Function.update (fun s => (1 - Complex.exp (-(T : ℂ) * (s - a))) / (s - a)) a (T : ℂ)

theorem truncPole_of_ne {a : ℂ} {T : ℝ} {s : ℂ} (hs : s ≠ a) :
    truncPole a T s = (1 - Complex.exp (-(T : ℂ) * (s - a))) / (s - a) := by
  rw [truncPole, Function.update_of_ne hs]

theorem truncPole_self (a : ℂ) (T : ℝ) : truncPole a T a = (T : ℂ) := by
  rw [truncPole, Function.update_self]

/-- The approximant is entire: the apparent singularity at `a` is removable. -/
theorem differentiable_truncPole (a : ℂ) (T : ℝ) : Differentiable ℂ (truncPole a T) := by
  have hoff : DifferentiableOn ℂ (truncPole a T) (Set.univ \ {a}) := by
    intro s hs
    have hsa : s ≠ a := fun h => hs.2 (by simp [h])
    have hne : s - a ≠ 0 := sub_ne_zero.mpr hsa
    have heq : Set.EqOn (truncPole a T)
        (fun z => (1 - Complex.exp (-(T : ℂ) * (z - a))) / (z - a)) (Set.univ \ {a}) := by
      intro z hz
      exact truncPole_of_ne (fun h => hz.2 (by simp [h]))
    refine DifferentiableWithinAt.congr ?_ (fun z hz => heq hz) (heq hs)
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.div ?_ ?_ hne
    · exact (differentiableAt_const 1).sub
        (Complex.differentiable_exp.differentiableAt.comp s (by fun_prop))
    · fun_prop
  have hcont : ContinuousAt (truncPole a T) a := by
    have hd : HasDerivAt (fun z : ℂ => 1 - Complex.exp (-(T : ℂ) * (z - a))) (T : ℂ) a := by
      have h1 : HasDerivAt (fun z : ℂ => -(T : ℂ) * (z - a)) (-(T : ℂ)) a := by
        simpa using ((hasDerivAt_id a).sub_const a).const_mul (-(T : ℂ))
      have h2 : HasDerivAt (fun z : ℂ => Complex.exp (-(T : ℂ) * (z - a))) (-(T : ℂ)) a := by
        simpa using HasDerivAt.cexp h1
      have h3 : HasDerivAt (fun z : ℂ => 1 - Complex.exp (-(T : ℂ) * (z - a)))
          (-(-(T : ℂ))) a := h2.const_sub 1
      simpa using h3
    have hslope0 := hasDerivAt_iff_tendsto_slope.mp hd
    have hslope : Filter.Tendsto
        (fun z : ℂ => (1 - Complex.exp (-(T : ℂ) * (z - a))) / (z - a))
        (nhdsWithin a {a}ᶜ) (nhds (T : ℂ)) := by
      refine hslope0.congr fun z => ?_
      rw [slope_def_field]
      simp
    have htend : Filter.Tendsto (truncPole a T) (nhdsWithin a {a}ᶜ)
        (nhds (truncPole a T a)) := by
      rw [truncPole_self]
      refine hslope.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (truncPole_of_ne hz).symm
    have hfull : Filter.Tendsto (truncPole a T) (nhds a) (nhds (truncPole a T a)) := by
      rw [← nhdsNE_sup_pure a]
      exact Filter.Tendsto.sup htend (by simpa using tendsto_pure_nhds (truncPole a T) a)
    exact hfull
  have hall : DifferentiableOn ℂ (truncPole a T) Set.univ :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (Filter.univ_mem)).mp ⟨hoff, hcont⟩
  intro z
  exact hall.differentiableAt Filter.univ_mem

/-- **The exponentially small half-plane error.** -/
theorem norm_pole_sub_truncPole_le {a : ℂ} (ha : a.re < 1) {T : ℝ} (hT : 0 ≤ T) {s : ℂ}
    (hs : 1 ≤ s.re) :
    ‖(s - a)⁻¹ - truncPole a T s‖ ≤ Real.exp (-(T * (1 - a.re))) / (1 - a.re) := by
  have hδ : 0 < 1 - a.re := by linarith
  have hre : 1 - a.re ≤ (s - a).re := by
    rw [Complex.sub_re]
    linarith
  have hne : s - a ≠ 0 := by
    intro h
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    linarith
  have hsa : s ≠ a := sub_ne_zero.mp hne
  have heq : (s - a)⁻¹ - truncPole a T s
      = Complex.exp (-(T : ℂ) * (s - a)) / (s - a) := by
    rw [truncPole_of_ne hsa]
    field_simp
    ring
  rw [heq, norm_div, Complex.norm_exp]
  have hnum : (-(T : ℂ) * (s - a)).re = -(T * (s - a).re) := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [hnum]
  have hden : 1 - a.re ≤ ‖s - a‖ := le_trans hre (Complex.re_le_norm _)
  have hexp : Real.exp (-(T * (s - a).re)) ≤ Real.exp (-(T * (1 - a.re))) := by
    refine Real.exp_le_exp.mpr ?_
    have hmul : T * (1 - a.re) ≤ T * (s - a).re := mul_le_mul_of_nonneg_left hre hT
    linarith
  have hpos : (0:ℝ) < ‖s - a‖ := norm_pos_iff.mpr hne
  calc Real.exp (-(T * (s - a).re)) / ‖s - a‖
      ≤ Real.exp (-(T * (1 - a.re))) / ‖s - a‖ := by gcongr
    _ ≤ Real.exp (-(T * (1 - a.re))) / (1 - a.re) := by gcongr


/-- A single scaled pole is uniformly approximable on the closed half plane, to any accuracy. -/
theorem exists_truncPole_approx {a : ℂ} (ha : a.re < 1) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ s : ℂ, 1 ≤ s.re → ‖c * (s - a)⁻¹ - c * truncPole a T s‖ ≤ ε := by
  have hδ : 0 < 1 - a.re := by linarith
  by_cases hc : c = 0
  · refine ⟨0, le_refl _, fun s hs => ?_⟩
    rw [hc, zero_mul, zero_mul, sub_zero, norm_zero]
    exact le_of_lt hε
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    set T : ℝ := max 0 (Real.log (‖c‖ / (ε * (1 - a.re))) / (1 - a.re)) with hTdef
    have hT0 : 0 ≤ T := le_max_left _ _
    refine ⟨T, hT0, fun s hs => ?_⟩
    have hbound := norm_pole_sub_truncPole_le ha hT0 hs
    have hkey : Real.exp (-(T * (1 - a.re))) / (1 - a.re) ≤ ε / ‖c‖ := by
      rw [div_le_div_iff₀ hδ hcpos]
      have hexp : Real.exp (-(T * (1 - a.re))) ≤ ε * (1 - a.re) / ‖c‖ := by
        rcases le_or_gt (Real.log (‖c‖ / (ε * (1 - a.re)))) 0 with hlog | hlog
        · have hT : T = 0 := by
            rw [hTdef]
            refine max_eq_left ?_
            exact div_nonpos_of_nonpos_of_nonneg hlog (le_of_lt hδ)
          rw [hT]
          simp only [zero_mul, neg_zero, Real.exp_zero]
          have hle : ‖c‖ / (ε * (1 - a.re)) ≤ 1 := by
            by_contra hcon
            have h1 : 1 < ‖c‖ / (ε * (1 - a.re)) := not_le.mp hcon
            have := Real.log_pos h1
            linarith
          rw [div_le_iff₀ (by positivity)] at hle
          rw [le_div_iff₀ hcpos]
          linarith
        · have hTeq : T = Real.log (‖c‖ / (ε * (1 - a.re))) / (1 - a.re) := by
            rw [hTdef]
            refine max_eq_right ?_
            positivity
          rw [hTeq, div_mul_cancel₀ _ (ne_of_gt hδ)]
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          rw [inv_le_iff_one_le_mul₀ (by positivity)]
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          field_simp
          norm_num
      calc Real.exp (-(T * (1 - a.re))) * ‖c‖ ≤ (ε * (1 - a.re) / ‖c‖) * ‖c‖ := by
            exact mul_le_mul_of_nonneg_right hexp (le_of_lt hcpos)
        _ = ε * (1 - a.re) := by field_simp
    have hfac : ‖c * (s - a)⁻¹ - c * truncPole a T s‖ = ‖c‖ * ‖(s - a)⁻¹ - truncPole a T s‖ := by
      rw [← mul_sub, norm_mul]
    rw [hfac]
    calc ‖c‖ * ‖(s - a)⁻¹ - truncPole a T s‖
        ≤ ‖c‖ * (Real.exp (-(T * (1 - a.re))) / (1 - a.re)) :=
          mul_le_mul_of_nonneg_left hbound (le_of_lt hcpos)
      _ ≤ ‖c‖ * (ε / ‖c‖) := mul_le_mul_of_nonneg_left hkey (le_of_lt hcpos)
      _ = ε := by field_simp

/-- **Half-plane Arakelyan approximation for finitely many poles.**  A finite sum of simple poles
lying strictly to the left of `Re s = 1` is uniformly approximable, on the whole closed half plane
`Re s ≥ 1`, by an entire function. -/
theorem exists_entire_approx_finite_poles {ι : Type*} [DecidableEq ι] (t : Finset ι) (α : ι → ℂ)
    (m : ι → ℂ) (hα : ∀ i ∈ t, (α i).re < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, 1 ≤ s.re → ‖(∑ i ∈ t, m i * (s - α i)⁻¹) - g s‖ ≤ ε := by
  classical
  set ε' : ℝ := ε / (t.card + 1) with hε'def
  have hε' : 0 < ε' := by
    rw [hε'def]
    positivity
  have hchoice : ∀ i ∈ t, ∃ T : ℝ, 0 ≤ T ∧
      ∀ s : ℂ, 1 ≤ s.re → ‖m i * (s - α i)⁻¹ - m i * truncPole (α i) T s‖ ≤ ε' := by
    intro i hi
    exact exists_truncPole_approx (hα i hi) (m i) hε'
  choose! T hT0 hT using hchoice
  refine ⟨fun s => ∑ i ∈ t, m i * truncPole (α i) (T i) s, ?_, ?_⟩
  · intro z
    have hfun : (fun s : ℂ => ∑ i ∈ t, m i * truncPole (α i) (T i) s)
        = ∑ i ∈ t, fun s : ℂ => m i * truncPole (α i) (T i) s := by
      funext s
      simp
    rw [hfun]
    refine DifferentiableAt.sum fun i _ => ?_
    exact ((differentiable_truncPole (α i) (T i)).differentiableAt).const_mul (m i)
  · intro s hs
    have hsplit : (∑ i ∈ t, m i * (s - α i)⁻¹) - ∑ i ∈ t, m i * truncPole (α i) (T i) s
        = ∑ i ∈ t, (m i * (s - α i)⁻¹ - m i * truncPole (α i) (T i) s) := by
      rw [Finset.sum_sub_distrib]
    rw [hsplit]
    calc ‖∑ i ∈ t, (m i * (s - α i)⁻¹ - m i * truncPole (α i) (T i) s)‖
        ≤ ∑ i ∈ t, ‖m i * (s - α i)⁻¹ - m i * truncPole (α i) (T i) s‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ t, ε' := Finset.sum_le_sum fun i hi => hT i hi s hs
      _ = (t.card : ℝ) * ε' := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ε := by
          rw [hε'def, mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          have : (0:ℝ) ≤ ε := le_of_lt hε
          nlinarith [Nat.cast_nonneg (α := ℝ) t.card]

end GaloisForLFunctions.HTGeometry

end
