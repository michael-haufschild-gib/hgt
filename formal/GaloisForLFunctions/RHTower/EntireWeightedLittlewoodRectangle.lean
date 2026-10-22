import GaloisForLFunctions.RHTower.FinitePeeling
import GaloisForLFunctions.RHTower.RectangleLocalWeightedCauchyResidue
import GaloisForLFunctions.RHTower.WeightedLittlewoodRectangle

/-!
# Weighted Littlewood lemma on rectangles for entire functions

For an entire function `f` that is not identically zero, every zero has finite order and only
finitely many zeros lie in any closed rectangle. For a rectangle `[c, d] × [T₁, T₂]` whose
boundary contains no zero of `f`, this module proves the weighted Littlewood identity:
`2π ∑_ρ m(ρ)(Re ρ - c)` over the zeros `ρ` in the rectangle, counted with multiplicity `m(ρ)`,
equals `∫ log |f(c + it)| dt - ∫ log |f(d + it)| dt + (d - c) ∫ Re (f'/f)(d + it) dt
+ ∫ (x - c) Im (f'/f)(x + iT₁) dx - ∫ (x - c) Im (f'/f)(x + iT₂) dx`.

## Main results

- `analyticOrderAt_ne_top_of_entire_exists_ne_zero`: a nonzero entire function has finite
  analytic order at every point.
- `entire_zeros_closedRectangle_finite`: its zero set in a closed rectangle is finite.
- `exists_entire_weighted_littlewood_rectangle`: the weighted Littlewood identity above, with
  `Z` the finite set of zeros in the rectangle.

## Hypotheses

Unconditional for entire `f` with `f(z) ≠ 0` for some `z`. The Littlewood identity assumes
`c < d`, `T₁ < T₂`, and that `f` has no zero on the four edges of the rectangle.
-/

open Complex Filter MeasureTheory intervalIntegral Set Topology

namespace RHTower

noncomputable section

/-- An entire function that is not identically zero has finite analytic order at every point. -/
theorem analyticOrderAt_ne_top_of_entire_exists_ne_zero
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0) (rho : ℂ) :
    analyticOrderAt f rho ≠ ⊤ := by
  intro htop
  have hevent : f =ᶠ[nhds rho] 0 := analyticOrderAt_eq_top.mp htop
  have heq : Set.EqOn f 0 (Set.univ : Set ℂ) :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ rho) hevent
  obtain ⟨z, hz⟩ := hne
  exact hz (heq (Set.mem_univ z))

/-- An entire function that is not identically zero has only finitely many zeros in any closed rectangle. -/
theorem entire_zeros_closedRectangle_finite
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0) (z₁ z₂ : ℂ) :
    {z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) | f z = 0}.Finite := by
  obtain ⟨x, hx⟩ := hne
  have hcod : (f ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    hf.preimage_zero_mem_codiscreteWithin
      (x := x) hx (Set.mem_univ x) isConnected_univ
  have hcodK : (f ⁻¹' {0}ᶜ) ∈ codiscreteWithin
      (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_uIcc.reProdIm isCompact_uIcc).finite_sdiff_of_mem_codiscreteWithin
    hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

private theorem analyticAt_logDeriv_of_ne {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : f z ≠ 0) :
    AnalyticAt ℂ (logDeriv f) z := by
  have h : AnalyticAt ℂ (fun w => deriv f w / f w) z :=
    hf.deriv.div hf hz
  refine h.congr ?_
  filter_upwards with w
  rw [logDeriv_apply]

/-- Weighted Littlewood lemma: if `f` is entire, not identically zero, and zero-free on the boundary of
`[c, d] × [T₁, T₂]`, then `2π ∑ m(ρ)(Re ρ - c)` over the zeros in the rectangle equals the boundary
expression in `log |f|` and `f'/f` stated in the module doc. -/
theorem exists_entire_weighted_littlewood_rectangle
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0)
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, f ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ t ∈ uIcc T₁ T₂, f ((c : ℂ) + t * I) ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ f z = 0) ∧
      2 * Real.pi *
          (∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℝ) * (w.re - c)) =
        (∫ t in T₁..T₂, Real.log ‖f ((c : ℂ) + t * I)‖)
          - (∫ t in T₁..T₂, Real.log ‖f ((d : ℂ) + t * I)‖)
          + (d - c) *
            (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re)
          + (∫ x in c..d,
            (x - c) * (logDeriv f ((x : ℂ) + T₁ * I)).im)
          - ∫ x in c..d,
            (x - c) * (logDeriv f ((x : ℂ) + T₂ * I)).im := by
  let z₁ : ℂ := (c : ℂ) + T₁ * I
  let z₂ : ℂ := (d : ℂ) + T₂ * I
  let hfinite : {z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) |
      f z = 0}.Finite := entire_zeros_closedRectangle_finite hf hne z₁ z₂
  let Z : Finset ℂ := hfinite.toFinset
  have hmem (z : ℂ) : z ∈ Z ↔ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ f z = 0 := by
    change z ∈ hfinite.toFinset ↔ _
    rw [Set.Finite.mem_toFinset, Set.mem_sep_iff]
    simp [z₁, z₂]
  obtain ⟨m, h, hhan, hm, hh0, hfact⟩ := exists_finite_peel isOpen_univ
    hf Z (by simp) (fun w _ => analyticOrderAt_ne_top_of_entire_exists_ne_zero hf hne w)
  have hhK : ∀ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂), h z ≠ 0 := by
    intro z hzK hhzero
    have hf0 : f z = 0 := by
      rw [hfact z (Set.mem_univ z), hhzero, mul_zero]
    exact hh0 z ((hmem z).mpr ⟨hzK, hf0⟩) hhzero
  let V : Set ℂ := Set.univ ∩ {z : ℂ | h z ≠ 0}
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hhan z (Set.mem_univ z)).continuousAt
  have hVopen : IsOpen V := by
    apply isOpen_univ.inter
    change IsOpen (h ⁻¹' {0}ᶜ)
    exact isOpen_compl_singleton.preimage hhcont
  have hsubV : (uIcc c d ×ℂ uIcc T₁ T₂) ⊆ V :=
    fun z hz => ⟨Set.mem_univ z, hhK z hz⟩
  have hin : ∀ w ∈ Z, c < w.re ∧ w.re < d ∧ T₁ < w.im ∧ w.im < T₂ := by
    intro w hw
    obtain ⟨hwK, hwzero⟩ := (hmem w).mp hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
    have hwreU := hwre
    have hwimU := hwim
    rw [uIcc_of_le hcd.le] at hwre
    rw [uIcc_of_le hT.le] at hwim
    have hrel : c < w.re := by
      have hne' : c ≠ w.re := by
        intro heq
        have hedge : (c : ℂ) + w.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneF := hleft w.im hwimU
        rw [hedge] at hneF
        exact hneF hwzero
      exact lt_of_le_of_ne hwre.1 hne'
    have hrer : w.re < d := by
      have hne' : w.re ≠ d := by
        intro heq
        have hedge : (d : ℂ) + w.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneF := hright w.im hwimU
        rw [hedge] at hneF
        exact hneF hwzero
      exact lt_of_le_of_ne hwre.2 hne'
    have himl : T₁ < w.im := by
      have hne' : T₁ ≠ w.im := by
        intro heq
        have hedge : (w.re : ℂ) + T₁ * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneF := hbot w.re hwreU
        rw [hedge] at hneF
        exact hneF hwzero
      exact lt_of_le_of_ne hwim.1 hne'
    have himr : w.im < T₂ := by
      have hne' : w.im ≠ T₂ := by
        intro heq
        have hedge : (w.re : ℂ) + T₂ * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneF := htop w.re hwreU
        rw [hedge] at hneF
        exact hneF hwzero
      exact lt_of_le_of_ne hwim.2 hne'
    exact ⟨hrel, hrer, himl, himr⟩
  have hval : rectIntegral
      (fun z => (z - (c : ℂ)) * logDeriv f z) z₁ z₂ =
        2 * Real.pi * I *
          ∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℂ) * (w - (c : ℂ)) := by
    have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
      Z (fun w => w) m (f := f) (g := fun z => z - (c : ℂ)) (h := h)
      (z₁ := z₁) (z₂ := z₂) (U := V) hVopen
      (fun z _ => analyticAt_id.sub analyticAt_const)
      (by simpa [z₁, z₂] using hin) (by simpa [z₁, z₂] using hsubV)
      (hhan.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
      (fun z _ => hfact z (Set.mem_univ z))
    calc
      _ = 2 * Real.pi * I * ∑ w ∈ Z, (m w : ℂ) * (w - (c : ℂ)) := by
        simpa using hres
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro w hw
        rw [hm w hw]
  have hqbot : ContinuousOn
      (fun x : ℝ => logDeriv f ((x : ℂ) + T₁ * I)) (uIcc c d) := by
    intro x hx
    have hc := ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + T₁ * I)
      (analyticAt_logDeriv_of_ne (hf _ (Set.mem_univ _)) (hbot x hx)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + T₁ * I) x)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hqtop : ContinuousOn
      (fun x : ℝ => logDeriv f ((x : ℂ) + T₂ * I)) (uIcc c d) := by
    intro x hx
    have hc := ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + T₂ * I)
      (analyticAt_logDeriv_of_ne (hf _ (Set.mem_univ _)) (htop x hx)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + T₂ * I) x)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hqright : ContinuousOn
      (fun t : ℝ => logDeriv f ((d : ℂ) + t * I)) (uIcc T₁ T₂) := by
    intro t ht
    have hc := ContinuousAt.comp (f := fun y : ℝ => (d : ℂ) + y * I)
      (analyticAt_logDeriv_of_ne (hf _ (Set.mem_univ _)) (hright t ht)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (d : ℂ) + y * I) t)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hqleft : ContinuousOn
      (fun t : ℝ => logDeriv f ((c : ℂ) + t * I)) (uIcc T₁ T₂) := by
    intro t ht
    have hc := ContinuousAt.comp (f := fun y : ℝ => (c : ℂ) + y * I)
      (analyticAt_logDeriv_of_ne (hf _ (Set.mem_univ _)) (hleft t ht)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (c : ℂ) + y * I) t)
    simpa [Function.comp_def] using hc.continuousWithinAt
  refine ⟨Z, hmem, ?_⟩
  apply weighted_littlewood_from_rectIntegral (by simpa [z₁, z₂] using hval)
    hqbot hqtop hqright hqleft
  · intro x _
    exact (hf _ (Set.mem_univ _)).differentiableAt.hasDerivAt
  · intro x _
    exact (hf _ (Set.mem_univ _)).differentiableAt.hasDerivAt
  · intro t _
    exact (hf _ (Set.mem_univ _)).differentiableAt.hasDerivAt
  · intro t _
    exact (hf _ (Set.mem_univ _)).differentiableAt.hasDerivAt
  · exact hbot
  · exact htop
  · exact hright
  · exact hleft

end

end RHTower
