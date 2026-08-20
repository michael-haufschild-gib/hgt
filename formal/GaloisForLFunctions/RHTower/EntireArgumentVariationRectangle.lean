import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodRectangle

/-!
# The argument principle in argument-variation form

Taking the imaginary part of the unweighted rectangle argument principle expresses the variation of
the argument of an entire function along the *left* edge of a rectangle in terms of the variation
along the other three edges and the number of enclosed zeros:

```text
∫_{T₁}^{T₂} Re (f'/f)(c+it) dt
  = ∫_{T₁}^{T₂} Re (f'/f)(d+it) dt
    + ∫_c^d Im (f'/f)(x+iT₁) dx - ∫_c^d Im (f'/f)(x+iT₂) dx
    - 2π · (number of zeros in the rectangle, with multiplicity).
```

The left-hand side is the phase advance of `f` along the left edge, so an upper bound for the
enclosed zero count together with control of the three remaining edges is exactly what turns a
zero-density statement into a lower bound for the number of sign changes of `Re f` on the edge.
-/

open Complex Filter MeasureTheory intervalIntegral Set Topology

namespace RHTower

noncomputable section

private theorem analyticAt_logDeriv_of_ne_aux {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : f z ≠ 0) :
    AnalyticAt ℂ (logDeriv f) z := by
  have h : AnalyticAt ℂ (fun w => deriv f w / f w) z :=
    hf.deriv.div hf hz
  refine h.congr ?_
  filter_upwards with w
  rw [logDeriv_apply]

/-- **The argument principle in argument-variation form.**  For an entire `f` nonvanishing on the
boundary of the rectangle `[c,d]×[T₁,T₂]`, the argument variation along the left edge equals the
variation along the other three edges minus `2π` times the enclosed zero count. -/
theorem exists_entire_argument_variation_rectangle
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0)
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, f ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ t ∈ uIcc T₁ T₂, f ((c : ℂ) + t * I) ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ f z = 0) ∧
      (∫ t in T₁..T₂, (logDeriv f ((c : ℂ) + t * I)).re)
        = (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re)
          + (∫ x in c..d, (logDeriv f ((x : ℂ) + T₁ * I)).im)
          - (∫ x in c..d, (logDeriv f ((x : ℂ) + T₂ * I)).im)
          - 2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℝ) := by
  classical
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
  have hval : rectIntegral (logDeriv f) z₁ z₂ =
      2 * Real.pi * I *
        ∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℂ) * (1 : ℂ) := by
    have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
      Z (fun w => w) m (f := f) (g := fun _ => (1 : ℂ)) (h := h)
      (z₁ := z₁) (z₂ := z₂) (U := V) hVopen
      (fun z _ => analyticAt_const)
      (by simpa [z₁, z₂] using hin) (by simpa [z₁, z₂] using hsubV)
      (hhan.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
      (fun z _ => hfact z (Set.mem_univ z))
    simp only [one_mul] at hres
    rw [hres]
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    rw [hm w hw]
  have hqbot : ContinuousOn
      (fun x : ℝ => logDeriv f ((x : ℂ) + T₁ * I)) (uIcc c d) := by
    intro x hx
    have hc := ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + T₁ * I)
      (analyticAt_logDeriv_of_ne_aux (hf _ (Set.mem_univ _)) (hbot x hx)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + T₁ * I) x)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hqtop : ContinuousOn
      (fun x : ℝ => logDeriv f ((x : ℂ) + T₂ * I)) (uIcc c d) := by
    intro x hx
    have hc := ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + T₂ * I)
      (analyticAt_logDeriv_of_ne_aux (hf _ (Set.mem_univ _)) (htop x hx)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + T₂ * I) x)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hqright : ContinuousOn
      (fun t : ℝ => logDeriv f ((d : ℂ) + t * I)) (uIcc T₁ T₂) := by
    intro t ht
    have hc := ContinuousAt.comp (f := fun y : ℝ => (d : ℂ) + y * I)
      (analyticAt_logDeriv_of_ne_aux (hf _ (Set.mem_univ _)) (hright t ht)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (d : ℂ) + y * I) t)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hqleft : ContinuousOn
      (fun t : ℝ => logDeriv f ((c : ℂ) + t * I)) (uIcc T₁ T₂) := by
    intro t ht
    have hc := ContinuousAt.comp (f := fun y : ℝ => (c : ℂ) + y * I)
      (analyticAt_logDeriv_of_ne_aux (hf _ (Set.mem_univ _)) (hleft t ht)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (c : ℂ) + y * I) t)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hedges := two_pi_mul_weighted_re_sum_eq_edges
    (F := logDeriv f) (z₁ := z₁) (z₂ := z₂) (Z := Z)
    (m := fun w => (analyticOrderAt f w).toNat) (g := fun _ => (1 : ℂ))
    hval
    (by simpa [z₁, z₂] using hqbot.intervalIntegrable)
    (by simpa [z₁, z₂] using hqtop.intervalIntegrable)
    (by simpa [z₁, z₂] using hqright.intervalIntegrable)
    (by simpa [z₁, z₂] using hqleft.intervalIntegrable)
  simp only [Complex.one_re, mul_one, z₁, z₂] at hedges
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at hedges
  refine ⟨Z, hmem, ?_⟩
  norm_num at hedges
  linarith [hedges]

end

end RHTower
