import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SymmetricDilations.Scales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Vanishing probability from two bounded rows of Gaussian time samples -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.SymmetricDilations
open ShortWindows
noncomputable section

private def count {ι : Type*} {q : ℕ} (h : Fin q → ℝ) (E : Set (ι → ℝ)) (x : ι → ℝ) :=
  dilationCount (fun i => scale (h i)) E x + dilationCount (fun i => scale (-h i)) E x

private theorem row_integral {ι : Type*} [Fintype ι] {q : ℕ} (a : Fin q → ℝ)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] :
    Integrable (dilationCount a E) μ ∧
    (∫ x, dilationCount a E x ∂μ)=∑ i, μ.real ((fun x : ι → ℝ => a i • x) ⁻¹' E) := by
  let f (i : Fin q) := ((fun x : ι → ℝ => a i • x) ⁻¹' E).indicator (fun _ => (1:ℝ))
  have hm (i) := hE.preimage (measurable_id.const_smul (a i))
  have hi (i) : Integrable (f i) μ := (integrable_const _).indicator (hm i)
  refine ⟨integrable_finsetSum _ (fun i _ => hi i),?_⟩
  change (∫ x, ∑ i, f i x ∂μ)=_
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  exact Finset.sum_congr rfl fun i _ => integral_indicator_one (hm i)

/-- Scales can be sampled on the original disorder, including at an
origin determined by that disorder. The cost of atypical prefixes is
bounded by their probability, independently of the number of samples. -/
private theorem finite_count_bound {ι : Type*} [Fintype ι] {q : ℕ} (h : Fin q → ℝ)
    (hh : ∀ i, |h i|≤1/2 ∧ (Fintype.card ι:ℝ)*(h i)^2≤1/2)
    (E : Set (ι → ℝ)) (hE : MeasurableSet E) {L : ℝ} (hL : 0≤L) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    (q:ℝ)*μ.real E ≤ L+2*q*μ.real {x | L<count h E x} := by
  classical
  intro μ
  let f := count h E
  let A := {x | L<f x}
  let a (i) := scale (h i)
  let b (i) := scale (-h i)
  have hm (r : Fin q → ℝ) : Measurable (dilationCount r E) :=
    Finset.measurable_sum _ fun i _ => measurable_const.indicator (hE.preimage (measurable_id.const_smul _))
  have hA : MeasurableSet A := measurableSet_lt measurable_const ((hm a).add (hm b))
  have hcap (r : Fin q → ℝ) (x : ι → ℝ) : dilationCount r E x ≤ q := by
    calc _ ≤ ∑ _ : Fin q, (1:ℝ) := by
           apply Finset.sum_le_sum
           intro i _
           simp only [indicator_apply]
           split <;> norm_num
         _ = _ := by simp
  have hb (x : ι → ℝ) : f x ≤ L+2*(q:ℝ)*A.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x∈A
    · rw [indicator_of_mem hx,mul_one]
      change dilationCount a E x+dilationCount b E x ≤ _
      linarith only [hcap a x,hcap b x,hL]
    · rw [indicator_of_notMem hx,mul_zero,add_zero]
      exact le_of_not_gt hx
  obtain ⟨hai,hae⟩ := row_integral a E hE μ
  obtain ⟨hbi,hbe⟩ := row_integral b E hE μ
  have hi : Integrable (A.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hA
  have hsum := Finset.sum_le_sum (s:=Finset.univ) fun i _ =>
    bounded_precision_price (hh i).1 (hh i).2 E hE
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_add_distrib] at hsum
  have hint := integral_mono (hai.add hbi) ((integrable_const L).add (hi.const_mul (2*(q:ℝ)))) hb
  rw [integral_add hai hbi,hae,hbe,integral_add (integrable_const L) (hi.const_mul _),
    integral_const_mul,integral_indicator_one hA,integral_const,probReal_univ,one_smul] at hint
  exact hsum.trans hint

/-- Boundedly many visits in arbitrarily large finite rows give
vanishing event probability on the actual, overlapping Gaussian prefixes. -/
theorem prefix_mass_of_bounded_counts (E : (k : ℕ) → Set (PrefixIndex (k+1) → ℝ))
    (hE : ∀ k, MeasurableSet (E k)) (h : (q k : ℕ) → Fin q → ℝ) {L : ℝ} (hL : 0≤L)
    (hprice : ∀ q, ∀ᶠ k : ℕ in atTop, ∀ i, |h q k i|≤1/2 ∧
      (Fintype.card (PrefixIndex (k+1)):ℝ)*(h q k i)^2≤1/2)
    (hcount : ∀ q, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      dilationCount (fun i => scale (h q k i)) (E k) (prefixPoint k ω)+
        dilationCount (fun i => scale (-h q k i)) (E k) (prefixPoint k ω) ≤ L) :
    Tendsto (fun k => pathPauliDisorderLaw.real (prefixPoint k ⁻¹' E k)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨q,hq⟩ := exists_nat_gt (L/(ε/2))
  have hq₀ := (div_nonneg hL (half_pos hε).le).trans_lt hq
  let A (k : ℕ) := {x | L<count (h q k) (E k) x}
  have hm (k : ℕ) : MeasurableSet (A k) := by
    have hr (r : Fin q → ℝ) : Measurable (dilationCount r (E k)) :=
      Finset.measurable_sum _ fun i _ => measurable_const.indicator ((hE k).preimage (measurable_id.const_smul _))
    exact measurableSet_lt measurable_const ((hr _).add (hr _))
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by dsimp [μ,pathPauliDisorderLaw]; infer_instance
  have hz := probability_vanishes μ (fun k => prefixPoint k ⁻¹' A k)
    (fun k => (hm k).preimage (gaussian_pauli_prefix_coordinates_law (k+1)).measurable)
    ((hcount q).mono fun ω hω => hω.mono fun k hk => not_lt_of_ge hk)
  filter_upwards [hprice q,hz.eventually_lt_const (show 0<ε/4 by positivity)] with k hp hsmall
  have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
  have hh := finite_count_bound (h q k) hp (E k) (hE k) hL
  have he := hmp.measureReal_preimage (hE k).nullMeasurableSet
  have ha := hmp.measureReal_preimage (hm k).nullMeasurableSet
  change (q:ℝ)*(centredProductGaussian (PrefixIndex (k+1)) 1).real (E k) ≤
    L+2*q*(centredProductGaussian (PrefixIndex (k+1)) 1).real (A k) at hh
  rw [←he,←ha] at hh
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  apply (mul_lt_mul_iff_right₀ hq₀).mp
  have hc := (div_lt_iff₀ (half_pos hε)).mp hq
  have hs := mul_lt_mul_of_pos_left hsmall (show 0<2*(q:ℝ) by positivity)
  linarith only [hh,hc,hs]

#print axioms prefix_mass_of_bounded_counts
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.SymmetricDilations
