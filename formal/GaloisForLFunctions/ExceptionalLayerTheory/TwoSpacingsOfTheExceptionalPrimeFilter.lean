import GaloisForLFunctions.ExceptionalLayerTheory.ArbitraryDampingContractionReadsTheDivisor

/-!
# Recovering the order of a divisor filter by changing its spacing

The moving-dilation argument of Ponge–Tian (arXiv:2605.25591, Lemma 2.17)
applies to two readings of the same arithmetic filter at the same height.
Their quotient cancels the Gaussian kernel, the selected zero's
multiplicity and the divisor product. It retains the order of the spacing
zero. Recovery is uniform over arbitrarily small positive spacings.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem uniform_below_envelope {R : ℝ → ℝ → ℂ} {C : ℂ}
    (hall : ∀ h : ℝ → ℝ, Tendsto h atTop (𝓝 0) → (∀ᶠ t in atTop, 0 < h t) →
      Tendsto (fun t => R t (h t)) atTop (𝓝 C))
    {H : ℝ → ℝ} (hH : Tendsto H atTop (𝓝 0)) (hpos : ∀ᶠ t in atTop, 0 < H t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ s, 0 < s → s ≤ H t → dist (R t s) C < ε := by
  classical
  let bad (t s : ℝ) := 0 < s ∧ s ≤ H t ∧ ε ≤ dist (R t s) C
  let h (t : ℝ) := if e : ∃ s, bad t s then e.choose else H t
  have hp : ∀ᶠ t in atTop, 0 < h t := by
    filter_upwards [hpos] with t ht
    dsimp only [h]
    split
    next e => exact e.choose_spec.1
    next => exact ht
  have hb (t : ℝ) : h t ≤ H t := by
    dsimp only [h]
    split
    next e => exact e.choose_spec.2.1
    next => exact le_rfl
  have hlim : Tendsto h atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hH
      (hp.mono fun _ ht => ht.le) (Eventually.of_forall hb)
  filter_upwards [Metric.tendsto_nhds.mp (hall h hlim hp) ε hε] with t ht s hs hsH
  by_contra! hbad
  have e : ∃ s, bad t s := ⟨s,hs,hsH,hbad⟩
  exact (not_lt_of_ge e.choose_spec.2.2) (by simpa only [h,dif_pos e] using ht)

/-- The actual prime reading at height t and spacing s. -/
def topFilterReading (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a t s : ℝ) : ℂ :=
  primeDampingFilter (divisorDampingFilter F ρ β s) σ β a s t

/-- Failure of the asymptotic abscissa law gives an ordinary-prime filter
whose normalized reading converges uniformly over the whole interval
of spacings below any shrinking envelope. -/
theorem finite_top_filter_uniform_recovery :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (q : XiZeroCopy) (σ a : ℝ), q ∈ F ∧
        1/2 < σ ∧ σ < (xiZero q).re ∧ 0 < a ∧
        let ρ := xiZero q
        let d := 1+(F.filter (fun p => xiZero p ≠ ρ)).card
        ∃ C : ℂ, C ≠ 0 ∧ ∀ H : ℝ → ℝ, Tendsto H atTop (𝓝 0) →
          (∀ᶠ t in atTop, 0 < H t) → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ t in atTop, ∀ s : ℝ, 0 < s → s ≤ H t →
            dist (topFilterReading F ρ σ ρ.re a t s /
              ((s:ℂ)^d * gaussianMBKernel (Real.exp (-a*t)) (ρ-((σ:ℂ)+t*I)))) C < ε := by
  intro hf
  obtain ⟨F,σ,β,hσ,hgap,_,⟨q,hq,hqβ⟩,_,hall⟩ :=
    not_asymptoticAbscissaLaw_has_arbitrarily_contracting_prime_filters hf
  let a := Real.pi/(β-σ)
  have hd := sub_pos.mpr hgap
  have ha : 0 < a := div_pos Real.pi_pos hd
  have hr : 0 < gaussianObservationRate (xiZero q) σ a := by
    rw [gaussianObservationRate,hqβ,show a*(β-σ)=Real.pi from div_mul_cancel₀ _ hd.ne']
    linarith only [Real.pi_pos]
  obtain ⟨hC,hlim⟩ := hall q hq hqβ
  refine ⟨F,q,σ,a,hq,hσ,hqβ.symm ▸ hgap,ha,_,hC,?_⟩
  intro H hH hp ε hε
  rw [hqβ]
  exact uniform_below_envelope (hlim a ha hr) hH hp hε

/-- At the same height a fixed dilation of a contracting spacing changes
the unnormalized prime reading by the dilation to the exact filter order.
The limiting factor depends only on the number of retained divisor copies. -/
theorem finite_top_filter_spacing_dilation :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (q : XiZeroCopy) (σ a : ℝ), q ∈ F ∧
        1/2 < σ ∧ σ < (xiZero q).re ∧ 0 < a ∧
        ∀ (h : ℝ → ℝ), Tendsto h atTop (𝓝 0) → (∀ᶠ t in atTop, 0 < h t) →
        ∀ lam : ℝ, 0 < lam →
          Tendsto (fun t => topFilterReading F (xiZero q) σ (xiZero q).re a t (lam*h t) /
            topFilterReading F (xiZero q) σ (xiZero q).re a t (h t)) atTop
            (𝓝 ((lam:ℂ)^(1+(F.filter fun p => xiZero p ≠ xiZero q).card))) := by
  intro hf
  obtain ⟨F,q,σ,a,hq,hσ,hgap,ha,C,hC,hu⟩ := finite_top_filter_uniform_recovery hf
  refine ⟨F,q,σ,a,hq,hσ,hgap,ha,fun h hh hp lam hlam => ?_⟩
  let ρ := xiZero q
  let d := 1+(F.filter fun p => xiZero p ≠ ρ).card
  let A (t s : ℝ) := topFilterReading F ρ σ ρ.re a t s
  let K (t : ℝ) := gaussianMBKernel (Real.exp (-a*t)) (ρ-((σ:ℂ)+t*I))
  have recover (g : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0)) (hgp : ∀ᶠ t in atTop, 0 < g t) :
      Tendsto (fun t => A t (g t)/((g t:ℂ)^d*K t)) atTop (𝓝 C) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hu g hg hgp ε hε,hgp] with t ht hg'
    exact ht _ hg' le_rfl
  have hg : Tendsto (fun t => lam*h t) atTop (𝓝 0) := by simpa only [mul_zero] using hh.const_mul lam
  have H := recover h hh hp
  have G := recover (fun t => lam*h t) hg (hp.mono fun _ ht => mul_pos hlam ht)
  have Hnz := H.eventually_ne hC
  have ratio := ((G.div H hC).const_mul ((lam:ℂ)^d))
  rw [div_self hC,mul_one] at ratio
  apply ratio.congr'
  filter_upwards [Hnz,hp] with t hn ht
  have hak : A t (h t) ≠ 0 := fun hz => hn (by rw [hz,zero_div])
  have hk : K t ≠ 0 := fun hz => hn (by rw [hz,mul_zero,div_zero])
  have hlam' : (lam:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have h' : (h t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  change (lam:ℂ)^d*((A t (lam*h t)/(((lam*h t:ℝ):ℂ)^d*K t))/(A t (h t)/((h t:ℂ)^d*K t))) = _
  rw [Complex.ofReal_mul,mul_pow]
  field_simp
  exact (mul_div_cancel_left₀ (A t (lam*h t)) hak).symm

#print axioms finite_top_filter_uniform_recovery
#print axioms finite_top_filter_spacing_dilation

end GaloisForLFunctions.ExceptionalLayerTheory
