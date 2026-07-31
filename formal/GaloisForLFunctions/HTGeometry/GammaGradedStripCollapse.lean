import GaloisForLFunctions.HTGeometry.GammaSumValuationBoundary

/-!
# Unconditional finite-phase collapse for the whole graded coefficient algebra

The coefficients of a differential relation over the Gamma field are finite sums of graded monomials
`c(s)·w(s)^b·P(Γ)/Q(Γ)`, not single monomials.  Each such sum is asymptotic to its own dominant
monomial, so the projective comparison of two coefficients is the comparison of their dominant
monomials.  Feeding that into the Bohr hull of the strip gives eq. (8) for the entire graded algebra:

if a holomorphic vertically almost-periodic `f` satisfies `∑_α F_α · M_α(f) = 0` with every `F_α` a
sum of graded monomials, and the dominant monomial of `F_β` strictly dominates the dominant monomial
of every other `F_α`, then `M_β(f)` vanishes identically on the strip.

Nothing in the statement or the proof is hypothetical: the return times come from almost periodicity
and the coefficient boundary from the valuation ordering.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- **Finite-phase collapse over the graded coefficient algebra.** -/
theorem gradedSum_strip_relation_dominant_monomial_eq_zero
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (E : Finset ι) (P : ι → Finset κ)
    {w : ℂ → ℂ} (hw : ∀ x : ℝ, 0 < x → IsVerticalLogWeight w x)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ))
    (D : ι → κ → GammaRationalDatum) (c : ι → κ → Polynomial ℂ) (b : ι → κ → ℕ)
    (m : ι → κ) (β : ι) (hβ : β ∈ E)
    (hm : ∀ α ∈ E, m α ∈ P α)
    (hcm : ∀ α ∈ E, c α (m α) ≠ 0)
    (hinner : ∀ α ∈ E, ∀ q ∈ P α, q ≠ m α →
      StrictlySubordinateAt (D α q) (D α (m α)) (c α q).natDegree (b α q)
        (c α (m α)).natDegree (b α (m α)))
    (houter : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α (m α)) (D β (m β)) (c α (m α)).natDegree (b α (m α))
        (c β (m β)).natDegree (b β (m β)))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) w (b α q) s) * diffMonomial f (exps α) s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, diffMonomial f (exps β) z₀ = 0 := by
  classical
  obtain ⟨T, hT, hmain⟩ :=
    verticalStrip_recurrence_collapse E hη f exps
      (fun α s => ∑ q ∈ P α, (D α q).polyWeightedFn (c α q) w (b α q) s) β hβ hf hap hrel
  intro z₀ hz₀
  have hzre : 0 < z₀.re := by
    have habs : |z₀.re - σ| < η := hz₀
    have hlt := (abs_lt.mp habs).1
    linarith
  have hwz := hw z₀.re hzre
  have hFβ : ∀ᶠ l in atTop,
      (∑ q ∈ P β, (D β q).polyWeightedFn (c β q) w (b β q)
        (z₀ + (T l : ℂ) * Complex.I)) ≠ 0 :=
    eventually_vertical_along_returns
      (p := fun s => (∑ q ∈ P β, (D β q).polyWeightedFn (c β q) w (b β q) s) ≠ 0)
      (z₀ := z₀)
      (polyWeightedSum_eventually_ne_zero (P β) (D β) (c β) (b β) (m β) (hm β hβ)
        (hcm β hβ) (hinner β hβ) hzre hwz) hT
  have hcoeff : ∀ α ∈ E, Tendsto
      (fun l => (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) w (b α q)
            (z₀ + (T l : ℂ) * Complex.I)) /
        (∑ q ∈ P β, (D β q).polyWeightedFn (c β q) w (b β q)
            (z₀ + (T l : ℂ) * Complex.I)))
      atTop (nhds (if α = β then (1 : ℂ) else 0)) := by
    intro α hα
    rcases eq_or_ne α β with hab | hab
    · subst hab
      have hone : Tendsto
          (fun l => (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) w (b α q)
                (z₀ + (T l : ℂ) * Complex.I)) /
            (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) w (b α q)
                (z₀ + (T l : ℂ) * Complex.I)))
          atTop (nhds (1 : ℂ)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hFβ] with l hl
        exact (div_self hl).symm
      simpa using hone
    · have hdomRatio := polyWeightedRatio_tendsto_zero_of_subordinate
        (D α (m α)) (D β (m β)) (c α (m α)) (c β (m β)) (hcm β hβ) (b α (m α)) (b β (m β))
        (houter α hα hab) hzre hwz
      have hzero := tendsto_polyWeightedSum_ratio (P α) (P β) (D α) (c α) (b α)
        (D β) (c β) (b β) (m α) (hm α hα) (hcm α hα) (m β) (hm β hβ) (hcm β hβ)
        (hinner α hα) (hinner β hβ) hzre hwz hdomRatio
      simpa [hab] using tendsto_vertical_along_returns
        (F := fun s => (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) w (b α q) s) /
          (∑ q ∈ P β, (D β q).polyWeightedFn (c β q) w (b β q) s))
        (z₀ := z₀) hzero hT
  have hcollapse := hmain z₀ hz₀ (fun α => if α = β then (1 : ℂ) else 0) hFβ hcoeff
  have hred := Finset.sum_eq_single_of_mem β hβ
    (f := fun α : ι => (if α = β then (1 : ℂ) else 0) * diffMonomial f (exps α) z₀)
    (by
      intro q _ hq
      simp [hq])
  have hzero := hcollapse.1
  rw [hred] at hzero
  simpa using hzero

/-- **The digamma instance.**  Eq. (8) for coefficients that are arbitrary finite sums of graded
monomials `c(s)·ψ(s)^b·P(Γ)/Q(Γ)`. -/
theorem digammaGraded_strip_relation_dominant_monomial_eq_zero
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (E : Finset ι) (P : ι → Finset κ)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ))
    (D : ι → κ → GammaRationalDatum) (c : ι → κ → Polynomial ℂ) (b : ι → κ → ℕ)
    (m : ι → κ) (β : ι) (hβ : β ∈ E)
    (hm : ∀ α ∈ E, m α ∈ P α)
    (hcm : ∀ α ∈ E, c α (m α) ≠ 0)
    (hinner : ∀ α ∈ E, ∀ q ∈ P α, q ≠ m α →
      StrictlySubordinateAt (D α q) (D α (m α)) (c α q).natDegree (b α q)
        (c α (m α)).natDegree (b α (m α)))
    (houter : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α (m α)) (D β (m β)) (c α (m α)).natDegree (b α (m α))
        (c β (m β)).natDegree (b β (m β)))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) Complex.digamma (b α q) s) *
        diffMonomial f (exps α) s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, diffMonomial f (exps β) z₀ = 0 :=
  gradedSum_strip_relation_dominant_monomial_eq_zero E P
    (fun _x hx => isVerticalLogWeight_digamma hx.le) hη hση f exps D c b m β hβ hm hcm
    hinner houter hf hap hrel

end

end GaloisForLFunctions
