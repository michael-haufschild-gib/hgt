import GaloisForLFunctions.HTGeometry.PolynomialWeightedValuationBoundary

/-!
# A finite sum of graded monomials is asymptotically its dominant monomial

Equation (19) says that a nonzero element of the coefficient field has an exact leading term.  For a
finite sum of monomials `c_α(s)·w(s)^{b α}·P_α(Γ)/Q_α(Γ)` the ordering already decides which term is
dominant, and dividing the sum by that term makes every other summand tend to zero.  Hence the sum is
asymptotic to its dominant monomial — in particular **it does not cancel**: a nonzero sum of graded
monomials is eventually nonvanishing on a vertical line, with a computable leading behaviour.

That no-cancellation statement is the unconditional fragment of the transfer step of §3: for the
graded monomial algebra it is a theorem, with no appeal to hypertranscendence of the formal Stirling
series.  Ratios of two such sums are then governed by the ratio of their dominant monomials.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- The trivial Gamma-rational datum, with value identically `1`. -/
def GammaRationalDatum.one : GammaRationalDatum where
  numOrder := 0
  denOrder := 0
  numUnit := 1
  denUnit := 1
  numUnit_ne := by simp
  denUnit_ne := by simp

@[simp] theorem GammaRationalDatum.fn_one (s : ℂ) : GammaRationalDatum.one.fn s = 1 := by
  simp [GammaRationalDatum.fn, GammaRationalDatum.num, GammaRationalDatum.den,
    GammaRationalDatum.one]

/-- The limit of each normalized summand: `1` at the dominant index and `0` elsewhere. -/
theorem tendsto_polyWeightedTerm_div_dominant {ι : Type*} [DecidableEq ι] (E : Finset ι)
    (D : ι → GammaRationalDatum) (c : ι → Polynomial ℂ) (b : ι → ℕ) {w : ℂ → ℂ}
    (β : ι) (hcβ : c β ≠ 0)
    (hdom : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α) (D β) (c α).natDegree (b α) (c β).natDegree (b β))
    {σ : ℝ} (hσ : 0 < σ) (hw : IsVerticalLogWeight w σ) :
    ∀ α ∈ E, Tendsto (fun t : ℝ =>
        (D α).polyWeightedFn (c α) w (b α) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          (D β).polyWeightedFn (c β) w (b β) ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds (if α = β then (1 : ℂ) else 0)) := by
  intro α hα
  rcases eq_or_ne α β with hab | hne
  · subst hab
    rw [if_pos rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [polyWeightedFn_eventually_ne_zero (D α) hcβ hσ hw (b α)] with t hl
    exact (div_self hl).symm
  · rw [if_neg hne]
    exact polyWeightedRatio_tendsto_zero_of_subordinate (D α) (D β) (c α) (c β) hcβ
      (b α) (b β) (hdom α hα hne) hσ hw

/-- **The sum is asymptotic to its dominant monomial.** -/
theorem tendsto_polyWeightedSum_div_dominant {ι : Type*} [DecidableEq ι] (E : Finset ι)
    (D : ι → GammaRationalDatum) (c : ι → Polynomial ℂ) (b : ι → ℕ) {w : ℂ → ℂ}
    (β : ι) (hβ : β ∈ E) (hcβ : c β ≠ 0)
    (hdom : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α) (D β) (c α).natDegree (b α) (c β).natDegree (b β))
    {σ : ℝ} (hσ : 0 < σ) (hw : IsVerticalLogWeight w σ) :
    Tendsto (fun t : ℝ =>
        (∑ α ∈ E, (D α).polyWeightedFn (c α) w (b α) ((σ : ℂ) + (t : ℂ) * Complex.I)) /
          (D β).polyWeightedFn (c β) w (b β) ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 1) := by
  classical
  have hterms := tendsto_polyWeightedTerm_div_dominant E D c b β hcβ hdom hσ hw
  have hmodel := tendsto_finsetSum (f := fun (α : ι) (t : ℝ) =>
      (D α).polyWeightedFn (c α) w (b α) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        (D β).polyWeightedFn (c β) w (b β) ((σ : ℂ) + (t : ℂ) * Complex.I))
    (a := fun α => if α = β then (1 : ℂ) else 0) E hterms
  have hsum : (∑ α ∈ E, if α = β then (1 : ℂ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' E β (fun _ => (1 : ℂ)), if_pos hβ]
  rw [hsum] at hmodel
  refine hmodel.congr (fun t => ?_)
  rw [Finset.sum_div]

/-- **No cancellation.**  A sum of graded monomials with a strictly dominant term is eventually
nonvanishing on a vertical line. -/
theorem polyWeightedSum_eventually_ne_zero {ι : Type*} [DecidableEq ι] (E : Finset ι)
    (D : ι → GammaRationalDatum) (c : ι → Polynomial ℂ) (b : ι → ℕ) {w : ℂ → ℂ}
    (β : ι) (hβ : β ∈ E) (hcβ : c β ≠ 0)
    (hdom : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α) (D β) (c α).natDegree (b α) (c β).natDegree (b β))
    {σ : ℝ} (hσ : 0 < σ) (hw : IsVerticalLogWeight w σ) :
    ∀ᶠ t : ℝ in atTop,
      (∑ α ∈ E, (D α).polyWeightedFn (c α) w (b α) ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
  have h := (tendsto_polyWeightedSum_div_dominant E D c b β hβ hcβ hdom hσ hw).eventually
    (isOpen_ne.mem_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  filter_upwards [h] with t ht
  intro hzero
  rw [hzero, zero_div] at ht
  exact ht rfl

/-- **The projective boundary of two sums is that of their dominant monomials.**  Given the limit of
the dominant ratio, the ratio of the sums has the same limit. -/
theorem tendsto_polyWeightedSum_ratio {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (E : Finset ι) (F : Finset κ)
    (D : ι → GammaRationalDatum) (c : ι → Polynomial ℂ) (b : ι → ℕ)
    (D' : κ → GammaRationalDatum) (c' : κ → Polynomial ℂ) (b' : κ → ℕ) {w : ℂ → ℂ}
    (β : ι) (hβ : β ∈ E) (hcβ : c β ≠ 0)
    (γ : κ) (hγ : γ ∈ F) (hcγ : c' γ ≠ 0)
    (hdomE : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α) (D β) (c α).natDegree (b α) (c β).natDegree (b β))
    (hdomF : ∀ α ∈ F, α ≠ γ →
      StrictlySubordinateAt (D' α) (D' γ) (c' α).natDegree (b' α) (c' γ).natDegree (b' γ))
    {σ : ℝ} (hσ : 0 < σ) (hw : IsVerticalLogWeight w σ) {L : ℂ}
    (hL : Tendsto (fun t : ℝ =>
        (D β).polyWeightedFn (c β) w (b β) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          (D' γ).polyWeightedFn (c' γ) w (b' γ) ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds L)) :
    Tendsto (fun t : ℝ =>
        (∑ α ∈ E, (D α).polyWeightedFn (c α) w (b α) ((σ : ℂ) + (t : ℂ) * Complex.I)) /
          (∑ α ∈ F, (D' α).polyWeightedFn (c' α) w (b' α) ((σ : ℂ) + (t : ℂ) * Complex.I)))
      atTop (nhds L) := by
  classical
  have hE := tendsto_polyWeightedSum_div_dominant E D c b β hβ hcβ hdomE hσ hw
  have hF := tendsto_polyWeightedSum_div_dominant F D' c' b' γ hγ hcγ hdomF hσ hw
  have hFinv : Tendsto (fun t : ℝ =>
      ((D' γ).polyWeightedFn (c' γ) w (b' γ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        (∑ α ∈ F, (D' α).polyWeightedFn (c' α) w (b' α) ((σ : ℂ) + (t : ℂ) * Complex.I))))
      atTop (nhds 1) := by
    have := hF.inv₀ (one_ne_zero : (1 : ℂ) ≠ 0)
    simpa [inv_div] using this
  have hmul := (hE.mul hL).mul hFinv
  rw [one_mul, mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [polyWeightedFn_eventually_ne_zero (D β) hcβ hσ hw (b β),
    polyWeightedFn_eventually_ne_zero (D' γ) hcγ hσ hw (b' γ)] with t hβt hγt
  field_simp

end

end GaloisForLFunctions
