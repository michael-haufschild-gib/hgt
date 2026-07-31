import GaloisForLFunctions.HTGeometry.DigammaValuationBoundary

/-!
# Arbitrary polynomial coefficients in the valuation ordering

The `s`-part of a coefficient of eq. (19) is a rational function, not a monomial.  On a vertical line
a polynomial is asymptotically its leading monomial — `c(s)/s^{deg c} → lead c` — so replacing the
monomial `s^a` by an arbitrary polynomial only multiplies every normalized ratio by a factor
converging to the quotient of leading coefficients.  The whole ordering therefore transfers, and the
collapse holds for coefficients

`c(s) · w(s)^b · P(Γ)/Q(Γ)`,  `c ∈ ℂ[s]`,  `w ∈ {log, ψ}`,

with the lexicographic comparison run on `(deg c, b)`.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-! ### A polynomial is its leading monomial on a vertical line -/

/-- On a vertical line a polynomial is asymptotically its leading monomial. -/
theorem tendsto_polynomial_eval_div_pow_vertical (c : Polynomial ℂ) (σ : ℝ) :
    Tendsto (fun t : ℝ =>
        c.eval ((σ : ℂ) + (t : ℂ) * Complex.I) /
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ c.natDegree)
      atTop (nhds c.leadingCoeff) := by
  classical
  set d : ℕ := c.natDegree with hd
  have hmodel : Tendsto (fun t : ℝ =>
      ∑ i ∈ Finset.range (d + 1),
        c.coeff i * ((((σ : ℂ) + (t : ℂ) * Complex.I) ^ (d - i))⁻¹))
      atTop (nhds (∑ i ∈ Finset.range (d + 1), if i = d then c.coeff i else 0)) := by
    refine tendsto_finsetSum _ (fun i hi => ?_)
    rcases eq_or_ne i d with rfl | hne
    · simp
    · have hlt : i < d := by
        have := Finset.mem_range.mp hi
        omega
      have hpos : 0 < d - i := by omega
      have h := tendsto_inv_pow_vertical σ hpos
      rw [if_neg hne]
      simpa using h.const_mul (c.coeff i)
  have hsum : (∑ i ∈ Finset.range (d + 1), if i = d then c.coeff i else 0) = c.leadingCoeff := by
    rw [Finset.sum_ite_eq' (Finset.range (d + 1)) d (fun i => c.coeff i),
      if_pos (Finset.self_mem_range_succ d)]
    rfl
  rw [← hsum]
  refine hmodel.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h] at him
    simp only [Complex.zero_im] at him
    linarith
  rw [Polynomial.eval_eq_sum_range, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hile : i ≤ d := by
    have := Finset.mem_range.mp hi
    omega
  have hsplit : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d
      = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ i * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (d - i) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  field_simp

/-- A nonzero polynomial is eventually nonvanishing on a vertical line. -/
theorem polynomial_eval_eventually_ne_zero {c : Polynomial ℂ} (hc : c ≠ 0) (σ : ℝ) :
    ∀ᶠ t : ℝ in atTop, c.eval ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have hlead : c.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hc
  have h := (tendsto_polynomial_eval_div_pow_vertical c σ).eventually
    (isOpen_ne.mem_nhds hlead)
  filter_upwards [h] with t ht
  intro hzero
  rw [hzero, zero_div] at ht
  exact ht rfl

/-! ### Polynomial-weighted Gamma monomials -/

/-- A Gamma-rational coefficient weighted by `c(s) · w(s)^b` with `c` an arbitrary polynomial. -/
def GammaRationalDatum.polyWeightedFn (D : GammaRationalDatum) (c : Polynomial ℂ) (w : ℂ → ℂ)
    (b : ℕ) (s : ℂ) : ℂ :=
  c.eval s * (w s) ^ b * D.fn s

theorem polyWeightedFn_eq (D : GammaRationalDatum) (c : Polynomial ℂ) (w : ℂ → ℂ) (b : ℕ)
    {s : ℂ} (hs : s ≠ 0) :
    D.polyWeightedFn c w b s
      = (c.eval s / s ^ c.natDegree) * D.weightedFn w c.natDegree b s := by
  simp only [GammaRationalDatum.polyWeightedFn, GammaRationalDatum.weightedFn]
  field_simp

theorem polyWeightedFn_ratio_eq (D₁ D₂ : GammaRationalDatum) (c₁ c₂ : Polynomial ℂ) (w : ℂ → ℂ)
    (b₁ b₂ : ℕ) {s : ℂ} (hs : s ≠ 0) :
    D₁.polyWeightedFn c₁ w b₁ s / D₂.polyWeightedFn c₂ w b₂ s
      = ((c₁.eval s / s ^ c₁.natDegree) / (c₂.eval s / s ^ c₂.natDegree)) *
        (D₁.weightedFn w c₁.natDegree b₁ s / D₂.weightedFn w c₂.natDegree b₂ s) := by
  rw [polyWeightedFn_eq D₁ c₁ w b₁ hs, polyWeightedFn_eq D₂ c₂ w b₂ hs, div_mul_div_comm]

/-- The polynomial prefactors contribute only the quotient of leading coefficients. -/
theorem tendsto_polyPrefactor_ratio (c₁ c₂ : Polynomial ℂ) (hc₂ : c₂ ≠ 0) (σ : ℝ) :
    Tendsto (fun t : ℝ =>
        (c₁.eval ((σ : ℂ) + (t : ℂ) * Complex.I) /
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ c₁.natDegree) /
          (c₂.eval ((σ : ℂ) + (t : ℂ) * Complex.I) /
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ c₂.natDegree))
      atTop (nhds (c₁.leadingCoeff / c₂.leadingCoeff)) :=
  (tendsto_polynomial_eval_div_pow_vertical c₁ σ).div
    (tendsto_polynomial_eval_div_pow_vertical c₂ σ)
    (Polynomial.leadingCoeff_ne_zero.mpr hc₂)

/-- **Strict subordination with arbitrary polynomial prefactors.** -/
theorem polyWeightedRatio_tendsto_zero_of_subordinate (D₁ D₂ : GammaRationalDatum)
    {w : ℂ → ℂ} (c₁ c₂ : Polynomial ℂ) (hc₂ : c₂ ≠ 0) (b₁ b₂ : ℕ)
    (hsub : StrictlySubordinateAt D₁ D₂ c₁.natDegree b₁ c₂.natDegree b₂)
    {σ : ℝ} (hσ : 0 < σ) (hw : IsVerticalLogWeight w σ) :
    Tendsto (fun t : ℝ =>
        D₁.polyWeightedFn c₁ w b₁ ((σ : ℂ) + (t : ℂ) * Complex.I) /
          D₂.polyWeightedFn c₂ w b₂ ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hpre := tendsto_polyPrefactor_ratio c₁ c₂ hc₂ σ
  have hmain := weightedRatio_tendsto_zero_of_subordinate D₁ D₂ c₁.natDegree b₁ c₂.natDegree b₂
    hsub hσ hw
  have hmul := hpre.mul hmain
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h] at him
    simp only [Complex.zero_im] at him
    linarith
  exact (polyWeightedFn_ratio_eq D₁ D₂ c₁ c₂ w b₁ b₂ hsne).symm

/-- Eventual nonvanishing of a polynomial-weighted Gamma monomial with nonzero prefactor. -/
theorem polyWeightedFn_eventually_ne_zero (D : GammaRationalDatum) {c : Polynomial ℂ}
    (hc : c ≠ 0) {w : ℂ → ℂ} {σ : ℝ} (hσ : 0 < σ) (hw : IsVerticalLogWeight w σ) (b : ℕ) :
    ∀ᶠ t : ℝ in atTop, D.polyWeightedFn c w b ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  filter_upwards [polynomial_eval_eventually_ne_zero hc σ,
    hw.tendsto_norm_atTop.eventually_ge_atTop 1,
    gammaRationalDatum_fn_eventually_ne_zero D hσ] with t hcz hw1 hfn
  have hwne : w ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    linarith
  simp only [GammaRationalDatum.polyWeightedFn]
  exact mul_ne_zero (mul_ne_zero hcz (pow_ne_zero _ hwne)) hfn

/-- **Unconditional finite-phase collapse with arbitrary polynomial prefactors.**  For a weight that
is a logarithmic scale on every vertical line of positive abscissa — `Complex.log` and
`Complex.digamma` both are — a holomorphic Bohr almost-periodic `f` satisfying a finite differential
relation whose coefficients are `c_α(s)·w(s)^{b α}·P_α(Γ)/Q_α(Γ)`, with the coefficient at `β`
strictly dominating all the others in the ordering on `(deg c, b)` and Gamma valuation, has
`M_β(f) = 0` identically on the strip. -/
theorem polyWeighted_strip_relation_dominant_monomial_eq_zero
    {ι : Type*} [DecidableEq ι] (E : Finset ι) {w : ℂ → ℂ}
    (hw : ∀ x : ℝ, 0 < x → IsVerticalLogWeight w x)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ))
    (D : ι → GammaRationalDatum) (c : ι → Polynomial ℂ) (b : ι → ℕ)
    (hcne : ∀ α ∈ E, c α ≠ 0) (β : ι) (hβ : β ∈ E)
    (hdom : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α) (D β) (c α).natDegree (b α) (c β).natDegree (b β))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (D α).polyWeightedFn (c α) w (b α) s * diffMonomial f (exps α) s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, diffMonomial f (exps β) z₀ = 0 := by
  classical
  obtain ⟨T, hT, hmain⟩ :=
    verticalStrip_recurrence_collapse E hη f exps
      (fun α => (D α).polyWeightedFn (c α) w (b α)) β hβ hf hap hrel
  intro z₀ hz₀
  have hzre : 0 < z₀.re := by
    have habs : |z₀.re - σ| < η := hz₀
    have hlt := (abs_lt.mp habs).1
    linarith
  have hwz := hw z₀.re hzre
  have hFβ : ∀ᶠ l in atTop,
      (D β).polyWeightedFn (c β) w (b β) (z₀ + (T l : ℂ) * Complex.I) ≠ 0 :=
    eventually_vertical_along_returns
      (p := fun s => (D β).polyWeightedFn (c β) w (b β) s ≠ 0) (z₀ := z₀)
      (polyWeightedFn_eventually_ne_zero (D β) (hcne β hβ) hzre hwz (b β)) hT
  have hcoeff : ∀ α ∈ E, Tendsto
      (fun l => (D α).polyWeightedFn (c α) w (b α) (z₀ + (T l : ℂ) * Complex.I) /
        (D β).polyWeightedFn (c β) w (b β) (z₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (if α = β then (1 : ℂ) else 0)) := by
    intro α hα
    rcases eq_or_ne α β with hab | hab
    · subst hab
      have hone : Tendsto
          (fun l => (D α).polyWeightedFn (c α) w (b α) (z₀ + (T l : ℂ) * Complex.I) /
            (D α).polyWeightedFn (c α) w (b α) (z₀ + (T l : ℂ) * Complex.I))
          atTop (nhds (1 : ℂ)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hFβ] with l hl
        exact (div_self hl).symm
      simpa using hone
    · have hzero := polyWeightedRatio_tendsto_zero_of_subordinate (D α) (D β) (c α) (c β)
        (hcne β hβ) (b α) (b β) (hdom α hα hab) hzre hwz
      simpa [hab] using tendsto_vertical_along_returns
        (F := fun s => (D α).polyWeightedFn (c α) w (b α) s /
          (D β).polyWeightedFn (c β) w (b β) s)
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

/-- **The digamma instance with arbitrary polynomial prefactors.** -/
theorem digammaPoly_strip_relation_dominant_monomial_eq_zero
    {ι : Type*} [DecidableEq ι] (E : Finset ι)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ))
    (D : ι → GammaRationalDatum) (c : ι → Polynomial ℂ) (b : ι → ℕ)
    (hcne : ∀ α ∈ E, c α ≠ 0) (β : ι) (hβ : β ∈ E)
    (hdom : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α) (D β) (c α).natDegree (b α) (c β).natDegree (b β))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (D α).polyWeightedFn (c α) Complex.digamma (b α) s * diffMonomial f (exps α) s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, diffMonomial f (exps β) z₀ = 0 :=
  polyWeighted_strip_relation_dominant_monomial_eq_zero E
    (fun _x hx => isVerticalLogWeight_digamma hx.le) hη hση f exps D c b hcne β hβ hdom hf hap hrel

end

end GaloisForLFunctions
