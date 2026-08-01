import GaloisForLFunctions.HTGeometry.JetDominantExists

/-!
# The residue of a jet combination with polynomial coefficients

A polynomial coefficient shifts the argument degree of a jet monomial by its own degree, so the
datum of a term `p_α(s)·M_α(s)` is the pair `(e_α 0, deg p_α − Σ_j j·e_{α j})`.  Comparing two such
data needs no integers: `deg p_α − b_α ≤ deg p_β − b_β` is `deg p_α + b_β ≤ deg p_β + b_α`.

Dividing by the shape of a dominant term, the combination converges to the sum of
`lead p_α · Π_j c_j^{e_{α j}}` over the members sharing the datum.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- The asymptotic shape of a term with polynomial coefficient: log degree `a`, coefficient degree
`dP`, monomial argument degree `b`. -/
noncomputable def polyJetShape (σ : ℝ) (a dP b : ℕ) (t : ℝ) : ℂ :=
  (vertLog t) ^ a * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ dP
    / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ b

/-- **The residue of a jet combination with polynomial coefficients.**  Dividing by the shape of a
dominant term, the combination converges to the sum of the leading data over the members sharing the
dominant datum. -/
theorem tendsto_sum_polyCoeff_jetMonomial (hσ : 0 < σ) {n N : ℕ} (p : Fin N → Polynomial ℂ)
    (e : Fin N → Fin (n + 1) → ℕ) (β : Fin N)
    (hdom : ∀ α : Fin N,
      (e α 0 = e β 0 ∧ (p α).natDegree + jetSDeg (e β) = (p β).natDegree + jetSDeg (e α))
      ∨ ((p α).natDegree + jetSDeg (e β) < (p β).natDegree + jetSDeg (e α)
        ∨ ((p α).natDegree + jetSDeg (e β) = (p β).natDegree + jetSDeg (e α)
          ∧ e α 0 < e β 0))) :
    Tendsto (fun t : ℝ =>
        (∑ α : Fin N, (p α).eval ((σ : ℂ) + (t : ℂ) * Complex.I) * jetMonomial σ (e α) t)
          / polyJetShape σ (e β 0) ((p β).natDegree) (jetSDeg (e β)) t) atTop
      (nhds (∑ α ∈ Finset.univ.filter (fun α : Fin N =>
            e α 0 = e β 0 ∧ (p α).natDegree + jetSDeg (e β) = (p β).natDegree + jetSDeg (e α)),
        (p α).leadingCoeff * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j))) := by
  classical
  set A : ℕ := e β 0 with hA
  set B : ℕ := jetSDeg (e β) with hB
  set DP : ℕ := (p β).natDegree with hDP
  -- the limit of each term after normalization
  have hterm : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      ((p α).eval ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I)
          ^ (p α).natDegree)
        * (∏ j : Fin (n + 1), (normJet σ (j : ℕ) t) ^ (e α j))
        * (jetNormFactor σ (e α 0) (DP + jetSDeg (e α)) t
          / jetNormFactor σ A ((p α).natDegree + B) t)) atTop
      (nhds (if (e α 0 = A ∧ (p α).natDegree + B = DP + jetSDeg (e α)) then
        (p α).leadingCoeff * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j) else 0)) := by
    intro α
    have hlead := tendsto_eval_div_pow_natDegree_vertical σ (p α)
    have hprod := tendsto_prod_normJet hσ (e α)
    rcases hdom α with ⟨haa, hbb⟩ | hlt
    · rw [if_pos ⟨haa, hbb⟩]
      have hmul := hlead.mul hprod
      refine hmul.congr' ?_
      filter_upwards [eventually_jetNormFactor_ne_zero hσ A ((p α).natDegree + B)] with t ht
      rw [haa, ← hbb, div_self ht, mul_one]
    · rw [if_neg (by
        rintro ⟨haa, hbb⟩
        rcases hlt with h | ⟨h1, h2⟩
        · omega
        · omega)]
      have hratio : Tendsto (fun t : ℝ => jetNormFactor σ (e α 0) (DP + jetSDeg (e α)) t
          / jetNormFactor σ A ((p α).natDegree + B) t) atTop (nhds 0) := by
        refine tendsto_jetNormFactor_ratio hσ ?_
        rcases hlt with h | ⟨h1, h2⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, h2⟩
      have := (hlead.mul hprod).mul hratio
      rwa [mul_zero] at this
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun α _ => hterm α)
  rw [Finset.sum_filter]
  refine hsum.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ] with t hL hs
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [← prod_normJet_mul_jetNormFactor σ (e α) hL hs, jetNormFactor, jetNormFactor, jetNormFactor,
    polyJetShape]
  field_simp
  ring

end GaloisForLFunctions
