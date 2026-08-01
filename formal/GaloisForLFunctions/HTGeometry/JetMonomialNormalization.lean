import GaloisForLFunctions.HTGeometry.JetDominantClassLimit

/-!
# The normalized jet monomial is the monomial itself

A monomial in the digamma jets, divided by the normalization factor of its own datum — log degree
`e 0`, argument degree `Σ_j j·e_j` — is exactly the product of the normalized jets.  So the limit
laws stated for the normalized jets are laws about the monomials of `ℂ(s)⟨ψ⟩`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- The monomial in the digamma jets with exponent vector `e`, on a vertical line. -/
noncomputable def jetMonomial (σ : ℝ) {n : ℕ} (e : Fin (n + 1) → ℕ) (t : ℝ) : ℂ :=
  ∏ j : Fin (n + 1),
    (iteratedDeriv (j : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e j)

/-- The argument degree of a jet monomial: each jet of order `j` contributes `j`. -/
def jetSDeg {n : ℕ} (e : Fin (n + 1) → ℕ) : ℕ := ∑ j : Fin (n + 1), (j : ℕ) * e j

/-- Each normalized jet is the jet times its own normalizing weight. -/
theorem normJet_eq_mul (σ : ℝ) (j : ℕ) (t : ℝ) :
    normJet σ j t = iteratedDeriv j Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      * (if j = 0 then (vertLog t)⁻¹ else ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j) := by
  rw [normJet]
  split_ifs with h
  · rw [h, iteratedDeriv_zero, div_eq_mul_inv]
  · ring

/-- **The normalized monomial.**  The product of the normalized jets is the monomial divided by the
normalization factor of its datum. -/
theorem prod_normJet_mul_jetNormFactor (σ : ℝ) {n : ℕ} (e : Fin (n + 1) → ℕ) {t : ℝ}
    (hL : vertLog t ≠ 0) (hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    (∏ j : Fin (n + 1), (normJet σ (j : ℕ) t) ^ (e j))
        * jetNormFactor σ (e 0) (jetSDeg e) t
      = jetMonomial σ e t := by
  have hsplit : (∏ j : Fin (n + 1), (normJet σ (j : ℕ) t) ^ (e j))
      = (∏ j : Fin (n + 1),
          (iteratedDeriv (j : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e j))
        * ∏ j : Fin (n + 1),
          (if (j : ℕ) = 0 then (vertLog t)⁻¹
            else ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (j : ℕ)) ^ (e j) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [normJet_eq_mul, mul_pow]
  have hweight : (∏ j : Fin (n + 1),
      (if (j : ℕ) = 0 then (vertLog t)⁻¹
        else ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (j : ℕ)) ^ (e j))
      = ((vertLog t)⁻¹) ^ (e 0) * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (jetSDeg e) := by
    rw [Fin.prod_univ_succ]
    have hzero : ((if ((0 : Fin (n + 1)) : ℕ) = 0 then (vertLog t)⁻¹
        else ((σ : ℂ) + (t : ℂ) * Complex.I) ^ ((0 : Fin (n + 1)) : ℕ)) ^ (e 0))
        = ((vertLog t)⁻¹) ^ (e 0) := by
      simp
    rw [hzero]
    congr 1
    have hsucc : ∀ i : Fin n,
        (if ((i.succ : Fin (n + 1)) : ℕ) = 0 then (vertLog t)⁻¹
          else ((σ : ℂ) + (t : ℂ) * Complex.I) ^ ((i.succ : Fin (n + 1)) : ℕ)) ^ (e i.succ)
        = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (((i.succ : Fin (n + 1)) : ℕ) * e i.succ) := by
      intro i
      rw [if_neg (by simp), ← pow_mul]
    rw [Finset.prod_congr rfl (fun i _ => hsucc i), Finset.prod_pow_eq_pow_sum, jetSDeg,
      Fin.sum_univ_succ]
    simp
  rw [hsplit, hweight, jetNormFactor, jetMonomial]
  field_simp
  have hcancel : ((1 : ℂ) / vertLog t) ^ (e 0) * (vertLog t) ^ (e 0) = 1 := by
    rw [div_pow, one_pow, div_mul_cancel₀ _ (pow_ne_zero _ hL)]
  rw [mul_assoc, hcancel, mul_one]

/-- **The monomial law.**  A jet monomial, divided by the normalization factor of its own datum,
converges to the product of the jet leading constants — a nonzero number. -/
theorem tendsto_jetMonomial_div_jetNormFactor (hσ : 0 < σ) {n : ℕ} (e : Fin (n + 1) → ℕ) :
    Tendsto (fun t : ℝ => jetMonomial σ e t / jetNormFactor σ (e 0) (jetSDeg e) t) atTop
      (nhds (∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e j))) := by
  refine (tendsto_prod_normJet hσ e).congr' ?_
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ,
    eventually_jetNormFactor_ne_zero hσ (e 0) (jetSDeg e)] with t hL hs hF
  rw [← prod_normJet_mul_jetNormFactor σ e hL hs, mul_div_assoc, div_self hF, mul_one]

/-- **Eq. (19) for a finite combination of jet monomials.**  Dividing by the normalization factor of
a dominant datum, the combination converges to the sum of the leading constants over the members
sharing that datum. -/
theorem tendsto_sum_jetMonomial_div_dominant (hσ : 0 < σ) {n N : ℕ} (d : Fin N → ℂ)
    (e : Fin N → Fin (n + 1) → ℕ) (β : Fin N)
    (hdom : ∀ α : Fin N, (e α 0 = e β 0 ∧ jetSDeg (e α) = jetSDeg (e β))
      ∨ (jetSDeg (e β) < jetSDeg (e α)
        ∨ (jetSDeg (e β) = jetSDeg (e α) ∧ e α 0 < e β 0))) :
    Tendsto (fun t : ℝ => (∑ α : Fin N, d α * jetMonomial σ (e α) t)
        / jetNormFactor σ (e β 0) (jetSDeg (e β)) t) atTop
      (nhds (∑ α ∈ Finset.univ.filter
          (fun α : Fin N => e α 0 = e β 0 ∧ jetSDeg (e α) = jetSDeg (e β)),
        d α * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j))) := by
  classical
  refine (tendsto_sum_normJet_dominant hσ d e (fun α => e α 0) (fun α => jetSDeg (e α))
    (e β 0) (jetSDeg (e β)) hdom).congr' ?_
  filter_upwards [eventually_vertLog_ne_zero, eventually_vertical_ne_zero σ,
    eventually_jetNormFactor_ne_zero hσ (e β 0) (jetSDeg (e β))] with t hL hs hF
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [← prod_normJet_mul_jetNormFactor σ (e α) hL hs]
  field_simp

end GaloisForLFunctions
