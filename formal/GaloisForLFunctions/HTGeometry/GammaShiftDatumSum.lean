import GaloisForLFunctions.HTGeometry.GammaShiftDatumAlgebra

/-!
# Sums of shifted monomials with distinct signatures

Equation (15) writes an element as a sum of monomials, each with its own signature `(16)`.  When the
signatures are pairwise distinct the sum's datum is the dominant summand's: every other summand is
negligible against the dominant shape, so nothing can cancel the leading constant.

This is the half of eq. (16) that needs no independence input — the tie-breaking half, where several
terms share a signature, is what the formal transseries injection supplies.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {σ lam : ℝ}

/-- **A finite sum with pairwise distinct data has the dominant datum.** -/
theorem hasShiftDatum_sum_of_distinct (hσ : 0 < σ + lam) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hdat : ∀ α, HasShiftDatum lam σ (F α) (d α) (ω α) (b α) (c α))
    (hdist : ∀ α β : Fin N, α ≠ β → ¬(d α = d β ∧ ω α = ω β ∧ b α = b β)) :
    ∃ β : Fin N, HasShiftDatum lam σ (fun t => ∑ α : Fin N, F α t) (d β) (ω β) (b β) (c β) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shiftShape_index hN d ω b
  refine ⟨β, (hdat β).1, ?_⟩
  -- each summand, normalized by the dominant shape
  have hterm : ∀ α : Fin N, Tendsto
      (fun t : ℝ => F α t / gammaShiftShape lam σ (d β) (ω β) (b β) t) atTop
      (nhds (if α = β then c β else 0)) := by
    intro α
    by_cases hα : α = β
    · subst hα
      rw [if_pos rfl]
      exact (hdat α).2
    · rw [if_neg hα]
      have hsub : ShiftShapeDominates (d β) (ω β) (b β) (d α) (ω α) (b α) := by
        rcases hβ α with heq | hsub
        · exact absurd heq (hdist α β hα)
        · exact hsub
      have hzero := tendsto_gammaShiftShape_ratio_zero (σ := σ) hσ hsub
      have hmul := (hdat α).2.mul hzero
      rw [mul_zero] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_ge_atTop (3 : ℝ)] with t ht
      have hSα : gammaShiftShape lam σ (d α) (ω α) (b α) t ≠ 0 :=
        gammaShiftShape_ne_zero hσ ht _ _ _
      have hSβ : gammaShiftShape lam σ (d β) (ω β) (b β) t ≠ 0 :=
        gammaShiftShape_ne_zero hσ ht _ _ _
      field_simp
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun α _ => hterm α)
  have hval : ∑ α : Fin N, (if α = β then c β else 0) = c β := by
    rw [Finset.sum_ite_eq' Finset.univ β (fun _ => c β)]
    simp
  rw [hval] at hsum
  refine hsum.congr fun t => ?_
  rw [Finset.sum_div]

/-- **A finite sum of shifted Gamma monomials with distinct signatures has a datum.**  This is the
inhabited class of eq. (15): the coefficients of a relation may be any such sum. -/
theorem exists_hasShiftDatum_monomialSum (hσ : 0 < σ + lam) {N : ℕ} (hN : 0 < N)
    (cc : Fin N → ℂ) (hcc : ∀ α, cc α ≠ 0) (n : Fin N → ℤ) (q p : Fin N → Polynomial ℂ)
    (hq : ∀ α, q α ≠ 0) (hp : ∀ α, p α ≠ 0) (b : Fin N → ℤ)
    (hdist : ∀ α γ : Fin N, α ≠ γ → ¬(n α = n γ
      ∧ (((q α).natDegree : ℕ) : ℝ) - (((p α).natDegree : ℕ) : ℝ)
        = (((q γ).natDegree : ℕ) : ℝ) - (((p γ).natDegree : ℕ) : ℝ)
      ∧ b α = b γ)) :
    ∃ β : Fin N, HasShiftDatum lam σ
      (fun t => ∑ α : Fin N, cc α * gammaLine (σ + lam) t ^ n α
        * ((q α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / (p α).eval ((σ : ℂ) + (t : ℂ) * Complex.I))
        * vertLog t ^ b α)
      (n β) ((((q β).natDegree : ℕ) : ℝ) - (((p β).natDegree : ℕ) : ℝ)) (b β)
      (cc β * ((q β).leadingCoeff / (p β).leadingCoeff)) :=
  hasShiftDatum_sum_of_distinct hσ hN
    (fun α t => cc α * gammaLine (σ + lam) t ^ n α
      * ((q α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / (p α).eval ((σ : ℂ) + (t : ℂ) * Complex.I))
      * vertLog t ^ b α)
    n (fun α => (((q α).natDegree : ℕ) : ℝ) - (((p α).natDegree : ℕ) : ℝ)) b
    (fun α => cc α * ((q α).leadingCoeff / (p α).leadingCoeff))
    (fun α => hasShiftDatum_monomial hσ (hcc α) (n α) (hq α) (hp α) (b α)) hdist

end

end GaloisForLFunctions.HTGeometry
