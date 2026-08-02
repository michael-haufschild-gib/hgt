import GaloisForLFunctions.HTGeometry.UniformGammaJetPolyResidue

/-!
# Padding jet ranges to a common length

A presentation's terms carry their own jet ranges: the `j`-th coefficient is a polynomial in the jets
up to order `K j`.  The residue machinery works with one range for the whole family, and padding the
exponent vectors by zeros changes nothing, since a jet raised to the power zero is one.

With the padding lemma a family of terms with different jet ranges feeds the tube residue theorem
directly.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- An exponent vector extended by zeros beyond its own range. -/
def padExp (K : ℕ) (E : Fin (K + 1) → ℕ) : ℕ → ℕ :=
  fun i => if h : i < K + 1 then E ⟨i, h⟩ else 0

@[simp] theorem padExp_zero (K : ℕ) (E : Fin (K + 1) → ℕ) : padExp K E 0 = E 0 := by
  rw [padExp, dif_pos (Nat.succ_pos K)]
  rfl

/-- **Padding a jet monomial to a longer range.** -/
theorem prod_jets_pad {K K' : ℕ} (hKK : K ≤ K') (E : Fin (K + 1) → ℕ) (z : ℂ) :
    ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E i
      = ∏ i : Fin (K' + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ padExp K E (i : ℕ) := by
  classical
  have hleft : ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E i
      = ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ padExp K E (i : ℕ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    rw [padExp, dif_pos i.isLt]
  rw [hleft]
  rw [Fin.prod_univ_eq_prod_range
    (fun i => iteratedDeriv i Complex.digamma z ^ padExp K E i) (K + 1),
    Fin.prod_univ_eq_prod_range
      (fun i => iteratedDeriv i Complex.digamma z ^ padExp K E i) (K' + 1)]
  have hsub : Finset.range (K + 1) ⊆ Finset.range (K' + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) (by omega))
  refine Finset.prod_subset hsub fun i _ hi => ?_
  have hout : ¬ i < K + 1 := by
    intro h
    exact hi (Finset.mem_range.mpr h)
  rw [padExp, dif_neg hout, pow_zero]

/-- **The residue of a presentation whose terms carry different jet ranges.**  Padding to a common
range leaves each monomial unchanged, so the tube residue theorem applies verbatim. -/
theorem exists_tubeLimit_gammaJetPoly_residue_pad {M : ℝ} (hM : 0 < M) {Ntot : ℕ} (hN : 0 < Ntot)
    (Kf : Fin Ntot → ℕ) (K d : ℕ) (hK : ∀ α, Kf α ≤ K) (u : Fin Ntot → ℕ)
    (a : Fin Ntot → Polynomial ℂ) (E : ∀ α : Fin Ntot, Fin (Kf α + 1) → ℕ)
    (hdeg : ∀ α, (a α).natDegree ≤ d) (ha : ∀ α, a α ≠ 0) :
    ∃ (p : Fin Ntot → ℕ) (c : Fin Ntot → ℂ) (β : Fin Ntot), (∀ α, c α ≠ 0) ∧
      TubeLimit M (fun σ t => (∑ α : Fin Ntot, gammaLine σ t ^ u α
          * (((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
              / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
            * ∏ i : Fin (Kf α + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α i))
        / gammaShapeZ σ (u β : ℤ) (-(p β : ℤ)) ((E β 0 : ℤ)) t)
        (∑ α ∈ Finset.univ.filter (fun α : Fin Ntot =>
            (u α : ℤ) = (u β : ℤ) ∧ (-(p α : ℤ)) = (-(p β : ℤ))
              ∧ ((E α 0 : ℤ)) = ((E β 0 : ℤ))), c α) := by
  classical
  obtain ⟨p, c, β, hc, hlim⟩ := exists_tubeLimit_gammaJetPoly_residue hM hN K d u a
    (fun α => fun i : Fin (K + 1) => padExp (Kf α) (E α) (i : ℕ)) hdeg ha
  refine ⟨p, c, β, hc, ?_⟩
  have hpad : ∀ α : Fin Ntot, padExp (Kf α) (E α) ((0 : Fin (K + 1)) : ℕ) = E α 0 := by
    intro α
    have h0 : ((0 : Fin (K + 1)) : ℕ) = 0 := rfl
    rw [h0, padExp_zero]
  simp only [hpad] at hlim
  refine hlim.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  refine congrArg (fun w => w / gammaShapeZ σ (u β : ℤ) (-(p β : ℤ)) ((E β 0 : ℤ)) t) ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [prod_jets_pad (hK α) (E α)]

end

end GaloisForLFunctions.HTGeometry
