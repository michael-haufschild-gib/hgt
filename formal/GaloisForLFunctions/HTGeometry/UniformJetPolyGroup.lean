import GaloisForLFunctions.HTGeometry.UniformGammaPresentationDrop

/-!
# A `ψ`-degree group of a jet polynomial

Monomials sharing a `ψ`-degree can cancel against each other at leading order, so their residues must
not be taken one at a time: the sum has to go through the non-flatness dichotomy as a whole.  That is
exactly what the hypothesis-free datum does — it takes a jet polynomial in the *positive* jets and
returns a datum with a nonzero residue, whatever cancellation happens inside.

Factoring the shared `ψ`-power out of the group turns the group into such a polynomial, and its
exponent vectors stay distinct because the `ψ`-slot is common to all of them.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The datum of a `ψ`-degree group, uniformly on a tube.**  No cancellation hypothesis: the group
is handled as a whole by the dichotomy, so the residue is nonzero even if the leading terms of its
monomials cancel. -/
theorem exists_tubeLimit_jetPolyGroup_datum {M : ℝ} (hM : 0 < M) (K d Mm : ℕ) (e : ℕ)
    (a : Fin Mm → Polynomial ℂ) (E : Fin Mm → Fin (K + 1) → ℕ)
    (hdeg : ∀ α, (a α).natDegree ≤ d) (hEinj : Function.Injective E)
    (he : ∀ α, E α 0 = e) {β₀ : Fin Mm} (hβ₀ : a β₀ ≠ 0) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ TubeLimit M (fun σ t =>
      (∑ α : Fin Mm, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α i)
      / gammaShapeZ σ 0 (-(p : ℤ)) (e : ℤ) t) c := by
  classical
  -- the positive-order exponent vectors, still distinct
  set e' : Fin Mm → Fin K → ℕ := fun α i => E α i.succ with he'
  have hinj' : Function.Injective e' := by
    intro α γ hαγ
    refine hEinj ?_
    funext i
    refine Fin.cases ?_ ?_ i
    · rw [he α, he γ]
    · intro k
      have := congrFun hαγ k
      simpa [he'] using this
  have hne : jetPolyMvCoeff K Mm d a e' ≠ 0 := jetPolyMvCoeff_ne_zero a e' hinj' hβ₀
  obtain ⟨p, c, hc, hlim⟩ :=
    exists_uniform_jetPolyCoeff_datum_of_ne_zero hM K Mm 0 d e' a hdeg
      (fun α => Nat.zero_le _) hne
  refine ⟨p, c, hc, ?_⟩
  have hterm := tubeLimit_gammaJet_term hM hlim 0 e
  refine hterm.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  have hsplit : ∀ α : Fin Mm,
      ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α i
      = Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e
        * (((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin K, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e' α i) := by
    intro α
    rw [prod_jets_split K (E α), he α]
    ring
  rw [Finset.sum_congr rfl fun α _ => hsplit α, ← Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.cast_zero]

end

end GaloisForLFunctions.HTGeometry
