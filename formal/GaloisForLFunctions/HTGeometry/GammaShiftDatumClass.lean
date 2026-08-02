import GaloisForLFunctions.HTGeometry.GammaShiftDatumSum

/-!
# Sums with repeated signatures

Equation (15) is written in normal form: monomials with equal exponents are collected first.  So the
signatures of the collected terms need not be pairwise distinct — what matters is that the residues
of the dominant signature class do not cancel.

That is the exact hypothesis this file uses: the sum of a finite family with data has the dominant
datum, with residue the sum of the residues over the dominant class, whenever that sum is nonzero.
The pairwise-distinct case is the special case of a singleton class.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {σ lam : ℝ}

/-- **The datum of a sum, collected by signature class.**  Members outside the dominant class are
negligible; the dominant class contributes the sum of its residues. -/
theorem hasShiftDatum_sum_class (hσ : 0 < σ + lam) {N : ℕ} (F : Fin N → ℝ → ℂ) (d : Fin N → ℤ)
    (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hdat : ∀ α, HasShiftDatum lam σ (F α) (d α) (ω α) (b α) (c α)) (β : Fin N)
    (hdom : ∀ α : Fin N, (d α = d β ∧ ω α = ω β ∧ b α = b β)
      ∨ ShiftShapeDominates (d β) (ω β) (b β) (d α) (ω α) (b α))
    (hclass : (∑ α ∈ Finset.univ.filter
      (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α) ≠ 0) :
    HasShiftDatum lam σ (fun t => ∑ α : Fin N, F α t) (d β) (ω β) (b β)
      (∑ α ∈ Finset.univ.filter
        (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α) := by
  classical
  refine ⟨hclass, ?_⟩
  have hterm : ∀ α : Fin N, Tendsto
      (fun t : ℝ => F α t / gammaShiftShape lam σ (d β) (ω β) (b β) t) atTop
      (nhds (if (d α = d β ∧ ω α = ω β ∧ b α = b β) then c α else 0)) := by
    intro α
    by_cases htie : d α = d β ∧ ω α = ω β ∧ b α = b β
    · rw [if_pos htie]
      obtain ⟨h1, h2, h3⟩ := htie
      refine (hdat α).2.congr fun t => ?_
      rw [h1, h2, h3]
    · rw [if_neg htie]
      have hsub : ShiftShapeDominates (d β) (ω β) (b β) (d α) (ω α) (b α) :=
        (hdom α).resolve_left htie
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
  have hval : (∑ α : Fin N, (if (d α = d β ∧ ω α = ω β ∧ b α = b β) then c α else 0))
      = ∑ α ∈ Finset.univ.filter
        (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α := by
    rw [Finset.sum_filter]
  rw [hval] at hsum
  refine hsum.congr fun t => ?_
  rw [Finset.sum_div]

/-- **A sum with a nonvanishing dominant class has a datum.**  The dominant signature is chosen by
the order of eq. (16); the only hypothesis is that its residues do not cancel. -/
theorem exists_hasShiftDatum_sum_class (hσ : 0 < σ + lam) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hdat : ∀ α, HasShiftDatum lam σ (F α) (d α) (ω α) (b α) (c α))
    (hclass : ∀ β : Fin N, (∀ α : Fin N, (d α = d β ∧ ω α = ω β ∧ b α = b β)
        ∨ ShiftShapeDominates (d β) (ω β) (b β) (d α) (ω α) (b α)) →
      (∑ α ∈ Finset.univ.filter
        (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α) ≠ 0) :
    ∃ β : Fin N, HasShiftDatum lam σ (fun t => ∑ α : Fin N, F α t) (d β) (ω β) (b β)
      (∑ α ∈ Finset.univ.filter
        (fun α : Fin N => d α = d β ∧ ω α = ω β ∧ b α = b β), c α) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shiftShape_index hN d ω b
  exact ⟨β, hasShiftDatum_sum_class hσ F d ω b c hdat β hβ (hclass β hβ)⟩

end

end GaloisForLFunctions.HTGeometry
