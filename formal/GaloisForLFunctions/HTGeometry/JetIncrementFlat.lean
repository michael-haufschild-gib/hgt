import GaloisForLFunctions.HTGeometry.GermNegligible

/-!
# The residue statement in flattened form

The Hölder eliminator indexes its variables by `Fin M`, while the increments of the shifted digamma
jets are indexed by translate and jet order.  Pushing a charge vector on `Fin M` forward along an
injection into `Fin r × ℕ` turns it into a charge matrix, so the family residue statement applies
verbatim.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {r : ℕ}

/-- **Equation (8) with the variables flattened.**  No nonzero charge vector on an injectively
indexed set of jets is a rational shift coboundary. -/
theorem ratShift_sub_familyIncrement_flat (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ))
    {M : ℕ} (idx : Fin M → Fin r × ℕ) (hinj : Function.Injective idx)
    {w : RatFunc ℂ} {delta : Fin M → ℂ}
    (h : ratShift w - w = ∑ k : Fin M, algebraMap ℂ (RatFunc ℂ) (delta k)
      * familyIncrement lam (idx k).1 (idx k).2) :
    ∀ k, delta k = 0 := by
  classical
  set N : ℕ := Finset.univ.sup (fun k : Fin M => (idx k).2) with hN
  have hlt : ∀ k : Fin M, (idx k).2 < N + 1 := by
    intro k
    have : (idx k).2 ≤ N := Finset.le_sup (f := fun k : Fin M => (idx k).2) (Finset.mem_univ k)
    omega
  set idxFin : Fin M → Fin r × Fin (N + 1) := fun k => ((idx k).1, ⟨(idx k).2, hlt k⟩) with hidxFin
  have hidxFinInj : Function.Injective idxFin := by
    intro a b hab
    refine hinj ?_
    have h1 : (idx a).1 = (idx b).1 :=
      congrArg (fun p : Fin r × Fin (N + 1) => p.1) hab
    have h2 : (idx a).2 = (idx b).2 :=
      congrArg (fun p : Fin r × Fin (N + 1) => (p.2 : ℕ)) hab
    exact Prod.ext h1 h2
  set D : Fin r → Fin (N + 1) → ℂ :=
    fun i j => if hk : ∃ k : Fin M, idxFin k = (i, j) then delta hk.choose else 0 with hD
  have hDval : ∀ k : Fin M, D (idxFin k).1 (idxFin k).2 = delta k := by
    intro k
    have hk : ∃ k' : Fin M, idxFin k' = ((idxFin k).1, (idxFin k).2) := ⟨k, rfl⟩
    rw [hD]
    simp only [dif_pos hk]
    have hchoice : idxFin hk.choose = ((idxFin k).1, (idxFin k).2) := hk.choose_spec
    have : hk.choose = k := hidxFinInj (by rw [hchoice])
    rw [this]
  have hDzero : ∀ p : Fin r × Fin (N + 1), p ∉ Finset.univ.image idxFin → D p.1 p.2 = 0 := by
    intro p hp
    rw [hD]
    refine dif_neg ?_
    rintro ⟨k, hk⟩
    exact hp (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, by rw [hk]⟩)
  -- rewrite the flat sum as a matrix sum
  have hsum : ∑ i : Fin r, ∑ j : Fin (N + 1),
      algebraMap ℂ (RatFunc ℂ) (D i j) * familyIncrement lam i (j : ℕ)
      = ∑ k : Fin M, algebraMap ℂ (RatFunc ℂ) (delta k)
          * familyIncrement lam (idx k).1 (idx k).2 := by
    have hprod : ∑ i : Fin r, ∑ j : Fin (N + 1),
        algebraMap ℂ (RatFunc ℂ) (D i j) * familyIncrement lam i (j : ℕ)
        = ∑ p : Fin r × Fin (N + 1),
            algebraMap ℂ (RatFunc ℂ) (D p.1 p.2) * familyIncrement lam p.1 ((p.2 : ℕ)) :=
      (Fintype.sum_prod_type' _).symm
    rw [hprod]
    have hrestrict : ∑ p ∈ (Finset.univ : Finset (Fin r × Fin (N + 1))),
        algebraMap ℂ (RatFunc ℂ) (D p.1 p.2) * familyIncrement lam p.1 ((p.2 : ℕ))
        = ∑ p ∈ Finset.univ.image idxFin,
            algebraMap ℂ (RatFunc ℂ) (D p.1 p.2) * familyIncrement lam p.1 ((p.2 : ℕ)) := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_).symm
      rw [hDzero p hp, map_zero, zero_mul]
    rw [hrestrict, Finset.sum_image (fun a _ b _ hab => hidxFinInj hab)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hDval k]
  rw [← hsum] at h
  have hzero := ratShift_sub_familyIncrement_combination lam hincong h
  intro k
  rw [← hDval k]
  exact hzero (idxFin k).1 (idxFin k).2

end

end GaloisForLFunctions.HTGeometry
