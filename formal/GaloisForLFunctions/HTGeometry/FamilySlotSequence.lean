import GaloisForLFunctions.HTGeometry.FlatIndexFiber
import GaloisForLFunctions.HTGeometry.MagnitudeAtomGrading
import GaloisForLFunctions.HTGeometry.PolynomialPatternWeight
import GaloisForLFunctions.HTGeometry.SlotSequenceSeparation
import GaloisForLFunctions.HTGeometry.SquareFreeAtomKey

/-!
# A split at a square-free key is a slot sequence

The weight of a flattened split of a jet monomial is a product over its slots of a falling factorial
of the consumed source index against the slot's jet order, times the slot's dilation raised to that
index.  When the split realizes the key of an injective tuple `k` of parameters above the jet order,
the consumed indices are exactly `k` read in some order, so the weight is the slot-sequence
contribution

```text
slotTerm q w k = (∏_s (k_s)_{(w s).2}) · ∏_s q_{(w s).1}^{k_s} ,
```

for the slot sequence `w` obtained by listing the monomial's slots in that order.  The slot sequence
remembers the monomial: the number of slots carrying a given jet variable is that variable's
exponent.
-/

open Finset

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The slot label with its jet order read as a natural number. -/
def slotLabel {n : ℕ} (p : ι × Fin (n + 1)) : ι × ℕ := (p.1, (p.2 : ℕ))

omit [Fintype ι] [DecidableEq ι] in
theorem slotLabel_injective {n : ℕ} : Function.Injective (slotLabel (ι := ι) (n := n)) := by
  intro p p' h
  rw [slotLabel, slotLabel, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.ext h.2)

omit [DecidableEq ι] in
/-- The slot count of a monomial is determined by any key it realizes. -/
theorem slotCount_eq_of_key {n D : ℕ} (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (l : Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ) {k : Fin D → ℕ}
    (hkey : key (famOrder n m l) = key k) :
    (∑ p : ι × Fin (n + 1), m (some p)) = D := by
  have h1 := key_total_count (famOrder n m l)
  have h2 := key_total_count k
  rw [hkey, h2] at h1
  exact h1.symm

/-- **A split at a square-free key is a slot sequence.**  Its weight is the slot-sequence
contribution, and the multiplicities of the slot labels are the jet exponents of the monomial. -/
theorem exists_slotSeq_of_key {n D : ℕ} (q : ι → ℂ)
    (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (l : Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ)
    {k : Fin D → ℕ} (hkinj : Function.Injective k)
    (hkey : key (famOrder n m l) = key k) :
    ∃ w : Fin D → ι × ℕ,
      famWeight q n m l = HTGeometry.slotTerm q w k ∧
        (∀ p : ι × Fin (n + 1),
          (Finset.univ.filter (fun s => w s = slotLabel p)).card = m (some p)) := by
  classical
  have hcnt : (∑ p : ι × Fin (n + 1), m (some p)) = D := slotCount_eq_of_key m l hkey
  have hkey' : key (fun u : Fin D => famOrder n m l ((finCongr hcnt).symm u)) = key k := by
    rw [key_comp_equiv (finCongr hcnt).symm (famOrder n m l), hkey]
  obtain ⟨σ, hσ⟩ := (key_eq_iff_exists_perm hkinj).mp hkey'
  refine ⟨fun s => slotLabel (famSlot n m ((finCongr hcnt).symm (σ.symm s))), ?_, ?_⟩
  · have horder : ∀ s : Fin D,
        famOrder n m l ((finCongr hcnt).symm (σ.symm s)) = k s := by
      intro s
      have h1 := congrFun hσ (σ.symm s)
      simpa using h1
    have hreindex : famWeight q n m l
        = ∏ s : Fin D,
            (((famOrder n m l ((finCongr hcnt).symm (σ.symm s))).descFactorial
                ((famSlot n m ((finCongr hcnt).symm (σ.symm s))).2 : ℕ) : ℂ)
              * (q (famSlot n m ((finCongr hcnt).symm (σ.symm s))).1)
                  ^ (famOrder n m l ((finCongr hcnt).symm (σ.symm s)))) := by
      rw [famWeight]
      exact (Equiv.prod_comp (σ.symm.trans (finCongr hcnt).symm)
        (fun t => (((famOrder n m l t).descFactorial ((famSlot n m t).2 : ℕ) : ℂ)
          * (q (famSlot n m t).1) ^ (famOrder n m l t)))).symm
    rw [hreindex, HTGeometry.slotTerm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [horder s]
    rfl
  · intro p
    have hiff : ∀ s : Fin D,
        (slotLabel (famSlot n m ((finCongr hcnt).symm (σ.symm s))) = slotLabel p)
          ↔ (famSlot n m ((finCongr hcnt).symm (σ.symm s)) = p) :=
      fun s => ⟨fun h => slotLabel_injective h, fun h => by rw [h]⟩
    have hset : (Finset.univ.filter (fun s : Fin D =>
        slotLabel (famSlot n m ((finCongr hcnt).symm (σ.symm s))) = slotLabel p))
        = (Finset.univ.filter (fun s : Fin D =>
            famSlot n m ((finCongr hcnt).symm (σ.symm s)) = p)) :=
      Finset.filter_congr (fun s _ => hiff s)
    have hsum : (∑ s : Fin D,
          if famSlot n m ((finCongr hcnt).symm (σ.symm s)) = p then (1 : ℕ) else 0)
        = ∑ t : Fin (∑ p' : ι × Fin (n + 1), m (some p')),
            if famSlot n m t = p then (1 : ℕ) else 0 :=
      Equiv.sum_comp (σ.symm.trans (finCongr hcnt).symm)
        (fun t => if famSlot n m t = p then (1 : ℕ) else 0)
    rw [hset, Finset.card_filter, hsum, ← Finset.card_filter]
    exact card_filter_flatIndex (fun p' : ι × Fin (n + 1) => m (some p')) p

end

end GaloisForLFunctions
