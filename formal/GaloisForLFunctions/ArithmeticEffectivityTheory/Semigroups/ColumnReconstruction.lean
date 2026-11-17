import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.ResidueColumns
import Mathlib.Tactic

/-!
# Canonical reconstruction of cofinite additive spectra

Every cofinite additive submonoid containing a positive period has a unique
threshold in each residue column. The thresholds satisfy the finite Kunz
inequalities, and their sum is independent of the chosen period or tail
cutoff. This supplies the converse construction for the residue-column
criterion of Raja--Rashid, arXiv:2611.20832.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns

private theorem residue_column_nonempty (m : ℕ) (S : AddSubmonoid ℕ)
    (C : ℕ) (hC : ∀ n, C ≤ n → n ∈ S) (r : ℕ) :
    ∃ q : ℕ, q * (m + 1) + r ∈ S := by
  refine ⟨C, hC _ ?_⟩
  have he : C * (m + 1) = C * m + C := by ring
  omega

/-- Least allowed quotient in each residue column of a cofinite additive spectrum. -/
def thresholdAt (m : ℕ) (S : AddSubmonoid ℕ) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ S) (r : ℕ) : ℕ := by
  classical
  exact Nat.find (residue_column_nonempty m S C hC r)

/-- The least quotient and closure under the period determine the whole residue column. -/
theorem thresholdAt_mem_iff (m : ℕ) (S : AddSubmonoid ℕ) (hM : m + 1 ∈ S)
    (C : ℕ) (hC : ∀ n, C ≤ n → n ∈ S) (q r : ℕ) :
    q * (m + 1) + r ∈ S ↔ thresholdAt m S C hC r ≤ q := by
  classical
  constructor
  · intro hn
    exact Nat.find_min' (residue_column_nonempty m S C hC r) hn
  · intro hq
    have hfirst : thresholdAt m S C hC r * (m + 1) + r ∈ S :=
      Nat.find_spec (residue_column_nonempty m S C hC r)
    have hmultiple (t : ℕ) : t * (m + 1) ∈ S := by
      induction t with
      | zero => simpa only [Nat.zero_mul] using S.zero_mem
      | succ t ht => simpa only [Nat.succ_mul] using S.add_mem ht hM
    have hadd := S.add_mem hfirst (hmultiple (q - thresholdAt m S C hC r))
    have he : thresholdAt m S C hC r * (m + 1) + r +
        (q - thresholdAt m S C hC r) * (m + 1) = q * (m + 1) + r := by
      calc
        _ = (thresholdAt m S C hC r + (q - thresholdAt m S C hC r)) * (m + 1) + r := by ring
        _ = _ := by
          rw [show thresholdAt m S C hC r + (q - thresholdAt m S C hC r) = q by omega]
    exact he ▸ hadd

/-- Every cofinite additive spectrum containing the period has its canonical column description. -/
theorem thresholdAt_carrier (m : ℕ) (S : AddSubmonoid ℕ) (hM : m + 1 ∈ S)
    (C : ℕ) (hC : ∀ n, C ≤ n → n ∈ S) :
    (S : Set ℕ) = carrier m (thresholdAt m S C hC) := by
  ext n
  have h := thresholdAt_mem_iff m S hM C hC (n / (m + 1)) (n % (m + 1))
  have he : n / (m + 1) * (m + 1) + n % (m + 1) = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n (m + 1)
  rw [he] at h
  exact h

/-- The reconstructed thresholds automatically satisfy all finite carry inequalities. -/
theorem thresholdAt_conditions (m : ℕ) (S : AddSubmonoid ℕ) (hM : m + 1 ∈ S)
    (C : ℕ) (hC : ∀ n, C ≤ n → n ∈ S) :
    thresholdAt m S C hC 0 = 0 ∧ Kunz m (thresholdAt m S C hC) :=
  (exists_submonoid_iff m _).mp ⟨S, thresholdAt_carrier m S hM C hC⟩

/-- Cofiniteness and one positive period characterize exactly the additive column spectra. -/
theorem cofinite_submonoid_has_columns_iff (m : ℕ) (S : AddSubmonoid ℕ) :
    (∃ k : ℕ → ℕ, k 0 = 0 ∧ Kunz m k ∧ (S : Set ℕ) = carrier m k) ↔
      m + 1 ∈ S ∧ ∃ C : ℕ, ∀ n, C ≤ n → n ∈ S := by
  constructor
  · rintro ⟨k, h0, _, hS⟩
    have hm : m + 1 ∈ carrier m k := by
      have h := (mem_column m k 1 0 (Nat.succ_pos m)).mpr (by omega)
      simpa only [Nat.one_mul, Nat.add_zero] using h
    refine ⟨?_, tailBound m k, ?_⟩
    · change m + 1 ∈ (S : Set ℕ)
      rw [hS]
      exact hm
    · intro n hn
      change n ∈ (S : Set ℕ)
      rw [hS]
      exact mem_of_tailBound_le m k hn
  · rintro ⟨hM, C, hC⟩
    exact ⟨thresholdAt m S C hC, (thresholdAt_conditions m S hM C hC).1,
      (thresholdAt_conditions m S hM C hC).2, thresholdAt_carrier m S hM C hC⟩

/-- Changing the certified tail cutoff does not change any residue threshold. -/
theorem thresholdAt_cutoff_independent (m : ℕ) (S : AddSubmonoid ℕ) (hM : m + 1 ∈ S)
    (C D : ℕ) (hC : ∀ n, C ≤ n → n ∈ S) (hD : ∀ n, D ≤ n → n ∈ S)
    (r : ℕ) (hr : r < m + 1) : thresholdAt m S C hC r = thresholdAt m S D hD r := by
  apply (carrier_eq_iff m _ _).mp _ r hr
  exact (thresholdAt_carrier m S hM C hC).symm.trans (thresholdAt_carrier m S hM D hD)

/-- The column sum is intrinsic to the exponent set, independent of its residue period. -/
theorem genus_eq_of_same_carrier (m n : ℕ) (k l : ℕ → ℕ)
    (h : carrier m k = carrier n l) : genus m k = genus n l := by
  let e : {j : ℕ // j ∉ carrier m k} ≃ {j : ℕ // j ∉ carrier n l} :=
    Equiv.subtypeEquivRight fun j => by rw [h]
  simpa only [card_gaps] using Fintype.card_congr e

/-- Any two positive periods of a cofinite additive spectrum give the same total gap count. -/
theorem thresholdAt_genus_period_independent (m n : ℕ) (S : AddSubmonoid ℕ)
    (hm : m + 1 ∈ S) (hn : n + 1 ∈ S) (C D : ℕ)
    (hC : ∀ j, C ≤ j → j ∈ S) (hD : ∀ j, D ≤ j → j ∈ S) :
    genus m (thresholdAt m S C hC) = genus n (thresholdAt n S D hD) :=
  genus_eq_of_same_carrier m n _ _
    ((thresholdAt_carrier m S hm C hC).symm.trans (thresholdAt_carrier n S hn D hD))

#print axioms genus_eq_of_same_carrier
#print axioms thresholdAt_genus_period_independent

#print axioms thresholdAt_carrier
#print axioms cofinite_submonoid_has_columns_iff
#print axioms thresholdAt_cutoff_independent

end GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns
