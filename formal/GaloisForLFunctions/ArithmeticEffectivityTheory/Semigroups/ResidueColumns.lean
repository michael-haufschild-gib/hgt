import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.WeightedResidueGaps
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Residue columns and the finite Kunz criterion

A column threshold records the first allowed quotient in each residue class.
Addition is closed exactly when the thresholds satisfy the carry inequalities
of Raja--Rashid, arXiv:2611.20832, Theorem 4.9. This formulation allows any
positive period, without requiring it to be the least positive element.
-/

open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns

/-- Allowed exponents in eventually full residue columns modulo `m + 1`. -/
def carrier (m : ℕ) (k : ℕ → ℕ) : Set ℕ :=
  {n | k (n % (m + 1)) ≤ n / (m + 1)}

/-- The least allowed exponent in one residue column. -/
def first (m : ℕ) (k : ℕ → ℕ) (r : ℕ) : ℕ := k r * (m + 1) + r

theorem mem_column (m : ℕ) (k : ℕ → ℕ) (q r : ℕ) (hr : r < m + 1) :
    q * (m + 1) + r ∈ carrier m k ↔ k r ≤ q := by
  simp only [carrier, Set.mem_setOf_eq, Nat.add_mod, Nat.mul_mod_left,
    Nat.zero_add, Nat.mod_eq_of_lt hr]
  rw [Nat.mul_comm q (m + 1), Nat.mul_add_div (Nat.succ_pos m),
    Nat.div_eq_of_lt hr, Nat.add_zero]

theorem first_mem (m : ℕ) (k : ℕ → ℕ) (r : ℕ) (hr : r < m + 1) :
    first m k r ∈ carrier m k := (mem_column m k (k r) r hr).mpr le_rfl

/-- Membership is comparison with the least element in the same residue column. -/
theorem mem_iff_first_le (m : ℕ) (k : ℕ → ℕ) (n : ℕ) :
    n ∈ carrier m k ↔ first m k (n % (m + 1)) ≤ n := by
  change k (n % (m + 1)) ≤ n / (m + 1) ↔
    k (n % (m + 1)) * (m + 1) + n % (m + 1) ≤ n
  have hn := Nat.div_add_mod n (m + 1)
  rw [Nat.mul_comm (m + 1) (n / (m + 1))] at hn
  constructor
  · intro h
    have hm := Nat.mul_le_mul_right (m + 1) h
    omega
  · intro h
    by_contra hlt
    have hm := Nat.mul_lt_mul_of_pos_right (k := m + 1)
      (Nat.lt_of_not_ge hlt) (Nat.succ_pos m)
    omega

/-- These finitely many inequalities include the carry from adding two residues. -/
def Kunz (m : ℕ) (k : ℕ → ℕ) : Prop :=
  ∀ i < m + 1, ∀ j < m + 1,
    k ((i + j) % (m + 1)) ≤ k i + k j + (i + j) / (m + 1)

/-- Additive closure of infinitely many exponents has an exact finite criterion. -/
theorem add_closed_iff (m : ℕ) (k : ℕ → ℕ) :
    (∀ a ∈ carrier m k, ∀ b ∈ carrier m k, a + b ∈ carrier m k) ↔ Kunz m k := by
  constructor
  · intro h i hi j hj
    have hsum := h (first m k i) (first_mem m k i hi)
      (first m k j) (first_mem m k j hj)
    change k ((first m k i + first m k j) % (m + 1)) ≤
      (first m k i + first m k j) / (m + 1) at hsum
    have he : first m k i + first m k j = (k i + k j) * (m + 1) + (i + j) := by
      simp only [first, Nat.add_mul]
      omega
    simp only [he, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod] at hsum
    rw [Nat.mul_comm (k i + k j) (m + 1), Nat.mul_add_div (Nat.succ_pos m)] at hsum
    simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hsum
  · intro h a ha b hb
    have hk := h (a % (m + 1)) (Nat.mod_lt _ (Nat.succ_pos _))
      (b % (m + 1)) (Nat.mod_lt _ (Nat.succ_pos _))
    change k (a % (m + 1)) ≤ a / (m + 1) at ha
    change k (b % (m + 1)) ≤ b / (m + 1) at hb
    change k ((a + b) % (m + 1)) ≤ (a + b) / (m + 1)
    simp only [Nat.add_div (c := m + 1) (Nat.succ_pos m),
      Nat.div_eq_of_lt (Nat.mod_lt a (Nat.succ_pos m)),
      Nat.div_eq_of_lt (Nat.mod_lt b (Nat.succ_pos m)),
      Nat.mod_mod, Nat.zero_add] at hk
    rw [Nat.add_mod, Nat.add_div (c := m + 1) (Nat.succ_pos m)]
    omega

/-- Zero membership is exactly the vanishing of the zeroth threshold. -/
theorem zero_mem_iff (m : ℕ) (k : ℕ → ℕ) : 0 ∈ carrier m k ↔ k 0 = 0 := by
  simp only [carrier, Set.mem_setOf_eq, Nat.zero_mod, Nat.zero_div, Nat.le_zero]

/-- The finite threshold conditions construct the additive submonoid itself. -/
def columnSubmonoid (m : ℕ) (k : ℕ → ℕ) (h0 : k 0 = 0) (hK : Kunz m k) :
    AddSubmonoid ℕ where
  carrier := carrier m k
  zero_mem' := (zero_mem_iff m k).mpr h0
  add_mem' := fun ha hb => (add_closed_iff m k).mpr hK _ ha _ hb

/-- The threshold conditions classify exactly the realizable additive spectra. -/
theorem exists_submonoid_iff (m : ℕ) (k : ℕ → ℕ) :
    (∃ S : AddSubmonoid ℕ, (S : Set ℕ) = carrier m k) ↔ k 0 = 0 ∧ Kunz m k := by
  constructor
  · rintro ⟨S, hS⟩
    have hmem (n : ℕ) : n ∈ S ↔ n ∈ carrier m k := by rw [← hS]; rfl
    refine ⟨(zero_mem_iff m k).mp ((hmem 0).mp S.zero_mem), ?_⟩
    apply (add_closed_iff m k).mp
    intro a ha b hb
    exact (hmem (a + b)).mp (S.add_mem ((hmem a).mpr ha) ((hmem b).mpr hb))
  · rintro ⟨h0, hK⟩
    exact ⟨columnSubmonoid m k h0 hK, rfl⟩

/-- Column thresholds classify their exponent sets in reverse pointwise order. -/
theorem subset_iff (m : ℕ) (k l : ℕ → ℕ) :
    carrier m k ⊆ carrier m l ↔ ∀ r < m + 1, l r ≤ k r := by
  constructor
  · intro h r hr
    exact (mem_column m l (k r) r hr).mp (h (first_mem m k r hr))
  · intro h n hn
    exact (h (n % (m + 1)) (Nat.mod_lt _ (Nat.succ_pos _))).trans hn

/-- Equality of exponent sets recovers every residue threshold. -/
theorem carrier_eq_iff (m : ℕ) (k l : ℕ → ℕ) :
    carrier m k = carrier m l ↔ ∀ r < m + 1, k r = l r := by
  rw [Set.Subset.antisymm_iff, subset_iff, subset_iff]
  constructor
  · rintro ⟨hkl, hlk⟩ r hr
    exact Nat.le_antisymm (hlk r hr) (hkl r hr)
  · intro h
    exact ⟨fun r hr => (h r hr).ge, fun r hr => (h r hr).le⟩

/-- Number of missing exponents, summed over residue columns. -/
def genus (m : ℕ) (k : ℕ → ℕ) : ℕ := ∑ r ∈ Finset.range (m + 1), k r

/-- An explicit tail beyond every gap; no additive closure is needed. -/
def tailBound (m : ℕ) (k : ℕ → ℕ) : ℕ := genus m k * (m + 1)

theorem mem_of_tailBound_le (m : ℕ) (k : ℕ → ℕ) {n : ℕ}
    (hn : tailBound m k ≤ n) : n ∈ carrier m k := by
  have hk : k (n % (m + 1)) ≤ genus m k :=
    Finset.single_le_sum (fun r _ => Nat.zero_le (k r))
      (Finset.mem_range.mpr (Nat.mod_lt n (Nat.succ_pos m)))
  exact hk.trans ((Nat.le_div_iff_mul_le (Nat.succ_pos m)).mpr hn)

/-- The column description is the existing complete-residue progression description. -/
theorem mem_iff_progression (m : ℕ) (k : ℕ → ℕ) (n : ℕ) :
    n ∈ carrier m k ↔ ∃ i : Fin (m + 1), ∃ q : ℕ,
      (m + 1) * q + first m k i.val = n := by
  constructor
  · intro hn
    refine ⟨⟨n % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩,
      n / (m + 1) - k (n % (m + 1)), ?_⟩
    change (m + 1) * (n / (m + 1) - k (n % (m + 1))) +
      (k (n % (m + 1)) * (m + 1) + n % (m + 1)) = n
    rw [Nat.mul_comm (k (n % (m + 1))) (m + 1),
      ← Nat.add_assoc, ← Nat.mul_add, Nat.sub_add_cancel hn]
    exact Nat.div_add_mod _ _
  · rintro ⟨i, q, rfl⟩
    have he : (m + 1) * q + first m k i.val =
        (q + k i.val) * (m + 1) + i.val := by
      simp only [first, Nat.add_mul, Nat.mul_comm (m + 1) q, Nat.add_assoc]
    rw [he, mem_column m k _ _ i.isLt]
    exact Nat.le_add_left _ _

private theorem first_residue (m : ℕ) (k : ℕ → ℕ) (i : Fin (m + 1)) :
    first m k i.val % (m + 1) = i.val := by
  simp only [first, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt i.isLt]

private theorem first_quotient (m : ℕ) (k : ℕ → ℕ) (i : Fin (m + 1)) :
    first m k i.val / (m + 1) = k i.val := by
  rw [first, Nat.mul_comm (k i.val) (m + 1), Nat.mul_add_div (Nat.succ_pos m),
    Nat.div_eq_of_lt i.isLt, Nat.add_zero]

/-- Gap coordinates specialize the existing complete-residue weight equivalence. -/
noncomputable def gapEquiv (m : ℕ) (k : ℕ → ℕ) :
    {n : ℕ // n ∉ carrier m k} ≃ Σ r : Fin (m + 1), Fin (k r.val) :=
  (Equiv.subtypeEquivRight fun n => not_congr (mem_iff_progression m k n)).trans
    ((ArithmeticHarmonicAnalysis.weightedResidueGapEquiv (Nat.succ_pos m)
      (fun i : Fin (m + 1) => first m k i.val)
      (fun i j h => Fin.ext (by simpa only [first_residue] using h))).symm.trans
        (Equiv.sigmaCongrRight fun i => finCongr (first_quotient m k i)))

noncomputable instance gapsFintype (m : ℕ) (k : ℕ → ℕ) :
    Fintype {n : ℕ // n ∉ carrier m k} :=
  Fintype.ofEquiv (Σ r : Fin (m + 1), Fin (k r.val)) (gapEquiv m k).symm

/-- The column sum is the exact genus, rather than only an upper bound. -/
theorem card_gaps (m : ℕ) (k : ℕ → ℕ) :
    Fintype.card {n : ℕ // n ∉ carrier m k} = genus m k := by
  rw [Fintype.card_congr (gapEquiv m k), Fintype.card_sigma]
  simp only [Fintype.card_fin, genus, Fin.sum_univ_eq_sum_range]

#print axioms add_closed_iff
#print axioms exists_submonoid_iff
#print axioms carrier_eq_iff
#print axioms mem_of_tailBound_le
#print axioms card_gaps

end GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns
