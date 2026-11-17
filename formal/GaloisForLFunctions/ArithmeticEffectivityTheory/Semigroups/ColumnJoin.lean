import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.ColumnReconstruction
import Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Additive fusion of cofinite residue spectra

The joined threshold in each residue column is the attained minimum of
pairwise thresholds plus their carry. Intersection takes the pointwise
maximum; union takes the minimum, with additive closure governed by the
same finite Kunz criterion.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns

/-- The join of two additive spectra has a canonical threshold in each residue column. -/
def joinThreshold (m : ℕ) (S T : AddSubmonoid ℕ) (C : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ S) : ℕ → ℕ :=
  thresholdAt m (S ⊔ T) C (fun n hn => AddSubmonoid.mem_sup_left (hC n hn))

/-- Every pair of column minima gives an upper bound for the joined threshold, including its carry. -/
theorem joinThreshold_le_pair (m : ℕ) (S T : AddSubmonoid ℕ)
    (hS : m + 1 ∈ S) (hT : m + 1 ∈ T) (C D : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ S) (hD : ∀ n, D ≤ n → n ∈ T)
    (i j : ℕ) :
    joinThreshold m S T C hC ((i + j) % (m + 1)) ≤
      thresholdAt m S C hC i + thresholdAt m T D hD j + (i + j) / (m + 1) := by
  have hi := (thresholdAt_mem_iff m S hS C hC (thresholdAt m S C hC i) i).mpr le_rfl
  have hj := (thresholdAt_mem_iff m T hT D hD (thresholdAt m T D hD j) j).mpr le_rfl
  have hij := (S ⊔ T).add_mem (AddSubmonoid.mem_sup_left hi) (AddSubmonoid.mem_sup_right hj)
  have he : (thresholdAt m S C hC i * (m + 1) + i) +
      (thresholdAt m T D hD j * (m + 1) + j) =
      (thresholdAt m S C hC i + thresholdAt m T D hD j + (i + j) / (m + 1)) *
        (m + 1) + (i + j) % (m + 1) := by
    have hdiv := Nat.div_add_mod (i + j) (m + 1)
    rw [Nat.mul_comm (m + 1)] at hdiv
    calc
      _ = (thresholdAt m S C hC i + thresholdAt m T D hD j) * (m + 1) +
          ((i + j) / (m + 1) * (m + 1) + (i + j) % (m + 1)) := by rw [hdiv]; ring
      _ = _ := by ring
  rw [he] at hij
  exact (thresholdAt_mem_iff m (S ⊔ T) (AddSubmonoid.mem_sup_left hS) C
    (fun n hn => AddSubmonoid.mem_sup_left (hC n hn)) _ _).mp hij

/-- Each joined column threshold is attained by a pair of original residue minima. -/
theorem joinThreshold_attained (m : ℕ) (S T : AddSubmonoid ℕ)
    (hS : m + 1 ∈ S) (hT : m + 1 ∈ T) (C D : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ S) (hD : ∀ n, D ≤ n → n ∈ T)
    (r : ℕ) (hr : r < m + 1) :
    ∃ i < m + 1, ∃ j < m + 1, (i + j) % (m + 1) = r ∧
      joinThreshold m S T C hC r =
        thresholdAt m S C hC i + thresholdAt m T D hD j + (i + j) / (m + 1) := by
  have hfirst : joinThreshold m S T C hC r * (m + 1) + r ∈ S ⊔ T :=
    (thresholdAt_mem_iff m (S ⊔ T) (AddSubmonoid.mem_sup_left hS) C
      (fun n hn => AddSubmonoid.mem_sup_left (hC n hn)) _ _).mpr le_rfl
  obtain ⟨a, ha, b, hb, hab⟩ := AddSubmonoid.mem_sup.mp hfirst
  let i := a % (m + 1)
  let j := b % (m + 1)
  have hi : i < m + 1 := Nat.mod_lt a (Nat.succ_pos m)
  have hj : j < m + 1 := Nat.mod_lt b (Nat.succ_pos m)
  have hres : (i + j) % (m + 1) = r := by
    dsimp only [i, j]
    rw [← Nat.add_mod, hab, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_eq_of_lt hr]
    exact Nat.mod_eq_of_lt hr
  have hquot : a / (m + 1) + b / (m + 1) + (i + j) / (m + 1) =
      joinThreshold m S T C hC r := by
    have haeq : a / (m + 1) * (m + 1) + i = a := by
      dsimp only [i]
      exact Nat.div_add_mod' a (m + 1)
    have hbeq : b / (m + 1) * (m + 1) + j = b := by
      dsimp only [j]
      exact Nat.div_add_mod' b (m + 1)
    have hijeq : (i + j) / (m + 1) * (m + 1) + r = i + j := by
      rw [← hres]
      exact Nat.div_add_mod' (i + j) (m + 1)
    have he : (a / (m + 1) + b / (m + 1) + (i + j) / (m + 1)) * (m + 1) + r =
        joinThreshold m S T C hC r * (m + 1) + r := by
      nlinarith only [haeq, hbeq, hijeq, hab]
    have hc := Nat.add_right_cancel he
    exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) hc
  have ha' : thresholdAt m S C hC i ≤ a / (m + 1) := by
    apply (thresholdAt_mem_iff m S hS C hC _ i).mp
    have h := Nat.div_add_mod a (m + 1)
    rw [Nat.mul_comm (m + 1)] at h
    dsimp only [i]
    simpa only [h] using ha
  have hb' : thresholdAt m T D hD j ≤ b / (m + 1) := by
    apply (thresholdAt_mem_iff m T hT D hD _ j).mp
    have h := Nat.div_add_mod b (m + 1)
    rw [Nat.mul_comm (m + 1)] at h
    dsimp only [j]
    simpa only [h] using hb
  have hmin := joinThreshold_le_pair m S T hS hT C D hC hD i j
  rw [hres] at hmin
  exact ⟨i, hi, j, hj, hres, Nat.le_antisymm hmin (by omega)⟩

/-- Intersection of column spectra takes the larger threshold in each column. -/
theorem carrier_max (m : ℕ) (k l : ℕ → ℕ) :
    carrier m (fun r => max (k r) (l r)) = carrier m k ∩ carrier m l := by
  ext n
  change max (k (n % (m + 1))) (l (n % (m + 1))) ≤ n / (m + 1) ↔ _
  exact max_le_iff

/-- Union of column spectra takes the smaller threshold in each column. -/
theorem carrier_min (m : ℕ) (k l : ℕ → ℕ) :
    carrier m (fun r => min (k r) (l r)) = carrier m k ∪ carrier m l := by
  ext n
  change min (k (n % (m + 1))) (l (n % (m + 1))) ≤ n / (m + 1) ↔ _
  exact min_le_iff

/-- The finite carry criterion remains stable under intersections. -/
theorem kunz_max (m : ℕ) (k l : ℕ → ℕ) (hk : Kunz m k) (hl : Kunz m l) :
    Kunz m (fun r => max (k r) (l r)) := by
  apply (add_closed_iff m _).mp
  intro a ha b hb
  rw [carrier_max] at ha hb ⊢
  exact ⟨(add_closed_iff m k).mpr hk a ha.1 b hb.1,
    (add_closed_iff m l).mpr hl a ha.2 b hb.2⟩

#print axioms joinThreshold_attained
#print axioms kunz_max
end GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns
