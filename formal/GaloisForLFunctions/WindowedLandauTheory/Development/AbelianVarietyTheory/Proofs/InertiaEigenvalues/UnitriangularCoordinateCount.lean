import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter
import GaloisForLFunctions.WindowedLandauTheory.Compat.MatrixTriangular

/-! Upper unitriangular matrices with specified zero entries are parametrized by
the remaining strictly upper entries. -/

noncomputable section

open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private theorem card_upperEntries (n : ℕ) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card = n * (n - 1) / 2 := by
  have h (j : Fin n) : (Finset.univ.filter fun i : Fin n => i < j).card = (j : ℕ) := by
    rw [← Fin.card_Iio j]
    congr 1
    ext i
    simp
  calc
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card =
        ∑ j : Fin n, (Finset.univ.filter fun i : Fin n => i < j).card := by
          rw [Finset.card_filter, Fintype.sum_prod_type_right]
          simp only [Finset.card_filter]
    _ = ∑ j : Fin n, (j : ℕ) := Finset.sum_congr rfl fun j _ => h j
    _ = ∑ j ∈ Finset.range n, j := Fin.sum_univ_eq_sum_range (fun j => j) n
    _ = n * (n - 1) / 2 := Finset.sum_range_id n

/-- Each permitted upper entry gives one independent field coordinate. -/
private theorem card_unitriangular_filter (Q : Fin n × Fin n → Prop)
    (U : Finset (Gn g n)) (S : Finset (Fin n × Fin n))
    (hU : ∀ u, u ∈ U ↔ IsUniUp u.val ∧
      ∀ p : Fin n × Fin n, p.1 < p.2 → Q p → u.val p.1 p.2 = 0)
    (hS : ∀ p, p ∈ S ↔ p.1 < p.2 ∧ ¬ Q p) :
    U.card = g ^ S.card := by
  classical
  let M (f : S → ZMod g) : Mt g n := fun i j =>
    if i = j then 1 else if h : (i, j) ∈ S then f ⟨(i, j), h⟩ else 0
  have hdiag (f : S → ZMod g) (i : Fin n) : M f i i = 1 := by simp [M]
  have hbelow (f : S → ZMod g) {i j : Fin n} (h : j < i) : M f i j = 0 := by
    have hn : (i, j) ∉ S := fun hm => (not_lt_of_gt h) ((hS _).mp hm).1
    simp [M, ne_of_gt h, hn]
  have hforbidden (f : S → ZMod g) {i j : Fin n} (h : i < j) (hq : Q (i, j)) :
      M f i j = 0 := by
    have hn : (i, j) ∉ S := fun hm => ((hS _).mp hm).2 hq
    simp [M, ne_of_lt h, hn]
  have hunit (f : S → ZMod g) : IsUnit (M f) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular]
    · simp only [hdiag, Finset.prod_const_one, isUnit_one]
    · exact fun _ _ h => hbelow f h
  let entries (u : Gn g n) (p : S) : ZMod g := u.val p.val.1 p.val.2
  let e : U ≃ (S → ZMod g) :=
    { toFun := fun u => entries u.val
      invFun := fun f => ⟨(hunit f).unit, by
        apply (hU _).mpr
        rw [IsUnit.unit_spec]
        refine ⟨?_, fun p h hq => hforbidden f h hq⟩
        intro i j
        refine ⟨hbelow f, ?_⟩
        rintro rfl
        exact hdiag f i⟩
      left_inv := by
        intro u
        apply Subtype.ext
        apply Units.ext
        rw [IsUnit.unit_spec]
        ext i j
        change M (entries u.val) i j = u.val.val i j
        obtain ⟨hu, hz⟩ := (hU u.val).mp u.property
        obtain h | rfl | h := lt_trichotomy i j
        · by_cases hq : Q (i, j)
          · exact (hforbidden (entries u.val) h hq).trans (hz (i, j) h hq).symm
          · have hm : (i, j) ∈ S := (hS _).mpr ⟨h, hq⟩
            simp [M, entries, ne_of_lt h, hm]
        · exact (hdiag (entries u.val) i).trans ((hu i i).2 rfl).symm
        · exact (hbelow (entries u.val) h).trans ((hu i j).1 h).symm
      right_inv := by
        intro f
        funext p
        change (hunit f).unit.val p.val.1 p.val.2 = f p
        rw [IsUnit.unit_spec]
        simp [M, ne_of_lt ((hS p.val).mp p.property).1, p.property] }
  rw [← Fintype.card_coe U, Fintype.card_congr e, Fintype.card_fun, ZMod.card, Fintype.card_coe]

/-- The count of upper unitriangular matrices is the field size raised to
the number of strictly upper entries. -/
theorem card_unitriangular :
    (Finset.univ.filter fun u : Gn g n => IsUniUp u.val).card = g ^ (n * (n - 1) / 2) := by
  rw [← card_upperEntries n]
  exact card_unitriangular_filter (fun _ => False) _ _ (fun _ => by simp) (fun _ => by simp)

/-- Requiring the last k entries above the diagonal in column s + k to vanish
removes k independent field coordinates. -/
theorem inv_card_unitriangular_zeroColumn (s k : ℕ) (hc : s + k < n) :
    ((Finset.univ.filter fun u : Gn g n => IsUniUp u.val ∧
      ∀ a, s ≤ a → a < s + k → entN u.val a (s + k) = 0).card : ℂ)⁻¹ =
      (g : ℂ) ^ k * ((g : ℂ) ^ (n * (n - 1) / 2))⁻¹ := by
  classical
  let Q (p : Fin n × Fin n) := s ≤ (p.1 : ℕ) ∧ (p.2 : ℕ) = s + k
  have hp (u : Gn g n) :
      (∀ a, s ≤ a → a < s + k → entN u.val a (s + k) = 0) ↔
        ∀ p : Fin n × Fin n, p.1 < p.2 → Q p → u.val p.1 p.2 = 0 := by
    constructor
    · intro h p hlt hq
      obtain ⟨hrow, hcol⟩ := hq
      have hz := h p.1 hrow (hcol ▸ Fin.lt_def.mp hlt)
      rw [← hcol] at hz
      simpa [entN] using hz
    · intro h a hs ha
      have han : a < n := ha.trans hc
      simpa [entN, han, hc] using
        h (⟨a, han⟩, ⟨s + k, hc⟩) (Fin.mk_lt_mk.mpr ha) ⟨hs, rfl⟩
  let U := Finset.univ.filter fun u : Gn g n => IsUniUp u.val ∧
    ∀ a, s ≤ a → a < s + k → entN u.val a (s + k) = 0
  let S := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ¬ Q p
  change (U.card : ℂ)⁻¹ = _
  have hcard : U.card = g ^ S.card := card_unitriangular_filter Q U S
    (fun u => by
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_congr_right fun _ => hp u)
    (fun p => by simp [S])
  let T := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2
  have hQ : (T.filter Q).card = k := by
    refine (Finset.card_bij (t := Finset.range k) (fun p _ => (p.1 : ℕ) - s) ?_ ?_ ?_).trans
      (Finset.card_range k)
    · intro p hp
      simp only [T, Q, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hp
      rw [Finset.mem_range]
      omega
    · intro p hp q hq h
      simp only [T, Q, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hp hq
      apply Prod.ext <;> apply Fin.ext <;> omega
    · intro b hb
      rw [Finset.mem_range] at hb
      refine ⟨(⟨s + b, by omega⟩, ⟨s + k, hc⟩), ?_, by simp⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · exact Fin.mk_lt_mk.mpr (Nat.add_lt_add_left hb s)
      · exact ⟨Nat.le_add_right s b, rfl⟩
  have hfree : T.filter (fun p => ¬ Q p) =
      Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ ¬ Q p) := by
    ext p
    simp [T]
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) Q
  rw [hQ, hfree, card_upperEntries] at hsplit
  change k + S.card = n * (n - 1) / 2 at hsplit
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  calc
    _ = ((g ^ S.card : ℕ) : ℂ)⁻¹ := congrArg (fun a : ℕ => (a : ℂ)⁻¹) hcard
    _ = _ := by
      rw [Nat.cast_pow, ← hsplit, pow_add, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero k hg), one_mul]

end GlobalTheory.GLq
