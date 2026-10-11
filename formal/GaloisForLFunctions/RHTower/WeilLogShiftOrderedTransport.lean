import GaloisForLFunctions.RHTower.WeilLogShiftCutTransport
import GaloisForLFunctions.RHTower.WeilLogShiftAdjacentUniqueness

/-! The same canonical coupling minimizes every increasing reembedding, uniquely for strict order. -/

open scoped BigOperators NNReal

namespace RHTower

theorem finiteWeilCoupling_index_cost_eq_cuts {n : ℕ} {P Q : Fin (n + 1) → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) :
    finiteWeilCouplingCost gamma finiteWeilIndexCost =
      ∑ i : Fin n, finiteWeilCouplingCost gamma (finiteWeilCutCost i) := by
  have hm : Monotone (fun u : Fin (n + 1) => ((u : ℕ) : ℝ)) := by
    intro u v huv
    have hv : (u : ℕ) ≤ (v : ℕ) := huv
    change ((u : ℕ) : ℝ) ≤ ((v : ℕ) : ℝ)
    exact_mod_cast hv
  change finiteWeilCouplingCost gamma (fun u v => |((u : ℕ) : ℝ) - ((v : ℕ) : ℝ)|) = _
  rw [finiteWeilCoupling_ordered_cost_eq gamma _ hm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem finiteWeilCanonicalCoupling_ordered_cost (r k : ℕ) (x : Fin (r + 2) → ℝ)
    (hmono : Monotone x) :
    finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) (fun u v => |x u - x v|) =
      ∑ i, finiteWeilCanonicalEdgeMass r k i * (x i.succ - x i.castSucc) := by
  rw [finiteWeilCoupling_ordered_cost_eq _ x hmono]
  simp only [finiteWeilCanonicalCoupling_cut_cost, mul_comm]

theorem finiteWeilCanonicalTransport_ordered_optimal (r k : ℕ) (x : Fin (r + 2) → ℝ)
    (hmono : Monotone x)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) :
    finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) (fun u v => |x u - x v|) ≤
      finiteWeilCouplingCost gamma (fun u v => |x u - x v|) := by
  rw [finiteWeilCoupling_ordered_cost_eq _ x hmono, finiteWeilCoupling_ordered_cost_eq _ x hmono]
  apply Finset.sum_le_sum
  intro i hi
  rw [finiteWeilCanonicalCoupling_cut_cost]
  apply mul_le_mul_of_nonneg_left (finiteWeilCanonicalTransport_cut_lower_bound r k gamma i)
  exact sub_nonneg.mpr (hmono (show i.castSucc ≤ i.succ from by change i.val ≤ i.val + 1; omega))

theorem finiteWeilCanonicalTransport_ordered_minimum_iff (r k : ℕ) (x : Fin (r + 2) → ℝ)
    (hstrict : StrictMono x)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) :
    finiteWeilCouplingCost gamma (fun u v => |x u - x v|) =
      finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) (fun u v => |x u - x v|) ↔
        gamma = finiteWeilCanonicalCoupling r k := by
  constructor
  · intro hopt
    have hgap (i : Fin (r + 1)) : 0 < x i.succ - x i.castSucc :=
      sub_pos.mpr (hstrict (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))
    have hn (i : Fin (r + 1)) :
        0 ≤ finiteWeilCouplingCost gamma (finiteWeilCutCost i) - finiteWeilCanonicalEdgeMass r k i :=
      sub_nonneg.mpr (finiteWeilCanonicalTransport_cut_lower_bound r k gamma i)
    rw [finiteWeilCoupling_ordered_cost_eq _ x hstrict.monotone,
      finiteWeilCoupling_ordered_cost_eq _ x hstrict.monotone] at hopt
    simp only [finiteWeilCanonicalCoupling_cut_cost] at hopt
    have hz : (∑ i : Fin (r + 1), (x i.succ - x i.castSucc) *
        (finiteWeilCouplingCost gamma (finiteWeilCutCost i) - finiteWeilCanonicalEdgeMass r k i)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hopt, sub_self]
    have hcut (i : Fin (r + 1)) : finiteWeilCouplingCost gamma (finiteWeilCutCost i) =
        finiteWeilCanonicalEdgeMass r k i := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (le_of_lt (hgap j)) (hn j))).mp hz i (Finset.mem_univ i)
      have he := (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hgap i))
      linarith only [he]
    apply (finiteWeilCanonicalTransport_index_minimum_iff r k gamma).mp
    rw [finiteWeilCoupling_index_cost_eq_cuts]
    simp_rw [hcut]
    exact finiteWeilCanonicalEdgeMass_sum r k
  · intro he
    rw [he]

theorem finiteWeilCanonicalTransport_ordered_unique_minimizer (r k : ℕ) (x : Fin (r + 2) → ℝ)
    (hstrict : StrictMono x) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
        (finiteWeilCanonicalNegativeNNProfile r k),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
          (finiteWeilCanonicalNegativeNNProfile r k),
        finiteWeilCouplingCost gamma (fun u v => |x u - x v|) ≤
          finiteWeilCouplingCost eta (fun u v => |x u - x v|) := by
  refine ⟨finiteWeilCanonicalCoupling r k,
    finiteWeilCanonicalTransport_ordered_optimal r k x hstrict.monotone, ?_⟩
  intro gamma hg
  apply (finiteWeilCanonicalTransport_ordered_minimum_iff r k x hstrict gamma).mp
  exact le_antisymm (hg (finiteWeilCanonicalCoupling r k))
    (finiteWeilCanonicalTransport_ordered_optimal r k x hstrict.monotone gamma)

end RHTower
