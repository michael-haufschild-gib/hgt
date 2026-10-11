import GaloisForLFunctions.RHTower.WeilLogShiftMixtureIndexTransport
import GaloisForLFunctions.RHTower.WeilLogShiftOrderedTransport

/-! Exact mixture transport persists under every increasing reembedding of the nodes. -/

open scoped BigOperators NNReal

namespace RHTower

theorem finiteWeilCutCost_self {n : ℕ} (i : Fin n) (u : Fin (n + 1)) :
    finiteWeilCutCost i u u = 0 := by simp [finiteWeilCutCost]

theorem finiteWeilCutCost_symm {n : ℕ} (i : Fin n) (u v : Fin (n + 1)) :
    finiteWeilCutCost i u v = finiteWeilCutCost i v u := abs_sub_comm _ _

theorem finiteWeilMixtureCoupling_cut_cost (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) (i : Fin (r + 1)) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (finiteWeilCutCost i) =
      |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalEdgeMass r k i := by
  rw [finiteWeilMixtureCoupling_cost_eq r k a b _ (finiteWeilCutCost_self i) (finiteWeilCutCost_symm i),
    finiteWeilCanonicalCoupling_cut_cost]

theorem finiteWeilMixtureTransport_cut_lower_bound (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b)) (i : Fin (r + 1)) :
    |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalEdgeMass r k i ≤
      finiteWeilCouplingCost gamma (finiteWeilCutCost i) := by
  have hf (p q : Set.Icc (0 : ℝ) 1)
      (eta : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k p)
        (finiteWeilCanonicalMixtureNNProfile r k q)) :
      ((p : ℝ) - (q : ℝ)) * finiteWeilCanonicalEdgeMass r k i ≤
        finiteWeilCouplingCost eta (finiteWeilCutCost i) := by
    have h := finiteWeilCoupling_dual_bound eta (finiteWeilCutCost i)
      (fun u => finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i u)
      (finiteWeilCanonicalProfiles_cut_dual r i)
    rw [finiteWeilCanonicalMixtureNNProfile_pairing, finiteWeilCanonicalProfiles_cut_dual_pairing] at h
    exact h
  rcases le_total (b : ℝ) (a : ℝ) with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact hf a b gamma
  · have ht := hf b a (finiteWeilCouplingTranspose gamma)
    rw [finiteWeilCouplingCost_transpose _ _ (finiteWeilCutCost_symm i)] at ht
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith only [ht]

theorem finiteWeilMixtureCoupling_node_cost (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (x : Fin (r + 2) → ℝ) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (fun u v => |x u - x v|) =
      |(a : ℝ) - (b : ℝ)| *
        finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k) (fun u v => |x u - x v|) :=
  finiteWeilMixtureCoupling_cost_eq r k a b _ (fun u => by simp) (fun u v => abs_sub_comm _ _)

theorem finiteWeilMixtureTransport_ordered_optimal (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (x : Fin (r + 2) → ℝ) (hmono : Monotone x)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b)) :
    finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (fun u v => |x u - x v|) ≤
      finiteWeilCouplingCost gamma (fun u v => |x u - x v|) := by
  rw [finiteWeilCoupling_ordered_cost_eq _ x hmono, finiteWeilCoupling_ordered_cost_eq _ x hmono]
  apply Finset.sum_le_sum
  intro i hi
  rw [finiteWeilMixtureCoupling_cut_cost]
  apply mul_le_mul_of_nonneg_left (finiteWeilMixtureTransport_cut_lower_bound r k a b gamma i)
  exact sub_nonneg.mpr (hmono (show i.castSucc ≤ i.succ from by change i.val ≤ i.val + 1; omega))

theorem finiteWeilMixtureTransport_ordered_minimum_iff (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (x : Fin (r + 2) → ℝ) (hstrict : StrictMono x)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
      (finiteWeilCanonicalMixtureNNProfile r k b)) :
    finiteWeilCouplingCost gamma (fun u v => |x u - x v|) =
      finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b) (fun u v => |x u - x v|) ↔
        gamma = finiteWeilMixtureCoupling r k a b := by
  constructor
  · intro hopt
    have hgap (i : Fin (r + 1)) : 0 < x i.succ - x i.castSucc :=
      sub_pos.mpr (hstrict (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))
    have hn (i : Fin (r + 1)) :
        0 ≤ finiteWeilCouplingCost gamma (finiteWeilCutCost i) -
          |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalEdgeMass r k i :=
      sub_nonneg.mpr (finiteWeilMixtureTransport_cut_lower_bound r k a b gamma i)
    rw [finiteWeilCoupling_ordered_cost_eq _ x hstrict.monotone,
      finiteWeilCoupling_ordered_cost_eq _ x hstrict.monotone] at hopt
    simp only [finiteWeilMixtureCoupling_cut_cost] at hopt
    have hz : (∑ i : Fin (r + 1), (x i.succ - x i.castSucc) *
        (finiteWeilCouplingCost gamma (finiteWeilCutCost i) -
          |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalEdgeMass r k i)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hopt, sub_self]
    have hcut (i : Fin (r + 1)) : finiteWeilCouplingCost gamma (finiteWeilCutCost i) =
        |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalEdgeMass r k i := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (le_of_lt (hgap j)) (hn j))).mp hz i (Finset.mem_univ i)
      have he := (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hgap i))
      linarith only [he]
    apply (finiteWeilMixtureTransport_index_minimum_iff r k a b gamma).mp
    rw [finiteWeilCoupling_index_cost_eq_cuts]
    simp_rw [hcut]
    rw [← Finset.mul_sum, finiteWeilCanonicalEdgeMass_sum, mul_one]
  · intro he
    rw [he]

theorem finiteWeilMixtureTransport_ordered_unique_minimizer (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1)
    (x : Fin (r + 2) → ℝ) (hstrict : StrictMono x) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
        (finiteWeilCanonicalMixtureNNProfile r k b),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalMixtureNNProfile r k a)
          (finiteWeilCanonicalMixtureNNProfile r k b),
        finiteWeilCouplingCost gamma (fun u v => |x u - x v|) ≤
          finiteWeilCouplingCost eta (fun u v => |x u - x v|) := by
  refine ⟨finiteWeilMixtureCoupling r k a b,
    finiteWeilMixtureTransport_ordered_optimal r k a b x hstrict.monotone, ?_⟩
  intro gamma hg
  apply (finiteWeilMixtureTransport_ordered_minimum_iff r k a b x hstrict gamma).mp
  exact le_antisymm (hg (finiteWeilMixtureCoupling r k a b))
    (finiteWeilMixtureTransport_ordered_optimal r k a b x hstrict.monotone gamma)

end RHTower
