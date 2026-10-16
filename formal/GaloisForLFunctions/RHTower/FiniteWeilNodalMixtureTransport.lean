import GaloisForLFunctions.RHTower.FiniteWeilNodalAdjacentCoupling
import GaloisForLFunctions.RHTower.WeilLogShiftMixtureOrderedTransport

/-!
# Exact transport inside the nodal probability fiber of an arbitrary ordered node family

Let `h : Fin (r + 2) → ℝ` be strictly increasing, with nodal probability profiles `P` and `Q`
(`FiniteWeilNodalAdjacentCoupling`).  This file proves:

* `finiteWeilNodalTransport_ordered_unique_minimizer`: for every strictly increasing reembedding
  `x` of the nodes, and in particular for the node cost `|h_i - h_j|`
  (`finiteWeilNodalTransport_node_unique_minimizer`), the adjacent coupling is the unique optimal
  coupling of `P` to `Q`; its cost is `Σ m_i (x_{i+1} - x_i)`, a convex combination of the gaps;
* `finiteWeilNodalMomentFiber_iff`: the probabilities sharing the moments `p ≤ r` of `P` are
  exactly the mixtures `ν_a = a P + (1 - a) Q`, `0 ≤ a ≤ 1`;
* `finiteWeilNodalMixture_abs_distance`: `Σ |ν_a - ν_b| = 2 |a - b|`;
* `finiteWeilNodalMixtureTransport_index_unique_minimizer`: the optimal index cost between
  `ν_a` and `ν_b` is exactly `|a - b|`, attained by a unique coupling (common mass on the
  diagonal, excess along the adjacent edges);
* `finiteWeilNodalMixtureTransport_ordered_unique_minimizer`: the same coupling is the unique
  optimum for every strictly increasing node cost, at cost `|a - b|` times the endpoint cost.

The lower bounds are dual potentials: the parity potential `(-1) ^ (r + 1 - i) / 2` for the
index cost, and the cut indicators for ordered costs.
-/

open scoped BigOperators NNReal

noncomputable section
namespace RHTower

/-! ### Cuts and ordered node costs for the endpoint coupling -/

theorem finiteWeilNodalProfiles_cut_dual_pairing {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (i : Fin (r + 1)) :
    (∑ u, (finiteWeilNodalPositiveNNProfile h hh u : ℝ) *
      (finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i u)) -
      (∑ u, (finiteWeilNodalNegativeNNProfile h hh u : ℝ) *
        (finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i u)) =
        finiteWeilNodalEdgeMass h i := by
  calc
    _ = finiteWeilBinomialParity r i.castSucc *
        ((∑ u, (finiteWeilNodalPositiveNNProfile h hh u : ℝ) * finiteWeilCutIndicator i u) -
          (∑ u, (finiteWeilNodalNegativeNNProfile h hh u : ℝ) * finiteWeilCutIndicator i u)) := by
      simp only [mul_sub, Finset.mul_sum, mul_left_comm]
    _ = finiteWeilBinomialParity r i.castSucc * finiteWeilNodalPrefixDifference h i := by
      rw [finiteWeilNodalProfiles_cut_pairing h hh]
    _ = _ := by
      rw [finiteWeilNodalPrefixDifference_signed_mass h hh, ← mul_assoc, ← pow_two,
        finiteWeilBinomialParity_sq, one_mul]

theorem finiteWeilNodalCoupling_cut_cost {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (i : Fin (r + 1)) :
    finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) (finiteWeilCutCost i) =
      finiteWeilNodalEdgeMass h i := by
  rw [finiteWeilNodalCoupling_cost_eq]
  simp only [finiteWeilCanonicalEdge_cut_cost, mul_ite, mul_one, mul_zero]
  simp

theorem finiteWeilNodalTransport_cut_lower_bound {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh)) (i : Fin (r + 1)) :
    finiteWeilNodalEdgeMass h i ≤ finiteWeilCouplingCost gamma (finiteWeilCutCost i) := by
  rw [← finiteWeilNodalProfiles_cut_dual_pairing h hh i]
  exact finiteWeilCoupling_dual_bound gamma (finiteWeilCutCost i)
    (fun u => finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i u)
    (finiteWeilCanonicalProfiles_cut_dual r i)

/-- For a monotone reembedding `x` of the nodes, the adjacent coupling costs
`Σ m_i (x_{i+1} - x_i)`. -/
theorem finiteWeilNodalCoupling_ordered_cost {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (x : Fin (r + 2) → ℝ) (hx : Monotone x) :
    finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) (fun u v => |x u - x v|) =
      ∑ i : Fin (r + 1), finiteWeilNodalEdgeMass h i * (x i.succ - x i.castSucc) := by
  rw [finiteWeilCoupling_ordered_cost_eq _ x hx]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteWeilNodalCoupling_cut_cost h hh, mul_comm]

theorem finiteWeilNodalTransport_ordered_optimal {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (x : Fin (r + 2) → ℝ) (hx : Monotone x)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh)) :
    finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) (fun u v => |x u - x v|) ≤
      finiteWeilCouplingCost gamma (fun u v => |x u - x v|) := by
  rw [finiteWeilCoupling_ordered_cost_eq _ x hx, finiteWeilCoupling_ordered_cost_eq _ x hx]
  apply Finset.sum_le_sum
  intro i _
  rw [finiteWeilNodalCoupling_cut_cost h hh]
  apply mul_le_mul_of_nonneg_left (finiteWeilNodalTransport_cut_lower_bound h hh gamma i)
  exact sub_nonneg.mpr (hx (show i.castSucc ≤ i.succ from by change i.val ≤ i.val + 1; omega))

theorem finiteWeilNodalTransport_ordered_minimum_iff {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (x : Fin (r + 2) → ℝ) (hx : StrictMono x)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
      (finiteWeilNodalNegativeNNProfile h hh)) :
    finiteWeilCouplingCost gamma (fun u v => |x u - x v|) =
      finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) (fun u v => |x u - x v|) ↔
        gamma = finiteWeilNodalCoupling h hh := by
  refine ⟨fun hopt => ?_, fun he => by rw [he]⟩
  have hgap (i : Fin (r + 1)) : 0 < x i.succ - x i.castSucc :=
    sub_pos.mpr (hx (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))
  have hn (i : Fin (r + 1)) :
      0 ≤ finiteWeilCouplingCost gamma (finiteWeilCutCost i) - finiteWeilNodalEdgeMass h i :=
    sub_nonneg.mpr (finiteWeilNodalTransport_cut_lower_bound h hh gamma i)
  rw [finiteWeilCoupling_ordered_cost_eq _ x hx.monotone,
    finiteWeilCoupling_ordered_cost_eq _ x hx.monotone] at hopt
  simp only [finiteWeilNodalCoupling_cut_cost h hh] at hopt
  have hz : (∑ i : Fin (r + 1), (x i.succ - x i.castSucc) *
      (finiteWeilCouplingCost gamma (finiteWeilCutCost i) - finiteWeilNodalEdgeMass h i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hopt, sub_self]
  have hcut (i : Fin (r + 1)) :
      finiteWeilCouplingCost gamma (finiteWeilCutCost i) = finiteWeilNodalEdgeMass h i := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (le_of_lt (hgap j)) (hn j))).mp hz i (Finset.mem_univ i)
    have he := (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hgap i))
    linarith only [he]
  apply (finiteWeilNodalTransport_index_minimum_iff h hh gamma).mp
  rw [finiteWeilCoupling_index_cost_eq_cuts]
  simp_rw [hcut]
  exact finiteWeilNodalEdgeMass_sum h hh

/-- For every strictly increasing reembedding `x`, the adjacent coupling is the unique optimal
coupling of `P` to `Q` for the cost `|x_i - x_j|`. -/
theorem finiteWeilNodalTransport_ordered_unique_minimizer {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (x : Fin (r + 2) → ℝ) (hx : StrictMono x) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
        (finiteWeilNodalNegativeNNProfile h hh),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
          (finiteWeilNodalNegativeNNProfile h hh),
        finiteWeilCouplingCost gamma (fun u v => |x u - x v|) ≤
          finiteWeilCouplingCost eta (fun u v => |x u - x v|) := by
  refine ⟨finiteWeilNodalCoupling h hh,
    finiteWeilNodalTransport_ordered_optimal h hh x hx.monotone, fun gamma hg => ?_⟩
  apply (finiteWeilNodalTransport_ordered_minimum_iff h hh x hx gamma).mp
  exact le_antisymm (hg (finiteWeilNodalCoupling h hh))
    (finiteWeilNodalTransport_ordered_optimal h hh x hx.monotone gamma)

/-- The adjacent coupling is the unique optimal coupling of `P` to `Q` for the node cost
`|h_i - h_j|`. -/
theorem finiteWeilNodalTransport_node_unique_minimizer {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
        (finiteWeilNodalNegativeNNProfile h hh),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilNodalPositiveNNProfile h hh)
          (finiteWeilNodalNegativeNNProfile h hh),
        finiteWeilCouplingCost gamma (fun u v => |h u - h v|) ≤
          finiteWeilCouplingCost eta (fun u v => |h u - h v|) :=
  finiteWeilNodalTransport_ordered_unique_minimizer h hh h hh

/-- The optimal node cost is a convex combination of the node gaps, so it lies between any
lower and upper bound for the gaps. -/
theorem finiteWeilNodalCoupling_node_cost_bounds {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (lo hi : ℝ)
    (hgap : ∀ i : Fin (r + 1), lo ≤ h i.succ - h i.castSucc ∧ h i.succ - h i.castSucc ≤ hi) :
    lo ≤ finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) (fun u v => |h u - h v|) ∧
      finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) (fun u v => |h u - h v|) ≤ hi := by
  rw [finiteWeilNodalCoupling_ordered_cost h hh h hh.monotone]
  have hm := finiteWeilNodalEdgeMass_sum h hh
  have hpos (i : Fin (r + 1)) := (finiteWeilNodalEdgeMass_pos h hh i).le
  constructor
  · calc
      lo = ∑ i : Fin (r + 1), finiteWeilNodalEdgeMass h i * lo := by
        rw [← Finset.sum_mul, hm, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hgap i).1 (hpos i)
  · calc
      _ ≤ ∑ i : Fin (r + 1), finiteWeilNodalEdgeMass h i * hi :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hgap i).2 (hpos i)
      _ = hi := by rw [← Finset.sum_mul, hm, one_mul]

/-! ### The moment fiber is the segment of mixtures -/

/-- The mixture `a P + (1 - a) Q`. -/
def finiteWeilNodalMixture {r : ℕ} (h : Fin (r + 2) → ℝ) (a : ℝ) (i : Fin (r + 2)) : ℝ :=
  a * finiteWeilNodalPositiveProfile h i + (1 - a) * finiteWeilNodalNegativeProfile h i

/-- Probability vectors on the nodes sharing the moments `p ≤ r` of `P`. -/
def finiteWeilNodalMomentFiber {r : ℕ} (h : Fin (r + 2) → ℝ) (v : Fin (r + 2) → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧
    ∀ p ≤ r, (∑ i, v i * h i ^ p) = ∑ i, finiteWeilNodalPositiveProfile h i * h i ^ p

private theorem exists_pos_of_sum_eq_one {n : ℕ} (v : Fin n → ℝ) (hv : ∑ i, v i = 1) :
    ∃ i, 0 < v i := by
  by_contra hc
  have hn (i : Fin n) : v i ≤ 0 := le_of_not_gt (fun hi => hc ⟨i, hi⟩)
  have hs : ∑ i, v i ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
  linarith only [hv, hs]

theorem finiteWeilNodalMixture_nonneg_iff {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a : ℝ) : (∀ i, 0 ≤ finiteWeilNodalMixture h a i) ↔ 0 ≤ a ∧ a ≤ 1 := by
  have hs := finiteWeilNodalProfiles_spec h hh
  constructor
  · intro ha
    obtain ⟨i, hi⟩ := exists_pos_of_sum_eq_one _ hs.2.1
    obtain ⟨j, hj⟩ := exists_pos_of_sum_eq_one _ hs.2.2.1
    have hQi : finiteWeilNodalNegativeProfile h i = 0 :=
      (mul_eq_zero.mp (hs.1 i).2.2.1).resolve_left hi.ne'
    have hPj : finiteWeilNodalPositiveProfile h j = 0 :=
      (mul_eq_zero.mp (hs.1 j).2.2.1).resolve_right hj.ne'
    have hai : 0 ≤ a * finiteWeilNodalPositiveProfile h i := by
      simpa only [finiteWeilNodalMixture, hQi, mul_zero, add_zero] using ha i
    have haj : 0 ≤ (1 - a) * finiteWeilNodalNegativeProfile h j := by
      simpa only [finiteWeilNodalMixture, hPj, mul_zero, zero_add] using ha j
    refine ⟨nonneg_of_mul_nonneg_left hai hi, ?_⟩
    have := nonneg_of_mul_nonneg_left haj hj
    linarith
  · rintro ⟨ha, ha1⟩ i
    exact add_nonneg (mul_nonneg ha (hs.1 i).1) (mul_nonneg (sub_nonneg.mpr ha1) (hs.1 i).2.1)

theorem finiteWeilNodalMixture_injective {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h) :
    Function.Injective (finiteWeilNodalMixture h) := by
  have hs := finiteWeilNodalProfiles_spec h hh
  obtain ⟨i, hi⟩ := exists_pos_of_sum_eq_one _ hs.2.1
  have hQi : finiteWeilNodalNegativeProfile h i = 0 :=
    (mul_eq_zero.mp (hs.1 i).2.2.1).resolve_left hi.ne'
  intro a b hab
  have he := congrFun hab i
  simp only [finiteWeilNodalMixture, hQi, mul_zero, add_zero] at he
  exact mul_right_cancel₀ hi.ne' he

theorem finiteWeilNodalMixture_mem {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : finiteWeilNodalMomentFiber h (finiteWeilNodalMixture h a) := by
  have hs := finiteWeilNodalProfiles_spec h hh
  refine ⟨(finiteWeilNodalMixture_nonneg_iff h hh a).mpr ⟨ha, ha1⟩, ?_, fun p hp => ?_⟩
  · simp only [finiteWeilNodalMixture, Finset.sum_add_distrib, ← Finset.mul_sum, hs.2.1,
      hs.2.2.1, mul_one]
    ring
  · simp only [finiteWeilNodalMixture, add_mul, mul_assoc, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [← hs.2.2.2.2 p hp]
    ring

/-- Every vector annihilating the moments `p ≤ r` is a multiple of `P - Q`. -/
theorem finiteWeilNodalProfiles_annihilator_span {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (c : Fin (r + 2) → ℝ) (hm : ∀ p ≤ r, ∑ i, c i * h i ^ p = 0) :
    ∃ a : ℝ, ∀ i, c i =
      a * (finiteWeilNodalPositiveProfile h i - finiteWeilNodalNegativeProfile h i) := by
  let W := finiteWeilMomentWeights h
  let A := ∑ i, c i * h i ^ (r + 1)
  let t := (2 / finiteWeilAbsMass (finiteWeilNormalizedMomentDual h)) * ‖W‖⁻¹
  have hW : 0 < ‖W‖ := finiteWeilMomentWeights_norm_pos h hh.injective
  have ht : 0 < t := mul_pos (finiteWeilNodal_scale_pos h hh) (inv_pos.mpr hW)
  have hc : c = A • W := finiteWeilMomentWeights_span h hh.injective c (fun p hp => hm p (by omega))
  have hd (i : Fin (r + 2)) :
      finiteWeilNodalPositiveProfile h i - finiteWeilNodalNegativeProfile h i = t * W i := by
    unfold finiteWeilNodalPositiveProfile finiteWeilNodalNegativeProfile
    rw [finiteWeil_profile_difference]
    change (2 / finiteWeilAbsMass (finiteWeilNormalizedMomentDual h)) * (‖W‖⁻¹ * W i) = t * W i
    dsimp [t]
    ring
  refine ⟨A / t, fun i => ?_⟩
  rw [hd]
  calc
    c i = A * W i := congrFun hc i
    _ = (A / t) * (t * W i) := by rw [← mul_assoc, div_mul_cancel₀ _ ht.ne']

/-- A probability on the nodes shares the moments `p ≤ r` of `P` iff it is a mixture
`a P + (1 - a) Q` with a unique `a ∈ [0, 1]`. -/
theorem finiteWeilNodalMomentFiber_iff {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (v : Fin (r + 2) → ℝ) :
    finiteWeilNodalMomentFiber h v ↔
      ∃! a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ v = finiteWeilNodalMixture h a := by
  constructor
  · intro hv
    have hs := finiteWeilNodalProfiles_spec h hh
    have hm (p : ℕ) (hp : p ≤ r) :
        ∑ i, (v i - finiteWeilNodalNegativeProfile h i) * h i ^ p = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [hv.2.2 p hp, hs.2.2.2.2 p hp, sub_self]
    obtain ⟨a, ha⟩ := finiteWeilNodalProfiles_annihilator_span h hh
      (fun i => v i - finiteWeilNodalNegativeProfile h i) hm
    have he : v = finiteWeilNodalMixture h a := by
      funext i
      have hi := ha i
      dsimp [finiteWeilNodalMixture]
      linarith only [hi]
    have hbounds := (finiteWeilNodalMixture_nonneg_iff h hh a).mp (he ▸ hv.1)
    refine ⟨a, ⟨hbounds.1, hbounds.2, he⟩, fun b hb => ?_⟩
    exact finiteWeilNodalMixture_injective h hh (hb.2.2.symm.trans he)
  · rintro ⟨a, ha, _⟩
    rw [ha.2.2]
    exact finiteWeilNodalMixture_mem h hh a ha.1 ha.2.1

theorem finiteWeilNodalMixture_difference {r : ℕ} (h : Fin (r + 2) → ℝ) (a b : ℝ)
    (i : Fin (r + 2)) :
    finiteWeilNodalMixture h a i - finiteWeilNodalMixture h b i =
      (a - b) * (finiteWeilNodalPositiveProfile h i - finiteWeilNodalNegativeProfile h i) := by
  unfold finiteWeilNodalMixture
  ring

/-- The `ℓ¹` distance between two mixtures is `2 |a - b|`. -/
theorem finiteWeilNodalMixture_abs_distance {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a b : ℝ) :
    (∑ i, |finiteWeilNodalMixture h a i - finiteWeilNodalMixture h b i|) = 2 * |a - b| := by
  simp only [finiteWeilNodalMixture_difference, abs_mul, ← Finset.mul_sum]
  rw [(finiteWeilNodalProfiles_spec h hh).2.2.2.1, mul_comm]

/-! ### Couplings between two mixtures -/

/-- The mixture `ν_a` as a nonnegative profile, for `a ∈ [0, 1]`. -/
def finiteWeilNodalMixtureNNProfile {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a : Set.Icc (0 : ℝ) 1) (u : Fin (r + 2)) : ℝ≥0 :=
  NNReal.mk (finiteWeilNodalMixture h a u)
    ((finiteWeilNodalMixture_nonneg_iff h hh a).mpr a.property u)

theorem finiteWeilNodalMixtureNNProfile_apply {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a : Set.Icc (0 : ℝ) 1) (u : Fin (r + 2)) :
    (finiteWeilNodalMixtureNNProfile h hh a u : ℝ) = finiteWeilNodalMixture h a u := rfl

theorem finiteWeilNodalMixtureNNProfile_pairing {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a b : Set.Icc (0 : ℝ) 1) (f : Fin (r + 2) → ℝ) :
    (∑ u, (finiteWeilNodalMixtureNNProfile h hh a u : ℝ) * f u) -
      (∑ u, (finiteWeilNodalMixtureNNProfile h hh b u : ℝ) * f u) =
      ((a : ℝ) - (b : ℝ)) *
        ((∑ u, (finiteWeilNodalPositiveNNProfile h hh u : ℝ) * f u) -
          (∑ u, (finiteWeilNodalNegativeNNProfile h hh u : ℝ) * f u)) := by
  change (∑ u, finiteWeilNodalMixture h a u * f u) - (∑ u, finiteWeilNodalMixture h b u * f u) =
    ((a : ℝ) - (b : ℝ)) * ((∑ u, finiteWeilNodalPositiveProfile h u * f u) -
      (∑ u, finiteWeilNodalNegativeProfile h u * f u))
  calc
    _ = ∑ u, (finiteWeilNodalMixture h a u - finiteWeilNodalMixture h b u) * f u := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ = ∑ u, ((a : ℝ) - (b : ℝ)) *
        ((finiteWeilNodalPositiveProfile h u - finiteWeilNodalNegativeProfile h u) * f u) := by
      simp only [finiteWeilNodalMixture_difference, mul_assoc]
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [sub_mul, Finset.sum_sub_distrib]

/-- For `b ≤ a`: keep the common mass `b P + (1 - a) Q` on the diagonal and move the excess
`(a - b)` along the adjacent edges. -/
def finiteWeilNodalOrientedMixturePlan {r : ℕ} (h : Fin (r + 2) → ℝ) (a b : Set.Icc (0 : ℝ) 1)
    (u v : Fin (r + 2)) : ℝ :=
  (if u = v then (b : ℝ) * finiteWeilNodalPositiveProfile h u +
    (1 - (a : ℝ)) * finiteWeilNodalNegativeProfile h u else 0) +
      ((a : ℝ) - (b : ℝ)) * finiteWeilNodalEdgePlan h u v

theorem finiteWeilNodalOrientedMixturePlan_nonneg {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) (hba : (b : ℝ) ≤ (a : ℝ)) (u v : Fin (r + 2)) :
    0 ≤ finiteWeilNodalOrientedMixturePlan h a b u v := by
  have hs := finiteWeilNodalProfiles_spec h hh
  unfold finiteWeilNodalOrientedMixturePlan
  apply add_nonneg
  · split_ifs
    · exact add_nonneg (mul_nonneg b.property.1 (hs.1 u).1)
        (mul_nonneg (sub_nonneg.mpr a.property.2) (hs.1 u).2.1)
    · exact le_rfl
  · exact mul_nonneg (sub_nonneg.mpr hba) (finiteWeilNodalEdgePlan_nonneg h hh u v)

theorem finiteWeilNodalOrientedMixturePlan_marginals {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) (u : Fin (r + 2)) :
    (∑ v, finiteWeilNodalOrientedMixturePlan h a b u v) = finiteWeilNodalMixture h a u ∧
      (∑ v, finiteWeilNodalOrientedMixturePlan h a b v u) = finiteWeilNodalMixture h b u := by
  constructor
  · simp only [finiteWeilNodalOrientedMixturePlan, Finset.sum_add_distrib, ← Finset.mul_sum,
      (finiteWeilNodalEdgePlan_marginals h hh u).1]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, finiteWeilNodalMixture]
    ring
  · simp only [finiteWeilNodalOrientedMixturePlan, Finset.sum_add_distrib, ← Finset.mul_sum,
      (finiteWeilNodalEdgePlan_marginals h hh u).2]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, finiteWeilNodalMixture]
    ring

def finiteWeilNodalOrientedMixtureCoupling {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a b : Set.Icc (0 : ℝ) 1) (hba : (b : ℝ) ≤ (a : ℝ)) :
    HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b) where
  plan u v := NNReal.mk (finiteWeilNodalOrientedMixturePlan h a b u v)
    (finiteWeilNodalOrientedMixturePlan_nonneg h hh a b hba u v)
  row u := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, NNReal.coe_mk, finiteWeilNodalMixtureNNProfile] using
      (finiteWeilNodalOrientedMixturePlan_marginals h hh a b u).1
  col u := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, NNReal.coe_mk, finiteWeilNodalMixtureNNProfile] using
      (finiteWeilNodalOrientedMixturePlan_marginals h hh a b u).2

theorem finiteWeilNodalOrientedMixtureCoupling_cost_eq {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) (hba : (b : ℝ) ≤ (a : ℝ))
    (c : Fin (r + 2) → Fin (r + 2) → ℝ) (hc : ∀ u, c u u = 0) :
    finiteWeilCouplingCost (finiteWeilNodalOrientedMixtureCoupling h hh a b hba) c =
      ((a : ℝ) - (b : ℝ)) * finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) c := by
  have hd (u : Fin (r + 2)) :
      (∑ v, (if u = v then (b : ℝ) * finiteWeilNodalPositiveProfile h u +
          (1 - (a : ℝ)) * finiteWeilNodalNegativeProfile h u else 0) * c u v) = 0 := by
    simp [ite_mul, hc]
  change (∑ u, ∑ v, finiteWeilNodalOrientedMixturePlan h a b u v * c u v) =
    ((a : ℝ) - (b : ℝ)) * (∑ u, ∑ v, finiteWeilNodalEdgePlan h u v * c u v)
  simp only [finiteWeilNodalOrientedMixturePlan, add_mul, Finset.sum_add_distrib, hd, zero_add,
    mul_assoc, ← Finset.mul_sum]

theorem finiteWeilNodalMixtureNNProfile_index_pairing {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) :
    (∑ u, (finiteWeilNodalMixtureNNProfile h hh a u : ℝ) * (finiteWeilBinomialParity r u / 2)) -
      (∑ u, (finiteWeilNodalMixtureNNProfile h hh b u : ℝ) *
        (finiteWeilBinomialParity r u / 2)) = (a : ℝ) - (b : ℝ) := by
  rw [finiteWeilNodalMixtureNNProfile_pairing, finiteWeilNodalProfiles_index_dual_pairing h hh,
    mul_one]

theorem finiteWeilNodalOrientedMixtureCoupling_index_cost {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) (hba : (b : ℝ) ≤ (a : ℝ)) :
    finiteWeilCouplingCost (finiteWeilNodalOrientedMixtureCoupling h hh a b hba)
      finiteWeilIndexCost = (a : ℝ) - (b : ℝ) := by
  rw [finiteWeilNodalOrientedMixtureCoupling_cost_eq h hh a b hba _ finiteWeilIndexCost_self,
    finiteWeilNodalCoupling_index_cost, mul_one]

theorem finiteWeilNodalOrientedMixtureTransport_index_lower_bound {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b)) :
    (a : ℝ) - (b : ℝ) ≤ finiteWeilCouplingCost gamma finiteWeilIndexCost := by
  rw [← finiteWeilNodalMixtureNNProfile_index_pairing h hh a b]
  exact finiteWeilCoupling_dual_bound gamma finiteWeilIndexCost
    (fun u => finiteWeilBinomialParity r u / 2) (finiteWeilBinomialParity_index_dual r)

theorem finiteWeilNodalOrientedMixtureTransport_index_banded {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b))
    (hopt : finiteWeilCouplingCost gamma finiteWeilIndexCost = (a : ℝ) - (b : ℝ))
    (u v : Fin (r + 2)) (hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ)) :
    gamma.plan u v = 0 := by
  apply finiteWeilCoupling_zero_of_strict_dual gamma finiteWeilIndexCost
    (fun j => finiteWeilBinomialParity r j / 2) (finiteWeilBinomialParity_index_dual r)
  · rw [finiteWeilNodalMixtureNNProfile_index_pairing h hh]
    exact hopt
  · exact finiteWeilBinomialParity_index_dual_strict r u v hfar

theorem finiteWeilNodalOrientedMixtureTransport_reverse_edge_zero {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b))
    (hopt : finiteWeilCouplingCost gamma finiteWeilIndexCost = (a : ℝ) - (b : ℝ))
    (i : Fin (r + 1)) :
    gamma.plan (finiteWeilCanonicalEdgeTarget r i) (finiteWeilCanonicalEdgeSource r i) = 0 := by
  apply finiteWeilCoupling_zero_of_strict_dual gamma finiteWeilIndexCost
    (fun j => finiteWeilBinomialParity r j / 2) (finiteWeilBinomialParity_index_dual r)
  · rw [finiteWeilNodalMixtureNNProfile_index_pairing h hh]
    exact hopt
  · rw [finiteWeilIndexCost_symm, finiteWeilCanonicalEdge_index_cost,
      finiteWeilCanonicalEdgeTarget_parity, finiteWeilCanonicalEdgeSource_parity]
    norm_num

theorem finiteWeilNodalMixtureCoupling_cut_flux {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b))
    (hband : ∀ u v : Fin (r + 2), (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) →
      gamma.plan u v = 0)
    (i : Fin (r + 1)) :
    (gamma.plan i.castSucc i.succ : ℝ) - (gamma.plan i.succ i.castSucc : ℝ) =
      ((a : ℝ) - (b : ℝ)) * finiteWeilNodalPrefixDifference h i := by
  have hp := finiteWeilCoupling_pairing gamma (finiteWeilCutIndicator i)
  rw [finiteWeilNodalMixtureNNProfile_pairing, finiteWeilNodalProfiles_cut_pairing h hh] at hp
  unfold finiteWeilCouplingCost at hp
  rw [finiteWeil_banded_cut_pairing (fun u v => (gamma.plan u v : ℝ))
    (fun u v huv => by rw [hband u v huv]; rfl)] at hp
  exact hp.symm

theorem finiteWeilNodalOrientedMixtureTransport_edge_mass {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b))
    (hopt : finiteWeilCouplingCost gamma finiteWeilIndexCost = (a : ℝ) - (b : ℝ))
    (i : Fin (r + 1)) :
    (gamma.plan (finiteWeilCanonicalEdgeSource r i) (finiteWeilCanonicalEdgeTarget r i) : ℝ) =
      ((a : ℝ) - (b : ℝ)) * finiteWeilNodalEdgeMass h i := by
  have hp := finiteWeilNodalMixtureCoupling_cut_flux h hh a b gamma
    (finiteWeilNodalOrientedMixtureTransport_index_banded h hh a b gamma hopt) i
  have hz := finiteWeilNodalOrientedMixtureTransport_reverse_edge_zero h hh a b gamma hopt i
  rcases finiteWeilBinomialParity_eq_one_or_neg_one r i.castSucc with hs | hs
  · simp only [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, hs,
      ↓reduceIte] at hz ⊢
    have hz' : (gamma.plan i.succ i.castSucc : ℝ) = 0 := congrArg NNReal.toReal hz
    rw [hz', sub_zero, finiteWeilNodalPrefixDifference_signed_mass h hh, hs, one_mul] at hp
    exact hp
  · norm_num [finiteWeilCanonicalEdgeSource, finiteWeilCanonicalEdgeTarget, hs] at hz ⊢
    have hz' : (gamma.plan i.castSucc i.succ : ℝ) = 0 := congrArg NNReal.toReal hz
    rw [hz', finiteWeilNodalPrefixDifference_signed_mass h hh, hs, neg_one_mul] at hp
    linarith only [hp]

theorem finiteWeilNodalOrientedMixtureTransport_index_minimum_iff {r : ℕ}
    (h : Fin (r + 2) → ℝ) (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1)
    (hba : (b : ℝ) ≤ (a : ℝ))
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b)) :
    finiteWeilCouplingCost gamma finiteWeilIndexCost = (a : ℝ) - (b : ℝ) ↔
      gamma = finiteWeilNodalOrientedMixtureCoupling h hh a b hba := by
  refine ⟨fun hopt => ?_, fun he => by rw [he, finiteWeilNodalOrientedMixtureCoupling_index_cost]⟩
  have hc := finiteWeilNodalOrientedMixtureCoupling_index_cost h hh a b hba
  apply finiteWeilCoupling_ext_of_off_diagonal
  intro u v he
  by_cases ha : (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)
  · obtain ⟨i, hi⟩ := finiteWeilCanonicalEdge_covers_adjacent r u v ha
    rcases hi with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · rw [← hu, ← hv]
      apply NNReal.coe_injective
      rw [finiteWeilNodalOrientedMixtureTransport_edge_mass h hh a b gamma hopt,
        finiteWeilNodalOrientedMixtureTransport_edge_mass h hh a b _ hc]
    · rw [← hu, ← hv, finiteWeilNodalOrientedMixtureTransport_reverse_edge_zero h hh a b gamma hopt,
        finiteWeilNodalOrientedMixtureTransport_reverse_edge_zero h hh a b _ hc]
  · have hval : (u : ℕ) ≠ (v : ℕ) := fun e => he (Fin.ext e)
    have hfar : (u : ℕ) + 1 < (v : ℕ) ∨ (v : ℕ) + 1 < (u : ℕ) := by omega
    rw [finiteWeilNodalOrientedMixtureTransport_index_banded h hh a b gamma hopt u v hfar,
      finiteWeilNodalOrientedMixtureTransport_index_banded h hh a b _ hc u v hfar]

/-- The canonical coupling of `ν_a` to `ν_b`: the oriented coupling or the transpose of the
reverse one. -/
def finiteWeilNodalMixtureCoupling {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a b : Set.Icc (0 : ℝ) 1) :
    HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b) :=
  if hba : (b : ℝ) ≤ (a : ℝ) then finiteWeilNodalOrientedMixtureCoupling h hh a b hba
  else finiteWeilCouplingTranspose
    (finiteWeilNodalOrientedMixtureCoupling h hh b a ((le_total (a : ℝ) (b : ℝ)).resolve_right hba))

theorem finiteWeilNodalMixtureCoupling_cost_eq {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a b : Set.Icc (0 : ℝ) 1) (c : Fin (r + 2) → Fin (r + 2) → ℝ) (hc : ∀ u, c u u = 0)
    (hsym : ∀ u v, c u v = c v u) :
    finiteWeilCouplingCost (finiteWeilNodalMixtureCoupling h hh a b) c =
      |(a : ℝ) - (b : ℝ)| * finiteWeilCouplingCost (finiteWeilNodalCoupling h hh) c := by
  by_cases hba : (b : ℝ) ≤ (a : ℝ)
  · rw [finiteWeilNodalMixtureCoupling, dif_pos hba,
      finiteWeilNodalOrientedMixtureCoupling_cost_eq h hh a b hba c hc,
      abs_of_nonneg (sub_nonneg.mpr hba)]
  · have hab : (a : ℝ) ≤ (b : ℝ) := (le_total (a : ℝ) (b : ℝ)).resolve_right hba
    rw [finiteWeilNodalMixtureCoupling, dif_neg hba, finiteWeilCouplingCost_transpose _ c hsym,
      finiteWeilNodalOrientedMixtureCoupling_cost_eq h hh b a _ c hc,
      abs_of_nonpos (sub_nonpos.mpr hab)]
    ring

/-- The common mass of two equal mixtures stays on the diagonal: at `a = b` the coupling is
diagonal. -/
theorem finiteWeilNodalMixtureCoupling_self_off_diagonal {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a : Set.Icc (0 : ℝ) 1) (u v : Fin (r + 2)) (huv : u ≠ v) :
    (finiteWeilNodalMixtureCoupling h hh a a).plan u v = 0 := by
  rw [finiteWeilNodalMixtureCoupling, dif_pos le_rfl]
  apply NNReal.coe_injective
  change finiteWeilNodalOrientedMixturePlan h a a u v = 0
  simp [finiteWeilNodalOrientedMixturePlan, huv]

/-! ### Index cost between mixtures: exactly `|a - b|`, with a unique optimum -/

theorem finiteWeilNodalMixtureCoupling_index_cost {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) :
    finiteWeilCouplingCost (finiteWeilNodalMixtureCoupling h hh a b) finiteWeilIndexCost =
      |(a : ℝ) - (b : ℝ)| := by
  rw [finiteWeilNodalMixtureCoupling_cost_eq h hh a b _ finiteWeilIndexCost_self
    finiteWeilIndexCost_symm, finiteWeilNodalCoupling_index_cost, mul_one]

theorem finiteWeilNodalMixtureTransport_index_lower_bound {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b)) :
    |(a : ℝ) - (b : ℝ)| ≤ finiteWeilCouplingCost gamma finiteWeilIndexCost := by
  rcases le_total (b : ℝ) (a : ℝ) with hba | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact finiteWeilNodalOrientedMixtureTransport_index_lower_bound h hh a b gamma
  · have ht := finiteWeilNodalOrientedMixtureTransport_index_lower_bound h hh b a
      (finiteWeilCouplingTranspose gamma)
    rw [finiteWeilCouplingCost_transpose _ _ finiteWeilIndexCost_symm] at ht
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith only [ht]

theorem finiteWeilNodalMixtureTransport_index_minimum_iff {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b)) :
    finiteWeilCouplingCost gamma finiteWeilIndexCost = |(a : ℝ) - (b : ℝ)| ↔
      gamma = finiteWeilNodalMixtureCoupling h hh a b := by
  refine ⟨fun hopt => ?_, fun he => by rw [he, finiteWeilNodalMixtureCoupling_index_cost]⟩
  by_cases hba : (b : ℝ) ≤ (a : ℝ)
  · rw [finiteWeilNodalMixtureCoupling, dif_pos hba]
    apply (finiteWeilNodalOrientedMixtureTransport_index_minimum_iff h hh a b hba gamma).mp
    simpa only [abs_of_nonneg (sub_nonneg.mpr hba)] using hopt
  · have hab : (a : ℝ) ≤ (b : ℝ) := (le_total (a : ℝ) (b : ℝ)).resolve_right hba
    rw [finiteWeilNodalMixtureCoupling, dif_neg hba]
    have ht : finiteWeilCouplingCost (finiteWeilCouplingTranspose gamma) finiteWeilIndexCost =
        (b : ℝ) - (a : ℝ) := by
      rw [finiteWeilCouplingCost_transpose _ _ finiteWeilIndexCost_symm, hopt,
        abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
    have he := (finiteWeilNodalOrientedMixtureTransport_index_minimum_iff h hh b a hab
      (finiteWeilCouplingTranspose gamma)).mp ht
    have he' := congrArg (fun g => finiteWeilCouplingTranspose g) he
    simpa only [finiteWeilCouplingTranspose_involutive] using he'

/-- Between any two mixtures in the fiber the optimal index cost is exactly `|a - b|`, attained
by a unique coupling. -/
theorem finiteWeilNodalMixtureTransport_index_unique_minimizer {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
        (finiteWeilNodalMixtureNNProfile h hh b),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
          (finiteWeilNodalMixtureNNProfile h hh b),
        finiteWeilCouplingCost gamma finiteWeilIndexCost ≤
          finiteWeilCouplingCost eta finiteWeilIndexCost := by
  refine ⟨finiteWeilNodalMixtureCoupling h hh a b, fun eta => ?_, fun gamma hg => ?_⟩
  · rw [finiteWeilNodalMixtureCoupling_index_cost]
    exact finiteWeilNodalMixtureTransport_index_lower_bound h hh a b eta
  · have hle := hg (finiteWeilNodalMixtureCoupling h hh a b)
    rw [finiteWeilNodalMixtureCoupling_index_cost] at hle
    exact (finiteWeilNodalMixtureTransport_index_minimum_iff h hh a b gamma).mp
      (le_antisymm hle (finiteWeilNodalMixtureTransport_index_lower_bound h hh a b gamma))

/-! ### Ordered node costs between mixtures -/

theorem finiteWeilNodalMixtureCoupling_cut_cost {r : ℕ} (h : Fin (r + 2) → ℝ) (hh : StrictMono h)
    (a b : Set.Icc (0 : ℝ) 1) (i : Fin (r + 1)) :
    finiteWeilCouplingCost (finiteWeilNodalMixtureCoupling h hh a b) (finiteWeilCutCost i) =
      |(a : ℝ) - (b : ℝ)| * finiteWeilNodalEdgeMass h i := by
  rw [finiteWeilNodalMixtureCoupling_cost_eq h hh a b _ (finiteWeilCutCost_self i)
    (finiteWeilCutCost_symm i), finiteWeilNodalCoupling_cut_cost h hh]

theorem finiteWeilNodalMixtureTransport_cut_lower_bound {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b)) (i : Fin (r + 1)) :
    |(a : ℝ) - (b : ℝ)| * finiteWeilNodalEdgeMass h i ≤
      finiteWeilCouplingCost gamma (finiteWeilCutCost i) := by
  have hf (p q : Set.Icc (0 : ℝ) 1)
      (eta : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh p)
        (finiteWeilNodalMixtureNNProfile h hh q)) :
      ((p : ℝ) - (q : ℝ)) * finiteWeilNodalEdgeMass h i ≤
        finiteWeilCouplingCost eta (finiteWeilCutCost i) := by
    have hd := finiteWeilCoupling_dual_bound eta (finiteWeilCutCost i)
      (fun u => finiteWeilBinomialParity r i.castSucc * finiteWeilCutIndicator i u)
      (finiteWeilCanonicalProfiles_cut_dual r i)
    rw [finiteWeilNodalMixtureNNProfile_pairing,
      finiteWeilNodalProfiles_cut_dual_pairing h hh] at hd
    exact hd
  rcases le_total (b : ℝ) (a : ℝ) with hba | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hf a b gamma
  · have ht := hf b a (finiteWeilCouplingTranspose gamma)
    rw [finiteWeilCouplingCost_transpose _ _ (finiteWeilCutCost_symm i)] at ht
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith only [ht]

theorem finiteWeilNodalMixtureCoupling_ordered_cost {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) (x : Fin (r + 2) → ℝ) (hx : Monotone x) :
    finiteWeilCouplingCost (finiteWeilNodalMixtureCoupling h hh a b) (fun u v => |x u - x v|) =
      |(a : ℝ) - (b : ℝ)| *
        ∑ i : Fin (r + 1), finiteWeilNodalEdgeMass h i * (x i.succ - x i.castSucc) := by
  rw [finiteWeilNodalMixtureCoupling_cost_eq h hh a b _ (fun u => by simp)
    (fun u v => abs_sub_comm _ _), finiteWeilNodalCoupling_ordered_cost h hh x hx]

theorem finiteWeilNodalMixtureTransport_ordered_optimal {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) (x : Fin (r + 2) → ℝ) (hx : Monotone x)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b)) :
    finiteWeilCouplingCost (finiteWeilNodalMixtureCoupling h hh a b) (fun u v => |x u - x v|) ≤
      finiteWeilCouplingCost gamma (fun u v => |x u - x v|) := by
  rw [finiteWeilCoupling_ordered_cost_eq _ x hx, finiteWeilCoupling_ordered_cost_eq _ x hx]
  apply Finset.sum_le_sum
  intro i _
  rw [finiteWeilNodalMixtureCoupling_cut_cost h hh]
  apply mul_le_mul_of_nonneg_left (finiteWeilNodalMixtureTransport_cut_lower_bound h hh a b gamma i)
  exact sub_nonneg.mpr (hx (show i.castSucc ≤ i.succ from by change i.val ≤ i.val + 1; omega))

theorem finiteWeilNodalMixtureTransport_ordered_minimum_iff {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) (x : Fin (r + 2) → ℝ) (hx : StrictMono x)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
      (finiteWeilNodalMixtureNNProfile h hh b)) :
    finiteWeilCouplingCost gamma (fun u v => |x u - x v|) =
      finiteWeilCouplingCost (finiteWeilNodalMixtureCoupling h hh a b) (fun u v => |x u - x v|) ↔
        gamma = finiteWeilNodalMixtureCoupling h hh a b := by
  refine ⟨fun hopt => ?_, fun he => by rw [he]⟩
  have hgap (i : Fin (r + 1)) : 0 < x i.succ - x i.castSucc :=
    sub_pos.mpr (hx (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))
  have hn (i : Fin (r + 1)) :
      0 ≤ finiteWeilCouplingCost gamma (finiteWeilCutCost i) -
        |(a : ℝ) - (b : ℝ)| * finiteWeilNodalEdgeMass h i :=
    sub_nonneg.mpr (finiteWeilNodalMixtureTransport_cut_lower_bound h hh a b gamma i)
  rw [finiteWeilCoupling_ordered_cost_eq _ x hx.monotone,
    finiteWeilCoupling_ordered_cost_eq _ x hx.monotone] at hopt
  simp only [finiteWeilNodalMixtureCoupling_cut_cost h hh] at hopt
  have hz : (∑ i : Fin (r + 1), (x i.succ - x i.castSucc) *
      (finiteWeilCouplingCost gamma (finiteWeilCutCost i) -
        |(a : ℝ) - (b : ℝ)| * finiteWeilNodalEdgeMass h i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hopt, sub_self]
  have hcut (i : Fin (r + 1)) : finiteWeilCouplingCost gamma (finiteWeilCutCost i) =
      |(a : ℝ) - (b : ℝ)| * finiteWeilNodalEdgeMass h i := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (le_of_lt (hgap j)) (hn j))).mp hz i (Finset.mem_univ i)
    have he := (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hgap i))
    linarith only [he]
  apply (finiteWeilNodalMixtureTransport_index_minimum_iff h hh a b gamma).mp
  rw [finiteWeilCoupling_index_cost_eq_cuts]
  simp_rw [hcut]
  rw [← Finset.mul_sum, finiteWeilNodalEdgeMass_sum h hh, mul_one]

/-- For every strictly increasing node cost, the mixture coupling is the unique optimal coupling
of `ν_a` to `ν_b`; in particular for the node cost `|h_i - h_j|`. -/
theorem finiteWeilNodalMixtureTransport_ordered_unique_minimizer {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) (x : Fin (r + 2) → ℝ) (hx : StrictMono x) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
        (finiteWeilNodalMixtureNNProfile h hh b),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilNodalMixtureNNProfile h hh a)
          (finiteWeilNodalMixtureNNProfile h hh b),
        finiteWeilCouplingCost gamma (fun u v => |x u - x v|) ≤
          finiteWeilCouplingCost eta (fun u v => |x u - x v|) := by
  refine ⟨finiteWeilNodalMixtureCoupling h hh a b,
    finiteWeilNodalMixtureTransport_ordered_optimal h hh a b x hx.monotone, fun gamma hg => ?_⟩
  apply (finiteWeilNodalMixtureTransport_ordered_minimum_iff h hh a b x hx gamma).mp
  exact le_antisymm (hg (finiteWeilNodalMixtureCoupling h hh a b))
    (finiteWeilNodalMixtureTransport_ordered_optimal h hh a b x hx.monotone gamma)

/-- The optimal strictly increasing node cost between two mixtures vanishes only at `a = b`. -/
theorem finiteWeilNodalMixtureCoupling_ordered_cost_eq_zero_iff {r : ℕ} (h : Fin (r + 2) → ℝ)
    (hh : StrictMono h) (a b : Set.Icc (0 : ℝ) 1) (x : Fin (r + 2) → ℝ) (hx : StrictMono x) :
    finiteWeilCouplingCost (finiteWeilNodalMixtureCoupling h hh a b) (fun u v => |x u - x v|) = 0 ↔
      a = b := by
  rw [finiteWeilNodalMixtureCoupling_ordered_cost h hh a b x hx.monotone, mul_eq_zero]
  have hpos : 0 < ∑ i : Fin (r + 1), finiteWeilNodalEdgeMass h i * (x i.succ - x i.castSucc) :=
    Finset.sum_pos (fun i _ => mul_pos (finiteWeilNodalEdgeMass_pos h hh i)
      (sub_pos.mpr (hx (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))))
      Finset.univ_nonempty
  constructor
  · rintro (hab | hz)
    · exact Subtype.ext (sub_eq_zero.mp (abs_eq_zero.mp hab))
    · exact absurd hz hpos.ne'
  · intro hab
    subst b
    exact Or.inl (by simp)

/-! ### The canonical logarithmic cluster is the special case `h = log nodes` -/

theorem finiteWeilCanonicalPositiveProfile_eq_nodal (r k : ℕ) :
    finiteWeilCanonicalPositiveProfile r k =
      finiteWeilNodalPositiveProfile (finiteWeilClusterLogNodes r k) := rfl

theorem finiteWeilCanonicalNegativeProfile_eq_nodal (r k : ℕ) :
    finiteWeilCanonicalNegativeProfile r k =
      finiteWeilNodalNegativeProfile (finiteWeilClusterLogNodes r k) := rfl

theorem finiteWeilCanonicalEdgeMass_eq_nodal (r k : ℕ) :
    finiteWeilCanonicalEdgeMass r k = finiteWeilNodalEdgeMass (finiteWeilClusterLogNodes r k) := rfl

/-! ### Why the nodal producer is needed -/

/-- Alternating signs and zero total mass do not force alternating prefix signs: for `u > v > 0`
the vector `(u, -v, v, -u)` alternates and sums to zero, but its first two prefix sums are both
positive. -/
theorem alternating_zero_sum_prefix_signs_not_forced {u v : ℝ} (hv : 0 < v) (huv : v < u) :
    let c : Fin 4 → ℝ := ![u, -v, v, -u]
    (∀ i : Fin 3, c i.castSucc * c i.succ < 0) ∧ (∑ i, c i) = 0 ∧
      0 < c 0 ∧ 0 < c 0 + c 1 := by
  intro c
  have hu : 0 < u := hv.trans huv
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> simp [c] <;> nlinarith
  · simp [c, Fin.sum_univ_four]
  · simp [c, hu]
  · simp [c]
    linarith

end RHTower
