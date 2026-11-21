import GaloisForLFunctions.HTGeometry.Quantum.BoundaryResponse.SeriesNetwork
import Mathlib.Tactic.LinearCombination

/-!
# Simple low modes of a layered boundary response

Each color carries a mean-zero sign mode on its two families of layers.
Adding color-dependent terms to a positive complete-graph kernel leaves
all conductances positive and separates these modes below the rest of
the positive spectrum.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.BoundaryResponse

open WeightedGraph

noncomputable section

/-- Colors, two signs and a repeated layer index. -/
abbrev LayeredBoundary (K N : ℕ) := Fin (N + 1) × (Bool × Fin (K + 1))

private def layerSign : Bool → ℝ
  | false => 1
  | true => -1

private theorem layerSign_mul_self (s : Bool) : layerSign s * layerSign s = 1 := by
  cases s <;> norm_num [layerSign]

private theorem sum_layerSign (K : ℕ) : (∑ r : Bool × Fin (K + 1), layerSign r.1) = 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [layerSign, Finset.sum_const]

/-- The sign mode occupies exactly one color. -/
def colorMode {K N : ℕ} (i : Fin (N + 1)) (v : LayeredBoundary K N) : ℝ :=
  if v.1 = i then layerSign v.2.1 else 0

theorem colorMode_ne_zero (K : ℕ) {N : ℕ} (i : Fin (N + 1)) :
    (colorMode i : LayeredBoundary K N → ℝ) ≠ 0 := by
  intro h
  have h' := congrFun h ((i, (false, 0)) : LayeredBoundary K N)
  simp [colorMode, layerSign] at h'

private theorem sum_colorMode (K : ℕ) {N : ℕ} (i : Fin (N + 1)) :
    (∑ v : LayeredBoundary K N, colorMode i v) = 0 := by
  rw [Fintype.sum_prod_type]
  have he (j : Fin (N + 1)) : (∑ r : Bool × Fin (K + 1), colorMode i (j, r)) = 0 := by
    by_cases h : j = i
    · simpa only [colorMode, if_pos h] using sum_layerSign K
    · simp only [colorMode, if_neg h, Finset.sum_const_zero]
  simp only [he, Finset.sum_const_zero]

private def rowSize (K : ℕ) : ℝ := 2 * ((K + 1 : ℕ) : ℝ)

private theorem rowSize_pos (K : ℕ) : 0 < rowSize K := by unfold rowSize; positivity

private def rowPair {K N : ℕ} (i : Fin (N + 1)) (x : LayeredBoundary K N → ℝ) : ℝ :=
  ∑ r : Bool × Fin (K + 1), layerSign r.1 * x (i, r)

private theorem rowPair_const (K : ℕ) {N : ℕ} (i : Fin (N + 1)) :
    rowPair (K := K) i (fun _ => 1) = 0 := by
  simpa only [rowPair, mul_one] using sum_layerSign K

private theorem rowPair_colorMode (K : ℕ) {N : ℕ} (i j : Fin (N + 1)) :
    rowPair (K := K) i (colorMode j) = if i = j then rowSize K else 0 := by
  by_cases h : i = j
  · simp only [rowPair, colorMode, if_pos h, layerSign_mul_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one, rowSize]
  · simp only [rowPair, colorMode, if_neg h, mul_zero, Finset.sum_const_zero]

private def baselineWeight (N : ℕ) : ℝ := ((N + 1 : ℕ) : ℝ) + 1

private theorem baselineWeight_pos (N : ℕ) : 0 < baselineWeight N := by
  unfold baselineWeight
  positivity

private def modeWeight {N : ℕ} (i : Fin (N + 1)) : ℝ := ((N + 1 : ℕ) : ℝ) - (i.val : ℝ)

private theorem modeWeight_pos {N : ℕ} (i : Fin (N + 1)) : 0 < modeWeight i := by
  unfold modeWeight
  exact sub_pos.mpr (by exact_mod_cast i.isLt)

private theorem modeWeight_lt_baseline {N : ℕ} (i : Fin (N + 1)) :
    modeWeight i < baselineWeight N :=
  (sub_le_self _ (Nat.cast_nonneg i.val)).trans_lt (lt_add_of_pos_right _ one_pos)

private def kernel {K N : ℕ} (v u : LayeredBoundary K N) : ℝ :=
  baselineWeight N + if v.1 = u.1 then modeWeight v.1 * layerSign v.2.1 * layerSign u.2.1 else 0

private theorem kernel_symm {K N : ℕ} (v u : LayeredBoundary K N) : kernel v u = kernel u v := by
  by_cases h : v.1 = u.1
  · unfold kernel
    rw [if_pos h, if_pos h.symm, h]
    ring
  · simp only [kernel, if_neg h, if_neg (Ne.symm h)]

private theorem kernel_pos {K N : ℕ} (v u : LayeredBoundary K N) : 0 < kernel v u := by
  have h₁ := modeWeight_lt_baseline v.1
  have h₂ := (modeWeight_pos v.1).le
  by_cases h : v.1 = u.1
  · rw [kernel, if_pos h]
    cases hv : v.2.1 <;> cases hu : u.2.1 <;>
      simp only [layerSign, mul_one, mul_neg, neg_neg] <;>
      linarith only [h₁, h₂]
  · simpa only [kernel, if_neg h, add_zero] using baselineWeight_pos N

/-- Positive conductance matrix of the prescribed response. -/
def layeredBoundaryGraph (K N : ℕ) : WeightedGraph (LayeredBoundary K N) where
  w v u := if v = u then 0 else kernel v u
  w_symm v u := by
    by_cases h : v = u
    · subst u
      rfl
    · simp only [if_neg h, if_neg (Ne.symm h), kernel_symm v u]
  w_nonneg v u := by
    split_ifs
    · exact le_rfl
    · exact (kernel_pos v u).le
  w_diag v := if_pos rfl

theorem layeredBoundaryGraph_weight_pos {K N : ℕ} {v u : LayeredBoundary K N} (h : v ≠ u) :
    0 < (layeredBoundaryGraph K N).w v u := by
  simpa only [layeredBoundaryGraph, if_neg h] using kernel_pos v u

private theorem sum_kernel_mul {K N : ℕ} (v : LayeredBoundary K N) (x : LayeredBoundary K N → ℝ) :
    (∑ u, kernel v u * x u) = baselineWeight N * (∑ u, x u) +
      modeWeight v.1 * layerSign v.2.1 * rowPair v.1 x := by
  simp only [kernel, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ j : Fin (N + 1), if v.1 = j then ∑ r : Bool × Fin (K + 1),
        modeWeight v.1 * layerSign v.2.1 * layerSign r.1 * x (j, r) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : v.1 = j
      · simp only [if_pos h]
      · simp only [if_neg h, Finset.sum_const_zero]
    _ = _ := by
      rw [Fintype.sum_ite_eq, rowPair, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring

/-- The common eigenvalue above the low color modes. -/
def upperBoundaryLevel (K N : ℕ) : ℝ :=
  baselineWeight N * (Fintype.card (LayeredBoundary K N) : ℝ)

/-- The simple low eigenvalues, indexed in increasing order by color. -/
def colorEigenvalue (K : ℕ) {N : ℕ} (i : Fin (N + 1)) : ℝ :=
  upperBoundaryLevel K N - modeWeight i * rowSize K

private theorem layeredBoundaryGraph_flux {K N : ℕ} (x : LayeredBoundary K N → ℝ)
    (v : LayeredBoundary K N) :
    (layeredBoundaryGraph K N).networkFlux x v = upperBoundaryLevel K N * x v -
      baselineWeight N * (∑ u, x u) - modeWeight v.1 * layerSign v.2.1 * rowPair v.1 x := by
  have hmass : (∑ u, kernel v u) = upperBoundaryLevel K N := by
    have h := sum_kernel_mul v (fun _ => 1)
    simpa only [mul_one, rowPair_const, mul_zero, add_zero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, upperBoundaryLevel] using h
  have hw (u : LayeredBoundary K N) :
      (layeredBoundaryGraph K N).w v u * (x v - x u) =
        kernel v u * x v - kernel v u * x u := by
    by_cases h : v = u
    · subst u
      rw [sub_self, mul_zero, sub_self]
    · simp only [layeredBoundaryGraph, if_neg h, mul_sub]
  rw [networkFlux, Finset.sum_congr rfl (fun u _ => hw u), Finset.sum_sub_distrib, ← Finset.sum_mul,
    hmass, sum_kernel_mul]
  ring

theorem colorEigenvalue_bounds (K : ℕ) {N : ℕ} (i : Fin (N + 1)) :
    0 < colorEigenvalue K i ∧ colorEigenvalue K i < upperBoundaryLevel K N := by
  have hcard : (Fintype.card (LayeredBoundary K N) : ℝ) = ((N + 1 : ℕ) : ℝ) * rowSize K := by
    simp only [LayeredBoundary, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_ofNat, rowSize]
  have hN : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  have hsmall : rowSize K ≤ (Fintype.card (LayeredBoundary K N) : ℝ) := by
    rw [hcard]
    exact le_mul_of_one_le_left (rowSize_pos K).le hN
  constructor
  · apply sub_pos.mpr
    exact (mul_lt_mul_of_pos_right (modeWeight_lt_baseline i) (rowSize_pos K)).trans_le
      (mul_le_mul_of_nonneg_left hsmall (baselineWeight_pos N).le)
  · exact sub_lt_self _ (mul_pos (modeWeight_pos i) (rowSize_pos K))

theorem strictMono_colorEigenvalue (K N : ℕ) : StrictMono (colorEigenvalue K (N := N)) := by
  intro i j hij
  have h : (i.val : ℝ) < j.val := by exact_mod_cast hij
  have hα : modeWeight j < modeWeight i := by unfold modeWeight; linarith only [h]
  exact sub_lt_sub_left (mul_lt_mul_of_pos_right hα (rowSize_pos K)) _

/-- Each color mode is an eigenvector of the response network. -/
theorem layeredBoundaryGraph_flux_colorMode (K : ℕ) {N : ℕ} (i : Fin (N + 1))
    (v : LayeredBoundary K N) :
    (layeredBoundaryGraph K N).networkFlux (colorMode i) v = colorEigenvalue K i * colorMode i v := by
  rw [layeredBoundaryGraph_flux, sum_colorMode, mul_zero, sub_zero, rowPair_colorMode]
  by_cases h : v.1 = i
  · simp only [colorMode, h, if_true, colorEigenvalue]
    ring
  · simp only [colorMode, if_neg h, mul_zero, sub_zero]

private theorem sum_networkFlux_zero {V : Type*} [Fintype V] (G : WeightedGraph V) (x : V → ℝ) :
    (∑ v, G.networkFlux x v) = 0 := by
  simp only [networkFlux, mul_sub, Finset.sum_sub_distrib]
  rw [G.sum_sum_w_mul_left, G.sum_sum_w_mul_right, sub_self]

private theorem networkFlux_const_mul {V : Type*} [Fintype V] (G : WeightedGraph V)
    (c : ℝ) (x : V → ℝ) (v : V) :
    G.networkFlux (fun u => c * x u) v = c * G.networkFlux x v := by
  simp only [networkFlux, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

/-- Every positive eigenpair below the upper level is exactly one of
the color modes, up to a nonzero scalar. -/
theorem smallPositiveEigenpair_iff (K N : ℕ)
    (level : Set.Ioo (0 : ℝ) (upperBoundaryLevel K N)) (x : LayeredBoundary K N → ℝ) :
    (x ≠ 0 ∧ ∀ v, (layeredBoundaryGraph K N).networkFlux x v = (level : ℝ) * x v) ↔
      ∃ i : Fin (N + 1), (level : ℝ) = colorEigenvalue K i ∧
        ∃ c : ℝ, c ≠ 0 ∧ x = fun v => c * colorMode i v := by
  constructor
  · rintro ⟨hx, hlevel⟩
    have hpos : 0 < (level : ℝ) := level.2.1
    let D := upperBoundaryLevel K N - (level : ℝ)
    let P (i : Fin (N + 1)) := rowPair i x
    have hD : 0 < D := sub_pos.mpr level.2.2
    have hsum : (∑ v, x v) = 0 := by
      have h := sum_networkFlux_zero (layeredBoundaryGraph K N) x
      simp only [hlevel, ← Finset.mul_sum] at h
      exact (mul_eq_zero.mp h).resolve_left hpos.ne'
    have he (v : LayeredBoundary K N) : D * x v = modeWeight v.1 * layerSign v.2.1 * P v.1 := by
      have h := hlevel v
      rw [layeredBoundaryGraph_flux, hsum, mul_zero, sub_zero] at h
      dsimp only [D, P]
      linear_combination h
    have hcard : (Fintype.card (Bool × Fin (K + 1)) : ℝ) = rowSize K := by
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_ofNat, rowSize]
    have hrow (i : Fin (N + 1)) : D * P i = modeWeight i * rowSize K * P i := calc
      _ = ∑ r : Bool × Fin (K + 1), layerSign r.1 * (D * x (i, r)) := by
        rw [show P i = rowPair i x from rfl, rowPair, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
      _ = ∑ r : Bool × Fin (K + 1), layerSign r.1 * (modeWeight i * layerSign r.1 * P i) :=
        Finset.sum_congr rfl fun r _ => congrArg (layerSign r.1 * ·) (he (i, r))
      _ = ∑ _ : Bool × Fin (K + 1), modeWeight i * P i := by
        apply Finset.sum_congr rfl
        intro r _
        calc
          _ = modeWeight i * (layerSign r.1 * layerSign r.1) * P i := by ring
          _ = _ := by rw [layerSign_mul_self, mul_one]
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
        ring
    have hvanish (i : Fin (N + 1)) : (colorEigenvalue K i - (level : ℝ)) * P i = 0 := by
      have h := hrow i
      dsimp only [D] at h
      unfold colorEigenvalue
      linear_combination h
    have hnz : ∃ i, P i ≠ 0 := by
      by_contra h
      apply hx
      funext v
      have hi : P v.1 = 0 := not_ne_iff.mp (fun hp => h ⟨v.1, hp⟩)
      have hv := he v
      rw [hi, mul_zero] at hv
      exact (mul_eq_zero.mp hv).resolve_left hD.ne'
    obtain ⟨i, hi⟩ := hnz
    have hval : (level : ℝ) = colorEigenvalue K i :=
      (sub_eq_zero.mp ((mul_eq_zero.mp (hvanish i)).resolve_right hi)).symm
    have hz (j : Fin (N + 1)) (hj : j ≠ i) : P j = 0 := by
      apply (mul_eq_zero.mp (hvanish j)).resolve_left
      rw [hval]
      exact sub_ne_zero.mpr (fun h => hj ((strictMono_colorEigenvalue K N).injective h))
    refine ⟨i, hval, modeWeight i * P i / D,
      div_ne_zero (mul_ne_zero (modeWeight_pos i).ne' hi) hD.ne', ?_⟩
    funext v
    have hv : x v = modeWeight v.1 * layerSign v.2.1 * P v.1 / D :=
      (eq_div_iff hD.ne').mpr (by rw [mul_comm (x v)]; exact he v)
    rw [hv]
    by_cases hv' : v.1 = i
    · simp only [colorMode, hv', if_true]
      ring
    · rw [colorMode, if_neg hv', hz v.1 hv', mul_zero, zero_div, mul_zero]
  · rintro ⟨i, hi, c, hc, rfl⟩
    constructor
    · intro h
      apply colorMode_ne_zero K i
      funext v
      exact (mul_eq_zero.mp (congrFun h v)).resolve_left hc
    · intro v
      rw [networkFlux_const_mul, layeredBoundaryGraph_flux_colorMode, hi]
      ring

#print axioms layeredBoundaryGraph_weight_pos
#print axioms colorEigenvalue_bounds
#print axioms strictMono_colorEigenvalue
#print axioms smallPositiveEigenpair_iff

end

end GaloisForLFunctions.HTGeometry.BoundaryResponse
