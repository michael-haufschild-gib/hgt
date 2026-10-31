import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Newton identities and the pair-difference polynomial from power sums

Given a degree `M` and power sums `s_r = ∑_{i ∈ t} m_i z_i^r` (`1 ≤ r ≤ M`), the classical
Newton recurrence reconstructs the elementary symmetric coefficients and hence the exact monic
divisor polynomial `∏_{i ∈ t} (X - z_i)^{m_i}` without root coordinates. Convolving the power
sums binomially produces the power sums of all `M²` pairwise differences `z_i - z_j` and
reconstructs `∏_{i, j ∈ t} (X - (z_i - z_j))^{m_i m_j}` directly from `(M, s_1, …, s_{M²})`.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-- Elementary symmetric values reconstructed recursively from power sums `s 1, s 2, …`
via Newton's identities `k e_k = ∑_{j=0}^{k-1} (-1)^j e_{k-1-j} s_{j+1}`. -/
def newtonElem (s : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 =>
      ((k + 1 : ℂ))⁻¹ *
        ∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * newtonElem s (k - j) * s (j + 1)

/-- Monic degree-`M` polynomial reconstructed from Newton elementary symmetric values. -/
def newtonPoly (M : ℕ) (s : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (M + 1), C ((-1 : ℂ) ^ k * newtonElem s k) * X ^ (M - k)

/-- Binomial convolution converting degree-`M` power sums `s` into the power sums of all
ordered pairwise differences `z_i - z_j`. -/
def pairDiffPowerSum (M : ℕ) (s : ℕ → ℂ) (K : ℕ) : ℂ :=
  let s₀ : ℕ → ℂ := fun r => if r = 0 then (M : ℂ) else s r
  ∑ r ∈ Finset.range (K + 1),
    (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * s₀ r * s₀ (K - r)

/-- Monic degree-`M²` pair-difference polynomial reconstructed solely from `(M, s_1, …, s_{M²})`. -/
def pairDiffPoly (M : ℕ) (s : ℕ → ℂ) : Polynomial ℂ :=
  newtonPoly (M ^ 2) (pairDiffPowerSum M s)

@[simp]
theorem newtonPoly_zero (s : ℕ → ℂ) : newtonPoly 0 s = 1 := by
  simp [newtonPoly, newtonElem]

@[simp]
theorem pairDiffPoly_zero (s : ℕ → ℂ) : pairDiffPoly 0 s = 1 := by
  simp [pairDiffPoly]

private def listPowerSum (L : List ℂ) (r : ℕ) : ℂ :=
  (L.map (fun a => a ^ r)).sum

private def revPoly : List ℂ → Polynomial ℂ
  | [] => 1
  | a :: L => (1 - C a * X) * revPoly L

private def leibnizSum : List ℂ → Polynomial ℂ
  | [] => 0
  | a :: L => C a * revPoly L + (1 - C a * X) * leibnizSum L

private def truncPowerPoly (L : List ℂ) (K : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range K, C (listPowerSum L (j + 1)) * X ^ j

private def remSum : List ℂ → ℕ → Polynomial ℂ
  | [], _ => 0
  | a :: L, K => C (a ^ (K + 1)) * revPoly L + (1 - C a * X) * remSum L K

private lemma derivative_revPoly (L : List ℂ) :
    derivative (revPoly L) = -leibnizSum L := by
  induction L with
  | nil => simp [revPoly, leibnizSum]
  | cons a L ih =>
    simp only [revPoly, leibnizSum, derivative_mul, derivative_sub, derivative_one,
      derivative_C, derivative_X, zero_mul, mul_one, zero_sub, ih]
    ring

private lemma one_sub_mul_geom_sum (a : ℂ) (K : ℕ) :
    (1 - C a * X) * (∑ j ∈ Finset.range K, C (a ^ (j + 1)) * X ^ j) =
      C a - C (a ^ (K + 1)) * X ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hpow : C a * X * (C (a ^ (K + 1)) * X ^ K) = C (a ^ (K + 2)) * X ^ (K + 1) := by
      rw [show K + 2 = (K + 1) + 1 by omega, pow_succ a (K + 1), C.map_mul, pow_succ X K]
      ring
    calc
      C a - C (a ^ (K + 1)) * X ^ K + (1 - C a * X) * (C (a ^ (K + 1)) * X ^ K) =
          C a - C a * X * (C (a ^ (K + 1)) * X ^ K) := by ring
      _ = C a - C (a ^ (K + 2)) * X ^ (K + 1) := by rw [hpow]

private lemma truncPowerPoly_cons (a : ℂ) (L : List ℂ) (K : ℕ) :
    truncPowerPoly (a :: L) K =
      (∑ j ∈ Finset.range K, C (a ^ (j + 1)) * X ^ j) + truncPowerPoly L K := by
  unfold truncPowerPoly listPowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [List.map_cons, List.sum_cons, C.map_add, add_mul]

private lemma revPoly_mul_truncPowerPoly (L : List ℂ) (K : ℕ) :
    revPoly L * truncPowerPoly L K = leibnizSum L - X ^ K * remSum L K := by
  induction L with
  | nil =>
    simp [revPoly, leibnizSum, remSum, truncPowerPoly, listPowerSum]
  | cons a L ih =>
    rw [revPoly, truncPowerPoly_cons, leibnizSum, remSum]
    calc
      (1 - C a * X) * revPoly L *
          ((∑ j ∈ Finset.range K, C (a ^ (j + 1)) * X ^ j) + truncPowerPoly L K) =
          revPoly L * ((1 - C a * X) * ∑ j ∈ Finset.range K, C (a ^ (j + 1)) * X ^ j) +
            (1 - C a * X) * (revPoly L * truncPowerPoly L K) := by ring
      _ = revPoly L * (C a - C (a ^ (K + 1)) * X ^ K) +
            (1 - C a * X) * (leibnizSum L - X ^ K * remSum L K) := by
          rw [one_sub_mul_geom_sum, ih]
      _ = C a * revPoly L + (1 - C a * X) * leibnizSum L -
            X ^ K * (C (a ^ (K + 1)) * revPoly L + (1 - C a * X) * remSum L K) := by ring

private lemma revPoly_coeff_zero (L : List ℂ) : (revPoly L).coeff 0 = 1 := by
  induction L with
  | nil => simp [revPoly]
  | cons a L ih =>
    rw [revPoly, mul_coeff_zero, ih]
    simp

private lemma revPoly_newton_recurrence (L : List ℂ) (k : ℕ) :
    -((k + 1 : ℂ) * (revPoly L).coeff (k + 1)) =
      ∑ j ∈ Finset.range (k + 1), (revPoly L).coeff (k - j) * listPowerSum L (j + 1) := by
  have h1 := congrArg (fun P : Polynomial ℂ => P.coeff k) (revPoly_mul_truncPowerPoly L (k + 1))
  have hrem : (X ^ (k + 1) * remSum L (k + 1)).coeff k = 0 := by
    rw [coeff_X_pow_mul']
    simp
  have hleib : (leibnizSum L).coeff k = -((k + 1 : ℂ) * (revPoly L).coeff (k + 1)) := by
    have hd := congrArg (fun P : Polynomial ℂ => P.coeff k) (derivative_revPoly L)
    rw [coeff_derivative, coeff_neg] at hd
    linear_combination hd
  rw [coeff_sub, hrem, sub_zero, hleib] at h1
  rw [← h1]
  unfold truncPowerPoly
  rw [Finset.mul_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← mul_assoc, coeff_mul_X_pow', if_pos hjk, coeff_mul_C]

private lemma newtonElem_eq_signed_revPoly_coeff (L : List ℂ) {s : ℕ → ℂ} {K : ℕ}
    (hs : ∀ r, 1 ≤ r → r ≤ K → s r = listPowerSum L r) :
    ∀ k ≤ K, newtonElem s k = (-1 : ℂ) ^ k * (revPoly L).coeff k := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · simp [newtonElem, revPoly_coeff_zero]
    · have hk1ne : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [newtonElem]
      have hsum :
          (∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j * newtonElem s (k - j) * s (j + 1)) =
            (-1 : ℂ) ^ k * ∑ j ∈ Finset.range (k + 1),
              (revPoly L).coeff (k - j) * listPowerSum L (j + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hrec := ih (k - j) (by omega) (by omega)
        have hsr := hs (j + 1) (by omega) (by omega)
        rw [hrec, hsr]
        have hsign : (-1 : ℂ) ^ j * (-1 : ℂ) ^ (k - j) = (-1 : ℂ) ^ k := by
          rw [← pow_add, Nat.add_sub_of_le hjk]
        calc
          (-1 : ℂ) ^ j * ((-1 : ℂ) ^ (k - j) * (revPoly L).coeff (k - j)) *
              listPowerSum L (j + 1) =
              ((-1 : ℂ) ^ j * (-1 : ℂ) ^ (k - j)) *
                ((revPoly L).coeff (k - j) * listPowerSum L (j + 1)) := by ring
          _ = (-1 : ℂ) ^ k * ((revPoly L).coeff (k - j) * listPowerSum L (j + 1)) := by
              rw [hsign]
      rw [hsum, ← revPoly_newton_recurrence]
      rw [pow_succ (-1 : ℂ) k]
      field_simp [hk1ne]

private lemma natDegree_revPoly_le (L : List ℂ) : (revPoly L).natDegree ≤ L.length := by
  induction L with
  | nil => simp [revPoly]
  | cons a L ih =>
    rw [revPoly]
    have hdeg1 : (1 - C a * X).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans ?_
      simp only [natDegree_one, zero_max]
      exact natDegree_mul_le.trans (by simp [natDegree_C, natDegree_X])
    exact (natDegree_mul_le).trans (by simp [List.length_cons]; omega)

private lemma eval_revPoly (L : List ℂ) (u : ℂ) :
    (revPoly L).eval u = (L.map (fun a => 1 - a * u)).prod := by
  induction L with
  | nil => simp [revPoly]
  | cons a L ih => simp [revPoly, ih]

private lemma revPoly_coeff_length (L : List ℂ) :
    (revPoly L).coeff L.length = (L.map (fun a => -a)).prod := by
  induction L with
  | nil => simp [revPoly]
  | cons a L ih =>
    rw [revPoly, show (1 - C a * X) * revPoly L = revPoly L - C a * (X * revPoly L) by ring]
    have h0 : (revPoly L).coeff (L.length + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_revPoly_le L) (by omega))
    simp [List.length_cons, h0, coeff_C_mul, coeff_X_mul, ih]

private lemma prod_X_sub_C_eq_homogenized_revPoly (L : List ℂ) :
    (L.map (fun a => X - C a)).prod =
      ∑ k ∈ Finset.range (L.length + 1), C ((revPoly L).coeff k) * X ^ (L.length - k) := by
  haveI : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  apply Polynomial.funext
  intro w
  rw [eval_list_prod, List.map_map, eval_finsetSum]
  by_cases hw : w = 0
  · subst hw
    rw [Finset.sum_eq_single L.length]
    · simp only [Function.comp_def, eval_sub, eval_X, eval_C, zero_sub,
        Nat.sub_self, pow_zero, mul_one, revPoly_coeff_length]
    · intro k hk hne
      have hklt : k < L.length := by
        have := Finset.mem_range.mp hk
        omega
      have hpos : L.length - k ≠ 0 := by omega
      simp [zero_pow hpos]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self L.length)) hmem
  · have heval := eval_eq_sum_range' (lt_of_le_of_lt (natDegree_revPoly_le L)
      (Nat.lt_succ_self L.length)) w⁻¹
    have hmul : w ^ L.length * (revPoly L).eval w⁻¹ =
        ∑ k ∈ Finset.range (L.length + 1), (revPoly L).coeff k * w ^ (L.length - k) := by
      rw [heval, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkle : k ≤ L.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpow : w ^ L.length * (w⁻¹) ^ k = w ^ (L.length - k) := by
        have hsplit : w ^ L.length = w ^ (L.length - k) * w ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hkle]
        rw [hsplit, mul_assoc, ← mul_pow, mul_inv_cancel₀ hw, one_pow, mul_one]
      calc
        w ^ L.length * ((revPoly L).coeff k * (w⁻¹) ^ k) =
            (revPoly L).coeff k * (w ^ L.length * (w⁻¹) ^ k) := by ring
        _ = (revPoly L).coeff k * w ^ (L.length - k) := by rw [hpow]
    have hprod : w ^ L.length * (L.map (fun a => 1 - a * w⁻¹)).prod =
        (L.map ((fun p : Polynomial ℂ => p.eval w) ∘ fun a => X - C a)).prod := by
      clear heval hmul
      induction L with
      | nil => simp
      | cons a L ih =>
        simp only [List.length_cons, pow_succ', List.map_cons, List.prod_cons,
          Function.comp_apply, eval_sub, eval_X, eval_C]
        have hlin : w * (1 - a * w⁻¹) = w - a := by
          field_simp [hw]
        calc
          w * w ^ L.length * ((1 - a * w⁻¹) * (List.map (fun b => 1 - b * w⁻¹) L).prod) =
              (w * (1 - a * w⁻¹)) * (w ^ L.length * (List.map (fun b => 1 - b * w⁻¹) L).prod) := by
            ring
          _ = (w - a) * (List.map ((fun p : Polynomial ℂ => p.eval w) ∘ fun b => X - C b) L).prod := by
            rw [hlin, ih]
    rw [← hprod, ← eval_revPoly, hmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp

/-- Newton's identities reconstruct any list product `∏_{a ∈ L} (X - a)` from its power sums. -/
theorem newtonPoly_eq_list_prod (L : List ℂ) {s : ℕ → ℂ}
    (hs : ∀ r, 1 ≤ r → r ≤ L.length → s r = (L.map (fun a => a ^ r)).sum) :
    newtonPoly L.length s = (L.map (fun a => X - C a)).prod := by
  rw [prod_X_sub_C_eq_homogenized_revPoly, newtonPoly]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkle : k ≤ L.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hcoeff := newtonElem_eq_signed_revPoly_coeff L hs k hkle
  have hsign : (-1 : ℂ) ^ k * ((-1 : ℂ) ^ k * (revPoly L).coeff k) = (revPoly L).coeff k := by
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [hcoeff, hsign]

private def weightedRootList {κ : Type*} (l : List κ) (z : κ → ℂ) (m : κ → ℕ) : List ℂ :=
  l.flatMap (fun i => List.replicate (m i) (z i))

private lemma weightedRootList_length {κ : Type*} (l : List κ) (z : κ → ℂ) (m : κ → ℕ) :
    (weightedRootList l z m).length = (l.map m).sum := by
  unfold weightedRootList
  induction l with
  | nil => simp
  | cons i l ih => simp [List.flatMap_cons, ih]

private lemma weightedRootList_powerSum {κ : Type*} (l : List κ) (z : κ → ℂ) (m : κ → ℕ) (r : ℕ) :
    ((weightedRootList l z m).map (fun a => a ^ r)).sum =
      (l.map (fun i => (m i : ℂ) * (z i) ^ r)).sum := by
  unfold weightedRootList
  induction l with
  | nil => simp
  | cons i l ih => simp [List.flatMap_cons, List.map_replicate, nsmul_eq_mul, ih]

private lemma weightedRootList_prod {κ : Type*} (l : List κ) (z : κ → ℂ) (m : κ → ℕ) :
    ((weightedRootList l z m).map (fun a => X - C a)).prod =
      (l.map (fun i => (X - C (z i)) ^ m i)).prod := by
  unfold weightedRootList
  induction l with
  | nil => simp
  | cons i l ih => simp [List.flatMap_cons, List.map_replicate, ih]

/-- **Newton divisor polynomial reconstruction.** For any finite weighted root set `(t, z, m)` of
total multiplicity `M = ∑_{i ∈ t} m_i`, the polynomial `newtonPoly M s` built from the power sums
`s_r = ∑_{i ∈ t} m_i z_i^r` (`1 ≤ r ≤ M`) equals `∏_{i ∈ t} (X - C (z_i))^{m_i}`. -/
theorem newtonPoly_eq_finset_prod {κ : Type*} (t : Finset κ) (z : κ → ℂ) (m : κ → ℕ)
    {M : ℕ} {s : ℕ → ℂ} (hM : M = ∑ i ∈ t, m i)
    (hs : ∀ r, 1 ≤ r → r ≤ M → s r = ∑ i ∈ t, (m i : ℂ) * (z i) ^ r) :
    newtonPoly M s = ∏ i ∈ t, (X - C (z i)) ^ m i := by
  classical
  let l := t.toList
  let L := weightedRootList l z m
  have hlen : L.length = M := by
    dsimp only [L, l]
    rw [weightedRootList_length, Finset.sum_map_toList, hM]
  have hsL : ∀ r, 1 ≤ r → r ≤ L.length → s r = (L.map (fun a => a ^ r)).sum := by
    intro r hr1 hrL
    rw [hlen] at hrL
    rw [hs r hr1 hrL]
    dsimp only [L, l]
    rw [weightedRootList_powerSum, Finset.sum_map_toList]
  rw [← hlen, newtonPoly_eq_list_prod L hsL]
  dsimp only [L, l]
  rw [weightedRootList_prod, Finset.prod_map_toList]

private def listPairDiff (L : List ℂ) : List ℂ :=
  L.flatMap (fun a => L.map (fun b => a - b))

private lemma listPairDiff_length (L : List ℂ) :
    (listPairDiff L).length = L.length ^ 2 := by
  unfold listPairDiff
  have haux : ∀ L₁ : List ℂ, (L₁.flatMap (fun a => L.map (fun b => a - b))).length =
      L₁.length * L.length := by
    intro L₁
    induction L₁ with
    | nil => simp
    | cons a L₁ ih => simp [ih, Nat.succ_mul, Nat.add_comm]
  rw [haux, pow_two]

private lemma listPairDiff_prod {κ : Type*} (t : Finset κ) (z : κ → ℂ) (m : κ → ℕ) :
    let L := weightedRootList t.toList z m
    ((listPairDiff L).map (fun d => X - C d)).prod =
      ∏ i ∈ t, ∏ j ∈ t, (X - C (z i - z j)) ^ (m i * m j) := by
  classical
  intro L
  have houter : ∀ L₁ : List ℂ,
      ((L₁.flatMap (fun a => L.map (fun b => a - b))).map (fun d => X - C d)).prod =
        (L₁.map (fun a => (L.map (fun b => X - C (a - b))).prod)).prod := by
    intro L₁
    induction L₁ with
    | nil => simp
    | cons a L₁ ih =>
      rw [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons, List.prod_cons,
        ih, List.map_map]
      rfl
  change ((L.flatMap (fun a => L.map (fun b => a - b))).map (fun d => X - C d)).prod = _
  rw [houter]
  have hinner : ∀ a : ℂ,
      (L.map (fun b => X - C (a - b))).prod =
        ∏ j ∈ t, (X - C (a - z j)) ^ m j := by
    intro a
    dsimp only [L]
    have haux : ∀ l : List κ,
        ((weightedRootList l z m).map (fun b => X - C (a - b))).prod =
          (l.map (fun j => (X - C (a - z j)) ^ m j)).prod := by
      unfold weightedRootList
      intro l
      induction l with
      | nil => simp
      | cons j l ih =>
        rw [List.flatMap_cons, List.map_append, List.prod_append, List.map_replicate,
          List.prod_replicate, List.map_cons, List.prod_cons, ih]
    rw [haux, Finset.prod_map_toList]
  have hstep :
      (L.map (fun a => ∏ j ∈ t, (X - C (a - z j)) ^ m j)).prod =
        ∏ i ∈ t, (∏ j ∈ t, (X - C (z i - z j)) ^ m j) ^ m i := by
    dsimp only [L]
    have haux : ∀ l : List κ,
        ((weightedRootList l z m).map (fun a => ∏ j ∈ t, (X - C (a - z j)) ^ m j)).prod =
          (l.map (fun i => (∏ j ∈ t, (X - C (z i - z j)) ^ m j) ^ m i)).prod := by
      unfold weightedRootList
      intro l
      induction l with
      | nil => simp
      | cons i l ih =>
        rw [List.flatMap_cons, List.map_append, List.prod_append, List.map_replicate,
          List.prod_replicate, List.map_cons, List.prod_cons, ih]
    rw [haux, Finset.prod_map_toList]
  have hcongr : L.map (fun a => (L.map (fun b => X - C (a - b))).prod) =
      L.map (fun a => ∏ j ∈ t, (X - C (a - z j)) ^ m j) :=
    List.map_congr_left fun a _ => hinner a
  rw [hcongr, hstep]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm (m j) (m i)]

private lemma list_sum_eq_finset_sum_power {κ : Type*} (t : Finset κ) (z : κ → ℂ) (m : κ → ℕ)
    (r : ℕ) :
    ((weightedRootList t.toList z m).map (fun a => a ^ r)).sum =
      ∑ i ∈ t, (m i : ℂ) * (z i) ^ r := by
  classical
  rw [weightedRootList_powerSum, Finset.sum_map_toList]

private lemma listPairDiff_powerSum (L : List ℂ) (K : ℕ) :
    ((listPairDiff L).map (fun d => d ^ K)).sum =
      ∑ r ∈ Finset.range (K + 1),
        (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) *
          (L.map (fun a => a ^ r)).sum * (L.map (fun b => b ^ (K - r))).sum := by
  have hflat : ∀ L₁ : List ℂ,
      ((L₁.flatMap (fun a => L.map (fun b => a - b))).map (fun d => d ^ K)).sum =
        (L₁.map (fun a => (L.map (fun b => (a - b) ^ K)).sum)).sum := by
    intro L₁
    induction L₁ with
    | nil => simp
    | cons a L₁ ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        ih, List.map_map]
      rfl
  unfold listPairDiff
  rw [hflat]
  clear hflat
  have hbinom : ∀ a b : ℂ, (a - b) ^ K =
      ∑ r ∈ Finset.range (K + 1),
        (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a ^ r * b ^ (K - r) := by
    intro a b
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [neg_eq_neg_one_mul b, mul_pow]
    ring
  have hinner : ∀ a : ℂ, (L.map (fun b => (a - b) ^ K)).sum =
      ∑ r ∈ Finset.range (K + 1),
        (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a ^ r * (L.map (fun b => b ^ (K - r))).sum := by
    intro a
    induction L with
    | nil => simp
    | cons b L' ih =>
      rw [List.map_cons, List.sum_cons, ih, hbinom a b, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [List.map_cons, List.sum_cons]
      ring
  have houter : ∀ L₁ : List ℂ,
      (L₁.map (fun a => ∑ r ∈ Finset.range (K + 1),
        (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a ^ r *
          (L.map (fun b => b ^ (K - r))).sum)).sum =
        ∑ r ∈ Finset.range (K + 1),
          (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) *
            (L₁.map (fun a => a ^ r)).sum * (L.map (fun b => b ^ (K - r))).sum := by
    intro L₁
    induction L₁ with
    | nil => simp
    | cons a L₁ ih =>
      rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [List.map_cons, List.sum_cons]
      ring
  have hmap : L.map (fun a => (L.map (fun b => (a - b) ^ K)).sum) =
      L.map (fun a => ∑ r ∈ Finset.range (K + 1),
        (-1 : ℂ) ^ (K - r) * (Nat.choose K r : ℂ) * a ^ r *
          (L.map (fun b => b ^ (K - r))).sum) :=
    List.map_congr_left fun a _ => hinner a
  rw [hmap, houter]

/-- **Pair-difference polynomial reconstruction.** Given total multiplicity `M = ∑_{i ∈ t} m_i`
and power sums `s_r = ∑_{i ∈ t} m_i z_i^r` (`1 ≤ r ≤ M²`), `pairDiffPoly M s` equals the exact
weighted difference polynomial `∏_{i ∈ t} ∏_{j ∈ t} (X - C (z_i - z_j))^{m_i m_j}`. -/
theorem pairDiffPoly_eq_finset_prod {κ : Type*} (t : Finset κ) (z : κ → ℂ) (m : κ → ℕ)
    {M : ℕ} {s : ℕ → ℂ} (hM : M = ∑ i ∈ t, m i)
    (hs : ∀ r, 1 ≤ r → r ≤ M ^ 2 → s r = ∑ i ∈ t, (m i : ℂ) * (z i) ^ r) :
    pairDiffPoly M s = ∏ i ∈ t, ∏ j ∈ t, (X - C (z i - z j)) ^ (m i * m j) := by
  classical
  let L := weightedRootList t.toList z m
  have hlenL : L.length = M := by
    dsimp only [L]
    rw [weightedRootList_length, Finset.sum_map_toList, hM]
  have hlenD : (listPairDiff L).length = M ^ 2 := by
    rw [listPairDiff_length, hlenL]
  have hs0 : ∀ r, r ≤ M ^ 2 →
      (if r = 0 then (M : ℂ) else s r) = (L.map (fun a => a ^ r)).sum := by
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0
      simp only [ite_true]
      dsimp only [L]
      rw [list_sum_eq_finset_sum_power, hM, Nat.cast_sum]
      simp
    · rw [if_neg hr0, hs r (Nat.pos_of_ne_zero hr0) hr]
      exact (list_sum_eq_finset_sum_power t z m r).symm
  have hsD : ∀ K, 1 ≤ K → K ≤ (listPairDiff L).length →
      pairDiffPowerSum M s K = ((listPairDiff L).map (fun d => d ^ K)).sum := by
    intro K _ hK
    rw [hlenD] at hK
    unfold pairDiffPowerSum
    dsimp only
    rw [listPairDiff_powerSum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrK : r ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [hs0 r (hrK.trans hK), hs0 (K - r) ((Nat.sub_le K r).trans hK)]
  rw [pairDiffPoly, ← hlenD, newtonPoly_eq_list_prod (listPairDiff L) hsD]
  exact listPairDiff_prod t z m

/-- Pointwise evaluation of `pairDiffPoly M s` gives the exact product of shifted differences. -/
theorem eval_pairDiffPoly_eq_finset_prod {κ : Type*} (t : Finset κ) (z : κ → ℂ) (m : κ → ℕ)
    {M : ℕ} {s : ℕ → ℂ} (hM : M = ∑ i ∈ t, m i)
    (hs : ∀ r, 1 ≤ r → r ≤ M ^ 2 → s r = ∑ i ∈ t, (m i : ℂ) * (z i) ^ r) (w : ℂ) :
    (pairDiffPoly M s).eval w = ∏ i ∈ t, ∏ j ∈ t, (w - (z i - z j)) ^ (m i * m j) := by
  rw [pairDiffPoly_eq_finset_prod t z m hM hs, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.pairDiffPoly_eq_finset_prod
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.eval_pairDiffPoly_eq_finset_prod
