import GaloisForLFunctions.AdelicKreinGeometry.TheSignatureOfASeparableAssembly
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The function-field conformal successor

Calibration of the conformal successor over `𝔽_q[T]`. On the additive group of a polynomial ring
`K[X]` the absolute value at infinity is `|p|_∞ = b^{deg p}` (`b = q` for `K = 𝔽_q`), and
multiplication by `X` is conformal for it with factor `b` (`absInf_X_mul`), the conformal factor of
Frobenius.

* **Ultrametric decomposition** (`absInf_sub_eq_sum`): with `p ∼_k p'` meaning that `p` and `p'`
  agree in all degrees `≥ k`, `|p − p'|_∞ = Σ_{k ≤ D} w_k 1[p ≁_k p']`, `w_0 = 1`,
  `w_k = b^k − b^{k−1}`.
* **Equivalence kernels are positive** (`re_sum_ite_eq_sum_normSq`, `re_sum_ite_eq_nonneg`):
  `Σ c̄_a c_b 1[f(a) = f(b)]` is the sum of the squares of the class sums.
* **One negative square** (`negIndex_negAbsInf`): `−|·|_∞` is conditionally positive, so it has
  exactly one negative square.

Over `𝔽_q` the conformal successor is quantized: the uniformizer at infinity acts with factor `q`,
and the index-one state is the same as over `ℚ` (`negIndex_negAbsRat`), where the factor of the
dilation `x ↦ ux` is the archimedean size `|u|`. The conformal mechanism therefore does not
distinguish `ℤ` from `𝔽_q[T]`; what distinguishes them is that over `𝔽_q` the factor is the size of
a single place.
-/

open Complex Finset Polynomial
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Equivalence kernels -/

/-- **Equivalence kernels are sums of squares**: `Σ c̄_a c_b 1[f(a) = f(b)] = Σ_v |Σ_{f(b) = v} c_b|²`. -/
theorem re_sum_ite_eq_sum_normSq {ι β : Type*} [Fintype ι] [DecidableEq β] (f : ι → β)
    (c : ι → ℂ) : (∑ a, ∑ b, conj (c a) * c b * (if f a = f b then 1 else 0)).re =
      ∑ v ∈ univ.image f, normSq (∑ b ∈ univ.filter (fun b => f b = v), c b) := by
  set S : β → ℂ := fun v => ∑ b ∈ univ.filter (fun b => f b = v), c b
  have h1 : ∀ a, ∑ b, conj (c a) * c b * (if f a = f b then 1 else 0) = conj (c a) * S (f a) := by
    intro a
    simp only [S, mul_ite, mul_one, mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.mul_sum]
    refine sum_congr ?_ fun b _ => rfl
    ext b; simp [eq_comm]
  have h2 : ∑ a, conj (c a) * S (f a) = ∑ v ∈ univ.image f, conj (S v) * S v := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := univ.image f)
      (fun a _ => mem_image_of_mem f (mem_univ a))]
    refine sum_congr rfl fun v _ => ?_
    have : ∀ a ∈ univ.filter (fun a => f a = v), conj (c a) * S (f a) = conj (c a) * S v :=
      fun a ha => by rw [(mem_filter.mp ha).2]
    rw [sum_congr rfl this, ← sum_mul, ← map_sum]
  simp_rw [h1]
  rw [h2, Complex.re_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [Complex.conj_mul']
  norm_cast
  rw [Complex.sq_norm]

/-- **Equivalence kernels are positive.** -/
theorem re_sum_ite_eq_nonneg {ι β : Type*} [Fintype ι] [DecidableEq β] (f : ι → β) (c : ι → ℂ) :
    0 ≤ (∑ a, ∑ b, conj (c a) * c b * (if f a = f b then 1 else 0)).re := by
  rw [re_sum_ite_eq_sum_normSq]
  exact sum_nonneg fun v _ => normSq_nonneg _

/-! ### The absolute value at infinity -/

section Infinity

open scoped Classical

variable {K : Type*} [Field K] (b : ℝ)

/-- The absolute value at infinity `|p|_∞ = b^{deg p}`, `|0|_∞ = 0`. -/
def absInf (p : K[X]) : ℝ := if p = 0 then 0 else b ^ p.natDegree

/-- Multiplication by `X` is conformal with factor `b`. -/
theorem absInf_X_mul (p : K[X]) : absInf b (X * p) = b * absInf b p := by
  unfold absInf
  by_cases hp : p = 0
  · simp [hp]
  · have hXp : X * p ≠ 0 := mul_ne_zero X_ne_zero hp
    rw [if_neg hXp, if_neg hp, natDegree_X_mul hp, pow_succ]
    ring

/-- The weights `w_0 = 1`, `w_k = b^k − b^{k−1}`. -/
def ultraWeight (k : ℕ) : ℝ := if k = 0 then 1 else b ^ k - b ^ (k - 1)

theorem sum_range_ultraWeight (e : ℕ) : ∑ k ∈ range (e + 1), ultraWeight b k = b ^ e := by
  induction e with
  | zero => simp [ultraWeight]
  | succ e ih =>
    rw [Finset.sum_range_succ, ih, ultraWeight, if_neg (Nat.succ_ne_zero e), Nat.add_sub_cancel]
    ring

theorem ultraWeight_nonneg {b : ℝ} (hb : 1 ≤ b) (k : ℕ) : 0 ≤ ultraWeight b k := by
  unfold ultraWeight
  split_ifs with h
  · norm_num
  · have : b ^ (k - 1) ≤ b ^ k := pow_le_pow_right₀ hb (Nat.sub_le k 1)
    linarith

/-- The high part of a polynomial: its coefficients in degrees `≥ k`. -/
def highPart (k : ℕ) (p : K[X]) : ℕ → K := fun j => p.coeff (k + j)

theorem highPart_eq_iff (k : ℕ) (p p' : K[X]) :
    highPart k p = highPart k p' ↔ (p - p').degree < k := by
  rw [degree_lt_iff_coeff_zero]
  constructor
  · intro h m hm
    have := congrFun h (m - k)
    simp only [highPart, Nat.add_sub_cancel' hm] at this
    rw [coeff_sub, this, sub_self]
  · intro h
    funext j
    have := h (k + j) (Nat.le_add_right k j)
    rw [coeff_sub, sub_eq_zero] at this
    exact this

/-- **Ultrametric decomposition** of `|p − p'|_∞`. -/
theorem absInf_sub_eq_sum (p p' : K[X]) {D : ℕ} (hD : (p - p').natDegree ≤ D) :
    absInf b (p - p') =
      ∑ k ∈ range (D + 1), ultraWeight b k * (if highPart k p = highPart k p' then 0 else 1) := by
  classical
  unfold absInf
  by_cases h0 : p - p' = 0
  · rw [if_pos h0]
    refine (sum_eq_zero fun k _ => ?_).symm
    rw [if_pos ((highPart_eq_iff k p p').mpr (by rw [h0, degree_zero]; exact WithBot.bot_lt_coe k)),
      mul_zero]
  · rw [if_neg h0]
    set e := (p - p').natDegree
    have hdeg : (p - p').degree = e := degree_eq_natDegree h0
    have hk : ∀ k, (highPart k p = highPart k p') ↔ e < k := fun k => by
      rw [highPart_eq_iff, hdeg, Nat.cast_lt]
    have hsum : ∑ k ∈ range (D + 1), ultraWeight b k * (if highPart k p = highPart k p' then 0 else 1)
        = ∑ k ∈ range (e + 1), ultraWeight b k := by
      rw [← Finset.sum_range_add_sum_Ico _ (show e + 1 ≤ D + 1 by omega)]
      have hA : ∑ k ∈ range (e + 1), ultraWeight b k *
          (if highPart k p = highPart k p' then 0 else 1) = ∑ k ∈ range (e + 1), ultraWeight b k :=
        sum_congr rfl fun k hk' => by
          rw [if_neg (fun h => by have := (hk k).mp h; simp at hk'; omega), mul_one]
      have hB : ∑ k ∈ Ico (e + 1) (D + 1), ultraWeight b k *
          (if highPart k p = highPart k p' then 0 else 1) = 0 :=
        sum_eq_zero fun k hk' => by
          rw [if_pos ((hk k).mpr (by simp at hk'; omega)), mul_zero]
      rw [hA, hB, add_zero]
    rw [hsum, sum_range_ultraWeight]

/-- The kernel `−|·|_∞` on the additive group of `K[X]`. -/
def negAbsInf (m : Multiplicative K[X]) : ℂ := -((absInf b (Multiplicative.toAdd m) : ℝ) : ℂ)

/-- **`−|·|_∞` is conditionally positive** for `b ≥ 1`. -/
theorem hermQuad_gram_negAbsInf_nonneg {b : ℝ} (hb : 1 ≤ b) {n : ℕ} (x : Fin n → Multiplicative K[X])
    (c : Fin n → ℂ) (hc : ∑ a, c a = 0) : 0 ≤ hermQuad (gram (negAbsInf (K := K) b) x) c := by
  classical
  set p : Fin n → K[X] := fun a => Multiplicative.toAdd (x a)
  set D : ℕ := ∑ a, (p a).natDegree
  have hD : ∀ a a', (p a' - p a).natDegree ≤ D := fun a a' =>
    (natDegree_sub_le _ _).trans (max_le
      (Finset.single_le_sum (f := fun a => (p a).natDegree) (fun _ _ => Nat.zero_le _) (mem_univ a'))
      (Finset.single_le_sum (f := fun a => (p a).natDegree) (fun _ _ => Nat.zero_le _) (mem_univ a)))
  set ρ : Fin n → Fin n → ℝ := fun a a' => (conj (c a) * c a').re
  have hmass : ∑ a, ∑ a', ρ a a' = 0 := by
    simp only [ρ, ← Complex.re_sum]
    rw [← sum_mul_sum, ← map_sum, hc, map_zero, zero_mul, Complex.zero_re]
  have hform : hermQuad (gram (negAbsInf b) x) c =
      ∑ k ∈ range (D + 1), ultraWeight b k *
        (∑ a, ∑ a', conj (c a) * c a' * (if highPart k (p a) = highPart k (p a') then 1 else 0)).re := by
    rw [hermQuad_gram]
    have hent : ∀ a a', negAbsInf b ((x a)⁻¹ * x a') = -((absInf b (p a' - p a) : ℝ) : ℂ) := by
      intro a a'; simp [negAbsInf, p, toAdd_mul, toAdd_inv, neg_add_eq_sub]
    simp_rw [hent, absInf_sub_eq_sum b _ _ (hD _ _)]
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    have e : ∀ a a', (conj (c a) * -((∑ k ∈ range (D + 1), ultraWeight b k *
        (if highPart k (p a') = highPart k (p a) then 0 else 1) : ℝ) : ℂ) * c a').re =
        ∑ k ∈ range (D + 1), ultraWeight b k *
          ((if highPart k (p a) = highPart k (p a') then (1 : ℝ) else 0) * ρ a a' - ρ a a') := by
      intro a a'
      rw [show conj (c a) * -((∑ k ∈ range (D + 1), ultraWeight b k *
          (if highPart k (p a') = highPart k (p a) then 0 else 1) : ℝ) : ℂ) * c a' =
          ((-(∑ k ∈ range (D + 1), ultraWeight b k *
            (if highPart k (p a') = highPart k (p a) then 0 else 1)) : ℝ) : ℂ) * (conj (c a) * c a')
          by push_cast; ring, Complex.re_ofReal_mul, neg_mul, sum_mul, ← sum_neg_distrib]
      refine sum_congr rfl fun k _ => ?_
      simp only [ρ, eq_comm (a := highPart k (p a'))]
      split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (univ : Finset (Fin n))) (t := range (D + 1))]
    refine sum_congr rfl fun k _ => ?_
    simp only [← mul_sum, sum_sub_distrib]
    congr 1
    have h2 : ∑ a, ∑ a', ρ a' a = 0 := by rw [Finset.sum_comm]; exact hmass
    rw [h2, sub_zero, Finset.sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
    simp only [ρ]
    split_ifs <;> simp
  rw [hform]
  exact sum_nonneg fun k _ =>
    mul_nonneg (ultraWeight_nonneg hb k) (re_sum_ite_eq_nonneg (fun a => highPart k (p a)) c)

/-- **`−|·|_∞` has exactly one negative square** for `b ≥ 1`. -/
theorem negIndex_negAbsInf {b : ℝ} (hb : 1 ≤ b) : negIndex (negAbsInf (K := K) b) = 1 := by
  refine le_antisymm ?_ ?_
  · have hpol : polarIndex (negAbsInf (K := K) b) = 0 := by
      refine nonpos_iff_eq_zero.mp (iSup₂_le fun n x => ?_)
      rw [negIndexOn_eq_zero_of_nonneg fun c hc => hermQuad_gram_negAbsInf_nonneg hb x c hc]
      rfl
    simpa [hpol] using negIndex_le_polarIndex_add_one (negAbsInf (K := K) b)
  · have hneg : hermQuad (gram (negAbsInf (K := K) b) ![1, Multiplicative.ofAdd 1]) ![1, 1] < 0 := by
      rw [hermQuad_gram]
      simp [Fin.sum_univ_two, negAbsInf, absInf]
    simpa using card_le_negIndex_of_orthogonal_translates (J := Fin 1) hneg (fun _ => 1)
      fun j j' h => absurd (Subsingleton.elim j j') h

end Infinity

end GaloisForLFunctions.AdelicKreinGeometry
