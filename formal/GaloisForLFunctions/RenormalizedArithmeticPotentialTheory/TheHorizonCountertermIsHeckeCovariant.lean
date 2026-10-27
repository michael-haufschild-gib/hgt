import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsATensorProduct
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheHeckeCocycleOfRenormalization

/-!
# The horizon counterterm is Hecke covariant

Under the Abel radius the Hecke correspondence `[t]` replaces the regulator `r` by `r^t`, and the
counterterm moves by the anomaly `log t` minus the tame different (AIT): no regularization by a
radius is covariant. At the horizon the anomaly cancels exactly, for `[p]` acting on `p`-adic
classes.

The **Hecke shift** `(T_t x)(n) = x(n/t)` on multiples of `t`, `0` elsewhere (`heckeShift`), maps
the orders `≤ N` to the orders `≤ tN`.

* **The prime form is invariant** (`atomicWeilForm_heckeShift`): `P_{tN}(T_t x) = P_N(x)`, by Hecke
  invariance of Weil's kernel (AIT `weilPrimeKernel_mul_left`).
* **`[p]` raises the valuation class by one** (`heckeShift_classPole`):
  `T_p w_j^{(M)} = √p · w_{j+1}^{(pM)}`. The class-wise profile spaces are stable.
* **The class polar functionals shift** (`classPolar_heckeShift_succ`, `classPolar_heckeShift_zero`):
  `ℓ_{j+1}(T_p x) = ℓ_j(x)/√p` and `ℓ_0(T_p x) = 0`.
* **The orbit densities shift by the degree** (`classDensity_succ`): `δ_{j+1} = δ_j/p`, the
  multiplicative form of the anomaly: the dual orbit `O_{p^{J+1−j}}` of the class `j + 1` has `1/p`
  of the points of that of the class `j`.
* **No anomaly** (`tensorCounterterm_heckeShift`, `finitePart_heckeShift`): the tensor counterterm
  `C(x) = Σ_j δ_j^{−1} ℓ_j(x)²` satisfies `C(T_p x) = C(x)`, so the renormalized finite part
  `P − C` is exactly invariant under `[p]`.

So the degree `p = #ker[p]` that appears under the Abel radius as the additive anomaly `log p`
appears at the horizon as the scaling `1/p` of the orbit densities, and is compensated exactly by the
scaling `p^{−1/2}` of the polar functional. Condition (ii) of the report's central conjecture — a
Hecke-covariant finite part — holds at the horizon for `[p]` on the `p`-adic classes, together with
the tensor law of `TheHorizonCountertermIsATensorProduct`.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

/-- The **Hecke shift** `(T_t x)(n) = x(n/t)` on multiples of `t`, `0` elsewhere. -/
def heckeShift (t : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ := if t ∣ n then x (n / t) else 0

/-- Summing a shifted function over the orders `≤ tN` is summing over the orders `≤ N`. -/
theorem sum_Icc_mul_dvd {t : ℕ} (ht : 0 < t) (N : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 (t * N), (if t ∣ n then F (n / t) else 0) = ∑ m ∈ Icc 1 N, F m := by
  rw [← sum_filter, filter_dvd_Icc_eq_image ht, Nat.mul_div_cancel_left N ht,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left ht h]
  exact sum_congr rfl fun m _ => by rw [Nat.mul_div_cancel_left m ht]

/-- **The prime form is Hecke invariant**: `P_{tN}(T_t x) = P_N(x)`. -/
theorem atomicWeilForm_heckeShift {t : ℕ} (ht : 0 < t) (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm (t * N) (heckeShift t x) = atomicWeilForm N x := by
  unfold atomicWeilForm
  have hrow : ∀ a ∈ Icc 1 (t * N), ∑ b ∈ Icc 1 (t * N),
      heckeShift t x a * heckeShift t x b * weilPrimeKernel a b =
      if t ∣ a then ∑ n ∈ Icc 1 N, x (a / t) * x n * weilPrimeKernel (a / t) n else 0 := by
    intro a _
    by_cases ha : t ∣ a
    · rw [if_pos ha, ← sum_Icc_mul_dvd ht N
        (fun n => x (a / t) * x n * weilPrimeKernel (a / t) n)]
      refine sum_congr rfl fun b _ => ?_
      by_cases hb : t ∣ b
      · obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        simp only [heckeShift, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ ht,
          ArithmeticIntersectionTheory.weilPrimeKernel_mul_left ht]
      · simp [heckeShift, hb]
    · rw [if_neg ha]
      simp [heckeShift, ha]
  rw [sum_congr rfl hrow, sum_Icc_mul_dvd ht N
    (fun m => ∑ n ∈ Icc 1 N, x m * x n * weilPrimeKernel m n)]

variable {p : ℕ}

/-- **`[p]` raises the valuation class by one**: `T_p w_j^{(M)} = √p · w_{j+1}^{(pM)}`. -/
theorem heckeShift_classPole (hp : p.Prime) (j M n : ℕ) :
    heckeShift p (classPole p j M) n = Real.sqrt p * classPole p (j + 1) (p * M) n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold heckeShift
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [classPole, truncPole, poleVector]
    obtain ⟨m, rfl⟩ := hpn
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    rw [Nat.mul_div_cancel_left m hp.pos]
    have hv : (p * m).factorization p = m.factorization p + 1 := by
      rw [Nat.factorization_mul hp.ne_zero hm.ne', Finsupp.add_apply, hp.factorization_self]
      ring
    simp only [classPole, truncPole, hv, Nat.add_right_cancel_iff]
    have hle : p * m ≤ p * M ↔ m ≤ M := Nat.mul_le_mul_left_iff hp.pos
    by_cases h1 : m.factorization p = j
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : m ≤ M
      · rw [if_pos h2, if_pos (hle.mpr h2), poleVector, poleVector, Nat.cast_mul,
          Real.sqrt_mul hp0.le]
        have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
        have hm' : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hm)).ne'
        field_simp
      · rw [if_neg h2, if_neg (fun h => h2 (hle.mp h)), mul_zero]
    · rw [if_neg h1, if_neg h1, mul_zero]
  · rw [if_neg hpn]
    have hv : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
    simp [classPole, hv]

/-- The density of the class `j + 1` is `1/p` of that of the class `j`. -/
theorem classDensity_succ (p j : ℕ) : classDensity p (j + 1) = classDensity p j / p := by
  unfold classDensity
  rw [pow_succ, div_div]

/-- **The class polar functionals shift**: `ℓ_{j+1}(T_p x) = ℓ_j(x)/√p` at horizons `pN` and `N`. -/
theorem classPolar_heckeShift_succ (hp : p.Prime) (j N : ℕ) (x : ℕ → ℝ) :
    classPolar p (j + 1) (p * N) (heckeShift p x) = classPolar p j N x / Real.sqrt p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  unfold classPolar
  have hterm : ∀ n ∈ Icc 1 (p * N), (if n.factorization p = j + 1 then
      heckeShift p x n * poleVector n else 0) =
      if p ∣ n then (if (n / p).factorization p = j then
        x (n / p) * poleVector (n / p) / Real.sqrt p else 0) else 0 := by
    intro n hn
    have hn0 : n ≠ 0 := (pos_of_mem_Icc' hn).ne'
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm : m ≠ 0 := fun h => hn0 (by rw [h, mul_zero])
      have hv : (p * m).factorization p = m.factorization p + 1 := by
        rw [Nat.factorization_mul hp.ne_zero hm, Finsupp.add_apply, hp.factorization_self]
        ring
      have hm' : Real.sqrt m ≠ 0 :=
        (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hm)).ne'
      simp only [heckeShift, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hp.pos, hv,
        Nat.add_right_cancel_iff]
      split_ifs
      · rw [poleVector, poleVector, Nat.cast_mul, Real.sqrt_mul hp0.le]
        field_simp
      · rfl
    · have hv : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
      simp [hpn, hv]
  rw [sum_congr rfl hterm, sum_Icc_mul_dvd hp.pos N
    (fun m => if m.factorization p = j then x m * poleVector m / Real.sqrt p else 0), sum_div]
  refine sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

/-- The class `0` is empty on multiples of `p`: `ℓ_0(T_p x) = 0`. -/
theorem classPolar_heckeShift_zero (hp : p.Prime) (N : ℕ) (x : ℕ → ℝ) :
    classPolar p 0 (p * N) (heckeShift p x) = 0 := by
  unfold classPolar heckeShift
  refine sum_eq_zero fun n hn => ?_
  have hn0 : n ≠ 0 := (pos_of_mem_Icc' hn).ne'
  by_cases hpn : p ∣ n
  · have : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn0).mp hpn
    rw [if_neg (by omega)]
  · rw [if_pos (Nat.factorization_eq_zero_of_not_dvd hpn), if_neg hpn, zero_mul]

/-- The **tensor counterterm** `C(x) = Σ_{j ≤ J} δ_j^{−1} ℓ_j(x)²` at horizon `N`. -/
def tensorCounterterm (p J N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ j : Fin (J + 1), classPolar p j N x ^ 2 / classDensity p j

/-- **No anomaly at the horizon**: `C_{J+1}(T_p x)` at horizon `pN` equals `C_J(x)` at horizon `N`. -/
theorem tensorCounterterm_heckeShift (hp : p.Prime) (J N : ℕ) (x : ℕ → ℝ) :
    tensorCounterterm p (J + 1) (p * N) (heckeShift p x) = tensorCounterterm p J N x := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold tensorCounterterm
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, classPolar_heckeShift_zero hp, classPolar_heckeShift_succ hp,
    classDensity_succ]
  have hδ : ∀ j : ℕ, classDensity p j ≠ 0 := fun j => (classDensity_pos hp j).ne'
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  rw [show (0 : ℝ) ^ 2 / classDensity p 0 = 0 by simp, zero_add]
  refine sum_congr rfl fun j _ => ?_
  rw [div_pow, hs]
  field_simp

/-- **The renormalized finite part is Hecke covariant**: `P − C` is invariant under `[p]`, the
horizon moving from `N` to `pN` and the class range from `J` to `J + 1`. -/
theorem finitePart_heckeShift (hp : p.Prime) (J N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm (p * N) (heckeShift p x) - tensorCounterterm p (J + 1) (p * N) (heckeShift p x) =
      atomicWeilForm N x - tensorCounterterm p J N x := by
  rw [atomicWeilForm_heckeShift hp.pos, tensorCounterterm_heckeShift hp]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
