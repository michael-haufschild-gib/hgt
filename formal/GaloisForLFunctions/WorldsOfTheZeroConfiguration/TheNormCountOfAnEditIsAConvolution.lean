import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedPrimeEdits

/-!
# The norm count of an edit is a convolution

Let `S`, `T` be sets of integers and `B = (ℙ ∖ S) ⊕ (ℙ ∩ T)` the system with the primes of `S`
deleted and a second copy of the primes of `T` (`sumSystem (keptPrimeSystem S)
(keptPrimeSystem Tᶜ)`); the system of an edit is the case `S = minusSet e`, `T = plusSet e`.
Write `1_S` for the indicator of the integers without prime factor in `S` (`freeFn S`) and `μ_S`
for the Möbius function restricted to the integers composed of primes of `S` (`mobFn S`).

* **Norm count** (`intCount_eq`).  The number of integers of `B` of norm `n` is
  `(1_S * 1_{Tᶜ})(n)`.
* **Twin coefficients** (`normCount_eq_sum_divisors`).  `1_S * 1_{Tᶜ} = 1 * u` with
  `u = μ_S * 1_{Tᶜ}`, the coefficients of `ζ_B / ζ`.
* **Deleted primes** (`normCount_eq_zero`).  A prime of `S ∖ T` divides no norm.
* **Mass of the twin coefficients** (`sum_abs_twinCoeff_le`).  If the primes of `S` and of `T`
  are summable at the exponent `θ > 0`, then `Σ_{d ≤ y} |u(d)| ≤ K y^θ`.
* **Count** (`sum_intCount_eq_countBall`, `sum_normCount_eq_countBall`).  The partial sums of the
  norm multiplicities are the count: `Σ_{n ≤ x} (1_S * 1_{Tᶜ})(n) = N_B(x)`.
* **Positive density** (`density_pos`).  If `N_B(x) = A x + O(x^β)`, `β < 1`, and the primes of
  `S` are summable at an exponent below `1`, then `A > 0`: putting the primes of `S` back gives a
  system that represents every integer, and thin additions keep the count rate.
-/

open Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.NormCount

open ThinAdditions TwoSidedEdits

/-! ## The arithmetic functions of a set of primes -/

theorem mobSet_zero (S : Set ℕ) : mobSet S 0 = 0 := by simp [mobSet, sOnly]

/-- The indicator of the integers without prime factor in `S`. -/
def freeFn (S : Set ℕ) : ArithmeticFunction ℝ := ⟨sFreeR S, sFreeR_zero S⟩

/-- The Möbius function on the integers composed of primes of `S`. -/
def mobFn (S : Set ℕ) : ArithmeticFunction ℝ := ⟨mobSet S, mobSet_zero S⟩

theorem freeFn_apply (S : Set ℕ) (n : ℕ) : freeFn S n = sFreeR S n := rfl

theorem mobFn_apply (S : Set ℕ) (n : ℕ) : mobFn S n = mobSet S n := rfl

theorem freeFn_nonneg (S : Set ℕ) (n : ℕ) : 0 ≤ freeFn S n := sFreeR_nonneg S n

/-- `1_S = 1 * μ_S`. -/
theorem freeFn_eq (S : Set ℕ) :
    freeFn S = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * mobFn S := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ArithmeticFunction.coe_zeta_mul_apply]
    exact sFreeR_eq_sum_divisors_mobSet S hn

theorem sFreeR_eq_zero_of_dvd {S : Set ℕ} {p m : ℕ} (hp : p.Prime) (hS : p ∈ S) (hpm : p ∣ m) :
    sFreeR S m = 0 := by
  classical
  unfold sFreeR
  rw [if_neg]
  rintro ⟨hm0, hfree⟩
  exact hfree p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm0⟩) hS

theorem abs_mobSet_le (S : Set ℕ) (m : ℕ) : |mobSet S m| ≤ sFreeR Sᶜ m := by
  classical
  unfold mobSet
  split_ifs with h
  · have hfree : SFree Sᶜ m := ⟨h.1, fun p hp hc => hc (h.2 p hp)⟩
    unfold sFreeR
    rw [if_pos hfree]
    have h1 := ArithmeticFunction.abs_moebius_le_one (n := m)
    exact_mod_cast h1
  · rw [abs_zero]
    exact sFreeR_nonneg _ _

/-! ## The norm count and the twin coefficients -/

/-- The number of integers of norm `n` in `(ℙ ∖ S) ⊕ (ℙ ∩ T)`. -/
theorem intCount_eq (S T : Set ℕ) (n : ℕ) :
    (SumProductArithmeticOfTheLogarithm.intCount
      (sumSystem (keptPrimeSystem S) (keptPrimeSystem Tᶜ))
      (hasIntegerNorms_sumSystem (hasIntegerNorms_keptPrimeSystem S)
        (hasIntegerNorms_keptPrimeSystem Tᶜ)) n : ℝ) = (freeFn S * freeFn Tᶜ) n := by
  rw [intCount_sumSystem (hasIntegerNorms_keptPrimeSystem S) (hasIntegerNorms_keptPrimeSystem Tᶜ)
    (isDiscrete_keptPrimeSystem S) (isDiscrete_keptPrimeSystem Tᶜ),
    ArithmeticFunction.mul_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.cast_mul, intCount_keptPrimeSystem, intCount_keptPrimeSystem, freeFn_apply,
    freeFn_apply]

theorem normCount_nonneg (S T : Set ℕ) (n : ℕ) : 0 ≤ (freeFn S * freeFn Tᶜ) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (freeFn_nonneg _ _) (freeFn_nonneg _ _)

/-- **Twin coefficients.**  The norm count is the divisor sum of `μ_S * 1_{Tᶜ}`. -/
theorem normCount_eq_sum_divisors (S T : Set ℕ) (n : ℕ) :
    (freeFn S * freeFn Tᶜ) n = ∑ d ∈ n.divisors, (mobFn S * freeFn Tᶜ) d := by
  rw [freeFn_eq S, mul_assoc, ArithmeticFunction.coe_zeta_mul_apply]

/-- **A prime of `S ∖ T` divides no norm.** -/
theorem normCount_eq_zero {S T : Set ℕ} {p : ℕ} (hp : p.Prime) (hS : p ∈ S) (hT : p ∉ T)
    {n : ℕ} (hpn : p ∣ n) : (freeFn S * freeFn Tᶜ) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  obtain ⟨hx1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hdiv : p ∣ x.1 * x.2 := hx1 ▸ hpn
  rcases (Nat.Prime.dvd_mul hp).mp hdiv with h | h
  · rw [freeFn_apply, sFreeR_eq_zero_of_dvd hp hS h, zero_mul]
  · rw [freeFn_apply, freeFn_apply, sFreeR_eq_zero_of_dvd hp (show p ∈ Tᶜ from hT) h, mul_zero]

/-- The norm count dominates the indicator of the integers without prime factor in `S`. -/
theorem free_le_normCount (S T : Set ℕ) (m : ℕ) : sFreeR S m ≤ (freeFn S * freeFn Tᶜ) m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sFreeR_zero]
  · rw [ArithmeticFunction.mul_apply]
    have hmem : (m, 1) ∈ m.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one m, hm⟩
    refine le_trans ?_ (Finset.single_le_sum
      (fun x _ => mul_nonneg (freeFn_nonneg S x.1) (freeFn_nonneg Tᶜ x.2)) hmem)
    rw [freeFn_apply, freeFn_apply, sFreeR_one, mul_one]

/-! ## The mass of a convolution -/

/-- Rankin's bound for a convolution of nonnegative functions: the pairs `(m, j)` with
`m j ≤ y` weigh at most `y^θ (m j)^{−θ}`. -/
theorem sum_Ioc_mul_le {F G : ArithmeticFunction ℝ} (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n)
    {θ : ℝ} (hθ : 0 ≤ θ) (y : ℕ) :
    ∑ d ∈ Ioc 0 y, (F * G) d ≤
      (y : ℝ) ^ θ * ((∑ m ∈ Ioc 0 y, F m * (m : ℝ) ^ (-θ)) *
        ∑ j ∈ Ioc 0 y, G j * (j : ℝ) ^ (-θ)) := by
  classical
  have hterm : ∀ d ∈ Ioc 0 y, (F * G) d ≤
      ∑ x ∈ Ioc 0 y ×ˢ Ioc 0 y, if x.1 * x.2 = d then
        (y : ℝ) ^ θ * ((F x.1 * (x.1 : ℝ) ^ (-θ)) * (G x.2 * (x.2 : ℝ) ^ (-θ))) else 0 := by
    intro d hd
    obtain ⟨hd0, hdy⟩ := mem_Ioc.mp hd
    have hset : d.divisorsAntidiagonal =
        (Ioc 0 y ×ˢ Ioc 0 y).filter (fun x => x.1 * x.2 = d) := by
      ext x
      simp only [Nat.mem_divisorsAntidiagonal, mem_filter, mem_product, mem_Ioc]
      constructor
      · rintro ⟨hx, -⟩
        have h1 : 0 < x.1 := Nat.pos_of_ne_zero fun h0 => by
          rw [h0, zero_mul] at hx
          omega
        have h2 : 0 < x.2 := Nat.pos_of_ne_zero fun h0 => by
          rw [h0, mul_zero] at hx
          omega
        exact ⟨⟨⟨h1, (Nat.le_mul_of_pos_right _ h2).trans (hx.le.trans hdy)⟩, h2,
          (Nat.le_mul_of_pos_left _ h1).trans (hx.le.trans hdy)⟩, hx⟩
      · rintro ⟨-, hx⟩
        exact ⟨hx, by omega⟩
    rw [ArithmeticFunction.mul_apply, ← Finset.sum_filter, hset]
    refine Finset.sum_le_sum fun x hx => ?_
    obtain ⟨hxP, hxd⟩ := mem_filter.mp hx
    obtain ⟨hx1, hx2⟩ := mem_product.mp hxP
    have hm0 : (0 : ℝ) < x.1 := by exact_mod_cast (mem_Ioc.mp hx1).1
    have hj0 : (0 : ℝ) < x.2 := by exact_mod_cast (mem_Ioc.mp hx2).1
    have hmj : (0 : ℝ) < (x.1 : ℝ) * (x.2 : ℝ) := mul_pos hm0 hj0
    have hle : ((x.1 : ℝ) * (x.2 : ℝ)) ^ θ ≤ (y : ℝ) ^ θ :=
      Real.rpow_le_rpow hmj.le (by exact_mod_cast hxd.le.trans hdy) hθ
    have hone : 1 ≤ (y : ℝ) ^ θ * ((x.1 : ℝ) ^ (-θ) * (x.2 : ℝ) ^ (-θ)) := by
      rw [← Real.mul_rpow hm0.le hj0.le, Real.rpow_neg hmj.le, ← div_eq_mul_inv,
        one_le_div (Real.rpow_pos_of_pos hmj _)]
      exact hle
    have hFG : 0 ≤ F x.1 * G x.2 := mul_nonneg (hF _) (hG _)
    calc F x.1 * G x.2 = F x.1 * G x.2 * 1 := (mul_one _).symm
      _ ≤ F x.1 * G x.2 * ((y : ℝ) ^ θ * ((x.1 : ℝ) ^ (-θ) * (x.2 : ℝ) ^ (-θ))) :=
          mul_le_mul_of_nonneg_left hone hFG
      _ = (y : ℝ) ^ θ * ((F x.1 * (x.1 : ℝ) ^ (-θ)) * (G x.2 * (x.2 : ℝ) ^ (-θ))) := by ring
  have hnn : ∀ x : ℕ × ℕ,
      0 ≤ (y : ℝ) ^ θ * ((F x.1 * (x.1 : ℝ) ^ (-θ)) * (G x.2 * (x.2 : ℝ) ^ (-θ))) := fun x =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (mul_nonneg (hF _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (mul_nonneg (hG _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  calc ∑ d ∈ Ioc 0 y, (F * G) d
      ≤ ∑ d ∈ Ioc 0 y, ∑ x ∈ Ioc 0 y ×ˢ Ioc 0 y, if x.1 * x.2 = d then
          (y : ℝ) ^ θ * ((F x.1 * (x.1 : ℝ) ^ (-θ)) * (G x.2 * (x.2 : ℝ) ^ (-θ))) else 0 :=
        Finset.sum_le_sum hterm
    _ = ∑ x ∈ Ioc 0 y ×ˢ Ioc 0 y, if x.1 * x.2 ∈ Ioc 0 y then
          (y : ℝ) ^ θ * ((F x.1 * (x.1 : ℝ) ^ (-θ)) * (G x.2 * (x.2 : ℝ) ^ (-θ))) else 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_ite_eq]
    _ ≤ ∑ x ∈ Ioc 0 y ×ˢ Ioc 0 y,
          (y : ℝ) ^ θ * ((F x.1 * (x.1 : ℝ) ^ (-θ)) * (G x.2 * (x.2 : ℝ) ^ (-θ))) :=
        Finset.sum_le_sum fun x _ => by
          split_ifs
          exacts [le_rfl, hnn x]
    _ = (y : ℝ) ^ θ * ((∑ m ∈ Ioc 0 y, F m * (m : ℝ) ^ (-θ)) *
          ∑ j ∈ Ioc 0 y, G j * (j : ℝ) ^ (-θ)) := by
        rw [Finset.sum_product, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]

/-- The integers composed of a thin set of primes, summed below `y`. -/
theorem sum_Ioc_free_compl_le {T : Set ℕ} {θ : ℝ} (hθ : 0 < θ)
    (hT : Summable fun p : ℕ => T.indicator (fun n => (n : ℝ) ^ (-θ)) p) (y : ℕ) :
    ∑ j ∈ Ioc 0 y, freeFn Tᶜ j * (j : ℝ) ^ (-θ) ≤
      ∑' j : ℕ, sFreeR Tᶜ j * (j : ℝ) ^ (-θ) :=
  (summable_sFreeR_compl_rpow hθ hT).sum_le_tsum _ fun _ _ =>
    mul_nonneg (sFreeR_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **Mass of the twin coefficients.** -/
theorem sum_abs_twinCoeff_le {S T : Set ℕ} {θ : ℝ} (hθ : 0 < θ)
    (hS : Summable fun p : ℕ => S.indicator (fun n => (n : ℝ) ^ (-θ)) p)
    (hT : Summable fun p : ℕ => T.indicator (fun n => (n : ℝ) ^ (-θ)) p) (y : ℕ) :
    ∑ d ∈ Ioc 0 y, |(mobFn S * freeFn Tᶜ) d| ≤
      (∑' j : ℕ, sFreeR Sᶜ j * (j : ℝ) ^ (-θ)) * (∑' j : ℕ, sFreeR Tᶜ j * (j : ℝ) ^ (-θ)) *
        (y : ℝ) ^ θ := by
  have hpt : ∀ d : ℕ, |(mobFn S * freeFn Tᶜ) d| ≤ (freeFn Sᶜ * freeFn Tᶜ) d := by
    intro d
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul, abs_of_nonneg (freeFn_nonneg Tᶜ x.2)]
    exact mul_le_mul_of_nonneg_right (abs_mobSet_le S x.1) (freeFn_nonneg _ _)
  have hZS := sum_Ioc_free_compl_le hθ hS y
  have hZT := sum_Ioc_free_compl_le hθ hT y
  have hZT0 : 0 ≤ ∑' j : ℕ, sFreeR Tᶜ j * (j : ℝ) ^ (-θ) :=
    tsum_nonneg fun j => mul_nonneg (sFreeR_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hS0 : 0 ≤ ∑ m ∈ Ioc 0 y, freeFn Sᶜ m * (m : ℝ) ^ (-θ) :=
    Finset.sum_nonneg fun m _ =>
      mul_nonneg (freeFn_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc ∑ d ∈ Ioc 0 y, |(mobFn S * freeFn Tᶜ) d|
      ≤ ∑ d ∈ Ioc 0 y, (freeFn Sᶜ * freeFn Tᶜ) d := Finset.sum_le_sum fun d _ => hpt d
    _ ≤ (y : ℝ) ^ θ * ((∑ m ∈ Ioc 0 y, freeFn Sᶜ m * (m : ℝ) ^ (-θ)) *
          ∑ j ∈ Ioc 0 y, freeFn Tᶜ j * (j : ℝ) ^ (-θ)) :=
        sum_Ioc_mul_le (freeFn_nonneg _) (freeFn_nonneg _) hθ.le y
    _ ≤ (y : ℝ) ^ θ * ((∑' j : ℕ, sFreeR Sᶜ j * (j : ℝ) ^ (-θ)) *
          ∑' j : ℕ, sFreeR Tᶜ j * (j : ℝ) ^ (-θ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hZS hZT (Finset.sum_nonneg fun j _ =>
          mul_nonneg (freeFn_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (hS0.trans hZS)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by ring

/-! ## The count -/

/-- The partial sums of the norm multiplicities of an integer-norm system are its count. -/
theorem sum_intCount_eq_countBall {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hd : B.IsDiscrete) (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (SumProductArithmeticOfTheLogarithm.intCount B h n : ℝ) =
      (B.countBall (x : ℝ) : ℝ) := by
  rw [countBall_eq_sum_intCount h hd (Nat.cast_nonneg x), Nat.floor_natCast, Nat.cast_sum]
  have hsub : Ioc 0 x ⊆ Iic x := fun n hn => mem_Iic.mpr (mem_Ioc.mp hn).2
  refine Finset.sum_subset hsub fun n hn hn' => ?_
  have h0 : n = 0 := by
    by_contra h0
    exact hn' (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0, mem_Iic.mp hn⟩)
  rw [h0, intCount_zero, Nat.cast_zero]

/-- The partial sums of the norm count are the count of the system. -/
theorem sum_normCount_eq_countBall (S T : Set ℕ) (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (freeFn S * freeFn Tᶜ) n =
      ((sumSystem (keptPrimeSystem S) (keptPrimeSystem Tᶜ)).countBall (x : ℝ) : ℝ) := by
  rw [← sum_intCount_eq_countBall (hasIntegerNorms_sumSystem (hasIntegerNorms_keptPrimeSystem S)
    (hasIntegerNorms_keptPrimeSystem Tᶜ)) (isDiscrete_sumSystem (isDiscrete_keptPrimeSystem S)
    (isDiscrete_keptPrimeSystem Tᶜ)) x]
  exact Finset.sum_congr rfl fun n _ => (intCount_eq S T n).symm

/-! ## The density is positive -/

/-- Every positive integer is an integer without prime factor in `S` times an integer composed
of primes of `S`. -/
theorem exists_factorization (S : Set ℕ) :
    ∀ n : ℕ, 1 ≤ n → ∃ m j : ℕ, m * j = n ∧ SFree S m ∧ SFree Sᶜ j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hfree : SFree S n
    · exact ⟨n, 1, mul_one n, hfree, one_ne_zero, by simp⟩
    · have hn0 : n ≠ 0 := by omega
      have hex : ∃ p ∈ n.primeFactors, p ∈ S := by
        by_contra hcon
        exact hfree ⟨hn0, fun p hp hpS => hcon ⟨p, hp, hpS⟩⟩
      obtain ⟨p, hp, hpS⟩ := hex
      obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.mp hp
      obtain ⟨n', rfl⟩ := hpn
      have hn'0 : n' ≠ 0 := by
        rintro rfl
        simp at hn0
      have hlt : n' < p * n' := by
        have := hpp.two_le
        nlinarith [Nat.pos_of_ne_zero hn'0]
      obtain ⟨m, j, hmj, hm, hj⟩ := ih n' hlt (Nat.pos_of_ne_zero hn'0)
      refine ⟨m, p * j, by rw [← hmj]; ring, hm, mul_ne_zero hpp.ne_zero hj.1, ?_⟩
      intro q hq
      rw [Nat.primeFactors_mul hpp.ne_zero hj.1, Finset.mem_union, hpp.primeFactors,
        Finset.mem_singleton] at hq
      rcases hq with rfl | hq
      · exact fun hc => hc hpS
      · exact hj.2 q hq

/-- The system with the primes of `S` put back represents every positive integer. -/
theorem one_le_free_mul_free (S : Set ℕ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ (freeFn S * freeFn Sᶜ) n := by
  classical
  obtain ⟨m, j, hmj, hm, hj⟩ := exists_factorization S n hn
  rw [ArithmeticFunction.mul_apply]
  have hmem : (m, j) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨hmj, by omega⟩
  refine le_trans ?_ (Finset.single_le_sum
    (fun x _ => mul_nonneg (freeFn_nonneg S x.1) (freeFn_nonneg Sᶜ x.2)) hmem)
  rw [freeFn_apply, freeFn_apply]
  unfold sFreeR
  rw [if_pos hm, if_pos hj, mul_one]

/-- The integers composed of a thin set of primes are summable as generalized integers. -/
theorem summable_intNorm_kept_compl {T : Set ℕ} {β : ℝ} (hβ : 0 < β)
    (hT : Summable fun p : ℕ => T.indicator (fun n => (n : ℝ) ^ (-β)) p) :
    Summable fun v : (keptPrimeSystem Tᶜ).Integer =>
      ((keptPrimeSystem Tᶜ).intNorm v) ^ (-β) := by
  have hD := summable_sFreeR_compl_rpow hβ hT
  have hLS : LSeriesSummable (fun n => (SumProductArithmeticOfTheLogarithm.intCount
      (keptPrimeSystem Tᶜ) (hasIntegerNorms_keptPrimeSystem _) n : ℂ)) (β : ℂ) := by
    refine Summable.of_norm (hD.congr fun n => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, norm_zero, sFreeR_zero, zero_mul]
    · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re,
        intCount_keptPrimeSystem, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  exact summable_intNorm_rpow_of_lseriesSummable (hasIntegerNorms_keptPrimeSystem _)
    (isDiscrete_keptPrimeSystem Tᶜ) (σ := β) hLS

/-- **The density of a thin edit is positive.** -/
theorem density_pos {S T : Set ℕ} {A C β θ : ℝ} (hA : 0 ≤ A) (hβ1 : β < 1) (hθ : 0 < θ)
    (hθ1 : θ < 1) (hS : Summable fun p : ℕ => S.indicator (fun n => (n : ℝ) ^ (-θ)) p)
    (hN : ∀ x : ℝ, 1 ≤ x →
      |((sumSystem (keptPrimeSystem S) (keptPrimeSystem Tᶜ)).countBall x : ℝ) - A * x| ≤
        C * x ^ β) : 0 < A := by
  classical
  rcases hA.lt_or_eq with hpos | hzero
  · exact hpos
  exfalso
  have hC : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h
  -- one exponent `η < 1` for the count and for the primes of `S`
  obtain ⟨η, hηβ, hηθ, hη1⟩ : ∃ η : ℝ, β ≤ η ∧ θ ≤ η ∧ η < 1 :=
    ⟨max β θ, le_max_left _ _, le_max_right _ _, max_lt hβ1 hθ1⟩
  have hη0 : 0 < η := lt_of_lt_of_le hθ hηθ
  have hSη : Summable fun p : ℕ => S.indicator (fun n => (n : ℝ) ^ (-η)) p := by
    refine Summable.of_nonneg_of_le
      (fun p => Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) p)
      (fun p => ?_) hS
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      rcases Nat.eq_zero_or_pos p with rfl | hp0
      · rw [Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
      · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp0) (by linarith)
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
  set B : BeurlingSystem := sumSystem (keptPrimeSystem S) (keptPrimeSystem Tᶜ) with hB
  have hBint : HasIntegerNorms B :=
    hasIntegerNorms_sumSystem (hasIntegerNorms_keptPrimeSystem S)
      (hasIntegerNorms_keptPrimeSystem Tᶜ)
  have hBdisc : B.IsDiscrete :=
    isDiscrete_sumSystem (isDiscrete_keptPrimeSystem S) (isDiscrete_keptPrimeSystem Tᶜ)
  have hNη : ∀ y : ℝ, 1 ≤ y → |(B.countBall y : ℝ) - 0 * y| ≤ C * y ^ η := by
    intro y hy
    have h := hN y hy
    rw [← hzero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy hηβ) hC)
  -- putting the primes of `S` back keeps the count rate
  have hZ := summable_intNorm_kept_compl hη0 hSη
  have hup : ∀ x : ℝ, 1 ≤ x →
      ((sumSystem B (keptPrimeSystem Sᶜ)).countBall x : ℝ) ≤
        (C + 0) * (∑' v : (keptPrimeSystem Sᶜ).Integer,
          ((keptPrimeSystem Sᶜ).intNorm v) ^ (-η)) * x ^ η := by
    intro x hx
    have h := sumSystem_count_sub_le hBdisc (isDiscrete_keptPrimeSystem Sᶜ) le_rfl hC hη1.le
      hNη hZ hx
    rw [zero_mul, zero_mul, sub_zero] at h
    exact (le_abs_self _).trans h
  -- and the new system represents every integer
  have hlow : ∀ x : ℕ, (x : ℝ) ≤ ((sumSystem B (keptPrimeSystem Sᶜ)).countBall (x : ℝ) : ℝ) := by
    intro x
    rw [countBall_eq_sum_intCount (hasIntegerNorms_sumSystem hBint
      (hasIntegerNorms_keptPrimeSystem Sᶜ)) (isDiscrete_sumSystem hBdisc
      (isDiscrete_keptPrimeSystem Sᶜ)) (Nat.cast_nonneg x), Nat.floor_natCast, Nat.cast_sum]
    have hsub : Ioc 0 x ⊆ Iic x := fun n hn => mem_Iic.mpr (mem_Ioc.mp hn).2
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _)
    calc (x : ℝ) = ∑ n ∈ Ioc 0 x, (1 : ℝ) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.sub_zero]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := (mem_Ioc.mp hn).1
          rw [intCount_sumSystem hBint (hasIntegerNorms_keptPrimeSystem Sᶜ) hBdisc
            (isDiscrete_keptPrimeSystem Sᶜ), Nat.cast_sum]
          refine (one_le_free_mul_free S hn1).trans ?_
          rw [ArithmeticFunction.mul_apply]
          refine Finset.sum_le_sum fun y _ => ?_
          rw [Nat.cast_mul, intCount_keptPrimeSystem,
            show ((SumProductArithmeticOfTheLogarithm.intCount B hBint y.1 : ℕ) : ℝ) =
              (freeFn S * freeFn Tᶜ) y.1 from intCount_eq S T y.1, freeFn_apply, freeFn_apply]
          exact mul_le_mul_of_nonneg_right (free_le_normCount S T y.1) (sFreeR_nonneg _ _)
  -- a linear lower bound against a bound `O(x^η)`
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (C + 0) * (∑' v : (keptPrimeSystem Sᶜ).Integer,
      ((keptPrimeSystem Sᶜ).intNorm v) ^ (-η)) := ⟨_, rfl⟩
  rw [← hW] at hup
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact mul_nonneg (by linarith) (tsum_nonneg fun v =>
      Real.rpow_nonneg ((keptPrimeSystem Sᶜ).intNorm_pos v).le _)
  have h1η : 0 < 1 - η := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℕ, (W + 1) ^ (1 / (1 - η)) < x := exists_nat_gt _
  have hx0 : (0 : ℝ) < x :=
    lt_of_le_of_lt (Real.rpow_nonneg (by linarith) _) hx
  have hx1 : (1 : ℝ) ≤ x := by
    have : 1 ≤ x := by exact_mod_cast hx0
    exact_mod_cast this
  have hpow : W + 1 ≤ (x : ℝ) ^ (1 - η) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hx.le h1η.le
    rwa [← Real.rpow_mul (by linarith), one_div_mul_cancel h1η.ne', Real.rpow_one] at h
  have hsplit : (x : ℝ) = (x : ℝ) ^ (1 - η) * (x : ℝ) ^ η := by
    rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]
  have hxη : 0 < (x : ℝ) ^ η := Real.rpow_pos_of_pos hx0 _
  have h1 := (hlow x).trans (hup x hx1)
  have h2 : (W + 1) * (x : ℝ) ^ η ≤ (x : ℝ) := by
    calc (W + 1) * (x : ℝ) ^ η ≤ (x : ℝ) ^ (1 - η) * (x : ℝ) ^ η :=
          mul_le_mul_of_nonneg_right hpow hxη.le
      _ = x := hsplit.symm
  nlinarith

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.NormCount
