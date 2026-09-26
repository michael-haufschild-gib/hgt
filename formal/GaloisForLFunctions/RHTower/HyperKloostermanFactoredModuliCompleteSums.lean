import GaloisForLFunctions.RHTower.HyperKloostermanPrimeSquareStationaryPhase
import GaloisForLFunctions.RHTower.RootOfUnityIntervalCompletion
import GaloisForLFunctions.RHTower.EstermannKloostermanSaving

/-!
# Complete-sum bounds for moduli averages of `Kl₃` over moduli `p s²`

Let `K*(y; n) = Kl₃(y; n)` for units `y` and `0` otherwise. For a prime `p ≠ 2`, a prime `s`, and
units `u` mod `p`, `v` mod `s²`, let `c(m) = K*(um; p) K*(vm; s²)`. This is `Kl₃(am; ps²)` after
twisted multiplicativity.

* **Prime factor.** For every frequency `h`, `Σ_{x unit} Kl₃(ux; p) e(-hx/p) = p S(1, ·; p) - 1`,
  or `-1` when `h = 0`. Weil's bound gives `≤ 2p√p + 1` (`norm_zmodCoeff_klUnit_le`, via
  `RHTower.norm_kloostermanSum_le_weil`). Parseval then gives `Σ_x |K*(ux; p)|² ≤ (2p√p + 1)²`
  (`sum_norm_sq_klUnit_le`).
* **Prime-square factor.** `B(y) = K*(v₁y; s²) conj K*(v₂y; s²)` has `|B̂(h)| ≤ 6s⁵` for `s ∤ h` and
  `|B̂(h)| ≤ 9s⁶` always. These come from the stationary-phase bounds of
  `HyperKloostermanPrimeSquareStationaryPhase`.
* **Diagonal.** `Σ_{m ≤ L} |c(m)|² ≤ 9s⁴ (L/p + 1)(2p√p + 1)²` (`diag_le`).
* **Off-diagonal.** For distinct primes `p₁, p₂ ≠ s`, the correlation `Σ_{m ≤ L} c₁(m) conj c₂(m)` is
  completed modulo `p₁p₂s²` (`RootOfUnityCompletion.norm_sum_Icc_triple_le`). It is bounded by
  `(L/(p₁p₂s²))·9s⁶ + A₁A₂(6s⁵(1 + log p₁p₂s²) + 9s⁵(1 + log p₁p₂s))` with `A_i = 2p_i√p_i + 1`
  (`offdiag_le`).

Every input is Weil's bound for `Kl₂` or elementary; Deligne's theorem is not used.
-/

open Finset

namespace GaloisForLFunctions.RHTower.HyperKloostermanFactoredModuli

open GaloisForLFunctions.RHTower.HyperKloosterman
open GaloisForLFunctions.RHTower.HyperKloostermanSecondMoment
open GaloisForLFunctions.RHTower.HyperKloostermanPrimeSquare
open GaloisForLFunctions.RHTower.RootOfUnityCompletion

noncomputable section

/-- `Kl₃` restricted to unit arguments: `K*(y; n) = Kl₃(y; n)` for a unit `y`, and `0` otherwise. -/
def klUnit (n : ℕ) [NeZero n] (y : ZMod n) : ℂ :=
  if IsUnit y then hyperKloosterman ZMod.stdAddChar 3 y else 0

/-- An interval sum of a nonnegative `n`-periodic function is at most `(L/n + 1)` complete
periods. -/
theorem sum_Icc_periodic_le {n : ℕ} [NeZero n] (g : ZMod n → ℝ) (hg : ∀ x, 0 ≤ g x) (L : ℕ) :
    ∑ m ∈ Finset.Icc 1 L, g (m : ZMod n) ≤ ((L : ℝ) / n + 1) * ∑ x : ZMod n, g x := by
  classical
  rw [← Finset.sum_fiberwise (Finset.Icc 1 L) (fun m : ℕ => (m : ZMod n)) (fun m => g (m : ZMod n)),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hc : ∑ m ∈ (Finset.Icc 1 L).filter (fun m : ℕ => (m : ZMod n) = x), g (m : ZMod n) =
      ((Finset.Icc 1 L).filter (fun m : ℕ => (m : ZMod n) = x)).card * g x := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl fun m hm => by rw [(Finset.mem_filter.1 hm).2]
  rw [hc]
  refine mul_le_mul_of_nonneg_right ?_ (hg x)
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcard : ((Finset.Icc 1 L).filter (fun m : ℕ => (m : ZMod n) = x)).card ≤ L / n + 1 := by
    calc ((Finset.Icc 1 L).filter (fun m : ℕ => (m : ZMod n) = x)).card
        ≤ (Finset.range (L / n + 1)).card := by
          refine Finset.card_le_card_of_injOn (fun m => m / n) ?_ ?_
          · intro m hm
            simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hm
            simp only [Finset.coe_range, Set.mem_Iio]
            exact Nat.lt_succ_of_le (Nat.div_le_div_right hm.1.2)
          · intro m hm m' hm' he
            simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hm hm'
            have hmod : m % n = m' % n :=
              (ZMod.natCast_eq_natCast_iff' _ _ _).1 (hm.2.trans hm'.2.symm)
            simp only at he
            rw [← Nat.div_add_mod m n, ← Nat.div_add_mod m' n, he, hmod]
      _ = L / n + 1 := Finset.card_range _
  calc (((Finset.Icc 1 L).filter (fun m : ℕ => (m : ZMod n) = x)).card : ℝ)
      ≤ ((L / n + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (L : ℝ) / n + 1 := by
        push_cast
        gcongr
        exact Nat.cast_div_le

/-- **Parseval on `ZMod n`:** `Σ_h |Â(h)|² = n Σ_x |A(x)|²`. -/
theorem sum_norm_sq_zmodCoeff {n : ℕ} [NeZero n] (A : ZMod n → ℂ) :
    ∑ h : ZMod n, ‖zmodCoeff A h‖ ^ 2 = n * ∑ x : ZMod n, ‖A x‖ ^ 2 := by
  have key : ∑ h : ZMod n, zmodCoeff A h * star (zmodCoeff A h) =
      (n : ℂ) * ∑ x : ZMod n, A x * star (A x) := by
    simp only [zmodCoeff, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    have hch : ∀ (h x y : ZMod n), ZMod.stdAddChar (-(h * x)) * star (ZMod.stdAddChar (-(h * y))) =
        ZMod.stdAddChar (h * (y - x)) := by
      intro h x y
      rw [show ∀ z : ℂ, star z = starRingEnd ℂ z from fun _ => rfl, ← AddChar.map_neg_eq_conj,
        ← AddChar.map_add_eq_mul]
      congr 1; ring
    calc ∑ h : ZMod n, ∑ y : ZMod n, ∑ x : ZMod n,
          A x * ZMod.stdAddChar (-(h * x)) * (star (A y) * star (ZMod.stdAddChar (-(h * y))))
        = ∑ x : ZMod n, ∑ y : ZMod n, A x * star (A y) *
            ∑ h : ZMod n, ZMod.stdAddChar (h * (y - x)) := by
          rw [sum_comm_three_rev]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [← hch]; ring
      _ = ∑ x : ZMod n, (n : ℂ) * (A x * star (A x)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp_rw [sum_stdAddChar_mul, sub_eq_zero, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq']
          simp only [Finset.mem_univ, if_true]
          ring
  have hre : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [show star z = starRingEnd ℂ z from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hre] at key
  exact_mod_cast key

/-- The Fourier coefficient of a conjugated function. -/
theorem zmodCoeff_star {n : ℕ} [NeZero n] (A : ZMod n → ℂ) (h : ZMod n) :
    zmodCoeff (fun x => star (A x)) h = star (zmodCoeff A (-h)) := by
  simp only [zmodCoeff, star_sum, star_mul']
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  rw [show ∀ z : ℂ, star z = starRingEnd ℂ z from fun _ => rfl, ← AddChar.map_neg_eq_conj]
  congr 1; ring

section PrimePart

variable {p : ℕ} [hp : Fact p.Prime]

/-- The sum of the standard character over the units of a prime field is `-1`. -/
theorem sum_units_stdAddChar_prime : ∑ a : (ZMod p)ˣ, ZMod.stdAddChar (a : ZMod p) = -1 := by
  have h := sum_stdAddChar_mul (n := p) (1 : ZMod p)
  simp only [mul_one, one_ne_zero, if_false] at h
  rw [sum_units_eq]
  have hsplit : ∑ a : ZMod p, ZMod.stdAddChar a =
      ZMod.stdAddChar (0 : ZMod p) + ∑ a ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar a :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  rw [h, AddChar.map_zero_eq_one] at hsplit
  have : ∑ a : ZMod p, (if IsUnit a then ZMod.stdAddChar a else 0) =
      ∑ a ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar a := by
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp [isUnit_iff_ne_zero]
  rw [this]
  linear_combination -hsplit

/-- The unit-restricted Ramanujan sum modulo a prime: `Σ_{w unit} e(wc) = p[c = 0] - 1`. -/
theorem sum_units_stdAddChar_mul (c : ZMod p) :
    ∑ w : (ZMod p)ˣ, ZMod.stdAddChar ((w : ZMod p) * c) = (if c = 0 then (p : ℂ) else 0) - 1 := by
  have h := sum_stdAddChar_mul (n := p) c
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)), zero_mul,
    AddChar.map_zero_eq_one] at h
  rw [sum_units_eq (f := fun w : ZMod p => ZMod.stdAddChar (w * c))]
  have : ∑ a : ZMod p, (if IsUnit a then ZMod.stdAddChar (a * c) else 0) =
      ∑ a ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (a * c) := by
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp [isUnit_iff_ne_zero]
  rw [this]
  linear_combination h

/-- The unit-restricted Fourier transform of `Kl₃` modulo a prime:
`Σ_{w unit} Kl₃(w; p) e(βw/p) = p Σ_{a,b : a⁻¹b⁻¹ = -β} e((a+b)/p) - 1`. -/
theorem sum_units_hyperKloosterman_mul (β : ZMod p) :
    ∑ w : (ZMod p)ˣ, hyperKloosterman ZMod.stdAddChar 3 (w : ZMod p) *
        ZMod.stdAddChar (β * (w : ZMod p)) =
      (p : ℂ) * (∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ,
        if ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) = -β then
          ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) else 0) - 1 := by
  simp_rw [hyperKloosterman_three_units, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ a : (ZMod p)ˣ, ∑ w : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ,
      ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p) + (w : ZMod p) * ((a⁻¹ : (ZMod p)ˣ) : ZMod p) *
        ((b⁻¹ : (ZMod p)ˣ) : ZMod p)) * ZMod.stdAddChar (β * (w : ZMod p)) =
      ∑ b : (ZMod p)ˣ, ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) *
        ((if ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) + β = 0 then (p : ℂ) else 0)
          - 1) := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sum_units_stdAddChar_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hinner]
  have hsq : ∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ, ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) = 1 := by
    simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul,
      sum_units_stdAddChar_prime]
    norm_num
  have hterm : ∀ a b : (ZMod p)ˣ, ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) *
      ((if ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) + β = 0 then (p : ℂ) else 0)
        - 1) = (p : ℂ) * (if ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) = -β then
          ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) else 0) -
        ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) := by
    intro a b
    have hiff : (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) + β = 0) ↔
        (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) = -β) := by
      constructor <;> intro h <;> linear_combination h
    by_cases hc : ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) = -β
    · rw [if_pos (hiff.2 hc), if_pos hc]; ring
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]; ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hsq]

/-- **Twisted complete sums of `Kl₃` modulo a prime.** For a unit `u` and any frequency `h`,
`|Σ_{x unit} Kl₃(ux; p) e(-hx/p)| ≤ 2p√p + 1`. The sum equals `p S(1, ·; p) - 1`, or `-1` when
`h = 0`. -/
theorem norm_zmodCoeff_klUnit_le (hp2 : p ≠ 2) (u : (ZMod p)ˣ) (h : ZMod p) :
    ‖zmodCoeff (fun x : ZMod p => klUnit p ((u : ZMod p) * x)) h‖ ≤
      2 * p * Real.sqrt p + 1 := by
  classical
  set β : ZMod p := -h * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) with hβ
  have hre : zmodCoeff (fun x : ZMod p => klUnit p ((u : ZMod p) * x)) h =
      ∑ w : (ZMod p)ˣ, hyperKloosterman ZMod.stdAddChar 3 (w : ZMod p) *
        ZMod.stdAddChar (β * (w : ZMod p)) := by
    unfold zmodCoeff klUnit
    have hU : ∀ y : ZMod p, IsUnit ((u : ZMod p) * y) ↔ IsUnit y := fun y =>
      ⟨fun hy => isUnit_of_mul_isUnit_right hy, fun hy => (Units.isUnit u).mul hy⟩
    simp_rw [hU, ite_mul, zero_mul]
    rw [← sum_units_eq (f := fun y : ZMod p => hyperKloosterman ZMod.stdAddChar 3
      ((u : ZMod p) * y) * ZMod.stdAddChar (-(h * y)))]
    refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun y => ?_)
    simp only [Equiv.coe_mulLeft, Units.val_mul, hβ]
    congr 2
    have hu : ((u⁻¹ : (ZMod p)ˣ) : ZMod p) * (u : ZMod p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    linear_combination (h * (y : ZMod p)) * hu
  rw [hre, sum_units_hyperKloosterman_mul]
  have hK : ‖∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ,
      (if ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) = -β then
        ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) else 0)‖ ≤ 2 * Real.sqrt p := by
    by_cases hβ0 : β = 0
    · have : ∀ a b : (ZMod p)ˣ, ¬ (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) =
          -β) := by
        intro a b hab
        rw [hβ0, neg_zero] at hab
        exact (Units.isUnit (a⁻¹ * b⁻¹)).ne_zero (by rw [Units.val_mul]; exact hab)
      simp only [this, if_false, Finset.sum_const_zero, norm_zero]
      positivity
    · set c : (ZMod p)ˣ := Units.mk0 (-β) (neg_ne_zero.2 hβ0) with hc
      have hsum : ∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ,
          (if ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) = -β then
            ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) else 0) =
          RHTower.Sieve.kloostermanSum p 1 ((c⁻¹ : (ZMod p)ˣ) : ZMod p) := by
        unfold RHTower.Sieve.kloostermanSum RHTower.Sieve.kloostermanPhase
        refine Finset.sum_congr rfl fun a _ => ?_
        have hiff : ∀ b : (ZMod p)ˣ, (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) =
            -β) ↔ b = (c * a)⁻¹ := by
          intro b
          rw [← Units.val_mul, show -β = ((c : (ZMod p)ˣ) : ZMod p) from rfl, Units.val_inj]
          constructor
          · intro hb
            rw [← hb, mul_right_comm, inv_mul_cancel, one_mul, inv_inv]
          · intro hb
            rw [hb, inv_inv, mul_comm c a, inv_mul_cancel_left]
        simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]
        congr 1
        rw [mul_inv_rev, Units.val_mul, mul_comm]
      rw [hsum]
      exact RHTower.norm_kloostermanSum_le_weil p hp2 1 (Units.ne_zero _)
  calc ‖(p : ℂ) * (∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ,
        if ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) = -β then
          ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) else 0) - 1‖
      ≤ ‖(p : ℂ) * (∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ,
        if ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) = -β then
          ZMod.stdAddChar ((a : ZMod p) + (b : ZMod p)) else 0)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ p * (2 * Real.sqrt p) + 1 := by
        rw [norm_mul, Complex.norm_natCast, norm_one]
        gcongr
    _ = 2 * p * Real.sqrt p + 1 := by ring

/-- At the zero frequency the twisted complete sum is `-1`. -/
theorem norm_zmodCoeff_klUnit_zero_le (u : (ZMod p)ˣ) :
    ‖zmodCoeff (fun x : ZMod p => klUnit p ((u : ZMod p) * x)) 0‖ ≤ 1 := by
  classical
  have hre : zmodCoeff (fun x : ZMod p => klUnit p ((u : ZMod p) * x)) 0 =
      ∑ w : (ZMod p)ˣ, hyperKloosterman ZMod.stdAddChar 3 (w : ZMod p) := by
    unfold zmodCoeff klUnit
    have hU : ∀ y : ZMod p, IsUnit ((u : ZMod p) * y) ↔ IsUnit y := fun y =>
      ⟨fun hy => isUnit_of_mul_isUnit_right hy, fun hy => (Units.isUnit u).mul hy⟩
    simp_rw [hU, ite_mul, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
    rw [← sum_units_eq (f := fun y : ZMod p => hyperKloosterman ZMod.stdAddChar 3
      ((u : ZMod p) * y))]
    exact Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun y => by simp)
  have h2 := sum_units_hyperKloosterman_mul (p := p) 0
  simp only [zero_mul, AddChar.map_zero_eq_one, mul_one] at h2
  rw [hre, h2]
  have : ∀ a b : (ZMod p)ˣ, ¬ (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((b⁻¹ : (ZMod p)ˣ) : ZMod p) =
      -(0 : ZMod p)) := by
    intro a b hab
    rw [neg_zero] at hab
    exact (Units.isUnit (a⁻¹ * b⁻¹)).ne_zero (by rw [Units.val_mul]; exact hab)
  simp only [this, if_false, Finset.sum_const_zero, mul_zero, zero_sub, norm_neg, norm_one,
    le_refl]

/-- Parseval with the twisted bound: `Σ_x |K*(ux; p)|² ≤ (2p√p + 1)²`. -/
theorem sum_norm_sq_klUnit_le (hp2 : p ≠ 2) (u : (ZMod p)ˣ) :
    ∑ x : ZMod p, ‖klUnit p ((u : ZMod p) * x)‖ ^ 2 ≤ (2 * p * Real.sqrt p + 1) ^ 2 := by
  have hP := sum_norm_sq_zmodCoeff (fun x : ZMod p => klUnit p ((u : ZMod p) * x))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hbound : ∑ h : ZMod p, ‖zmodCoeff (fun x : ZMod p => klUnit p ((u : ZMod p) * x)) h‖ ^ 2 ≤
      p * (2 * p * Real.sqrt p + 1) ^ 2 := by
    calc ∑ h : ZMod p, ‖zmodCoeff (fun x : ZMod p => klUnit p ((u : ZMod p) * x)) h‖ ^ 2
        ≤ ∑ _h : ZMod p, (2 * p * Real.sqrt p + 1) ^ 2 := by
          refine Finset.sum_le_sum fun h _ => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_zmodCoeff_klUnit_le hp2 u h) 2
      _ = p * (2 * p * Real.sqrt p + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [hP] at hbound
  exact le_of_mul_le_mul_left hbound hp0

end PrimePart

section PrimeSquarePart

variable {s : ℕ} [hs : Fact s.Prime]

theorem norm_klUnit_prime_sq_le (y : ZMod (s ^ 2)) : ‖klUnit (s ^ 2) y‖ ≤ 3 * (s : ℝ) ^ 2 := by
  unfold klUnit
  split_ifs with hy
  · obtain ⟨w, rfl⟩ := hy
    exact norm_hyperKloosterman_prime_sq_le w
  · rw [norm_zero]; positivity

/-- The prime-square factor `B(y) = K*(v₁y; s²) · conj K*(v₂y; s²)` of the off-diagonal. -/
def primeSqFactor (v₁ v₂ : (ZMod (s ^ 2))ˣ) (y : ZMod (s ^ 2)) : ℂ :=
  klUnit (s ^ 2) ((v₁ : ZMod (s ^ 2)) * y) * star (klUnit (s ^ 2) ((v₂ : ZMod (s ^ 2)) * y))

theorem zmodCoeff_primeSqFactor (v₁ v₂ : (ZMod (s ^ 2))ˣ) (h : ZMod (s ^ 2)) :
    zmodCoeff (primeSqFactor v₁ v₂) h =
      ∑ x : (ZMod (s ^ 2))ˣ, hyperKloosterman ZMod.stdAddChar 3
        ((v₁ : ZMod (s ^ 2)) * (x : ZMod (s ^ 2))) *
        hyperKloosterman ZMod.stdAddChar 3 (((-v₂ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) *
          (x : ZMod (s ^ 2))) *
        ZMod.stdAddChar ((-h) * (x : ZMod (s ^ 2))) := by
  classical
  unfold zmodCoeff primeSqFactor klUnit
  have hU : ∀ (v : (ZMod (s ^ 2))ˣ) (y : ZMod (s ^ 2)),
      IsUnit ((v : ZMod (s ^ 2)) * y) ↔ IsUnit y := fun v y =>
    ⟨fun hy => isUnit_of_mul_isUnit_right hy, fun hy => (Units.isUnit v).mul hy⟩
  simp_rw [hU]
  have hterm : ∀ y : ZMod (s ^ 2), (if IsUnit y then hyperKloosterman ZMod.stdAddChar 3
      ((v₁ : ZMod (s ^ 2)) * y) else 0) * star (if IsUnit y then hyperKloosterman ZMod.stdAddChar 3
      ((v₂ : ZMod (s ^ 2)) * y) else 0) * ZMod.stdAddChar (-(h * y)) =
      if IsUnit y then hyperKloosterman ZMod.stdAddChar 3 ((v₁ : ZMod (s ^ 2)) * y) *
        hyperKloosterman ZMod.stdAddChar 3 (((-v₂ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * y) *
        ZMod.stdAddChar ((-h) * y) else 0 := by
    intro y
    split_ifs
    · rw [star_hyperKloosterman_three, Units.val_neg, neg_mul, neg_mul]
    · simp
  simp_rw [hterm]
  exact (sum_units_eq (f := fun y : ZMod (s ^ 2) => hyperKloosterman ZMod.stdAddChar 3
    ((v₁ : ZMod (s ^ 2)) * y) * hyperKloosterman ZMod.stdAddChar 3
      (((-v₂ : (ZMod (s ^ 2))ˣ) : ZMod (s ^ 2)) * y) * ZMod.stdAddChar ((-h) * y))).symm

/-- Generic frequencies: `|B̂(h)| ≤ 6s⁵` when `s ∤ h`. -/
theorem norm_zmodCoeff_primeSqFactor_le (v₁ v₂ : (ZMod (s ^ 2))ˣ) (h : ZMod (s ^ 2))
    (hh : red s h ≠ 0) : ‖zmodCoeff (primeSqFactor v₁ v₂) h‖ ≤ 6 * (s : ℝ) ^ 5 := by
  rw [zmodCoeff_primeSqFactor]
  exact norm_corr_prime_sq_le v₁ (-v₂) (-h) (by rw [map_neg, neg_ne_zero]; exact hh)

/-- All frequencies: `|B̂(h)| ≤ 9s⁶`. -/
theorem norm_zmodCoeff_primeSqFactor_le_all (v₁ v₂ : (ZMod (s ^ 2))ˣ) (h : ZMod (s ^ 2)) :
    ‖zmodCoeff (primeSqFactor v₁ v₂) h‖ ≤ 9 * (s : ℝ) ^ 6 := by
  unfold zmodCoeff
  calc ‖∑ y : ZMod (s ^ 2), primeSqFactor v₁ v₂ y * ZMod.stdAddChar (-(h * y))‖
      ≤ ∑ y : ZMod (s ^ 2), ‖primeSqFactor v₁ v₂ y * ZMod.stdAddChar (-(h * y))‖ := norm_sum_le _ _
    _ ≤ ∑ _y : ZMod (s ^ 2), (3 * (s : ℝ) ^ 2) * (3 * (s : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_mul, AddChar.norm_apply, mul_one, primeSqFactor, norm_mul, norm_star]
        exact mul_le_mul (norm_klUnit_prime_sq_le _) (norm_klUnit_prime_sq_le _) (norm_nonneg _)
          (by positivity)
    _ = 9 * (s : ℝ) ^ 6 := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        push_cast; ring

end PrimeSquarePart

section Assembly

variable {p p₁ p₂ s : ℕ}

/-- **Diagonal term.** `Σ_{m ≤ L} |K*(um; p) K*(vm; s²)|² ≤ 9s⁴ (L/p + 1)(2p√p + 1)²`. -/
theorem diag_le [Fact p.Prime] [Fact s.Prime] (hp2 : p ≠ 2) (u : (ZMod p)ˣ)
    (v : (ZMod (s ^ 2))ˣ) (L : ℕ) :
    ∑ m ∈ Finset.Icc 1 L, ‖klUnit p ((u : ZMod p) * (m : ZMod p)) *
        klUnit (s ^ 2) ((v : ZMod (s ^ 2)) * (m : ZMod (s ^ 2)))‖ ^ 2 ≤
      9 * (s : ℝ) ^ 4 * (((L : ℝ) / p + 1) * (2 * p * Real.sqrt p + 1) ^ 2) := by
  calc ∑ m ∈ Finset.Icc 1 L, ‖klUnit p ((u : ZMod p) * (m : ZMod p)) *
        klUnit (s ^ 2) ((v : ZMod (s ^ 2)) * (m : ZMod (s ^ 2)))‖ ^ 2
      ≤ ∑ m ∈ Finset.Icc 1 L, 9 * (s : ℝ) ^ 4 * ‖klUnit p ((u : ZMod p) * (m : ZMod p))‖ ^ 2 := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [norm_mul, mul_pow]
        have h3 := norm_klUnit_prime_sq_le (s := s) ((v : ZMod (s ^ 2)) * (m : ZMod (s ^ 2)))
        have h3' : ‖klUnit (s ^ 2) ((v : ZMod (s ^ 2)) * (m : ZMod (s ^ 2)))‖ ^ 2 ≤
            9 * (s : ℝ) ^ 4 := by
          calc _ ≤ (3 * (s : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
            _ = 9 * (s : ℝ) ^ 4 := by ring
        nlinarith [sq_nonneg ‖klUnit p ((u : ZMod p) * (m : ZMod p))‖]
    _ = 9 * (s : ℝ) ^ 4 * ∑ m ∈ Finset.Icc 1 L,
          ‖klUnit p ((u : ZMod p) * (m : ZMod p))‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ 9 * (s : ℝ) ^ 4 * (((L : ℝ) / p + 1) * (2 * p * Real.sqrt p + 1) ^ 2) := by
        gcongr
        refine (sum_Icc_periodic_le (fun x : ZMod p => ‖klUnit p ((u : ZMod p) * x)‖ ^ 2)
          (fun x => by positivity) L).trans ?_
        gcongr
        exact sum_norm_sq_klUnit_le hp2 u

/-- **Off-diagonal term.** For distinct primes `p₁, p₂` different from the prime `s`, the
correlation `Σ_{m ≤ L} c₁(m) conj c₂(m)` of `c_i(m) = K*(u_i m; p_i) K*(v_i m; s²)` is at most
`(L/(p₁p₂s²)) 9s⁶ + A₁A₂ (6s⁵ (1 + log (p₁p₂s²)) + 9s⁵ (1 + log (p₁p₂s)))` with `A_i = 2p_i√p_i + 1`. -/
theorem offdiag_le [Fact p₁.Prime] [Fact p₂.Prime] [Fact s.Prime] (hp₁2 : p₁ ≠ 2)
    (hp₂2 : p₂ ≠ 2) (h12 : p₁ ≠ p₂) (h1s : p₁ ≠ s) (h2s : p₂ ≠ s)
    (u₁ : (ZMod p₁)ˣ) (u₂ : (ZMod p₂)ˣ) (v₁ v₂ : (ZMod (s ^ 2))ˣ) (L : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 L, (klUnit p₁ ((u₁ : ZMod p₁) * (m : ZMod p₁)) *
        klUnit (s ^ 2) ((v₁ : ZMod (s ^ 2)) * (m : ZMod (s ^ 2)))) *
        star (klUnit p₂ ((u₂ : ZMod p₂) * (m : ZMod p₂)) *
        klUnit (s ^ 2) ((v₂ : ZMod (s ^ 2)) * (m : ZMod (s ^ 2))))‖ ≤
      (L : ℝ) / (p₁ * p₂ * s ^ 2 : ℕ) * (9 * (s : ℝ) ^ 6) +
        (2 * p₁ * Real.sqrt p₁ + 1) * (2 * p₂ * Real.sqrt p₂ + 1) * (6 * (s : ℝ) ^ 5) *
          (1 + Real.log (p₁ * p₂ * s ^ 2 : ℕ)) +
        (2 * p₁ * Real.sqrt p₁ + 1) * (2 * p₂ * Real.sqrt p₂ + 1) * (9 * (s : ℝ) ^ 6) / s *
          (1 + Real.log (p₁ * p₂ * s : ℕ)) := by
  have hp₁ := (Fact.out : p₁.Prime)
  have hp₂ := (Fact.out : p₂.Prime)
  have hs := (Fact.out : s.Prime)
  have c12 : p₁.Coprime p₂ := (Nat.coprime_primes hp₁ hp₂).2 h12
  have c13 : p₁.Coprime (s ^ 2) := Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp₁ hs).2 h1s)
  have c23 : p₂.Coprime (s ^ 2) := Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp₂ hs).2 h2s)
  have hsum : ∀ m : ℕ, (klUnit p₁ ((u₁ : ZMod p₁) * (m : ZMod p₁)) *
        klUnit (s ^ 2) ((v₁ : ZMod (s ^ 2)) * (m : ZMod (s ^ 2)))) *
        star (klUnit p₂ ((u₂ : ZMod p₂) * (m : ZMod p₂)) *
        klUnit (s ^ 2) ((v₂ : ZMod (s ^ 2)) * (m : ZMod (s ^ 2)))) =
      (fun x : ZMod p₁ => klUnit p₁ ((u₁ : ZMod p₁) * x)) (m : ZMod p₁) *
        (fun x : ZMod p₂ => star (klUnit p₂ ((u₂ : ZMod p₂) * x))) (m : ZMod p₂) *
        primeSqFactor v₁ v₂ (m : ZMod (s ^ 2)) := by
    intro m
    simp only [primeSqFactor, star_mul']
    ring
  rw [Finset.sum_congr rfl fun m _ => hsum m]
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs.pos
  refine norm_sum_Icc_triple_le c12 c13 c23 (d := s) (N₃ := s) hs.pos (sq s)
    (fun x : ZMod p₁ => klUnit p₁ ((u₁ : ZMod p₁) * x))
    (fun x : ZMod p₂ => star (klUnit p₂ ((u₂ : ZMod p₂) * x))) (primeSqFactor v₁ v₂)
    (fun h => norm_zmodCoeff_klUnit_le hp₁2 u₁ h)
    (fun h => by rw [zmodCoeff_star, norm_star]; exact norm_zmodCoeff_klUnit_le hp₂2 u₂ (-h))
    (by positivity)
    (fun h hh => norm_zmodCoeff_primeSqFactor_le v₁ v₂ h (by
      rw [red_apply]; intro h0; exact hh ((ZMod.natCast_eq_zero_iff _ _).1 h0)))
    (fun h => norm_zmodCoeff_primeSqFactor_le_all v₁ v₂ h) ?_ L
  rw [norm_mul, norm_mul]
  have e1 := norm_zmodCoeff_klUnit_zero_le u₁
  have e2 : ‖zmodCoeff (fun x : ZMod p₂ => star (klUnit p₂ ((u₂ : ZMod p₂) * x))) 0‖ ≤ 1 := by
    rw [zmodCoeff_star, norm_star, neg_zero]; exact norm_zmodCoeff_klUnit_zero_le u₂
  have e3 := norm_zmodCoeff_primeSqFactor_le_all v₁ v₂ 0
  calc _ ≤ 1 * 1 * (9 * (s : ℝ) ^ 6) :=
        mul_le_mul (mul_le_mul e1 e2 (norm_nonneg _) zero_le_one) e3 (norm_nonneg _)
          (by norm_num)
    _ = 9 * (s : ℝ) ^ 6 := by ring

end Assembly

end

end GaloisForLFunctions.RHTower.HyperKloostermanFactoredModuli
