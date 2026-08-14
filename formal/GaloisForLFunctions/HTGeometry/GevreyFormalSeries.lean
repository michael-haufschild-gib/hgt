import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Normed
import GaloisForLFunctions.HTGeometry.GevreyExactOrder

/-!
# The Gevrey filtration on formal power series

A formal power series is *Gevrey of order `r`* when its coefficients obey `‖aₙ‖ ≤ C Aⁿ (n!)^r`.
For `r = 0` this is exactly convergence; for `r > 0` it is the classical Gevrey class `ℂ[[t]]_r`,
the natural home of divergent solutions of analytic differential equations.

The filtration is increasing in `r` and each level is a differential subalgebra: sums, Cauchy
products and formal derivatives stay in the same class.  Multiplicativity uses only
`i! · j! ∣ (i+j)!` and the fact that the antidiagonal of `n` has `n+1` elements, and the derivative
uses only that a polynomial factor is dominated by a geometric one.
-/

open PowerSeries Filter
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### A polynomial factor is dominated by a geometric one -/

/-- Every polynomial growth is dominated by every geometric growth of ratio above one. -/
theorem exists_pow_le_const_mul_pow (d : ℕ) {B : ℝ} (hB : 1 < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ((n : ℝ)) ^ d ≤ C * B ^ n := by
  classical
  have hB0 : (0 : ℝ) < B := lt_trans zero_lt_one hB
  have htend := tendsto_pow_const_div_const_pow_of_one_lt d hB
  have hev : ∀ᶠ n : ℕ in atTop, ((n : ℝ)) ^ d / B ^ n < 1 := by
    have := htend.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    simpa using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨1 + ∑ k ∈ Finset.range N, ((k : ℝ)) ^ d, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ∑ k ∈ Finset.range N, ((k : ℝ)) ^ d :=
      Finset.sum_nonneg fun k _ => by positivity
    linarith
  · intro n
    have hpow : (1 : ℝ) ≤ B ^ n := one_le_pow₀ (le_of_lt hB)
    have hCnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range N, ((k : ℝ)) ^ d :=
      Finset.sum_nonneg fun k _ => by positivity
    by_cases hn : N ≤ n
    · have h1 := hN n hn
      have h2 : ((n : ℝ)) ^ d < B ^ n := by
        rw [div_lt_one (by positivity)] at h1
        exact h1
      calc ((n : ℝ)) ^ d ≤ B ^ n := le_of_lt h2
        _ ≤ (1 + ∑ k ∈ Finset.range N, ((k : ℝ)) ^ d) * B ^ n := by nlinarith [hpow]
    · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      have hle : ((n : ℝ)) ^ d ≤ ∑ k ∈ Finset.range N, ((k : ℝ)) ^ d :=
        Finset.single_le_sum (f := fun k : ℕ => ((k : ℝ)) ^ d)
          (fun k _ => by positivity) hmem
      calc ((n : ℝ)) ^ d ≤ ∑ k ∈ Finset.range N, ((k : ℝ)) ^ d := hle
        _ ≤ 1 + ∑ k ∈ Finset.range N, ((k : ℝ)) ^ d := by linarith
        _ ≤ (1 + ∑ k ∈ Finset.range N, ((k : ℝ)) ^ d) * B ^ n := by nlinarith [hpow]

/-- The shifted form: `(n+1)^d` is dominated by a geometric sequence. -/
theorem exists_succ_pow_le_const_mul_pow (d : ℕ) {B : ℝ} (hB : 1 < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, ((n : ℝ) + 1) ^ d ≤ C * B ^ n := by
  obtain ⟨C, hC1, hC⟩ := exists_pow_le_const_mul_pow d hB
  have hB0 : (0 : ℝ) < B := lt_trans zero_lt_one hB
  refine ⟨C * B, ?_, ?_⟩
  · nlinarith [hC1, hB]
  · intro n
    have h := hC (n + 1)
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    calc ((n : ℝ) + 1) ^ d ≤ C * B ^ (n + 1) := h
      _ = (C * B) * B ^ n := by rw [pow_succ]; ring

/-! ### The Gevrey classes -/

/-- A formal power series is Gevrey of order `r` when `‖aₙ‖ ≤ C Aⁿ (n!)^r`. -/
def IsGevreySeries (r : ℝ) (F : PowerSeries ℂ) : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ n : ℕ, ‖PowerSeries.coeff n F‖ ≤ C * A ^ n * (n ! : ℝ) ^ r

theorem one_le_factorial_cast (n : ℕ) : (1 : ℝ) ≤ (n ! : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)

theorem factorial_rpow_pos (n : ℕ) (r : ℝ) : (0 : ℝ) < (n ! : ℝ) ^ r :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (one_le_factorial_cast n)) r

/-- The Gevrey filtration is increasing in the order. -/
theorem IsGevreySeries.mono {r r' : ℝ} {F : PowerSeries ℂ} (hrr : r ≤ r')
    (h : IsGevreySeries r F) : IsGevreySeries r' F := by
  obtain ⟨C, A, hC, hA, hbound⟩ := h
  refine ⟨C, A, hC, hA, fun n => ?_⟩
  refine le_trans (hbound n) ?_
  have hfac : (n ! : ℝ) ^ r ≤ (n ! : ℝ) ^ r' :=
    Real.rpow_le_rpow_of_exponent_le (one_le_factorial_cast n) hrr
  have hpos : (0 : ℝ) ≤ C * A ^ n := by positivity
  exact mul_le_mul_of_nonneg_left hfac hpos

/-- Constants are Gevrey of every nonnegative order. -/
theorem isGevreySeries_C (r : ℝ) (c : ℂ) : IsGevreySeries r (PowerSeries.C c) := by
  refine ⟨‖c‖ + 1, 1, by positivity, one_pos, fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    simp only [PowerSeries.coeff_zero_C, Nat.factorial_zero, Nat.cast_one, pow_zero,
      Real.one_rpow, mul_one]
    linarith
  · rw [PowerSeries.coeff_C, if_neg hn, norm_zero]
    positivity

theorem IsGevreySeries.add {r : ℝ} {F G : PowerSeries ℂ} (hF : IsGevreySeries r F)
    (hG : IsGevreySeries r G) : IsGevreySeries r (F + G) := by
  obtain ⟨C₁, A₁, hC₁, hA₁, h₁⟩ := hF
  obtain ⟨C₂, A₂, hC₂, hA₂, h₂⟩ := hG
  refine ⟨C₁ + C₂, max A₁ A₂, by linarith, lt_of_lt_of_le hA₁ (le_max_left _ _), fun n => ?_⟩
  have hmax1 : A₁ ^ n ≤ (max A₁ A₂) ^ n :=
    pow_le_pow_left₀ (le_of_lt hA₁) (le_max_left _ _) n
  have hmax2 : A₂ ^ n ≤ (max A₁ A₂) ^ n :=
    pow_le_pow_left₀ (le_of_lt hA₂) (le_max_right _ _) n
  have hfac : (0 : ℝ) < (n ! : ℝ) ^ r := factorial_rpow_pos n r
  calc ‖PowerSeries.coeff n (F + G)‖
      ≤ ‖PowerSeries.coeff n F‖ + ‖PowerSeries.coeff n G‖ := by
        rw [map_add]; exact norm_add_le _ _
    _ ≤ C₁ * A₁ ^ n * (n ! : ℝ) ^ r + C₂ * A₂ ^ n * (n ! : ℝ) ^ r := add_le_add (h₁ n) (h₂ n)
    _ ≤ C₁ * (max A₁ A₂) ^ n * (n ! : ℝ) ^ r + C₂ * (max A₁ A₂) ^ n * (n ! : ℝ) ^ r := by
        gcongr
    _ = (C₁ + C₂) * (max A₁ A₂) ^ n * (n ! : ℝ) ^ r := by ring

/-- The Gevrey bound of a Cauchy product: `i! · j! ≤ (i+j)!` collapses the two factorial factors,
and the antidiagonal contributes only the polynomial factor `n+1`. -/
theorem IsGevreySeries.mul {r : ℝ} (hr : 0 ≤ r) {F G : PowerSeries ℂ}
    (hF : IsGevreySeries r F) (hG : IsGevreySeries r G) : IsGevreySeries r (F * G) := by
  classical
  obtain ⟨C₁, A₁, hC₁, hA₁, h₁⟩ := hF
  obtain ⟨C₂, A₂, hC₂, hA₂, h₂⟩ := hG
  set A : ℝ := max A₁ A₂ with hAdef
  have hA : 0 < A := lt_of_lt_of_le hA₁ (le_max_left _ _)
  obtain ⟨C₃, hC₃1, hC₃⟩ := exists_succ_pow_le_const_mul_pow 1 (by norm_num : (1 : ℝ) < 2)
  refine ⟨C₁ * C₂ * C₃, 2 * A, by positivity, by positivity, fun n => ?_⟩
  have hfacpos : (0 : ℝ) < (n ! : ℝ) ^ r := factorial_rpow_pos n r
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      ‖PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖
        ≤ C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r := by
    intro p hp
    have hpn : p.1 + p.2 = n := List.Nat.mem_antidiagonal.mp hp
    have hfac : ((p.1 ! * p.2 ! : ℕ) : ℝ) ≤ (n ! : ℝ) := by
      have hdvd := Nat.factorial_mul_factorial_dvd_factorial_add p.1 p.2
      have hle : p.1 ! * p.2 ! ≤ (p.1 + p.2)! :=
        Nat.le_of_dvd (Nat.factorial_pos _) hdvd
      rw [hpn] at hle
      exact_mod_cast hle
    have hrp : ((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r ≤ (n ! : ℝ) ^ r := by
      have hmul : ((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r = ((p.1 ! * p.2 ! : ℕ) : ℝ) ^ r := by
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [hmul]
      refine Real.rpow_le_rpow (by positivity) hfac hr
    have hAp : A₁ ^ p.1 * A₂ ^ p.2 ≤ A ^ n := by
      have h1 : A₁ ^ p.1 ≤ A ^ p.1 := pow_le_pow_left₀ (le_of_lt hA₁) (le_max_left _ _) _
      have h2 : A₂ ^ p.2 ≤ A ^ p.2 := pow_le_pow_left₀ (le_of_lt hA₂) (le_max_right _ _) _
      calc A₁ ^ p.1 * A₂ ^ p.2 ≤ A ^ p.1 * A ^ p.2 := by
            exact mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = A ^ n := by rw [← pow_add, hpn]
    calc ‖PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖
        = ‖PowerSeries.coeff p.1 F‖ * ‖PowerSeries.coeff p.2 G‖ := norm_mul _ _
      _ ≤ (C₁ * A₁ ^ p.1 * ((p.1 ! : ℝ)) ^ r) * (C₂ * A₂ ^ p.2 * ((p.2 ! : ℝ)) ^ r) :=
          mul_le_mul (h₁ p.1) (h₂ p.2) (norm_nonneg _) (by positivity)
      _ = (C₁ * C₂) * (A₁ ^ p.1 * A₂ ^ p.2) * (((p.1 ! : ℝ)) ^ r * ((p.2 ! : ℝ)) ^ r) := by ring
      _ ≤ (C₁ * C₂) * A ^ n * (n ! : ℝ) ^ r := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hAp (by positivity)) hrp
            (by positivity) (by positivity)
      _ = C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r := by ring
  have hcard : (Finset.HasAntidiagonal.antidiagonal n).card = n + 1 := Finset.Nat.card_antidiagonal n
  calc ‖PowerSeries.coeff n (F * G)‖
      = ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖ := by
        rw [PowerSeries.coeff_mul]
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal n, C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * (C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (C₃ * 2 ^ n) * (C₁ * C₂ * A ^ n * (n ! : ℝ) ^ r) := by
        have h := hC₃ n
        simp only [pow_one] at h
        exact mul_le_mul_of_nonneg_right h (by positivity)
    _ = C₁ * C₂ * C₃ * (2 * A) ^ n * (n ! : ℝ) ^ r := by
        rw [mul_pow]
        ring

/-- The Gevrey classes are stable under formal differentiation. -/
theorem IsGevreySeries.derivativeFun {r : ℝ} {F : PowerSeries ℂ}
    (hF : IsGevreySeries r F) : IsGevreySeries r F.derivativeFun := by
  obtain ⟨C, A, hC, hA, hbound⟩ := hF
  obtain ⟨C₃, hC₃1, hC₃⟩ :=
    exists_succ_pow_le_const_mul_pow ⌈1 + r⌉₊ (by norm_num : (1 : ℝ) < 2)
  refine ⟨C * A * C₃, 2 * A, by positivity, by positivity, fun n => ?_⟩
  have hfacsucc : (((n + 1)! : ℕ) : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hsplit : ((((n + 1)! : ℕ) : ℝ)) ^ r = ((n : ℝ) + 1) ^ r * (n ! : ℝ) ^ r := by
    rw [hfacsucc, Real.mul_rpow (by positivity) (by positivity)]
  have hstep : ‖PowerSeries.coeff n F.derivativeFun‖
      ≤ (C * A) * A ^ n * (n ! : ℝ) ^ r * (((n : ℝ) + 1) ^ r * ((n : ℝ) + 1)) := by
    rw [PowerSeries.coeff_derivativeFun, norm_mul]
    have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hnorm]
    have h1 := hbound (n + 1)
    have h2 : ‖PowerSeries.coeff (n + 1) F‖
        ≤ C * A ^ (n + 1) * (((n : ℝ) + 1) ^ r * (n ! : ℝ) ^ r) := by
      rw [← hsplit]
      exact h1
    calc ‖PowerSeries.coeff (n + 1) F‖ * ((n : ℝ) + 1)
        ≤ (C * A ^ (n + 1) * (((n : ℝ) + 1) ^ r * (n ! : ℝ) ^ r)) * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (C * A) * A ^ n * (n ! : ℝ) ^ r * (((n : ℝ) + 1) ^ r * ((n : ℝ) + 1)) := by
          rw [pow_succ]
          ring
  have hpoly : ((n : ℝ) + 1) ^ r * ((n : ℝ) + 1) ≤ C₃ * 2 ^ n := by
    have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hexp : ((n : ℝ) + 1) ^ r * ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ (r + 1) :=
      (Real.rpow_add_one hne r).symm
    rw [hexp]
    refine le_trans ?_ (hC₃ n)
    have hle : r + 1 ≤ (⌈1 + r⌉₊ : ℝ) := by
      have := Nat.le_ceil (1 + r)
      linarith
    calc ((n : ℝ) + 1) ^ (r + 1) ≤ ((n : ℝ) + 1) ^ ((⌈1 + r⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hle
      _ = ((n : ℝ) + 1) ^ (⌈1 + r⌉₊ : ℕ) := Real.rpow_natCast _ _
  calc ‖PowerSeries.coeff n F.derivativeFun‖
      ≤ (C * A) * A ^ n * (n ! : ℝ) ^ r * (((n : ℝ) + 1) ^ r * ((n : ℝ) + 1)) := hstep
    _ ≤ (C * A) * A ^ n * (n ! : ℝ) ^ r * (C₃ * 2 ^ n) := by
        refine mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = C * A * C₃ * (2 * A) ^ n * (n ! : ℝ) ^ r := by
        rw [mul_pow]
        ring

/-! ### The exact Gevrey order of a formal series -/

/-- The Gevrey class of a formal series is the Gevrey class of its coefficient moduli. -/
theorem isGevreySeries_iff_isGevreyOfOrder (r : ℝ) (F : PowerSeries ℂ) :
    IsGevreySeries r F ↔ IsGevreyOfOrder (fun n => ‖PowerSeries.coeff n F‖) r := Iff.rfl

/-- A formal series has exact Gevrey order `s` when it is Gevrey of order `s` and of no smaller
order. -/
def IsExactGevreySeriesOrder (F : PowerSeries ℂ) (s : ℝ) : Prop :=
  IsGevreySeries s F ∧ ∀ r : ℝ, r < s → ¬ IsGevreySeries r F

theorem isExactGevreySeriesOrder_iff (F : PowerSeries ℂ) (s : ℝ) :
    IsExactGevreySeriesOrder F s ↔ IsExactGevreyOrder (fun n => ‖PowerSeries.coeff n F‖) s :=
  Iff.rfl

/-! ### The irrational-power Barnes tail as a formal series -/

/-- The formal Barnes tail `R̂_s(t) = ∑_{k ≥ 1} (-1)^k ζ(-s k) t^k`. -/
noncomputable def barnesTailSeries (s : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => if k = 0 then 0 else (-1) ^ k * riemannZeta ((-(s * k) : ℝ) : ℂ)

theorem norm_coeff_barnesTailSeries (s : ℝ) (k : ℕ) :
    ‖PowerSeries.coeff k (barnesTailSeries s)‖ = |zetaTailModulus s k| := by
  rw [barnesTailSeries, PowerSeries.coeff_mk, zetaTailModulus]
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk, if_neg hk, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      abs_of_nonneg (norm_nonneg _)]

/-- **The formal Barnes tail of an irrational power has exact Gevrey order `s`.**  This is the
series that a Newton-polygon slope would have to reciprocate. -/
theorem barnesTailSeries_isExactGevreySeriesOrder {s : ℝ} (hs : 0 < s) (hirr : Irrational s) :
    IsExactGevreySeriesOrder (barnesTailSeries s) s := by
  have h := zetaTail_isGevreyOfOrder_exact hs hirr
  rw [isExactGevreySeriesOrder_iff]
  have hfun : (fun n => ‖PowerSeries.coeff n (barnesTailSeries s)‖)
      = fun n => |zetaTailModulus s n| := funext (norm_coeff_barnesTailSeries s)
  rw [hfun]
  exact h

end GaloisForLFunctions.HTGeometry
