import GaloisForLFunctions.RHTower.SelbergKloostermanCongruence
import GaloisForLFunctions.RHTower.Sieve.KloostermanRamanujanDivisorSum

open Complex RHTower.Sieve

/-!
# The `Γ(N)` Ramanujan sums: `|S_N(0, n; c)| ≤ (N|n|)²`

`S(a, 0; K)` is a Ramanujan sum; the Möbius–divisor formula bounds it by `gcd(a, K)²`
(`norm_kloostermanSum_zero_le`). In the character detection of `S_N(0,n;c)` the relevant gcd is
`gcd(sgn(c) n + j|c|, |c|N) ≤ N |n|`: its part dividing `|c|` divides `n` and the cofactor divides `N` (`gcd_le`).
Hence `|S_N(0, n; c)| ≤ (N|n|)²` uniformly in `c` (`norm_ksum_zero_le`), the arithmetic input for the Fourier
expansion of the `Γ(N)` Eisenstein series on `Re s > 1/2`.
-/

namespace GaloisForLFunctions.RHTower.SelbergRamanujanBound
open GaloisForLFunctions.RHTower.SelbergPoincareFourier GaloisForLFunctions.RHTower.SelbergKloostermanCongruence
  GaloisForLFunctions.RHTower.KloostermanUniform

/-- `|S(a, 0; K)| ≤ gcd(a, K)²` (Ramanujan sum through its Möbius–divisor formula). -/
theorem norm_kloostermanSum_zero_le (K : ℕ) [NeZero K] (a : ZMod K) :
    ‖kloostermanSum K a 0‖ ≤ ((a.val.gcd K : ℕ) : ℝ) ^ 2 := by
  set Q : RHTower.CGLPositiveModulus := ⟨K, Nat.pos_of_ne_zero (NeZero.ne K)⟩
  have h1 : kloostermanSum K a 0 = RHTower.cglRamanujanAdditiveSum Q a := by
    unfold kloostermanSum kloostermanPhase RHTower.cglRamanujanAdditiveSum
    simp only [zero_mul, add_zero]
    classical
    refine Finset.sum_bij' (fun u _ => (u : ZMod K)) (fun b hb => (Finset.mem_filter.mp hb).2.unit)
      (fun u _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩) (fun _ _ => Finset.mem_univ _)
      (fun u _ => by ext; simp) (fun b hb => by simp) (fun u _ => by rw [mul_comm])
  rw [h1, cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum_sieve]
  set g := a.val.gcd K
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ d ∈ g.divisors, ‖((d : ℕ) : ℂ) * ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ)‖ ≤ (g : ℝ) := by
    intro d hd
    rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
    have hμ : |((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := Q.value / d)
      exact_mod_cast this
    have hdg : (d : ℝ) ≤ g := by exact_mod_cast Nat.divisor_le hd
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℝ), Nat.cast_nonneg (α := ℝ) d]
  calc ∑ d ∈ g.divisors, ‖((d : ℕ) : ℂ) * ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ)‖
      ≤ ∑ _d ∈ g.divisors, (g : ℝ) := Finset.sum_le_sum hb
    _ = g.divisors.card * g := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ g * g := by
        gcongr
        exact_mod_cast Nat.card_divisors_le_self g
    _ = _ := by ring

/-- The gcd controlling the Ramanujan sums in `S_N(0,n;c)` is at most `N|n|`. -/
theorem gcd_le (N : ℕ) [NeZero N] {c : ℤ} (hc : c ≠ 0) {n : ℤ} (hn : n ≠ 0) (j : ℕ) :
    haveI : NeZero (c.natAbs * N) := ⟨Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hc) (NeZero.ne N)⟩
    ((((c.sign * n + (j * c.natAbs : ℕ) : ℤ)) : ZMod (c.natAbs * N)).val).gcd (c.natAbs * N) ≤ N * n.natAbs := by
  haveI : NeZero (c.natAbs * N) := ⟨Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hc) (NeZero.ne N)⟩
  set K := c.natAbs * N
  set e : ℤ := c.sign * n + (j * c.natAbs : ℕ)
  set g := (((e : ZMod K)).val).gcd K
  have hgK : g ∣ K := Nat.gcd_dvd_right _ _
  have hge : (g : ℤ) ∣ e := by
    have h1 : (g : ℤ) ∣ (((e : ZMod K)).val : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
    have h2 : (K : ℤ) ∣ e - (((e : ZMod K)).val : ℤ) := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]; simp
    have h3 : (g : ℤ) ∣ e - (((e : ZMod K)).val : ℤ) := (Int.natCast_dvd_natCast.mpr hgK).trans h2
    have := dvd_add h3 h1
    simpa using this
  set h := g.gcd c.natAbs
  have hh : (h : ℤ) ∣ n := by
    have h1 : (h : ℤ) ∣ e := (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)).trans hge
    have h2 : (h : ℤ) ∣ ((j * c.natAbs : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr ((Nat.gcd_dvd_right _ _).trans (Dvd.intro_left _ rfl))
    have h3 : (h : ℤ) ∣ c.sign * n := by
      have := dvd_sub h1 h2; simpa [e] using this
    have hs : IsUnit c.sign := by
      rcases lt_or_gt_of_ne hc with hlt | hgt
      · rw [Int.sign_eq_neg_one_of_neg hlt]; exact isUnit_one.neg
      · rw [Int.sign_eq_one_of_pos hgt]; exact isUnit_one
    exact (hs.dvd_mul_left).mp h3
  have hgh : g ∣ h * N := by
    have := Nat.dvd_gcd (Dvd.intro N rfl : g ∣ g * N) hgK
    rwa [Nat.gcd_mul_right] at this
  have hhn : h ≤ n.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (Int.natCast_dvd.mp hh)
  calc g ≤ h * N := Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (fun h0 => by
          have := Nat.gcd_eq_zero_iff.mp h0; exact Int.natAbs_ne_zero.mpr hc this.2)) (Nat.pos_of_ne_zero (NeZero.ne N))) hgh
    _ ≤ n.natAbs * N := Nat.mul_le_mul_right _ hhn
    _ = N * n.natAbs := by ring

variable (N : ℕ)

theorem norm_ksum_zero_le [NeZero N] {c : ℤ} (hc : c ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    ‖ksum N 0 c n‖ ≤ ((N * n.natAbs : ℕ) : ℝ) ^ 2 := by
  set m : ℕ := 0
  haveI hK : NeZero (c.natAbs * N) := ⟨Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hc) (NeZero.ne N)⟩
  set K := c.natAbs * N
  by_cases hNc : (N : ℤ) ∣ c
  · have hNK : N ∣ K := Dvd.intro_left _ rfl
    set B : ZMod K := ((c.sign * m : ℤ) : ZMod K)
    set A : ZMod N → ZMod K := fun t => (((c.sign * n + (t.val * (K / N) : ℕ) : ℤ)) : ZMod K)
    have hterm : ∀ r ∈ Finset.range K, (adm N).indicator (kphase N m n) (c, (r : ℤ)) =
        (N : ℂ)⁻¹ * ∑ t : ZMod N, ZMod.stdAddChar (-t) *
          (if IsUnit (r : ZMod K) then ZMod.stdAddChar (A t * (r : ZMod K) + B * (r : ZMod K)⁻¹) else 0) := by
      intro r _
      by_cases hu : IsUnit (r : ZMod K)
      · simp only [if_pos hu]
        have hind : (adm N).indicator (kphase N m n) (c, (r : ℤ)) =
            (if (r : ZMod N) = 1 then (1 : ℂ) else 0) * kphase N m n (c, r) := by
          by_cases h1 : (r : ZMod N) = 1
          · rw [Set.indicator_of_mem ((adm_iff N hNc r).mpr ⟨h1, hu⟩), if_pos h1, one_mul]
          · rw [Set.indicator_of_notMem (fun h => h1 ((adm_iff N hNc r).mp h).1), if_neg h1, zero_mul]
        rw [hind, ite_eq_one, kphase_eq N m hc n r, mul_assoc, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        rw [mul_sub, mul_one, sub_eq_add_neg, AddChar.map_add_eq_mul, stdAddChar_cast N hNK, mul_comm (ZMod.stdAddChar _) (ZMod.stdAddChar (-t)), mul_assoc,
          ← AddChar.map_add_eq_mul]
        congr 2
        simp only [A, Int.cast_add, Int.cast_natCast]
        ring
      · simp only [if_neg hu, mul_zero, Finset.sum_const_zero]
        exact Set.indicator_of_notMem (fun h => hu ((adm_iff N hNc r).mp h).2) _
    have hks : ksum N m c n = (N : ℂ)⁻¹ * ∑ t : ZMod N, ZMod.stdAddChar (-t) * kloostermanSum K (A t) B := by
      unfold ksum
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.mul_sum, sum_range_units K (fun a => ZMod.stdAddChar (A t * a + B * a⁻¹))]
      congr 1
      unfold kloostermanSum kloostermanPhase
      apply Finset.sum_congr rfl
      intro x _
      rw [ZMod.inv_coe_unit]
    rw [hks, norm_mul, norm_inv, Complex.norm_natCast]
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    rw [inv_mul_le_iff₀ hN]
    refine (norm_sum_le _ _).trans ?_
    have hKN : K / N = c.natAbs := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne N))
    have hb : ∀ t : ZMod N, ‖ZMod.stdAddChar (-t) * kloostermanSum K (A t) B‖ ≤ ((N * n.natAbs : ℕ) : ℝ) ^ 2 := by
      intro t
      rw [norm_mul, AddChar.norm_apply, one_mul]
      have hB0 : B = 0 := by simp [B, m]
      rw [hB0]
      refine (norm_kloostermanSum_zero_le K (A t)).trans ?_
      have hg := gcd_le N hc hn t.val
      simp only [A, hKN] at hg ⊢
      gcongr
    calc ∑ t : ZMod N, ‖ZMod.stdAddChar (-t) * kloostermanSum K (A t) B‖ ≤ ∑ _t : ZMod N, ((N * n.natAbs : ℕ) : ℝ) ^ 2 :=
          Finset.sum_le_sum (fun t _ => hb t)
      _ = N * ((N * n.natAbs : ℕ) : ℝ) ^ 2 := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  · have h0 : ksum N m c n = 0 := by
      unfold ksum
      exact Finset.sum_eq_zero (fun r _ => Set.indicator_of_notMem (fun h => hNc h.1) _)
    rw [h0, norm_zero]
    positivity


end GaloisForLFunctions.RHTower.SelbergRamanujanBound
