import GaloisForLFunctions.RHTower.DeningerMobiusPreimage

/-!
# The pointwise Möbius right inverse on the positive ray

An absolutely summable family on `ℕ × ℕ` supported away from the zero product may be summed along
the fibres of the product map, and each fibre is the divisor antidiagonal.  This is the only
interchange the Möbius calculus of the ray needs.

Applied to `μ(k) H_h((nk)x)` it gives the pointwise right-inverse theorem: summing the canonical
Möbius preimage over the dilation orbit returns the pullback,

`∑_{n ≥ 1} f_h(nx) = H_h(x)`,

because `∑_{d | N} μ(N/d)` is `1` at `N = 1` and `0` elsewhere.

* `deningerProductFibre_tsum` : **the product-fibre interchange.**
* `deningerRaySum` : the dilation-orbit sum `Z`.
* `deningerMobius_rightInverse` : **`Z f_h = H_h` on the positive ray.**
-/

namespace RHTower

open SchwartzMap ArithmeticFunction

noncomputable section

/-! ## The product-fibre interchange -/

/-- **The product-fibre interchange.**  An absolutely summable family on `ℕ × ℕ` vanishing on the
zero product is summed by grouping along the fibres of `(m, k) ↦ mk`, each of which is the divisor
antidiagonal. -/
theorem deningerProductFibre_tsum {F : ℕ × ℕ → ℂ} (hF : Summable F)
    (hzero : ∀ q : ℕ × ℕ, q.1 * q.2 = 0 → F q = 0) :
    (∑' q : ℕ × ℕ, F q) = ∑' N : ℕ, ∑ d ∈ N.divisors, F (d, N / d) := by
  classical
  set E : (Σ N : ℕ, {q : ℕ × ℕ // q ∈ N.divisorsAntidiagonal}) → ℕ × ℕ := fun p => p.2.1 with hE
  have hEinj : Function.Injective E := by
    rintro ⟨N, ⟨q, hq⟩⟩ ⟨N', ⟨q', hq'⟩⟩ hEq
    have hqq : q = q' := hEq
    subst hqq
    have h1 : q.1 * q.2 = N := (Nat.mem_divisorsAntidiagonal.mp hq).1
    have h2 : q.1 * q.2 = N' := (Nat.mem_divisorsAntidiagonal.mp hq').1
    have hNN : N = N' := by rw [← h1, h2]
    subst hNN
    rfl
  have hsupp : Function.support F ⊆ Set.range E := by
    intro q hq
    have hne : q.1 * q.2 ≠ 0 := fun h => hq (hzero q h)
    exact ⟨⟨q.1 * q.2, ⟨q, Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hne⟩⟩⟩, rfl⟩
  have hcomp : Summable (fun p : (Σ N : ℕ, {q : ℕ × ℕ // q ∈ N.divisorsAntidiagonal}) => F (E p)) :=
    hF.comp_injective hEinj
  rw [← hEinj.tsum_eq hsupp, hcomp.tsum_sigma]
  refine tsum_congr fun N => ?_
  rw [tsum_fintype]
  have hcoe : (∑ c : {q : ℕ × ℕ // q ∈ N.divisorsAntidiagonal}, F (E ⟨N, c⟩))
      = ∑ q ∈ N.divisorsAntidiagonal, F q :=
    Finset.sum_coe_sort N.divisorsAntidiagonal F
  rw [hcoe]
  exact Nat.sum_divisorsAntidiagonal fun a b => F (a, b)

/-! ## The dilation-orbit sum -/

/-- The dilation-orbit sum `Z F(x) = ∑_{n ≥ 1} F(nx)` of a function on the positive ray. -/
def deningerRaySum (F : ℝ → ℂ) (x : ℝ) : ℂ := ∑' n : ℕ, F (((n : ℝ) + 1) * x)

/-! ## The right-inverse theorem -/

/-- The two-variable family whose fibre sums are the Möbius preimage. -/
private def deningerMobiusPair (h : 𝓢(ℝ, ℂ)) (x : ℝ) (q : ℕ × ℕ) : ℂ :=
  if q.1 = 0 then 0
  else ((moebius q.2 : ℤ) : ℂ) * deningerLogPull h (((q.1 * q.2 : ℕ) : ℝ) * x)

private theorem deningerMobiusPair_zero (h : 𝓢(ℝ, ℂ)) (x : ℝ) {q : ℕ × ℕ}
    (hq : q.1 * q.2 = 0) : deningerMobiusPair h x q = 0 := by
  rw [deningerMobiusPair]
  rcases Nat.mul_eq_zero.mp hq with h1 | h2
  · rw [if_pos h1]
  · rw [h2]
    simp

private theorem deningerMobiusPair_summable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) {x : ℝ}
    (hx : 0 < x) : Summable (deningerMobiusPair h x) := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le_inv_sq hh
  have hxsq : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
  have hsq : Summable fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hpair : Summable fun q : ℕ × ℕ =>
      (C / x ^ (2 : ℕ)) * ((1 / (q.1 : ℝ) ^ (2 : ℕ)) * (1 / (q.2 : ℝ) ^ (2 : ℕ))) := by
    refine Summable.mul_left _ ?_
    exact Summable.mul_of_nonneg (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ))
      (g := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) hsq hsq
      (fun n => by positivity) (fun n => by positivity)
  refine Summable.of_norm_bounded hpair fun q => ?_
  rcases Nat.eq_zero_or_pos (q.1 * q.2) with hq0 | hqpos
  · rw [deningerMobiusPair_zero h x hq0, norm_zero]
    rcases Nat.mul_eq_zero.mp hq0 with h1 | h2
    · rw [h1]
      simp
    · rw [h2]
      simp
  · have h1 : 0 < q.1 := Nat.pos_of_ne_zero fun hz => by simp [hz] at hqpos
    have h2 : 0 < q.2 := Nat.pos_of_ne_zero fun hz => by simp [hz] at hqpos
    have hr1 : (0 : ℝ) < (q.1 : ℝ) := by exact_mod_cast h1
    have hr2 : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast h2
    have hprod : (0 : ℝ) < ((q.1 * q.2 : ℕ) : ℝ) * x := by
      have hcastpos : (0 : ℝ) < ((q.1 * q.2 : ℕ) : ℝ) := by exact_mod_cast hqpos
      exact mul_pos hcastpos hx
    have hterm := (hC (((q.1 * q.2 : ℕ) : ℝ) * x) hprod).2
    have hmu : ‖((moebius q.2 : ℤ) : ℂ)‖ ≤ 1 := by
      rcases moebius_eq_or q.2 with h1' | h1' | h1' <;> rw [h1'] <;> norm_num
    rw [deningerMobiusPair, if_neg h1.ne', norm_mul]
    have hstep : ‖((moebius q.2 : ℤ) : ℂ)‖ * ‖deningerLogPull h (((q.1 * q.2 : ℕ) : ℝ) * x)‖
        ≤ 1 * ‖deningerLogPull h (((q.1 * q.2 : ℕ) : ℝ) * x)‖ :=
      mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
    rw [one_mul] at hstep
    refine le_trans hstep (le_trans hterm (le_of_eq ?_))
    have hcast : ((q.1 * q.2 : ℕ) : ℝ) = (q.1 : ℝ) * (q.2 : ℝ) := by push_cast; ring
    rw [hcast, mul_pow, mul_pow]
    field_simp

/-- The divisor sum of the Möbius function detects the unit. -/
theorem deningerMobiusDivisorSumInt (N : ℕ) :
    (∑ d ∈ N.divisors, (moebius (N / d) : ℤ)) = if N = 1 then 1 else 0 := by
  classical
  rw [Nat.sum_div_divisors N (fun d => (moebius d : ℤ))]
  have hmul := congrArg (fun f : ArithmeticFunction ℤ => f N)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at hmul
  exact hmul

/-- The divisor sum of the Möbius function detects the unit, over the complex numbers. -/
theorem deningerMobiusDivisorSum (N : ℕ) :
    (∑ d ∈ N.divisors, ((moebius (N / d) : ℤ) : ℂ)) = if N = 1 then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (deningerMobiusDivisorSumInt N)
  rw [Int.cast_sum] at h
  rw [h]
  by_cases hN : N = 1 <;> simp [hN]

/-- **The pointwise Möbius right inverse.**  Summing the canonical Möbius preimage over the
dilation orbit returns the pullback: `∑_{n ≥ 1} f_h(nx) = H_h(x)` for every `x > 0`.  The whole
content is the product-fibre interchange together with `∑_{d | N} μ(N/d) = [N = 1]`. -/
theorem deningerMobius_rightInverse {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) {x : ℝ}
    (hx : 0 < x) :
    deningerRaySum (deningerMobiusPreimage h) x = deningerLogPull h x := by
  classical
  have hsum := deningerMobiusPair_summable hh hx
  set Φ : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + 1, p.2) with hΦ
  have hΦinj : Function.Injective Φ := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hcd
    have h1 : a + 1 = c + 1 := congrArg Prod.fst hcd
    have h2 : b = d := congrArg Prod.snd hcd
    have hac : a = c := by omega
    rw [hac, h2]
  have hsupp : Function.support (deningerMobiusPair h x) ⊆ Set.range Φ := by
    rintro ⟨a, b⟩ hab
    have ha : a ≠ 0 := by
      intro h0
      refine hab ?_
      rw [deningerMobiusPair, if_pos h0]
    refine ⟨(a - 1, b), ?_⟩
    have : a - 1 + 1 = a := by omega
    rw [hΦ]
    exact Prod.ext this rfl
  have hshift : ∀ p : ℕ × ℕ, deningerMobiusPair h x (Φ p)
      = ((moebius p.2 : ℤ) : ℂ) * deningerLogPull h ((p.2 : ℝ) * (((p.1 : ℝ) + 1) * x)) := by
    intro p
    rw [hΦ, deningerMobiusPair, if_neg (Nat.succ_ne_zero p.1)]
    congr 2
    push_cast
    ring
  have hleft : (∑' p : ℕ × ℕ, deningerMobiusPair h x (Φ p))
      = deningerRaySum (deningerMobiusPreimage h) x := by
    have hprod := (hsum.comp_injective hΦinj).tsum_prod
    rw [show (∑' p : ℕ × ℕ, deningerMobiusPair h x (Φ p))
        = ∑' p : ℕ × ℕ, (deningerMobiusPair h x ∘ Φ) p from rfl, hprod, deningerRaySum]
    refine tsum_congr fun n => ?_
    rw [deningerMobiusPreimage]
    exact tsum_congr fun k => hshift (n, k)
  have hmid : (∑' p : ℕ × ℕ, deningerMobiusPair h x (Φ p))
      = ∑' q : ℕ × ℕ, deningerMobiusPair h x q := hΦinj.tsum_eq hsupp
  have hright := deningerProductFibre_tsum hsum
    (fun q hq => deningerMobiusPair_zero h x hq)
  have hfib : ∀ N : ℕ, (∑ d ∈ N.divisors, deningerMobiusPair h x (d, N / d))
      = (if N = 1 then (1 : ℂ) else 0) * deningerLogPull h ((N : ℝ) * x) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hterm : ∀ d ∈ N.divisors, deningerMobiusPair h x (d, N / d)
          = ((moebius (N / d) : ℤ) : ℂ) * deningerLogPull h ((N : ℝ) * x) := by
        intro d hd
        have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
        have hdvd : d * (N / d) = N := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
        rw [deningerMobiusPair, if_neg hd0]
        congr 3
        exact congrArg (fun m : ℕ => (m : ℝ)) hdvd
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, deningerMobiusDivisorSum]
  have hfinal : (∑' N : ℕ, (if N = 1 then (1 : ℂ) else 0) *
      deningerLogPull h ((N : ℝ) * x)) = deningerLogPull h x := by
    rw [tsum_eq_single 1 (fun N hN => by rw [if_neg hN, zero_mul])]
    rw [if_pos rfl, one_mul, Nat.cast_one, one_mul]
  rw [← hleft, hmid, hright, tsum_congr hfib, hfinal]

/-! ## The Möbius--log divisor sum -/

/-- The divisor sum of the Möbius function detects the unit, over the reals. -/
theorem deningerMobiusDivisorSumReal (N : ℕ) :
    (∑ d ∈ N.divisors, ((moebius d : ℤ) : ℝ)) = if N = 1 then 1 else 0 := by
  have hint := deningerMobiusDivisorSumInt N
  rw [Nat.sum_div_divisors N (fun d => (moebius d : ℤ))] at hint
  have h := congrArg (fun z : ℤ => (z : ℝ)) hint
  rw [Int.cast_sum] at h
  rw [h]
  by_cases hN : N = 1 <;> simp [hN]

/-- **The Möbius--log divisor sum.**  `∑_{d | n} μ(d) log d = -Λ(n)`: writing `log d` as
`log n - log(n/d)` splits the sum into the Möbius unit detector, which is killed by `log n`, and
the Möbius--log convolution, which is the von Mangoldt weight. -/
theorem deningerMobiusLogDivisorSum (n : ℕ) :
    (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)) = -vonMangoldt n := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact this.ne'
    have hsplit : ∀ d ∈ n.divisors,
        ((moebius d : ℤ) : ℝ) * Real.log (d : ℝ)
          = ((moebius d : ℤ) : ℝ) * Real.log (n : ℝ)
            - ((moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)) := by
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
        rw [Nat.cast_div hdvd (by exact_mod_cast hd0)]
      have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
      rw [hcast, Real.log_div hn0 hdr]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul,
      deningerMobiusDivisorSumReal]
    have hzero : (if n = 1 then (1 : ℝ) else 0) * Real.log (n : ℝ) = 0 := by
      by_cases h1 : n = 1
      · rw [if_pos h1, h1]
        simp
      · rw [if_neg h1, zero_mul]
    rw [hzero, zero_sub, ← Sieve.vonMangoldt_eq_sum_moebius_mul_log n]

end

end RHTower
