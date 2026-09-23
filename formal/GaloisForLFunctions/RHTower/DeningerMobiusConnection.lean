import GaloisForLFunctions.RHTower.DeningerMobiusRightInverse
import GaloisForLFunctions.RHTower.DeningerCausalVonMangoldtWall

/-!
# The Möbius--von Mangoldt connection on the positive ray

Inverting the Möbius--log divisor sum turns it into the other convolution order,
`Λ * μ = -(μ · log)`, and feeding that through the product-fibre interchange gives the connection
identity on the ray:

`∑_m Λ(m) f_h(mx) = -∑_n μ(n) log n · H_h(nx)`.

So the Möbius derivative of the canonical preimage carries the whole Euler connection, with the
leading pole already cancelled — the von Mangoldt current is present, not lost.

* `deningerNegMobiusLog`, `deningerNegMobiusLog_mul_zeta` : the Möbius--log function and `(44)`.
* `deningerVonMangoldt_mul_moebius` : **`Λ * μ = -μ · log`.**
* `deningerMobius_connection` : **the connection identity on the ray.**
-/

namespace RHTower

open SchwartzMap ArithmeticFunction

noncomputable section

/-! ## The arithmetic identity -/

/-- The negated Möbius--log arithmetic function `n ↦ -μ(n) log n`.  Carrying the sign inside the
pointwise product keeps every convolution identity below sign-free. -/
def deningerNegMobiusLog : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul (↑moebius) (-ArithmeticFunction.log)

@[simp]
theorem deningerNegMobiusLog_apply (n : ℕ) :
    deningerNegMobiusLog n = -(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) := by
  rw [deningerNegMobiusLog, ArithmeticFunction.pmul_apply, ArithmeticFunction.neg_apply,
    ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply, mul_neg]

/-- **`(44)` in convolution form**: `(-μ · log) * ζ = Λ`. -/
theorem deningerNegMobiusLog_mul_zeta :
    deningerNegMobiusLog * (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ)
      = ArithmeticFunction.vonMangoldt := by
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    Finset.sum_congr rfl (fun d (_ : d ∈ n.divisors) => deningerNegMobiusLog_apply d),
    Finset.sum_neg_distrib, deningerMobiusLogDivisorSum, neg_neg]

/-- **The inverted connection identity** `Λ * μ = -μ · log`.  Convolving `(44)` with `μ` and using
`ζ * μ = 1` swaps the convolution order. -/
theorem deningerVonMangoldt_mul_moebius :
    ArithmeticFunction.vonMangoldt * (↑moebius : ArithmeticFunction ℝ)
      = deningerNegMobiusLog := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f * (↑moebius : ArithmeticFunction ℝ))
    deningerNegMobiusLog_mul_zeta
  rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one] at h
  exact h.symm

/-- The divisor form of the inverted identity. -/
theorem deningerVonMangoldtMoebiusDivisorSum (N : ℕ) :
    (∑ d ∈ N.divisors, vonMangoldt d * ((moebius (N / d) : ℤ) : ℝ))
      = -(((moebius N : ℤ) : ℝ) * Real.log (N : ℝ)) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f N) deningerVonMangoldt_mul_moebius
  simp only [ArithmeticFunction.mul_apply, deningerNegMobiusLog_apply,
    ArithmeticFunction.intCoe_apply] at h
  rw [← h]
  exact (Nat.sum_divisorsAntidiagonal
    (fun a b => vonMangoldt a * ((moebius b : ℤ) : ℝ))).symm

/-! ## The connection identity on the ray -/

/-- The Möbius derivative of a cochain on the positive ray. -/
def deningerMobiusDerivative (h : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ∑' n : ℕ, ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
    deningerLogPull h ((n : ℝ) * x)

/-- The two-variable family whose fibre sums are the von Mangoldt current. -/
private def deningerConnectionPair (h : 𝓢(ℝ, ℂ)) (x : ℝ) (q : ℕ × ℕ) : ℂ :=
  ((vonMangoldt q.1 : ℝ) : ℂ) * (((moebius q.2 : ℤ) : ℂ) *
    deningerLogPull h (((q.1 * q.2 : ℕ) : ℝ) * x))

private theorem deningerConnectionPair_zero (h : 𝓢(ℝ, ℂ)) (x : ℝ) {q : ℕ × ℕ}
    (hq : q.1 * q.2 = 0) : deningerConnectionPair h x q = 0 := by
  rw [deningerConnectionPair]
  rcases Nat.mul_eq_zero.mp hq with h1 | h2
  · rw [h1]
    simp
  · rw [h2]
    simp

private theorem deningerConnectionPair_summable {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerExpSchwartz) {x : ℝ} (hx : 0 < x) :
    Summable (deningerConnectionPair h x) := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le_inv_sq hh
  have hxsq : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
  have hsq : Summable fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hpair : Summable fun q : ℕ × ℕ =>
      (C / x ^ (2 : ℕ)) * ((vonMangoldt q.1 / (q.1 : ℝ) ^ (2 : ℕ)) * (1 / (q.2 : ℝ) ^ (2 : ℕ))) := by
    refine Summable.mul_left _ ?_
    exact Summable.mul_of_nonneg (f := fun n : ℕ => vonMangoldt n / (n : ℝ) ^ (2 : ℕ))
      (g := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) deningerVonMangoldt_summable_div_sq hsq
      (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) (fun n => by positivity)
  refine Summable.of_norm_bounded hpair fun q => ?_
  rcases Nat.eq_zero_or_pos (q.1 * q.2) with hq0 | hqpos
  · rw [deningerConnectionPair_zero h x hq0, norm_zero]
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
    rw [deningerConnectionPair, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg]
    have hinner : ‖((moebius q.2 : ℤ) : ℂ)‖ *
        ‖deningerLogPull h (((q.1 * q.2 : ℕ) : ℝ) * x)‖
        ≤ C / (((q.1 : ℝ) * (q.2 : ℝ)) * x) ^ (2 : ℕ) := by
      have hstep : ‖((moebius q.2 : ℤ) : ℂ)‖ *
          ‖deningerLogPull h (((q.1 * q.2 : ℕ) : ℝ) * x)‖
          ≤ 1 * ‖deningerLogPull h (((q.1 * q.2 : ℕ) : ℝ) * x)‖ :=
        mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
      rw [one_mul] at hstep
      refine le_trans hstep (le_trans hterm (le_of_eq ?_))
      have hcast : ((q.1 * q.2 : ℕ) : ℝ) = (q.1 : ℝ) * (q.2 : ℝ) := by push_cast; ring
      rw [hcast]
    refine le_trans (mul_le_mul_of_nonneg_left hinner vonMangoldt_nonneg) (le_of_eq ?_)
    rw [mul_pow, mul_pow]
    field_simp

/-- **The connection identity on the ray.**  The von Mangoldt current of the canonical Möbius
preimage is the Möbius derivative: `∑_m Λ(m) f_h(mx) = -∑_n μ(n) log n · H_h(nx)`. -/
theorem deningerMobius_connection {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) {x : ℝ}
    (hx : 0 < x) :
    (∑' m : ℕ, ((vonMangoldt m : ℝ) : ℂ) * deningerMobiusPreimage h ((m : ℝ) * x))
      = deningerMobiusDerivative h x := by
  classical
  have hsum := deningerConnectionPair_summable hh hx
  have hleft : (∑' q : ℕ × ℕ, deningerConnectionPair h x q)
      = ∑' m : ℕ, ((vonMangoldt m : ℝ) : ℂ) * deningerMobiusPreimage h ((m : ℝ) * x) := by
    rw [hsum.tsum_prod]
    refine tsum_congr fun m => ?_
    rw [deningerMobiusPreimage, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [deningerConnectionPair]
    congr 2
    push_cast
    ring
  have hright := deningerProductFibre_tsum hsum
    (fun q hq => deningerConnectionPair_zero h x hq)
  have hfib : ∀ N : ℕ, (∑ d ∈ N.divisors, deningerConnectionPair h x (d, N / d))
      = ((-(((moebius N : ℤ) : ℝ) * Real.log (N : ℝ)) : ℝ) : ℂ) *
        deningerLogPull h ((N : ℝ) * x) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hterm : ∀ d ∈ N.divisors, deningerConnectionPair h x (d, N / d)
          = ((vonMangoldt d * ((moebius (N / d) : ℤ) : ℝ) : ℝ) : ℂ) *
            deningerLogPull h ((N : ℝ) * x) := by
        intro d hd
        have hdvd : d * (N / d) = N := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
        rw [deningerConnectionPair,
          show (((d, N / d) : ℕ × ℕ).1 * ((d, N / d) : ℕ × ℕ).2 : ℕ) = N from hdvd]
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      congr 1
      rw [← Complex.ofReal_sum, deningerVonMangoldtMoebiusDivisorSum]
  rw [← hleft, hright, tsum_congr hfib, deningerMobiusDerivative]

end

end RHTower
