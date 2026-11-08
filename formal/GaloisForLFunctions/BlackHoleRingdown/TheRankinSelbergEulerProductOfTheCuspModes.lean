import GaloisForLFunctions.BlackHoleRingdown.TheEulerProductOfTheCuspModes

/-!
# The Rankin–Selberg Euler product of the cusp modes

Let `σ, τ` be normalized Hecke sequences with eigenvalues `λ_p`, `λ'_p`
(`σ(pn) = λ_p σ(n) − [p ∣ n] σ(n/p)`). At a prime the Satake roots are `α₁α₂ = 1`,
`α₁ + α₂ = λ_p` and `β₁β₂ = 1`, `β₁ + β₂ = λ'_p`, and the Rankin–Selberg local polynomial is

  `Q_p(x) = Π_{i,j} (1 − α_iβ_j x) = 1 − λλ'x + (λ² + λ'² − 2)x² − λλ'x³ + x⁴`   (`rsLocal`).

* **Four-term recursion** (`HeckeRec.prod_pow_rec`): `c_e = σ(p^e)τ(p^e)` obeys the recursion of `Q_p`.
* **Local factor** (`HeckeRec.rankinSelberg_local_factor`): `Q_p(x) Σ_e c_e x^e = 1 − x²`.
* **Euler product** (`HeckeRec.rankinSelberg_euler`): for absolutely convergent `Σ σ(n)τ(n)n^{−s}`,
  `Re s > 0`, `Σ_n σ(n)τ(n) n^{−s} = Π_p (1 − p^{−2s}) / Q_p(p^{−s})`.
* **The symmetric square** (`rsLocal_self`, `HeckeRec.rankinSelberg_euler_self`): for `τ = σ`,
  `Q_p(x) = (1 − x)² (1 − (λ² − 2)x + x²)`, so
  `Σ σ(n)² n^{−s} = Π_p (1 + p^{−s}) / ((1 − p^{−s})(1 − (λ_p² − 2)p^{−s} + p^{−2s}))`,
  which is `ζ(s) L(Sym² g, s) / ζ(2s)` with `L_p(Sym² g, s)⁻¹ = (1 − α₁²x)(1 − x)(1 − α₂²x)`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown.CuspEuler

variable {lam lam' : ℕ → ℂ} {σ τ : ℕ → ℂ}

/-- The Rankin–Selberg local polynomial `1 − abx + (a² + b² − 2)x² − abx³ + x⁴`. -/
def rsLocal (a b x : ℂ) : ℂ := 1 - a * b * x + (a ^ 2 + b ^ 2 - 2) * x ^ 2 - a * b * x ^ 3 + x ^ 4

/-- **The four-term recursion** of the product of two Hecke prime-power sequences. -/
theorem HeckeRec.prod_pow_rec (hσ : HeckeRec lam σ) (hτ : HeckeRec lam' τ) {p : ℕ} (hp : p.Prime)
    (e : ℕ) :
    σ (p ^ (e + 4)) * τ (p ^ (e + 4)) =
      lam p * lam' p * (σ (p ^ (e + 3)) * τ (p ^ (e + 3))) -
        (lam p ^ 2 + lam' p ^ 2 - 2) * (σ (p ^ (e + 2)) * τ (p ^ (e + 2))) +
        lam p * lam' p * (σ (p ^ (e + 1)) * τ (p ^ (e + 1))) - σ (p ^ e) * τ (p ^ e) := by
  have a2 := hσ.pow_succ_succ hp e
  have a3 := hσ.pow_succ_succ hp (e + 1)
  have a4 := hσ.pow_succ_succ hp (e + 2)
  have b2 := hτ.pow_succ_succ hp e
  have b3 := hτ.pow_succ_succ hp (e + 1)
  have b4 := hτ.pow_succ_succ hp (e + 2)
  rw [show e + 1 + 2 = e + 3 by ring] at a3 b3
  rw [show e + 2 + 2 = e + 4 by ring, show e + 2 + 1 = e + 3 by ring] at a4 b4
  rw [a4, b4, a3, b3, a2, b2]
  ring

/-- **The Rankin–Selberg local factor**: `Q_p(x) Σ_e σ(p^e)τ(p^e) x^e = 1 − x²`. -/
theorem HeckeRec.rankinSelberg_local_factor (hσ : HeckeRec lam σ) (hτ : HeckeRec lam' τ)
    (h1σ : σ 1 = 1) (h1τ : τ 1 = 1) {p : ℕ} (hp : p.Prime) {x : ℂ}
    (hs : Summable fun e : ℕ => σ (p ^ e) * τ (p ^ e) * x ^ e) :
    rsLocal (lam p) (lam' p) x * ∑' e : ℕ, σ (p ^ e) * τ (p ^ e) * x ^ e = 1 - x ^ 2 := by
  set a : ℕ → ℂ := fun e => σ (p ^ e) * τ (p ^ e) * x ^ e with ha
  have hs1 : Summable fun e => a (e + 1) := (summable_nat_add_iff 1).2 hs
  have hs2 : Summable fun e => a (e + 2) := (summable_nat_add_iff 2).2 hs
  have hs3 : Summable fun e => a (e + 3) := (summable_nat_add_iff 3).2 hs
  have hS1 : ∑' e, a e = a 0 + ∑' e, a (e + 1) := hs.tsum_eq_zero_add
  have hS2 : ∑' e, a (e + 1) = a 1 + ∑' e, a (e + 2) := hs1.tsum_eq_zero_add
  have hS3 : ∑' e, a (e + 2) = a 2 + ∑' e, a (e + 3) := hs2.tsum_eq_zero_add
  have hS4 : ∑' e, a (e + 3) = a 3 + ∑' e, a (e + 4) := hs3.tsum_eq_zero_add
  set u : ℂ := lam p ^ 2 + lam' p ^ 2 - 2 with hu
  set v : ℂ := lam p * lam' p with hv
  have hrec : ∀ e, a (e + 4) = v * x * a (e + 3) - u * x ^ 2 * a (e + 2) +
      v * x ^ 3 * a (e + 1) - x ^ 4 * a e := fun e => by
    simp only [ha]
    rw [hσ.prod_pow_rec hτ hp e]
    ring
  have hS5 : ∑' e, a (e + 4) = v * x * ∑' e, a (e + 3) - u * x ^ 2 * ∑' e, a (e + 2) +
      v * x ^ 3 * ∑' e, a (e + 1) - x ^ 4 * ∑' e, a e := by
    rw [tsum_congr hrec, ((((hs3.mul_left _).sub (hs2.mul_left _)).add (hs1.mul_left _)).tsum_sub
      (hs.mul_left _)), (((hs3.mul_left _).sub (hs2.mul_left _)).tsum_add (hs1.mul_left _)),
      (hs3.mul_left _).tsum_sub (hs2.mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left,
      tsum_mul_left]
  -- the first four coefficients
  have hp1 : σ p = lam p := hσ.prime h1σ hp
  have hq1 : τ p = lam' p := hτ.prime h1τ hp
  have hp2 : σ (p ^ 2) = lam p ^ 2 - 1 := by
    have := hσ.pow_succ_succ hp 0
    simp only [zero_add, pow_one, pow_zero, h1σ, hp1] at this
    rw [this]; ring
  have hq2 : τ (p ^ 2) = lam' p ^ 2 - 1 := by
    have := hτ.pow_succ_succ hp 0
    simp only [zero_add, pow_one, pow_zero, h1τ, hq1] at this
    rw [this]; ring
  have hp3 : σ (p ^ 3) = lam p ^ 3 - 2 * lam p := by
    have := hσ.pow_succ_succ hp 1
    rw [show 1 + 2 = 3 by rfl, show 1 + 1 = 2 by rfl, hp2, pow_one, hp1] at this
    rw [this]; ring
  have hq3 : τ (p ^ 3) = lam' p ^ 3 - 2 * lam' p := by
    have := hτ.pow_succ_succ hp 1
    rw [show 1 + 2 = 3 by rfl, show 1 + 1 = 2 by rfl, hq2, pow_one, hq1] at this
    rw [this]; ring
  have ha0 : a 0 = 1 := by simp [ha, h1σ, h1τ]
  have ha1 : a 1 = v * x := by simp [ha, hp1, hq1, hv]
  have ha2 : a 2 = (lam p ^ 2 - 1) * (lam' p ^ 2 - 1) * x ^ 2 := by simp only [ha, hp2, hq2]
  have ha3 : a 3 = (lam p ^ 3 - 2 * lam p) * (lam' p ^ 3 - 2 * lam' p) * x ^ 3 := by
    simp only [ha, hp3, hq3]
  change rsLocal (lam p) (lam' p) x * ∑' e, a e = 1 - x ^ 2
  rw [ha0] at hS1
  rw [ha1] at hS2
  rw [ha2] at hS3
  rw [ha3] at hS4
  unfold rsLocal
  rw [← hv, show lam p ^ 2 + lam' p ^ 2 - 2 = u from rfl]
  linear_combination (1 - v * x + u * x ^ 2 - v * x ^ 3) * hS1 + (1 - v * x + u * x ^ 2) * hS2 +
    (1 - v * x) * hS3 + hS4 + hS5

/-- The local polynomial does not vanish where the local series converges and `x² ≠ 1`. -/
theorem HeckeRec.rsLocal_ne_zero (hσ : HeckeRec lam σ) (hτ : HeckeRec lam' τ)
    (h1σ : σ 1 = 1) (h1τ : τ 1 = 1) {p : ℕ} (hp : p.Prime) {x : ℂ} (hx : x ^ 2 ≠ 1)
    (hs : Summable fun e : ℕ => σ (p ^ e) * τ (p ^ e) * x ^ e) :
    rsLocal (lam p) (lam' p) x ≠ 0 := fun h0 => by
  have := hσ.rankinSelberg_local_factor hτ h1σ h1τ hp hs
  rw [h0, zero_mul] at this
  exact hx (sub_eq_zero.mp this.symm).symm

/-- **The Rankin–Selberg Euler product** of two normalized Hecke sequences, as a convergent product:
`Π_p (1 − p^{−2s}) / Q_p(p^{−s}) = Σ_n σ(n)τ(n) n^{−s}`. -/
theorem HeckeRec.rankinSelberg_hasProd (hσ : HeckeRec lam σ) (hτ : HeckeRec lam' τ)
    (h1σ : σ 1 = 1) (h1τ : τ 1 = 1) (h0 : σ 0 = 0) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable fun n : ℕ => ‖σ n * τ n * (n : ℂ) ^ (-s)‖) :
    HasProd (fun p : Nat.Primes =>
        (1 - ((p : ℂ) ^ (-s)) ^ 2) / rsLocal (lam p) (lam' p) ((p : ℂ) ^ (-s)))
      (∑' n : ℕ, σ n * τ n * (n : ℂ) ^ (-s)) := by
  set f : ℕ → ℂ := fun n => σ n * τ n * (n : ℂ) ^ (-s)
  have hf1 : f 1 = 1 := by simp [f, h1σ, h1τ]
  have hf0 : f 0 = 0 := by simp [f, h0]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [Nat.coprime_zero_left] at hmn
      subst hmn
      simp [hf1]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Nat.coprime_zero_right] at hmn
      subst hmn
      simp [hf1]
    simp only [f]
    rw [hσ.mul h1σ n m hm hn hmn, hτ.mul h1τ n m hm hn hmn, Nat.cast_mul,
      natCast_mul_natCast_cpow]
    ring
  have hlocal : ∀ p : Nat.Primes, ∑' e, f ((p : ℕ) ^ e) =
      (1 - ((p : ℂ) ^ (-s)) ^ 2) / rsLocal (lam p) (lam' p) ((p : ℂ) ^ (-s)) := by
    intro p
    have hpow : ∀ e : ℕ, f ((p : ℕ) ^ e) =
        σ ((p : ℕ) ^ e) * τ ((p : ℕ) ^ e) * ((p : ℂ) ^ (-s)) ^ e := fun e => by
      simp only [f]
      rw [Nat.cast_pow, ← natCast_cpow_natCast_mul, cpow_nat_mul]
    have hsp : Summable fun e : ℕ =>
        σ ((p : ℕ) ^ e) * τ ((p : ℕ) ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
      have := (hsum.of_norm.comp_injective (Nat.pow_right_injective p.prop.two_le))
      exact this.congr fun e => hpow e
    -- `|p^{−s}| < 1`, so `p^{−2s} ≠ 1`
    have hx : ((p : ℂ) ^ (-s)) ^ 2 ≠ 1 := by
      intro h1
      have hn := congrArg norm h1
      rw [norm_pow, norm_one, Complex.norm_natCast_cpow_of_pos p.prop.pos, neg_re] at hn
      have hlt : (p : ℝ) ^ (-s.re) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
      have : ((p : ℝ) ^ (-s.re)) ^ 2 < 1 := by
        have h0 : 0 ≤ (p : ℝ) ^ (-s.re) := by positivity
        nlinarith
      linarith
    rw [tsum_congr hpow]
    have hne := hσ.rsLocal_ne_zero hτ h1σ h1τ p.prop hx hsp
    refine ((div_eq_iff hne).mpr ?_).symm
    rw [mul_comm]
    exact (hσ.rankinSelberg_local_factor hτ h1σ h1τ p.prop hsp).symm
  have h := EulerProduct.eulerProduct_hasProd hf1 hmul hsum hf0
  rwa [show (fun p : Nat.Primes => ∑' e, f ((p : ℕ) ^ e)) = fun p : Nat.Primes =>
    (1 - ((p : ℂ) ^ (-s)) ^ 2) / rsLocal (lam p) (lam' p) ((p : ℂ) ^ (-s)) from
    funext hlocal] at h

/-- **The Rankin–Selberg Euler product** of two normalized Hecke sequences:
`Σ_n σ(n)τ(n) n^{−s} = Π_p (1 − p^{−2s}) / Q_p(p^{−s})`. -/
theorem HeckeRec.rankinSelberg_euler (hσ : HeckeRec lam σ) (hτ : HeckeRec lam' τ)
    (h1σ : σ 1 = 1) (h1τ : τ 1 = 1) (h0 : σ 0 = 0) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable fun n : ℕ => ‖σ n * τ n * (n : ℂ) ^ (-s)‖) :
    ∏' p : Nat.Primes, (1 - ((p : ℂ) ^ (-s)) ^ 2) / rsLocal (lam p) (lam' p) ((p : ℂ) ^ (-s)) =
      ∑' n : ℕ, σ n * τ n * (n : ℂ) ^ (-s) :=
  (hσ.rankinSelberg_hasProd hτ h1σ h1τ h0 hs hsum).tprod_eq

/-- **The diagonal local polynomial factors**: `Q_p(x) = (1 − x)² (1 − (λ² − 2)x + x²)`. -/
theorem rsLocal_self (a x : ℂ) : rsLocal a a x = (1 - x) ^ 2 * (1 - (a ^ 2 - 2) * x + x ^ 2) := by
  unfold rsLocal
  ring

/-- **The symmetric square.** For a normalized Hecke sequence,
`Σ_n σ(n)² n^{−s} = Π_p (1 + p^{−s}) / ((1 − p^{−s})(1 − (λ_p² − 2) p^{−s} + p^{−2s}))`,
the Euler product of `ζ(s) L(Sym² g, s) / ζ(2s)`. -/
theorem HeckeRec.rankinSelberg_euler_self (hσ : HeckeRec lam σ) (h1σ : σ 1 = 1) (h0 : σ 0 = 0)
    {s : ℂ} (hs : 0 < s.re) (hsum : Summable fun n : ℕ => ‖σ n * σ n * (n : ℂ) ^ (-s)‖) :
    ∏' p : Nat.Primes, (1 + (p : ℂ) ^ (-s)) /
        ((1 - (p : ℂ) ^ (-s)) * (1 - (lam p ^ 2 - 2) * (p : ℂ) ^ (-s) + ((p : ℂ) ^ (-s)) ^ 2)) =
      ∑' n : ℕ, σ n * σ n * (n : ℂ) ^ (-s) := by
  rw [← hσ.rankinSelberg_euler hσ h1σ h1σ h0 hs hsum]
  refine tprod_congr fun p => ?_
  set x : ℂ := (p : ℂ) ^ (-s)
  have hx1 : 1 - x ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h).symm
    rw [norm_one, Complex.norm_natCast_cpow_of_pos p.prop.pos, neg_re] at hn
    have hlt : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
    linarith
  rw [rsLocal_self, show 1 - x ^ 2 = (1 - x) * (1 + x) by ring, pow_two (1 - x),
    mul_assoc (1 - x) (1 - x), mul_div_mul_left _ _ hx1]

end GaloisForLFunctions.BlackHoleRingdown.CuspEuler
