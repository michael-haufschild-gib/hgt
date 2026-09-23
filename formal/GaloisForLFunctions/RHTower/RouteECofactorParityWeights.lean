import GaloisForLFunctions.RHTower.RouteECofactorParityBalance
import GaloisForLFunctions.RHTower.Sieve.MertensSecond
import GaloisForLFunctions.RHTower.Sieve.ChernoffTails

/-!
# Parity balance at an arbitrary weight, and the band's Euler factor

The pairing `s ↔ 2s` of `RouteECofactorParityBalance` costs a factor two in *any* weight that
doubling decreases by at most a half.  Both weights the cofactor card uses — `1/t` for its `(9)`
and `1/√t` for its `(7)` — qualify, the second with room to spare.

The other half of `(7)` and `(9)` is that excluding a full polylogarithmic band of primes only
multiplies the unsigned squarefree main term by a fixed positive Euler factor.  That factor is
bounded below by `(log P/log Q)·e^{-(L+U)}` by Mertens' second theorem, hence by a positive
constant whenever the band's endpoints have comparable logarithms — which is exactly the card's
`(log U)^{a₀} ≤ p ≤ 2(log U)^{a₁}`.
-/

open Finset

namespace RHTower

namespace CofactorParity

variable {Band : ℕ → Prop} [DecidablePred Band]

/-- **The parity-balance inequality at an arbitrary weight.** -/
theorem half_sum_oddBase_le_sum_parityClass_weight (hband : ¬ Band 2) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (T : ℕ) (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hwhalf : ∀ s : ℕ, 1 ≤ s → (1 / 2 : ℝ) * w s ≤ w (2 * s)) :
    (1 / 2 : ℝ) * ∑ s ∈ oddBase Band T, w s ≤ ∑ t ∈ parityClass Band σ T, w t := by
  classical
  have hsub : (oddBase Band T).image (pairMap σ) ⊆ parityClass Band σ T := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    exact pairMap_mem hband hσ hs
  have himg : ∑ q ∈ (oddBase Band T).image (pairMap σ), w q
      = ∑ s ∈ oddBase Band T, w (pairMap σ s) :=
    Finset.sum_image (f := w) pairMap_injOn
  have hterm : ∀ s ∈ oddBase Band T, (1 / 2 : ℝ) * w s ≤ w (pairMap σ s) := by
    intro s hs
    have hs1 : 1 ≤ s := ((mem_oddBase_iff).mp hs).1.1
    rw [pairMap]
    split_ifs with h
    · linarith [hw0 s]
    · exact hwhalf s hs1
  calc (1 / 2 : ℝ) * ∑ s ∈ oddBase Band T, w s
      = ∑ s ∈ oddBase Band T, (1 / 2 : ℝ) * w s := by rw [Finset.mul_sum]
    _ ≤ ∑ s ∈ oddBase Band T, w (pairMap σ s) := Finset.sum_le_sum hterm
    _ = ∑ q ∈ (oddBase Band T).image (pairMap σ), w q := himg.symm
    _ ≤ ∑ t ∈ parityClass Band σ T, w t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hw0 i

/-- **Parity balance for the card's square-root weight `(7)`.** -/
theorem half_sum_oddBase_le_sum_parityClass_sqrt (hband : ¬ Band 2) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (T : ℕ) :
    (1 / 2 : ℝ) * ∑ s ∈ oddBase Band T, (Real.sqrt s)⁻¹
      ≤ ∑ t ∈ parityClass Band σ T, (Real.sqrt t)⁻¹ := by
  refine half_sum_oddBase_le_sum_parityClass_weight hband hσ T _
    (fun n => by positivity) ?_
  intro s hs
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hsq : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hcast : ((2 * s : ℕ) : ℝ) = 2 * (s : ℝ) := by push_cast; ring
  rw [hcast, Real.sqrt_mul (by norm_num) (s : ℝ)]
  have hle : Real.sqrt 2 * Real.sqrt s ≤ 2 * Real.sqrt s := by
    have h2 : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [hsq]
  have hpos : (0 : ℝ) < Real.sqrt 2 * Real.sqrt s := by positivity
  have hinv := one_div_le_one_div_of_le hpos hle
  rw [one_div, one_div] at hinv
  have hval : ((2 : ℝ) * Real.sqrt s)⁻¹ = (1 / 2 : ℝ) * (Real.sqrt s)⁻¹ := by
    rw [mul_inv]
    norm_num
  linarith [hinv, hval]

/-! ## The band's Euler factor -/

/-- An Euler product over a finite prime set is at most the exponential of its reciprocal sum. -/
theorem prod_one_add_inv_le_exp (s : Finset ℕ) :
    ∏ p ∈ s, (1 + ((p : ℝ))⁻¹) ≤ Real.exp (∑ p ∈ s, ((p : ℝ))⁻¹) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
  have := Real.add_one_le_exp ((p : ℝ))⁻¹
  linarith

/-- **The band's Euler factor is bounded below by the exponential of its reciprocal mass.** -/
theorem exp_neg_le_prod_inv (s : Finset ℕ) :
    Real.exp (-∑ p ∈ s, ((p : ℝ))⁻¹) ≤ (∏ p ∈ s, (1 + ((p : ℝ))⁻¹))⁻¹ := by
  have hpos : (0 : ℝ) < ∏ p ∈ s, (1 + ((p : ℝ))⁻¹) :=
    Finset.prod_pos fun p _ => by positivity
  rw [Real.exp_neg]
  exact inv_anti₀ hpos (prod_one_add_inv_le_exp s)

/-- **The band's Euler factor, explicitly.**  Excluding every prime of `(P, Q]` multiplies the
unsigned squarefree main term by at least `(log P/log Q)·e^{-(L+U)}`, so by a positive constant
whenever the band's endpoints have comparable logarithms. -/
theorem band_euler_factor_ge {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (Real.log P / Real.log Q)
        * Real.exp (-(Sieve.mertensSecondLowerConst + Sieve.mertensSecondUpperConst))
      ≤ (∏ p ∈ Sieve.bigPrimeSet P Q, (1 + ((p : ℝ))⁻¹))⁻¹ := by
  have hQ : 2 ≤ Q := le_trans hP hPQ
  have hlogP : (0 : ℝ) < Real.log P := by
    refine Real.log_pos ?_
    exact_mod_cast (by omega : 1 < P)
  have hlogQ : (0 : ℝ) < Real.log Q := by
    refine Real.log_pos ?_
    exact_mod_cast (by omega : 1 < Q)
  have hmass : ∑ p ∈ Sieve.bigPrimeSet P Q, ((p : ℝ))⁻¹
      ≤ Sieve.logLog Q - Sieve.logLog P
        + (Sieve.mertensSecondLowerConst + Sieve.mertensSecondUpperConst) := by
    have hsplit : ∑ p ∈ Sieve.bigPrimeSet P Q, 1 / (p : ℝ)
        = Sieve.mertensS Q - Sieve.mertensS P := Sieve.sum_inv_bigPrimeSet P Q hPQ
    have hup := Sieve.mertensS_le hQ
    have hlow := Sieve.le_mertensS hP
    have hcast : ∑ p ∈ Sieve.bigPrimeSet P Q, ((p : ℝ))⁻¹
        = ∑ p ∈ Sieve.bigPrimeSet P Q, 1 / (p : ℝ) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [one_div]
    rw [hcast, hsplit]
    linarith
  refine le_trans ?_ (exp_neg_le_prod_inv (Sieve.bigPrimeSet P Q))
  have hstep : -(Sieve.logLog Q - Sieve.logLog P
        + (Sieve.mertensSecondLowerConst + Sieve.mertensSecondUpperConst))
      ≤ -∑ p ∈ Sieve.bigPrimeSet P Q, ((p : ℝ))⁻¹ := by linarith
  refine le_trans (le_of_eq ?_) (Real.exp_le_exp.2 hstep)
  rw [show -(Sieve.logLog Q - Sieve.logLog P
        + (Sieve.mertensSecondLowerConst + Sieve.mertensSecondUpperConst))
      = (Sieve.logLog P - Sieve.logLog Q)
        + -(Sieve.mertensSecondLowerConst + Sieve.mertensSecondUpperConst) by ring,
    Real.exp_add, Sieve.logLog, Sieve.logLog, Real.exp_sub,
    Real.exp_log hlogP, Real.exp_log hlogQ]

end CofactorParity

end RHTower
