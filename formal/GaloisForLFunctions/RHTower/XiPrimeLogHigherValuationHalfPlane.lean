import GaloisForLFunctions.RHTower.XiMassPrimeSquareBoundaryResidue

/-!
# Higher prime valuations below the prime-zeta wall

The prime-only logarithmic current stops converging at `Re s = 1`, but its valuation-`>= 2`
correction has the strictly larger half-plane of absolute convergence `Re s > 1/2`.  This file
proves that distinction directly.  It is the arithmetic separation needed by Route T: after the
first prime-zeta shift, higher valuations are holomorphic throughout the translated physical strip
and therefore cannot cancel a pole produced by a nontrivial zeta zero.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Two-scale prime/valuation summability.  Prime exponent `beta > 1` pays for the outer prime
sum; any positive valuation slope `alpha` pays for the inner geometric tail. -/
theorem summable_primeLog_mul_inv_rpow_mul_add
    (alpha beta : ℝ) (halpha : 0 < alpha) (hbeta : 1 < beta) :
    Summable (fun pk : Nat.Primes × ℕ =>
      Real.log (pk.1 : ℝ) *
        ((pk.1 : ℝ)⁻¹) ^ ((pk.2 : ℝ) * alpha + beta)) := by
  have hp0 (p : Nat.Primes) : 0 < (p : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr p.prop.pos)
  have hp1 (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast p.prop.one_lt)
  have hbase : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) * (p : ℝ) ^ (-beta)) := by
    have hAbs : Summable (fun p : Nat.Primes =>
        |Real.log (p : ℝ)| * (p : ℝ) ^ (-beta)) := by
      have h := (summable_abs_log_natCast_pow_mul_rpow_neg 1 beta hbeta).comp_injective
        (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
      simpa only [Function.comp_apply, pow_one] using! h
    apply hAbs.of_nonneg_of_le
    · intro p
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (by positivity)
    intro p
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hcoeff : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ beta) := by
    apply hbase.congr
    intro p
    rw [Real.inv_rpow (Nat.cast_nonneg _),
      Real.rpow_neg (Nat.cast_nonneg _)]
  have hr1 : ((2 : ℝ)⁻¹) ^ alpha < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) halpha
  let C : ℝ := (1 - ((2 : ℝ)⁻¹) ^ alpha)⁻¹
  have hmajor := hcoeff.mul_left C
  rw [summable_prod_of_nonneg (fun pk => mul_nonneg
    (Real.log_nonneg (by exact_mod_cast pk.1.prop.one_le)) (by positivity))]
  refine ⟨?_, ?_⟩
  · intro p
    have hratio0 : 0 ≤ ((p : ℝ)⁻¹) ^ alpha :=
      (Real.rpow_pos_of_pos (hp0 p) _).le
    have hratio1 : ((p : ℝ)⁻¹) ^ alpha < 1 :=
      Real.rpow_lt_one (hp0 p).le (hp1 p) halpha
    have hgeo := (summable_geometric_of_lt_one hratio0 hratio1).mul_left
      (Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ beta)
    apply hgeo.congr
    intro k
    rw [Real.rpow_add (hp0 p), show (k : ℝ) * alpha = alpha * k by ring,
      Real.rpow_mul_natCast (hp0 p).le]
    ring
  · apply hmajor.of_nonneg_of_le
      (fun p => tsum_nonneg fun k => mul_nonneg
        (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (by positivity))
    intro p
    have hratio0 : 0 ≤ ((p : ℝ)⁻¹) ^ alpha :=
      (Real.rpow_pos_of_pos (hp0 p) _).le
    have hratio1 : ((p : ℝ)⁻¹) ^ alpha < 1 :=
      Real.rpow_lt_one (hp0 p).le (hp1 p) halpha
    rw [show (fun k : ℕ => Real.log (p : ℝ) *
        ((p : ℝ)⁻¹) ^ ((k : ℝ) * alpha + beta)) =
        fun k => (Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ beta) *
          (((p : ℝ)⁻¹) ^ alpha) ^ k by
      funext k
      rw [Real.rpow_add (hp0 p), show (k : ℝ) * alpha = alpha * k by ring,
        Real.rpow_mul_natCast (hp0 p).le]
      ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hratio0 hratio1]
    have hp2inv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
      exact inv_anti₀ (by norm_num) (by exact_mod_cast p.prop.two_le)
    have hratioLe : ((p : ℝ)⁻¹) ^ alpha ≤ ((2 : ℝ)⁻¹) ^ alpha := by
      exact Real.rpow_le_rpow (by positivity) hp2inv halpha.le
    have hdenC : 0 < 1 - ((2 : ℝ)⁻¹) ^ alpha := sub_pos.mpr hr1
    have hinv : (1 - ((p : ℝ)⁻¹) ^ alpha)⁻¹ ≤ C := by
      dsimp only [C]
      exact inv_anti₀ hdenC (sub_le_sub_left hratioLe 1)
    have hcoeffNonneg :
        0 ≤ Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ beta :=
      mul_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (by positivity)
    calc
      Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ beta *
          (1 - ((p : ℝ)⁻¹) ^ alpha)⁻¹ ≤
          (Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ beta) * C :=
        mul_le_mul_of_nonneg_left hinv hcoeffNonneg
      _ = C * (Real.log (p : ℝ) * ((p : ℝ)⁻¹) ^ beta) := by ring

/-- Exact positive majorant for the higher-valuation logarithmic Euler current. -/
def xiPrimeLogHigherValuationHalfPlaneWeight
    (sigma : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  Real.log (pk.1 : ℝ) *
    ((pk.1 : ℝ)⁻¹) ^ (((pk.2 + 2 : ℕ) : ℝ) * sigma)

theorem summable_xiPrimeLogHigherValuationHalfPlaneWeight
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    Summable (xiPrimeLogHigherValuationHalfPlaneWeight sigma) := by
  have h := summable_primeLog_mul_inv_rpow_mul_add sigma (2 * sigma)
    (by linarith) (by linarith)
  apply h.congr
  rintro ⟨p, k⟩
  rw [xiPrimeLogHigherValuationHalfPlaneWeight]
  congr 2
  push_cast
  ring

/-- Norm of one higher-valuation von Mangoldt atom, valid without a half-plane assumption. -/
theorem norm_vonMangoldtLSeriesTerm_primePower_eq_halfPlaneWeight
    (s : ℂ) (pk : Nat.Primes × ℕ) :
    ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      s ((pk.1 : ℕ) ^ (pk.2 + 2))‖ =
      xiPrimeLogHigherValuationHalfPlaneWeight s.re pk := by
  have hpPow : 0 < (pk.1 : ℕ) ^ (pk.2 + 2) := pow_pos pk.1.prop.pos _
  have hpR : (1 : ℝ) < (pk.1 : ℝ) := by exact_mod_cast pk.1.prop.one_lt
  rw [LSeries.norm_term_eq, if_neg hpPow.ne',
    ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime pk.1.prop]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos hpR)]
  rw [xiPrimeLogHigherValuationHalfPlaneWeight, Nat.cast_pow,
    div_eq_mul_inv,
    ← Real.rpow_neg (by positivity : 0 ≤ ((pk.1 : ℝ) ^ (pk.2 + 2)))]
  congr 1
  rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (pk.1 : ℝ))]
  rw [Real.inv_rpow (by positivity : 0 ≤ (pk.1 : ℝ)),
    ← Real.rpow_neg (by positivity : 0 ≤ (pk.1 : ℝ))]
  congr 1
  ring

/-- **Half-plane improvement.**  Valuations at least two converge absolutely on `Re s > 1/2`,
although the valuation-one prime logarithmic series only converges on `Re s > 1`. -/
theorem summable_xiPrimeLogHigherValuation_term_of_half_lt_re
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun pk : Nat.Primes × ℕ =>
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        s ((pk.1 : ℕ) ^ (pk.2 + 2))) := by
  apply summable_norm_iff.mp
  exact (summable_xiPrimeLogHigherValuationHalfPlaneWeight hs).congr
    (fun pk => (norm_vonMangoldtLSeriesTerm_primePower_eq_halfPlaneWeight s pk).symm)

/-- The higher-valuation correction is holomorphic at every point of its larger convergence
half-plane.  Local uniformity uses a vertical line strictly between `1/2` and the target point. -/
theorem differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => xiPrimeLogHigherValuation z) s := by
  let c : ℝ := (s.re + 1 / 2) / 2
  let U : Set ℂ := {z : ℂ | c < z.re}
  have hc : 1 / 2 < c := by dsimp only [c]; linarith
  have hcs : c < s.re := by dsimp only [c]; linarith
  have hU : IsOpen U := by
    exact isOpen_lt (continuous_const : Continuous fun _ : ℂ => c) Complex.continuous_re
  have hsU : s ∈ U := by simpa only [U, Set.mem_setOf_eq] using hcs
  have hmajor := summable_xiPrimeLogHigherValuationHalfPlaneWeight hc
  have hterm : ∀ pk : Nat.Primes × ℕ,
      DifferentiableOn ℂ (fun z : ℂ =>
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          z ((pk.1 : ℕ) ^ (pk.2 + 2))) U := by
    intro pk
    have hn0 : (pk.1 : ℕ) ^ (pk.2 + 2) ≠ 0 :=
      (pow_pos pk.1.prop.pos _).ne'
    have heq : (fun z : ℂ =>
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          z ((pk.1 : ℕ) ^ (pk.2 + 2))) =
        fun z : ℂ =>
          (ArithmeticFunction.vonMangoldt ((pk.1 : ℕ) ^ (pk.2 + 2)) : ℂ) /
            ((((pk.1 : ℕ) ^ (pk.2 + 2) : ℕ) : ℂ) ^ z) := by
      funext z
      rw [LSeries.term_of_ne_zero hn0]
    rw [heq]
    intro z hz
    have hn0C : ((((pk.1 : ℕ) ^ (pk.2 + 2) : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast hn0
    have hpow : DifferentiableAt ℂ
        (fun w : ℂ => ((((pk.1 : ℕ) ^ (pk.2 + 2) : ℕ) : ℂ) ^ w)) z :=
      differentiableAt_id.const_cpow (Or.inl hn0C)
    have hden : ((((pk.1 : ℕ) ^ (pk.2 + 2) : ℕ) : ℂ) ^ z) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hn0C)
    exact ((differentiableAt_const
      (c := (ArithmeticFunction.vonMangoldt ((pk.1 : ℕ) ^ (pk.2 + 2)) : ℂ))).div
        hpow hden).differentiableWithinAt
  have hbound : ∀ (pk : Nat.Primes × ℕ) (z : ℂ), z ∈ U →
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          z ((pk.1 : ℕ) ^ (pk.2 + 2))‖ ≤
        xiPrimeLogHigherValuationHalfPlaneWeight c pk := by
    intro pk z hz
    have hcz : c ≤ z.re := by simpa only [U, Set.mem_setOf_eq] using hz.le
    calc
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          z ((pk.1 : ℕ) ^ (pk.2 + 2))‖ ≤
          ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (c : ℂ) ((pk.1 : ℕ) ^ (pk.2 + 2))‖ :=
        LSeries.norm_term_le_of_re_le_re _ (by simpa using hcz) _
      _ = xiPrimeLogHigherValuationHalfPlaneWeight c pk :=
        norm_vonMangoldtLSeriesTerm_primePower_eq_halfPlaneWeight (c : ℂ) pk
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm
    hmajor hterm hU hbound
  simpa only [xiPrimeLogHigherValuation] using
    hdiff.differentiableAt (hU.mem_nhds hsU)

/-- **Half-plane separation theorem.**  Higher prime valuations define a holomorphic function on
`Re s > 1/2`; singularities of the continued valuation-one current there cannot come from this
Euler tail. -/
theorem differentiableOn_xiPrimeLogHigherValuation_halfPlane :
    DifferentiableOn ℂ (fun z : ℂ => xiPrimeLogHigherValuation z)
      {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  exact (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re hs).differentiableWithinAt

end

end RHTower
