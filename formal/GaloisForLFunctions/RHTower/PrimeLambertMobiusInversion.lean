import GaloisForLFunctions.RHTower.Mollifier
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Möbius inversion for the weighted Lambert transform

This file proves the exact infinite-series inversion used in the Euler-unit
completeness argument.  Absolute summability is explicit; no rearrangement is
hidden.  The remaining analytic work is to obtain this summability from the
sectorial exponential bound on the Fourier--Borel transform.
-/

noncomputable section

namespace RHTower

open Filter Complex ArithmeticFunction Nat Topology
open scoped BigOperators

/-- The weighted Lambert transform `H(n) = Σ_(m≥1) m a(nm)`. -/
def weightedLambertTransform (a : ℕ+ → ℂ) (n : ℕ+) : ℂ :=
  ∑' m : ℕ+, (m : ℂ) * a (n * m)

/-- The absolutely summable double-series term appearing after multiplication
by `μ(n)n`. -/
def weightedLambertMobiusPair (a : ℕ+ → ℂ) (c : ℕ+ × ℕ+) : ℂ :=
  (ArithmeticFunction.moebius c.1 : ℂ) * (c.1 : ℂ) * (c.2 : ℂ) *
    a (c.1 * c.2)

private theorem sum_moebius_first_divisorsAntidiagonal (b : ℕ+) :
    (∑ x : (b : ℕ).divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1.1) = if b = 1 then 1 else 0 := by
  rw [show (∑ x : (b : ℕ).divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1.1) =
      ∑ x ∈ (b : ℕ).divisorsAntidiagonal, ArithmeticFunction.moebius x.1 from by
        simpa only [Finset.univ_eq_attach] using
          ((b : ℕ).divisorsAntidiagonal.sum_attach
            (fun x ↦ ArithmeticFunction.moebius x.1))]
  rw [Nat.sum_divisorsAntidiagonal
    (f := fun i _ ↦ ArithmeticFunction.moebius i)]
  simpa using sum_moebius_divisors (b : ℕ)

private theorem weightedLambertMobius_antidiagonal
    (a : ℕ+ → ℂ) (b : ℕ+) :
    (∑ x : (b : ℕ).divisorsAntidiagonal,
      weightedLambertMobiusPair a (divisorsAntidiagonalFactors b x)) =
      if b = 1 then a 1 else 0 := by
  classical
  have hterm (x : (b : ℕ).divisorsAntidiagonal) :
      weightedLambertMobiusPair a (divisorsAntidiagonalFactors b x) =
        (ArithmeticFunction.moebius x.1.1 : ℂ) * (b : ℂ) * a b := by
    let d := divisorsAntidiagonalFactors b x
    have hval : d.1.1 * d.2.1 = (b : ℕ) :=
      divisorsAntidiagonalFactors_eq x
    have hprod : d.1 * d.2 = b := Subtype.ext hval
    change (ArithmeticFunction.moebius d.1 : ℂ) * (d.1 : ℂ) * (d.2 : ℂ) *
      a (d.1 * d.2) = _
    rw [hprod]
    have hcast : (d.1 : ℂ) * (d.2 : ℂ) = (b : ℂ) := by
      change ((d.1.1 : ℕ) : ℂ) * ((d.2.1 : ℕ) : ℂ) = ((b.1 : ℕ) : ℂ)
      exact_mod_cast hval
    rw [show (ArithmeticFunction.moebius d.1 : ℂ) * (d.1 : ℂ) * (d.2 : ℂ) =
        (ArithmeticFunction.moebius d.1 : ℂ) * (b : ℂ) by
      rw [mul_assoc, hcast]]
    rfl
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hmuC :
      (∑ x : (b : ℕ).divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1.1 : ℂ)) =
        if b = 1 then 1 else 0 := by
    rw [← Int.cast_sum, sum_moebius_first_divisorsAntidiagonal b]
    split_ifs <;> simp
  rw [hmuC]
  split_ifs with hb
  · subst b
    norm_num
  · simp

/-- **Absolute weighted Lambert--Möbius inversion.**  If the double series is
summable, then

`a(1) = Σ_(n≥1) μ(n)n Σ_(m≥1) m a(nm)`.

This is the exact regrouping used to recover the Fourier--Borel transform from
the vanishing Lambert transform. -/
theorem weightedLambertMobius_inversion (a : ℕ+ → ℂ)
    (hsum : Summable (weightedLambertMobiusPair a)) :
    (∑' n : ℕ+, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) *
      weightedLambertTransform a n) = a 1 := by
  have hrow (n : ℕ+) :
      (∑' m : ℕ+, weightedLambertMobiusPair a (n, m)) =
        (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) *
          weightedLambertTransform a n := by
    rw [weightedLambertTransform, ← tsum_mul_left]
    apply tsum_congr
    intro m
    simp [weightedLambertMobiusPair, mul_assoc]
  rw [← tsum_congr hrow]
  rw [← hsum.tsum_prod]
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  rw [Summable.tsum_sigma]
  · calc
      _ = ∑' b : ℕ+, if b = 1 then a 1 else 0 := by
        apply tsum_congr
        intro b
        rw [tsum_fintype]
        exact weightedLambertMobius_antidiagonal a b
      _ = a 1 := by simp
  · exact (sigmaAntidiagonalEquivProd.summable_iff).2 hsum

/-- If every weighted Lambert value vanishes, the first coefficient vanishes. -/
theorem weightedLambertMobius_first_eq_zero
    (a : ℕ+ → ℂ)
    (hsum : Summable (weightedLambertMobiusPair a))
    (hzero : ∀ n : ℕ+, weightedLambertTransform a n = 0) :
    a 1 = 0 := by
  calc
    a 1 = ∑' n : ℕ+, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) *
        weightedLambertTransform a n :=
      (weightedLambertMobius_inversion a hsum).symm
    _ = 0 := by simp [hzero]

/-- Geometric decay supplies the absolute double summability required by
`weightedLambertMobius_inversion`.  The proof does not hide a conditional
rearrangement: it majorizes the factor `n * m` by `n² + m²` and invokes the
absolutely summable Lambert-product majorants on both coordinates. -/
theorem weightedLambertMobiusPair_summable_of_geometric
    (a : ℕ+ → ℂ) (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ n : ℕ+, ‖a n‖ ≤ C * r ^ (n : ℕ)) :
    Summable (weightedLambertMobiusPair a) := by
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  have hsecond : Summable (fun c : ℕ+ × ℕ+ ↦
      ((c.2 : ℝ) ^ 2) * r ^ (c.1 * c.2 : ℕ)) := by
    simpa using (summable_prod_mul_pow (𝕜 := ℝ) 2 hrnorm)
  have hfirst : Summable (fun c : ℕ+ × ℕ+ ↦
      ((c.1 : ℝ) ^ 2) * r ^ (c.1 * c.2 : ℕ)) := by
    have h := ((Equiv.prodComm ℕ+ ℕ+).summable_iff).2 hsecond
    apply h.congr
    rintro ⟨n, m⟩
    simp only [Function.comp_apply, Equiv.prodComm_apply]
    dsimp
    rw [mul_comm]
    ring
  have hmajor : Summable (fun c : ℕ+ × ℕ+ ↦
      C * (((c.1 : ℝ) ^ 2) * r ^ (c.1 * c.2 : ℕ) +
        ((c.2 : ℝ) ^ 2) * r ^ (c.1 * c.2 : ℕ))) :=
    (hfirst.add hsecond).mul_left C
  apply Summable.of_norm_bounded hmajor
  intro c
  have hmu : ‖(ArithmeticFunction.moebius c.1 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := c.1)
  have hn0 : 0 ≤ (c.1 : ℝ) := by positivity
  have hm0 : 0 ≤ (c.2 : ℝ) := by positivity
  have hrpow : 0 ≤ r ^ (c.1 * c.2 : ℕ) := pow_nonneg hr0 _
  have hnm : (c.1 : ℝ) * (c.2 : ℝ) ≤
      (c.1 : ℝ) ^ 2 + (c.2 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hn0 hm0]
  have hcastprod : ((c.1 * c.2 : ℕ+) : ℕ) =
      (c.1 : ℕ) * (c.2 : ℕ) := rfl
  calc
    ‖weightedLambertMobiusPair a c‖ =
        ‖(ArithmeticFunction.moebius c.1 : ℂ)‖ * (c.1 : ℝ) * (c.2 : ℝ) *
          ‖a (c.1 * c.2)‖ := by
            simp only [weightedLambertMobiusPair, norm_mul, Complex.norm_natCast]
    _ ≤ 1 * (c.1 : ℝ) * (c.2 : ℝ) *
          (C * r ^ ((c.1 * c.2 : ℕ+) : ℕ)) := by
            gcongr
            exact ha (c.1 * c.2)
    _ ≤ C * (((c.1 : ℝ) ^ 2) * r ^ (c.1 * c.2 : ℕ) +
          ((c.2 : ℝ) ^ 2) * r ^ (c.1 * c.2 : ℕ)) := by
            rw [hcastprod]
            calc
              1 * (c.1 : ℝ) * (c.2 : ℝ) *
                  (C * r ^ ((c.1 : ℕ) * (c.2 : ℕ))) =
                  C * ((c.1 : ℝ) * (c.2 : ℝ)) *
                    r ^ ((c.1 : ℕ) * (c.2 : ℕ)) := by ring
              _ ≤ C * ((c.1 : ℝ) ^ 2 + (c.2 : ℝ) ^ 2) *
                    r ^ ((c.1 : ℕ) * (c.2 : ℕ)) := by gcongr
              _ = _ := by ring

end RHTower
