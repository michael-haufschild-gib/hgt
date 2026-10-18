import GaloisForLFunctions.BezoutValuationIncidence.DilationProfileIntegerJumpCoupling

/-!
# Additive reciprocity on dilation jump fibers

Coprime integer scales preserve Ramanujan amplitudes. On a Diophantine
jump fiber their product is the literal additive lag correlation. A complete
successor fiber has exact signed mass r μ(r), uniformly in both scales and
in its starting solution. Character orthogonality supplies the finite mean;
no infinite lag-sector summation is asserted.
-/

open scoped BigOperators
open Finset RHTower
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- A scale coprime to the modulus preserves every literal Ramanujan coefficient. -/
theorem ramanujanNaturalCoefficient_mul_of_coprime {p r : ℕ}
    (hpr : Nat.Coprime p r) (a : ℕ) :
    d4BMRamanujanNaturalCoefficient (p * a) r =
      d4BMRamanujanNaturalCoefficient a r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [d4BMRamanujanNaturalCoefficient]
  · rw [d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum hr,
      d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum hr,
      hpr.gcd_mul_left_cancel]

/-- The Diophantine jump equation converts dilation coefficients into literal additive correlation. -/
theorem ramanujan_jump_pair_eq_additive_pair {p q r a b h : ℕ}
    (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r) (hab : p * a = q * b + h) :
    d4BMRamanujanNaturalCoefficient a r * d4BMRamanujanNaturalCoefficient b r =
      d4BMRamanujanNaturalCoefficient (q * b + h) r *
        d4BMRamanujanNaturalCoefficient (q * b) r := by
  rw [← hab, ramanujanNaturalCoefficient_mul_of_coprime hpr,
    ramanujanNaturalCoefficient_mul_of_coprime hqr]

/-- The full residue correlation is a Ramanujan coefficient at the additive lag. -/
theorem ramanujan_complete_additive_correlation (Q : CGLPositiveModulus)
    (h : ZMod Q.value) :
    (∑ n : ZMod Q.value,
      cglRamanujanAdditiveSum Q (n + h) * cglRamanujanAdditiveSum Q n) =
      (Q.value : ℂ) * cglRamanujanAdditiveSum Q h := by
  classical
  let U := (univ : Finset (ZMod Q.value)).filter IsUnit
  have hchar (a b n : ZMod Q.value) :
      (ZMod.stdAddChar (a * (n + h)) : ℂ) * ZMod.stdAddChar (b * n) =
        ZMod.stdAddChar (n * (a + b)) * ZMod.stdAddChar (a * h) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hinner (a : ZMod Q.value) (ha : a ∈ U) :
      (∑ b ∈ U, (if a + b = 0 then (Q.value : ℂ) else 0) *
        ZMod.stdAddChar (a * h)) = (Q.value : ℂ) * ZMod.stdAddChar (a * h) := by
    have hu : IsUnit a := (mem_filter.mp ha).2
    have he (b : ZMod Q.value) : a + b = 0 ↔ b = -a := by
      constructor <;> intro hb
      · calc b = (a + b) - a := by ring
             _ = -a := by rw [hb]; simp
      · rw [hb, add_neg_cancel]
    simp [he, U, hu]
  unfold cglRamanujanAdditiveSum
  change (∑ n : ZMod Q.value, (∑ a ∈ U, _) * (∑ b ∈ U, _)) = _
  simp only [sum_mul_sum, hchar]
  rw [sum_comm]
  rw [mul_sum]
  apply sum_congr rfl
  intro a ha
  rw [sum_comm]
  calc
    _ = ∑ b ∈ U, (if a + b = 0 then (Q.value : ℂ) else 0) *
        ZMod.stdAddChar (a * h) := by
      apply sum_congr rfl
      intro b hb
      rw [← sum_mul, RHTower.Sieve.sum_stdAddChar_mul]
      split_ifs <;> simp
    _ = _ := hinner a ha

end GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.BezoutValuationIncidence

/-- Sampling along any invertible arithmetic progression preserves the complete lag correlation. -/
theorem ramanujan_complete_affine_correlation (Q : CGLPositiveModulus)
    (u : (ZMod Q.value)ˣ) (b h : ZMod Q.value) :
    (∑ t : ZMod Q.value,
      cglRamanujanAdditiveSum Q ((u : ZMod Q.value) * t + b + h) *
        cglRamanujanAdditiveSum Q ((u : ZMod Q.value) * t + b)) =
      (Q.value : ℂ) * cglRamanujanAdditiveSum Q h := by
  let e : ZMod Q.value ≃ ZMod Q.value :=
    { toFun := fun t => (u : ZMod Q.value) * t + b
      invFun := fun t => u.inv * (t - b)
      left_inv := by
        intro t
        calc
          _ = (u.inv * ↑u) * t := by ring
          _ = t := by rw [u.inv_val]; ring
      right_inv := by
        intro t
        calc
          _ = ((u : ZMod Q.value) * u.inv) * (t - b) + b := by ring
          _ = t := by rw [u.val_inv]; ring }
  have he := e.sum_comp (fun t => cglRamanujanAdditiveSum Q (t + h) *
    cglRamanujanAdditiveSum Q t)
  exact he.trans (ramanujan_complete_additive_correlation Q h)

/-- A coprime integer step carries exactly the same full-residue additive correlation. -/
theorem ramanujan_complete_progression_correlation (Q : CGLPositiveModulus)
    (m : ℕ) (hm : Nat.Coprime m Q.value) (b h : ℕ) :
    (∑ t : ZMod Q.value,
      cglRamanujanAdditiveSum Q ((m : ZMod Q.value) * t + b + h) *
        cglRamanujanAdditiveSum Q ((m : ZMod Q.value) * t + b)) =
      (Q.value : ℂ) * d4BMRamanujanNaturalCoefficient h Q.value := by
  simpa only [ZMod.coe_unitOfCoprime, d4BMRamanujanNaturalCoefficient,
    dif_pos Q.positive] using
    ramanujan_complete_affine_correlation Q (ZMod.unitOfCoprime m hm) b h


/-- Successor specialization, reusing the existing natural-coefficient theorem. -/
theorem ramanujanNaturalCoefficient_one (r : ℕ) :
    d4BMRamanujanNaturalCoefficient 1 r = (ArithmeticFunction.moebius r : ℂ) :=
  pm_ramanujan_at_one r

/-- Every full residue block on the jump-solution step pq has the exact successor mean μ(r). -/
theorem ramanujan_complete_successor_progression (Q : CGLPositiveModulus)
    (p q b : ℕ) (hpr : Nat.Coprime p Q.value) (hqr : Nat.Coprime q Q.value) :
    (∑ t : ZMod Q.value,
      cglRamanujanAdditiveSum Q (((p * q : ℕ) : ZMod Q.value) * t + b + 1) *
        cglRamanujanAdditiveSum Q (((p * q : ℕ) : ZMod Q.value) * t + b)) =
      (Q.value : ℂ) * (ArithmeticFunction.moebius Q.value : ℂ) := by
  simpa only [Nat.cast_one, ramanujanNaturalCoefficient_one] using
    ramanujan_complete_progression_correlation Q (p * q) (hpr.mul_left hqr) b 1

/-- The actual multiplier coefficients on a successor Diophantine fiber have signed mass r μ(r). -/
theorem ramanujan_successor_fiber_sum (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hpr : Nat.Coprime p Q.value) (hqr : Nat.Coprime q Q.value)
    (hab : p * a = q * b + 1) :
    (∑ t : ZMod Q.value,
      d4BMRamanujanNaturalCoefficient (a + q * t.val) Q.value *
        d4BMRamanujanNaturalCoefficient (b + p * t.val) Q.value) =
      (Q.value : ℂ) * (ArithmeticFunction.moebius Q.value : ℂ) := by
  calc
    _ = ∑ t : ZMod Q.value,
        cglRamanujanAdditiveSum Q (((p * q : ℕ) : ZMod Q.value) * t + q * b + 1) *
          cglRamanujanAdditiveSum Q (((p * q : ℕ) : ZMod Q.value) * t + q * b) := by
      apply sum_congr rfl
      intro t ht
      rw [← ramanujanNaturalCoefficient_mul_of_coprime hpr (a + q * t.val),
        ← ramanujanNaturalCoefficient_mul_of_coprime hqr (b + p * t.val)]
      have ha : p * (a + q * t.val) = p * q * t.val + q * b + 1 := by
        calc
          _ = p * q * t.val + p * a := by ring
          _ = _ := by rw [hab]; omega
      have hb : q * (b + p * t.val) = p * q * t.val + q * b := by ring
      rw [ha, hb]
      simp only [d4BMRamanujanNaturalCoefficient, dif_pos Q.positive,
        Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val]
    _ = _ := by
      simpa only [Nat.cast_mul] using ramanujan_complete_successor_progression Q p q (q * b) hpr hqr

private theorem ramanujanNaturalCoefficient_im (n r : ℕ) :
    (d4BMRamanujanNaturalCoefficient n r).im = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [d4BMRamanujanNaturalCoefficient]
  · rw [d4BMRamanujanNaturalCoefficient_eq_gcd_mobiusDivisorSum hr]
    simp

/-- The real jump amplitudes have the same exact signed successor mass. -/
theorem ramanujan_successor_fiber_re_sum (Q : CGLPositiveModulus) {p q a b : ℕ}
    (hpr : Nat.Coprime p Q.value) (hqr : Nat.Coprime q Q.value)
    (hab : p * a = q * b + 1) :
    (∑ t : ZMod Q.value,
      (d4BMRamanujanNaturalCoefficient (a + q * t.val) Q.value).re *
        (d4BMRamanujanNaturalCoefficient (b + p * t.val) Q.value).re) =
      (Q.value : ℝ) * (ArithmeticFunction.moebius Q.value : ℝ) := by
  have h := congrArg Complex.re (ramanujan_successor_fiber_sum Q hpr hqr hab)
  simpa only [Complex.re_sum, Complex.mul_re, ramanujanNaturalCoefficient_im,
    zero_mul, sub_zero, Complex.natCast_re, Complex.natCast_im,
    Complex.intCast_re] using h

end GaloisForLFunctions.BezoutValuationIncidence
