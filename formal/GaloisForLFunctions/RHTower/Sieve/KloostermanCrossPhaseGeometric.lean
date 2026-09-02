import GaloisForLFunctions.RHTower.Sieve.KloostermanAnalyticFrontier
import GaloisForLFunctions.RHTower.SawtoothFourierSeries

/-!
# Geometric cancellation for unequal-modulus Kloosterman phases

Every unit additive character has exact order equal to its modulus. Consequently a quotient of
unit phases belonging to unequal positive moduli is nontrivial. Its finite orbit therefore obeys
the geometric-series bound independently of orbit length. This is the first cancellation bound on
the explicit terminal distinct-modulus carrier; no spectral estimate is assumed.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem coe_toCircle_eq_pow
    (q : ℕ) [NeZero q] (z : ZMod q) :
    (ZMod.toCircle z : ℂ) =
      (Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))) ^ z.val := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [ZMod.toCircle_apply, ← Complex.exp_nat_mul]
  congr 1
  field_simp

/-- The standard additive character on a positive cyclic group is faithful. -/
theorem stdAddChar_eq_one_iff
    (q : ℕ) [NeZero q] (z : ZMod q) :
    ZMod.stdAddChar z = (1 : ℂ) ↔ z = 0 := by
  rw [ZMod.stdAddChar_apply, coe_toCircle_eq_pow]
  constructor
  · intro hz
    have hprim := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
    have hdvd : q ∣ z.val := (hprim.pow_eq_one_iff_dvd z.val).mp hz
    have hzval : z.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt z)
    exact (ZMod.val_eq_zero z).mp hzval
  · rintro rfl
    simp

/-- Ratio governing one cross-unit additive-frequency orbit. -/
def kloostermanCrossPhaseRatio
    (q r : ℕ) [NeZero q] [NeZero r]
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) : ℂ :=
  star (ZMod.stdAddChar (x : ZMod q)) *
    ZMod.stdAddChar (y : ZMod r)

@[simp] theorem norm_kloostermanCrossPhaseRatio
    (q r : ℕ) [NeZero q] [NeZero r]
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    ‖kloostermanCrossPhaseRatio q r x y‖ = 1 := by
  simp [kloostermanCrossPhaseRatio]

/-- The standard additive character sends natural additive multiples to powers. -/
theorem stdAddChar_nsmul_eq_pow
    (q a : ℕ) [NeZero q] (z : ZMod q) :
    ZMod.stdAddChar (a • z) = (ZMod.stdAddChar z) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [succ_nsmul, AddChar.map_add_eq_mul, ih, pow_succ]

private theorem dvd_of_stdAddChar_unit_pow_eq_one
    (q a : ℕ) [NeZero q] (x : (ZMod q)ˣ)
    (h : (ZMod.stdAddChar (x : ZMod q)) ^ a = 1) :
    q ∣ a := by
  have hchar : ZMod.stdAddChar (a • (x : ZMod q)) = 1 := by
    rw [stdAddChar_nsmul_eq_pow]
    exact h
  have hzero : a • (x : ZMod q) = 0 :=
    (stdAddChar_eq_one_iff q _).mp hchar
  have hacast : (a : ZMod q) = 0 := by
    have hmul := congrArg
      (fun z : ZMod q => z * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) hzero
    simpa [nsmul_eq_mul, mul_assoc] using hmul
  exact (ZMod.natCast_eq_zero_iff a q).mp hacast

/-- Cross-unit phase ratios of unequal positive moduli are never the trivial character. -/
theorem kloostermanCrossPhaseRatio_ne_one_of_ne
    (q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    kloostermanCrossPhaseRatio q r x y ≠ 1 := by
  intro hratio
  have hqnorm : ‖ZMod.stdAddChar (x : ZMod q)‖ = 1 := by simp
  have hrnorm : ‖ZMod.stdAddChar (y : ZMod r)‖ = 1 := by simp
  have hqne : ZMod.stdAddChar (x : ZMod q) ≠ 0 := by
    exact norm_ne_zero_iff.mp (by simp [hqnorm])
  have hrne : ZMod.stdAddChar (y : ZMod r) ≠ 0 := by
    exact norm_ne_zero_iff.mp (by simp [hrnorm])
  have hxmul : star (ZMod.stdAddChar (x : ZMod q)) *
      ZMod.stdAddChar (x : ZMod q) = 1 := by
    calc
      star (ZMod.stdAddChar (x : ZMod q)) *
          ZMod.stdAddChar (x : ZMod q) =
          ZMod.stdAddChar (x : ZMod q) *
            conj (ZMod.stdAddChar (x : ZMod q)) := by
              rw [show star (ZMod.stdAddChar (x : ZMod q)) =
                conj (ZMod.stdAddChar (x : ZMod q)) by rfl]
              ring
      _ = (Complex.normSq (ZMod.stdAddChar (x : ZMod q)) : ℂ) := by
            rw [Complex.mul_conj]
      _ = 1 := by rw [Complex.normSq_eq_norm_sq, hqnorm]; norm_num
  have hrel : ZMod.stdAddChar (y : ZMod r) =
      ZMod.stdAddChar (x : ZMod q) := by
    unfold kloostermanCrossPhaseRatio at hratio
    have hsne : star (ZMod.stdAddChar (x : ZMod q)) ≠ 0 := by
      simp [hqne]
    apply mul_left_cancel₀ hsne
    exact hratio.trans hxmul.symm
  have hrpow : (ZMod.stdAddChar (y : ZMod r)) ^ q = 1 := by
    rw [hrel, ← stdAddChar_nsmul_eq_pow]
    simp
  have hqpow : (ZMod.stdAddChar (x : ZMod q)) ^ r = 1 := by
    rw [← hrel, ← stdAddChar_nsmul_eq_pow]
    simp
  have hrq : r ∣ q := dvd_of_stdAddChar_unit_pow_eq_one r q y hrpow
  have hqr' : q ∣ r := dvd_of_stdAddChar_unit_pow_eq_one q r x hqpow
  exact hqr (Nat.dvd_antisymm hqr' hrq)

/-- Unequal-modulus cross-unit phase orbits obey a bound independent of interval length. -/
theorem norm_sum_range_kloostermanCrossPhaseRatio_pow_le
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    ‖∑ i ∈ Finset.range M, (kloostermanCrossPhaseRatio q r x y) ^ i‖ ≤
      2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖ := by
  exact RHTower.norm_geom_sum_le
    (norm_kloostermanCrossPhaseRatio q r x y)
    (kloostermanCrossPhaseRatio_ne_one_of_ne q r hqr x y) M

end

end RHTower.Sieve
