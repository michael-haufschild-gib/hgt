import GaloisForLFunctions.RHTower.FieldOnePadicHaarScaling

/-!
# Local Haar characters equal local norm modules

This file upgrades the prime-generator calculation to every local unit:

* on `ℚ_p`, a unit is split into a norm-one unit and an integral power of
  the prime uniformizer;
* the same splitting is transferred algebraically to each rational adic
  completion;
* the continuous rational algebra equivalence preserves the closed unit
  ball, which is enough to transfer the norm-one property; and
* consequently the additive Haar character of every local unit is exactly
  its nonnegative norm.

The proof uses the discrete valuation and the already proved same-place
uniformizer scaling.  It makes no finiteness approximation.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

variable (p : ℕ) [Fact p.Prime]

/-! ## Explicit p-adic field -/

/-- Every unit of `ℚ_p` has additive Haar character equal to its norm. -/
theorem fieldOnePadicUnits_distribHaarChar_eq_nnnorm
    (a : ℚ_[p]ˣ) :
    distribHaarChar ℚ_[p] a = ‖(a : ℚ_[p])‖₊ := by
  let P : ℚ_[p]ˣ := fieldOnePadicPrimeUnit p
  let n : ℤ := (a : ℚ_[p]).valuation
  let b : ℚ_[p]ˣ := a * P ^ (-n)
  have ha0 : (a : ℚ_[p]) ≠ 0 :=
    Units.ne_zero a
  have hnorma :
      ‖(a : ℚ_[p])‖ =
        (p : ℝ) ^ (-n) := by
    exact Padic.norm_eq_zpow_neg_valuation ha0
  have hnormb :
      ‖(b : ℚ_[p])‖ = 1 := by
    dsimp [b, P, fieldOnePadicPrimeUnit]
    rw [Units.val_zpow_eq_zpow_val]
    change
      ‖(a : ℚ_[p]) *
          (p : ℚ_[p]) ^ (-n)‖ = 1
    rw [norm_mul, hnorma, Padic.norm_p_zpow]
    rw [← zpow_add₀]
    · simp
    · exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hcharb :
      distribHaarChar ℚ_[p] b = 1 :=
    fieldOne_units_distribHaarChar_eq_one_of_norm_eq_one
      b hnormb
  have hdecomp : a = b * P ^ n := by
    dsimp [b]
    rw [mul_assoc, ← zpow_add]
    simp
  calc
    distribHaarChar ℚ_[p] a =
        distribHaarChar ℚ_[p] (b * P ^ n) := by
          rw [hdecomp]
    _ =
        distribHaarChar ℚ_[p] b *
          distribHaarChar ℚ_[p] (P ^ n) := by
          rw [map_mul]
    _ =
        1 * (distribHaarChar ℚ_[p] P) ^ n := by
          rw [map_zpow, hcharb]
    _ = (((p : ℝ≥0)⁻¹) ^ n) := by
          rw [fieldOnePadicPrimeUnit_distribHaarChar]
          simp
    _ = ‖(a : ℚ_[p])‖₊ := by
          apply NNReal.eq
          rw [NNReal.coe_zpow]
          rw [NNReal.coe_inv]
          rw [NNReal.coe_natCast]
          rw [inv_zpow']
          exact hnorma.symm

/-! ## Rational adic completions -/

/-- The rational adic-completion equivalence with `ℚ_p` preserves the
closed unit ball. -/
theorem fieldOneAdic_padicEquiv_norm_le_one_iff
    (v : HeightOneSpectrum ℤ)
    (x : v.adicCompletion ℚ) :
    ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x‖ ≤ 1 ↔
      ‖x‖ ≤ 1 := by
  let q : ℕ := Rat.HeightOneSpectrum.primesEquiv v
  letI : Fact q.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let e :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  constructor
  · intro hx
    have hx' : e x ∈ PadicInt.subring q := hx
    obtain ⟨z, hz, hzx⟩ :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn hx'
    have hzx' : z = x := e.injective hzx
    rw [← hzx']
    exact Valued.toNormedField.norm_le_one_iff.mpr hz
  · intro hx
    have hx' :
        x ∈ v.adicCompletionIntegers ℚ :=
      Valued.toNormedField.norm_le_one_iff.mp hx
    exact
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hx'

/-- Every unit of a rational adic completion has additive Haar character
equal to its norm. -/
theorem fieldOneAdicUnits_distribHaarChar_eq_nnnorm
    (v : HeightOneSpectrum ℤ)
    (a : (v.adicCompletion ℚ)ˣ) :
    distribHaarChar (v.adicCompletion ℚ) a =
      ‖(a : v.adicCompletion ℚ)‖₊ := by
  let q : ℕ := Rat.HeightOneSpectrum.primesEquiv v
  letI : Fact q.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let e :=
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let P : (v.adicCompletion ℚ)ˣ :=
    fieldOneRationalLocalUnit v
      (fieldOneRationalPrimeUnit v)
  let n : ℤ := (e (a : v.adicCompletion ℚ)).valuation
  let b : (v.adicCompletion ℚ)ˣ :=
    a * P ^ (-n)
  have hea0 :
      e (a : v.adicCompletion ℚ) ≠ 0 := by
    exact (map_ne_zero e).mpr (Units.ne_zero a)
  have hPmap :
      e (P : v.adicCompletion ℚ) = (q : ℚ_[q]) := by
    change
      e (algebraMap ℚ (v.adicCompletion ℚ)
        (Rat.HeightOneSpectrum.primesEquiv v : ℚ)) =
        (q : ℚ_[q])
    simp [q]
  have hPzpow :
      e ((P : v.adicCompletion ℚ) ^ (-n)) =
        (q : ℚ_[q]) ^ (-n) := by
    have hPmap' :
        e.toAlgEquiv.toRingEquiv
            (P : v.adicCompletion ℚ) =
          (q : ℚ_[q]) :=
      hPmap
    change
      e.toAlgEquiv.toRingEquiv
          ((P : v.adicCompletion ℚ) ^ (-n)) =
        (q : ℚ_[q]) ^ (-n)
    rw [map_zpow₀, hPmap']
  have heb :
      e (b : v.adicCompletion ℚ) =
        e (a : v.adicCompletion ℚ) *
          (q : ℚ_[q]) ^ (-n) := by
    dsimp [b]
    rw [Units.val_zpow_eq_zpow_val]
    rw [map_mul, hPzpow]
  have hnormea :
      ‖e (a : v.adicCompletion ℚ)‖ =
        (q : ℝ) ^ (-n) := by
    exact Padic.norm_eq_zpow_neg_valuation hea0
  have hnormeb :
      ‖e (b : v.adicCompletion ℚ)‖ = 1 := by
    rw [heb, norm_mul, hnormea, Padic.norm_p_zpow]
    rw [← zpow_add₀]
    · simp
    · exact_mod_cast
        (Rat.HeightOneSpectrum.primesEquiv v).property.ne_zero
  have hnormb :
      ‖(b : v.adicCompletion ℚ)‖ = 1 := by
    have hb_le :
        ‖(b : v.adicCompletion ℚ)‖ ≤ 1 :=
      (fieldOneAdic_padicEquiv_norm_le_one_iff
        v (b : v.adicCompletion ℚ)).mp hnormeb.le
    have hbinv_le :
        ‖((b⁻¹ : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ)‖ ≤ 1 := by
      apply
        (fieldOneAdic_padicEquiv_norm_le_one_iff
          v ((b⁻¹ : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ)).mp
      rw [show
        e (((b⁻¹ : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ)) =
          (e (b : v.adicCompletion ℚ))⁻¹ by
            simp]
      rw [norm_inv, hnormeb]
      simp
    have hb0 :
        ‖(b : v.adicCompletion ℚ)‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr (Units.ne_zero b)
    have hbinv_le' :
        ‖(b : v.adicCompletion ℚ)‖⁻¹ ≤ 1 := by
      simpa using hbinv_le
    have hone_le :
        1 ≤ ‖(b : v.adicCompletion ℚ)‖ := by
      calc
        1 =
            ‖(b : v.adicCompletion ℚ)‖ *
              ‖(b : v.adicCompletion ℚ)‖⁻¹ :=
          (mul_inv_cancel₀ hb0).symm
        _ ≤ ‖(b : v.adicCompletion ℚ)‖ * 1 :=
          mul_le_mul_of_nonneg_left hbinv_le'
            (norm_nonneg _)
        _ = ‖(b : v.adicCompletion ℚ)‖ := mul_one _
    exact le_antisymm hb_le hone_le
  have hcharb :
      distribHaarChar (v.adicCompletion ℚ) b = 1 :=
    fieldOne_units_distribHaarChar_eq_one_of_norm_eq_one
      b hnormb
  have hdecomp : a = b * P ^ n := by
    dsimp [b]
    rw [mul_assoc, ← zpow_add]
    simp
  have hcharP :
      distribHaarChar (v.adicCompletion ℚ) P =
        (q : ℝ≥0)⁻¹ := by
    exact
      fieldOneRationalPrimeUnit_localDistribHaarChar_self v
  have hnnormb :
      ‖(b : v.adicCompletion ℚ)‖₊ = 1 := by
    apply NNReal.eq
    exact hnormb
  have hnnormP :
      ‖(P : v.adicCompletion ℚ)‖₊ =
        (q : ℝ≥0)⁻¹ := by
    change
      ‖algebraMap ℚ (v.adicCompletion ℚ)
          (Rat.HeightOneSpectrum.primesEquiv v : ℚ)‖₊ =
        (q : ℝ≥0)⁻¹
    apply NNReal.eq
    simpa [q] using
      fieldOneRationalPrimeUnit_localNorm_self v
  calc
    distribHaarChar (v.adicCompletion ℚ) a =
        distribHaarChar (v.adicCompletion ℚ)
          (b * P ^ n) := by rw [hdecomp]
    _ =
        distribHaarChar (v.adicCompletion ℚ) b *
          distribHaarChar (v.adicCompletion ℚ)
            (P ^ n) := by rw [map_mul]
    _ =
        1 *
          (distribHaarChar (v.adicCompletion ℚ) P) ^ n := by
            rw [map_zpow, hcharb]
    _ = ((q : ℝ≥0)⁻¹) ^ n := by
          rw [hcharP]
          simp
    _ = ‖(a : v.adicCompletion ℚ)‖₊ := by
          rw [hdecomp]
          simp only [Units.val_mul,
            Units.val_zpow_eq_zpow_val, nnnorm_mul,
            nnnorm_zpow]
          rw [hnnormb, hnnormP]
          simp

end

end GaloisForLFunctions.RHTower
