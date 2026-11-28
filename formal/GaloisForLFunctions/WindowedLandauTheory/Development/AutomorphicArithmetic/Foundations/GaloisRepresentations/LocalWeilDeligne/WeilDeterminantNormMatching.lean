import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneCharacterTwists
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A smooth character has unit norm on inertia and its Frobenius
value determines its norm everywhere. An unramified twist matches
the determinant norm of a positive-dimensional parameter with
that of a prescribed smooth character. -/

noncomputable section

open NumberField IsDedekindDomain Module
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}

theorem IsSmooth.norm_eq_one_on_inertia {χ : Weil h →* ℂˣ} (hχ : IsSmooth χ) (t : Ine (F := E) A) :
    ‖(χ (ineIncl h t) : ℂ)‖ = 1 := by
  let r := χ.comp (ineIncl h)
  have hf : (r.range : Set ℂˣ).Finite := hχ.finite_range
  letI : Finite r.range := hf
  let u : r.range := ⟨r t, ⟨t, rfl⟩⟩
  have hu := pow_orderOf_eq_one u
  have hpow : (χ (ineIncl h t) : ℂ) ^ orderOf u = 1 := by
    have hh := congrArg (fun x : r.range => ((x.val : ℂˣ) : ℂ)) hu
    change (u.val : ℂ) ^ orderOf u = 1
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one] using hh
  exact Complex.norm_eq_one_of_pow_eq_one hpow (orderOf_pos u).ne'

theorem IsSmooth.norm_eq_frob_zpow {χ : Weil h →* ℂˣ} (hχ : IsSmooth χ) (σ : Weil h) :
    ‖(χ σ : ℂ)‖ = ‖(χ (frob h) : ℂ)‖ ^ deg σ := by
  obtain ⟨t, hσ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  conv_lhs => rw [hσ]
  rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow,
    hχ.norm_eq_one_on_inertia, mul_one]

/-- The Frobenius norm exponent normalized by the rank. -/
def determinantNormExponent (χ : Weil h →* ℂˣ) (d : ℕ) : ℝ :=
  Real.log ‖(χ (frob h) : ℂ)‖ / ((d : ℝ) * Real.log (normV v : ℝ))

theorem determinantNormExponent_mul_unramified
    (χ : Weil h →* ℂˣ) {d : ℕ} (hd : 0 < d) (s : ℝ) :
    determinantNormExponent (χ * (unrChar h (qPow v s)) ^ d) d =
      determinantNormExponent χ d + s := by
  have hq : 1 < (normV v : ℝ) := by exact_mod_cast one_lt_normV v
  have hq0 := zero_lt_one.trans hq
  have hn : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hl := (Real.log_pos hq).ne'
  have hz : ‖(χ (frob h) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (Units.ne_zero _)
  unfold determinantNormExponent
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val,
    unrChar_apply, deg_frob, zpow_one, norm_mul, norm_pow, norm_qPow]
  rw [Real.log_mul hz (pow_ne_zero _ (Real.rpow_pos_of_pos hq0 s).ne'), Real.log_pow, Real.log_rpow hq0]
  field_simp

theorem unramified_twist_matches_determinantNorm
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (hd : 0 < finrank ℂ V) (ha : ∀ σ, ‖LinearMap.det (a.ρ σ)‖ = 1)
    (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (σ : Weil h) :
    let c := qPow v (determinantNormExponent χ (finrank ℂ V))
    ‖LinearMap.det ((a.twist (unrChar h c) (isSmooth_unrChar h c)).ρ σ)‖ = ‖(χ σ : ℂ)‖ := by
  let d := finrank ℂ V
  let z := ‖(χ (frob h) : ℂ)‖
  have hz : 0 < z := norm_pos_iff.mpr (Units.ne_zero _)
  let e := determinantNormExponent χ d
  let c := qPow v e
  let b := a.twist (unrChar h c) (isSmooth_unrChar h c)
  have hq : 1 < (normV v : ℝ) := by exact_mod_cast one_lt_normV v
  have hq0 := zero_lt_one.trans hq
  have hn : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hl := (Real.log_pos hq).ne'
  have hnorm : ‖(b.detChar (frob h) : ℂ)‖ = ‖(χ (frob h) : ℂ)‖ := by
    change ‖LinearMap.det (((unrChar h c (frob h) : ℂˣ) : ℂ) • a.ρ (frob h))‖ = z
    rw [unrChar_apply, deg_frob, zpow_one, LinearMap.det_smul, norm_mul, norm_pow, ha, mul_one]
    change ‖(qPow v e : ℂ)‖ ^ d = z
    rw [norm_qPow, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, Real.rpow_def_of_pos hq0, ← Real.exp_log hz]
    congr 1
    change Real.log (normV v : ℝ) * (Real.log z / ((d : ℝ) * Real.log (normV v : ℝ)) * d) = Real.log z
    field_simp
  change ‖(b.detChar σ : ℂ)‖ = ‖(χ σ : ℂ)‖
  rw [b.smooth_detChar.norm_eq_frob_zpow σ, hχ.norm_eq_frob_zpow σ, hnorm]

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.unramified_twist_matches_determinantNorm
#print axioms GlobalTheory.WeilDeligne.determinantNormExponent_mul_unramified
