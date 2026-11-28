import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.UniformizerRadicalArtin
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.TameArtinCharacters
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.KummerRadicalField

/-! Norms of two uniformizer radicals calibrate inverse Artin on the
residue units. One radical is multiplied by an (m)-th root of a
unit, on which arithmetic Frobenius reads the unit's residue. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial WithZero
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory.Kummer GlobalTheory.TameKummer GaloisForLFunctions.HTGeometry

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}

local notation "Fv" => v.adicCompletion K
local notation "V" => (Valued.v : Valuation Fv ℤᵐ⁰)
local notation "m" => (normV v - 1)

private theorem artin_log_valuation {α : Weil h →* Fvˣ} (hα : IsLocalArtin K Ω α)
    (s : Weil h) : log (V (α s : Fv)) = deg s := by
  have he : (tameValHom V (α s)).toAdd = -log (V (α s : Fv)) := by
    rw [tameValHom_toAdd, ← coe_tameUnzero V (α s)] <;> rfl
  exact neg_inj.mp (he.symm.trans (hα.ord_eq s))

private theorem unitRadical_fixed_inertia (hm : ¬ A.valuation ((m : ℕ) : Ω) < 1)
    (β : Ω) (hβ : A.valuation β = 1) {u : K} (hpow : β ^ m = algebraMap K Ω u)
    (s : Ine (F := K) A) : s.val β = β := by
  have hβ0 : β ≠ 0 := fun h => by rw [h, map_zero] at hβ; exact zero_ne_one hβ
  have hratio : (s.val β / β) ^ m = 1 := by
    rw [div_pow, ← map_pow, hpow, AlgEquiv.commutes, div_self]
    rw [← hpow]
    exact pow_ne_zero _ hβ0
  have hres := s.2.2 β hβ.le
  have hc : A.valuation (s.val β / β - 1) < 1 := by
    rwa [div_sub_one hβ0, Valuation.map_div, hβ, div_one]
  have h1 := eq_of_pow_eq_one A hm hratio (one_pow m) hc
  exact (div_eq_one_iff_eq hβ0).mp h1

private theorem ratio_eq_of_norm_calibration {π β : Ω} (hπ : π ≠ 0) (hβ : β ≠ 0)
    (φ s t : Gal(Ω/K))
    (hφπ : φ π = π) (hsβ : s β = β)
    (hφs : (φ * s) (π * β) = π * β)
    (hts : (t * s) π = π)
    (c : K) (hc : s π = algebraMap K Ω c * π) :
    t π / π = φ β / β := by
  have h1 : algebraMap K Ω c * (t π / π) = 1 := by
    rw [← mul_div_assoc]
    rw [show algebraMap K Ω c * t π = t (algebraMap K Ω c * π) by rw [map_mul, AlgEquiv.commutes],
      ← hc, ← AlgEquiv.mul_apply, hts, div_self hπ]
  have h2 : algebraMap K Ω c * (φ β / β) = 1 := by
    have e : algebraMap K Ω c * (π * φ β) = π * β := by
      simpa only [AlgEquiv.mul_apply, map_mul, hc, hsβ, AlgEquiv.commutes, hφπ, mul_assoc] using hφs
    have he : algebraMap K Ω c * φ β = β := mul_left_cancel₀ hπ
      ((mul_left_comm π (algebraMap K Ω c) (φ β)).trans e)
    rw [← mul_div_assoc, he, div_self hβ]
  have hc0 : algebraMap K Ω c ≠ 0 := fun hc0 => by rw [hc0, zero_mul] at h1; exact zero_ne_one h1
  exact mul_left_cancel₀ hc0 (h1.trans h2.symm)

theorem residue_inverseArtin_eq_uniformizerRadical_of_roots
    [HasEnoughRootsOfUnity K m] {a : Kˣ}
    (ha : V (algebraMap K Fv (a : K)) = exp (-1 : ℤ))
    (π : Ω) (hπ : π ^ m = algebraMap K Ω (a : K))
    (hmA : ¬ A.valuation ((m : ℕ) : Ω) < 1)
    (hmv : V ((m : ℕ) : Fv) = 1)
    {α : Weil h →* Fvˣ} (hα : IsLocalArtin K Ω α)
    (t : Ine (F := K) A) (x : 𝓞 K)
    (hx : V ((α (ineIncl h t) : Fv) - algebraMap K Fv (x : K)) < 1) :
    A.valuation (t.val π / π - algebraMap K Ω (x : K)) < 1 := by
  have hm : 0 < m := Nat.sub_pos_of_lt (one_lt_normV v)
  letI : NeZero m := ⟨hm.ne'⟩
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let b := α (ineIncl h t)
  have hvalb : V (b : Fv) = 1 := (mem_unitsLevel.mp (localArtinOnInertia hα t).2).1
  have hvalx : V (algebraMap K Fv (x : K)) = 1 := by
    have hh : V (algebraMap K Fv (x : K) - (b : Fv)) < V (b : Fv) := by
      rw [Valuation.map_sub_swap, hvalb]
      exact hx
    exact (Valuation.map_eq_of_sub_lt V hh).trans hvalb
  have hx0 : (x : K) ≠ 0 := by
    intro hz
    rw [hz, map_zero, map_zero] at hvalx
    exact zero_ne_one hvalx
  let u : Kˣ := Units.mk0 (x : K) hx0
  let U : Kˣ →* Fvˣ := Units.map (algebraMap K Fv).toMonoidHom
  have hvalU : V (U u : Fv) = 1 := hvalx
  have hxu : x ∉ v.asIdeal := by
    intro hmem
    have hv := (valued_algebraMap_int_lt_one_iff v x).mpr hmem
    change V (algebraMap K Fv (x : K)) < 1 at hv
    rw [hvalx] at hv
    exact (lt_irrefl _ hv)
  have hvxA : A.valuation (algebraMap K Ω (x : K)) = 1 := by
    have hle : A.valuation (algebraMap K Ω (x : K)) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr
        (mem_of_isIntegral_int A (x.2.map (algebraMap K Ω).toIntAlgHom))
    exact le_antisymm hle (le_of_not_gt fun hn => hxu ((h x).mp hn))
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (x : K)) hm
  have hβV : A.valuation β = 1 := (pow_eq_one_iff_of_nonneg zero_le hm.ne').mp
    (by rw [← Valuation.map_pow, hβ, hvxA])
  have hβ0 : β ≠ 0 := fun hz => by rw [hz, map_zero] at hβV; exact zero_ne_one hβV
  have hπ0 : π ≠ 0 := fun hz => by
    rw [hz, zero_pow hm.ne'] at hπ
    exact a.ne_zero ((map_eq_zero_iff _ (algebraMap K Ω).injective).mp hπ.symm)
  let sign : Fvˣ := (-1 : Fvˣ) ^ (m - 1)
  have hsign : V (sign : Fv) = 1 := by simp [sign, Units.val_pow_eq_pow_val]
  obtain ⟨φ, hφ⟩ := hα.surj (sign * U a)⁻¹
  have hφdeg : deg φ = 1 := by
    rw [← artin_log_valuation hα φ, hφ, Units.val_inv_eq_inv_val, map_inv₀, Units.val_mul, map_mul,
      hsign, one_mul, show V (U a : Fv) = _ from ha, ← exp_neg, log_exp, neg_neg]
  obtain ⟨s, hs⟩ := hα.surj (U u)⁻¹
  have hsdeg : deg s = 0 := by
    rw [← artin_log_valuation hα s, hs, Units.val_inv_eq_inv_val, map_inv₀, hvalU, inv_one, log_one]
  let sI : Ine (F := K) A := ⟨s.val, deg_eq_zero_iff.mp hsdeg⟩
  have hsβ : s.val β = β := unitRadical_fixed_inertia (v := v) hmA β hβV hβ sI
  have hφπ := (inverseArtin_fixes_uniformizerRadical K Ω h a ha π hπ hα).1 φ
    (by rw [hφ, inv_inv])
  have hau : V (algebraMap K Fv ((a * u : Kˣ) : K)) = exp (-1 : ℤ) := by
    rw [Units.val_mul, map_mul, map_mul, ha]
    change exp (-1 : ℤ) * V (algebraMap K Fv (x : K)) = _
    rw [hvalx, mul_one]
  have hπβ : (π * β) ^ m = algebraMap K Ω ((a * u : Kˣ) : K) := by
    rw [mul_pow, hπ, hβ, Units.val_mul, map_mul]
    rfl
  have hφsπβ := (inverseArtin_fixes_uniformizerRadical K Ω h (a * u) hau (π * β) hπβ hα).1
    (φ * s) (by
      simp only [map_mul, hφ, hs, mul_inv_rev, inv_inv]
      change U u * (sign * U a) = sign * (U a * U u)
      ac_rfl)
  have hbm : V (((b * (U u)⁻¹ : Fvˣ) : Fv) - 1) < 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
    rwa [div_sub_one (U u).ne_zero, Valuation.map_div, hvalU, div_one]
  have hLvl : b * (U u)⁻¹ ∈ unitsLevel (K := K) v 1 :=
    (mem_unitsLevel_one_iff_lt_one v _).mpr hbm
  obtain ⟨d, -, hd, hroot⟩ := exists_unitsLevel_pow_roots v m hm.ne'
  obtain rfl := hd hmv
  obtain ⟨y, -, hy⟩ := hroot _ ((unitsLevel (K := K) v 1).inv_mem hLvl)
  have hts := (inverseArtin_fixes_uniformizerRadical K Ω h a ha π hπ hα).2
    (ineIncl h t * s) y (by rw [map_mul, hs]; exact hy.symm)
  obtain ⟨c, hc⟩ := exists_scalar_mul_of_same_class (a := a) (b := a) rfl
    (x := s.val π) (y := π) (by rw [← map_pow, hπ, AlgEquiv.commutes]) hπ
  have hratio := ratio_eq_of_norm_calibration hπ0 hβ0 φ.val s.val t.val hφπ hsβ hφsπβ hts c hc
  have hfrob := (deg_eq_one_iff.mp hφdeg).2 β hβV.le
  have hβq : β ^ normV v = β ^ m * β := by
    rw [← pow_succ, Nat.sub_add_cancel (one_lt_normV v).le]
  rw [hβq, hβ, mul_comm (algebraMap K Ω (x : K))] at hfrob
  rw [hratio]
  conv_lhs =>
    rw [show algebraMap K Ω (x : K) = β * algebraMap K Ω (x : K) / β from
      (mul_div_cancel_left₀ _ hβ0).symm]
  rw [← sub_div, Valuation.map_div, hβV, div_one]
  exact hfrob

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.residue_inverseArtin_eq_uniformizerRadical_of_roots
