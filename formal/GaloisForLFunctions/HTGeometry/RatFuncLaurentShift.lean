import GaloisForLFunctions.HTGeometry.LaurentShiftFixedField
import GaloisForLFunctions.HTGeometry.LaurentShiftDerivation
import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity

/-!
# The rational function field inside the formal Laurent field at infinity

The coordinate `s = X⁻¹` is transcendental over `ℂ`, so `ℂ(s)` embeds into `ℂ((X))`.  The
embedding intertwines the translation `s ↦ s + h` of rational functions with the translation
automorphism of the Laurent field.
-/

open PowerSeries
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem laurentX_eq_single : laurentX = HahnSeries.single (1 : ℤ) (1 : ℂ) := by
  rw [laurentX]
  show (HahnSeries.ofPowerSeries ℤ ℂ) PowerSeries.X = _
  rw [HahnSeries.ofPowerSeries_X]

theorem coordS_eq_single : coordS = HahnSeries.single (-1 : ℤ) (1 : ℂ) := by
  have hmul : HahnSeries.single (-1 : ℤ) (1 : ℂ) * laurentX = 1 := by
    rw [laurentX_eq_single, HahnSeries.single_mul_single]
    norm_num
  rw [coordS]
  exact (eq_inv_of_mul_eq_one_left hmul).symm ▸ rfl

theorem coordS_pow (k : ℕ) : coordS ^ k = HahnSeries.single (-(k : ℤ)) (1 : ℂ) := by
  induction k with
  | zero => simp [HahnSeries.single_zero_one]
  | succ k ih =>
      rw [pow_succ, ih, coordS_eq_single, HahnSeries.single_mul_single, mul_one,
        show (-(k : ℤ)) + (-1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring]

/-- Complex constants inside the Laurent field, as a ring homomorphism. -/
def laurentCHom : ℂ →+* LaurentSeries ℂ :=
  (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) : PowerSeries ℂ →+* LaurentSeries ℂ).comp
    (PowerSeries.C)

theorem laurentCHom_apply (a : ℂ) : laurentCHom a = laurentC a := rfl

theorem laurentCHom_eq_single (a : ℂ) : laurentCHom a = HahnSeries.single (0 : ℤ) a := by
  show (HahnSeries.ofPowerSeries ℤ ℂ) (PowerSeries.C a) = _
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

theorem laurentCHom_mul_coordS_pow (a : ℂ) (i : ℕ) :
    laurentCHom a * coordS ^ i = HahnSeries.single (-(i : ℤ)) a := by
  rw [coordS_pow, laurentCHom_eq_single, HahnSeries.single_mul_single, zero_add, mul_one]

/-- The polynomial ring embedded in the Laurent field through `s = X⁻¹`. -/
def polyToLaurent : Polynomial ℂ →+* LaurentSeries ℂ :=
  Polynomial.eval₂RingHom laurentCHom coordS

theorem coeff_polyToLaurent (p : Polynomial ℂ) (j : ℕ) :
    (polyToLaurent p).coeff (-(j : ℤ)) = p.coeff j := by
  classical
  rw [polyToLaurent, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  simp only [laurentCHom_mul_coordS_pow]
  rw [HahnSeries.coeff_sum]
  have hterm : ∀ i ∈ Finset.range (p.natDegree + 1),
      (HahnSeries.single (-(i : ℤ)) (p.coeff i)).coeff (-(j : ℤ))
        = if i = j then p.coeff i else 0 := by
    intro i _
    rw [HahnSeries.coeff_single]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg (by omega), if_neg hij]
  refine (Finset.sum_congr rfl hterm).trans ?_
  by_cases hj : j ≤ p.natDegree
  · rw [Finset.sum_ite_eq' (Finset.range (p.natDegree + 1)) j (fun i => p.coeff i),
      if_pos (Finset.mem_range.mpr (by omega))]
  · rw [Finset.sum_eq_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    intro i hi
    rw [if_neg]
    intro hij
    subst hij
    exact hj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

theorem polyToLaurent_injective : Function.Injective polyToLaurent := by
  intro p q hpq
  ext j
  have h := congrArg (fun z : LaurentSeries ℂ => z.coeff (-(j : ℤ))) hpq
  simpa [coeff_polyToLaurent] using h

/-- **The rational function field inside the Laurent field at infinity.** -/
def ratToLaurent : RatFunc ℂ →+* LaurentSeries ℂ :=
  IsFractionRing.lift (A := Polynomial ℂ) polyToLaurent_injective

theorem ratToLaurent_algebraMap (p : Polynomial ℂ) :
    ratToLaurent (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = polyToLaurent p :=
  IsFractionRing.lift_algebraMap _ _

theorem ratToLaurent_X : ratToLaurent (RatFunc.X : RatFunc ℂ) = coordS := by
  rw [RatFunc.X, ratToLaurent_algebraMap, polyToLaurent]
  simp

theorem ratToLaurent_C (c : ℂ) : ratToLaurent (RatFunc.C c) = laurentCHom c := by
  have hc : (RatFunc.C c : RatFunc ℂ)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) := by
    rw [RatFunc.algebraMap_C]
  rw [hc, ratToLaurent_algebraMap, polyToLaurent]
  simp

theorem ratToLaurent_injective : Function.Injective ratToLaurent :=
  ratToLaurent.injective

theorem shiftLaurent_laurentCHom (h c : ℂ) :
    shiftLaurent h (laurentCHom c) = laurentCHom c := by
  show shiftLaurent h (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (PowerSeries.C c)) = _
  rw [shiftLaurent_algebraMap, shiftPS_C]
  rfl

theorem shiftLaurent_polyToLaurent (h : ℂ) (p : Polynomial ℂ) :
    shiftLaurent h (polyToLaurent p)
      = polyToLaurent (p.comp (Polynomial.X + Polynomial.C h)) := by
  have hhom : ((shiftLaurent h : LaurentSeries ℂ →+* LaurentSeries ℂ).comp polyToLaurent)
      = (polyToLaurent.comp
          ((Polynomial.aeval (Polynomial.X + Polynomial.C h) :
            Polynomial ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom)) := by
    refine Polynomial.ringHom_ext ?_ ?_
    · intro c
      rw [RingHom.comp_apply, RingHom.comp_apply]
      show shiftLaurent h (polyToLaurent (Polynomial.C c))
        = polyToLaurent (Polynomial.aeval (Polynomial.X + Polynomial.C h) (Polynomial.C c))
      rw [Polynomial.aeval_C]
      have hCP : polyToLaurent (Polynomial.C c) = laurentCHom c := by
        rw [polyToLaurent]
        simp
      have halg : (algebraMap ℂ (Polynomial ℂ)) c = Polynomial.C c := rfl
      rw [halg, hCP, shiftLaurent_laurentCHom]
    · rw [RingHom.comp_apply, RingHom.comp_apply]
      show shiftLaurent h (polyToLaurent Polynomial.X)
        = polyToLaurent (Polynomial.aeval (Polynomial.X + Polynomial.C h) Polynomial.X)
      have hX : polyToLaurent (Polynomial.X : Polynomial ℂ) = coordS := by
        rw [polyToLaurent]; simp
      rw [Polynomial.aeval_X, hX, shiftLaurent_coordS, map_add, hX]
      congr 1
      rw [polyToLaurent]
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [laurentC]
      rfl
  have hfun := RingHom.congr_fun hhom p
  rw [RingHom.comp_apply, RingHom.comp_apply] at hfun
  exact hfun

/-- **The embedding intertwines the two translations.** -/
theorem shiftLaurent_ratToLaurent (h : ℂ) (r : RatFunc ℂ) :
    shiftLaurent h (ratToLaurent r) = ratToLaurent (ratShiftBy h r) := by
  have hhom : ((shiftLaurent h : LaurentSeries ℂ →+* LaurentSeries ℂ).comp ratToLaurent)
      = ratToLaurent.comp (ratShiftBy h) := by
    refine IsFractionRing.ringHom_ext (A := Polynomial ℂ) ?_
    intro p
    rw [RingHom.comp_apply, RingHom.comp_apply, ratToLaurent_algebraMap, ratShiftBy_algebraMap,
      ratToLaurent_algebraMap]
    exact shiftLaurent_polyToLaurent h p
  exact RingHom.congr_fun hhom r

end

end GaloisForLFunctions.HTGeometry
