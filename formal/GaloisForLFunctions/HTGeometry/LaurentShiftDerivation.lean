import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization
import GaloisForLFunctions.HTGeometry.LaurentShiftAutomorphism

/-!
# The derivation `d/ds` on the formal Laurent field at infinity

In the coordinate `X = s⁻¹` the derivation `d/ds` is `-X² d/dX`.  It sends the coordinate `s` to
`1` and commutes with every translation `s ↦ s + h`, because the substitution `a = X/(1+hX)`
satisfies the chain-rule identity `X² a′ = a²`.
-/

open PowerSeries
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `d/ds = -X² d/dX` on the formal Laurent field at infinity. -/
@[reducible] def laurentSDifferential : Differential (LaurentSeries ℂ) :=
  ⟨(-(laurentX ^ 2)) • (GaloisForLFunctions.formalLaurentDifferential.deriv)⟩

local instance : Differential (LaurentSeries ℂ) := laurentSDifferential

theorem laurentSDeriv_apply (F : LaurentSeries ℂ) :
    F′ = -(laurentX ^ 2) * (GaloisForLFunctions.formalLaurentDifferential.deriv F) := by
  show ((-(laurentX ^ 2)) • (GaloisForLFunctions.formalLaurentDifferential.deriv)) F = _
  simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]

theorem laurentSDeriv_add (x y : LaurentSeries ℂ) : (x + y)′ = x′ + y′ := by
  simp only [map_add]

theorem laurentSDeriv_mul (x y : LaurentSeries ℂ) : (x * y)′ = x * y′ + y * x′ := by
  simp only [Derivation.leibniz, smul_eq_mul]

theorem laurentSDeriv_pow (x : LaurentSeries ℂ) (n : ℕ) :
    (x ^ n)′ = (n : LaurentSeries ℂ) * x ^ (n - 1) * x′ := by
  simp only [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
  ring

/-- **The derivation on the image of the power series.** -/
theorem laurentSDeriv_algebraMap (F : PowerSeries ℂ) :
    (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) F)′
      = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (coordDerivPS F) := by
  rw [laurentSDeriv_apply, GaloisForLFunctions.formalLaurentDifferential_algebraMap, coordDerivPS,
    map_mul, map_neg, map_pow]
  rfl

theorem deriv_laurentX : (laurentX)′ = -(laurentX ^ 2) := by
  have h := laurentSDeriv_algebraMap (PowerSeries.X : PowerSeries ℂ)
  rw [coordDerivPS, PowerSeries.derivative_X, mul_one, map_neg, map_pow] at h
  exact h

/-- **The coordinate `s` has derivative one.** -/
theorem deriv_coordS : (coordS)′ = 1 := by
  have hX : laurentX ≠ 0 := laurentX_ne_zero
  have hmul : coordS * laurentX = 1 := coordS_mul_laurentX
  have hd := congrArg (fun z : LaurentSeries ℂ => z′) hmul
  simp only [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul] at hd
  rw [deriv_laurentX] at hd
  have hcs : coordS * laurentX ^ 2 = laurentX := by
    have hstep : coordS * laurentX ^ 2 = (coordS * laurentX) * laurentX := by ring
    rw [hstep, hmul, one_mul]
  have hz : laurentX * ((coordS)′ - 1) = 0 := by linear_combination hd + hcs
  rcases mul_eq_zero.mp hz with hc | hc
  · exact absurd hc hX
  · exact sub_eq_zero.mp hc

/-- **The translation commutes with `d/ds` on the image of the power series.** -/
theorem shiftLaurent_deriv_algebraMap (h : ℂ) (F : PowerSeries ℂ) :
    shiftLaurent h ((algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) F)′)
      = ((shiftLaurent h (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) F))′) := by
  rw [laurentSDeriv_algebraMap, shiftLaurent_algebraMap, shiftLaurent_algebraMap,
    laurentSDeriv_algebraMap, shiftPS_coordDerivPS]

/-- **The translation commutes with `d/ds`.** -/
theorem shiftLaurent_deriv (h : ℂ) (x : LaurentSeries ℂ) :
    shiftLaurent h (x′) = (shiftLaurent h x)′ := by
  obtain ⟨A, B, hB, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries ℂ) x
  set a : LaurentSeries ℂ := algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) A with ha
  set b : LaurentSeries ℂ := algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) B with hb
  have hbne : b ≠ 0 := by
    rw [hb]
    exact algebraMap_powerSeries_ne_zero (nonZeroDivisors.ne_zero hB)
  have hσbne : shiftLaurent h b ≠ 0 := by
    intro hc
    exact hbne ((shiftLaurent h).injective (by rw [hc, map_zero]))
  have hda : shiftLaurent h (a′) = (shiftLaurent h a)′ := by
    rw [ha]; exact shiftLaurent_deriv_algebraMap h A
  have hdb : shiftLaurent h (b′) = (shiftLaurent h b)′ := by
    rw [hb]; exact shiftLaurent_deriv_algebraMap h B
  have heq1 : (a / b) * b = a := div_mul_cancel₀ a hbne
  have hd1 := congrArg (fun z : LaurentSeries ℂ => z′) heq1
  simp only [Derivation.leibniz, smul_eq_mul] at hd1
  have hσdiv : shiftLaurent h (a / b) = shiftLaurent h a / shiftLaurent h b := map_div₀ _ _ _
  have hd1σ := congrArg (shiftLaurent h) hd1
  rw [map_add, map_mul, map_mul, hσdiv, hda, hdb] at hd1σ
  have heq2 : (shiftLaurent h a / shiftLaurent h b) * shiftLaurent h b = shiftLaurent h a :=
    div_mul_cancel₀ _ hσbne
  have hd2 := congrArg (fun z : LaurentSeries ℂ => z′) heq2
  simp only [Derivation.leibniz, smul_eq_mul] at hd2
  have hzero : shiftLaurent h b * (shiftLaurent h ((a / b)′)
      - ((shiftLaurent h a / shiftLaurent h b)′)) = 0 := by
    linear_combination hd1σ - hd2
  rcases mul_eq_zero.mp hzero with hc | hc
  · exact absurd hc hσbne
  · rw [hσdiv]
    exact sub_eq_zero.mp hc

end

end GaloisForLFunctions.HTGeometry
