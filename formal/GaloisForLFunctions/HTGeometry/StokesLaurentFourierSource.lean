import GaloisForLFunctions.HTGeometry.AiryTowerStokesRigidity
import GaloisForLFunctions.HTGeometry.StokesFormalUniformizer

/-!
# Laurent-series source of the negative Airy local Fourier branch

This module models the actual formal local-Fourier coordinate relation
`hat z = f / z` in `ℂ((t))`.  A normalized irregular value
`f = t^(-(R+E)) u(t)`, with `u(0)=1`, yields
`hat z = t^(-E)u(t)` and reciprocal coordinate
`hat zeta = t^E u(t)^(-1)`.  The formal-uniformizer theorem upgrades its order statement to an
exact conjugacy: a Laurent-series `ℂ`-algebra automorphism sends `t^E` to `hat zeta`.

The final section constructs a genuine coefficient-one Laurent series from every ramified
characteristic.  For an Airy tower its first negative Fourier step therefore has an exact new
ramification coordinate, with no postulated exponent-transition rule.
-/

open scoped PowerSeries

namespace GaloisForLFunctions
namespace IrregularStokes
namespace LaurentFourier

open FormalUniformizer

noncomputable section

def laurentMonomial (n : ℤ) : LaurentSeries ℂ := HahnSeries.single n 1

@[simp] theorem laurentMonomial_mul (a b : ℤ) :
    laurentMonomial a * laurentMonomial b = laurentMonomial (a + b) := by
  simp [laurentMonomial, HahnSeries.single_mul_single]

@[simp] theorem laurentMonomial_inv (a : ℤ) :
    (laurentMonomial a)⁻¹ = laurentMonomial (-a) := by
  simp [laurentMonomial, HahnSeries.inv_single]

@[simp] theorem laurentMonomial_ne_zero (a : ℤ) : laurentMonomial a ≠ 0 := by
  exact HahnSeries.single_ne_zero one_ne_zero

@[simp] theorem laurentMonomial_order (a : ℤ) :
    (laurentMonomial a).order = a := by
  exact HahnSeries.order_single one_ne_zero

@[simp] theorem laurentMonomial_orderTop (a : ℤ) :
    (laurentMonomial a).orderTop = a := by
  exact HahnSeries.orderTop_single one_ne_zero

theorem powerSeries_coe_ne_zero {u : PowerSeries ℂ} (hu : u ≠ 0) :
    (u : LaurentSeries ℂ) ≠ 0 :=
  by simpa using (HahnSeries.ofPowerSeries_injective (Γ := ℤ)).ne hu

theorem powerSeries_inverse_coe (u : PowerSeries ℂ)
    (hu : u.constantCoeff ≠ 0) :
    ((u⁻¹ : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((u : LaurentSeries ℂ)⁻¹) := by
  have huPS : u ≠ 0 := by
    intro h
    rw [h] at hu
    exact hu (by simp)
  have huLS : (u : LaurentSeries ℂ) ≠ 0 := powerSeries_coe_ne_zero huPS
  apply mul_right_cancel₀ huLS
  rw [inv_mul_cancel₀ huLS]
  change (HahnSeries.ofPowerSeries ℤ ℂ) u⁻¹ *
      (HahnSeries.ofPowerSeries ℤ ℂ) u = 1
  rw [← map_mul, PowerSeries.inv_mul_cancel u hu, map_one]

theorem powerSeries_coe_coeff_of_neg (u : PowerSeries ℂ) {j : ℤ} (hj : j < 0) :
    (u : LaurentSeries ℂ).coeff j = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨n, hn, hnj⟩
  have hj0 : 0 ≤ j := by
    rw [← hnj]
    exact Int.natCast_nonneg n
  omega

theorem powerSeries_coe_order_zero (u : PowerSeries ℂ)
    (hu : u.constantCoeff ≠ 0) :
    (u : LaurentSeries ℂ).order = 0 := by
  have huPS : u ≠ 0 := by
    intro h
    rw [h] at hu
    exact hu (by simp)
  have huLS : (u : LaurentSeries ℂ) ≠ 0 := powerSeries_coe_ne_zero huPS
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    change ((HahnSeries.ofPowerSeries ℤ ℂ) u).coeff ((0 : ℕ) : ℤ) ≠ 0
    rw [HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hu
  · rw [HahnSeries.le_order_iff_forall huLS]
    intro j hj
    exact powerSeries_coe_coeff_of_neg u hj

def originalCoordinate (R : ℕ) : LaurentSeries ℂ :=
  laurentMonomial (-(R : ℤ))

def normalizedIrregularValue (R E : ℕ) (u : PowerSeries ℂ) : LaurentSeries ℂ :=
  laurentMonomial (-((R + E : ℕ) : ℤ)) * (u : LaurentSeries ℂ)

def localFourierCoordinate (R : ℕ) (f : LaurentSeries ℂ) : LaurentSeries ℂ :=
  f * (originalCoordinate R)⁻¹

def localFourierReciprocalCoordinate (R : ℕ) (f : LaurentSeries ℂ) : LaurentSeries ℂ :=
  (localFourierCoordinate R f)⁻¹

theorem localFourierCoordinate_normalized (R E : ℕ) (u : PowerSeries ℂ) :
    localFourierCoordinate R (normalizedIrregularValue R E u) =
      laurentMonomial (-(E : ℤ)) * (u : LaurentSeries ℂ) := by
  rw [localFourierCoordinate, normalizedIrregularValue, originalCoordinate,
    laurentMonomial_inv]
  calc
    (laurentMonomial (-((R + E : ℕ) : ℤ)) * (u : LaurentSeries ℂ)) *
          laurentMonomial (-(-(R : ℤ))) =
        (laurentMonomial (-((R + E : ℕ) : ℤ)) *
          laurentMonomial (-(-(R : ℤ)))) * (u : LaurentSeries ℂ) := by
            ac_rfl
    _ = laurentMonomial (-(E : ℤ)) * (u : LaurentSeries ℂ) := by
      rw [laurentMonomial_mul]
      congr 2
      push_cast
      omega

theorem localFourierCoordinate_normalized_order
    (R E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) :
    (localFourierCoordinate R (normalizedIrregularValue R E u)).order =
      -(E : ℤ) := by
  rw [localFourierCoordinate_normalized]
  have huLS : (u : LaurentSeries ℂ) ≠ 0 := powerSeries_coe_ne_zero <| by
    intro h
    rw [h] at hu
    simp at hu
  rw [HahnSeries.order_mul (laurentMonomial_ne_zero _) huLS,
    laurentMonomial_order, powerSeries_coe_order_zero u]
  · simp
  · rw [hu]
    exact one_ne_zero

theorem localFourierReciprocalCoordinate_normalized
    (R E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) :
    localFourierReciprocalCoordinate R (normalizedIrregularValue R E u) =
      ((PowerSeries.X ^ E * u⁻¹ : PowerSeries ℂ) : LaurentSeries ℂ) := by
  rw [localFourierReciprocalCoordinate, localFourierCoordinate_normalized,
    mul_inv_rev, laurentMonomial_inv]
  have hu0 : u.constantCoeff ≠ 0 := by
    rw [hu]
    exact one_ne_zero
  rw [← powerSeries_inverse_coe u hu0]
  change (HahnSeries.ofPowerSeries ℤ ℂ) u⁻¹ * laurentMonomial (-(-(E : ℤ))) =
    (HahnSeries.ofPowerSeries ℤ ℂ) (PowerSeries.X ^ E * u⁻¹)
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow]
  rw [show -(-(E : ℤ)) = (E : ℤ) by omega]
  simp only [laurentMonomial]
  exact mul_comm _ _

theorem order_inv_of_ne_zero (f : LaurentSeries ℂ) (hf : f ≠ 0) :
    f⁻¹.order = -f.order := by
  have hfinv : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hmul := HahnSeries.order_mul hf hfinv
  rw [mul_inv_cancel₀ hf, HahnSeries.order_one] at hmul
  omega

theorem localFourierReciprocalCoordinate_normalized_order
    (R E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) :
    (localFourierReciprocalCoordinate R
      (normalizedIrregularValue R E u)).order = (E : ℤ) := by
  rw [localFourierReciprocalCoordinate,
    order_inv_of_ne_zero]
  · rw [localFourierCoordinate_normalized_order R E u hu]
    omega
  · rw [localFourierCoordinate_normalized]
    exact mul_ne_zero (laurentMonomial_ne_zero _) <|
      powerSeries_coe_ne_zero <| by
        intro h
        rw [h] at hu
        simp at hu

theorem localFourierReciprocalCoordinate_is_exact_ramified_power
    {E : ℕ} (hE : 0 < E) (R : ℕ) (u : PowerSeries ℂ)
    (hu : u.constantCoeff = 1) :
    ∃ phi : LaurentSeries ℂ ≃ₐ[ℂ] LaurentSeries ℂ,
      localFourierReciprocalCoordinate R (normalizedIrregularValue R E u) =
        phi ((PowerSeries.X ^ E : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have huInv : (u⁻¹).constantCoeff = 1 := by simp [hu]
  refine ⟨laurentAlgReparametrization E u⁻¹ huInv, ?_⟩
  rw [localFourierReciprocalCoordinate_normalized R E u hu,
    laurentAlgReparametrization_X_pow hE u⁻¹ huInv]

end
end LaurentFourier

namespace Characteristic

open FormalUniformizer LaurentFourier

noncomputable section

def canonicalLaurent {R beta : ℕ}
    (c : Characteristic R beta) : LaurentSeries ℂ :=
  match c with
  | .terminal _ _ _ => laurentMonomial (-(beta : ℤ))
  | .step _ _ _ _ _ tail =>
      laurentMonomial (-(beta : ℤ)) + tail.canonicalLaurent

theorem firstExponent_pos {R beta : ℕ} (c : Characteristic R beta) : 0 < beta := by
  cases c with
  | terminal _ hbeta _ => exact hbeta
  | step _ _ hbeta _ _ _ => exact hbeta

theorem canonicalLaurent_order {R beta : ℕ}
    (c : Characteristic R beta) : c.canonicalLaurent.order = -(beta : ℤ) := by
  induction c with
  | terminal hR hbeta hgcd =>
      exact laurentMonomial_order _
  | @step R E beta gamma hER hE hbeta hgcd hgamma tail ih =>
      have htail : tail.canonicalLaurent ≠ 0 := by
        intro h
        rw [h, HahnSeries.order_zero] at ih
        have := tail.firstExponent_pos
        omega
      have hlt : (laurentMonomial (-(beta : ℤ))).orderTop <
          tail.canonicalLaurent.orderTop := by
        rw [laurentMonomial_orderTop,
          ← HahnSeries.order_eq_orderTop_of_ne_zero htail, ih]
        have hgammaZ : (gamma : ℤ) < (beta : ℤ) := by exact_mod_cast hgamma
        exact_mod_cast Int.neg_lt_neg hgammaZ
      have haddTop := HahnSeries.orderTop_add_eq_left hlt
      have hadd : laurentMonomial (-(beta : ℤ)) + tail.canonicalLaurent ≠ 0 := by
        apply HahnSeries.orderTop_ne_top.mp
        rw [haddTop, laurentMonomial_orderTop]
        exact WithTop.coe_ne_top
      rw [canonicalLaurent]
      apply WithTop.coe_injective
      rw [HahnSeries.order_eq_orderTop_of_ne_zero hadd, haddTop,
        laurentMonomial_orderTop]

theorem canonicalLaurent_leadingCoeff {R beta : ℕ}
    (c : Characteristic R beta) : c.canonicalLaurent.leadingCoeff = 1 := by
  induction c with
  | terminal => simp [canonicalLaurent, laurentMonomial]
  | @step R E beta gamma hER hE hbeta hgcd hgamma tail ih =>
      have htail : tail.canonicalLaurent ≠ 0 := by
        intro h
        have hord := tail.canonicalLaurent_order
        rw [h, HahnSeries.order_zero] at hord
        have := tail.firstExponent_pos
        omega
      have hlt : (laurentMonomial (-(beta : ℤ))).orderTop <
          tail.canonicalLaurent.orderTop := by
        rw [laurentMonomial_orderTop,
          ← HahnSeries.order_eq_orderTop_of_ne_zero htail,
          tail.canonicalLaurent_order]
        have hgammaZ : (gamma : ℤ) < (beta : ℤ) := by exact_mod_cast hgamma
        exact_mod_cast Int.neg_lt_neg hgammaZ
      rw [canonicalLaurent,
        HahnSeries.leadingCoeff_add_eq_left hlt]
      simp [laurentMonomial]

theorem canonicalLaurent_powerSeriesPart_constantCoeff
    {R beta : ℕ} (c : Characteristic R beta) :
    c.canonicalLaurent.powerSeriesPart.constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    LaurentSeries.powerSeriesPart_coeff]
  simpa [HahnSeries.leadingCoeff_eq] using c.canonicalLaurent_leadingCoeff

theorem canonicalLaurent_eq_normalizedIrregularValue
    {R beta E : ℕ} (c : Characteristic R beta) (hbeta : beta = R + E) :
    c.canonicalLaurent = normalizedIrregularValue R E
      c.canonicalLaurent.powerSeriesPart := by
  rw [normalizedIrregularValue]
  have hdecomp := c.canonicalLaurent.single_order_mul_powerSeriesPart
  rw [c.canonicalLaurent_order] at hdecomp
  rw [← hbeta]
  exact hdecomp.symm

theorem isAiryTower_firstExponent_eq
    {R beta : ℕ} (c : Characteristic R beta) (hc : c.IsAiryTower) :
    beta = R + c.nextRamification := by
  cases c with
  | terminal => simpa [IsAiryTower, nextRamification] using hc
  | step => exact hc.1

/-- An actual coefficient-one Laurent characteristic in the negative Airy branch has reciprocal
Fourier coordinate of exact order `E`, and an invertible formal change of uniformizer identifies
that coordinate with `X^E`. -/
theorem airyTower_negativeFourier_exact_uniformizer
    {R beta : ℕ} (c : Characteristic R beta) (hc : c.IsAiryTower) :
    ∃ u : PowerSeries ℂ,
      u.constantCoeff = 1 ∧
      c.canonicalLaurent = normalizedIrregularValue R c.nextRamification u ∧
      (localFourierCoordinate R c.canonicalLaurent).order =
        -(c.nextRamification : ℤ) ∧
      (localFourierReciprocalCoordinate R c.canonicalLaurent).order =
        (c.nextRamification : ℤ) ∧
      ∃ phi : LaurentSeries ℂ ≃ₐ[ℂ] LaurentSeries ℂ,
        localFourierReciprocalCoordinate R c.canonicalLaurent =
          phi ((PowerSeries.X ^ c.nextRamification : PowerSeries ℂ) :
            LaurentSeries ℂ) := by
  let u := c.canonicalLaurent.powerSeriesPart
  have hu : u.constantCoeff = 1 :=
    c.canonicalLaurent_powerSeriesPart_constantCoeff
  have hform : c.canonicalLaurent =
      normalizedIrregularValue R c.nextRamification u :=
    c.canonicalLaurent_eq_normalizedIrregularValue
      (c.isAiryTower_firstExponent_eq hc)
  refine ⟨u, hu, hform, ?_, ?_, ?_⟩
  · rw [hform]
    exact localFourierCoordinate_normalized_order R c.nextRamification u hu
  · rw [hform]
    exact localFourierReciprocalCoordinate_normalized_order
      R c.nextRamification u hu
  · rw [hform]
    exact localFourierReciprocalCoordinate_is_exact_ramified_power
      c.nextRamification_pos R u hu

end
end Characteristic
end IrregularStokes
end GaloisForLFunctions
