/-
# Physical-scale discrete parabola decoupling

The arithmetic two-torus sixth moment is transported to the physical
decoupling scale.  For `H` frequencies, the change of variables

`u = x / H`, `v = y / H²`

sends `[0,H²]²` to `[0,H] × [0,1]`.  Unit periodicity in `u` then gives
exactly `H` copies of the unit-square moment.  Consequently the normalized
physical-box moment is exactly the torus moment, before applying the
subpower bound.
-/
import GaloisForLFunctions.RHTower.BourgainPlanarDiscreteDecoupling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Unit periodicity of Bourgain's additive character. -/
theorem bourgainUnitCharacter_add_one (x : ℝ) :
    bourgainUnitCharacter (x + 1) = bourgainUnitCharacter x := by
  simp only [bourgainUnitCharacter]
  rw [show
    2 * (Real.pi : ℂ) * Complex.I * ((x + 1 : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I by
      push_cast
      ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The discrete parabola extension is periodic in its linear phase
variable. -/
theorem periodic_bourgainDiscreteParabolaExtension_first
    (H : ℕ) (a : Fin H → ℂ) (v : ℝ) :
    Function.Periodic
      (fun u => bourgainDiscreteParabolaExtension H a u v) 1 := by
  intro u
  change
    bourgainDiscreteParabolaExtension H a (u + 1) v =
      bourgainDiscreteParabolaExtension H a u v
  rw [bourgainDiscreteParabolaExtension_eq_twoTorus,
    bourgainDiscreteParabolaExtension_eq_twoTorus,
    bourgainUnitCharacter_add_one]

/-- Sixth powers of the extension norm inherit unit periodicity. -/
theorem periodic_norm_bourgainDiscreteParabolaExtension_pow_six_first
    (H : ℕ) (a : Fin H → ℂ) (v : ℝ) :
    Function.Periodic
      (fun u =>
        ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ)) 1 := by
  intro u
  change
    ‖bourgainDiscreteParabolaExtension H a (u + 1) v‖ ^ (6 : ℕ) =
      ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ)
  have hphase :=
    periodic_bourgainDiscreteParabolaExtension_first H a v u
  change
    bourgainDiscreteParabolaExtension H a (u + 1) v =
      bourgainDiscreteParabolaExtension H a u v at hphase
  rw [hphase]

/-- Integrating the periodic extension over `H` linear periods gives `H`
times its unit-period integral. -/
theorem integral_zero_nat_bourgainDiscreteParabolaExtension_pow_six
    (H : ℕ) (a : Fin H → ℂ) (v : ℝ) :
    (∫ u in (0 : ℝ)..(H : ℝ),
      ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ)) =
      (H : ℝ) *
        ∫ u in (0 : ℝ)..1,
          ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ) := by
  let f : ℝ → ℝ := fun u =>
    ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ)
  have hperiod : Function.Periodic f 1 :=
    periodic_norm_bourgainDiscreteParabolaExtension_pow_six_first H a v
  have hcont : Continuous f := by
    unfold f bourgainDiscreteParabolaExtension bourgainUnitCharacter
    fun_prop
  have hint : ∀ s t : ℝ, IntervalIntegrable f MeasureTheory.volume s t :=
    fun s t => hcont.intervalIntegrable (μ := MeasureTheory.volume) s t
  have hmultiple :=
    hperiod.intervalIntegral_add_zsmul_eq (H : ℤ) 0 hint
  simpa [f] using hmultiple

/-- Physical-scale discrete parabola extension. -/
def bourgainScaledParabolaExtension
    (H : ℕ) (a : Fin H → ℂ) (x y : ℝ) : ℂ :=
  bourgainDiscreteParabolaExtension H a
    (x / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ))

/-- The discrete parabola extension is periodic in its quadratic phase
variable. -/
theorem periodic_bourgainDiscreteParabolaExtension_second
    (H : ℕ) (a : Fin H → ℂ) (u : ℝ) :
    Function.Periodic
      (fun v => bourgainDiscreteParabolaExtension H a u v) 1 := by
  intro v
  change
    bourgainDiscreteParabolaExtension H a u (v + 1) =
      bourgainDiscreteParabolaExtension H a u v
  rw [bourgainDiscreteParabolaExtension_eq_twoTorus,
    bourgainDiscreteParabolaExtension_eq_twoTorus,
    bourgainUnitCharacter_add_one]

/-- The physical extension has period `H` in its linear coordinate. -/
theorem periodic_bourgainScaledParabolaExtension_first
    (H : ℕ) (hH : 0 < H) (a : Fin H → ℂ) (y : ℝ) :
    Function.Periodic
      (fun x => bourgainScaledParabolaExtension H a x y) (H : ℝ) := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  intro x
  unfold bourgainScaledParabolaExtension
  have hquot :
      (x + (H : ℝ)) / (H : ℝ) = x / (H : ℝ) + 1 := by
    field_simp
  change
    bourgainDiscreteParabolaExtension H a
        ((x + (H : ℝ)) / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ)) =
      bourgainDiscreteParabolaExtension H a
        (x / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ))
  rw [hquot]
  have hperiod :=
    periodic_bourgainDiscreteParabolaExtension_first H a
      (y / (H : ℝ) ^ (2 : ℕ)) (x / (H : ℝ))
  change
    bourgainDiscreteParabolaExtension H a
        (x / (H : ℝ) + 1) (y / (H : ℝ) ^ (2 : ℕ)) =
      bourgainDiscreteParabolaExtension H a
        (x / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ)) at hperiod
  exact hperiod

/-- The physical extension has period `H²` in its quadratic coordinate. -/
theorem periodic_bourgainScaledParabolaExtension_second
    (H : ℕ) (hH : 0 < H) (a : Fin H → ℂ) (x : ℝ) :
    Function.Periodic
      (fun y => bourgainScaledParabolaExtension H a x y)
      ((H : ℝ) ^ (2 : ℕ)) := by
  have hH20 : (H : ℝ) ^ (2 : ℕ) ≠ 0 := by positivity
  intro y
  unfold bourgainScaledParabolaExtension
  have hquot :
      (y + (H : ℝ) ^ (2 : ℕ)) / (H : ℝ) ^ (2 : ℕ) =
        y / (H : ℝ) ^ (2 : ℕ) + 1 := by
    field_simp
  change
    bourgainDiscreteParabolaExtension H a
        (x / (H : ℝ))
        ((y + (H : ℝ) ^ (2 : ℕ)) / (H : ℝ) ^ (2 : ℕ)) =
      bourgainDiscreteParabolaExtension H a
        (x / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ))
  rw [hquot]
  have hperiod :=
    periodic_bourgainDiscreteParabolaExtension_second H a
      (x / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ))
  change
    bourgainDiscreteParabolaExtension H a
        (x / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ) + 1) =
      bourgainDiscreteParabolaExtension H a
        (x / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ)) at hperiod
  exact hperiod

/-- Exact transport of the physical `[0,H²]²` sixth moment to the
unit-square sixth moment. -/
theorem integral_scaledParabola_physicalSquare_eq
    (H : ℕ) (hH : 0 < H) (a : Fin H → ℂ) :
    (∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
      ∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
      (H : ℝ) ^ (4 : ℕ) *
        ∫ v in (0 : ℝ)..1,
          ∫ u in (0 : ℝ)..1,
            ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ) := by
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  have hH20 : (H : ℝ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hH0
  unfold bourgainScaledParabolaExtension
  have hx (y : ℝ) :
      (∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ‖bourgainDiscreteParabolaExtension H a
          (x / (H : ℝ)) (y / (H : ℝ) ^ (2 : ℕ))‖ ^ (6 : ℕ)) =
        (H : ℝ) *
          ∫ u in (0 : ℝ)..(H : ℝ),
            ‖bourgainDiscreteParabolaExtension H a u
              (y / (H : ℝ) ^ (2 : ℕ))‖ ^ (6 : ℕ) := by
    have hchange :=
      intervalIntegral.integral_comp_div
        (fun u : ℝ =>
          ‖bourgainDiscreteParabolaExtension H a u
            (y / (H : ℝ) ^ (2 : ℕ))‖ ^ (6 : ℕ))
        hH0
        (a := (0 : ℝ)) (b := (H : ℝ) ^ (2 : ℕ))
    have hquot :
        (H : ℝ) ^ (2 : ℕ) / (H : ℝ) = (H : ℝ) := by
      field_simp
    rw [hquot] at hchange
    simpa using hchange
  simp_rw [hx]
  rw [intervalIntegral.integral_const_mul]
  have hychange :=
    intervalIntegral.integral_comp_div
      (fun v : ℝ =>
        ∫ u in (0 : ℝ)..(H : ℝ),
          ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ))
      hH20
      (a := (0 : ℝ)) (b := (H : ℝ) ^ (2 : ℕ))
  rw [hychange]
  simp only [zero_div, div_self hH20]
  simp_rw [integral_zero_nat_bourgainDiscreteParabolaExtension_pow_six]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Translation of the physical square does not change the sixth moment. -/
theorem integral_scaledParabola_translatedPhysicalSquare_eq
    (H : ℕ) (hH : 0 < H) (a : Fin H → ℂ) (x₀ y₀ : ℝ) :
    (∫ y in y₀..y₀ + (H : ℝ) ^ (2 : ℕ),
      ∫ x in x₀..x₀ + (H : ℝ) ^ (2 : ℕ),
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
      ∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
        ∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ) := by
  have hx (y : ℝ) :
      (∫ x in x₀..x₀ + (H : ℝ) ^ (2 : ℕ),
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
        ∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ) := by
    have hperiod :
        Function.Periodic
          (fun x =>
            ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ))
          (H : ℝ) := by
      intro x
      have hphase :=
        periodic_bourgainScaledParabolaExtension_first H hH a y x
      change
        bourgainScaledParabolaExtension H a (x + (H : ℝ)) y =
          bourgainScaledParabolaExtension H a x y at hphase
      change
        ‖bourgainScaledParabolaExtension H a (x + (H : ℝ)) y‖ ^ (6 : ℕ) =
          ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)
      rw [hphase]
    have hperiod_sq := hperiod.nsmul H
    have hscale :
        H • (H : ℝ) = (H : ℝ) ^ (2 : ℕ) := by
      simp only [nsmul_eq_mul]
      ring
    rw [hscale] at hperiod_sq
    simpa using hperiod_sq.intervalIntegral_add_eq x₀ 0
  rw [show
    (fun y : ℝ =>
      ∫ x in x₀..x₀ + (H : ℝ) ^ (2 : ℕ),
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
      (fun y : ℝ =>
        ∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) by
      funext y
      exact hx y]
  have hyperiod :
      Function.Periodic
        (fun y =>
          ∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ))
        ((H : ℝ) ^ (2 : ℕ)) := by
    intro y
    apply intervalIntegral.integral_congr
    intro x _
    have hphase :=
      periodic_bourgainScaledParabolaExtension_second H hH a x y
    change
      bourgainScaledParabolaExtension H a x
          (y + (H : ℝ) ^ (2 : ℕ)) =
        bourgainScaledParabolaExtension H a x y at hphase
    change
      ‖bourgainScaledParabolaExtension H a x
          (y + (H : ℝ) ^ (2 : ℕ))‖ ^ (6 : ℕ) =
        ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)
    rw [hphase]
  simpa using hyperiod.intervalIntegral_add_eq y₀ 0

/-- Exact equality of normalized physical and unit-square sixth moments. -/
theorem normalized_integral_scaledParabola_physicalSquare_eq
    (H : ℕ) (hH : 0 < H) (a : Fin H → ℂ) :
    ((H : ℝ) ^ (4 : ℕ))⁻¹ *
        (∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
          ∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
            ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) =
      ∫ v in (0 : ℝ)..1,
        ∫ u in (0 : ℝ)..1,
          ‖bourgainDiscreteParabolaExtension H a u v‖ ^ (6 : ℕ) := by
  rw [integral_scaledParabola_physicalSquare_eq H hH a]
  have hH0 : (H : ℝ) ^ (4 : ℕ) ≠ 0 := by positivity
  field_simp

/-- **Unconditional physical-scale discrete planar `L⁶` decoupling.**
The normalized sixth moment on `[0,H²]²` has only subpower loss over
the cube of the coefficient `ℓ²` mass. -/
theorem normalized_integral_scaledParabola_physicalSquare_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H → ∀ a : Fin H → ℂ,
        ((H : ℝ) ^ (4 : ℕ))⁻¹ *
            (∫ y in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
              ∫ x in (0 : ℝ)..(H : ℝ) ^ (2 : ℕ),
                ‖bourgainScaledParabolaExtension H a x y‖ ^ (6 : ℕ)) ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, hbound⟩ :=
    integral_unitSquare_discreteParabola_norm_pow_six_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H hH a
  rw [normalized_integral_scaledParabola_physicalSquare_eq H hH a]
  exact hbound H a

end

end RHTower
