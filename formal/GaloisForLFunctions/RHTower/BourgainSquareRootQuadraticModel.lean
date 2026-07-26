/-
# Quadratic localization of Bourgain's square-root curve

This module connects the exact curve
`(t,t²,t^(3/2),t^(1/2))` to the physical discrete parabola model.  It proves
the exact osculating-sum identity at an arbitrary denominator scale and
replaces Bourgain's suppressed Taylor multiplier by an explicit
`‖x‖ δ³` error.
-/
import GaloisForLFunctions.RHTower.BourgainOsculatingPlanarTransfer
import GaloisForLFunctions.RHTower.BourgainSixfoldCloud

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Real-parameter version of Bourgain's square-root moment curve. -/
def bourgainSquareRootCurve (t : ℝ) : BourgainPhaseSpace :=
  ![t, t ^ (2 : ℕ), t ^ (3 / 2 : ℝ), t ^ (1 / 2 : ℝ)]

/-- Scalar phase obtained by pairing with the square-root curve. -/
def bourgainSquareRootCurvePhase
    (x : BourgainPhaseSpace) (t : ℝ) : ℝ :=
  bourgainDot x (bourgainSquareRootCurve t)

/-- First-order phase coordinate at the base point `a²`. -/
def bourgainSquareRootLinearPhaseCoordinate
    (a : ℝ) (x : BourgainPhaseSpace) : ℝ :=
  x 0 + 2 * a ^ 2 * x 1 + (3 * a / 2) * x 2 +
    (1 / (2 * a)) * x 3

/-- Half of the second-order phase coordinate at the base point `a²`. -/
def bourgainSquareRootQuadraticPhaseCoordinate
    (a : ℝ) (x : BourgainPhaseSpace) : ℝ :=
  x 1 + (3 / (8 * a)) * x 2 - (1 / (8 * a ^ 3)) * x 3

/-- Literal quadratic Taylor phase at the base point `a²`. -/
def bourgainSquareRootQuadraticLocalPhase
    (a : ℝ) (x : BourgainPhaseSpace) (s : ℝ) : ℝ :=
  bourgainSquareRootCurvePhase x (a ^ 2) +
    bourgainSquareRootLinearPhaseCoordinate a x * s +
    bourgainSquareRootQuadraticPhaseCoordinate a x * s ^ (2 : ℕ)

/-- Finite exponential sum using the quadratic local phase. -/
def bourgainSquareRootQuadraticLocalSum
    (H : ℕ) (D a : ℝ) (c : Fin H → ℂ)
    (x : BourgainPhaseSpace) : ℂ :=
  ∑ n : Fin H,
    c n * bourgainUnitCharacter
      (bourgainSquareRootQuadraticLocalPhase a x
        ((bourgainIndex n : ℝ) / D))

/-- Finite exponential sum on the exact curve over the same local samples. -/
def bourgainSquareRootExactLocalSum
    (H : ℕ) (D a : ℝ) (c : Fin H → ℂ)
    (x : BourgainPhaseSpace) : ℂ :=
  ∑ n : Fin H,
    c n * bourgainUnitCharacter
      (bourgainSquareRootCurvePhase x
        (a ^ 2 + (bourgainIndex n : ℝ) / D))

/-- Anisotropic scaling of both planar phase-coordinate pairs. -/
def bourgainParabolaPhaseScale
    (scale : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![scale * y 0, scale ^ (2 : ℕ) * y 1,
    scale * y 2, scale ^ (2 : ℕ) * y 3]

theorem bourgainUnitCharacter_add (u v : ℝ) :
    bourgainUnitCharacter (u + v) =
      bourgainUnitCharacter u * bourgainUnitCharacter v := by
  unfold bourgainUnitCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem bourgainUnitCharacter_eq_bourgainOscillation (u : ℝ) :
    bourgainUnitCharacter u =
      bourgainOscillation (2 * Real.pi * u) := by
  unfold bourgainUnitCharacter bourgainOscillation
  congr 1
  push_cast
  ring

theorem bourgainSquareRootLinearPhaseCoordinate_eq
    {a b : ℝ} (x : BourgainPhaseSpace) :
    bourgainSquareRootLinearPhaseCoordinate a x =
      bourgainSquareRootPhaseCoordinates a b x 0 := by
  simp [bourgainSquareRootLinearPhaseCoordinate]

theorem bourgainSquareRootQuadraticPhaseCoordinate_eq
    {a b : ℝ} (x : BourgainPhaseSpace) :
    bourgainSquareRootQuadraticPhaseCoordinate a x =
      bourgainSquareRootPhaseCoordinates a b x 1 := by
  simp [bourgainSquareRootQuadraticPhaseCoordinate]

theorem bourgainSquareRootLinearPhaseCoordinate_eq_right
    {a b : ℝ} (x : BourgainPhaseSpace) :
    bourgainSquareRootLinearPhaseCoordinate b x =
      bourgainSquareRootPhaseCoordinates a b x 2 := by
  simp [bourgainSquareRootLinearPhaseCoordinate]

theorem bourgainSquareRootQuadraticPhaseCoordinate_eq_right
    {a b : ℝ} (x : BourgainPhaseSpace) :
    bourgainSquareRootQuadraticPhaseCoordinate b x =
      bourgainSquareRootPhaseCoordinates a b x 3 := by
  simp [bourgainSquareRootQuadraticPhaseCoordinate]

/-- Exact identity between the local quadratic sum and a physical scaled
parabola extension, up to a unit-modulus constant phase. -/
theorem bourgainSquareRootQuadraticLocalSum_eq_scaledParabola
    (H : ℕ) (hH : 0 < H) {D a : ℝ} (hD : D ≠ 0)
    (c : Fin H → ℂ) (x : BourgainPhaseSpace) :
    bourgainSquareRootQuadraticLocalSum H D a c x =
      bourgainUnitCharacter (bourgainSquareRootCurvePhase x (a ^ 2)) *
        bourgainScaledParabolaExtension H c
          (((H : ℝ) / D) *
            bourgainSquareRootLinearPhaseCoordinate a x)
          ((((H : ℝ) / D) ^ (2 : ℕ)) *
            bourgainSquareRootQuadraticPhaseCoordinate a x) := by
  have hHr : (H : ℝ) ≠ 0 := by positivity
  unfold bourgainSquareRootQuadraticLocalSum
    bourgainSquareRootQuadraticLocalPhase
    bourgainScaledParabolaExtension
    bourgainDiscreteParabolaExtension
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro n
  have hphase :
      bourgainSquareRootCurvePhase x (a ^ 2) +
          bourgainSquareRootLinearPhaseCoordinate a x *
            ((bourgainIndex n : ℝ) / D) +
          bourgainSquareRootQuadraticPhaseCoordinate a x *
            ((bourgainIndex n : ℝ) / D) ^ (2 : ℕ) =
        bourgainSquareRootCurvePhase x (a ^ 2) +
          ((bourgainIndex n : ℝ) *
              ((((H : ℝ) / D) *
                bourgainSquareRootLinearPhaseCoordinate a x) /
                  (H : ℝ)) +
            (bourgainIndex n : ℝ) ^ (2 : ℕ) *
              ((((H : ℝ) / D) ^ (2 : ℕ) *
                bourgainSquareRootQuadraticPhaseCoordinate a x) /
                  (H : ℝ) ^ (2 : ℕ))) := by
    field_simp
    ring
  rw [hphase, bourgainUnitCharacter_add]
  ring

theorem norm_bourgainSquareRootQuadraticLocalSum
    (H : ℕ) (hH : 0 < H) {D a : ℝ} (hD : D ≠ 0)
    (c : Fin H → ℂ) (x : BourgainPhaseSpace) :
    ‖bourgainSquareRootQuadraticLocalSum H D a c x‖ =
      ‖bourgainScaledParabolaExtension H c
          (((H : ℝ) / D) *
            bourgainSquareRootLinearPhaseCoordinate a x)
          ((((H : ℝ) / D) ^ (2 : ℕ)) *
            bourgainSquareRootQuadraticPhaseCoordinate a x)‖ := by
  rw [bourgainSquareRootQuadraticLocalSum_eq_scaledParabola H hH hD]
  rw [norm_mul, norm_bourgainUnitCharacter, one_mul]

/-- The two local quadratic sums are exactly the two independent planar
factors evaluated in the anisotropically scaled phase coordinates. -/
theorem quadraticLocalSum_bilinearIntegrand_eq
    (H : ℕ) (hH : 0 < H) {D a b : ℝ} (hD : D ≠ 0)
    (c₁ c₂ : Fin H → ℂ) (x : BourgainPhaseSpace) :
    ‖bourgainSquareRootQuadraticLocalSum H D a c₁ x‖ ^ (6 : ℕ) *
        ‖bourgainSquareRootQuadraticLocalSum H D b c₂ x‖ ^ (6 : ℕ) =
      bourgainScaledIndependentPlanarBilinearIntegrand H c₁ c₂
        (bourgainParabolaPhaseScale ((H : ℝ) / D)
          (bourgainSquareRootPhaseCoordinates a b x)) := by
  rw [norm_bourgainSquareRootQuadraticLocalSum H hH hD,
    norm_bourgainSquareRootQuadraticLocalSum H hH hD]
  unfold bourgainScaledIndependentPlanarBilinearIntegrand
    bourgainScaledPlanarSixthMass bourgainParabolaPhaseScale
  rw [← bourgainSquareRootLinearPhaseCoordinate_eq (b := b),
    ← bourgainSquareRootQuadraticPhaseCoordinate_eq (b := b),
    ← bourgainSquareRootLinearPhaseCoordinate_eq_right (a := a),
    ← bourgainSquareRootQuadraticPhaseCoordinate_eq_right (a := a)]
  rfl

theorem iteratedDeriv_bourgainSquareRootCurvePhase_one_sq
    {a : ℝ} (ha : 0 < a) (x : BourgainPhaseSpace) :
    iteratedDeriv 1 (bourgainSquareRootCurvePhase x) (a ^ 2) =
      bourgainSquareRootLinearPhaseCoordinate a x := by
  have hfun :
      bourgainSquareRootCurvePhase x =
        fun t : ℝ =>
          x 0 * t + x 1 * t ^ (2 : ℕ) +
            x 2 * t ^ (3 / 2 : ℝ) + x 3 * t ^ (1 / 2 : ℝ) := by
    funext t
    simp [bourgainSquareRootCurvePhase, bourgainDot,
      bourgainSquareRootCurve, Fin.sum_univ_four]
  rw [hfun]
  unfold bourgainSquareRootLinearPhaseCoordinate
  change iteratedDeriv 1
      (((fun t : ℝ => x 0 * t) +
        (fun t : ℝ => x 1 * t ^ (2 : ℕ))) +
        (fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ)) +
        (fun t : ℝ => x 3 * t ^ (1 / 2 : ℝ)))
      (a ^ 2) =
    x 0 + 2 * a ^ 2 * x 1 + (3 * a / 2) * x 2 +
      (1 / (2 * a)) * x 3
  have h0 : ContDiffAt ℝ 1 (fun t : ℝ => x 0 * t) (a ^ 2) := by
    fun_prop
  have h1 : ContDiffAt ℝ 1
      (fun t : ℝ => x 1 * t ^ (2 : ℕ)) (a ^ 2) := by
    fun_prop
  have h2 : ContDiffAt ℝ 1
      (fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ)) (a ^ 2) :=
    contDiffAt_const.mul
      (Real.contDiffAt_rpow_const_of_ne (pow_ne_zero 2 ha.ne'))
  have h3 : ContDiffAt ℝ 1
      (fun t : ℝ => x 3 * t ^ (1 / 2 : ℝ)) (a ^ 2) :=
    contDiffAt_const.mul
      (Real.contDiffAt_rpow_const_of_ne (pow_ne_zero 2 ha.ne'))
  have hout := iteratedDeriv_add (n := 1)
    (f := ((fun t : ℝ => x 0 * t) +
      (fun t : ℝ => x 1 * t ^ (2 : ℕ))) +
      (fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ)))
    (g := fun t : ℝ => x 3 * t ^ (1 / 2 : ℝ))
    ((h0.add h1).add h2) h3
  rw [hout]
  have hmid := iteratedDeriv_add (n := 1)
    (f := (fun t : ℝ => x 0 * t) +
      (fun t : ℝ => x 1 * t ^ (2 : ℕ)))
    (g := fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ))
    (h0.add h1) h2
  rw [hmid]
  have hinn := iteratedDeriv_add (n := 1)
    (f := fun t : ℝ => x 0 * t)
    (g := fun t : ℝ => x 1 * t ^ (2 : ℕ)) h0 h1
  rw [hinn]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  have hp3 := iteratedDeriv_rpow_three_halves_one_sq ha
  have hp1 := iteratedDeriv_rpow_half_one_sq ha
  rw [hp3, hp1]
  norm_num [iteratedDeriv_eq_iterate, iter_deriv_pow]
  ring

theorem iteratedDeriv_bourgainSquareRootCurvePhase_two_sq
    {a : ℝ} (ha : 0 < a) (x : BourgainPhaseSpace) :
    iteratedDeriv 2 (bourgainSquareRootCurvePhase x) (a ^ 2) =
      2 * bourgainSquareRootQuadraticPhaseCoordinate a x := by
  have hfun :
      bourgainSquareRootCurvePhase x =
        fun t : ℝ =>
          x 0 * t + x 1 * t ^ (2 : ℕ) +
            x 2 * t ^ (3 / 2 : ℝ) + x 3 * t ^ (1 / 2 : ℝ) := by
    funext t
    simp [bourgainSquareRootCurvePhase, bourgainDot,
      bourgainSquareRootCurve, Fin.sum_univ_four]
  rw [hfun]
  unfold bourgainSquareRootQuadraticPhaseCoordinate
  change iteratedDeriv 2
      (((fun t : ℝ => x 0 * t) +
        (fun t : ℝ => x 1 * t ^ (2 : ℕ))) +
        (fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ)) +
        (fun t : ℝ => x 3 * t ^ (1 / 2 : ℝ)))
      (a ^ 2) =
    2 * (x 1 + (3 / (8 * a)) * x 2 -
      (1 / (8 * a ^ 3)) * x 3)
  have h0 : ContDiffAt ℝ 2 (fun t : ℝ => x 0 * t) (a ^ 2) := by
    fun_prop
  have h1 : ContDiffAt ℝ 2
      (fun t : ℝ => x 1 * t ^ (2 : ℕ)) (a ^ 2) := by
    fun_prop
  have h2 : ContDiffAt ℝ 2
      (fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ)) (a ^ 2) :=
    contDiffAt_const.mul
      (Real.contDiffAt_rpow_const_of_ne (pow_ne_zero 2 ha.ne'))
  have h3 : ContDiffAt ℝ 2
      (fun t : ℝ => x 3 * t ^ (1 / 2 : ℝ)) (a ^ 2) :=
    contDiffAt_const.mul
      (Real.contDiffAt_rpow_const_of_ne (pow_ne_zero 2 ha.ne'))
  have hout := iteratedDeriv_add (n := 2)
    (f := ((fun t : ℝ => x 0 * t) +
      (fun t : ℝ => x 1 * t ^ (2 : ℕ))) +
      (fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ)))
    (g := fun t : ℝ => x 3 * t ^ (1 / 2 : ℝ))
    ((h0.add h1).add h2) h3
  rw [hout]
  have hmid := iteratedDeriv_add (n := 2)
    (f := (fun t : ℝ => x 0 * t) +
      (fun t : ℝ => x 1 * t ^ (2 : ℕ)))
    (g := fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ))
    (h0.add h1) h2
  rw [hmid]
  have hinn := iteratedDeriv_add (n := 2)
    (f := fun t : ℝ => x 0 * t)
    (g := fun t : ℝ => x 1 * t ^ (2 : ℕ)) h0 h1
  rw [hinn]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_rpow_three_halves_two_sq ha,
    iteratedDeriv_rpow_half_two_sq ha]
  norm_num [iteratedDeriv_eq_iterate, iter_deriv_pow]
  ring

/-- Exact third derivative of the scalar square-root-curve phase. -/
theorem iteratedDeriv_bourgainSquareRootCurvePhase_three
    {y : ℝ} (hy : 0 < y) (x : BourgainPhaseSpace) :
    iteratedDeriv 3 (bourgainSquareRootCurvePhase x) y =
      -(3 / 8 : ℝ) * x 2 * y ^ (-(3 / 2 : ℝ)) +
        (3 / 8 : ℝ) * x 3 * y ^ (-(5 / 2 : ℝ)) := by
  have hfun :
      bourgainSquareRootCurvePhase x =
        fun t : ℝ =>
          x 0 * t + x 1 * t ^ (2 : ℕ) +
            x 2 * t ^ (3 / 2 : ℝ) + x 3 * t ^ (1 / 2 : ℝ) := by
    funext t
    simp [bourgainSquareRootCurvePhase, bourgainDot,
      bourgainSquareRootCurve, Fin.sum_univ_four]
  rw [hfun]
  change iteratedDeriv 3
      (((fun t : ℝ => x 0 * t) +
        (fun t : ℝ => x 1 * t ^ (2 : ℕ))) +
        (fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ)) +
        (fun t : ℝ => x 3 * t ^ (1 / 2 : ℝ))) y = _
  have h0 : ContDiffAt ℝ 3 (fun t : ℝ => x 0 * t) y := by
    fun_prop
  have h1 : ContDiffAt ℝ 3
      (fun t : ℝ => x 1 * t ^ (2 : ℕ)) y := by
    fun_prop
  have h2 : ContDiffAt ℝ 3
      (fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ)) y :=
    contDiffAt_const.mul
      (Real.contDiffAt_rpow_const_of_ne hy.ne')
  have h3 : ContDiffAt ℝ 3
      (fun t : ℝ => x 3 * t ^ (1 / 2 : ℝ)) y :=
    contDiffAt_const.mul
      (Real.contDiffAt_rpow_const_of_ne hy.ne')
  have hout := iteratedDeriv_add (n := 3)
    (f := ((fun t : ℝ => x 0 * t) +
      (fun t : ℝ => x 1 * t ^ (2 : ℕ))) +
      (fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ)))
    (g := fun t : ℝ => x 3 * t ^ (1 / 2 : ℝ))
    ((h0.add h1).add h2) h3
  rw [hout]
  have hmid := iteratedDeriv_add (n := 3)
    (f := (fun t : ℝ => x 0 * t) +
      (fun t : ℝ => x 1 * t ^ (2 : ℕ)))
    (g := fun t : ℝ => x 2 * t ^ (3 / 2 : ℝ))
    (h0.add h1) h2
  rw [hmid]
  have hinn := iteratedDeriv_add (n := 3)
    (f := fun t : ℝ => x 0 * t)
    (g := fun t : ℝ => x 1 * t ^ (2 : ℕ)) h0 h1
  rw [hinn]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  norm_num [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const,
    iter_deriv_pow, descPochhammer]
  ring

theorem norm_apply_le_norm_bourgainPhaseSpace
    (x : BourgainPhaseSpace) (i : Fin 4) :
    ‖x i‖ ≤ ‖x‖ := by
  rw [Pi.norm_def]
  exact_mod_cast
    (Finset.le_sup (f := fun j : Fin 4 => ‖x j‖₊)
      (Finset.mem_univ i))

theorem bourgain_rpow_neg_le_of_le
    {A y r : ℝ} (hA : 0 < A) (hAy : A ≤ y) (hr : 0 ≤ r) :
    y ^ (-r) ≤ A ^ (-r) := by
  have hy : 0 < y := hA.trans_le hAy
  rw [Real.rpow_neg hy.le, Real.rpow_neg hA.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hA r)
    (Real.rpow_le_rpow hA.le hAy hr)

/-- Uniform scalar third-derivative coefficient above the base point `a²`. -/
def bourgainSquareRootThirdDerivativeBound (a : ℝ) : ℝ :=
  (3 / 8 : ℝ) *
    ((a ^ 2) ^ (-(3 / 2 : ℝ)) +
      (a ^ 2) ^ (-(5 / 2 : ℝ)))

/-- The third derivative is bounded linearly in the physical frequency
norm, uniformly over the local interval. -/
theorem norm_iteratedDerivWithin_bourgainSquareRootCurvePhase_three_le
    {a δ y : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hy : y ∈ Set.Icc (a ^ 2) (a ^ 2 + δ))
    (x : BourgainPhaseSpace) :
    ‖iteratedDerivWithin 3 (bourgainSquareRootCurvePhase x)
        (Set.Icc (a ^ 2) (a ^ 2 + δ)) y‖ ≤
      ‖x‖ * bourgainSquareRootThirdDerivativeBound a := by
  have hinterval : a ^ 2 < a ^ 2 + δ := lt_add_of_pos_right _ hδ
  have hypos : 0 < y := (sq_pos_of_pos ha).trans_le hy.1
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc hinterval)
    (by
      have hfun :
          bourgainSquareRootCurvePhase x =
            fun t : ℝ =>
              x 0 * t + x 1 * t ^ (2 : ℕ) +
                x 2 * t ^ (3 / 2 : ℝ) + x 3 * t ^ (1 / 2 : ℝ) := by
        funext t
        simp [bourgainSquareRootCurvePhase, bourgainDot,
          bourgainSquareRootCurve, Fin.sum_univ_four]
      rw [hfun]
      have hpow3 : ContDiffAt ℝ 3
          (fun t : ℝ => t ^ (3 / 2 : ℝ)) y :=
        Real.contDiffAt_rpow_const_of_ne hypos.ne'
      have hpow1 : ContDiffAt ℝ 3
          (fun t : ℝ => t ^ (1 / 2 : ℝ)) y :=
        Real.contDiffAt_rpow_const_of_ne hypos.ne'
      exact (((contDiffAt_const.mul contDiffAt_id).add
          (contDiffAt_const.mul (contDiffAt_id.pow 2))).add
            (contDiffAt_const.mul hpow3)).add
              (contDiffAt_const.mul hpow1))
    hy]
  rw [iteratedDeriv_bourgainSquareRootCurvePhase_three hypos x]
  have hpow3 :
      y ^ (-(3 / 2 : ℝ)) ≤
        (a ^ 2) ^ (-(3 / 2 : ℝ)) := by
    exact bourgain_rpow_neg_le_of_le (sq_pos_of_pos ha) hy.1 (by norm_num)
  have hpow5 :
      y ^ (-(5 / 2 : ℝ)) ≤
        (a ^ 2) ^ (-(5 / 2 : ℝ)) := by
    exact bourgain_rpow_neg_le_of_le (sq_pos_of_pos ha) hy.1 (by norm_num)
  have hx2 := norm_apply_le_norm_bourgainPhaseSpace x (2 : Fin 4)
  have hx3 := norm_apply_le_norm_bourgainPhaseSpace x (3 : Fin 4)
  unfold bourgainSquareRootThirdDerivativeBound
  rw [Real.norm_eq_abs]
  calc
    |-(3 / 8 : ℝ) * x 2 * y ^ (-(3 / 2 : ℝ)) +
        (3 / 8 : ℝ) * x 3 * y ^ (-(5 / 2 : ℝ))| ≤
        |-(3 / 8 : ℝ) * x 2 * y ^ (-(3 / 2 : ℝ))| +
          |(3 / 8 : ℝ) * x 3 * y ^ (-(5 / 2 : ℝ))| :=
      abs_add_le _ _
    _ = (3 / 8 : ℝ) * |x 2| * y ^ (-(3 / 2 : ℝ)) +
          (3 / 8 : ℝ) * |x 3| * y ^ (-(5 / 2 : ℝ)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      rw [abs_of_nonneg (Real.rpow_nonneg hypos.le (-(3 / 2 : ℝ))),
        abs_of_nonneg (Real.rpow_nonneg hypos.le (-(5 / 2 : ℝ)))]
      norm_num
    _ ≤ (3 / 8 : ℝ) * ‖x‖ *
          (a ^ 2) ^ (-(3 / 2 : ℝ)) +
        (3 / 8 : ℝ) * ‖x‖ *
          (a ^ 2) ^ (-(5 / 2 : ℝ)) := by
      rw [Real.norm_eq_abs] at hx2 hx3
      apply add_le_add
      · gcongr
      · gcongr
    _ = ‖x‖ * (3 / 8 *
          ((a ^ 2) ^ (-(3 / 2 : ℝ)) +
            (a ^ 2) ^ (-(5 / 2 : ℝ)))) := by
      ring

theorem contDiffAt_bourgainSquareRootCurvePhase
    {a : ℝ} (ha : 0 < a) (x : BourgainPhaseSpace) (n : ℕ) :
    ContDiffAt ℝ n (bourgainSquareRootCurvePhase x) (a ^ 2) := by
  have hfun :
      bourgainSquareRootCurvePhase x =
        fun t : ℝ =>
          x 0 * t + x 1 * t ^ (2 : ℕ) +
            x 2 * t ^ (3 / 2 : ℝ) + x 3 * t ^ (1 / 2 : ℝ) := by
    funext t
    simp [bourgainSquareRootCurvePhase, bourgainDot,
      bourgainSquareRootCurve, Fin.sum_univ_four]
  rw [hfun]
  have hpow3 : ContDiffAt ℝ n
      (fun t : ℝ => t ^ (3 / 2 : ℝ)) (a ^ 2) :=
    Real.contDiffAt_rpow_const_of_ne (pow_ne_zero 2 ha.ne')
  have hpow1 : ContDiffAt ℝ n
      (fun t : ℝ => t ^ (1 / 2 : ℝ)) (a ^ 2) :=
    Real.contDiffAt_rpow_const_of_ne (pow_ne_zero 2 ha.ne')
  exact (((contDiffAt_const.mul contDiffAt_id).add
      (contDiffAt_const.mul (contDiffAt_id.pow 2))).add
        (contDiffAt_const.mul hpow3)).add
          (contDiffAt_const.mul hpow1)

/-- Closed formula for a second-order Taylor polynomial evaluated at a
point. -/
theorem taylorWithinEval_two_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f 2 s x₀ x =
      f x₀ + (x - x₀) • iteratedDerivWithin 1 f s x₀ +
        ((1 / 2 : ℝ) * (x - x₀) ^ (2 : ℕ)) •
          iteratedDerivWithin 2 f s x₀ := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    taylorWithinEval_succ f 1]
  rw [show taylorWithinEval f 1 s x₀ x =
      taylorWithinEval f (0 + 1) s x₀ x by rfl,
    taylorWithinEval_succ f 0]
  rw [taylor_within_zero_eval]
  norm_num

/-- Exact identification of the abstract Taylor evaluator with the literal
quadratic local phase. -/
theorem taylorWithinEval_bourgainSquareRootCurvePhase_two
    {a δ s : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (x : BourgainPhaseSpace) :
    taylorWithinEval (bourgainSquareRootCurvePhase x) 2
        (Set.Icc (a ^ 2) (a ^ 2 + δ)) (a ^ 2) (a ^ 2 + s) =
      bourgainSquareRootQuadraticLocalPhase a x s := by
  have hinterval : a ^ 2 < a ^ 2 + δ := lt_add_of_pos_right _ hδ
  have hbase : a ^ 2 ∈ Set.Icc (a ^ 2) (a ^ 2 + δ) :=
    ⟨le_rfl, hinterval.le⟩
  rw [taylorWithinEval_two_eq]
  rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hinterval)
      (contDiffAt_bourgainSquareRootCurvePhase ha x 1) hbase,
    iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hinterval)
      (contDiffAt_bourgainSquareRootCurvePhase ha x 2) hbase]
  rw [iteratedDeriv_bourgainSquareRootCurvePhase_one_sq ha,
    iteratedDeriv_bourgainSquareRootCurvePhase_two_sq ha]
  unfold bourgainSquareRootQuadraticLocalPhase
  simp only [add_sub_cancel_left, smul_eq_mul]
  ring

/-- Explicit finite-sum comparison between the exact square-root curve and
its quadratic osculating model on one short interval. -/
theorem norm_bourgainSquareRootExactLocalSum_le_quadratic
    (H : ℕ) {D a δ C : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hC0 : 0 ≤ C) (c : Fin H → ℂ) (x : BourgainPhaseSpace)
    (hsample :
      ∀ n : Fin H,
        a ^ 2 + (bourgainIndex n : ℝ) / D ∈
          Set.Icc (a ^ 2) (a ^ 2 + δ))
    (hC :
      ∀ y ∈ Set.Icc (a ^ 2) (a ^ 2 + δ),
        ‖iteratedDerivWithin 3 (bourgainSquareRootCurvePhase x)
          (Set.Icc (a ^ 2) (a ^ 2 + δ)) y‖ ≤ C) :
    ‖bourgainSquareRootExactLocalSum H D a c x‖ ≤
      ‖bourgainSquareRootQuadraticLocalSum H D a c x‖ +
        (2 * Real.pi * (C * δ ^ (3 : ℕ) / 2)) *
          ∑ n : Fin H, ‖c n‖ := by
  unfold bourgainSquareRootExactLocalSum
    bourgainSquareRootQuadraticLocalSum
  simp_rw [bourgainUnitCharacter_eq_bourgainOscillation]
  apply norm_sum_weighted_bourgainOscillation_le
  intro n hn
  have hcont :
      ContDiffOn ℝ 3 (bourgainSquareRootCurvePhase x)
        (Set.Icc (a ^ 2) (a ^ 2 + δ)) := by
    intro y hy
    have hypos : 0 < y := (sq_pos_of_pos ha).trans_le hy.1
    have hfun :
        bourgainSquareRootCurvePhase x =
          fun t : ℝ =>
            x 0 * t + x 1 * t ^ (2 : ℕ) +
              x 2 * t ^ (3 / 2 : ℝ) + x 3 * t ^ (1 / 2 : ℝ) := by
      funext t
      simp [bourgainSquareRootCurvePhase, bourgainDot,
        bourgainSquareRootCurve, Fin.sum_univ_four]
    rw [hfun]
    have hpow3 : ContDiffAt ℝ 3
        (fun t : ℝ => t ^ (3 / 2 : ℝ)) y :=
      Real.contDiffAt_rpow_const_of_ne hypos.ne'
    have hpow1 : ContDiffAt ℝ 3
        (fun t : ℝ => t ^ (1 / 2 : ℝ)) y :=
      Real.contDiffAt_rpow_const_of_ne hypos.ne'
    exact ((((contDiffAt_const.mul contDiffAt_id).add
        (contDiffAt_const.mul (contDiffAt_id.pow 2))).add
          (contDiffAt_const.mul hpow3)).add
            (contDiffAt_const.mul hpow1)).contDiffWithinAt
  have hrem :=
    bourgain_quadraticTaylorWithin_remainder_of_sub_le
      (show a ^ 2 ≤ a ^ 2 + δ by linarith)
      hcont (hsample n) hC0 hC
      (show
        (a ^ 2 + (bourgainIndex n : ℝ) / D) - a ^ 2 ≤ δ by
          linarith [(hsample n).2])
  rw [taylorWithinEval_bourgainSquareRootCurvePhase_two ha hδ x] at hrem
  rw [← Real.norm_eq_abs, ← mul_sub, norm_mul]
  have hpi : ‖2 * Real.pi‖ = 2 * Real.pi := by
    rw [Real.norm_eq_abs, abs_of_pos]
    positivity
  rw [hpi]
  exact mul_le_mul_of_nonneg_left hrem (by positivity)

/-- Unconditional specialization with the third-derivative constant
discharged explicitly from the square-root curve. -/
theorem norm_bourgainSquareRootExactLocalSum_le_quadratic_explicit
    (H : ℕ) {D a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (c : Fin H → ℂ) (x : BourgainPhaseSpace)
    (hsample :
      ∀ n : Fin H,
        a ^ 2 + (bourgainIndex n : ℝ) / D ∈
          Set.Icc (a ^ 2) (a ^ 2 + δ)) :
    ‖bourgainSquareRootExactLocalSum H D a c x‖ ≤
      ‖bourgainSquareRootQuadraticLocalSum H D a c x‖ +
        (2 * Real.pi *
          ((‖x‖ * bourgainSquareRootThirdDerivativeBound a) *
            δ ^ (3 : ℕ) / 2)) *
          ∑ n : Fin H, ‖c n‖ := by
  apply norm_bourgainSquareRootExactLocalSum_le_quadratic
    H ha hδ (by
      unfold bourgainSquareRootThirdDerivativeBound
      positivity) c x hsample
  intro y hy
  exact
    norm_iteratedDerivWithin_bourgainSquareRootCurvePhase_three_le
      ha hδ hy x

end

end RHTower
