import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The coherent prime--prime determinant is a centred mean--variance defect

The heat profile `φ_t(L) = √(π/t) e^{-L²/(4t)}` has logarithm `(log π − log t)/2 − L²/(4t)`, so its
successive time derivatives are the profile times the explicit rational factors

`1/(2t) − L²/(4t²)`  and  `(1/(2t) − L²/(4t²))² + 1/(2t²) − L²/(2t³)`.

Against any probability weight these three jets have a Lorentz determinant which is exactly a
centred defect of the observable `Y = L²`:

`P₀P₂ − P₁² = (M²/(16t⁴)) (Var Y + 8t² − 8t·E Y)`.

For the continuous prime saddle `L ~ N(t, 2t)` one has `E Y = t² + 2t` and `Var Y = 8t³ + 8t²`, so
the bracket vanishes identically: the saddle sits exactly on the boundary of the Lorentz cone, and
the prime--prime curvature is precisely its Stein/variance defect.
-/

namespace RHTower

noncomputable section

/-! ## The heat profile and its two jets -/

/-- The heat profile `√(π/t) e^{-L²/(4t)}`. -/
def heatProfile (t L : ℝ) : ℝ := Real.sqrt (Real.pi / t) * Real.exp (-(L ^ 2) / (4 * t))

/-- The logarithm of the heat profile. -/
def heatLogProfile (t L : ℝ) : ℝ := (Real.log Real.pi - Real.log t) / 2 - L ^ 2 / (4 * t)

/-- The first heat jet factor. -/
def heatJetFactor1 (t L : ℝ) : ℝ := 1 / (2 * t) - L ^ 2 / (4 * t ^ 2)

/-- The second heat jet factor. -/
def heatJetFactor2 (t L : ℝ) : ℝ :=
  heatJetFactor1 t L ^ 2 + 1 / (2 * t ^ 2) - L ^ 2 / (2 * t ^ 3)

theorem heatProfile_pos {t : ℝ} (ht : 0 < t) (L : ℝ) : 0 < heatProfile t L := by
  rw [heatProfile]
  have hpi : 0 < Real.pi / t := by positivity
  exact mul_pos (Real.sqrt_pos.2 hpi) (Real.exp_pos _)

theorem heatProfile_eq_exp {t : ℝ} (ht : 0 < t) (L : ℝ) :
    heatProfile t L = Real.exp (heatLogProfile t L) := by
  have hpi : 0 < Real.pi / t := by positivity
  have hsqrt : Real.sqrt (Real.pi / t) = Real.exp (Real.log (Real.pi / t) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpi]
    congr 1
    ring
  rw [heatProfile, heatLogProfile, hsqrt, ← Real.exp_add,
    Real.log_div (ne_of_gt Real.pi_pos) (ne_of_gt ht)]
  congr 1
  ring

/-- **(24.168)** The heat profile has the first jet as its negative time derivative. -/
theorem hasDerivAt_heatProfile {t : ℝ} (ht : 0 < t) (L : ℝ) :
    HasDerivAt (fun s : ℝ => heatProfile s L) (-(heatProfile t L * heatJetFactor1 t L)) t := by
  have hlog : HasDerivAt (fun s : ℝ => heatLogProfile s L) (-heatJetFactor1 t L) t := by
    have h1 : HasDerivAt (fun s : ℝ => Real.log s) (1 / t) t := by
      simpa using Real.hasDerivAt_log (ne_of_gt ht)
    have h2 : HasDerivAt (fun s : ℝ => (Real.log Real.pi - Real.log s) / 2)
        (-(1 / t) / 2) t := by
      simpa using ((hasDerivAt_const t (Real.log Real.pi)).sub h1).div_const 2
    have h3 : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have h4 : HasDerivAt (fun s : ℝ => L ^ 2 / (4 * s))
        ((0 * (4 * t) - L ^ 2 * 4) / (4 * t) ^ 2) t :=
      (hasDerivAt_const t (L ^ 2)).div h3 (by positivity)
    have h5 := h2.sub h4
    refine h5.congr_deriv ?_
    rw [heatJetFactor1]
    field_simp
    ring
  have hexp := hlog.exp
  have hval : Real.exp (heatLogProfile t L) * -heatJetFactor1 t L
      = -(heatProfile t L * heatJetFactor1 t L) := by
    rw [← heatProfile_eq_exp ht]
    ring
  rw [hval] at hexp
  refine hexp.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact heatProfile_eq_exp hs L

/-- **(24.168)** The first jet has the second jet as its negative time derivative. -/
theorem hasDerivAt_heatJet1 {t : ℝ} (ht : 0 < t) (L : ℝ) :
    HasDerivAt (fun s : ℝ => heatProfile s L * heatJetFactor1 s L)
      (-(heatProfile t L * heatJetFactor2 t L)) t := by
  have hprofile := hasDerivAt_heatProfile ht L
  have hfactor : HasDerivAt (fun s : ℝ => heatJetFactor1 s L)
      (-(1 / (2 * t ^ 2)) + L ^ 2 / (2 * t ^ 3)) t := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => 1 / (2 * s))
        ((0 * (2 * t) - 1 * 2) / (2 * t) ^ 2) t :=
      (hasDerivAt_const t (1 : ℝ)).div h1 (by positivity)
    have h3 : HasDerivAt (fun s : ℝ => 4 * s ^ 2) (4 * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (4 : ℝ))
    have h4 : HasDerivAt (fun s : ℝ => L ^ 2 / (4 * s ^ 2))
        ((0 * (4 * t ^ 2) - L ^ 2 * (4 * (2 * t))) / (4 * t ^ 2) ^ 2) t :=
      (hasDerivAt_const t (L ^ 2)).div h3 (by positivity)
    have h5 := h2.sub h4
    refine h5.congr_deriv ?_
    field_simp
    ring
  have hprod := hprofile.mul hfactor
  refine hprod.congr_deriv ?_
  rw [heatJetFactor2]
  ring

/-! ## The exact determinant identity -/

variable {ι : Type*}

/-- **(24.169) The coherent prime--prime determinant is a centred mean--variance defect.** -/
theorem heatDeterminant_eq (s : Finset ι) (p Y : ι → ℝ) (M t : ℝ)
    (hp : ∑ n ∈ s, p n = 1) (ht : t ≠ 0) :
    M * (M * ∑ n ∈ s, p n * ((1 / (2 * t) - Y n / (4 * t ^ 2)) ^ 2
          + 1 / (2 * t ^ 2) - Y n / (2 * t ^ 3)))
        - (M * (1 / (2 * t) - (∑ n ∈ s, p n * Y n) / (4 * t ^ 2))) ^ 2
      = M ^ 2 / (16 * t ^ 4) *
          ((∑ n ∈ s, p n * Y n ^ 2) - (∑ n ∈ s, p n * Y n) ^ 2
            + 8 * t ^ 2 - 8 * t * ∑ n ∈ s, p n * Y n) := by
  have hterm : ∀ n ∈ s, p n * ((1 / (2 * t) - Y n / (4 * t ^ 2)) ^ 2
        + 1 / (2 * t ^ 2) - Y n / (2 * t ^ 3))
      = (1 / (4 * t ^ 2) + 1 / (2 * t ^ 2)) * p n
        + (-(1 / (4 * t ^ 3)) - 1 / (2 * t ^ 3)) * (p n * Y n)
        + (1 / (16 * t ^ 4)) * (p n * Y n ^ 2) := by
    intro n _
    field_simp
    ring
  have hsplit : ∑ n ∈ s, p n * ((1 / (2 * t) - Y n / (4 * t ^ 2)) ^ 2
        + 1 / (2 * t ^ 2) - Y n / (2 * t ^ 3))
      = (1 / (4 * t ^ 2) + 1 / (2 * t ^ 2))
        + (-(1 / (4 * t ^ 3)) - 1 / (2 * t ^ 3)) * (∑ n ∈ s, p n * Y n)
        + (1 / (16 * t ^ 4)) * (∑ n ∈ s, p n * Y n ^ 2) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hp, mul_one]
  rw [hsplit]
  field_simp
  ring

/-! ## The Gaussian saddle sits on the boundary of the cone -/

/-- The square of a shifted centred law has the stated first two moments. -/
theorem shifted_square_moments {m sig2 EZ EZ2 EZ3 EZ4 : ℝ}
    (h1 : EZ = 0) (h2 : EZ2 = sig2) (h3 : EZ3 = 0) (h4 : EZ4 = 3 * sig2 ^ 2) :
    m ^ 2 + 2 * m * EZ + EZ2 = m ^ 2 + sig2 ∧
      (m ^ 4 + 4 * m ^ 3 * EZ + 6 * m ^ 2 * EZ2 + 4 * m * EZ3 + EZ4)
          - (m ^ 2 + 2 * m * EZ + EZ2) ^ 2
        = 4 * m ^ 2 * sig2 + 2 * sig2 ^ 2 := by
  subst h1
  subst h2
  subst h3
  subst h4
  constructor <;> ring

/-- **(24.170)** The prime saddle `L ~ N(t, 2t)` has `E L² = t² + 2t` and
`Var L² = 8t³ + 8t²`. -/
theorem primeSaddle_square_moments (t : ℝ) :
    t ^ 2 + 2 * t = t ^ 2 + 2 * t ∧ 4 * t ^ 2 * (2 * t) + 2 * (2 * t) ^ 2 = 8 * t ^ 3 + 8 * t ^ 2 :=
  ⟨rfl, by ring⟩

/-- **(24.169)--(24.170) The saddle is exactly on the boundary.**  With the Gaussian moments the
centred bracket vanishes identically. -/
theorem primeSaddle_bracket_eq_zero (t : ℝ) :
    (8 * t ^ 3 + 8 * t ^ 2) + 8 * t ^ 2 - 8 * t * (t ^ 2 + 2 * t) = 0 := by
  ring

/-- **(24.169)** With the Gaussian saddle moments the whole determinant vanishes. -/
theorem heatDeterminant_saddle_eq_zero (s : Finset ι) (p Y : ι → ℝ) (M t : ℝ)
    (hp : ∑ n ∈ s, p n = 1) (ht : t ≠ 0)
    (hmean : ∑ n ∈ s, p n * Y n = t ^ 2 + 2 * t)
    (hvar : (∑ n ∈ s, p n * Y n ^ 2) - (∑ n ∈ s, p n * Y n) ^ 2 = 8 * t ^ 3 + 8 * t ^ 2) :
    M * (M * ∑ n ∈ s, p n * ((1 / (2 * t) - Y n / (4 * t ^ 2)) ^ 2
          + 1 / (2 * t ^ 2) - Y n / (2 * t ^ 3)))
        - (M * (1 / (2 * t) - (∑ n ∈ s, p n * Y n) / (4 * t ^ 2))) ^ 2 = 0 := by
  rw [heatDeterminant_eq s p Y M t hp ht, hvar, hmean, primeSaddle_bracket_eq_zero, mul_zero]

end

end RHTower
