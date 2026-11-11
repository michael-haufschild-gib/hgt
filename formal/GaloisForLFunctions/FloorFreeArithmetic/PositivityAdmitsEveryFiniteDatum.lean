import Mathlib

/-!
# Positivity admits every finite datum

Positivity of the prime weights says that the Chebyshev measure `dψ` is nonnegative. Its Laplace
transform in the variable `u = log x` is `−ζ'/ζ(s)`: a simple pole at `1` with residue `1` and a
pole with residue `−m` at every zero of multiplicity `m`.

For every abscissa `Θ < 1`, every finite family of ordinates `γ_j` and multiplicities `m_j`,
there is a nonnegative density `p` on `[0, ∞)` with

`∫₀^∞ e^{−su} p(u) du = 1/(s−1) − Σ_j m_j (1/(s−ρ_j) + 1/(s−ρ̄_j)) + E(s)`, `ρ_j = Θ + iγ_j`,

for `Re s > 1`, with `E` entire. The density is
`e^u − Σ_j 2 m_j e^{Θu} cos(γ_j u) + 2M e^u 1_{u ≤ u₀}`: beyond `u₀ = log(2M+2)/(1−Θ)` the main
term dominates the layer, and the compensator on `[0, u₀]` changes the transform by an entire
function.

So a positive prime measure with a simple pole can have any finite top layer below the line
`Re s = 1`: positivity constrains a top layer only on that line, where the main term and the
layer have the same rate.

* `layerDensity_nonneg`: the density is nonnegative on `[0, ∞)`.
* `laplace_layerDensity`: its Laplace transform.
* `exists_nonneg_density_with_layer`: the realization theorem.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

variable {ι : Type*} [Fintype ι]

/-- The length beyond which `e^u` dominates `2M e^{Θu}`. -/
def dominationLength (Θ M : ℝ) : ℝ := Real.log (2 * M + 2) / (1 - Θ)

theorem dominationLength_pos {Θ M : ℝ} (hΘ : Θ < 1) (hM : 0 ≤ M) : 0 < dominationLength Θ M :=
  div_pos (Real.log_pos (by linarith only [hM])) (by linarith only [hΘ])

/-- The density of a layer at the abscissa `Θ` with ordinates `γ_j` and multiplicities `m_j`,
compensated on `[0, u₀]` by `2M e^u`. -/
def layerDensity (Θ M : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (u : ℝ) : ℝ :=
  Real.exp u - ∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * u) * Real.cos (γ j * u)) +
    (Iic (dominationLength Θ M)).indicator (fun v => 2 * M * Real.exp v) u

/-- The transform of the compensator: an entire function. -/
def layerCorrection (Θ M : ℝ) (s : ℂ) : ℂ :=
  2 * M * dominationLength Θ M * dslope cexp 0 ((1 - s) * dominationLength Θ M)

theorem differentiable_layerCorrection (Θ M : ℝ) : Differentiable ℂ (layerCorrection Θ M) := by
  have hd : Differentiable ℂ (dslope cexp 0) := differentiableOn_univ.mp
    ((differentiableOn_dslope (isOpen_univ.mem_nhds (mem_univ (0 : ℂ)))).mpr
      differentiable_exp.differentiableOn)
  unfold layerCorrection
  exact (differentiable_const _).mul
    (hd.comp (((differentiable_const _).sub differentiable_id).mul_const _))

/-- The correction away from `s = 1`. -/
theorem layerCorrection_eq {Θ M : ℝ} (hΘ : Θ < 1) (hM : 0 ≤ M) {s : ℂ} (hs : 1 - s ≠ 0) :
    layerCorrection Θ M s =
      2 * M * ((cexp ((1 - s) * dominationLength Θ M) - 1) / (1 - s)) := by
  have hu : (dominationLength Θ M : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (dominationLength_pos hΘ hM).ne'
  have hz : (1 - s) * (dominationLength Θ M : ℂ) ≠ 0 := mul_ne_zero hs hu
  rw [layerCorrection, dslope_of_ne _ hz, slope_def_field, Complex.exp_zero, sub_zero]
  field_simp

/-- **The density is nonnegative** on `[0, ∞)`, when `M` bounds the total multiplicity. -/
theorem layerDensity_nonneg {Θ M : ℝ} (hΘ : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ)
    (hM : ∑ j, (m j : ℝ) ≤ M) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ layerDensity Θ M γ m u := by
  have hM0 : 0 ≤ M := (Finset.sum_nonneg fun j _ => Nat.cast_nonneg (m j)).trans hM
  have hE : 0 < Real.exp (Θ * u) := Real.exp_pos _
  -- the layer is at most `2M e^{Θu}`
  have hS : ∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * u) * Real.cos (γ j * u)) ≤
      2 * M * Real.exp (Θ * u) := by
    have h1 : ∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * u) * Real.cos (γ j * u)) ≤
        ∑ j, 2 * (m j : ℝ) * Real.exp (Θ * u) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have h2 := mul_le_mul_of_nonneg_left (Real.cos_le_one (γ j * u)) hE.le
      rw [mul_one] at h2
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h3 : ∑ j, 2 * (m j : ℝ) * Real.exp (Θ * u) =
        2 * (∑ j, (m j : ℝ)) * Real.exp (Θ * u) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    have h4 : 2 * (∑ j, (m j : ℝ)) * Real.exp (Θ * u) ≤ 2 * M * Real.exp (Θ * u) :=
      mul_le_mul_of_nonneg_right (by linarith only [hM]) hE.le
    linarith only [h1, h3, h4]
  unfold layerDensity
  by_cases hcase : u ≤ dominationLength Θ M
  · -- on `[0, u₀]` the compensator dominates the layer
    rw [Set.indicator_of_mem (mem_Iic.mpr hcase)]
    have h5 : Real.exp (Θ * u) ≤ Real.exp u :=
      Real.exp_le_exp.mpr (by nlinarith only [hu, hΘ])
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * M)
    linarith only [hS, h6, Real.exp_pos u]
  · -- beyond `u₀` the main term does
    rw [Set.indicator_of_notMem (fun h => hcase (mem_Iic.mp h)), add_zero]
    have h1Θ : 0 < 1 - Θ := by linarith only [hΘ]
    have h7 : Real.log (2 * M + 2) < u * (1 - Θ) := (div_lt_iff₀ h1Θ).mp (not_le.mp hcase)
    have h8 : 2 * M + 2 < Real.exp (u * (1 - Θ)) := by
      have h9 := Real.exp_lt_exp.mpr h7
      rwa [Real.exp_log (by linarith only [hM0])] at h9
    have h10 : Real.exp u = Real.exp (Θ * u) * Real.exp (u * (1 - Θ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h11 : 0 < Real.exp (Θ * u) * (Real.exp (u * (1 - Θ)) - 2 * M) :=
      mul_pos hE (by linarith only [h8])
    rw [h10]
    linarith only [hS, h11, mul_sub (Real.exp (Θ * u)) (Real.exp (u * (1 - Θ))) (2 * M),
      mul_comm (Real.exp (Θ * u)) (2 * M)]

/-- `2 e^{Θu} cos(γu)` as a sum of two complex exponentials. -/
theorem two_exp_cos (Θ γ u : ℝ) :
    ((2 * (Real.exp (Θ * u) * Real.cos (γ * u)) : ℝ) : ℂ) =
      cexp (((Θ : ℂ) + γ * I) * u) + cexp (((Θ : ℂ) - γ * I) * u) := by
  push_cast
  rw [Complex.cos, show ((Θ : ℂ) + γ * I) * u = Θ * u + γ * u * I by ring,
    show ((Θ : ℂ) - γ * I) * u = Θ * u + -(γ * u) * I by ring, Complex.exp_add, Complex.exp_add]
  ring

/-- **The Laplace transform of the density**, for `Re s > 1`. -/
theorem laplace_layerDensity {Θ M : ℝ} (hΘ : Θ < 1) (hM : 0 ≤ M) (γ : ι → ℝ) (m : ι → ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => cexp (-(s * u)) * (layerDensity Θ M γ m u : ℂ)) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (layerDensity Θ M γ m u : ℂ) =
        1 / (s - 1) -
          ∑ j, (m j : ℂ) * (1 / (s - ((Θ : ℂ) + γ j * I)) + 1 / (s - ((Θ : ℂ) - γ j * I))) +
          layerCorrection Θ M s := by
  have hu₀ := dominationLength_pos hΘ hM
  have ha : ((1 : ℂ) - s).re < 0 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have ha0 : (1 : ℂ) - s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at ha
    exact lt_irrefl _ ha
  have hρ : ∀ j, (((Θ : ℂ) + γ j * I) - s).re < 0 := fun j => by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith only [hs, hΘ]
  have hρ' : ∀ j, (((Θ : ℂ) - γ j * I) - s).re < 0 := fun j => by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero]
    linarith only [hs, hΘ]
  -- the integrand as a combination of exponentials
  have hpt : ∀ u : ℝ, cexp (-(s * u)) * (layerDensity Θ M γ m u : ℂ) =
      cexp ((1 - s) * u) -
        ∑ j, (m j : ℂ) * (cexp ((((Θ : ℂ) + γ j * I) - s) * u) +
          cexp ((((Θ : ℂ) - γ j * I) - s) * u)) +
        (Iic (dominationLength Θ M)).indicator (fun v : ℝ => 2 * (M : ℂ) * cexp ((1 - s) * v))
          u := by
    intro u
    have hsum : ((∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * u) * Real.cos (γ j * u)) : ℝ) : ℂ) =
        ∑ j, (m j : ℂ) * (cexp (((Θ : ℂ) + γ j * I) * u) + cexp (((Θ : ℂ) - γ j * I) * u)) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← two_exp_cos Θ (γ j) u]
      push_cast
      ring
    have hind : (((Iic (dominationLength Θ M)).indicator (fun v => 2 * M * Real.exp v) u : ℝ) :
        ℂ) = (Iic (dominationLength Θ M)).indicator (fun v : ℝ => 2 * (M : ℂ) * cexp v) u := by
      by_cases h : u ∈ Iic (dominationLength Θ M)
      · simp only [Set.indicator_of_mem h]
        push_cast
        ring
      · simp only [Set.indicator_of_notMem h, Complex.ofReal_zero]
    have h1 : cexp (-(s * u)) * cexp u = cexp ((1 - s) * u) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h2 : ∀ w : ℂ, cexp (-(s * u)) * cexp (w * u) = cexp ((w - s) * u) := fun w => by
      rw [← Complex.exp_add]
      congr 1
      ring
    have h3 : cexp (-(s * u)) *
        (Iic (dominationLength Θ M)).indicator (fun v : ℝ => 2 * (M : ℂ) * cexp v) u =
        (Iic (dominationLength Θ M)).indicator
          (fun v : ℝ => 2 * (M : ℂ) * cexp ((1 - s) * v)) u := by
      by_cases h : u ∈ Iic (dominationLength Θ M)
      · simp only [Set.indicator_of_mem h]
        rw [mul_left_comm, h1]
      · simp only [Set.indicator_of_notMem h, mul_zero]
    unfold layerDensity
    rw [Complex.ofReal_add, Complex.ofReal_sub, hsum, hind, Complex.ofReal_exp, mul_add,
      mul_sub, h1, h3, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, mul_add, h2, h2]
  -- the three pieces are integrable
  have hint1 : IntegrableOn (fun u : ℝ => cexp ((1 - s) * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi ha 0
  have hintj : ∀ j, IntegrableOn (fun u : ℝ => (m j : ℂ) *
      (cexp ((((Θ : ℂ) + γ j * I) - s) * u) + cexp ((((Θ : ℂ) - γ j * I) - s) * u)))
      (Ioi 0) := fun j =>
    ((integrableOn_exp_mul_complex_Ioi (hρ j) 0).add
      (integrableOn_exp_mul_complex_Ioi (hρ' j) 0)).const_mul _
  have hintS : IntegrableOn (fun u : ℝ => ∑ j, (m j : ℂ) *
      (cexp ((((Θ : ℂ) + γ j * I) - s) * u) + cexp ((((Θ : ℂ) - γ j * I) - s) * u)))
      (Ioi 0) := integrable_finsetSum _ fun j _ => hintj j
  have hint3 : IntegrableOn ((Iic (dominationLength Θ M)).indicator
      fun v : ℝ => 2 * (M : ℂ) * cexp ((1 - s) * v)) (Ioi 0) :=
    (hint1.const_mul (2 * (M : ℂ))).indicator measurableSet_Iic
  have hint12 : IntegrableOn (fun u : ℝ => cexp ((1 - s) * u) - ∑ j, (m j : ℂ) *
      (cexp ((((Θ : ℂ) + γ j * I) - s) * u) + cexp ((((Θ : ℂ) - γ j * I) - s) * u)))
      (Ioi 0) := hint1.sub hintS
  refine ⟨((hint12.add hint3).congr (Filter.Eventually.of_forall fun u => (hpt u).symm)), ?_⟩
  -- the three integrals
  have e1 : ∫ u in Ioi (0 : ℝ), cexp ((1 - s) * u) = 1 / (s - 1) := by
    rw [integral_exp_mul_complex_Ioi ha 0, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      neg_div, ← div_neg, neg_sub]
  have ej : ∀ j, ∫ u in Ioi (0 : ℝ), (m j : ℂ) *
      (cexp ((((Θ : ℂ) + γ j * I) - s) * u) + cexp ((((Θ : ℂ) - γ j * I) - s) * u)) =
      (m j : ℂ) * (1 / (s - ((Θ : ℂ) + γ j * I)) + 1 / (s - ((Θ : ℂ) - γ j * I))) := by
    intro j
    have hadd : ∫ u in Ioi (0 : ℝ), (cexp ((((Θ : ℂ) + γ j * I) - s) * u) +
        cexp ((((Θ : ℂ) - γ j * I) - s) * u)) =
        (∫ u in Ioi (0 : ℝ), cexp ((((Θ : ℂ) + γ j * I) - s) * u)) +
          ∫ u in Ioi (0 : ℝ), cexp ((((Θ : ℂ) - γ j * I) - s) * u) :=
      integral_add (integrableOn_exp_mul_complex_Ioi (hρ j) 0)
        (integrableOn_exp_mul_complex_Ioi (hρ' j) 0)
    rw [integral_const_mul, hadd, integral_exp_mul_complex_Ioi (hρ j) 0,
      integral_exp_mul_complex_Ioi (hρ' j) 0, Complex.ofReal_zero, mul_zero, mul_zero,
      Complex.exp_zero, neg_div, ← div_neg, neg_sub, neg_div, ← div_neg, neg_sub]
  have e3 : ∫ u in Ioi (0 : ℝ), (Iic (dominationLength Θ M)).indicator
      (fun v : ℝ => 2 * (M : ℂ) * cexp ((1 - s) * v)) u = layerCorrection Θ M s := by
    rw [layerCorrection_eq hΘ hM ha0, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
      ← intervalIntegral.integral_of_le hu₀.le, intervalIntegral.integral_const_mul,
      integral_exp_mul_complex ha0, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have eS : ∫ u in Ioi (0 : ℝ), ∑ j, (m j : ℂ) *
      (cexp ((((Θ : ℂ) + γ j * I) - s) * u) + cexp ((((Θ : ℂ) - γ j * I) - s) * u)) =
      ∑ j, (m j : ℂ) * (1 / (s - ((Θ : ℂ) + γ j * I)) + 1 / (s - ((Θ : ℂ) - γ j * I))) := by
    rw [integral_finsetSum _ fun j _ => hintj j]
    exact Finset.sum_congr rfl fun j _ => ej j
  have e12 : ∫ u in Ioi (0 : ℝ), (cexp ((1 - s) * u) - ∑ j, (m j : ℂ) *
      (cexp ((((Θ : ℂ) + γ j * I) - s) * u) + cexp ((((Θ : ℂ) - γ j * I) - s) * u))) =
      (∫ u in Ioi (0 : ℝ), cexp ((1 - s) * u)) - ∫ u in Ioi (0 : ℝ), ∑ j, (m j : ℂ) *
      (cexp ((((Θ : ℂ) + γ j * I) - s) * u) + cexp ((((Θ : ℂ) - γ j * I) - s) * u)) :=
    integral_sub hint1 hintS
  have eall : ∫ u in Ioi (0 : ℝ), (cexp ((1 - s) * u) - ∑ j, (m j : ℂ) *
      (cexp ((((Θ : ℂ) + γ j * I) - s) * u) + cexp ((((Θ : ℂ) - γ j * I) - s) * u)) +
      (Iic (dominationLength Θ M)).indicator (fun v : ℝ => 2 * (M : ℂ) * cexp ((1 - s) * v)) u) =
      (∫ u in Ioi (0 : ℝ), (cexp ((1 - s) * u) - ∑ j, (m j : ℂ) *
      (cexp ((((Θ : ℂ) + γ j * I) - s) * u) + cexp ((((Θ : ℂ) - γ j * I) - s) * u)))) +
      ∫ u in Ioi (0 : ℝ), (Iic (dominationLength Θ M)).indicator
        (fun v : ℝ => 2 * (M : ℂ) * cexp ((1 - s) * v)) u :=
    integral_add hint12 hint3
  rw [setIntegral_congr_fun measurableSet_Ioi fun u _ => hpt u, eall, e12, e1, eS, e3]

/-- **Positivity admits every finite datum.** For every `Θ < 1`, ordinates `γ_j` and
multiplicities `m_j` there are a density `p`, nonnegative on `[0, ∞)`, and an entire function
`E` such that the Laplace transform of `p` is
`1/(s−1) − Σ_j m_j (1/(s−ρ_j) + 1/(s−ρ̄_j)) + E(s)` for `Re s > 1`, with `ρ_j = Θ + iγ_j`. -/
theorem exists_nonneg_density_with_layer {Θ : ℝ} (hΘ : Θ < 1) (γ : ι → ℝ) (m : ι → ℕ) :
    ∃ (p : ℝ → ℝ) (E : ℂ → ℂ), (∀ u, 0 ≤ u → 0 ≤ p u) ∧ Differentiable ℂ E ∧
      ∀ s : ℂ, 1 < s.re →
        IntegrableOn (fun u : ℝ => cexp (-(s * u)) * (p u : ℂ)) (Ioi 0) ∧
        ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (p u : ℂ) =
          1 / (s - 1) -
            ∑ j, (m j : ℂ) * (1 / (s - ((Θ : ℂ) + γ j * I)) + 1 / (s - ((Θ : ℂ) - γ j * I))) +
            E s := by
  have hM0 : (0 : ℝ) ≤ ∑ j, (m j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg (m j)
  exact ⟨layerDensity Θ (∑ j, (m j : ℝ)) γ m, layerCorrection Θ (∑ j, (m j : ℝ)),
    fun u hu => layerDensity_nonneg hΘ γ m le_rfl hu, differentiable_layerCorrection Θ _,
    fun s hs => laplace_layerDensity hΘ hM0 γ m hs⟩

end GaloisForLFunctions.FloorFreeArithmetic
