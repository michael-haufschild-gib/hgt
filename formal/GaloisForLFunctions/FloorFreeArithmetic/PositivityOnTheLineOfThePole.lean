import GaloisForLFunctions.FloorFreeArithmetic.PositivityAdmitsEveryFiniteDatum
import GaloisForLFunctions.RHTower.SimultaneousPhaseRecurrence

/-!
# Positivity on the line of the pole

A prime measure with a pole of weight `A` at `1` and a finite layer of zeros at the abscissa
`Θ ≤ 1`, with ordinates `γ_j` and multiplicities `m_j`, has the density
`A e^u − Σ_j 2 m_j e^{Θu} cos(γ_j u)` in `u = log x`. Write `M = Σ_j m_j`.

* `poleDensity_nonneg`: for `A ≥ 2M` the density is nonnegative on `[0, ∞)`, with no
  compensator.
* `laplace_poleDensity`: for `Θ < 1` its Laplace transform is the rational function
  `A/(s−1) − Σ_j m_j (1/(s−ρ_j) + 1/(s−ρ̄_j))`.
* `eventually_nonneg_poleDensity_one_iff`: on the line of the pole, `Θ = 1`, the density is
  nonnegative for all large `u` if and only if `2M ≤ A`. At a time where all the phases
  `γ_j u` return to `0` together the normalized density `A − Σ_j 2 m_j cos(γ_j u)` is close
  to `A − 2M`.
* `eventually_nonneg_poleDensity_simple_iff`: with a simple pole, `A = 1`, only the empty
  layer is admitted.

Below the line a compensator on a bounded interval restores positivity for every layer
(`exists_nonneg_density_with_layer`); on the line nothing does. Positivity excludes a finite
layer exactly where the pole and the layer have the same rate, and there it is the count
`2M ≤ A` of the classical proof.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

variable {ι : Type*} [Fintype ι]

/-- The density of a pole of weight `A` and a layer at the abscissa `Θ`. -/
def poleDensity (A Θ : ℝ) (γ : ι → ℝ) (m : ι → ℕ) (u : ℝ) : ℝ :=
  A * Real.exp u - ∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * u) * Real.cos (γ j * u))

/-- **A pole of weight at least `2M` needs no compensator.** -/
theorem poleDensity_nonneg {A Θ : ℝ} (hΘ : Θ ≤ 1) (γ : ι → ℝ) (m : ι → ℕ)
    (hA : 2 * ∑ j, (m j : ℝ) ≤ A) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ poleDensity A Θ γ m u := by
  have hE : 0 < Real.exp (Θ * u) := Real.exp_pos _
  have h1 : ∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * u) * Real.cos (γ j * u)) ≤
      ∑ j, 2 * (m j : ℝ) * Real.exp (Θ * u) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have h2 := mul_le_mul_of_nonneg_left (Real.cos_le_one (γ j * u)) hE.le
    rw [mul_one] at h2
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have h3 : ∑ j, 2 * (m j : ℝ) * Real.exp (Θ * u) =
      2 * (∑ j, (m j : ℝ)) * Real.exp (Θ * u) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hM0 : 0 ≤ 2 * ∑ j, (m j : ℝ) :=
    mul_nonneg zero_le_two (Finset.sum_nonneg fun j _ => Nat.cast_nonneg (m j))
  have h4 : 2 * (∑ j, (m j : ℝ)) * Real.exp (Θ * u) ≤ A * Real.exp u :=
    mul_le_mul hA (Real.exp_le_exp.mpr (by nlinarith only [hu, hΘ])) hE.le (hM0.trans hA)
  unfold poleDensity
  linarith only [h1, h3, h4]

/-- **The transform is rational**: for `Θ < 1` and `Re s > 1`,
`∫₀^∞ e^{−su} (A e^u − Σ 2 m_j e^{Θu} cos γ_j u) du = A/(s−1) − Σ m_j (1/(s−ρ_j) + 1/(s−ρ̄_j))`. -/
theorem laplace_poleDensity {Θ : ℝ} (hΘ : Θ < 1) (A : ℝ) (γ : ι → ℝ) (m : ι → ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => cexp (-(s * u)) * (poleDensity A Θ γ m u : ℂ)) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (poleDensity A Θ γ m u : ℂ) =
        A / (s - 1) -
          ∑ j, (m j : ℂ) * (1 / (s - ((Θ : ℂ) + γ j * I)) + 1 / (s - ((Θ : ℂ) - γ j * I))) := by
  obtain ⟨hint, hval⟩ := laplace_layerDensity hΘ le_rfl γ m hs
  have ha : ((1 : ℂ) - s).re < 0 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have ha0 : (1 : ℂ) - s ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at ha
    exact lt_irrefl _ ha
  have hs1 : s - 1 ≠ 0 := fun h => ha0 (by rw [← neg_sub, h, neg_zero])
  -- the density is `(A − 1) e^u` plus the uncompensated layer density
  have hsplit : ∀ u : ℝ, cexp (-(s * u)) * (poleDensity A Θ γ m u : ℂ) =
      ((A : ℂ) - 1) * cexp ((1 - s) * u) + cexp (-(s * u)) * (layerDensity Θ 0 γ m u : ℂ) := by
    intro u
    have hL : layerDensity Θ 0 γ m u =
        Real.exp u - ∑ j, 2 * (m j : ℝ) * (Real.exp (Θ * u) * Real.cos (γ j * u)) := by
      simp [layerDensity]
    have hP : poleDensity A Θ γ m u = (A - 1) * Real.exp u + layerDensity Θ 0 γ m u := by
      rw [hL, poleDensity]
      ring
    have h1 : cexp (-(s * u)) * cexp u = cexp ((1 - s) * u) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [hP]
    push_cast
    rw [← h1]
    ring
  have hint1 : IntegrableOn (fun u : ℝ => ((A : ℂ) - 1) * cexp ((1 - s) * u)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi ha 0).const_mul _
  refine ⟨(hint1.add hint).congr_fun (fun u _ => (hsplit u).symm) measurableSet_Ioi, ?_⟩
  have hcorr : layerCorrection Θ 0 s = 0 := by
    simp [layerCorrection]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hsplit u), integral_add hint1 hint,
    integral_const_mul, integral_exp_mul_complex_Ioi ha, hval, hcorr, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- **On the line of the pole a layer needs a pole of weight `2M`.** If the density at
`Θ = 1` is nonnegative for all large `u`, then `2M ≤ A`. -/
theorem two_mul_sum_le_of_eventually_nonneg {A : ℝ} {γ : ι → ℝ} {m : ι → ℕ}
    (h : ∀ᶠ u : ℝ in atTop, 0 ≤ poleDensity A 1 γ m u) : 2 * ∑ j, (m j : ℝ) ≤ A := by
  by_contra hcon
  have hlt : A < 2 * ∑ j, (m j : ℝ) := lt_of_not_ge hcon
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ j, (m j : ℝ) := ⟨_, rfl⟩
  rw [← hM] at hlt
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact Finset.sum_nonneg fun j _ => Nat.cast_nonneg (m j)
  -- a tolerance with `2M ε < 2M − A`
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (2 * M - A) / (2 * (2 * M + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    exact div_pos (by linarith only [hlt]) (by linarith only [hM0])
  have hMε : 2 * M * ε < 2 * M - A := by
    have h1 : ε * (2 * (2 * M + 1)) = 2 * M - A := by
      rw [hε]
      field_simp
    nlinarith only [h1, hlt, hM0, hε0]
  -- a late time at which all phases return
  obtain ⟨U, hU⟩ := eventually_atTop.mp h
  obtain ⟨u, hu, hrec⟩ := _root_.RHTower.exists_simultaneous_phase_recurrence γ hε0 U
  have hcos : ∀ j, 1 - ε ≤ Real.cos (γ j * u) := fun j => by
    have hre : (bohrChar (γ j) u - 1).re = Real.cos (γ j * u) - 1 := by
      rw [bohrChar, Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    have h1 := (Complex.abs_re_le_norm _).trans (hrec j)
    rw [hre] at h1
    linarith only [(abs_le.mp h1).1]
  have hD := hU u hu
  unfold poleDensity at hD
  rw [one_mul] at hD
  have hE : 0 < Real.exp u := Real.exp_pos u
  have hsum : 2 * M * (1 - ε) * Real.exp u ≤
      ∑ j, 2 * (m j : ℝ) * (Real.exp u * Real.cos (γ j * u)) := by
    have h1 : ∑ j, 2 * (m j : ℝ) * (Real.exp u * (1 - ε)) ≤
        ∑ j, 2 * (m j : ℝ) * (Real.exp u * Real.cos (γ j * u)) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcos j) hE.le) (by positivity)
    have h2 : ∑ j, 2 * (m j : ℝ) * (Real.exp u * (1 - ε)) = 2 * M * (1 - ε) * Real.exp u := by
      rw [hM, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith only [h1, h2]
  nlinarith only [hD, hsum, hMε, hE]

/-- **Positivity on the line of the pole is the count `2M ≤ A`.** -/
theorem eventually_nonneg_poleDensity_one_iff {A : ℝ} {γ : ι → ℝ} {m : ι → ℕ} :
    (∀ᶠ u : ℝ in atTop, 0 ≤ poleDensity A 1 γ m u) ↔ 2 * ∑ j, (m j : ℝ) ≤ A :=
  ⟨two_mul_sum_le_of_eventually_nonneg, fun hA =>
    (eventually_ge_atTop 0).mono fun _ hu => poleDensity_nonneg le_rfl γ m hA hu⟩

/-- **With a simple pole no layer lies on the line of the pole.** -/
theorem eventually_nonneg_poleDensity_simple_iff {γ : ι → ℝ} {m : ι → ℕ} :
    (∀ᶠ u : ℝ in atTop, 0 ≤ poleDensity 1 1 γ m u) ↔ ∀ j, m j = 0 := by
  rw [eventually_nonneg_poleDensity_one_iff]
  constructor
  · intro h j
    by_contra hj
    have h1 : (1 : ℝ) ≤ m j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    have h2 := Finset.single_le_sum (fun k _ => Nat.cast_nonneg (α := ℝ) (m k))
      (Finset.mem_univ j)
    linarith only [h, h1, h2]
  · intro h
    simp [h]

end GaloisForLFunctions.FloorFreeArithmetic
