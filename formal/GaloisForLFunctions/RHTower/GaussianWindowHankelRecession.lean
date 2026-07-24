import GaloisForLFunctions.RHTower.GaussianWindowMomentRescaling
import GaloisForLFunctions.RHTower.GaussianWindowHankelPositiveDefinite
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Gaussian moment-defect recession

Strong Gaussian cooling makes every fixed finite Hankel section strictly positive definite, even for a
sign-changing density, provided the density is positive at the cooling centre.  For a bounded
continuous `J` with `J 0 > 0` and any section size `n`, the Gaussian-windowed Hankel matrix
`H_(J,tau,n)` is positive definite for all sufficiently large `tau`
(`gaussianWindow_momentHankelMatrix_posDef_eventually`).  Hence the least defect degree recedes to
infinity: every finite family of sections is eventually positive definite
(`gaussianWindow_momentHankelMatrix_posDef_eventually_forall_le`).

The mechanism is the exact diagonal-congruence factorisation
`v ⬝ᵥ H_(J,tau) *ᵥ v = (sqrt tau)⁻¹ * (w ⬝ᵥ K_tau *ᵥ w)` with `w_i = v_i (sqrt tau)⁻¹^i`, where the
cooled Hankel matrix `K_tau` has entries `∫ y^(i+j) exp(-y^2) J(y / sqrt tau) dy`.  As `tau -> ∞` those
entries converge to `J 0` times the standard Gaussian moments, whose Hankel matrix is positive
definite; positive-definiteness is open under entrywise convergence, so `K_tau` — and therefore
`H_(J,tau)` — is eventually positive definite.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal

namespace RHTower

/-- The cooled moment sequence: the `m`-th moment of the standard Gaussian weight against the density
`J` rescaled by `1 / sqrt tau`. -/
noncomputable def cooledMoment (J : ℝ → ℝ) (tau : ℝ) (m : ℕ) : ℝ :=
  ∫ y, y ^ m * Real.exp (-y ^ 2) * J ((Real.sqrt tau)⁻¹ * y)

/-- The Gaussian-windowed moment as the cooled moment scaled by `(sqrt tau)⁻¹^(m+1)`. -/
theorem weightedMoment_eq_cooled {tau : ℝ} (htau : 0 < tau) (J : ℝ → ℝ) (m : ℕ) :
    weightedMoment (gaussianWindowMeasure tau) J m
      = (Real.sqrt tau)⁻¹ ^ (m + 1) * cooledMoment J tau m :=
  weightedMoment_gaussianWindow_rescale htau J m

/-- The standard Gaussian moment `∫ y^m exp(-y^2) dy` is the unit-window weighted moment of the
constant density `1`. -/
theorem gaussianStdMoment_eq (m : ℕ) :
    (∫ y, y ^ m * Real.exp (-y ^ 2)) = weightedMoment (gaussianWindowMeasure 1) (fun _ => 1) m := by
  rw [weightedMoment, gaussianWindowMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_one]
  apply integral_congr_ae; filter_upwards with y
  rw [neg_one_mul]; ring

/-- The coefficient-vector quadratic form of a finite Hankel matrix is the double moment sum. -/
theorem quadForm_momentHankelMatrix (s : ℕ → ℝ) (n : ℕ) (v : Fin n → ℝ) :
    v ⬝ᵥ (HTGeometry.momentHankelMatrix s n) *ᵥ v
      = ∑ i : Fin n, ∑ j : Fin n, v i * s ((i : ℕ) + (j : ℕ)) * v j := by
  rw [dotProduct]
  apply Finset.sum_congr rfl; intro i _
  have hmv : (HTGeometry.momentHankelMatrix s n *ᵥ v) i
      = ∑ j : Fin n, s ((i : ℕ) + (j : ℕ)) * v j := by
    simp [Matrix.mulVec, dotProduct, HTGeometry.momentHankelMatrix]
  rw [hmv, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; ring

/-- **Gaussian moment-defect recession `(D)`.**  For a bounded continuous density `J` with `J 0 > 0`,
every finite Gaussian-windowed Hankel section is positive definite for all sufficiently large `tau` —
even when `J` is negative away from the origin.  The proof factors the section's quadratic form through
the cooled Hankel matrix and applies openness of positive-definiteness under entrywise convergence to
the positive-definite standard Gaussian Hankel matrix. -/
theorem gaussianWindow_momentHankelMatrix_posDef_eventually
    {J : ℝ → ℝ} (hJc : Continuous J) {C : ℝ} (hJb : ∀ x, |J x| ≤ C) (hJ0 : 0 < J 0) (n : ℕ) :
    ∀ᶠ tau in Filter.atTop,
      (HTGeometry.momentHankelMatrix (weightedMoment (gaussianWindowMeasure tau) J) n).PosDef := by
  set G : ℕ → ℝ := fun m => ∫ y, y ^ m * Real.exp (-y ^ 2) with hG
  have hGpd : (HTGeometry.momentHankelMatrix G n).PosDef := by
    have heq : G = weightedMoment (gaussianWindowMeasure 1) (fun _ => 1) := by
      funext m; exact gaussianStdMoment_eq m
    rw [heq]
    exact gaussianWindow_momentHankelMatrix_posDef_of_nonneg one_pos continuous_const
      (fun _ => zero_le_one) (memLp_top_const 1) (x₀ := 0) one_pos n
  have hM₀pd : ((J 0) • HTGeometry.momentHankelMatrix G n).PosDef := hGpd.smul hJ0
  have hcooled : ∀ᶠ tau in Filter.atTop,
      (HTGeometry.momentHankelMatrix (cooledMoment J tau) n).PosDef := by
    refine posDef_eventually_of_tendsto hM₀pd
      (Filter.Eventually.of_forall fun tau => HTGeometry.momentHankelMatrix_isHermitian _ _) ?_
    intro p q
    simp only [HTGeometry.momentHankelMatrix, Matrix.smul_apply, smul_eq_mul, hG]
    rw [mul_comm]
    exact tendsto_gaussianCooledMoment J hJc hJb (p + q)
  filter_upwards [hcooled, eventually_gt_atTop (0 : ℝ)] with tau hKpd hτ0
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨HTGeometry.momentHankelMatrix_isHermitian _ _, fun v hv => ?_⟩
  rw [star_trivial]
  set w : Fin n → ℝ := fun i => v i * (Real.sqrt tau)⁻¹ ^ (i : ℕ) with hw
  have hsqrtpos : 0 < Real.sqrt tau := Real.sqrt_pos.mpr hτ0
  have hwne : w ≠ 0 := by
    intro h; apply hv; funext i
    have hi := congrFun h i
    simp only [hw, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ (inv_ne_zero hsqrtpos.ne'))
  have hquad : v ⬝ᵥ
        (HTGeometry.momentHankelMatrix (weightedMoment (gaussianWindowMeasure tau) J) n) *ᵥ v
      = (Real.sqrt tau)⁻¹ *
        (w ⬝ᵥ (HTGeometry.momentHankelMatrix (cooledMoment J tau) n) *ᵥ w) := by
    rw [quadForm_momentHankelMatrix, quadForm_momentHankelMatrix, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [weightedMoment_eq_cooled hτ0]
    simp only [hw]
    rw [pow_succ, pow_add]
    ring
  rw [hquad]
  have hpos : 0 < w ⬝ᵥ (HTGeometry.momentHankelMatrix (cooledMoment J tau) n) *ᵥ w := by
    have := hKpd.re_dotProduct_pos hwne
    simpa [Matrix.star_eq_conjTranspose, star_trivial] using this
  exact mul_pos (inv_pos.mpr hsqrtpos) hpos

/-- **Least-defect-degree recession `(E)`.**  Every finite family of Gaussian-windowed Hankel sections
of a bounded continuous density with `J 0 > 0` is eventually simultaneously positive definite: for each
`d`, all sections of size at most `d+1` are positive definite for large `tau`.  Hence the least degree
at which positivity can fail exceeds any prescribed `d` cofinally. -/
theorem gaussianWindow_momentHankelMatrix_posDef_eventually_forall_le
    {J : ℝ → ℝ} (hJc : Continuous J) {C : ℝ} (hJb : ∀ x, |J x| ≤ C) (hJ0 : 0 < J 0) (d : ℕ) :
    ∀ᶠ tau in Filter.atTop, ∀ k ≤ d,
      (HTGeometry.momentHankelMatrix (weightedMoment (gaussianWindowMeasure tau) J) (k + 1)).PosDef := by
  have hstep : ∀ k ∈ Finset.Iic d, ∀ᶠ tau in Filter.atTop,
      (HTGeometry.momentHankelMatrix (weightedMoment (gaussianWindowMeasure tau) J) (k + 1)).PosDef :=
    fun k _ => gaussianWindow_momentHankelMatrix_posDef_eventually hJc hJb hJ0 (k + 1)
  filter_upwards [(eventually_all_finset (Finset.Iic d)).mpr hstep] with tau htau
  intro k hk
  exact htau k (Finset.mem_Iic.mpr hk)

end RHTower
