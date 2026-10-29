import GaloisForLFunctions.HTGeometry.AffineLatticePoisson
import GaloisForLFunctions.HTGeometry.FinitePiProductSummability
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian theta inversion on full lattices

The inverse lattice map bounds integer coordinates by the Euclidean norm. This
reduces normal convergence to a product of scalar Gaussian series. Poisson
summation and the explicit Gaussian Fourier transform then give theta inversion
with the inverse absolute determinant and inverse-adjoint lattice. The proof
also covers dimension zero.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "X" => ι → ℝ
local notation "Z" => ι → ℤ

/-- The radial Gaussian with decay rate `a`, viewed as a complex-valued function. -/
def gaussianKernel (a : ℝ) (x : E) : ℂ := Complex.exp (-(a : ℂ) * ‖x‖ ^ 2)

theorem norm_gaussianKernel (a : ℝ) (x : E) :
    ‖gaussianKernel a x‖ = Real.exp (-a * ‖x‖ ^ 2) := by
  rw [gaussianKernel, show -(a : ℂ) * ‖x‖ ^ 2 =
    ((-a * ‖x‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.norm_exp, Complex.ofReal_re]

/-- Gaussian lattice translates admit one summable majorant on every bounded set. -/
theorem gaussian_summable_translates (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (R : ℝ) (_hR : 0 ≤ R) :
    ∃ u : Z → ℝ, Summable u ∧ ∀ x : X, ‖x‖ ≤ R → ∀ k : Z,
      ‖gaussianKernel a (B (WithLp.toLp 2 (x + integerPoint k)))‖ ≤ u k := by
  classical
  -- The inverse lattice map controls each integer coordinate.
  let M := max 1 ‖B.symm.toContinuousLinearMap‖
  have hM : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  -- The extra dimension in this bound also covers an empty coordinate set.
  let D : ℝ := 2 * (Fintype.card ι + 1 : ℝ) * M ^ 2
  have hD : 0 < D := by dsimp only [D]; positivity
  let c := a / D
  have hc : 0 < c := div_pos ha hD
  have hcD : c * D = a := div_mul_cancel₀ a hD.ne'
  have hs : Summable (fun k : Z => ∏ i, Real.exp (-c * (k i : ℝ) ^ 2)) := by
    have hz : Summable (fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2)) := by
      simpa only [pow_zero, one_mul] using
        GaloisForLFunctions.summable_one_add_natAbs_pow_mul_exp_neg_int_sq 0 hc
    have hsFin : Summable (fun k : Fin (Fintype.card ι) → ℤ =>
        ∏ i, Real.exp (-c * (k i : ℝ) ^ 2)) :=
      summable_prod_pi (fun _ k => Real.exp (-c * (k : ℝ) ^ 2))
        (fun _ _ => (Real.exp_pos _).le) (fun _ => hz)
    let e := Fintype.equivFin ι
    let e' : Z ≃ (Fin (Fintype.card ι) → ℤ) :=
      { toFun k j := k (e.symm j)
        invFun k i := k (e i)
        left_inv k := by funext i; simp
        right_inv k := by funext j; simp }
    refine (hsFin.comp_injective e'.injective).congr fun k => ?_
    change (∏ j : Fin (Fintype.card ι), Real.exp (-c * (k (e.symm j) : ℝ) ^ 2)) = _
    exact Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  refine ⟨fun k => Real.exp (a * R ^ 2) * ∏ i, Real.exp (-c * (k i : ℝ) ^ 2),
    hs.mul_left _, fun x hx k => ?_⟩
  let y := B (WithLp.toLp 2 (x + integerPoint k))
  have hinv : ‖B.symm y‖ ≤ M * ‖y‖ :=
    (B.symm.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg y))
  have hi (i : ι) : |(k i : ℝ)| ≤ M * ‖y‖ + R := by
    have he : |(k i : ℝ)| = ‖(B.symm y) i - x i‖ := by
      simp [y, integerPoint]
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add
      ((PiLp.norm_apply_le (B.symm y) i).trans hinv)
      ((norm_le_pi_norm x i).trans hx))
  have hM2 : 1 ≤ M ^ 2 := by nlinarith only [hM]
  have hcoord (i : ι) : (k i : ℝ) ^ 2 ≤ 2 * M ^ 2 * (‖y‖ ^ 2 + R ^ 2) := by
    have hsq := pow_le_pow_left₀ (abs_nonneg (k i : ℝ)) (hi i) 2
    rw [sq_abs] at hsq
    have hMR := mul_le_mul_of_nonneg_right hM2 (sq_nonneg R)
    nlinarith only [hsq, sq_nonneg (M * ‖y‖ - R), hMR]
  have hsum : (∑ i, (k i : ℝ) ^ 2) ≤ D * (‖y‖ ^ 2 + R ^ 2) := by
    calc
      _ ≤ ∑ _ : ι, 2 * M ^ 2 * (‖y‖ ^ 2 + R ^ 2) :=
        Finset.sum_le_sum (fun i _ => hcoord i)
      _ = (Fintype.card ι : ℝ) * (2 * M ^ 2 * (‖y‖ ^ 2 + R ^ 2)) := by simp
      _ ≤ (Fintype.card ι + 1 : ℝ) * (2 * M ^ 2 * (‖y‖ ^ 2 + R ^ 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by dsimp only [D]; ring
  have hscale := mul_le_mul_of_nonneg_left hsum hc.le
  rw [← mul_assoc, hcD] at hscale
  rw [norm_gaussianKernel]
  change Real.exp (-a * ‖y‖ ^ 2) ≤
    Real.exp (a * R ^ 2) * ∏ i, Real.exp (-c * (k i : ℝ) ^ 2)
  rw [← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [← Finset.mul_sum]
  change -a * ‖y‖ ^ 2 ≤ a * R ^ 2 + -c * ∑ i, (k i : ℝ) ^ 2
  nlinarith only [hscale]

/-- Gaussian samples on every full lattice are absolutely summable. -/
theorem summable_norm_gaussian_lattice (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a) :
    Summable (fun k : Z => ‖gaussianKernel a (B (euclideanIntegerPoint k))‖) := by
  obtain ⟨u, hu, hb⟩ := gaussian_summable_translates B ha 0 le_rfl
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hu
  intro k
  simpa only [zero_add, euclideanIntegerPoint] using hb 0 (by simp) k


theorem continuous_gaussianKernel (a : ℝ) : Continuous (gaussianKernel (ι := ι) a) := by
  unfold gaussianKernel
  fun_prop

theorem integrable_gaussianKernel {a : ℝ} (ha : 0 < a) :
    Integrable (gaussianKernel (ι := ι) a) := by
  change Integrable (fun x : E => Complex.exp (-(a : ℂ) * ‖x‖ ^ 2))
  simpa only [zero_mul, add_zero] using
    (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (a : ℂ)) ha 0 (0 : E))

/-- The scalar factor in the Fourier transform of a radial Gaussian. -/
def gaussianFactor (a : ℝ) : ℝ :=
  (Real.pi / a) ^ ((Module.finrank ℝ E : ℝ) / 2)

/-- Fourier transformation inverts the decay rate and rescales by dimension. -/
theorem fourier_gaussianKernel {a : ℝ} (ha : 0 < a) (w : E) :
    (𝓕 (gaussianKernel (ι := ι) a)) w =
      gaussianFactor (ι := ι) a • gaussianKernel (Real.pi ^ 2 / a) w := by
  change (𝓕 (fun v : E => Complex.exp (-(a : ℂ) * ‖v‖ ^ 2))) w = _
  rw [fourier_gaussian_innerProductSpace (b := (a : ℂ)) ha]
  have hf : ((Real.pi : ℂ) / a) ^ ((Module.finrank ℝ E : ℂ) / 2) =
      (gaussianFactor (ι := ι) a : ℂ) := by
    unfold gaussianFactor
    rw [Complex.ofReal_cpow (div_nonneg Real.pi_pos.le ha.le)]
    simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  rw [hf, Complex.real_smul, gaussianKernel]
  congr 2
  push_cast
  ring

/-- Gaussian Poisson summation with the inverse-adjoint lattice map. -/
theorem gaussian_lattice_poisson (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a) :
    (∑' k : Z, gaussianKernel a (B (euclideanIntegerPoint k))) =
      latticeScale B • gaussianFactor (ι := ι) a •
        ∑' k : Z, gaussianKernel (Real.pi ^ 2 / a)
          (inverseAdjointEquiv B (euclideanIntegerPoint k)) := by
  have ha' : 0 < Real.pi ^ 2 / a := div_pos (sq_pos_of_pos Real.pi_pos) ha
  have hd := (summable_norm_gaussian_lattice (inverseAdjointEquiv B) ha').of_norm
  have hs : Summable (fun k : Z =>
      (𝓕 (fun x => gaussianKernel a (B x))) (euclideanIntegerPoint k)) := by
    refine ((hd.mul_left (gaussianFactor (ι := ι) a : ℂ)).mul_left
      (latticeScale B : ℂ)).congr fun k => ?_
    rw [fourier_comp_linearEquiv, fourier_gaussianKernel ha]
    rfl
  have hp := euclidean_poisson_of_summable_translates
    ((continuous_gaussianKernel a).comp B.continuous)
    (integrable_comp_linearEquiv (integrable_gaussianKernel ha) B)
    (gaussian_summable_translates B ha) hs
  simp only [Function.comp_def] at hp
  rw [hp]
  simp only [fourier_comp_linearEquiv, fourier_gaussianKernel ha,
    inverseAdjointEquiv_apply, Complex.real_smul, tsum_mul_left]


theorem gaussianKernel_eq_ofReal (a : ℝ) (x : E) :
    gaussianKernel a x = (Real.exp (-a * ‖x‖ ^ 2) : ℂ) := by
  rw [gaussianKernel, Complex.ofReal_exp]
  congr 1
  push_cast
  rfl

/-- The real Gaussian sum with decay rate `a`. -/
def gaussianLatticeSum (B : E ≃L[ℝ] E) (a : ℝ) : ℝ :=
  ∑' k : Z, Real.exp (-a * ‖B (euclideanIntegerPoint k)‖ ^ 2)

theorem summable_gaussianLatticeSum (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a) :
    Summable (fun k : Z => Real.exp (-a * ‖B (euclideanIntegerPoint k)‖ ^ 2)) := by
  simpa only [norm_gaussianKernel] using summable_norm_gaussian_lattice B ha

theorem ofReal_gaussianLatticeSum (B : E ≃L[ℝ] E) (a : ℝ) :
    (gaussianLatticeSum B a : ℂ) =
      ∑' k : Z, gaussianKernel a (B (euclideanIntegerPoint k)) := by
  simp only [gaussianLatticeSum, Complex.ofReal_tsum, gaussianKernel_eq_ofReal]

/-- The Gaussian Poisson identity over the real numbers. -/
theorem gaussianLatticeSum_poisson (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a) :
    gaussianLatticeSum B a = latticeScale B * gaussianFactor (ι := ι) a *
      gaussianLatticeSum (inverseAdjointEquiv B) (Real.pi ^ 2 / a) := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, ofReal_gaussianLatticeSum, Complex.real_smul, mul_assoc]
    using gaussian_lattice_poisson B ha

/-- The conventional theta parameter places a factor of `π` in the Gaussian. -/
def latticeTheta (B : E ≃L[ℝ] E) (t : ℝ) : ℝ := gaussianLatticeSum B (Real.pi * t)

omit [Fintype ι] in
theorem gaussianFactor_pi_mul {t : ℝ} (ht : 0 < t) :
    gaussianFactor (ι := ι) (Real.pi * t) =
      t ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
  unfold gaussianFactor
  have he : Real.pi / (Real.pi * t) = t⁻¹ := by
    field_simp
  rw [he, Real.inv_rpow ht.le, Real.rpow_neg ht.le]

/-- Theta inversion for every full Euclidean lattice, including dimension zero. -/
theorem latticeTheta_inversion (B : E ≃L[ℝ] E) {t : ℝ} (ht : 0 < t) :
    latticeTheta B t = latticeScale B * t ^ (-((Module.finrank ℝ E : ℝ) / 2)) *
      latticeTheta (inverseAdjointEquiv B) (1 / t) := by
  have he : Real.pi ^ 2 / (Real.pi * t) = Real.pi * (1 / t) := by
    field_simp
  simpa only [latticeTheta, gaussianFactor_pi_mul ht, he] using
    gaussianLatticeSum_poisson B (mul_pos Real.pi_pos ht)


end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
