import GaloisForLFunctions.HTGeometry.LatticeMinkowskiBound
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Uniform short vectors under determinant-one deformations

Minkowski's theorem gives one radius, depending only on a fixed full lattice, that contains a
nonzero point after every determinant-one linear deformation.  The quantifier order is essential:
the radius is chosen before the deformation.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Module MeasureTheory Metric
open scoped Classical ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive coordinatewise scaling as a real linear equivalence. -/
def positiveDiagonalLinearEquiv (s : ι → ℝ) (hs : ∀ i, 0 < s i) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) := by
  have hdet : IsUnit (Matrix.diagonal s).det := by
    rw [Matrix.det_diagonal]
    apply isUnit_iff_ne_zero.mpr
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (hs i)
  exact Matrix.toLinearEquiv' (Matrix.diagonal s)
    ((Matrix.isUnit_iff_isUnit_det _).2 hdet).invertible

@[simp]
theorem positiveDiagonalLinearEquiv_apply (s : ι → ℝ) (hs : ∀ i, 0 < s i)
    (x : ι → ℝ) :
    positiveDiagonalLinearEquiv s hs x = fun i => s i * x i := by
  change Matrix.toLin' (Matrix.diagonal s) x = _
  rw [Matrix.toLin'_apply]
  ext i
  change (∑ j, Matrix.diagonal s i j * x j) = s i * x i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Matrix.diagonal, Ne.symm hji]
  · simp

theorem det_positiveDiagonalLinearEquiv (s : ι → ℝ) (hs : ∀ i, 0 < s i) :
    LinearMap.det (positiveDiagonalLinearEquiv s hs : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
      ∏ i, s i := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ ι)]
  have hmat :
      LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
          (positiveDiagonalLinearEquiv s hs : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
        Matrix.diagonal s := by
    ext i j
    change ∑ k, Matrix.diagonal s i k *
      (Pi.single j (1 : ℝ) : ι → ℝ) k = Matrix.diagonal s i j
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Pi.single, hkj]
    · simp
  rw [hmat, Matrix.det_diagonal]

/-- One radius works for every determinant-one deformation of a fixed full lattice. -/
theorem exists_uniform_ne_zero_zspan_linearEquiv_norm_le [Nonempty ι]
    (b : Basis ι ℝ (ι → ℝ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ T : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ),
      LinearMap.det (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) = 1 →
        ∃ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 ∧ ‖T x‖ ≤ R := by
  let c : ENNReal := volume (ZSpan.fundamentalDomain b)
  let R : ℝ := c.toReal + 1
  have hc_top : c < ∞ := (ZSpan.fundamentalDomain_isBounded b).measure_lt_top
  have hc_eq : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hc_top.ne
  have hR : 0 < R := by
    dsimp [R]
    exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
  have hunitBall : volume (Metric.ball (0 : ι → ℝ) 1) =
      (2 : ENNReal) ^ (Fintype.card ι : ℝ) := by
    have hset : Metric.ball (0 : ι → ℝ) 1 =
        Set.pi Set.univ (fun _ : ι => Set.Ioo (-1 : ℝ) 1) := by
      ext x
      simp [Metric.mem_ball, pi_norm_lt_iff, abs_lt]
    rw [hset, MeasureTheory.volume_pi_pi]
    simp [Real.volume_Ioo]
    norm_num
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hRone : 1 ≤ R := by
    dsimp [R]
    exact le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hreal : c.toReal < R ^ Fintype.card ι := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hcard)
    rw [hn, pow_succ]
    calc
      c.toReal < R := by dsimp [R]; linarith
      _ = 1 * R := by rw [one_mul]
      _ ≤ R ^ n * R :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hRone) (le_trans zero_le_one hRone)
  refine ⟨R, hR, ?_⟩
  intro T hdetT
  let bT : Basis ι ℝ (ι → ℝ) := b.map T
  let F : Set (ι → ℝ) := ZSpan.fundamentalDomain bT
  let L : Submodule ℤ (ι → ℝ) := Submodule.span ℤ (Set.range bT)
  have hbdet : b.det (bT : ι → (ι → ℝ)) = 1 := by
    rw [Basis.det_apply]
    have hmat : b.toMatrix (bT : ι → (ι → ℝ)) =
        LinearMap.toMatrix b b (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) := by
      ext i j
      dsimp [bT]
      simp only [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
      rfl
    rw [hmat, LinearMap.det_toMatrix, hdetT]
  have hvolF : volume F = c := by
    dsimp [F, bT, c]
    rw [ZSpan.measure_fundamentalDomain (b.map T) volume b, hbdet,
      abs_one, ENNReal.ofReal_one, one_mul]
  have hvol : volume F * 2 ^ finrank ℝ (ι → ℝ) <
      volume (Metric.closedBall (0 : ι → ℝ) R) := by
    rw [hvolF, Measure.addHaar_closedBall volume (0 : ι → ℝ) hR.le, hunitBall]
    simp only [finrank_pi_fintype, finrank_self, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_univ, Nat.cast_id]
    rw [← hc_eq, ENNReal.rpow_natCast]
    have hfactor0 : (2 : ENNReal) ^ Fintype.card ι ≠ 0 := by positivity
    have hfactorTop : (2 : ENNReal) ^ Fintype.card ι ≠ ⊤ := by finiteness
    have hofReal : ENNReal.ofReal c.toReal < ENNReal.ofReal (R ^ Fintype.card ι) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hreal
    simpa only [mul_comm] using ENNReal.mul_lt_mul_right hfactor0 hfactorTop hofReal
  have hfund : IsAddFundamentalDomain L F volume :=
    ZSpan.isAddFundamentalDomain bT volume
  let f : (ι → ℤ) → (ι → ℝ) := fun n => ∑ i, n i • bT i
  have hL_subset : (L : Set (ι → ℝ)) ⊆ Set.range f := by
    intro y hy
    dsimp [L] at hy
    refine Submodule.span_induction (p := fun y _ => y ∈ Set.range f) ?_ ?_ ?_ ?_ hy
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      refine ⟨Pi.single i 1, ?_⟩
      dsimp [f]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single, hji]
      · simp
    · exact ⟨0, by simp [f]⟩
    · rintro x y _ _ ⟨nx, rfl⟩ ⟨ny, rfl⟩
      refine ⟨nx + ny, ?_⟩
      simp only [f, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · rintro a x _ ⟨n, rfl⟩
      refine ⟨fun i => a * n i, ?_⟩
      simp only [f, Finset.smul_sum, mul_smul]
  have hL_countable : (L : Set (ι → ℝ)).Countable :=
    Set.Countable.mono hL_subset (Set.countable_range f)
  letI : Encodable L.toAddSubgroup := hL_countable.toEncodable
  obtain ⟨y, hyL, hy0, hyR⟩ :=
    exists_ne_zero_norm_le_of_covolume (L := L.toAddSubgroup) hfund hvol
  have hyMap : y ∈ Submodule.map (T.restrictScalars ℤ : (ι → ℝ) →ₗ[ℤ] (ι → ℝ))
      (Submodule.span ℤ (Set.range b)) := by
    rw [ZSpan.map b T]
    exact hyL
  rcases hyMap with ⟨x, hx, hxy⟩
  refine ⟨x, hx, ?_, ?_⟩
  · intro hx0
    apply hy0
    rw [← hxy, hx0, map_zero]
  · calc
      ‖T x‖ = ‖y‖ := congrArg norm hxy
      _ ≤ R := hyR

/-- Uniform determinant-one reduction specialized to positive diagonal scaling. -/
theorem exists_uniform_ne_zero_zspan_positiveDiagonal_norm_le [Nonempty ι]
    (b : Basis ι ℝ (ι → ℝ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (s : ι → ℝ) (hs : ∀ i, 0 < s i), (∏ i, s i) = 1 →
      ∃ x ∈ Submodule.span ℤ (Set.range b),
        x ≠ 0 ∧ ‖positiveDiagonalLinearEquiv s hs x‖ ≤ R := by
  obtain ⟨R, hR, hRall⟩ := exists_uniform_ne_zero_zspan_linearEquiv_norm_le b
  refine ⟨R, hR, ?_⟩
  intro s hs hprod
  apply hRall (positiveDiagonalLinearEquiv s hs)
  rw [det_positiveDiagonalLinearEquiv, hprod]

end

end GaloisForLFunctions.HTGeometry
