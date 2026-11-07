import GaloisForLFunctions.BlackHoleRingdown.TheCuspFormsExist
import GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum

/-!
# The cusp spectrum of the modular horizon is discrete

A nonnegative unit point-pair kernel of radius `R` with `R · 512(Λ + 1) ≤ 1` has Selberg transform
within `½` of `1` at every spectral parameter with `|s|² ≤ Λ` (`norm_selbergTransform_sub_one_le`):
on its support `|Im w - 1|² ≤ 8R`, so `(Im w)^s = exp(s log Im w)` is within `½` of `1`. On the
critical line `|s|² = s(1 - s) = λ`.

So every cuspidal eigenvalue `λ ≤ Λ` gives an eigenvalue of norm at least `½` of one compact
symmetric operator. Such eigenvalues are finitely many, each with a finite-dimensional eigenspace,
and the basis vectors with `λ ≤ Λ` form an orthonormal family in their sum. Hence there are finitely
many of them (`finite_cuspEigenIndex_le`).

With the existence theorem the counting function `N(Λ) = #{i : λ_i ≤ Λ}` is finite and tends to
infinity (`tendsto_cuspCount`), and the eigenvalues are unbounded (`not_bddAbove_cuspEigenvalues`):
the undamped tones of the modular black hole form a discrete sequence of frequencies with no finite
accumulation point.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  MaassFiniteDeckDirichlet SelbergMaassCongruenceTrace
open GaloisForLFunctions.HTGeometry (pairU)

namespace CuspSpectrum

/-! ### The Selberg transform of a narrow kernel -/

/-- On the support of a kernel of radius `R ≤ 1/32` around `i`, the height lies in `(½, 2)` and
`(Im w - 1)² ≤ 8R`. -/
theorem height_bounds {w : ℍ} {R : ℝ} (hR : R ≤ 1 / 32) (hu : pairU UpperHalfPlane.I w ≤ R) :
    1 / 2 < w.im ∧ (w.im - 1) ^ 2 ≤ 8 * R := by
  have hy := w.im_pos
  have hR0 : 0 ≤ R := le_trans (by unfold pairU; positivity) hu
  have hd : |1 - w.im| ≤ dist ((UpperHalfPlane.I : ℍ) : ℂ) (w : ℂ) := by
    rw [dist_eq_norm]
    have := Complex.abs_im_le_norm (((UpperHalfPlane.I : ℍ) : ℂ) - w)
    simpa using this
  have hu' : dist ((UpperHalfPlane.I : ℍ) : ℂ) (w : ℂ) ^ 2 ≤ 4 * R * w.im := by
    unfold pairU at hu
    rw [UpperHalfPlane.I_im, div_le_iff₀ (by positivity)] at hu
    linarith
  have h1 : (1 - w.im) ^ 2 ≤ 4 * R * w.im :=
    calc (1 - w.im) ^ 2 = |1 - w.im| ^ 2 := (sq_abs _).symm
      _ ≤ dist ((UpperHalfPlane.I : ℍ) : ℂ) (w : ℂ) ^ 2 := by gcongr
      _ ≤ _ := hu'
  have h2 : (1 - w.im) ^ 2 ≤ w.im / 8 := by nlinarith [mul_le_mul_of_nonneg_right hR hy.le]
  have hlo : 1 / 2 < w.im := by nlinarith
  have hhi : w.im < 2 := by nlinarith
  refine ⟨hlo, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hhi.le hR0]

/-- `|log y| ≤ 2 |y - 1|` for `y > ½`. -/
theorem abs_log_le {y : ℝ} (hy : 1 / 2 < y) : |Real.log y| ≤ 2 * |y - 1| := by
  have hy0 : 0 < y := by linarith
  have hinv : y⁻¹ < 2 := by
    rw [inv_lt_comm₀ hy0 (by norm_num)]
    linarith
  have h1 : |1 - y⁻¹| ≤ 2 * |y - 1| := by
    rw [show 1 - y⁻¹ = (y - 1) * y⁻¹ by field_simp, abs_mul, abs_of_pos (inv_pos.mpr hy0)]
    nlinarith [abs_nonneg (y - 1), mul_le_mul_of_nonneg_left hinv.le (abs_nonneg (y - 1))]
  rw [abs_le]
  constructor
  · linarith [Real.one_sub_inv_le_log_of_pos hy0, neg_abs_le (1 - y⁻¹)]
  · linarith [Real.log_le_sub_one_of_pos hy0, le_abs_self (y - 1), abs_nonneg (y - 1)]

/-- Near height `1` the power `y^s` is within `½` of `1`, uniformly in `|s|² ≤ Λ`. -/
theorem norm_cpow_sub_one_le {y : ℝ} (hy1 : 1 / 2 < y) {s : ℂ} {Λ R : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ‖s‖ ^ 2 ≤ Λ) (hyR : (y - 1) ^ 2 ≤ 8 * R) (hR : R * (512 * (Λ + 1)) ≤ 1) :
    ‖(y : ℂ) ^ s - 1‖ ≤ 1 / 2 := by
  have hy0 : 0 < y := by linarith
  have hR0 : 0 ≤ R := by nlinarith [sq_nonneg (y - 1)]
  have hlog := abs_log_le hy1
  have hz2 : ‖(Real.log y : ℂ) * s‖ ^ 2 ≤ 1 / 16 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have h1 : |Real.log y| ^ 2 ≤ 4 * (y - 1) ^ 2 := by
      nlinarith [abs_nonneg (Real.log y), abs_nonneg (y - 1), sq_abs (y - 1)]
    calc |Real.log y| ^ 2 * ‖s‖ ^ 2 ≤ (4 * (y - 1) ^ 2) * Λ :=
          mul_le_mul h1 hs (by positivity) (by positivity)
      _ ≤ (4 * (8 * R)) * Λ := by gcongr
      _ ≤ 1 / 16 := by nlinarith
  have hz : ‖(Real.log y : ℂ) * s‖ ≤ 1 / 4 := by nlinarith [norm_nonneg ((Real.log y : ℂ) * s)]
  have he : (y : ℂ) ^ s = Complex.exp ((Real.log y : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy0.ne'), Complex.ofReal_log hy0.le]
  rw [he]
  calc ‖Complex.exp ((Real.log y : ℂ) * s) - 1‖ ≤ 2 * ‖(Real.log y : ℂ) * s‖ :=
        Complex.norm_exp_sub_one_le (by linarith)
    _ ≤ 1 / 2 := by linarith

/-- **A narrow unit kernel has Selberg transform near `1`** on the spectral disc `|s|² ≤ Λ`. -/
theorem norm_selbergTransform_sub_one_le (P : SmoothProfile) (hP0 : ∀ u, 0 ≤ P.toFun u)
    (hPm : ppKernelMass P.toFun = 1) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hR : P.radius * (512 * (Λ + 1)) ≤ 1)
    {s : ℂ} (hs : ‖s‖ ^ 2 ≤ Λ) : ‖selbergTransform P.toFun s - 1‖ ≤ 1 / 2 := by
  have hc : Continuous P.toFun := P.contDiff_two.continuous
  have hR32 : P.radius ≤ 1 / 32 := by nlinarith [P.radius_nonneg]
  have hEc := HyperbolicPointPair.continuous_of_smooth (HyperbolicPowerEigen.powerEigen_smooth s)
  have hint1 : Integrable fun w : ℍ =>
      ((P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ) * HyperbolicPowerEigen.powerEigen s w :=
    (integrable_pairKernel_smul' hc P.kernelSupport hEc UpperHalfPlane.I).congr
      (Eventually.of_forall fun w => by simp [Complex.real_smul])
  have hintR : Integrable fun w : ℍ => P.toFun (pairU UpperHalfPlane.I w) :=
    (integrable_pairKernel_smul' hc P.kernelSupport (continuous_const (y := (1 : ℝ)))
      UpperHalfPlane.I).congr (Eventually.of_forall fun w => by simp)
  have hint2 : Integrable fun w : ℍ => ((P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ) := hintR.ofReal
  have hmass : ∫ w : ℍ, ((P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ) = 1 := by
    rw [integral_complex_ofReal, integral_pairKernel hc hP0 hPm UpperHalfPlane.I, Complex.ofReal_one]
  have e : selbergTransform P.toFun s - 1 = ∫ w : ℍ, ((P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ) *
      (HyperbolicPowerEigen.powerEigen s w - 1) := by
    have h3 : ∫ w : ℍ, ((P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ) *
        (HyperbolicPowerEigen.powerEigen s w - 1) =
        selbergTransform P.toFun s - ∫ w : ℍ, ((P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ) := by
      rw [selbergTransform, ← integral_sub hint1 hint2]
      congr 1
      funext w
      ring
    rw [h3, hmass]
  rw [e]
  have hbound : ∀ w : ℍ, ‖((P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ) *
      (HyperbolicPowerEigen.powerEigen s w - 1)‖ ≤ P.toFun (pairU UpperHalfPlane.I w) * (1 / 2) := by
    intro w
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP0 _)]
    by_cases hu : pairU UpperHalfPlane.I w ≤ P.radius
    · obtain ⟨h1, h3⟩ := height_bounds hR32 hu
      exact mul_le_mul_of_nonneg_left (norm_cpow_sub_one_le h1 hΛ hs h3 hR) (hP0 _)
    · rw [P.kernelSupport _ (not_le.mp hu)]
      simp
  calc ‖∫ w : ℍ, ((P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ) *
        (HyperbolicPowerEigen.powerEigen s w - 1)‖
      ≤ ∫ w : ℍ, P.toFun (pairU UpperHalfPlane.I w) * (1 / 2) :=
        norm_integral_le_of_norm_le (hintR.mul_const _) (Eventually.of_forall hbound)
    _ = 1 / 2 := by rw [integral_mul_const, integral_pairKernel hc hP0 hPm UpperHalfPlane.I, one_mul]

end CuspSpectrum

open CuspSpectrum

/-! ### Finitely many eigenvalues below every bound -/

/-- **The cusp spectrum is discrete**: finitely many basis vectors have eigenvalue at most `Λ`. -/
theorem finite_cuspEigenIndex_le (Λ : ℝ) : {i : CuspEigenIndex 0 | i.1 ≤ Λ}.Finite := by
  set L := max Λ 0
  have hL : 0 ≤ L := le_max_right _ _
  obtain ⟨P, hPR, hP0, hPm⟩ := exists_smoothUnitProfile (R := 1 / (512 * (L + 1))) (by positivity)
  have hR : P.radius * (512 * (L + 1)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hPR (by positivity : (0 : ℝ) ≤ 512 * (L + 1))
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  set T : CuspidalL2 0 →ₗ[ℂ] CuspidalL2 0 := (P.pp.cuspOp 0 : CuspidalL2 0 →ₗ[ℂ] CuspidalL2 0)
  have hTc : IsCompactOperator T := P.pp.isCompactOperator_cuspOp
  have hTs : T.IsSymmetric := P.pp.cuspOp_isSymmetric
  set F := {μ : ℂ | Module.End.HasEigenvalue T μ ∧ (1 / 2 : ℝ) ≤ ‖μ‖}
  have hF : F.Finite :=
    GaloisForLFunctions.HTGeometry.finite_setOf_hasEigenvalue_norm_ge hTc hTs (by norm_num)
  have key : ∀ i : CuspEigenIndex 0, i.1 ≤ Λ →
      ∃ μ ∈ F, (cuspEigenBasis 0 i : CuspidalL2 0) ∈ Module.End.eigenspace T μ := by
    intro i hi
    have hq := one_quarter_le_cuspEigenBasis i
    set t := Real.sqrt (i.1 - 1 / 4)
    have ht : t ^ 2 = i.1 - 1 / 4 := Real.sq_sqrt (by linarith)
    set s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
    have hs1 : s * (1 - s) = (i.1 : ℂ) := by
      have h : s * (1 - s) = 1 / 4 + ((t ^ 2 : ℝ) : ℂ) := by
        simp only [s]
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [h, ht]
      push_cast
      ring
    have hs2 : ‖s‖ ^ 2 ≤ L := by
      rw [← Complex.normSq_eq_norm_sq]
      have h : Complex.normSq s = 1 / 4 + t ^ 2 := by
        simp [s, Complex.normSq_apply]
        ring
      rw [h, ht]
      linarith [le_max_left Λ 0]
    have hmem : (cuspEigenBasis 0 i : CuspidalL2 0) ∈
        Module.End.eigenspace T (selbergTransform P.toFun s) := by
      obtain ⟨U, hU, hb⟩ := cuspEigenBasis_spec i
      exact eigenClassSpace_le_eigenspace P hs1 ⟨U, hU, hb⟩
    refine ⟨selbergTransform P.toFun s, ⟨?_, ?_⟩, hmem⟩
    · exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, (cuspEigenBasis 0).orthonormal.ne_zero i⟩
    · have h := norm_selbergTransform_sub_one_le P hP0 hPm hL hR hs2
      have h2 := norm_sub_norm_le (1 : ℂ) (selbergTransform P.toFun s)
      rw [norm_sub_rev, norm_one] at h2
      linarith
  haveI : Finite F := hF.to_subtype
  haveI : ∀ μ : F, FiniteDimensional ℂ (Module.End.eigenspace T (μ : ℂ)) := fun μ =>
    ContinuousLinearMap.finite_dimensional_eigenspace hTc (μ : ℂ) (by
      intro h0
      have h := μ.2.2
      rw [h0, norm_zero] at h
      norm_num at h)
  choose μ hμF hμ using key
  have hW : ∀ i : {i : CuspEigenIndex 0 | i.1 ≤ Λ},
      (cuspEigenBasis 0 i.1 : CuspidalL2 0) ∈ ⨆ ν : F, Module.End.eigenspace T (ν : ℂ) := fun i =>
    (le_iSup (fun ν : F => Module.End.eigenspace T (ν : ℂ)) ⟨μ i.1 i.2, hμF i.1 i.2⟩) (hμ i.1 i.2)
  have hv := ((cuspEigenBasis 0).orthonormal.comp _ Subtype.val_injective).codRestrict _ hW
  have hfin : Finite {i : CuspEigenIndex 0 | i.1 ≤ Λ} := hv.linearIndependent.finite
  exact Set.finite_coe_iff.mp hfin

/-- Finitely many distinct cuspidal eigenvalues lie below every bound. -/
theorem finite_cuspEigenvalues_le (Λ : ℝ) :
    {l ∈ Set.range (Sigma.fst : CuspEigenIndex 0 → ℝ) | l ≤ Λ}.Finite :=
  ((finite_cuspEigenIndex_le Λ).image Sigma.fst).subset (by
    rintro l ⟨⟨i, rfl⟩, hl⟩
    exact ⟨i, hl, rfl⟩)

/-- **The cuspidal eigenvalues are unbounded.** -/
theorem not_bddAbove_cuspEigenvalues : ¬ BddAbove (Set.range (Sigma.fst : CuspEigenIndex 0 → ℝ)) := by
  rintro ⟨Λ, hΛ⟩
  exact infinite_cuspEigenvalues ((finite_cuspEigenvalues_le Λ).subset fun l hl => ⟨hl, hΛ hl⟩)

/-- The counting function of the cusp spectrum, with multiplicity. -/
def cuspCount (Λ : ℝ) : ℕ := (finite_cuspEigenIndex_le Λ).toFinset.card

/-- **The counting function is finite and tends to infinity**: the undamped tones of the modular
black hole are a discrete sequence with no finite accumulation point. -/
theorem tendsto_cuspCount : Tendsto cuspCount atTop atTop := by
  refine tendsto_atTop_atTop.2 fun n => ?_
  haveI := infinite_cuspEigenIndex
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (CuspEigenIndex 0) n
  refine ⟨∑ i ∈ S, |i.1|, fun Λ hΛ => ?_⟩
  rw [← hS]
  refine Finset.card_le_card fun i hi => ?_
  rw [Set.Finite.mem_toFinset]
  show i.1 ≤ Λ
  have h1 : |i.1| ≤ ∑ j ∈ S, |j.1| :=
    Finset.single_le_sum (f := fun j : CuspEigenIndex 0 => |j.1|) (fun j _ => abs_nonneg j.1) hi
  linarith [le_abs_self i.1]

end GaloisForLFunctions.BlackHoleRingdown
