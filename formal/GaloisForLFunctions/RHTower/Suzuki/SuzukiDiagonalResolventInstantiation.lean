import GaloisForLFunctions.RHTower.Suzuki.SuzukiStrongResolventLimit
import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-!
# Diagonal instantiation of the strong resolvent limits

The strong resolvent limits `tendsto_resolventFamily_id` and `tendsto_neumannShiftFamily_id`
are stated for an arbitrary bounded operator `B` that is self-adjoint, injective, and has
spectrum in `Icc 0 M`.  This file exhibits an explicit family of such operators, so that the
hypothesis class is inhabited and the limits are not vacuous.

The operators are the diagonal multipliers of `lp (fun _ : ℕ => ℂ) 2` with nonnegative real,
nowhere vanishing, bounded multiplier sequence.  Such an operator is symmetric because the
multiplier is real, injective because the multiplier never vanishes, and positive because the
multiplier is nonnegative; positivity places the spectrum in `Icc 0 ‖B‖`.

Taking the multiplier `n ↦ 1/(n+1)` gives a single concrete operator whose multiplier tends to
zero, which is the situation the abstract theorems were designed for: the resolvent symbols fail
to converge uniformly near the accumulation point `0` of the spectrum, so the convergence is
strong and not norm.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology _root_.RHTower

/-- Instance search does not locate the real continuous functional calculus on the bounded
operators of `lp (fun _ : ℕ => ℂ) 2`, although the restriction instance applies: naming it
resolves the synthesis. -/
noncomputable local instance : ContinuousFunctionalCalculus ℝ
    (_root_.RHTower.EllTwo →L[ℂ] _root_.RHTower.EllTwo) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

instance : Nontrivial _root_.RHTower.EllTwo := by
  refine ⟨⟨lp.single 2 0 (1 : ℂ), 0, ?_⟩⟩
  intro h
  have := congrArg (fun x : _root_.RHTower.EllTwo => (x : ℕ → ℂ) 0) h
  simp [lp.single_apply] at this

/-- A diagonal multiplier with real entries is symmetric. -/
theorem isSymmetric_diagonalOperator_ofReal (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) :
    ((diagonalOperator (fun n => (r n : ℂ)) hC : _root_.RHTower.EllTwo →L[ℂ]
      _root_.RHTower.EllTwo) : _root_.RHTower.EllTwo →ₗ[ℂ] _root_.RHTower.EllTwo).IsSymmetric := by
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [ContinuousLinearMap.coe_coe, diagonalOperator_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal]
  ring

/-- A diagonal multiplier with real entries is self-adjoint. -/
theorem isSelfAdjoint_diagonalOperator_ofReal (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) :
    IsSelfAdjoint (diagonalOperator (fun n => (r n : ℂ)) hC) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (isSymmetric_diagonalOperator_ofReal r hC)

/-- A diagonal multiplier that never vanishes is injective. -/
theorem injective_diagonalOperator (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C)
    (hne : ∀ n, lam n ≠ 0) : Function.Injective (diagonalOperator lam hC) := by
  intro f g h
  refine lp.ext (funext fun n => ?_)
  have hn : lam n * f n = lam n * g n := by
    have := congrArg (fun x : _root_.RHTower.EllTwo => (x : ℕ → ℂ) n) h
    simpa using this
  exact mul_left_cancel₀ (hne n) hn

/-- A diagonal multiplier with nonnegative real entries is a positive operator. -/
theorem isPositive_diagonalOperator_ofReal (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) (hr : ∀ n, 0 ≤ r n) :
    (diagonalOperator (fun n => (r n : ℂ)) hC).IsPositive := by
  refine ⟨isSymmetric_diagonalOperator_ofReal r hC, fun f => ?_⟩
  have hsum : Summable fun n =>
      inner ℂ (((diagonalOperator (fun n => (r n : ℂ)) hC) f : _root_.RHTower.EllTwo) n)
        ((f : _root_.RHTower.EllTwo) n) := lp.summable_inner _ _
  show (0 : ℝ) ≤ (inner ℂ ((diagonalOperator (fun n => (r n : ℂ)) hC) f) f).re
  rw [lp.inner_eq_tsum, Complex.re_tsum hsum]
  refine tsum_nonneg fun n => ?_
  have hval : inner ℂ (((diagonalOperator (fun n => (r n : ℂ)) hC) f : _root_.RHTower.EllTwo) n)
      ((f : _root_.RHTower.EllTwo) n)
      = ((r n : ℂ)) * ((Complex.normSq ((f : ℕ → ℂ) n) : ℝ) : ℂ) := by
    simp only [diagonalOperator_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    rw [← Complex.mul_conj]
    ring
  rw [hval]
  simp [Complex.normSq_nonneg, mul_nonneg, hr n]

/-- A diagonal multiplier with nonnegative real entries is nonnegative in the operator order. -/
theorem nonneg_diagonalOperator_ofReal (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) (hr : ∀ n, 0 ≤ r n) :
    0 ≤ diagonalOperator (fun n => (r n : ℂ)) hC :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (isPositive_diagonalOperator_ofReal r hC hr)

/-- The spectrum of a nonnegative diagonal multiplier lies in `Icc 0 ‖B‖`. -/
theorem spectrum_diagonalOperator_ofReal_subset (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) (hr : ∀ n, 0 ≤ r n) :
    spectrum ℝ (diagonalOperator (fun n => (r n : ℂ)) hC)
      ⊆ Set.Icc 0 ‖diagonalOperator (fun n => (r n : ℂ)) hC‖ :=
  spectrum_subset_Icc_of_nonneg (nonneg_diagonalOperator_ofReal r hC hr)

/-- The strong resolvent limit holds for every nonnegative, nowhere vanishing diagonal
multiplier. -/
theorem tendsto_diagonalResolventFamily_id (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) (hr : ∀ n, 0 ≤ r n) (hne : ∀ n, r n ≠ 0)
    (rho : ℝ) (v : _root_.RHTower.EllTwo) :
    Tendsto (fun s : ℝ => cfc (fun x : ℝ => (s - rho) * x / (1 + s * x))
      (diagonalOperator (fun n => (r n : ℂ)) hC) v) atTop (𝓝 v) :=
  tendsto_resolventFamily_id (isSelfAdjoint_diagonalOperator_ofReal r hC)
    (injective_diagonalOperator _ hC (fun n => by
      simpa using Complex.ofReal_ne_zero.mpr (hne n)))
    (spectrum_diagonalOperator_ofReal_subset r hC hr) v

/-- The Neumann shift limit holds for every nonnegative, nowhere vanishing diagonal
multiplier. -/
theorem tendsto_diagonalNeumannShiftFamily_id (r : ℕ → ℝ) {C : ℝ}
    (hC : ∀ n, ‖((r n : ℂ))‖ ≤ C) (hr : ∀ n, 0 ≤ r n) (hne : ∀ n, r n ≠ 0)
    (rho : ℝ) (v : _root_.RHTower.EllTwo) :
    Tendsto (fun eps : ℝ => cfc (fun x : ℝ => x / (eps + (1 + eps * rho) * x))
      (diagonalOperator (fun n => (r n : ℂ)) hC) v) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 v) :=
  tendsto_neumannShiftFamily_id (isSelfAdjoint_diagonalOperator_ofReal r hC)
    (injective_diagonalOperator _ hC (fun n => by
      simpa using Complex.ofReal_ne_zero.mpr (hne n)))
    (spectrum_diagonalOperator_ofReal_subset r hC hr) v

/-- The harmonic multiplier `n ↦ 1/(n+1)`, a nonnegative sequence tending to zero. -/
def harmonicMultiplier : ℕ → ℝ := fun n => 1 / (n + 1)

theorem harmonicMultiplier_pos (n : ℕ) : 0 < harmonicMultiplier n := by
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simpa [harmonicMultiplier] using one_div_pos.mpr this

theorem harmonicMultiplier_nonneg (n : ℕ) : 0 ≤ harmonicMultiplier n :=
  (harmonicMultiplier_pos n).le

theorem harmonicMultiplier_ne_zero (n : ℕ) : harmonicMultiplier n ≠ 0 :=
  ne_of_gt (harmonicMultiplier_pos n)

theorem norm_harmonicMultiplier_le (n : ℕ) : ‖((harmonicMultiplier n : ℂ))‖ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : harmonicMultiplier n ≤ 1 := by
    rw [harmonicMultiplier, div_le_one h0]
    exact h1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (harmonicMultiplier_nonneg n)]
  exact this

/-- The diagonal operator with harmonic multiplier: an explicit positive injective self-adjoint
operator whose spectrum accumulates at `0`. -/
def harmonicDiagonalOperator : _root_.RHTower.EllTwo →L[ℂ] _root_.RHTower.EllTwo :=
  diagonalOperator (fun n => ((harmonicMultiplier n : ℝ) : ℂ)) norm_harmonicMultiplier_le

theorem isSelfAdjoint_harmonicDiagonalOperator : IsSelfAdjoint harmonicDiagonalOperator :=
  isSelfAdjoint_diagonalOperator_ofReal _ norm_harmonicMultiplier_le

theorem injective_harmonicDiagonalOperator : Function.Injective harmonicDiagonalOperator :=
  injective_diagonalOperator _ norm_harmonicMultiplier_le (fun n => by
    simpa using Complex.ofReal_ne_zero.mpr
      (harmonicMultiplier_ne_zero n))

theorem nonneg_harmonicDiagonalOperator : 0 ≤ harmonicDiagonalOperator :=
  nonneg_diagonalOperator_ofReal _ norm_harmonicMultiplier_le harmonicMultiplier_nonneg

/-- The strong resolvent limit for the explicit harmonic diagonal operator. -/
theorem tendsto_harmonicResolventFamily_id (rho : ℝ) (v : _root_.RHTower.EllTwo) :
    Tendsto (fun s : ℝ => cfc (fun x : ℝ => (s - rho) * x / (1 + s * x))
      harmonicDiagonalOperator v) atTop (𝓝 v) :=
  tendsto_diagonalResolventFamily_id _ norm_harmonicMultiplier_le harmonicMultiplier_nonneg
    harmonicMultiplier_ne_zero rho v

/-- The Neumann shift limit for the explicit harmonic diagonal operator. -/
theorem tendsto_harmonicNeumannShiftFamily_id (rho : ℝ) (v : _root_.RHTower.EllTwo) :
    Tendsto (fun eps : ℝ => cfc (fun x : ℝ => x / (eps + (1 + eps * rho) * x))
      harmonicDiagonalOperator v) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 v) :=
  tendsto_diagonalNeumannShiftFamily_id _ norm_harmonicMultiplier_le harmonicMultiplier_nonneg
    harmonicMultiplier_ne_zero rho v

/-- A diagonal multiplier acts on the canonical basis of `ℓ²` by its entries. -/
theorem diagonalOperator_lpBasis (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) (i : ℕ) :
    diagonalOperator lam hC (HilbertSchmidt.lpBasis ℕ i)
      = lam i • HilbertSchmidt.lpBasis ℕ i := by
  rw [HilbertSchmidt.lpBasis_apply]
  refine lp.ext (funext fun n => ?_)
  by_cases h : n = i
  · subst h
    simp [lp.single_apply]
  · simp [lp.single_apply, h]

/-- A diagonal multiplier tending to zero gives a compact operator. -/
theorem isCompactOperator_diagonalOperator (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C)
    (hlim : Tendsto (fun n => ‖lam n‖) atTop (𝓝 0)) :
    IsCompactOperator (diagonalOperator lam hC) := by
  refine GaloisForLFunctions.HTGeometry.isCompactOperator_of_diag_tendsto_cofinite
    (HilbertSchmidt.lpBasis ℕ) (diagonalOperator_lpBasis lam hC) ?_
  rwa [Nat.cofinite_eq_atTop]

theorem tendsto_harmonicMultiplier_zero :
    Tendsto (fun n => ‖((harmonicMultiplier n : ℝ) : ℂ)‖) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine h.congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (harmonicMultiplier_nonneg n)]
  rfl

/-- The harmonic diagonal operator is compact. -/
theorem isCompactOperator_harmonicDiagonalOperator :
    IsCompactOperator harmonicDiagonalOperator :=
  isCompactOperator_diagonalOperator _ norm_harmonicMultiplier_le tendsto_harmonicMultiplier_zero

/-- Only finitely many spectral points of the harmonic diagonal operator lie outside any disc
around `0`: the spectrum accumulates only at `0`. -/
theorem finite_spectrum_harmonicDiagonalOperator {eps : ℝ} (heps : 0 < eps) :
    {mu : ℂ | mu ∈ spectrum ℂ harmonicDiagonalOperator ∧ eps ≤ ‖mu‖}.Finite :=
  GaloisForLFunctions.HTGeometry.finite_setOf_mem_spectrum_norm_ge
    isCompactOperator_harmonicDiagonalOperator
    (isSymmetric_diagonalOperator_ofReal _ norm_harmonicMultiplier_le) heps

/-- The spectrum of the harmonic diagonal operator is countable. -/
theorem countable_spectrum_harmonicDiagonalOperator :
    (spectrum ℂ harmonicDiagonalOperator).Countable :=
  GaloisForLFunctions.HTGeometry.countable_spectrum_of_isCompactOperator
    isCompactOperator_harmonicDiagonalOperator
    (isSymmetric_diagonalOperator_ofReal _ norm_harmonicMultiplier_le)

theorem injective_harmonicMultiplier : Function.Injective harmonicMultiplier := by
  intro a b h
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  rw [harmonicMultiplier, harmonicMultiplier, div_eq_div_iff ha.ne' hb.ne'] at h
  have : (a : ℝ) = b := by linarith
  exact_mod_cast this

/-- Every harmonic multiplier entry is an eigenvalue, hence lies in the spectrum. -/
theorem mem_spectrum_harmonicMultiplier (n : ℕ) :
    ((harmonicMultiplier n : ℝ) : ℂ) ∈ spectrum ℂ harmonicDiagonalOperator := by
  refine (IsCompactOperator.hasEigenvalue_iff_mem_spectrum
    isCompactOperator_harmonicDiagonalOperator ?_).mp ?_
  · simpa using Complex.ofReal_ne_zero.mpr (harmonicMultiplier_ne_zero n)
  · refine Module.End.hasEigenvalue_of_hasEigenvector
      (x := HilbertSchmidt.lpBasis ℕ n) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact diagonalOperator_lpBasis _ norm_harmonicMultiplier_le n
    · exact (HilbertBasis.orthonormal (HilbertSchmidt.lpBasis ℕ)).ne_zero n

/-- The spectrum of the harmonic diagonal operator is infinite: it contains the whole null
sequence of multiplier entries. -/
theorem infinite_spectrum_harmonicDiagonalOperator :
    (spectrum ℂ harmonicDiagonalOperator).Infinite :=
  Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((harmonicMultiplier n : ℝ) : ℂ))
    (fun _ _ h => injective_harmonicMultiplier (Complex.ofReal_inj.mp h))
    mem_spectrum_harmonicMultiplier

theorem tendsto_harmonicMultiplier_ofReal_zero :
    Tendsto (fun n : ℕ => ((harmonicMultiplier n : ℝ) : ℂ)) atTop (𝓝 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr tendsto_harmonicMultiplier_zero

/-- Zero lies in the spectrum, as the limit of the multiplier entries. -/
theorem zero_mem_spectrum_harmonicDiagonalOperator :
    (0 : ℂ) ∈ spectrum ℂ harmonicDiagonalOperator :=
  (spectrum.isClosed (𝕜 := ℂ) harmonicDiagonalOperator).mem_of_tendsto
    tendsto_harmonicMultiplier_ofReal_zero
    (Eventually.of_forall mem_spectrum_harmonicMultiplier)

/-- The harmonic diagonal operator has dense range. -/
theorem denseRange_harmonicDiagonalOperator : DenseRange harmonicDiagonalOperator :=
  GaloisForLFunctions.HTGeometry.denseRange_of_isSelfAdjoint_of_injective
    isSelfAdjoint_harmonicDiagonalOperator injective_harmonicDiagonalOperator

/-- The harmonic diagonal operator is not surjective: `0` lies in its spectrum, so it is not
invertible, and an injective bounded operator on a Banach space that is surjective would be. -/
theorem not_surjective_harmonicDiagonalOperator :
    ¬ Function.Surjective harmonicDiagonalOperator := by
  intro hsurj
  have hunit : IsUnit harmonicDiagonalOperator :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨injective_harmonicDiagonalOperator, hsurj⟩
  have h0 := zero_mem_spectrum_harmonicDiagonalOperator
  rw [spectrum.mem_iff] at h0
  refine h0 ?_
  simpa using hunit.neg

/-- The range is dense but proper, so the operator inverted in the resolvent coordinate is
densely defined and not everywhere defined: it is genuinely unbounded. -/
theorem range_harmonicDiagonalOperator_ne_top :
    LinearMap.range (harmonicDiagonalOperator : _root_.RHTower.EllTwo →ₗ[ℂ]
      _root_.RHTower.EllTwo) ≠ ⊤ := by
  intro h
  exact not_surjective_harmonicDiagonalOperator (LinearMap.range_eq_top.mp h)

end GaloisForLFunctions.RHTower
