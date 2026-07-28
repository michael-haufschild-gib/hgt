import GaloisForLFunctions.HTGeometry.PeripheralContractionPointSpectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Peripheral/transient decomposition of a finite contraction

This file builds the operator-theoretic bridge from an arbitrary
finite-dimensional Hilbert contraction to its lossless peripheral subspace
and stable orthogonal complement.
-/

open Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace RHTower

/-! ## A quantitative-free spectral-radius decay lemma -/

/-- Powers of an element of a complete complex normed algebra converge to
zero whenever its spectral radius is strictly below one. -/
theorem tendsto_pow_atTop_nhds_zero_of_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A]
    (a : A) (hradius : spectralRadius ℂ a < 1) :
    Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  have hroot :=
    spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  have hroot_lt : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ)) < 1 :=
    hroot.eventually (Iio_mem_nhds hradius)
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_gt_atTop 0
  obtain ⟨N, hNroot, hNpos⟩ :=
    (hroot_lt.and hpositive).exists
  have hNne : N ≠ 0 := Nat.ne_of_gt hNpos
  have hNrootReal : ‖a ^ N‖ ^ (1 / N : ℝ) < 1 :=
    ENNReal.ofReal_lt_one.mp hNroot
  have hNnorm : ‖a ^ N‖ < 1 := by
    rw [Real.rpow_lt_one_iff' (norm_nonneg _) (by positivity)] at hNrootReal
    exact hNrootReal
  let C : ℝ := max 1 (‖a‖ ^ N)
  have hrem (n : ℕ) : ‖a ^ (n % N)‖ ≤ C := by
    calc
      ‖a ^ (n % N)‖ ≤ ‖a‖ ^ (n % N) := norm_pow_le _ _
      _ ≤ C := by
        dsimp only [C]
        by_cases ha : ‖a‖ ≤ 1
        · exact (pow_le_one₀ (norm_nonneg _) ha).trans (le_max_left _ _)
        · exact (pow_le_pow_right₀ (le_of_not_ge ha)
            (Nat.le_of_lt (Nat.mod_lt n hNpos))).trans
              (le_max_right _ _)
  have hbound (n : ℕ) :
      ‖a ^ n‖ ≤ ‖a ^ N‖ ^ (n / N) * C := by
    calc
      ‖a ^ n‖ =
          ‖(a ^ N) ^ (n / N) * a ^ (n % N)‖ := by
        congr 1
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      _ ≤ ‖(a ^ N) ^ (n / N)‖ * ‖a ^ (n % N)‖ :=
        norm_mul_le _ _
      _ ≤ ‖a ^ N‖ ^ (n / N) * C := by
        exact mul_le_mul (norm_pow_le _ _) (hrem n)
          (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg (a ^ n)) hbound ?_
  simpa only [zero_mul] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (norm_nonneg (a ^ N)) hNnorm).comp
        (Nat.tendsto_div_const_atTop hNne)).mul_const C

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Unit-modulus eigenvalues of a finite contraction. -/
abbrev FiniteContractionPeripheralEigenvalue (T : H →L[ℂ] H) :=
  {μ : Module.End.Eigenvalues T.toLinearMap // ‖(μ : ℂ)‖ = 1}

/-- Eigenspace belonging to a bundled peripheral eigenvalue. -/
def finiteContractionPeripheralEigenspace (T : H →L[ℂ] H)
    (μ : FiniteContractionPeripheralEigenvalue T) : Submodule ℂ H :=
  Module.End.eigenspace T.toLinearMap (μ : ℂ)

/-- Span of all unit-modulus eigenspaces. -/
def finiteContractionPeripheralSubspace (T : H →L[ℂ] H) :
    Submodule ℂ H :=
  ⨆ μ : FiniteContractionPeripheralEigenvalue T,
    finiteContractionPeripheralEigenspace T μ

/-- Distinct peripheral eigenspaces of a contraction are orthogonal. -/
theorem finiteContractionPeripheralEigenspaces_orthogonal
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    OrthogonalFamily ℂ
      (fun μ : FiniteContractionPeripheralEigenvalue T =>
        finiteContractionPeripheralEigenspace T μ)
      (fun μ => (finiteContractionPeripheralEigenspace T μ).subtypeₗᵢ) := by
  rintro μ ν hμν ⟨x, hx⟩ ⟨y, hy⟩
  apply HTGeometry.inner_eq_zero_of_distinct_peripheral_eigenvectors T hT
  · exact Module.End.mem_eigenspace_iff.mp hx
  · exact Module.End.mem_eigenspace_iff.mp hy
  · exact μ.property
  · intro h
    apply hμν
    exact Subtype.ext (Subtype.ext h)

/-- The contraction preserves its peripheral span. -/
theorem finiteContractionPeripheralSubspace_invariant
    (T : H →L[ℂ] H) :
    ∀ x ∈ finiteContractionPeripheralSubspace T,
      T x ∈ finiteContractionPeripheralSubspace T := by
  intro x hx
  induction hx using Submodule.iSup_induction' with
  | mem μ x hx =>
      apply Submodule.mem_iSup_of_mem μ
      unfold finiteContractionPeripheralEigenspace at hx ⊢
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      exact (congrArg T hx).trans (map_smul T _ _)
  | zero =>
      simpa using (Submodule.zero_mem
        (finiteContractionPeripheralSubspace T))
  | add x y _ _ hx hy =>
      simpa only [map_add] using Submodule.add_mem _ hx hy

/-- The adjoint preserves the peripheral span. -/
theorem finiteContractionPeripheralSubspace_adjoint_invariant
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∀ x ∈ finiteContractionPeripheralSubspace T,
      T.adjoint x ∈ finiteContractionPeripheralSubspace T := by
  intro x hx
  induction hx using Submodule.iSup_induction' with
  | mem μ x hx =>
      have hadj :=
        HTGeometry.adjoint_eigenvector_of_contraction T hT
          (Module.End.mem_eigenspace_iff.mp hx) μ.property
      apply Submodule.mem_iSup_of_mem μ
      rw [hadj]
      exact Submodule.smul_mem _ _ hx
  | zero =>
      simpa using (Submodule.zero_mem
        (finiteContractionPeripheralSubspace T))
  | add x y _ _ hx hy =>
      simpa only [map_add] using Submodule.add_mem _ hx hy

/-- Orthogonal transient complement of the peripheral span. -/
def finiteContractionTransientSubspace (T : H →L[ℂ] H) :
    Submodule ℂ H :=
  (finiteContractionPeripheralSubspace T)ᗮ

/-- The orthogonal transient complement is invariant under the
contraction. -/
theorem finiteContractionTransientSubspace_invariant
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∀ x ∈ finiteContractionTransientSubspace T,
      T x ∈ finiteContractionTransientSubspace T := by
  intro x hx
  rw [finiteContractionTransientSubspace,
    Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [← T.adjoint_inner_right]
  exact hx _ (finiteContractionPeripheralSubspace_adjoint_invariant
    T hT y hy)

/-- Restriction of a contraction to its transient complement. -/
def finiteContractionTransientRestriction
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    finiteContractionTransientSubspace T →L[ℂ]
      finiteContractionTransientSubspace T :=
  T.restrict (finiteContractionTransientSubspace_invariant T hT)

@[simp]
theorem finiteContractionTransientRestriction_apply_coe
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (x : finiteContractionTransientSubspace T) :
    ((finiteContractionTransientRestriction T hT x :
      finiteContractionTransientSubspace T) : H) = T x := rfl

/-- Every spectral value of the transient restriction lies strictly inside
the unit disk. -/
theorem norm_lt_one_of_mem_spectrum_finiteContractionTransientRestriction
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ
      (finiteContractionTransientRestriction T hT)) :
    ‖μ‖ < 1 := by
  have hμlin : μ ∈ spectrum ℂ
      (finiteContractionTransientRestriction T hT).toLinearMap := by
    rw [← ContinuousLinearMap.spectrum_eq]
    exact hμ
  have heigen : Module.End.HasEigenvalue
      (finiteContractionTransientRestriction T hT).toLinearMap μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμlin
  obtain ⟨x, hxmem, hxne⟩ := heigen.exists_hasEigenvector
  have hxrestrict :
      finiteContractionTransientRestriction T hT x = μ • x :=
    Module.End.mem_eigenspace_iff.mp hxmem
  have hlift : T (x : H) = μ • (x : H) := by
    exact congrArg Subtype.val hxrestrict
  have hxcoe_ne : (x : H) ≠ 0 := by
    intro hx0
    apply hxne
    exact Subtype.ext hx0
  have hxnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr hxcoe_ne
  have hμle : ‖μ‖ ≤ 1 := by
    apply le_of_mul_le_mul_right (a := ‖(x : H)‖) _ hxnorm
    calc
      ‖μ‖ * ‖(x : H)‖ = ‖T (x : H)‖ := by
        rw [hlift, norm_smul]
      _ ≤ ‖T‖ * ‖(x : H)‖ := T.le_opNorm _
      _ ≤ 1 * ‖(x : H)‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg _)
  apply lt_of_le_of_ne hμle
  intro hμeq
  have hμT : Module.End.HasEigenvalue T.toLinearMap μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hlift, hxcoe_ne⟩
  let ν : FiniteContractionPeripheralEigenvalue T :=
    ⟨⟨μ, hμT⟩, hμeq⟩
  have hxPeripheral :
      (x : H) ∈ finiteContractionPeripheralSubspace T := by
    apply Submodule.mem_iSup_of_mem ν
    exact Module.End.mem_eigenspace_iff.mpr hlift
  have hxTransient :
      (x : H) ∈ finiteContractionTransientSubspace T := x.property
  have hinner :
      inner ℂ (x : H) (x : H) = 0 := by
    exact (Submodule.mem_orthogonal'
      (finiteContractionPeripheralSubspace T) (x : H)).mp
        hxTransient (x : H) hxPeripheral
  exact hxcoe_ne (inner_self_eq_zero.mp hinner)

/-- The transient restriction has spectral radius strictly below one. -/
theorem spectralRadius_finiteContractionTransientRestriction_lt_one
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    [Nontrivial (finiteContractionTransientSubspace T)] :
    spectralRadius ℂ (finiteContractionTransientRestriction T hT) < 1 := by
  apply spectrum.spectralRadius_lt_of_forall_lt
    (finiteContractionTransientRestriction T hT)
  intro μ hμ
  exact_mod_cast
    norm_lt_one_of_mem_spectrum_finiteContractionTransientRestriction
      T hT hμ

/-- Powers of the transient restriction converge to zero in operator norm. -/
theorem tendsto_pow_finiteContractionTransientRestriction_zero
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    Tendsto
      (fun n : ℕ => (finiteContractionTransientRestriction T hT) ^ n)
      atTop (𝓝 0) := by
  by_cases hnontrivial :
      Nontrivial (finiteContractionTransientSubspace T)
  · letI := hnontrivial
    exact tendsto_pow_atTop_nhds_zero_of_spectralRadius_lt_one
      (finiteContractionTransientRestriction T hT)
      (spectralRadius_finiteContractionTransientRestriction_lt_one T hT)
  · letI : Subsingleton (finiteContractionTransientSubspace T) :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    have hconstant :
        (fun n : ℕ => (finiteContractionTransientRestriction T hT) ^ n) =
          (fun _ : ℕ => (0 :
            finiteContractionTransientSubspace T →L[ℂ]
              finiteContractionTransientSubspace T)) := by
      funext n
      exact Subsingleton.elim _ _
    rw [hconstant]
    exact tendsto_const_nhds

/-- Restriction and taking powers commute after inclusion into the ambient
Hilbert space. -/
@[simp]
theorem finiteContractionTransientRestriction_pow_apply_coe
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (n : ℕ) (x : finiteContractionTransientSubspace T) :
    ((((finiteContractionTransientRestriction T hT) ^ n) x :
      finiteContractionTransientSubspace T) : H) = (T ^ n) (x : H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change T ((((finiteContractionTransientRestriction T hT) ^ n) x :
        finiteContractionTransientSubspace T) : H) = T ((T ^ n) (x : H))
      rw [ih]

/-- Every transient vector is driven to zero by repeated application of the
finite contraction. -/
theorem tendsto_finiteContraction_pow_apply_transient_zero
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (x : finiteContractionTransientSubspace T) :
    Tendsto (fun n : ℕ => (T ^ n) (x : H)) atTop (𝓝 0) := by
  have hrestricted :
      Tendsto
        (fun n : ℕ =>
          ((finiteContractionTransientRestriction T hT) ^ n) x)
        atTop (𝓝 0) :=
    (ContinuousLinearMap.apply ℂ
      (finiteContractionTransientSubspace T) x).continuous.tendsto 0
      |>.comp (tendsto_pow_finiteContractionTransientRestriction_zero T hT)
  have hinclusion :
      Tendsto
        (fun n : ℕ =>
          (finiteContractionTransientSubspace T).subtypeL
            (((finiteContractionTransientRestriction T hT) ^ n) x))
        atTop
        (𝓝 ((finiteContractionTransientSubspace T).subtypeL 0)) :=
    ((finiteContractionTransientSubspace T).subtypeL.continuous.tendsto 0).comp
      hrestricted
  refine hinclusion.congr' ?_
  filter_upwards with n
  exact finiteContractionTransientRestriction_pow_apply_coe T hT n x

end RHTower
