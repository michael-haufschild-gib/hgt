import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Uniform locality from separated spectral clusters

This file isolates the deterministic mechanism needed to strengthen
finite-horizon Anderson locality to an all-time statement.  A Hermitian
matrix close to a simple diagonal matrix has one separated spectral cluster
near each diagonal energy.  Continuous functional calculus turns plateau
functions on those clusters into a complete family of spectral projections.
Their proximity to coordinate projections controls every transition
amplitude uniformly over all times.

The first layer below is independent of perturbation theory: it constructs
the plateau functions and proves the exact projector algebra from a spectral
cluster certificate.
-/

open Set Filter Topology
open NormedSpace
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Continuous plateau equal to one within distance `δ` of `center` and
zero from distance `2δ` onward. -/
def spectralClusterPlateau (center δ x : ℝ) : ℝ :=
  max 0 (min 1 ((2 * δ - |x - center|) / δ))

theorem continuous_spectralClusterPlateau (center δ : ℝ) :
    Continuous (spectralClusterPlateau center δ) := by
  unfold spectralClusterPlateau
  fun_prop

theorem spectralClusterPlateau_eq_one
    {center δ x : ℝ} (hδ : 0 < δ)
    (hx : |x - center| < δ) :
    spectralClusterPlateau center δ x = 1 := by
  unfold spectralClusterPlateau
  have hratio : 1 ≤ (2 * δ - |x - center|) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  rw [min_eq_left hratio]
  simp

theorem spectralClusterPlateau_eq_zero
    {center δ x : ℝ} (hδ : 0 < δ)
    (hx : 2 * δ ≤ |x - center|) :
    spectralClusterPlateau center δ x = 0 := by
  unfold spectralClusterPlateau
  rw [max_eq_left]
  exact
    (min_le_right 1 ((2 * δ - |x - center|) / δ)).trans
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)

theorem spectralClusterPlateau_atomic
    (center : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    spectralClusterPlateau center δ center = 1 := by
  apply spectralClusterPlateau_eq_one hδ
  simpa using hδ

/-- A real spectrum lies in the disjoint inner cluster neighborhoods
labelled by `energy`. -/
def SpectrallyClusteredAround
    {n : ℕ} (energy : Fin n → ℝ) (δ : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x ∈ spectrum ℝ A, ∃ k, |x - energy k| < δ

/-- Separation by `4δ` makes every point in one inner cluster lie outside
the outer support of every other plateau. -/
theorem spectralClusterPlateau_eq_zero_of_other_cluster
    {n : ℕ} {energy : Fin n → ℝ} {δ x : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j|)
    {i j : Fin n} (hij : i ≠ j)
    (hx : |x - energy i| < δ) :
    spectralClusterPlateau (energy j) δ x = 0 := by
  apply spectralClusterPlateau_eq_zero hδ
  have htriangle :
      |energy i - energy j| ≤
        |energy i - x| + |x - energy j| := by
    exact abs_sub_le (energy i) x (energy j)
  have hleft : |energy i - x| = |x - energy i| := abs_sub_comm _ _
  rw [hleft] at htriangle
  have hlarge := hsep i j hij
  linarith

/-- Plateau functional-calculus projection associated with one labelled
spectral cluster. -/
def spectralClusterProjection
    {n : ℕ} (energy : Fin n → ℝ) (δ : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  cfc (spectralClusterPlateau (energy k) δ) A

/-- On a separated clustered spectrum, the plateau projections resolve the
identity exactly. -/
theorem spectralClusterProjection_sum_eq_one
    {n : ℕ} {energy : Fin n → ℝ} {δ : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j|)
    (hcluster : SpectrallyClusteredAround energy δ A) :
    ∑ k, spectralClusterProjection energy δ A k = 1 := by
  have hfunctions :
      (spectrum ℝ A).EqOn
        (fun x => ∑ k, spectralClusterPlateau (energy k) δ x)
        (fun _ => 1) := by
    intro x hx
    obtain ⟨i, hi⟩ := hcluster x hx
    change (∑ k, spectralClusterPlateau (energy k) δ x) = 1
    rw [Finset.sum_eq_single i]
    · exact spectralClusterPlateau_eq_one hδ hi
    · intro j _hj hji
      exact spectralClusterPlateau_eq_zero_of_other_cluster
        hδ hsep hji.symm hi
    · intro hiuniv
      exact (hiuniv (Finset.mem_univ i)).elim
  have hcfc :
      cfc (fun x => ∑ k, spectralClusterPlateau (energy k) δ x) A =
        cfc (fun _ : ℝ => 1) A :=
    cfc_congr hfunctions
  have hsumfun :
      (fun x => ∑ k, spectralClusterPlateau (energy k) δ x) =
        ∑ k, spectralClusterPlateau (energy k) δ := by
    funext x
    simp
  rw [hsumfun,
    cfc_sum_univ
      (fun k => spectralClusterPlateau (energy k) δ) A
      (fun k =>
        (continuous_spectralClusterPlateau (energy k) δ).continuousOn)]
      at hcfc
  have hone : cfc (fun _ : ℝ => 1) A = 1 :=
    cfc_const_one ℝ A hA
  rw [hone] at hcfc
  simpa [spectralClusterProjection] using hcfc

/-- Each plateau projection is idempotent because its defining plateau is
zero or one on the clustered spectrum. -/
theorem spectralClusterProjection_mul_self
    {n : ℕ} {energy : Fin n → ℝ} {δ : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j|)
    (hcluster : SpectrallyClusteredAround energy δ A)
    (k : Fin n) :
    spectralClusterProjection energy δ A k *
        spectralClusterProjection energy δ A k =
      spectralClusterProjection energy δ A k := by
  let f := spectralClusterPlateau (energy k) δ
  have hsq :
      (spectrum ℝ A).EqOn (fun x => f x * f x) f := by
    intro x hx
    obtain ⟨i, hi⟩ := hcluster x hx
    change f x * f x = f x
    by_cases hik : i = k
    · subst k
      have hone : f x = 1 := spectralClusterPlateau_eq_one hδ hi
      rw [hone]
      simp
    · have hzero :=
        spectralClusterPlateau_eq_zero_of_other_cluster
          hδ hsep hik hi
      have hzero' : f x = 0 := hzero
      rw [hzero']
      simp
  have hcfc : cfc (fun x => f x * f x) A = cfc f A :=
    cfc_congr hsq
  have hf :
      ContinuousOn f (spectrum ℝ A) :=
    (continuous_spectralClusterPlateau (energy k) δ).continuousOn
  rw [cfc_mul f f A hf hf] at hcfc
  simpa [spectralClusterProjection, f] using hcfc

/-- Every plateau projection commutes with every function of the same
Hermitian matrix, in particular with its Schrödinger evolution. -/
theorem spectralClusterProjection_commute_exp
    {n : ℕ} {energy : Fin n → ℝ} {δ t : ℝ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (k : Fin n) :
    Commute (spectralClusterProjection energy δ A k)
      (exp ((-(Complex.I * (t : ℂ))) • A)) := by
  apply hA.isSelfAdjoint.commute_cfc
  exact
    (((Commute.refl A).smul_right
      (-(Complex.I * (t : ℂ)))).exp_right)

/-! ## Algebraic all-time transition bound -/

/-- Entrywise mixing budget of a labelled family of projections.  It
vanishes off diagonal for the coordinate projections. -/
def spectralProjectionMixingBudget
    {n : ℕ} (P : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (j i : Fin n) : ℝ :=
  ∑ k, ∑ b, ∑ a, ‖P k j a‖ * ‖P k b i‖

/-- A complete family of idempotents commuting with `U` gives an exact
block decomposition of `U`. -/
theorem matrix_eq_sum_projection_mul_self
    {n : ℕ} (P : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hsum : ∑ k, P k = 1)
    (hidempotent : ∀ k, P k * P k = P k)
    (hcommute : ∀ k, Commute (P k) U) :
    U = ∑ k, P k * U * P k := by
  symm
  calc
    (∑ k, P k * U * P k) =
        ∑ k, (P k * P k) * U := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [mul_assoc, ← (hcommute k).eq, ← mul_assoc]
    _ = ∑ k, P k * U := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [hidempotent k]
    _ = (∑ k, P k) * U := by
      rw [Finset.sum_mul]
    _ = U := by
      rw [hsum, one_mul]

/-- If every entry of `U` has modulus at most one, the off-diagonal entry
of a projection block is bounded by the corresponding projection mixing
budget. -/
theorem norm_sum_projection_mul_self_apply_le
    {n : ℕ} (P : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ a b, ‖U a b‖ ≤ 1)
    (j i : Fin n) :
    ‖((∑ k, P k * U * P k :
        Matrix (Fin n) (Fin n) ℂ)) j i‖ ≤
      spectralProjectionMixingBudget P j i := by
  rw [spectralProjectionMixingBudget]
  let S : Matrix (Fin n) (Fin n) ℂ :=
    ∑ k, P k * U * P k
  have hS : S j i = ∑ k, (P k * U * P k) j i := by
    change (Matrix.entryAddMonoidHom ℂ j i) S =
      ∑ k, (Matrix.entryAddMonoidHom ℂ j i) (P k * U * P k)
    rw [show S = ∑ k, P k * U * P k by rfl, map_sum]
  change ‖S j i‖ ≤ _
  rw [hS]
  calc
    ‖∑ k, (P k * U * P k) j i‖ ≤
        ∑ k, ‖(P k * U * P k) j i‖ :=
      norm_sum_le Finset.univ _
    _ ≤ ∑ k, ∑ b, ∑ a, ‖P k j a‖ * ‖P k b i‖ := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [Matrix.mul_apply]
      calc
        ‖∑ b, (P k * U) j b * P k b i‖ ≤
            ∑ b, ‖(P k * U) j b * P k b i‖ :=
          norm_sum_le Finset.univ _
        _ ≤ ∑ b, ∑ a, ‖P k j a‖ * ‖P k b i‖ := by
          apply Finset.sum_le_sum
          intro b _hb
          rw [Matrix.mul_apply]
          calc
            ‖(∑ a, P k j a * U a b) * P k b i‖ =
                ‖∑ a, P k j a * U a b‖ * ‖P k b i‖ := by
              rw [norm_mul]
            _ ≤ (∑ a, ‖P k j a * U a b‖) * ‖P k b i‖ := by
              gcongr
              exact norm_sum_le Finset.univ _
            _ = ∑ a, ‖P k j a * U a b‖ * ‖P k b i‖ := by
              rw [Finset.sum_mul]
            _ ≤ ∑ a, ‖P k j a‖ * ‖P k b i‖ := by
              apply Finset.sum_le_sum
              intro a _ha
              rw [norm_mul]
              have hnonneg : 0 ≤ ‖P k j a‖ := norm_nonneg _
              have hnonneg' : 0 ≤ ‖P k b i‖ := norm_nonneg _
              calc
                ‖P k j a‖ * ‖U a b‖ * ‖P k b i‖ ≤
                    ‖P k j a‖ * 1 * ‖P k b i‖ := by
                  gcongr
                  exact hU a b
                _ = ‖P k j a‖ * ‖P k b i‖ := by ring

/-- Uniform transition suppression follows from a time-independent
projection mixing budget. -/
theorem norm_apply_lt_of_projection_mixingBudget_lt
    {n : ℕ} (P : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hsum : ∑ k, P k = 1)
    (hidempotent : ∀ k, P k * P k = P k)
    (hcommute : ∀ k, Commute (P k) U)
    (hU : ∀ a b, ‖U a b‖ ≤ 1)
    {j i : Fin n} {ε : ℝ}
    (hmixing : spectralProjectionMixingBudget P j i < ε) :
    ‖U j i‖ < ε := by
  rw [matrix_eq_sum_projection_mul_self P U hsum hidempotent hcommute]
  exact
    (norm_sum_projection_mul_self_apply_le P U hU j i).trans_lt
      hmixing

/-! ## Atomic projectors and continuity -/

open Polynomial

/-- Evaluating a real polynomial on a complex diagonal matrix acts
entrywise on its real diagonal. -/
theorem aeval_realPolynomial_diagonal
    {n : ℕ} (q : ℝ[X]) (energy : Fin n → ℝ) :
    aeval (Matrix.diagonal (fun i => (energy i : ℂ))) q =
      Matrix.diagonal
        (fun i => ((q.eval (energy i) : ℝ) : ℂ)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
  | monomial n a =>
      simp only [aeval_def, eval₂_monomial]
      rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_pow,
        Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]

/-- Lagrange polynomial selecting one coordinate of an injective real
energy packet. -/
def coordinateLagrangePolynomial
    {n : ℕ} (energy : Fin n → ℝ) (k : Fin n) : ℝ[X] :=
  ∏ j ∈ Finset.univ.erase k,
    C ((energy k - energy j)⁻¹) * (X - C (energy j))

theorem coordinateLagrangePolynomial_eval
    {n : ℕ} {energy : Fin n → ℝ}
    (hinjective : Function.Injective energy)
    (k i : Fin n) :
    (coordinateLagrangePolynomial energy k).eval (energy i) =
      if i = k then 1 else 0 := by
  by_cases hik : i = k
  · subst i
    rw [if_pos rfl, coordinateLagrangePolynomial, eval_prod]
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_erase] at hj
    rw [eval_mul, eval_C, eval_sub, eval_X, eval_C]
    have hne : energy k - energy j ≠ 0 :=
      sub_ne_zero.mpr (hinjective.ne hj.1.symm)
    field_simp
  · rw [if_neg hik, coordinateLagrangePolynomial, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)
    simp

/-- Real spectrum of a real diagonal complex matrix is exactly its
diagonal packet, independent of the canonical eigenvalue ordering. -/
theorem spectrum_real_diagonal_ofReal
    {n : ℕ} (energy : Fin n → ℝ) :
    spectrum ℝ (Matrix.diagonal (fun i => (energy i : ℂ))) =
      Set.range energy := by
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => (energy i : ℂ))
  have hD : D.IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    rw [isSelfAdjoint_iff]
    simp
  have hcomplex :
      (RCLike.ofReal '' Set.range hD.eigenvalues : Set ℂ) =
        Set.range (fun i => (energy i : ℂ)) := by
    rw [← hD.spectrum_eq_image_range]
    exact spectrum_diagonal (fun i => (energy i : ℂ))
  rw [show Matrix.diagonal (fun i => (energy i : ℂ)) = D by rfl,
    hD.spectrum_real_eq_range_eigenvalues]
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    have hx :
        (RCLike.ofReal (hD.eigenvalues i) : ℂ) ∈
          (RCLike.ofReal '' Set.range hD.eigenvalues : Set ℂ) :=
      ⟨hD.eigenvalues i, ⟨i, rfl⟩, rfl⟩
    rw [hcomplex] at hx
    obtain ⟨j, hj⟩ := hx
    exact
      ⟨j, Complex.ofReal_injective
        (by simpa using hj)⟩
  · rintro ⟨i, rfl⟩
    have hx :
        (RCLike.ofReal (energy i) : ℂ) ∈
          (RCLike.ofReal '' Set.range hD.eigenvalues : Set ℂ) := by
      rw [hcomplex]
      exact ⟨i, rfl⟩
    obtain ⟨x, ⟨j, rfl⟩, hx⟩ := hx
    exact
      ⟨j, Complex.ofReal_injective
        (by simpa using hx)⟩

/-- At the atomic diagonal point, the labelled cluster projection is the
corresponding coordinate projection. -/
theorem spectralClusterProjection_diagonal
    {n : ℕ} {energy : Fin n → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j|)
    (k : Fin n) :
    spectralClusterProjection energy δ
        (Matrix.diagonal (fun i => (energy i : ℂ))) k =
      Matrix.diagonal (fun i => if i = k then (1 : ℂ) else 0) := by
  have hinjective : Function.Injective energy := by
    intro i j hij
    by_contra hne
    have hlarge := hsep i j hne
    rw [hij, sub_self, abs_zero] at hlarge
    linarith
  let q := coordinateLagrangePolynomial energy k
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => (energy i : ℂ))
  have hfunctions :
      (spectrum ℝ D).EqOn
        (spectralClusterPlateau (energy k) δ) q.eval := by
    intro x hx
    obtain ⟨i, rfl⟩ :
        ∃ i, x = energy i := by
      rw [show D = Matrix.diagonal
        (fun i => (energy i : ℂ)) by rfl,
        spectrum_real_diagonal_ofReal] at hx
      obtain ⟨i, hi⟩ := hx
      exact ⟨i, hi.symm⟩
    change spectralClusterPlateau (energy k) δ (energy i) =
      q.eval (energy i)
    rw [show q.eval (energy i) =
      if i = k then 1 else 0 by
        exact coordinateLagrangePolynomial_eval hinjective k i]
    by_cases hik : i = k
    · subst k
      rw [if_pos rfl]
      exact spectralClusterPlateau_atomic (energy i) hδ
    · rw [if_neg hik]
      apply spectralClusterPlateau_eq_zero hδ
      have hlarge := hsep i k hik
      have habs : |energy i - energy k| = |energy k - energy i| :=
        abs_sub_comm _ _
      rw [habs]
      linarith
  have hcfc :
      cfc (spectralClusterPlateau (energy k) δ) D =
        cfc q.eval D :=
    cfc_congr hfunctions
  have hD : D.IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    rw [isSelfAdjoint_iff]
    simp
  have hpoly :
      cfc (fun x => q.eval x) D = aeval D q :=
    cfc_polynomial q D hD
  rw [hpoly] at hcfc
  rw [aeval_realPolynomial_diagonal q energy] at hcfc
  rw [spectralClusterProjection]
  change cfc (spectralClusterPlateau (energy k) δ) D = _
  rw [hcfc]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [q, coordinateLagrangePolynomial_eval hinjective]
    · simp [q, coordinateLagrangePolynomial_eval hinjective, hik]
  · simp [hij]

/-- The projection mixing budget vanishes between distinct sites at the
atomic diagonal point. -/
theorem spectralProjectionMixingBudget_diagonal_eq_zero
    {n : ℕ} {energy : Fin n → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j|)
    {j i : Fin n} (hji : j ≠ i) :
    spectralProjectionMixingBudget
        (fun k => spectralClusterProjection energy δ
          (Matrix.diagonal (fun a => (energy a : ℂ))) k)
        j i = 0 := by
  simp only [spectralProjectionMixingBudget,
    spectralClusterProjection_diagonal hδ hsep]
  apply Finset.sum_eq_zero
  intro k _hk
  by_cases hkj : k = j
  · subst k
    apply Finset.sum_eq_zero
    intro b _hb
    apply Finset.sum_eq_zero
    intro a _ha
    apply mul_eq_zero_of_right
    rw [Matrix.diagonal_apply]
    by_cases hbi : b = i
    · subst b
      simp [hji.symm]
    · simp [hbi]
  · apply Finset.sum_eq_zero
    intro b _hb
    apply Finset.sum_eq_zero
    intro a _ha
    apply mul_eq_zero_of_left
    rw [Matrix.diagonal_apply]
    by_cases hja : j = a
    · subst a
      simp [Ne.symm hkj]
    · simp [hja]

/-- Continuous Hermitian families have continuous labelled cluster
projections. -/
theorem continuousAt_spectralClusterProjection
    {X : Type*} [TopologicalSpace X]
    {n : ℕ} [Nonempty (Fin n)]
    {energy : Fin n → ℝ} {δ : ℝ}
    {A : X → Matrix (Fin n) (Fin n) ℂ} {x₀ : X}
    (hAcont : ContinuousAt A x₀)
    (hHermitian : ∀ x, (A x).IsHermitian)
    (k : Fin n) :
    ContinuousAt
      (fun x => spectralClusterProjection energy δ (A x) k) x₀ := by
  let M : ℝ := ‖A x₀‖ + 1
  have hnorm :
      ∀ᶠ x in 𝓝 x₀, ‖A x‖ < M := by
    exact hAcont.norm (Iio_mem_nhds (by simp [M]))
  have hspectrum :
      ∀ᶠ x in 𝓝 x₀, spectrum ℝ (A x) ⊆ Set.Icc (-M) M := by
    filter_upwards [hnorm] with x hx y hy
    have habs : |y| ≤ ‖A x‖ := by
      simpa [Real.norm_eq_abs] using
        spectrum.norm_le_norm_of_mem hy
    exact ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  exact
    hAcont.cfc isCompact_Icc
      (spectralClusterPlateau (energy k) δ)
      hspectrum
      (Filter.Eventually.of_forall fun x => (hHermitian x).isSelfAdjoint)
      (continuous_spectralClusterPlateau (energy k) δ).continuousOn

/-- The finite projection mixing budget is continuous along every
continuous Hermitian family. -/
theorem continuousAt_spectralProjectionMixingBudget
    {X : Type*} [TopologicalSpace X]
    {n : ℕ} [Nonempty (Fin n)]
    {energy : Fin n → ℝ} {δ : ℝ}
    {A : X → Matrix (Fin n) (Fin n) ℂ} {x₀ : X}
    (hAcont : ContinuousAt A x₀)
    (hHermitian : ∀ x, (A x).IsHermitian)
    (j i : Fin n) :
    ContinuousAt
      (fun x => spectralProjectionMixingBudget
        (fun k => spectralClusterProjection energy δ (A x) k) j i)
      x₀ := by
  have hprojection (k : Fin n) :
      ContinuousAt
        (fun x => spectralClusterProjection energy δ (A x) k) x₀ :=
    continuousAt_spectralClusterProjection hAcont hHermitian k
  have hentry (k a b : Fin n) :
      ContinuousAt
        (fun x => spectralClusterProjection energy δ (A x) k a b) x₀ := by
    let row :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → ℂ) :=
      ContinuousLinearMap.proj a
    let col : (Fin n → ℂ) →L[ℂ] ℂ :=
      ContinuousLinearMap.proj b
    let entry :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
      col.comp row
    exact entry.continuous.continuousAt.comp (hprojection k)
  unfold spectralProjectionMixingBudget
  fun_prop

/-- Every continuous matrix family through a real diagonal point remains
spectrally clustered around that diagonal packet in a neighborhood. -/
theorem eventually_spectrallyClusteredAround_diagonal
    {X : Type*} [TopologicalSpace X]
    {n : ℕ} {energy : Fin n → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    {A : X → Matrix (Fin n) (Fin n) ℂ} {x₀ : X}
    (hAcont : ContinuousAt A x₀)
    (hA0 :
      A x₀ = Matrix.diagonal (fun i => (energy i : ℂ))) :
    ∀ᶠ x in 𝓝 x₀, SpectrallyClusteredAround energy δ (A x) := by
  let U : Set ℝ := ⋃ k, Metric.ball (energy k) δ
  have hUopen : IsOpen U := isOpen_iUnion fun _ => Metric.isOpen_ball
  have hDsubset :
      spectrum ℝ (Matrix.diagonal (fun i => (energy i : ℂ))) ⊆ U := by
    rw [spectrum_real_diagonal_ofReal]
    rintro x ⟨i, rfl⟩
    exact Set.mem_iUnion.2
      ⟨i, by simpa [Real.dist_eq] using hδ⟩
  have hUnhds :
      U ∈ 𝓝ˢ
        (spectrum ℝ
          (Matrix.diagonal (fun i => (energy i : ℂ)))) :=
    hUopen.mem_nhdsSet.mpr hDsubset
  have hmatrix :
      ∀ᶠ B in 𝓝
          (Matrix.diagonal (fun i => (energy i : ℂ))),
        spectrum ℝ B ⊆ U :=
    (upperHemicontinuous_spectrum ℝ
      (Matrix (Fin n) (Fin n) ℂ)).upperHemicontinuousAt
        (Matrix.diagonal (fun i => (energy i : ℂ))) U hUnhds
      |>.mono fun _ h => subset_of_mem_nhdsSet h
  have hpull :
      ∀ᶠ x in 𝓝 x₀, spectrum ℝ (A x) ⊆ U := by
    have htendsto :
        Tendsto A (𝓝 x₀)
          (𝓝 (Matrix.diagonal (fun i => (energy i : ℂ)))) := by
      rw [← hA0]
      exact hAcont
    exact htendsto.eventually hmatrix
  filter_upwards [hpull] with x hx y hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hx hy)
  exact ⟨k, by simpa [Real.dist_eq] using hk⟩

/-- Near a separated atomic point, all distinct-site projection mixing
budgets are simultaneously smaller than any positive tolerance. -/
theorem eventually_all_spectralProjectionMixingBudget_lt
    {X : Type*} [TopologicalSpace X]
    {n : ℕ} [Nonempty (Fin n)]
    {energy : Fin n → ℝ} {δ ε : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i j, i ≠ j → 4 * δ ≤ |energy i - energy j|)
    (hε : 0 < ε)
    {A : X → Matrix (Fin n) (Fin n) ℂ} {x₀ : X}
    (hAcont : ContinuousAt A x₀)
    (hHermitian : ∀ x, (A x).IsHermitian)
    (hA0 :
      A x₀ = Matrix.diagonal (fun i => (energy i : ℂ))) :
    ∀ᶠ x in 𝓝 x₀,
      SpectrallyClusteredAround energy δ (A x) ∧
      ∀ j i, j ≠ i →
        spectralProjectionMixingBudget
          (fun k => spectralClusterProjection energy δ (A x) k)
          j i < ε := by
  have hcluster :=
    eventually_spectrallyClusteredAround_diagonal hδ hAcont hA0
  have hbudget :
      ∀ᶠ x in 𝓝 x₀, ∀ j i, j ≠ i →
        spectralProjectionMixingBudget
          (fun k => spectralClusterProjection energy δ (A x) k)
          j i < ε := by
    have hall :
        ∀ᶠ x in 𝓝 x₀,
          ∀ j ∈ Finset.univ, ∀ i ∈ Finset.univ, j ≠ i →
            spectralProjectionMixingBudget
              (fun k => spectralClusterProjection energy δ (A x) k)
              j i < ε := by
      apply (eventually_all_finset Finset.univ).2
      intro j _hj
      apply (eventually_all_finset Finset.univ).2
      intro i _hi
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall fun _ hne => (hne hji).elim
      · have hcont :=
          continuousAt_spectralProjectionMixingBudget
            (energy := energy) (δ := δ)
            hAcont hHermitian j i
        have hev :
            ∀ᶠ x in 𝓝 x₀,
              spectralProjectionMixingBudget
                (fun k => spectralClusterProjection energy δ (A x) k)
                j i < ε := by
          have hbase :
              spectralProjectionMixingBudget
                (fun k => spectralClusterProjection energy δ (A x₀) k)
                j i < ε := by
            rw [hA0,
              spectralProjectionMixingBudget_diagonal_eq_zero
                hδ hsep hji]
            exact hε
          exact hcont (Iio_mem_nhds hbase)
        exact hev.mono fun _ hx _ => hx
    simpa using hall
  exact hcluster.and hbudget

end

end GaloisForLFunctions.HTGeometry
