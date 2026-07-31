import GaloisForLFunctions.U0.HolomorphicIFT
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Matrix.Normed

/-!
# Holomorphic scalar branches over finite-dimensional parameter spaces

This module extends the existing scalar-parameter holomorphic implicit-function theorem to an
arbitrary complete complex Banach parameter space. The result is the analytic branch engine needed
for eigenvalues of Hamiltonians with one independent coupling per interaction edge.
-/

open Filter Topology Complex ContinuousLinearMap Set
open scoped ContDiff
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

/-- Holomorphic implicit function theorem with an arbitrary complete complex Banach parameter
space and a scalar root variable. -/
theorem parametric_holo_implicit
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    {f : P × ℂ → ℂ} {p₀ : P} {w₀ : ℂ}
    (hf : AnalyticAt ℂ f (p₀, w₀)) (h0 : f (p₀, w₀) = 0)
    (hfw : (fderiv ℂ f (p₀, w₀)) (0, 1) ≠ 0) :
    ∃ r : P → ℂ, AnalyticAt ℂ r p₀ ∧ r p₀ = w₀ ∧
      (∀ᶠ p in 𝓝 p₀, f (p, r p) = 0) := by
  have cdf : ContDiffAt ℂ ω f (p₀, w₀) := hf.contDiffAt
  have if₂ : (fderiv ℂ f (p₀, w₀) ∘L (.inr ℂ P ℂ)).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne (by simpa using hfw)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  refine ⟨cdf.implicitFunction hω if₂,
    (cdf.contDiffAt_implicitFunction hω if₂).analyticAt, ?_, ?_⟩
  · exact cdf.implicitFunction_apply_self hω if₂
  · filter_upwards [cdf.eventually_apply_implicitFunction hω if₂] with p hp
    rw [hp, h0]

/-- The parametric holomorphic branch is the unique continuous local branch through the simple
root. Uniqueness is at the level of germs, which is the form needed to compare branches after
restricting couplings or splitting a Hamiltonian into disconnected components. -/
theorem parametric_holo_implicit_unique
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    {f : P × ℂ → ℂ} {p₀ : P} {w₀ : ℂ}
    (hf : AnalyticAt ℂ f (p₀, w₀)) (h0 : f (p₀, w₀) = 0)
    (hfw : (fderiv ℂ f (p₀, w₀)) (0, 1) ≠ 0) :
    ∃ r : P → ℂ, AnalyticAt ℂ r p₀ ∧ r p₀ = w₀ ∧
      (∀ᶠ p in 𝓝 p₀, f (p, r p) = 0) ∧
      ∀ s : P → ℂ, ContinuousAt s p₀ → s p₀ = w₀ →
        (∀ᶠ p in 𝓝 p₀, f (p, s p) = 0) → r =ᶠ[𝓝 p₀] s := by
  have cdf : ContDiffAt ℂ ω f (p₀, w₀) := hf.contDiffAt
  have if₂ : (fderiv ℂ f (p₀, w₀) ∘L (.inr ℂ P ℂ)).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne (by simpa using hfw)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  let r : P → ℂ := cdf.implicitFunction hω if₂
  refine ⟨r, (cdf.contDiffAt_implicitFunction hω if₂).analyticAt,
    cdf.implicitFunction_apply_self hω if₂, ?_, ?_⟩
  · filter_upwards [cdf.eventually_apply_implicitFunction hω if₂] with p hp
    rw [hp, h0]
  · intro s hs hs0 hseq
    have hpair :
        Tendsto (fun p : P => (p, s p)) (𝓝 p₀) (𝓝 (p₀, w₀)) := by
      have hpcont := continuousAt_id.prodMk hs
      change Tendsto (fun p : P => (p, s p)) (𝓝 p₀) (𝓝 (p₀, s p₀)) at hpcont
      simpa [hs0] using hpcont
    have hiff :
        ∀ᶠ p in 𝓝 p₀,
          f (p, s p) = f (p₀, w₀) ↔ r p = s p :=
      hpair.eventually (cdf.eventually_apply_eq_iff_implicitFunction hω if₂)
    filter_upwards [hseq, hiff] with p hp hpi
    exact hpi.mp (by simpa [h0] using hp)

/-! ## Analytic branches of simple diagonal matrix eigenvalues -/

open Matrix Polynomial
open scoped Kronecker BigOperators

/-- Determinants preserve analyticity of a finite matrix-valued family. -/
theorem analyticAt_matrix_det_parametric
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Fintype ι] [DecidableEq ι]
    {M : P → Matrix ι ι ℂ} {p₀ : P}
    (hM : ∀ i j, AnalyticAt ℂ (fun p => M p i j) p₀) :
    AnalyticAt ℂ (fun p => (M p).det) p₀ := by
  have heq : (fun p => (M p).det)
      = fun p => ∑ σ : Equiv.Perm ι,
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M p (σ i) i := by
    funext p
    rw [Matrix.det_apply]
    exact Finset.sum_congr rfl
      (fun σ _ => by rw [Units.smul_def, zsmul_eq_mul])
  rw [heq]
  exact Finset.analyticAt_fun_sum _
    (fun σ _ => analyticAt_const.mul
      (Finset.analyticAt_fun_prod _ (fun i _ => hM (σ i) i)))

/-- Characteristic determinant with the matrix and spectral value both treated as parameters. -/
def matrixCharpolyRelation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : Matrix ι ι ℂ × ℂ) : ℂ :=
  (Matrix.scalar ι q.2 - q.1).det

theorem matrixCharpolyRelation_analyticAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q₀ : Matrix ι ι ℂ × ℂ) :
    AnalyticAt ℂ (matrixCharpolyRelation (ι := ι)) q₀ := by
  apply analyticAt_matrix_det_parametric
  intro i j
  have hentry :
      AnalyticAt ℂ (fun q : Matrix ι ι ℂ × ℂ => q.1 i j) q₀ := by
    let row : Matrix ι ι ℂ →L[ℂ] (ι → ℂ) :=
      ContinuousLinearMap.proj (R := ℂ) i
    let col : (ι → ℂ) →L[ℂ] ℂ :=
      ContinuousLinearMap.proj (R := ℂ) j
    let entry : Matrix ι ι ℂ →L[ℂ] ℂ := col.comp row
    exact (entry.analyticAt q₀.1).comp analyticAt_fst
  by_cases hij : i = j
  · subst j
    simpa [matrixCharpolyRelation, Matrix.scalar_apply] using!
      analyticAt_snd.sub hentry
  · have hneg :
        AnalyticAt ℂ (fun q : Matrix ι ι ℂ × ℂ => -q.1 i j) q₀ :=
      hentry.neg
    convert hneg using 1
    funext q
    simp [Matrix.scalar_apply, hij]

/-- The pure spectral-value derivative of the characteristic determinant is the derivative of the
characteristic polynomial. -/
theorem matrixCharpolyRelation_partial_w
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (w : ℂ) :
    (fderiv ℂ (matrixCharpolyRelation (ι := ι)) (H, w)) (0, 1) =
      (derivative H.charpoly).eval w := by
  let f := matrixCharpolyRelation (ι := ι)
  have hfdiff : HasFDerivAt f (fderiv ℂ f (H, w)) (H, w) :=
    (matrixCharpolyRelation_analyticAt (H, w)).differentiableAt.hasFDerivAt
  have hι : HasFDerivAt (fun z : ℂ => (H, z))
      ((0 : ℂ →L[ℂ] Matrix ι ι ℂ).prod
        (ContinuousLinearMap.id ℂ ℂ)) w :=
    (hasFDerivAt_const H w).prodMk (hasFDerivAt_id w)
  have hcomp : HasFDerivAt (fun z => f (H, z))
      ((fderiv ℂ f (H, w)).comp
        ((0 : ℂ →L[ℂ] Matrix ι ι ℂ).prod
          (ContinuousLinearMap.id ℂ ℂ))) w :=
    hfdiff.comp w hι
  have hpoly :
      HasDerivAt (fun z => f (H, z))
        ((derivative H.charpoly).eval w) w := by
    have heq : (fun z => f (H, z)) =
        fun z => H.charpoly.eval z := by
      funext z
      exact (Matrix.eval_charpoly H z).symm
    rw [heq]
    exact Polynomial.hasDerivAt H.charpoly w
  have huniq := hcomp.unique hpoly.hasFDerivAt
  have hev := ContinuousLinearMap.ext_iff.mp huniq 1
  simpa [f] using hev

/-- Each diagonal entry is a root of the corresponding characteristic relation. -/
theorem matrixCharpolyRelation_diagonal_root
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (x : ι) :
    matrixCharpolyRelation (Matrix.diagonal energy, energy x) = 0 := by
  unfold matrixCharpolyRelation
  rw [← Matrix.eval_charpoly, Matrix.charpoly_diagonal, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ x)
  simp

/-- Pairwise-distinct diagonal energies make every diagonal root simple in the spectral
variable. -/
theorem matrixCharpolyRelation_diagonal_partial_w_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy) (x : ι) :
    (fderiv ℂ (matrixCharpolyRelation (ι := ι))
      (Matrix.diagonal energy, energy x)) (0, 1) ≠ 0 := by
  have hsep :
      (∏ i, (X - C (energy i)) : ℂ[X]).Separable :=
    Polynomial.separable_prod_X_sub_C_iff.mpr hinj
  have heval :
      (∏ i, (X - C (energy i)) : ℂ[X]).eval (energy x) = 0 := by
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ x)
    simp
  have hderiv :
      (derivative (Matrix.diagonal energy).charpoly).eval (energy x) ≠ 0 := by
    rw [Matrix.charpoly_diagonal]
    have hne := hsep.eval₂_derivative_ne_zero
      (RingHom.id ℂ) (by simpa using heval)
    simpa using hne
  exact (matrixCharpolyRelation_partial_w
    (Matrix.diagonal energy) (energy x)).symm ▸ hderiv

/-- Every eigenvalue of a diagonal matrix with pairwise-distinct entries has a locally analytic
branch under arbitrary complex matrix perturbations. -/
theorem simpleDiagonalMatrix_eigenvalueBranch
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy) (x : ι) :
    ∃ branch : Matrix ι ι ℂ → ℂ,
      AnalyticAt ℂ branch (Matrix.diagonal energy) ∧
      branch (Matrix.diagonal energy) = energy x ∧
      (∀ᶠ H in 𝓝 (Matrix.diagonal energy),
        (matrixCharpolyRelation (H, branch H) = 0)) := by
  have hanalytic :
      AnalyticAt ℂ (matrixCharpolyRelation (ι := ι))
        (Matrix.diagonal energy, energy x) :=
    matrixCharpolyRelation_analyticAt _
  exact parametric_holo_implicit hanalytic
    (matrixCharpolyRelation_diagonal_root energy x)
    (matrixCharpolyRelation_diagonal_partial_w_ne energy hinj x)

/-- Two continuous characteristic roots converging to the same simple diagonal eigenvalue define
the same germ. The matrix family itself need only converge; no differentiability is required. -/
theorem simpleDiagonalMatrix_root_germs_unique
    {P ι : Type*} [TopologicalSpace P]
    [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy) (x : ι)
    {p₀ : P} {H : P → Matrix ι ι ℂ} {s t : P → ℂ}
    (hH : Tendsto H (𝓝 p₀) (𝓝 (Matrix.diagonal energy)))
    (hs : Tendsto s (𝓝 p₀) (𝓝 (energy x)))
    (ht : Tendsto t (𝓝 p₀) (𝓝 (energy x)))
    (hsroot : ∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, s p) = 0)
    (htroot : ∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, t p) = 0) :
    s =ᶠ[𝓝 p₀] t := by
  let f := matrixCharpolyRelation (ι := ι)
  have cdf : ContDiffAt ℂ ω f (Matrix.diagonal energy, energy x) :=
    (matrixCharpolyRelation_analyticAt _).contDiffAt
  have if₂ :
      (fderiv ℂ f (Matrix.diagonal energy, energy x) ∘L
        (.inr ℂ (Matrix ι ι ℂ) ℂ)).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne
      (by simpa [f] using
        matrixCharpolyRelation_diagonal_partial_w_ne energy hinj x)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  let r : Matrix ι ι ℂ → ℂ := cdf.implicitFunction hω if₂
  have hpairS :
      Tendsto (fun p => (H p, s p)) (𝓝 p₀)
        (𝓝 (Matrix.diagonal energy, energy x)) := by
    simpa only [nhds_prod_eq] using hH.prodMk hs
  have hpairT :
      Tendsto (fun p => (H p, t p)) (𝓝 p₀)
        (𝓝 (Matrix.diagonal energy, energy x)) := by
    simpa only [nhds_prod_eq] using hH.prodMk ht
  have hiffS :
      ∀ᶠ p in 𝓝 p₀, f (H p, s p) = 0 ↔ r (H p) = s p := by
    have hpull := hpairS.eventually
      (cdf.eventually_apply_eq_iff_implicitFunction hω if₂)
    simpa [f, matrixCharpolyRelation_diagonal_root energy x] using hpull
  have hiffT :
      ∀ᶠ p in 𝓝 p₀, f (H p, t p) = 0 ↔ r (H p) = t p := by
    have hpull := hpairT.eventually
      (cdf.eventually_apply_eq_iff_implicitFunction hω if₂)
    simpa [f, matrixCharpolyRelation_diagonal_root energy x] using hpull
  filter_upwards [hsroot, htroot, hiffS, hiffT] with p hsr htr his hit
  exact (his.mp hsr).symm.trans (hit.mp htr)

/-- Pulling the universal simple-eigenvalue branch back along an analytic matrix family gives an
analytic characteristic-root branch for that family. -/
theorem analyticMatrixFamily_eigenvalueBranch
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Fintype ι] [DecidableEq ι]
    {H : P → Matrix ι ι ℂ} {p₀ : P}
    (hH : AnalyticAt ℂ H p₀)
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (hbase : H p₀ = Matrix.diagonal energy) (x : ι) :
    ∃ branch : P → ℂ,
      AnalyticAt ℂ branch p₀ ∧ branch p₀ = energy x ∧
      (∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, branch p) = 0) := by
  obtain ⟨r, hr, hr0, hrroot⟩ :=
    simpleDiagonalMatrix_eigenvalueBranch energy hinj x
  have hHt :
      Tendsto H (𝓝 p₀) (𝓝 (Matrix.diagonal energy)) := by
    have hcont := hH.continuousAt
    change Tendsto H (𝓝 p₀) (𝓝 (H p₀)) at hcont
    simpa only [hbase] using! hcont
  refine ⟨fun p => r (H p), hr.fun_comp_of_eq hH hbase, ?_, ?_⟩
  · simpa [hbase] using hr0
  · exact hHt.eventually hrroot

/-! ## Disconnected spectra add exactly -/

/-- Tensor product of two coordinate vectors. -/
def tensorVec {R ι κ : Type*} [Mul R] (v : ι → R) (w : κ → R) : ι × κ → R :=
  fun p => v p.1 * w p.2

/-- A Kronecker product acts componentwise on a tensor-product vector. -/
theorem kronecker_mulVec_tensorVec
    {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (B : Matrix κ κ R)
    (v : ι → R) (w : κ → R) :
    (A ⊗ₖ B) *ᵥ tensorVec v w =
      tensorVec (A *ᵥ v) (B *ᵥ w) := by
  ext p
  rcases p with ⟨i, j⟩
  simp only [mulVec, dotProduct, tensorVec]
  change (∑ x : ι × κ, (A i x.1 * B j x.2) * (v x.1 * w x.2)) =
    (∑ x : ι, A i x * v x) * ∑ x : κ, B j x * w x
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i' hi'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j' hj'
  ring

/-- A tensor product of nonzero vectors over a domain is nonzero. -/
theorem tensorVec_ne_zero
    {R ι κ : Type*} [CommRing R] [NoZeroDivisors R]
    {v : ι → R} {w : κ → R} (hv : v ≠ 0) (hw : w ≠ 0) :
    tensorVec v w ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by simpa [Function.ne_iff] using hv
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by simpa [Function.ne_iff] using hw
  have hp := congr_fun h (i, j)
  exact mul_ne_zero hi hj (by simpa [tensorVec] using hp)

/-- Matrix Kronecker sum, representing two dynamically disconnected components. -/
def kroneckerSum
    {R ι κ : Type*} [CommRing R] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι R) (B : Matrix κ κ R) :
    Matrix (ι × κ) (ι × κ) R :=
  A ⊗ₖ (1 : Matrix κ κ R) + (1 : Matrix ι ι R) ⊗ₖ B

/-- The Kronecker sum of diagonal matrices adds their diagonal energies. -/
theorem kroneckerSum_diagonal
    {R ι κ : Type*} [CommRing R] [DecidableEq ι] [DecidableEq κ]
    (ea : ι → R) (eb : κ → R) :
    kroneckerSum (Matrix.diagonal ea) (Matrix.diagonal eb) =
      Matrix.diagonal (fun p : ι × κ => ea p.1 + eb p.2) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases hij : i = j <;> by_cases hkl : k = l
  · subst j
    subst l
    simp [kroneckerSum]
  · subst j
    simp [kroneckerSum, hkl]
  · subst l
    simp [kroneckerSum, hij]
  · simp [kroneckerSum, hij, hkl]

/-- Kronecker sums preserve analyticity of finite matrix families. -/
theorem analyticAt_kroneckerSum
    {P ι κ : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : P → Matrix ι ι ℂ} {B : P → Matrix κ κ ℂ} {p₀ : P}
    (hA : AnalyticAt ℂ A p₀) (hB : AnalyticAt ℂ B p₀) :
    AnalyticAt ℂ (fun p => kroneckerSum (A p) (B p)) p₀ := by
  apply AnalyticAt.pi
  intro ik
  apply AnalyticAt.pi
  intro jl
  rcases ik with ⟨i, k⟩
  rcases jl with ⟨j, l⟩
  have hAij : AnalyticAt ℂ (fun p => A p i j) p₀ :=
    analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hA i) j
  have hBkl : AnalyticAt ℂ (fun p => B p k l) p₀ :=
    analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hB k) l
  by_cases hij : i = j <;> by_cases hkl : k = l
  · subst j
    subst l
    simpa [kroneckerSum] using! hAij.add hBkl
  · subst j
    simpa [kroneckerSum, hkl] using hBkl
  · subst l
    simpa [kroneckerSum, hij] using hAij
  · simpa [kroneckerSum, hij, hkl] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : P => (0 : ℂ)) p₀)

/-- Eigenvalues of dynamically disconnected components add. This is an exact root theorem over
every commutative domain, without diagonalizability or self-adjointness assumptions. -/
theorem charpoly_eval_kroneckerSum_eq_zero
    {R ι κ : Type*} [CommRing R] [IsDomain R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι R) (B : Matrix κ κ R)
    {a b : R} (ha : A.charpoly.eval a = 0)
    (hb : B.charpoly.eval b = 0) :
    (kroneckerSum A B).charpoly.eval (a + b) = 0 := by
  have hda : (Matrix.scalar ι a - A).det = 0 := by
    simpa [Matrix.eval_charpoly] using ha
  have hdb : (Matrix.scalar κ b - B).det = 0 := by
    simpa [Matrix.eval_charpoly] using hb
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hda
  obtain ⟨w, hw, hBw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdb
  rw [Matrix.eval_charpoly]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨tensorVec v w, tensorVec_ne_zero hv hw, ?_⟩
  ext p
  rcases p with ⟨i, j⟩
  have hAvi := congr_fun hAv i
  have hBwj := congr_fun hBw j
  simp only [sub_mulVec, Pi.sub_apply, Pi.zero_apply] at hAvi hBwj
  have hscalarA : ((Matrix.scalar ι a) *ᵥ v) i = a * v i := by
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hscalarB : ((Matrix.scalar κ b) *ᵥ w) j = b * w j := by
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [hscalarA] at hAvi
  rw [hscalarB] at hBwj
  have hAv' : (A *ᵥ v) i = a * v i := (sub_eq_zero.mp hAvi).symm
  have hBw' : (B *ᵥ w) j = b * w j := (sub_eq_zero.mp hBwj).symm
  simp only [kroneckerSum, sub_mulVec, add_mulVec,
    kronecker_mulVec_tensorVec, Pi.sub_apply, Pi.add_apply, tensorVec,
    one_mulVec, Pi.zero_apply]
  have hscalar :
      ((Matrix.scalar (ι × κ) (a + b)) *ᵥ tensorVec v w) (i, j) =
        (a + b) * tensorVec v w (i, j) := by
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [hscalar, hAv', hBw']
  simp [tensorVec]
  ring

/-- **Disconnected analytic branches add as germs.** For any two analytic finite matrix families,
if the uncoupled product energies are simple, then the simple branch of their Kronecker sum is
exactly the sum of the two component branches near the base point. This is the spectral
additivity input behind connected-cluster cancellation. -/
theorem disconnectedAnalyticEigenvalueBranches_add
    {P ι κ : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : P → Matrix ι ι ℂ} {B : P → Matrix κ κ ℂ} {p₀ : P}
    (hA : AnalyticAt ℂ A p₀) (hB : AnalyticAt ℂ B p₀)
    (ea : ι → ℂ) (eb : κ → ℂ)
    (hAbase : A p₀ = Matrix.diagonal ea)
    (hBbase : B p₀ = Matrix.diagonal eb)
    (hcombined : Function.Injective (fun p : ι × κ => ea p.1 + eb p.2))
    (x : ι) (y : κ) :
    ∃ aBranch bBranch totalBranch : P → ℂ,
      AnalyticAt ℂ aBranch p₀ ∧
      AnalyticAt ℂ bBranch p₀ ∧
      AnalyticAt ℂ totalBranch p₀ ∧
      aBranch p₀ = ea x ∧
      bBranch p₀ = eb y ∧
      totalBranch p₀ = ea x + eb y ∧
      (∀ᶠ p in 𝓝 p₀,
        matrixCharpolyRelation (A p, aBranch p) = 0) ∧
      (∀ᶠ p in 𝓝 p₀,
        matrixCharpolyRelation (B p, bBranch p) = 0) ∧
      (∀ᶠ p in 𝓝 p₀,
        matrixCharpolyRelation
          (kroneckerSum (A p) (B p), totalBranch p) = 0) ∧
      totalBranch =ᶠ[𝓝 p₀] fun p => aBranch p + bBranch p := by
  have hinjA : Function.Injective ea := by
    intro i j hij
    have hp := hcombined (a₁ := (i, y)) (a₂ := (j, y))
    exact congrArg Prod.fst (hp (by simp [hij]))
  have hinjB : Function.Injective eb := by
    intro i j hij
    have hp := hcombined (a₁ := (x, i)) (a₂ := (x, j))
    exact congrArg Prod.snd (hp (by simp [hij]))
  obtain ⟨aBranch, ha, ha0, haroot⟩ :=
    analyticMatrixFamily_eigenvalueBranch hA ea hinjA hAbase x
  obtain ⟨bBranch, hb, hb0, hbroot⟩ :=
    analyticMatrixFamily_eigenvalueBranch hB eb hinjB hBbase y
  let totalEnergy : ι × κ → ℂ := fun p => ea p.1 + eb p.2
  let totalMatrix : P → Matrix (ι × κ) (ι × κ) ℂ :=
    fun p => kroneckerSum (A p) (B p)
  have htotal : AnalyticAt ℂ totalMatrix p₀ :=
    analyticAt_kroneckerSum hA hB
  have htotalBase :
      totalMatrix p₀ = Matrix.diagonal totalEnergy := by
    dsimp only [totalMatrix, totalEnergy]
    rw [hAbase, hBbase, kroneckerSum_diagonal]
  obtain ⟨totalBranch, htotalBranch, htotal0, htotalRoot⟩ :=
    analyticMatrixFamily_eigenvalueBranch htotal totalEnergy hcombined
      htotalBase (x, y)
  have hsumRoot :
      ∀ᶠ p in 𝓝 p₀,
        matrixCharpolyRelation
          (totalMatrix p, aBranch p + bBranch p) = 0 := by
    filter_upwards [haroot, hbroot] with p hap hbp
    have haeval : (A p).charpoly.eval (aBranch p) = 0 := by
      rw [Matrix.eval_charpoly]
      exact hap
    have hbeval : (B p).charpoly.eval (bBranch p) = 0 := by
      rw [Matrix.eval_charpoly]
      exact hbp
    unfold matrixCharpolyRelation
    rw [← Matrix.eval_charpoly]
    exact charpoly_eval_kroneckerSum_eq_zero (A p) (B p) haeval hbeval
  have htotalTendsto :
      Tendsto totalMatrix (𝓝 p₀) (𝓝 (Matrix.diagonal totalEnergy)) := by
    have hcont := htotal.continuousAt
    change Tendsto totalMatrix (𝓝 p₀) (𝓝 (totalMatrix p₀)) at hcont
    simpa only [htotalBase] using! hcont
  have hbranchTendsto :
      Tendsto totalBranch (𝓝 p₀) (𝓝 (totalEnergy (x, y))) := by
    have hcont := htotalBranch.continuousAt
    change Tendsto totalBranch (𝓝 p₀) (𝓝 (totalBranch p₀)) at hcont
    simpa only [htotal0] using hcont
  have hsumTendsto :
      Tendsto (fun p => aBranch p + bBranch p) (𝓝 p₀)
        (𝓝 (totalEnergy (x, y))) := by
    have hadd := ha.continuousAt.add hb.continuousAt
    change Tendsto (fun p => aBranch p + bBranch p) (𝓝 p₀)
      (𝓝 (aBranch p₀ + bBranch p₀)) at hadd
    simpa only [ha0, hb0, totalEnergy] using hadd
  have hadditive :
      totalBranch =ᶠ[𝓝 p₀] fun p => aBranch p + bBranch p :=
    simpleDiagonalMatrix_root_germs_unique totalEnergy hcombined (x, y)
      htotalTendsto hbranchTendsto hsumTendsto htotalRoot hsumRoot
  exact ⟨aBranch, bBranch, totalBranch, ha, hb, htotalBranch,
    ha0, hb0, htotal0, haroot, hbroot, htotalRoot, hadditive⟩

end GaloisForLFunctions.HTGeometry
