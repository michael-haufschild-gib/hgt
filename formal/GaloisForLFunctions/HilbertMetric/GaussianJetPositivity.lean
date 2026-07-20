import GaloisForLFunctions.HilbertMetric.CCRDimensionFluctuation
import GaloisForLFunctions.HilbertMetric.CentroidGauge
import GaloisForLFunctions.HilbertMetric.DeterminantCurvatureJet
import GaloisForLFunctions.HilbertMetric.GaussianFock
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Gaussian first-jet positivity

This module develops the matrix prerequisite for the coherent-state realization of finite
Gaussian Gram determinants.  It first records that positive semidefiniteness is closed under
entrywise matrix limits, and upgrades the existing ordered-tensor Fock approximation from a
determinant statement to literal positive semidefiniteness of the exponential inner-product
kernel.

The final section constructs the joint Gram matrix of coherent vectors and their first coordinate
jets as a limit of finite-difference Gaussian Gram matrices.  This gives the unconditional
positive-semidefinite Schur complement needed to manufacture the finite rectangular CCR leakage
blocks; no positivity certificate is assumed.
-/

open Filter
open scoped BigOperators Matrix MatrixOrder RealInnerProductSpace

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Positive semidefiniteness of finite real matrices is closed under matrix convergence. -/
theorem Matrix.PosSemidef.of_tendsto {α n : Type*} [Fintype n]
    {l : Filter α} [l.NeBot] {A : α → Matrix n n ℝ} {M : Matrix n n ℝ}
    (hA : ∀ᶠ a in l, (A a).PosSemidef) (hlim : Tendsto A l (nhds M)) :
    M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian]
    have hc : Continuous (fun N : Matrix n n ℝ => N.conjTranspose) := by fun_prop
    have hleft : Tendsto (fun a => (A a).conjTranspose) l
        (nhds M.conjTranspose) := hc.continuousAt.tendsto.comp hlim
    have hright : Tendsto (fun a => (A a).conjTranspose) l (nhds M) := by
      apply hlim.congr'
      filter_upwards [hA] with a ha
      exact ha.isHermitian.eq.symm
    exact tendsto_nhds_unique hleft hright
  · intro x
    have hc : Continuous (fun N : Matrix n n ℝ =>
        dotProduct (star x) (N.mulVec x)) := by fun_prop
    have hq := hc.continuousAt.tendsto.comp hlim
    apply isClosed_Ici.mem_of_tendsto hq
    filter_upwards [hA] with a ha
    exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp ha).2 x

/-- Every ordinary finite Euclidean feature Gram matrix is positive semidefinite. -/
theorem standardFeatureGram_posSemidef {n : ℕ} {κ : Type*} [Fintype κ]
    (evaluation : Fin n → κ → ℝ) :
    (standardFeatureGram evaluation).PosSemidef := by
  let A : Matrix (Fin n) κ ℝ := fun i k => evaluation i k
  have hA : standardFeatureGram evaluation = A * A.conjTranspose := by
    ext i j
    simp [standardFeatureGram, A, Matrix.mul_apply]
  rw [hA]
  exact Matrix.posSemidef_self_mul_conjTranspose A

/-- Every ordered-tensor Taylor truncation of the exponential inner-product kernel is positive
semidefinite. -/
theorem truncatedExponentialInnerMatrix_posSemidef {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (truncatedExponentialInnerMatrix y m t).PosSemidef := by
  rw [← orderedTensorFockGram_sqrt_eq_truncatedExponentialInnerMatrix y m t ht]
  exact standardFeatureGram_posSemidef _

/-- The full Euclidean exponential inner-product matrix is positive semidefinite. -/
theorem coordinateExponentialInnerMatrix_posSemidef {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (coordinateExponentialInnerMatrix y t).PosSemidef := by
  apply Matrix.PosSemidef.of_tendsto (α := ℕ) (n := Fin n) (l := atTop)
    (M := coordinateExponentialInnerMatrix y t)
  · exact Filter.Eventually.of_forall fun m =>
      truncatedExponentialInnerMatrix_posSemidef y m t ht
  · exact tendsto_truncatedExponentialInnerMatrix y t

/-- Positive semidefiniteness of the exponential inner-product kernel for a finite family in a
finite-dimensional real Hilbert space. -/
theorem hilbertExponentialInnerMatrix_fin_posSemidef_of_finiteDimensional
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x : Fin n → E) (t : ℝ) (ht : 0 ≤ t) :
    (hilbertExponentialInnerMatrix x t).PosSemidef := by
  rw [← coordinateExponentialInnerMatrix_orthonormalCoordinates x t]
  exact coordinateExponentialInnerMatrix_posSemidef _ t ht

/-- Positive semidefiniteness of the exponential inner-product kernel for a finite Hilbert family,
with no finite-dimensional ambient-space assumption. -/
theorem hilbertExponentialInnerMatrix_fin_posSemidef
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : Fin n → E) (t : ℝ) (ht : 0 ≤ t) :
    (hilbertExponentialInnerMatrix x t).PosSemidef := by
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range x)
  letI : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range x)
  let xs : Fin n → S := fun i =>
    ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩
  have h := hilbertExponentialInnerMatrix_fin_posSemidef_of_finiteDimensional xs t ht
  simpa [hilbertExponentialInnerMatrix, xs] using h

/-- Universal positive semidefiniteness of the exponential inner-product kernel on a finite real
Hilbert configuration. -/
theorem hilbertExponentialInnerMatrix_posSemidef
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ι → E) (t : ℝ) (ht : 0 ≤ t) :
    (hilbertExponentialInnerMatrix x t).PosSemidef := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let xf : Fin (Fintype.card ι) → E := fun k => x (e.symm k)
  have h := hilbertExponentialInnerMatrix_fin_posSemidef xf t ht
  have hs := h.submatrix (fun i : ι => e i)
  convert hs using 1
  ext i j
  simp [hilbertExponentialInnerMatrix, Matrix.submatrix, xf, e]

/-! ### Finite differences and the coherent first-jet matrix -/

/-- Labels for the original coherent vectors and for one first jet in every coordinate. -/
abbrev gaussianFirstJetIndex (n d : ℕ) := Fin n ⊕ (Fin d × Fin n)

/-- The point family containing each original point and each one-coordinate perturbation. -/
def gaussianJetPerturbedPoint {n d : ℕ} (y : Fin n → Fin d → ℝ) (h : ℝ) :
    gaussianFirstJetIndex n d → EuclideanSpace ℝ (Fin d)
  | Sum.inl p => WithLp.toLp 2 (y p)
  | Sum.inr ip => WithLp.toLp 2 fun k => y ip.2 k + if k = ip.1 then h else 0

/-- Sparse row operation turning perturbed kernel sections into first difference quotients. -/
def gaussianJetDifferenceTransform (n d : ℕ) (h : ℝ) :
    Matrix (gaussianFirstJetIndex n d) (gaussianFirstJetIndex n d) ℝ
  | Sum.inl p, q => if q = Sum.inl p then 1 else 0
  | Sum.inr ip, q =>
      ((if q = Sum.inr ip then 1 else 0) -
        if q = Sum.inl ip.2 then 1 else 0) / h

/-- Gram matrix of coherent sections and their coordinate finite differences. -/
def gaussianJetFiniteDifferenceGram {n d : ℕ} (y : Fin n → Fin d → ℝ) (h : ℝ) :
    Matrix (gaussianFirstJetIndex n d) (gaussianFirstJetIndex n d) ℝ :=
  let C := gaussianJetDifferenceTransform n d h
  let K := hilbertExponentialInnerMatrix (gaussianJetPerturbedPoint y h) (1 / 2)
  C * K * C.conjTranspose

/-- Exact joint Gram matrix of coherent vectors and their first coordinate jets. -/
def gaussianCoherentFirstJetMatrix {n d : ℕ} (y : Fin n → Fin d → ℝ) :
    Matrix (gaussianFirstJetIndex n d) (gaussianFirstJetIndex n d) ℝ
  | Sum.inl p, Sum.inl q => Real.exp (coordinateDot y p q)
  | Sum.inl p, Sum.inr jq =>
      y p jq.1 * Real.exp (coordinateDot y p jq.2)
  | Sum.inr ip, Sum.inl q =>
      y q ip.1 * Real.exp (coordinateDot y ip.2 q)
  | Sum.inr ip, Sum.inr jq =>
      ((if ip.1 = jq.1 then 1 else 0) + y ip.2 jq.1 * y jq.2 ip.1) *
        Real.exp (coordinateDot y ip.2 jq.2)

/-- Every finite-difference coherent first-jet Gram matrix is positive semidefinite. -/
theorem gaussianJetFiniteDifferenceGram_posSemidef {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (h : ℝ) :
    (gaussianJetFiniteDifferenceGram y h).PosSemidef := by
  unfold gaussianJetFiniteDifferenceGram
  exact (hilbertExponentialInnerMatrix_posSemidef
    (gaussianJetPerturbedPoint y h) (1 / 2) (by norm_num)).mul_mul_conjTranspose_same _

/-- The base--base block is unchanged by the finite-difference row operation. -/
theorem gaussianJetFiniteDifferenceGram_base_base {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (h : ℝ) (p q : Fin n) :
    gaussianJetFiniteDifferenceGram y h (Sum.inl p) (Sum.inl q) =
      Real.exp (coordinateDot y p q) := by
  unfold gaussianJetFiniteDifferenceGram gaussianJetDifferenceTransform
    hilbertExponentialInnerMatrix gaussianJetPerturbedPoint coordinateDot
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_id_of_comm]
  simp [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A base--jet entry is the first exponential difference quotient. -/
theorem gaussianJetFiniteDifferenceGram_base_jet {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (h : ℝ)
    (p q : Fin n) (j : Fin d) :
    gaussianJetFiniteDifferenceGram y h (Sum.inl p) (Sum.inr (j, q)) =
      Real.exp (coordinateDot y p q) *
        (Real.exp (h * y p j) - 1) / h := by
  unfold gaussianJetFiniteDifferenceGram gaussianJetDifferenceTransform
    hilbertExponentialInnerMatrix gaussianJetPerturbedPoint coordinateDot
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_id_of_comm]
  simp [PiLp.inner_apply, div_eq_mul_inv]
  have hdot : (∑ x, y q x * y p x) = coordinateDot y p q := by
    unfold coordinateDot
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpert : (∑ x, (y q x + if x = j then h else 0) * y p x) =
      coordinateDot y p q + h * y p j := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, hdot]
    simp
  have hdot' : (∑ x, y p x * y q x) = coordinateDot y p q := rfl
  rw [hdot, hpert, hdot', Real.exp_add]
  ring

/-- A jet--base entry is the transposed first exponential difference quotient. -/
theorem gaussianJetFiniteDifferenceGram_jet_base {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (h : ℝ)
    (p q : Fin n) (i : Fin d) :
    gaussianJetFiniteDifferenceGram y h (Sum.inr (i, p)) (Sum.inl q) =
      Real.exp (coordinateDot y p q) *
        (Real.exp (h * y q i) - 1) / h := by
  have hsymm := (gaussianJetFiniteDifferenceGram_posSemidef y h).isHermitian.apply
    (Sum.inr (i, p)) (Sum.inl q)
  simp only [star_id_of_comm] at hsymm
  rw [← hsymm, gaussianJetFiniteDifferenceGram_base_jet]
  have hdot : coordinateDot y q p = coordinateDot y p q := by
    unfold coordinateDot
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hdot]

/-- A jet--jet entry is the mixed second exponential difference quotient. -/
theorem gaussianJetFiniteDifferenceGram_jet_jet {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (h : ℝ)
    (p q : Fin n) (i j : Fin d) :
    gaussianJetFiniteDifferenceGram y h (Sum.inr (i, p)) (Sum.inr (j, q)) =
      Real.exp (coordinateDot y p q) *
        (Real.exp (h * (y p j + y q i) + h ^ 2 * (if i = j then 1 else 0)) -
            Real.exp (h * y q i) - Real.exp (h * y p j) + 1) / h ^ 2 := by
  unfold gaussianJetFiniteDifferenceGram gaussianJetDifferenceTransform
    hilbertExponentialInnerMatrix gaussianJetPerturbedPoint coordinateDot
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_id_of_comm]
  simp [PiLp.inner_apply, div_eq_mul_inv]
  have hdot : (∑ x, y q x * y p x) = coordinateDot y p q := by
    unfold coordinateDot
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hdot' : (∑ x, y p x * y q x) = coordinateDot y p q := rfl
  have hleft : (∑ x, (y q x + if x = j then h else 0) * y p x) =
      coordinateDot y p q + h * y p j := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, hdot]
    simp
  have hright : (∑ x, y q x * (y p x + if x = i then h else 0)) =
      coordinateDot y p q + h * y q i := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hdot]
    simp
    ring
  have hboth :
      (∑ x, (y q x + if x = j then h else 0) *
        (y p x + if x = i then h else 0)) =
        coordinateDot y p q + h * (y p j + y q i) +
          h ^ 2 * (if i = j then 1 else 0) := by
    simp_rw [add_mul, mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hdot]
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
      ring
  rw [hdot, hdot', hleft, hright, hboth]
  simp_rw [Real.exp_add]
  by_cases hij : i = j
  · subst j
    simp
    ring
  · simp [hij]
    ring

/-- The elementary exponential first difference quotient converges to its linear coefficient. -/
theorem tendsto_exp_mul_sub_one_div (a : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (h * a) - 1) / h)
      (nhdsWithin 0 {0}ᶜ) (nhds a) := by
  have hlinear : HasDerivAt (fun h : ℝ => h * a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const a
  have hexp : HasDerivAt (fun h : ℝ => Real.exp (h * a)) a 0 := by
    simpa using (Real.hasDerivAt_exp (0 * a)).comp 0 hlinear
  have hslope := hexp.tendsto_slope_zero
  convert hslope using 1
  funext h
  simp [div_eq_mul_inv]
  ring

/-- Squaring the increment preserves the exponential first-slope limit. -/
theorem tendsto_exp_sq_mul_sub_one_div (c : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (h ^ 2 * c) - 1) / h ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds c) := by
  have hsquare : Tendsto (fun h : ℝ => h ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun h : ℝ => h) (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
        tendsto_id.mono_left inf_le_left
      simpa using hid.pow 2
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hh ⊢
      exact pow_ne_zero 2 hh
  exact (tendsto_exp_mul_sub_one_div c).comp hsquare

/-- Universal mixed exponential quotient.  The limit splits into a product of first jets plus
the diagonal second-jet coefficient. -/
theorem tendsto_mixed_exp_difference_quotient (a b c : ℝ) :
    Tendsto (fun h : ℝ =>
        (Real.exp (h * (a + b) + h ^ 2 * c) -
            Real.exp (h * b) - Real.exp (h * a) + 1) / h ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (a * b + c)) := by
  let A : ℝ → ℝ := fun h => (Real.exp (h * a) - 1) / h
  let B : ℝ → ℝ := fun h => (Real.exp (h * b) - 1) / h
  let C : ℝ → ℝ := fun h => (Real.exp (h ^ 2 * c) - 1) / h ^ 2
  let E : ℝ → ℝ := fun h => Real.exp (h * (a + b))
  have hA : Tendsto A (nhdsWithin 0 {0}ᶜ) (nhds a) :=
    tendsto_exp_mul_sub_one_div a
  have hB : Tendsto B (nhdsWithin 0 {0}ᶜ) (nhds b) :=
    tendsto_exp_mul_sub_one_div b
  have hC : Tendsto C (nhdsWithin 0 {0}ᶜ) (nhds c) :=
    tendsto_exp_sq_mul_sub_one_div c
  have hE : Tendsto E (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have hzero : Tendsto (fun h : ℝ => h * (a + b))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have hid : Tendsto (fun h : ℝ => h) (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
        tendsto_id.mono_left inf_le_left
      simpa using hid.mul_const (a + b)
    simpa [E] using (Real.continuous_exp.tendsto 0).comp hzero
  have hsum := hA.mul hB |>.add (hE.mul hC)
  have hsum' : Tendsto (fun h => A h * B h + E h * C h)
      (nhdsWithin 0 {0}ᶜ) (nhds (a * b + c)) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  dsimp [A, B, C, E]
  rw [show h * (a + b) = h * a + h * b by ring, Real.exp_add]
  rw [Real.exp_add, Real.exp_add]
  field_simp [hh]
  ring

/-- Finite-difference coherent Gram matrices converge entrywise to the exact coherent first-jet
matrix. -/
theorem tendsto_gaussianJetFiniteDifferenceGram {n d : ℕ}
    (y : Fin n → Fin d → ℝ) :
    Tendsto (fun h : ℝ => gaussianJetFiniteDifferenceGram y h)
      (nhdsWithin 0 {0}ᶜ) (nhds (gaussianCoherentFirstJetMatrix y)) := by
  apply tendsto_pi_nhds.2
  intro r
  apply tendsto_pi_nhds.2
  intro s
  rcases r with p | ⟨i, p⟩
  · rcases s with q | ⟨j, q⟩
    · apply tendsto_const_nhds.congr'
      exact Filter.Eventually.of_forall fun h =>
        (gaussianJetFiniteDifferenceGram_base_base y h p q).symm
    · have hc : Tendsto (fun _ : ℝ => Real.exp (coordinateDot y p q))
          (nhdsWithin 0 {0}ᶜ) (nhds (Real.exp (coordinateDot y p q))) :=
        tendsto_const_nhds
      have hlim := hc.mul (tendsto_exp_mul_sub_one_div (y p j))
      have heq : (fun h : ℝ => Real.exp (coordinateDot y p q) *
            ((Real.exp (h * y p j) - 1) / h)) =ᶠ[nhdsWithin 0 {0}ᶜ]
          (fun h => gaussianJetFiniteDifferenceGram y h
            (Sum.inl p) (Sum.inr (j, q))) := by
        exact Filter.Eventually.of_forall fun h => by
          change Real.exp (coordinateDot y p q) *
              ((Real.exp (h * y p j) - 1) / h) =
            gaussianJetFiniteDifferenceGram y h (Sum.inl p) (Sum.inr (j, q))
          rw [gaussianJetFiniteDifferenceGram_base_jet]
          ring
      have hconv := hlim.congr' heq
      convert hconv using 1
      simp only [gaussianCoherentFirstJetMatrix]
      ring
  · rcases s with q | ⟨j, q⟩
    · have hc : Tendsto (fun _ : ℝ => Real.exp (coordinateDot y p q))
          (nhdsWithin 0 {0}ᶜ) (nhds (Real.exp (coordinateDot y p q))) :=
        tendsto_const_nhds
      have hlim := hc.mul (tendsto_exp_mul_sub_one_div (y q i))
      have heq : (fun h : ℝ => Real.exp (coordinateDot y p q) *
            ((Real.exp (h * y q i) - 1) / h)) =ᶠ[nhdsWithin 0 {0}ᶜ]
          (fun h => gaussianJetFiniteDifferenceGram y h
            (Sum.inr (i, p)) (Sum.inl q)) := by
        exact Filter.Eventually.of_forall fun h => by
          change Real.exp (coordinateDot y p q) *
              ((Real.exp (h * y q i) - 1) / h) =
            gaussianJetFiniteDifferenceGram y h (Sum.inr (i, p)) (Sum.inl q)
          rw [gaussianJetFiniteDifferenceGram_jet_base]
          ring
      have hconv := hlim.congr' heq
      convert hconv using 1
      simp only [gaussianCoherentFirstJetMatrix]
      ring
    · have hquot := tendsto_mixed_exp_difference_quotient
        (y p j) (y q i) (if i = j then 1 else 0)
      have hc : Tendsto (fun _ : ℝ => Real.exp (coordinateDot y p q))
          (nhdsWithin 0 {0}ᶜ) (nhds (Real.exp (coordinateDot y p q))) :=
        tendsto_const_nhds
      have hlim := hc.mul hquot
      have heq : (fun h : ℝ => Real.exp (coordinateDot y p q) *
            ((Real.exp (h * (y p j + y q i) + h ^ 2 * (if i = j then 1 else 0)) -
                Real.exp (h * y q i) - Real.exp (h * y p j) + 1) / h ^ 2))
          =ᶠ[nhdsWithin 0 {0}ᶜ]
            (fun h => gaussianJetFiniteDifferenceGram y h
              (Sum.inr (i, p)) (Sum.inr (j, q))) := by
        exact Filter.Eventually.of_forall fun h => by
          change Real.exp (coordinateDot y p q) *
              ((Real.exp (h * (y p j + y q i) + h ^ 2 * (if i = j then 1 else 0)) -
                  Real.exp (h * y q i) - Real.exp (h * y p j) + 1) / h ^ 2) =
            gaussianJetFiniteDifferenceGram y h
              (Sum.inr (i, p)) (Sum.inr (j, q))
          rw [gaussianJetFiniteDifferenceGram_jet_jet]
          ring
      have hconv := hlim.congr' heq
      convert hconv using 1
      simp only [gaussianCoherentFirstJetMatrix]
      ring

/-- **Gaussian coherent first-jet positivity.**  The joint Gram matrix of every finite Euclidean
coherent family and all of its first coordinate jets is positive semidefinite. -/
theorem gaussianCoherentFirstJetMatrix_posSemidef {n d : ℕ}
    (y : Fin n → Fin d → ℝ) :
    (gaussianCoherentFirstJetMatrix y).PosSemidef := by
  apply Matrix.PosSemidef.of_tendsto
    (α := ℝ) (n := gaussianFirstJetIndex n d) (l := nhdsWithin 0 {0}ᶜ)
  · exact Filter.Eventually.of_forall fun h =>
      gaussianJetFiniteDifferenceGram_posSemidef y h
  · exact tendsto_gaussianJetFiniteDifferenceGram y

/-! ### The intrinsic coherent Schur complement -/

/-- Gram matrix of the unnormalized coherent vectors attached to a Euclidean configuration. -/
def gaussianCoherentGram {n d : ℕ} (y : Fin n → Fin d → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun p q => Real.exp (coordinateDot y p q)

/-- Cross Gram matrix between coherent vectors and their first coordinate jets. -/
def gaussianCoherentCrossJet {n d : ℕ} (y : Fin n → Fin d → ℝ) :
    Matrix (Fin n) (Fin d × Fin n) ℝ :=
  fun p jq => y p jq.1 * Real.exp (coordinateDot y p jq.2)

/-- Gram matrix of all first coordinate jets. -/
def gaussianCoherentJetBlock {n d : ℕ} (y : Fin n → Fin d → ℝ) :
    Matrix (Fin d × Fin n) (Fin d × Fin n) ℝ :=
  fun ip jq =>
    ((if ip.1 = jq.1 then 1 else 0) + y ip.2 jq.1 * y jq.2 ip.1) *
      Real.exp (coordinateDot y ip.2 jq.2)

/-- The coherent first-jet matrix is literally the block matrix built from its value, cross, and
jet Gram blocks. -/
theorem gaussianCoherentFirstJetMatrix_eq_fromBlocks {n d : ℕ}
    (y : Fin n → Fin d → ℝ) :
    gaussianCoherentFirstJetMatrix y =
      Matrix.fromBlocks (gaussianCoherentGram y) (gaussianCoherentCrossJet y)
        (gaussianCoherentCrossJet y).conjTranspose (gaussianCoherentJetBlock y) := by
  ext r s
  rcases r with p | ⟨i, p⟩ <;> rcases s with q | ⟨j, q⟩
  · rfl
  · rfl
  · simp only [gaussianCoherentFirstJetMatrix, Matrix.fromBlocks_apply₂₁,
      Matrix.conjTranspose_apply, star_id_of_comm, gaussianCoherentCrossJet]
    congr 2
    unfold coordinateDot
    apply Finset.sum_congr rfl
    intro k _
    ring
  · rfl

/-- The residual first-jet Gram matrix after orthogonal projection onto the coherent span. -/
def gaussianCoherentJetSchurComplement {n d : ℕ}
    (y : Fin n → Fin d → ℝ) :
    Matrix (Fin d × Fin n) (Fin d × Fin n) ℝ :=
  gaussianCoherentJetBlock y -
    (gaussianCoherentCrossJet y).conjTranspose *
      (gaussianCoherentGram y)⁻¹ * gaussianCoherentCrossJet y

/-- Once the coherent vectors are independent, the intrinsic residual first-jet Gram matrix is
positive semidefinite. -/
theorem gaussianCoherentJetSchurComplement_posSemidef {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    (gaussianCoherentJetSchurComplement y).PosSemidef := by
  letI : Invertible (gaussianCoherentGram y) :=
    Matrix.invertibleOfIsUnitDet _
      ((gaussianCoherentGram y).isUnit_iff_isUnit_det.mp hG.isUnit)
  apply (Matrix.PosDef.fromBlocks₁₁
    (gaussianCoherentCrossJet y) (gaussianCoherentJetBlock y) hG).mp
  rw [← gaussianCoherentFirstJetMatrix_eq_fromBlocks]
  exact gaussianCoherentFirstJetMatrix_posSemidef y

/-! ### Orthonormal coherent compression and its CCR defect -/

/-- Positive square root of the coherent Gram matrix. -/
def gaussianCoherentSqrt {n d : ℕ} (y : Fin n → Fin d → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt (gaussianCoherentGram y)

/-- Diagonal joint-eigenvalue matrix for one Euclidean coordinate. -/
def gaussianCoordinateDiagonal {n d : ℕ} (y : Fin n → Fin d → ℝ) (i : Fin d) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun p => y p i

/-- Annihilation compression in orthonormal coordinates on the coherent span. -/
def gaussianCoherentCompression {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (i : Fin d) : Matrix (Fin n) (Fin n) ℝ :=
  gaussianCoherentSqrt y * gaussianCoordinateDiagonal y i * (gaussianCoherentSqrt y)⁻¹

/-- Mode-block lifting of one matrix to a matrix on `mode × coherent-label`. -/
def gaussianModeBlockDiagonal {n d : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin d × Fin n) (Fin d × Fin n) ℝ :=
  fun ip jq => if ip.1 = jq.1 then R ip.2 jq.2 else 0

/-- Block matrix of the canonical CCR defects of the coherent compressions. -/
def gaussianCoherentCCRDefect {n d : ℕ} (y : Fin n → Fin d → ℝ) :
    Matrix (Fin d × Fin n) (Fin d × Fin n) ℝ :=
  fun ip jq =>
    ((if ip.1 = jq.1 then 1 else 0) +
      (gaussianCoherentCompression y jq.1).transpose *
        gaussianCoherentCompression y ip.1 -
      gaussianCoherentCompression y ip.1 *
        (gaussianCoherentCompression y jq.1).transpose) ip.2 jq.2

theorem gaussianCoherentGram_transpose {n d : ℕ} (y : Fin n → Fin d → ℝ) :
    (gaussianCoherentGram y).transpose = gaussianCoherentGram y := by
  ext p q
  simp only [Matrix.transpose_apply, gaussianCoherentGram]
  congr 1
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem gaussianCoordinateDiagonal_transpose {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (i : Fin d) :
    (gaussianCoordinateDiagonal y i).transpose = gaussianCoordinateDiagonal y i := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [gaussianCoordinateDiagonal]
  · simp [gaussianCoordinateDiagonal, hpq, Ne.symm hpq]

theorem gaussianCoordinateDiagonal_commutes {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (i j : Fin d) :
    gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j =
      gaussianCoordinateDiagonal y j * gaussianCoordinateDiagonal y i := by
  unfold gaussianCoordinateDiagonal
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  ring

theorem gaussianCoherentSqrt_mul_self {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    gaussianCoherentSqrt y * gaussianCoherentSqrt y = gaussianCoherentGram y := by
  exact CFC.sqrt_mul_sqrt_self _ hG.posSemidef.nonneg

theorem gaussianCoherentSqrt_transpose {n d : ℕ}
    (y : Fin n → Fin d → ℝ) :
    (gaussianCoherentSqrt y).transpose = gaussianCoherentSqrt y := by
  have hstar := (CFC.sqrt_nonneg (gaussianCoherentGram y)).isSelfAdjoint.star_eq
  rw [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hstar
  exact hstar

theorem gaussianCoherentCompression_commutes {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    IsCommutingCCRCompression (gaussianCoherentCompression y) := by
  have hRunit : IsUnit (gaussianCoherentSqrt y) :=
    (CFC.isUnit_sqrt_iff (gaussianCoherentGram y) hG.posSemidef.nonneg).mpr hG.isUnit
  letI : Invertible (gaussianCoherentSqrt y) := hRunit.nonempty_invertible.some
  intro i j
  unfold gaussianCoherentCompression
  have hcancel : (gaussianCoherentSqrt y)⁻¹ * gaussianCoherentSqrt y = 1 :=
    Matrix.inv_mul_of_invertible (gaussianCoherentSqrt y)
  calc
    gaussianCoherentSqrt y * gaussianCoordinateDiagonal y i *
          (gaussianCoherentSqrt y)⁻¹ *
        (gaussianCoherentSqrt y * gaussianCoordinateDiagonal y j *
          (gaussianCoherentSqrt y)⁻¹) =
        gaussianCoherentSqrt y * gaussianCoordinateDiagonal y i *
          ((gaussianCoherentSqrt y)⁻¹ * gaussianCoherentSqrt y) *
            gaussianCoordinateDiagonal y j * (gaussianCoherentSqrt y)⁻¹ := by
              noncomm_ring
    _ = gaussianCoherentSqrt y *
          (gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j) *
            (gaussianCoherentSqrt y)⁻¹ := by rw [hcancel]; noncomm_ring
    _ = gaussianCoherentSqrt y *
          (gaussianCoordinateDiagonal y j * gaussianCoordinateDiagonal y i) *
            (gaussianCoherentSqrt y)⁻¹ := by
              rw [gaussianCoordinateDiagonal_commutes]
    _ = gaussianCoherentSqrt y * gaussianCoordinateDiagonal y j *
          (gaussianCoherentSqrt y)⁻¹ *
        (gaussianCoherentSqrt y * gaussianCoordinateDiagonal y i *
          (gaussianCoherentSqrt y)⁻¹) := by
            symm
            calc
              gaussianCoherentSqrt y * gaussianCoordinateDiagonal y j *
                    (gaussianCoherentSqrt y)⁻¹ *
                  (gaussianCoherentSqrt y * gaussianCoordinateDiagonal y i *
                    (gaussianCoherentSqrt y)⁻¹) =
                  gaussianCoherentSqrt y * gaussianCoordinateDiagonal y j *
                    ((gaussianCoherentSqrt y)⁻¹ * gaussianCoherentSqrt y) *
                      gaussianCoordinateDiagonal y i * (gaussianCoherentSqrt y)⁻¹ := by
                        noncomm_ring
              _ = gaussianCoherentSqrt y *
                    (gaussianCoordinateDiagonal y j * gaussianCoordinateDiagonal y i) *
                      (gaussianCoherentSqrt y)⁻¹ := by rw [hcancel]; noncomm_ring

/-- Extract one mode-to-mode block from a matrix on `mode × coherent-label`. -/
def gaussianModeBlock {n d : ℕ}
    (M : Matrix (Fin d × Fin n) (Fin d × Fin n) ℝ) (i j : Fin d) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun p q => M (i, p) (j, q)

theorem gaussianCoherentCrossJet_mode {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (j : Fin d) :
    (fun p q => gaussianCoherentCrossJet y p (j, q)) =
      gaussianCoordinateDiagonal y j * gaussianCoherentGram y := by
  ext p q
  simp [gaussianCoherentCrossJet, gaussianCoordinateDiagonal,
    gaussianCoherentGram, Matrix.diagonal_mul]

theorem gaussianCoherentCrossJet_transpose_mode {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (i : Fin d) :
    (fun p q => (gaussianCoherentCrossJet y).transpose (i, p) q) =
      gaussianCoherentGram y * gaussianCoordinateDiagonal y i := by
  ext p q
  simp only [Matrix.transpose_apply, gaussianCoherentCrossJet,
    gaussianCoherentGram, gaussianCoordinateDiagonal, Matrix.mul_diagonal]
  have hdot : coordinateDot y q p = coordinateDot y p q := by
    unfold coordinateDot
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hdot]
  ring

theorem gaussianCoherentJetBlock_mode {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (i j : Fin d) :
    gaussianModeBlock (gaussianCoherentJetBlock y) i j =
      (if i = j then gaussianCoherentGram y else 0) +
        gaussianCoordinateDiagonal y j * gaussianCoherentGram y *
          gaussianCoordinateDiagonal y i := by
  ext p q
  simp only [gaussianModeBlock, gaussianCoherentJetBlock, Matrix.add_apply]
  simp [gaussianCoordinateDiagonal, gaussianCoherentGram,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i = j <;> simp [hij, gaussianCoherentGram] <;> ring

theorem gaussianCoherentProjectionBlock_mode {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (i j : Fin d) :
    (fun p q => ((gaussianCoherentCrossJet y).transpose *
        (gaussianCoherentGram y)⁻¹ * gaussianCoherentCrossJet y)
          (i, p) (j, q)) =
      gaussianCoherentGram y * gaussianCoordinateDiagonal y i *
        (gaussianCoherentGram y)⁻¹ * gaussianCoordinateDiagonal y j *
          gaussianCoherentGram y := by
  let Yi : Matrix (Fin n) (Fin n) ℝ :=
    fun a b => (gaussianCoherentCrossJet y).transpose (i, a) b
  let Yj : Matrix (Fin n) (Fin n) ℝ :=
    fun a b => gaussianCoherentCrossJet y a (j, b)
  have hblock : (fun p q => ((gaussianCoherentCrossJet y).transpose *
        (gaussianCoherentGram y)⁻¹ * gaussianCoherentCrossJet y)
          (i, p) (j, q)) = Yi * (gaussianCoherentGram y)⁻¹ * Yj := by
    ext p q
    simp [Yi, Yj, Matrix.mul_apply]
  have hYi : Yi = gaussianCoherentGram y * gaussianCoordinateDiagonal y i := by
    exact gaussianCoherentCrossJet_transpose_mode y i
  have hYj : Yj = gaussianCoordinateDiagonal y j * gaussianCoherentGram y := by
    exact gaussianCoherentCrossJet_mode y j
  rw [hblock, hYi, hYj]
  noncomm_ring

theorem gaussianCoherentJetSchurComplement_mode {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (i j : Fin d) :
    gaussianModeBlock (gaussianCoherentJetSchurComplement y) i j =
      (if i = j then gaussianCoherentGram y else 0) +
          gaussianCoordinateDiagonal y j * gaussianCoherentGram y *
            gaussianCoordinateDiagonal y i -
        gaussianCoherentGram y * gaussianCoordinateDiagonal y i *
          (gaussianCoherentGram y)⁻¹ * gaussianCoordinateDiagonal y j *
            gaussianCoherentGram y := by
  ext p q
  unfold gaussianModeBlock gaussianCoherentJetSchurComplement
  simp only [Matrix.sub_apply]
  rw [show gaussianCoherentJetBlock y (i, p) (j, q) =
      gaussianModeBlock (gaussianCoherentJetBlock y) i j p q by rfl,
    gaussianCoherentJetBlock_mode]
  rw [show ((gaussianCoherentCrossJet y).conjTranspose *
      (gaussianCoherentGram y)⁻¹ * gaussianCoherentCrossJet y) (i, p) (j, q) =
      ((gaussianCoherentCrossJet y).transpose *
        (gaussianCoherentGram y)⁻¹ * gaussianCoherentCrossJet y) (i, p) (j, q) by
    simp [Matrix.conjTranspose_eq_transpose_of_trivial]]
  rw [show ((gaussianCoherentCrossJet y).transpose *
      (gaussianCoherentGram y)⁻¹ * gaussianCoherentCrossJet y) (i, p) (j, q) =
      (fun a b => ((gaussianCoherentCrossJet y).transpose *
        (gaussianCoherentGram y)⁻¹ * gaussianCoherentCrossJet y)
          (i, a) (j, b)) p q by rfl,
    gaussianCoherentProjectionBlock_mode]

theorem gaussianCoherentGram_inv_eq_sqrt_inv_mul {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    (gaussianCoherentGram y)⁻¹ =
      (gaussianCoherentSqrt y)⁻¹ * (gaussianCoherentSqrt y)⁻¹ := by
  letI : Invertible (gaussianCoherentGram y) :=
    Matrix.invertibleOfIsUnitDet _
      ((gaussianCoherentGram y).isUnit_iff_isUnit_det.mp hG.isUnit)
  have hRunit : IsUnit (gaussianCoherentSqrt y) :=
    (CFC.isUnit_sqrt_iff (gaussianCoherentGram y) hG.posSemidef.nonneg).mpr hG.isUnit
  letI : Invertible (gaussianCoherentSqrt y) := hRunit.nonempty_invertible.some
  apply Matrix.mul_left_injective_of_invertible (A := gaussianCoherentGram y)
  change (gaussianCoherentGram y)⁻¹ * gaussianCoherentGram y =
    ((gaussianCoherentSqrt y)⁻¹ * (gaussianCoherentSqrt y)⁻¹) *
      gaussianCoherentGram y
  rw [Matrix.inv_mul_of_invertible]
  rw [← gaussianCoherentSqrt_mul_self y hG]
  have hcancel : (gaussianCoherentSqrt y)⁻¹ * gaussianCoherentSqrt y = 1 :=
    Matrix.inv_mul_of_invertible _
  symm
  calc
    ((gaussianCoherentSqrt y)⁻¹ * (gaussianCoherentSqrt y)⁻¹) *
          (gaussianCoherentSqrt y * gaussianCoherentSqrt y) =
        (gaussianCoherentSqrt y)⁻¹ *
          ((gaussianCoherentSqrt y)⁻¹ * gaussianCoherentSqrt y) *
            gaussianCoherentSqrt y := by noncomm_ring
    _ = (gaussianCoherentSqrt y)⁻¹ * gaussianCoherentSqrt y := by
      rw [hcancel]
      simp
    _ = 1 := hcancel

theorem gaussianCoherentCompression_transpose {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (i : Fin d) :
    (gaussianCoherentCompression y i).transpose =
      (gaussianCoherentSqrt y)⁻¹ * gaussianCoordinateDiagonal y i *
        gaussianCoherentSqrt y := by
  unfold gaussianCoherentCompression
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv, gaussianCoherentSqrt_transpose,
    gaussianCoordinateDiagonal_transpose]
  noncomm_ring

theorem gaussianCoherentCCRDefect_conjugation {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef)
    (i j : Fin d) :
    gaussianCoherentSqrt y * gaussianModeBlock (gaussianCoherentCCRDefect y) i j *
        gaussianCoherentSqrt y =
      gaussianModeBlock (gaussianCoherentJetSchurComplement y) i j := by
  let R := gaussianCoherentSqrt y
  let Ri := (gaussianCoherentSqrt y)⁻¹
  let Di := gaussianCoordinateDiagonal y i
  let Dj := gaussianCoordinateDiagonal y j
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff (gaussianCoherentGram y) hG.posSemidef.nonneg).mpr hG.isUnit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hleft : R * Ri = 1 := Matrix.mul_inv_of_invertible _
  have hright : Ri * R = 1 := Matrix.inv_mul_of_invertible _
  have hterm₁ :
      R * ((Ri * Dj * R) * (R * Di * Ri)) * R = Dj * (R * R) * Di := by
    calc
      R * ((Ri * Dj * R) * (R * Di * Ri)) * R =
          (R * Ri) * Dj * (R * R) * Di * (Ri * R) := by noncomm_ring
      _ = Dj * (R * R) * Di := by rw [hleft, hright]; simp
  have hterm₂ :
      R * ((R * Di * Ri) * (Ri * Dj * R)) * R =
        (R * R) * Di * (Ri * Ri) * Dj * (R * R) := by noncomm_ring
  rw [gaussianCoherentJetSchurComplement_mode]
  unfold gaussianModeBlock gaussianCoherentCCRDefect
  change R * ((if i = j then 1 else 0) +
      (gaussianCoherentCompression y j).transpose * gaussianCoherentCompression y i -
      gaussianCoherentCompression y i *
        (gaussianCoherentCompression y j).transpose) * R = _
  rw [gaussianCoherentCompression_transpose]
  change R * ((if i = j then 1 else 0) +
      (Ri * Dj * R) * (R * Di * Ri) -
      (R * Di * Ri) * (Ri * Dj * R)) * R = _
  rw [gaussianCoherentGram_inv_eq_sqrt_inv_mul y hG]
  rw [show gaussianCoherentGram y = R * R by
    exact (gaussianCoherentSqrt_mul_self y hG).symm]
  change R * ((if i = j then 1 else 0) +
      (Ri * Dj * R) * (R * Di * Ri) -
      (R * Di * Ri) * (Ri * Dj * R)) * R =
    (if i = j then R * R else 0) + Dj * (R * R) * Di -
      (R * R) * Di * (Ri * Ri) * Dj * (R * R)
  have hdelta : R * (if i = j then 1 else 0) * R =
      if i = j then R * R else 0 := by
    by_cases hij : i = j <;> simp [hij]
  calc
    R * ((if i = j then 1 else 0) +
          (Ri * Dj * R) * (R * Di * Ri) -
          (R * Di * Ri) * (Ri * Dj * R)) * R =
        R * (if i = j then 1 else 0) * R +
          R * ((Ri * Dj * R) * (R * Di * Ri)) * R -
          R * ((R * Di * Ri) * (Ri * Dj * R)) * R := by noncomm_ring
    _ = (if i = j then R * R else 0) + Dj * (R * R) * Di -
        (R * R) * Di * (Ri * Ri) * Dj * (R * R) := by
          rw [hdelta, hterm₁, hterm₂]

theorem gaussianModeBlockDiagonal_mul {n d : ℕ}
    (R S : Matrix (Fin n) (Fin n) ℝ) :
    gaussianModeBlockDiagonal (d := d) R * gaussianModeBlockDiagonal S =
      gaussianModeBlockDiagonal (R * S) := by
  ext ip jq
  simp only [Matrix.mul_apply, gaussianModeBlockDiagonal]
  rw [Fintype.sum_prod_type]
  by_cases hij : ip.1 = jq.1 <;> simp [hij]

theorem gaussianModeBlockDiagonal_transpose {n d : ℕ}
    (R : Matrix (Fin n) (Fin n) ℝ) :
    (gaussianModeBlockDiagonal (d := d) R).transpose =
      gaussianModeBlockDiagonal R.transpose := by
  ext ip jq
  by_cases hij : ip.1 = jq.1
  · simp [gaussianModeBlockDiagonal, Matrix.transpose_apply, hij]
  · simp [gaussianModeBlockDiagonal, Matrix.transpose_apply, hij, Ne.symm hij]

theorem gaussianModeBlockDiagonal_one {n d : ℕ} :
    gaussianModeBlockDiagonal (d := d) (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  ext ip jq
  by_cases hmode : ip.1 = jq.1 <;> by_cases hlabel : ip.2 = jq.2 <;>
    simp [gaussianModeBlockDiagonal, Matrix.one_apply, Prod.ext_iff, hmode, hlabel]

theorem gaussianModeBlockDiagonal_isUnit {n d : ℕ}
    {R : Matrix (Fin n) (Fin n) ℝ} (hR : IsUnit R) :
    IsUnit (gaussianModeBlockDiagonal (d := d) R) := by
  letI : Invertible R := hR.nonempty_invertible.some
  apply IsUnit.of_mul_eq_one (gaussianModeBlockDiagonal (d := d) R⁻¹)
  rw [gaussianModeBlockDiagonal_mul, Matrix.mul_inv_of_invertible,
    gaussianModeBlockDiagonal_one]

theorem gaussianModeBlock_diagonal_mul_mul {n d : ℕ}
    (R S : Matrix (Fin n) (Fin n) ℝ)
    (M : Matrix (Fin d × Fin n) (Fin d × Fin n) ℝ) (i j : Fin d) :
    gaussianModeBlock (gaussianModeBlockDiagonal R * M * gaussianModeBlockDiagonal S) i j =
      R * gaussianModeBlock M i j * S := by
  ext p q
  simp [gaussianModeBlock, Matrix.mul_apply, gaussianModeBlockDiagonal,
    Fintype.sum_prod_type]

/-- The canonical coherent CCR defect is positive semidefinite; this is the intrinsic finite
operator form of residual first-jet positivity. -/
theorem gaussianCoherentCCRDefect_posSemidef {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    (gaussianCoherentCCRDefect y).PosSemidef := by
  let Q := gaussianModeBlockDiagonal (d := d) (gaussianCoherentSqrt y)
  have hRunit : IsUnit (gaussianCoherentSqrt y) :=
    (CFC.isUnit_sqrt_iff (gaussianCoherentGram y) hG.posSemidef.nonneg).mpr hG.isUnit
  have hQunit : IsUnit Q := gaussianModeBlockDiagonal_isUnit hRunit
  apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hQunit).mp
  have hconj : Q * gaussianCoherentCCRDefect y * star Q =
      gaussianCoherentJetSchurComplement y := by
    rw [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial,
      show Q.transpose = gaussianModeBlockDiagonal
          (gaussianCoherentSqrt y).transpose by
        exact gaussianModeBlockDiagonal_transpose _]
    rw [gaussianCoherentSqrt_transpose]
    dsimp [Q]
    ext ip jq
    calc
      (gaussianModeBlockDiagonal (d := d) (gaussianCoherentSqrt y) *
          gaussianCoherentCCRDefect y *
            gaussianModeBlockDiagonal (d := d) (gaussianCoherentSqrt y)) ip jq =
        gaussianModeBlock
          (gaussianModeBlockDiagonal (d := d) (gaussianCoherentSqrt y) *
            gaussianCoherentCCRDefect y *
              gaussianModeBlockDiagonal (d := d) (gaussianCoherentSqrt y))
            ip.1 jq.1 ip.2 jq.2 := rfl
      _ = (gaussianCoherentSqrt y *
          gaussianModeBlock (gaussianCoherentCCRDefect y) ip.1 jq.1 *
            gaussianCoherentSqrt y) ip.2 jq.2 := by
        rw [gaussianModeBlock_diagonal_mul_mul]
      _ = gaussianModeBlock (gaussianCoherentJetSchurComplement y)
          ip.1 jq.1 ip.2 jq.2 :=
        congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M ip.2 jq.2)
          (gaussianCoherentCCRDefect_conjugation y hG ip.1 jq.1)
      _ = gaussianCoherentJetSchurComplement y ip jq := rfl
  rw [hconj]
  exact gaussianCoherentJetSchurComplement_posSemidef y hG

/-- Residual coherent-jet positivity produces literal rectangular CCR leakage blocks. -/
theorem exists_gaussianCoherentCCRCompletion {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    ∃ B : Fin d → Matrix (Fin n) (Fin d × Fin n) ℝ,
      IsCCRCompletion (gaussianCoherentCompression y) B := by
  have hL := gaussianCoherentCCRDefect_posSemidef y hG
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hL.nonneg
  let B : Fin d → Matrix (Fin n) (Fin d × Fin n) ℝ :=
    fun i p k => X k (i, p)
  refine ⟨B, ?_⟩
  intro i j
  ext p q
  have hfactor :
      (B i * (B j).transpose) p q =
        (X.conjTranspose * X) (i, p) (j, q) := by
    simp only [Matrix.mul_apply, B, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, star_id_of_comm]
  rw [hfactor]
  have hX' : gaussianCoherentCCRDefect y = X.conjTranspose * X := by
    simpa [Matrix.star_eq_conjTranspose] using hX
  rw [← hX']
  rfl

/-- A canonical choice of finite coherent CCR leakage blocks. -/
def gaussianCoherentLeakage {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    Fin d → Matrix (Fin n) (Fin d × Fin n) ℝ :=
  Classical.choose (exists_gaussianCoherentCCRCompletion y hG)

theorem gaussianCoherentLeakage_isCCRCompletion {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    IsCCRCompletion (gaussianCoherentCompression y)
      (gaussianCoherentLeakage y hG) :=
  Classical.choose_spec (exists_gaussianCoherentCCRCompletion y hG)

/-- The coherent Gaussian compression obeys the exact pairwise CCR dimension--fluctuation law. -/
theorem gaussianCoherent_dimension_fluctuation_pairwise_identity {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    (d : ℝ) * ((d : ℝ) + 1) *
        ((d : ℝ) * ccrMeanEnergy (gaussianCoherentCompression y) -
          ccrNumberVariance (gaussianCoherentCompression y)
            (gaussianCoherentLeakage y hG)) =
      (d : ℝ) ^ 2 *
          ccrPairwiseMixedCommutatorEnergy (gaussianCoherentCompression y) +
        ccrScaledTracelessLeakageEnergy (gaussianCoherentCompression y)
          (gaussianCoherentLeakage y hG) := by
  simpa using ccr_dimension_fluctuation_pairwise_identity
    (gaussianCoherentCompression y) (gaussianCoherentLeakage y hG)
    (gaussianCoherentCompression_commutes y hG)
    (gaussianCoherentLeakage_isCCRCompletion y hG)

/-- The number variance of an independent finite coherent Gaussian family is at most the ambient
coordinate dimension times its compressed mean energy. -/
theorem gaussianCoherent_numberVariance_le_dim_mul_mean {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef)
    (hd : 0 < d) :
    ccrNumberVariance (gaussianCoherentCompression y)
        (gaussianCoherentLeakage y hG) ≤
      (d : ℝ) * ccrMeanEnergy (gaussianCoherentCompression y) := by
  simpa using ccr_numberVariance_le_card_mul_mean
    (gaussianCoherentCompression y) (gaussianCoherentLeakage y hG)
    (gaussianCoherentCompression_commutes y hG)
    (gaussianCoherentLeakage_isCCRCompletion y hG)
    (show 0 < Fintype.card (Fin d) by simpa using hd)

/-! ### Strict positivity of distinct coherent families -/

/-- Ordinary coordinate Gram matrix. -/
def coordinateDotMatrix {n d : ℕ} (y : Fin n → Fin d → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun p q => coordinateDot y p q

/-- Entrywise natural power of the coordinate Gram matrix. -/
def coordinateDotPowerMatrix {n d : ℕ} (y : Fin n → Fin d → ℝ) (r : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun p q => coordinateDot y p q ^ r

theorem coordinateDotMatrix_posSemidef {n d : ℕ} (y : Fin n → Fin d → ℝ) :
    (coordinateDotMatrix y).PosSemidef := by
  have h : coordinateDotMatrix y = standardFeatureGram y := by
    ext p q
    rfl
  rw [h]
  exact standardFeatureGram_posSemidef y

theorem coordinateDotPowerMatrix_posSemidef {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (r : ℕ) :
    (coordinateDotPowerMatrix y r).PosSemidef := by
  induction r with
  | zero =>
      have h : coordinateDotPowerMatrix y 0 =
          standardFeatureGram (κ := Unit) (fun (_ : Fin n) (_ : Unit) => (1 : ℝ)) := by
        ext p q
        simp [coordinateDotPowerMatrix, standardFeatureGram]
      rw [h]
      exact standardFeatureGram_posSemidef _
  | succ r hr =>
      have h : coordinateDotPowerMatrix y (r + 1) =
          (coordinateDotPowerMatrix y r ⊙ coordinateDotMatrix y) := by
        ext p q
        simp [coordinateDotPowerMatrix, coordinateDotMatrix, pow_succ]
      rw [h]
      exact hr.hadamard (coordinateDotMatrix_posSemidef y)

/-- Finite exponential-series tail from degree `m + 1` through `m + k + 1`. -/
def gaussianExpTailMatrix {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (m k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ r ∈ Finset.Ico (m + 1) (m + k + 2),
    ((1 : ℝ) / Nat.factorial r) • coordinateDotPowerMatrix y r

theorem gaussianExpTailMatrix_posSemidef {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (m k : ℕ) :
    (gaussianExpTailMatrix y m k).PosSemidef := by
  unfold gaussianExpTailMatrix
  apply Matrix.posSemidef_sum
  intro r hr
  exact (coordinateDotPowerMatrix_posSemidef y r).smul
    (by positivity : (0 : ℝ) ≤ 1 / Nat.factorial r)

theorem truncatedExpSeries_eq_sum_range (z : ℝ) (m : ℕ) :
    truncatedExpSeries z m =
      ∑ r ∈ Finset.range (m + 1), z ^ r / Nat.factorial r := by
  exact Fin.sum_univ_eq_sum_range
    (fun r => z ^ r / Nat.factorial r) (m + 1)

theorem truncatedExponentialInnerMatrix_add_tail {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (m k : ℕ) :
    truncatedExponentialInnerMatrix y m (1 / 2) + gaussianExpTailMatrix y m k =
      truncatedExponentialInnerMatrix y (m + k + 1) (1 / 2) := by
  ext p q
  unfold truncatedExponentialInnerMatrix truncatedExpSeries gaussianExpTailMatrix
    coordinateDotPowerMatrix
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change truncatedExpSeries (2 * (1 / 2) * coordinateDot y p q) m +
      (∑ r ∈ Finset.Ico (m + 1) (m + k + 2),
        (1 / Nat.factorial r : ℝ) * coordinateDot y p q ^ r) =
    truncatedExpSeries (2 * (1 / 2) * coordinateDot y p q) (m + k + 1)
  rw [truncatedExpSeries_eq_sum_range, truncatedExpSeries_eq_sum_range]
  norm_num
  have hle : m + 1 ≤ m + k + 2 := by omega
  rw [Finset.sum_Ico_eq_sub _ hle]
  ring

/-- The exact coherent Gram matrix minus any Taylor truncation is positive semidefinite. -/
theorem gaussianCoherentGram_sub_truncation_posSemidef {n d : ℕ}
    (y : Fin n → Fin d → ℝ) (m : ℕ) :
    (gaussianCoherentGram y -
      truncatedExponentialInnerMatrix y m (1 / 2)).PosSemidef := by
  apply Matrix.PosSemidef.of_tendsto (α := ℕ) (n := Fin n) (l := atTop)
    (A := fun k => truncatedExponentialInnerMatrix y (m + k + 1) (1 / 2) -
      truncatedExponentialInnerMatrix y m (1 / 2))
    (M := gaussianCoherentGram y -
      truncatedExponentialInnerMatrix y m (1 / 2))
  · exact Filter.Eventually.of_forall fun k => by
      rw [show truncatedExponentialInnerMatrix y (m + k + 1) (1 / 2) -
          truncatedExponentialInnerMatrix y m (1 / 2) =
          gaussianExpTailMatrix y m k by
        rw [← truncatedExponentialInnerMatrix_add_tail]
        abel]
      exact gaussianExpTailMatrix_posSemidef y m k
  · have hlim := (tendsto_truncatedExponentialInnerMatrix y (1 / 2)).comp
        (tendsto_add_atTop_nat (m + 1))
    have hc : Tendsto
        (fun _ : ℕ => truncatedExponentialInnerMatrix y m (1 / 2)) atTop
        (nhds (truncatedExponentialInnerMatrix y m (1 / 2))) := tendsto_const_nhds
    have hsub := hlim.sub hc
    have hfun : (fun k =>
        ((fun r => truncatedExponentialInnerMatrix y r (1 / 2)) ∘
            fun a => a + (m + 1)) k -
          truncatedExponentialInnerMatrix y m (1 / 2)) =
        (fun k => truncatedExponentialInnerMatrix y (m + k + 1) (1 / 2) -
          truncatedExponentialInnerMatrix y m (1 / 2)) := by
      funext k
      simp only [Function.comp_apply]
      congr 2
      omega
    have hCG : coordinateExponentialInnerMatrix y (1 / 2) =
        gaussianCoherentGram y := by
      ext p q
      simp only [coordinateExponentialInnerMatrix, gaussianCoherentGram]
      congr 1
      ring
    rw [← hfun]
    simpa only [hCG] using hsub

/-! ### Vandermonde strict positivity

The first `n` tensor powers along any coordinate that separates the `n` points form a square
Vandermonde subsystem of the degree-`n` Fock feature matrix.  Hence that finite truncation already
has full row rank; the positive Taylor tail then upgrades the exact coherent Gram matrix from
positive semidefinite to positive definite.
-/

/-- The constant ordered tensor word of degree `q`, used to expose a Vandermonde subsystem. -/
def gaussianVandermondeFeature {d n : ℕ} (k : Fin d) (q : Fin n) :
    orderedTensorFeature d n :=
  toLex ⟨q.castSucc, toLex (fun _ => k)⟩

@[simp]
theorem orderedTensorDegree_gaussianVandermondeFeature {d n : ℕ}
    (k : Fin d) (q : Fin n) :
    orderedTensorDegree (gaussianVandermondeFeature k q) = q.1 := by
  simp [orderedTensorDegree, gaussianVandermondeFeature]

theorem orderedTensorMonomial_gaussianVandermondeFeature {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (k : Fin d) (i q : Fin n) :
    orderedTensorMonomial y i (gaussianVandermondeFeature k q) = y i k ^ q.1 := by
  change (∏ _ : Fin q.1, y i k) = y i k ^ q.1
  simp

theorem orderedTensorWeight_gaussianVandermondeFeature_pos {d n : ℕ}
    (k : Fin d) (q : Fin n) :
    0 < orderedTensorWeight (gaussianVandermondeFeature k q) := by
  unfold orderedTensorWeight
  rw [orderedTensorDegree_gaussianVandermondeFeature]
  positivity

theorem orderedTensorFockRow_gaussianVandermondeFeature {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (k : Fin d) (i q : Fin n) :
    orderedTensorFockRow y (Real.sqrt (1 / 2)) i (gaussianVandermondeFeature k q) =
      Real.sqrt (orderedTensorWeight (gaussianVandermondeFeature k q)) *
        Real.sqrt (1 / 2) ^ q.1 * y i k ^ q.1 := by
  unfold orderedTensorFockRow scaledFeatureRows
  rw [orderedTensorDegree_gaussianVandermondeFeature]
  rw [orderedTensorMonomial_gaussianVandermondeFeature]

/-- If one coordinate separates the points, the degree-`n` ordered Fock feature matrix has full
row rank.  The proof restricts a hypothetical row dependence to its Vandermonde columns. -/
theorem gaussianOrderedTensorFockRow_vecMul_injective_of_coordinate_injective
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (k : Fin d)
    (hy : Function.Injective (fun i => y i k)) :
    Function.Injective
      (fun x : Fin n → ℝ =>
        Matrix.vecMul x (fun i (q : orderedTensorFeature d n) =>
          orderedTensorFockRow (m := n) y (Real.sqrt (1 / 2)) i q)) := by
  let A : Matrix (Fin n) (orderedTensorFeature d n) ℝ :=
    fun i q => orderedTensorFockRow y (Real.sqrt (1 / 2)) i q
  intro x x' hxx
  change x ᵥ* A = x' ᵥ* A at hxx
  have hv : (x - x') ᵥ* A = 0 := by
    rw [Matrix.sub_vecMul, hxx, sub_self]
  have hp : ∀ q : Fin n, ∑ i : Fin n, (x i - x' i) * y i k ^ q.1 = 0 := by
    intro q
    have hq := congrFun hv (gaussianVandermondeFeature k q)
    simp only [Pi.zero_apply] at hq
    rw [show ((x - x') ᵥ* A) (gaussianVandermondeFeature k q) =
        ∑ i : Fin n, (x i - x' i) * A i (gaussianVandermondeFeature k q) by rfl] at hq
    have hw : Real.sqrt (orderedTensorWeight (gaussianVandermondeFeature k q)) *
        Real.sqrt (1 / 2) ^ q.1 ≠ 0 := by
      apply mul_ne_zero
      · exact (Real.sqrt_pos.2
          (orderedTensorWeight_gaussianVandermondeFeature_pos k q)).ne'
      · exact pow_ne_zero _ (Real.sqrt_pos.2 (by norm_num)).ne'
    have hfactor :
        (Real.sqrt (orderedTensorWeight (gaussianVandermondeFeature k q)) *
            Real.sqrt (1 / 2) ^ q.1) *
          (∑ i : Fin n, (x i - x' i) * y i k ^ q.1) = 0 := by
      calc
        _ = ∑ i : Fin n, (x i - x' i) * A i (gaussianVandermondeFeature k q) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show A i (gaussianVandermondeFeature k q) =
              Real.sqrt (orderedTensorWeight (gaussianVandermondeFeature k q)) *
                Real.sqrt (1 / 2) ^ q.1 * y i k ^ q.1 by
            exact orderedTensorFockRow_gaussianVandermondeFeature y k i q]
          ring
        _ = 0 := hq
    exact (mul_eq_zero.mp hfactor).resolve_left hw
  have hzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hy hp
  exact sub_eq_zero.mp hzero

/-- A separating coordinate makes the degree-`n` exponential Taylor Gram positive definite. -/
theorem truncatedExponentialInnerMatrix_posDef_of_coordinate_injective
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (k : Fin d)
    (hy : Function.Injective (fun i => y i k)) :
    (truncatedExponentialInnerMatrix y n (1 / 2)).PosDef := by
  rw [← orderedTensorFockGram_sqrt_eq_truncatedExponentialInnerMatrix y n (1 / 2)
    (by norm_num)]
  let A : Matrix (Fin n) (orderedTensorFeature d n) ℝ :=
    fun i q => orderedTensorFockRow y (Real.sqrt (1 / 2)) i q
  have hA : Function.Injective A.vecMul :=
    gaussianOrderedTensorFockRow_vecMul_injective_of_coordinate_injective y k hy
  have hGram : orderedTensorFockGram y n (Real.sqrt (1 / 2)) =
      A * A.conjTranspose := by
    ext i j
    simp [orderedTensorFockGram, standardFeatureGram, A, Matrix.mul_apply]
  rw [hGram]
  exact Matrix.PosDef.mul_conjTranspose_self A hA

/-- A separating coordinate makes the exact coherent Gaussian Gram matrix positive definite. -/
theorem gaussianCoherentGram_posDef_of_coordinate_injective
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (k : Fin d)
    (hy : Function.Injective (fun i => y i k)) :
    (gaussianCoherentGram y).PosDef := by
  have htrunc : (truncatedExponentialInnerMatrix y n (1 / 2)).PosDef :=
    truncatedExponentialInnerMatrix_posDef_of_coordinate_injective y k hy
  have htail : (gaussianCoherentGram y -
      truncatedExponentialInnerMatrix y n (1 / 2)).PosSemidef :=
    gaussianCoherentGram_sub_truncation_posSemidef y n
  have hsum := htrunc.add_posSemidef htail
  convert hsum using 1
  abel

/-! ### Coordinate-free strict positivity

An arbitrary real linear functional on `Fin d → ℝ` is a finite coordinate sum.  If it separates
the configuration, its first `n` powers form a Vandermonde system inside the ordered-tensor feature
matrix.  A finite family of nonzero pairwise differences admits such a functional because a finite
union of proper dual hyperplanes cannot cover a real vector space.
-/

/-- An arbitrary tensor word in degree `q`, embedded into the degree-`n` feature type. -/
def gaussianTensorWordFeature {d n : ℕ} (q : Fin n) (w : Fin q.1 → Fin d) :
    orderedTensorFeature d n :=
  toLex ⟨q.castSucc, toLex w⟩

@[simp]
theorem orderedTensorDegree_gaussianTensorWordFeature {d n : ℕ}
    (q : Fin n) (w : Fin q.1 → Fin d) :
    orderedTensorDegree (gaussianTensorWordFeature q w) = q.1 := by
  simp [orderedTensorDegree, gaussianTensorWordFeature]

theorem orderedTensorMonomial_gaussianTensorWordFeature {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (i : Fin n) (q : Fin n) (w : Fin q.1 → Fin d) :
    orderedTensorMonomial y i (gaussianTensorWordFeature q w) = ∏ r, y i (w r) := by
  rfl

theorem orderedTensorWeight_gaussianTensorWordFeature_pos {d n : ℕ}
    (q : Fin n) (w : Fin q.1 → Fin d) :
    0 < orderedTensorWeight (gaussianTensorWordFeature q w) := by
  unfold orderedTensorWeight
  rw [orderedTensorDegree_gaussianTensorWordFeature]
  positivity

theorem orderedTensorFockRow_gaussianTensorWordFeature {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (i : Fin n) (q : Fin n) (w : Fin q.1 → Fin d) :
    orderedTensorFockRow y (Real.sqrt (1 / 2)) i (gaussianTensorWordFeature q w) =
      Real.sqrt (orderedTensorWeight (gaussianTensorWordFeature q w)) *
        Real.sqrt (1 / 2) ^ q.1 * ∏ r, y i (w r) := by
  unfold orderedTensorFockRow scaledFeatureRows
  rw [orderedTensorDegree_gaussianTensorWordFeature,
    orderedTensorMonomial_gaussianTensorWordFeature]

/-- The power of a finite linear form is its ordered-word tensor expansion. -/
theorem linearForm_power_eq_sum_orderedWords {d : ℕ}
    (c z : Fin d → ℝ) (q : ℕ) :
    (∑ s, c s * z s) ^ q =
      ∑ w : Fin q → Fin d, (∏ r, c (w r)) * ∏ r, z (w r) := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.prod_mul_distrib]

/-- A separating linear form makes the full degree-`n` ordered Fock feature matrix injective on
row coefficients. -/
theorem gaussianOrderedTensorFockRow_vecMul_injective_of_linearForm_injective
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (c : Fin d → ℝ)
    (hy : Function.Injective (fun i => ∑ s, c s * y i s)) :
    Function.Injective
      (fun x : Fin n → ℝ =>
        Matrix.vecMul x (fun i (q : orderedTensorFeature d n) =>
          orderedTensorFockRow (m := n) y (Real.sqrt (1 / 2)) i q)) := by
  let A : Matrix (Fin n) (orderedTensorFeature d n) ℝ :=
    fun i q => orderedTensorFockRow y (Real.sqrt (1 / 2)) i q
  intro x x' hxx
  change x ᵥ* A = x' ᵥ* A at hxx
  have hv : (x - x') ᵥ* A = 0 := by
    rw [Matrix.sub_vecMul, hxx, sub_self]
  have hword : ∀ (q : Fin n) (w : Fin q.1 → Fin d),
      ∑ i : Fin n, (x i - x' i) * ∏ r, y i (w r) = 0 := by
    intro q w
    have hq := congrFun hv (gaussianTensorWordFeature q w)
    simp only [Pi.zero_apply] at hq
    rw [show ((x - x') ᵥ* A) (gaussianTensorWordFeature q w) =
        ∑ i : Fin n, (x i - x' i) * A i (gaussianTensorWordFeature q w) by rfl] at hq
    have hw : Real.sqrt (orderedTensorWeight (gaussianTensorWordFeature q w)) *
        Real.sqrt (1 / 2) ^ q.1 ≠ 0 := by
      apply mul_ne_zero
      · exact (Real.sqrt_pos.2
          (orderedTensorWeight_gaussianTensorWordFeature_pos q w)).ne'
      · exact pow_ne_zero _ (Real.sqrt_pos.2 (by norm_num)).ne'
    have hfactor :
        (Real.sqrt (orderedTensorWeight (gaussianTensorWordFeature q w)) *
            Real.sqrt (1 / 2) ^ q.1) *
          (∑ i : Fin n, (x i - x' i) * ∏ r, y i (w r)) = 0 := by
      calc
        _ = ∑ i : Fin n, (x i - x' i) * A i (gaussianTensorWordFeature q w) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show A i (gaussianTensorWordFeature q w) =
              Real.sqrt (orderedTensorWeight (gaussianTensorWordFeature q w)) *
                Real.sqrt (1 / 2) ^ q.1 * ∏ r, y i (w r) by
            exact orderedTensorFockRow_gaussianTensorWordFeature y i q w]
          ring
        _ = 0 := hq
    exact (mul_eq_zero.mp hfactor).resolve_left hw
  have hp : ∀ q : Fin n,
      ∑ i : Fin n, (x i - x' i) * (∑ s, c s * y i s) ^ q.1 = 0 := by
    intro q
    simp_rw [linearForm_power_eq_sum_orderedWords]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro w _
    calc
      _ = (∏ r, c (w r)) *
          (∑ i : Fin n, (x i - x' i) * ∏ r, y i (w r)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hword q w, mul_zero]
  have hzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hy hp
  exact sub_eq_zero.mp hzero

/-- Ordered pairs of distinct row indices. -/
abbrev gaussianOffDiagonalPair (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- Every injective finite Euclidean configuration admits a real linear form that separates all
of its points. -/
theorem exists_gaussianSeparatingLinearForm {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    ∃ c : Fin d → ℝ, Function.Injective (fun i => ∑ s, c s * y i s) := by
  let v : gaussianOffDiagonalPair n → (Fin d → ℝ) := fun p => y p.1.1 - y p.1.2
  have hv : ∀ p, v p ≠ 0 := by
    intro p
    exact sub_ne_zero.mpr (hy.ne p.2)
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero
    (K := ℝ) (M := Fin d → ℝ) v hv
  let c : Fin d → ℝ := fun s => f (Pi.single s 1)
  have hrepr (i : Fin n) : (∑ s, c s * y i s) = f (y i) := by
    calc
      _ = ∑ s, f (Pi.single s (y i s)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [show Pi.single s (y i s) = y i s • Pi.single s (1 : ℝ) by
          ext r
          by_cases h : r = s
          · subst r
            simp
          · simp [h]]
        rw [map_smul]
        simp [c, mul_comm]
      _ = f (∑ s, Pi.single s (y i s)) := by rw [map_sum]
      _ = f (y i) := by rw [Finset.univ_sum_single]
  refine ⟨c, fun i j hij => ?_⟩
  by_contra hne
  let p : gaussianOffDiagonalPair n := ⟨(i, j), hne⟩
  have hfij : f (y i) = f (y j) := by
    rw [← hrepr i, ← hrepr j]
    exact hij
  have hz : f (v p) = 0 := by
    rw [show v p = y i - y j by rfl, map_sub, hfij, sub_self]
  exact hf p hz

/-- The degree-`n` exponential Taylor Gram of every injective finite Euclidean configuration is
positive definite. -/
theorem truncatedExponentialInnerMatrix_posDef_of_injective
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    (truncatedExponentialInnerMatrix y n (1 / 2)).PosDef := by
  obtain ⟨c, hc⟩ := exists_gaussianSeparatingLinearForm y hy
  rw [← orderedTensorFockGram_sqrt_eq_truncatedExponentialInnerMatrix y n (1 / 2)
    (by norm_num)]
  let A : Matrix (Fin n) (orderedTensorFeature d n) ℝ :=
    fun i q => orderedTensorFockRow y (Real.sqrt (1 / 2)) i q
  have hA : Function.Injective A.vecMul :=
    gaussianOrderedTensorFockRow_vecMul_injective_of_linearForm_injective y c hc
  have hGram : orderedTensorFockGram y n (Real.sqrt (1 / 2)) =
      A * A.conjTranspose := by
    ext i j
    simp [orderedTensorFockGram, standardFeatureGram, A, Matrix.mul_apply]
  rw [hGram]
  exact Matrix.PosDef.mul_conjTranspose_self A hA

/-- The coherent Gaussian Gram matrix of every injective finite Euclidean configuration is
positive definite, including all empty-dimensional and singleton edge cases. -/
theorem gaussianCoherentGram_posDef_of_injective
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    (gaussianCoherentGram y).PosDef := by
  have htrunc : (truncatedExponentialInnerMatrix y n (1 / 2)).PosDef :=
    truncatedExponentialInnerMatrix_posDef_of_injective y hy
  have htail : (gaussianCoherentGram y -
      truncatedExponentialInnerMatrix y n (1 / 2)).PosSemidef :=
    gaussianCoherentGram_sub_truncation_posSemidef y n
  have hsum := htrunc.add_posSemidef htail
  convert hsum using 1
  abel

/-! ### Unconditional finite Gaussian CCR law -/

/-- Canonical CCR leakage of an injective finite coherent Gaussian family. -/
def gaussianCoherentInjectiveLeakage {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    Fin d → Matrix (Fin n) (Fin d × Fin n) ℝ :=
  gaussianCoherentLeakage y (gaussianCoherentGram_posDef_of_injective y hy)

theorem gaussianCoherentInjectiveLeakage_isCCRCompletion {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    IsCCRCompletion (gaussianCoherentCompression y)
      (gaussianCoherentInjectiveLeakage y hy) :=
  gaussianCoherentLeakage_isCCRCompletion y
    (gaussianCoherentGram_posDef_of_injective y hy)

/-- Every injective finite Euclidean configuration obeys the exact coherent pairwise CCR
dimension--fluctuation identity, with no positivity certificate among its hypotheses. -/
theorem gaussianCoherentInjective_dimension_fluctuation_pairwise_identity
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    (d : ℝ) * ((d : ℝ) + 1) *
        ((d : ℝ) * ccrMeanEnergy (gaussianCoherentCompression y) -
          ccrNumberVariance (gaussianCoherentCompression y)
            (gaussianCoherentInjectiveLeakage y hy)) =
      (d : ℝ) ^ 2 *
          ccrPairwiseMixedCommutatorEnergy (gaussianCoherentCompression y) +
        ccrScaledTracelessLeakageEnergy (gaussianCoherentCompression y)
          (gaussianCoherentInjectiveLeakage y hy) := by
  exact gaussianCoherent_dimension_fluctuation_pairwise_identity y
    (gaussianCoherentGram_posDef_of_injective y hy)

/-- For every injective finite Euclidean configuration in positive dimension, coherent number
variance is at most ambient dimension times coherent mean energy. -/
theorem gaussianCoherentInjective_numberVariance_le_dim_mul_mean
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) (hd : 0 < d) :
    ccrNumberVariance (gaussianCoherentCompression y)
        (gaussianCoherentInjectiveLeakage y hy) ≤
      (d : ℝ) * ccrMeanEnergy (gaussianCoherentCompression y) := by
  exact gaussianCoherent_numberVariance_le_dim_mul_mean y
    (gaussianCoherentGram_posDef_of_injective y hy) hd

/-! ### Literal log-determinant scale curvature -/

/-- Coherent Gaussian Gram matrix along logarithmic metric scale. -/
def gaussianCoherentLogScaleGram {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q => Real.exp (Real.exp s * coordinateDot y p q)

/-- First entrywise jet of the logarithmic-scale coherent Gram path. -/
def gaussianCoherentLogScaleFirst {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q => (Real.exp s * coordinateDot y p q) *
    gaussianCoherentLogScaleGram y s p q

/-- Second entrywise jet of the logarithmic-scale coherent Gram path. -/
def gaussianCoherentLogScaleSecond {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q =>
    ((Real.exp s * coordinateDot y p q) +
      (Real.exp s * coordinateDot y p q) ^ 2) *
        gaussianCoherentLogScaleGram y s p q

theorem hasDerivAt_gaussianCoherentLogScaleGram {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (s : ℝ) (p q : Fin n) :
    HasDerivAt (fun u => gaussianCoherentLogScaleGram y u p q)
      (gaussianCoherentLogScaleFirst y s p q) s := by
  have ha : HasDerivAt (fun u => Real.exp u * coordinateDot y p q)
      (Real.exp s * coordinateDot y p q) s :=
    (Real.hasDerivAt_exp s).mul_const _
  simpa [gaussianCoherentLogScaleGram, gaussianCoherentLogScaleFirst,
    mul_comm] using ha.exp

theorem hasDerivAt_gaussianCoherentLogScaleFirst {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (s : ℝ) (p q : Fin n) :
    HasDerivAt (fun u => gaussianCoherentLogScaleFirst y u p q)
      (gaussianCoherentLogScaleSecond y s p q) s := by
  have ha : HasDerivAt (fun u => Real.exp u * coordinateDot y p q)
      (Real.exp s * coordinateDot y p q) s :=
    (Real.hasDerivAt_exp s).mul_const _
  have he := hasDerivAt_gaussianCoherentLogScaleGram y s p q
  convert ha.mul he using 1
  simp only [gaussianCoherentLogScaleFirst, gaussianCoherentLogScaleSecond,
    gaussianCoherentLogScaleGram]
  ring

@[simp]
theorem gaussianCoherentLogScaleGram_zero {d n : ℕ}
    (y : Fin n → Fin d → ℝ) :
    gaussianCoherentLogScaleGram y 0 = gaussianCoherentGram y := by
  ext p q
  simp [gaussianCoherentLogScaleGram, gaussianCoherentGram]

/-- Logarithmic rescaling of an injective configuration preserves strict coherent Gram
positivity at every real scale. -/
theorem gaussianCoherentLogScaleGram_posDef_of_injective {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) (s : ℝ) :
    (gaussianCoherentLogScaleGram y s).PosDef := by
  let r : ℝ := Real.sqrt (Real.exp s)
  let ys : Fin n → Fin d → ℝ := fun p a => r * y p a
  have hr : r ≠ 0 := (Real.sqrt_pos.2 (Real.exp_pos s)).ne'
  have hys : Function.Injective ys := by
    intro p q hpq
    apply hy
    funext a
    exact mul_left_cancel₀ hr (congrFun hpq a)
  have hpath : gaussianCoherentLogScaleGram y s = gaussianCoherentGram ys := by
    ext p q
    simp only [gaussianCoherentLogScaleGram, gaussianCoherentGram]
    congr 1
    have hdot : coordinateDot ys p q = r ^ 2 * coordinateDot y p q := by
      unfold coordinateDot ys
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hdot, show r ^ 2 = Real.exp s by
      exact Real.sq_sqrt (Real.exp_pos s).le]
  rw [hpath]
  exact gaussianCoherentGram_posDef_of_injective ys hys

/-- The literal second derivative of the coherent log determinant at unit scale is its matrix
log-curvature jet. -/
theorem gaussianCoherentLogScale_logDet_secondDerivative_eq_gramLogCurvatureJet
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    deriv (deriv (fun s => Real.log (gaussianCoherentLogScaleGram y s).det)) 0 =
      gramLogCurvatureJet (gaussianCoherentLogScaleGram y 0)
        (gaussianCoherentLogScaleFirst y 0)
        (gaussianCoherentLogScaleSecond y 0) := by
  apply logDet_secondDerivative_eq_gramLogCurvatureJet
  · intro s p q
    exact hasDerivAt_gaussianCoherentLogScaleGram y s p q
  · intro s p q
    exact hasDerivAt_gaussianCoherentLogScaleFirst y s p q
  · exact Filter.Eventually.of_forall fun s =>
      (gaussianCoherentLogScaleGram_posDef_of_injective y hy s).det_pos.ne'

/-- First number-moment matrix in the nonorthonormal coherent basis. -/
def gaussianCoherentDegreeFirstMoment {d n : ℕ}
    (y : Fin n → Fin d → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, gaussianCoordinateDiagonal y i * gaussianCoherentGram y *
    gaussianCoordinateDiagonal y i

/-- Second number-moment matrix in the nonorthonormal coherent basis. -/
def gaussianCoherentDegreeSecondMoment {d n : ℕ}
    (y : Fin n → Fin d → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  gaussianCoherentDegreeFirstMoment y +
    ∑ i, ∑ j,
      (gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j) *
        gaussianCoherentGram y *
          (gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j)

@[simp]
theorem gaussianCoherentLogScaleFirst_zero {d n : ℕ}
    (y : Fin n → Fin d → ℝ) :
    gaussianCoherentLogScaleFirst y 0 = gaussianCoherentDegreeFirstMoment y := by
  ext p q
  simp only [gaussianCoherentLogScaleFirst, gaussianCoherentLogScaleGram,
    Real.exp_zero, one_mul, gaussianCoherentDegreeFirstMoment, Matrix.sum_apply]
  simp only [gaussianCoordinateDiagonal, gaussianCoherentGram,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  unfold coordinateDot
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp]
theorem gaussianCoherentLogScaleSecond_zero {d n : ℕ}
    (y : Fin n → Fin d → ℝ) :
    gaussianCoherentLogScaleSecond y 0 = gaussianCoherentDegreeSecondMoment y := by
  rw [show gaussianCoherentDegreeSecondMoment y =
      gaussianCoherentDegreeFirstMoment y +
        ∑ i, ∑ j,
          (gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j) *
            gaussianCoherentGram y *
              (gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j) by rfl]
  rw [← gaussianCoherentLogScaleFirst_zero]
  ext p q
  simp only [gaussianCoherentLogScaleSecond, gaussianCoherentLogScaleFirst,
    gaussianCoherentLogScaleGram, Real.exp_zero, one_mul, Matrix.add_apply,
    Matrix.sum_apply]
  simp only [gaussianCoordinateDiagonal, Matrix.diagonal_mul_diagonal,
    gaussianCoherentGram, Matrix.diagonal_mul, Matrix.mul_diagonal]
  unfold coordinateDot
  have hdouble :
      (∑ i, y p i * y q i) * (∑ j, y p j * y q j) *
          Real.exp (∑ s, y p s * y q s) =
        ∑ i, ∑ j,
          y p i * y p j * Real.exp (∑ s, y p s * y q s) *
            (y q i * y q j) := by
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← hdouble]
  ring

/-- Hilbert--Schmidt energy of a coherent square-root similarity is the corresponding
nonorthonormal Gram trace. -/
theorem matrixHilbertSchmidtEnergy_gaussianSimilarity {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.transpose = D) :
    matrixHilbertSchmidtEnergy
        (gaussianCoherentSqrt y * D * (gaussianCoherentSqrt y)⁻¹) =
      Matrix.trace ((gaussianCoherentGram y)⁻¹ * D *
        gaussianCoherentGram y * D) := by
  let R := gaussianCoherentSqrt y
  let Ri := (gaussianCoherentSqrt y)⁻¹
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff (gaussianCoherentGram y) hG.posSemidef.nonneg).mpr hG.isUnit
  letI : Invertible R := hRunit.nonempty_invertible.some
  have hR2 : R * R = gaussianCoherentGram y :=
    gaussianCoherentSqrt_mul_self y hG
  have hRi2 : Ri * Ri = (gaussianCoherentGram y)⁻¹ :=
    (gaussianCoherentGram_inv_eq_sqrt_inv_mul y hG).symm
  have htrans : (R * D * Ri).transpose = Ri * D * R := by
    dsimp [Ri, R]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      gaussianCoherentSqrt_transpose, hD]
    noncomm_ring
  rw [matrixHilbertSchmidtEnergy_eq_trace_transpose_mul, htrans]
  change Matrix.trace ((Ri * D * R) * (R * D * Ri)) =
    Matrix.trace ((gaussianCoherentGram y)⁻¹ * D * gaussianCoherentGram y * D)
  rw [← hRi2, ← hR2]
  calc
    Matrix.trace ((Ri * D * R) * (R * D * Ri)) =
        Matrix.trace ((Ri * D * (R * R) * D) * Ri) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (Ri * (Ri * D * (R * R) * D)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Ri * Ri) * D * (R * R) * D) := by
      congr 1
      noncomm_ring

/-- The coherent compression mean is the first logarithmic-scale Gram trace. -/
theorem ccrMeanEnergy_gaussianCoherentCompression_eq_trace {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    ccrMeanEnergy (gaussianCoherentCompression y) =
      Matrix.trace ((gaussianCoherentGram y)⁻¹ *
        gaussianCoherentDegreeFirstMoment y) := by
  unfold ccrMeanEnergy gaussianCoherentDegreeFirstMoment
  simp only [Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show gaussianCoherentCompression y i =
      gaussianCoherentSqrt y * gaussianCoordinateDiagonal y i *
        (gaussianCoherentSqrt y)⁻¹ by rfl]
  rw [matrixHilbertSchmidtEnergy_gaussianSimilarity y hG
    (gaussianCoordinateDiagonal y i) (gaussianCoordinateDiagonal_transpose y i)]
  congr 1
  noncomm_ring

/-- Products of coherent compressions are the square-root similarities of products of their
coordinate diagonals. -/
theorem gaussianCoherentCompression_mul {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) (i j : Fin d) :
    gaussianCoherentCompression y i * gaussianCoherentCompression y j =
      gaussianCoherentSqrt y *
        (gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j) *
          (gaussianCoherentSqrt y)⁻¹ := by
  have hRunit : IsUnit (gaussianCoherentSqrt y) :=
    (CFC.isUnit_sqrt_iff (gaussianCoherentGram y) hG.posSemidef.nonneg).mpr hG.isUnit
  letI : Invertible (gaussianCoherentSqrt y) := hRunit.nonempty_invertible.some
  have hcancel : (gaussianCoherentSqrt y)⁻¹ * gaussianCoherentSqrt y = 1 :=
    Matrix.inv_mul_of_invertible _
  unfold gaussianCoherentCompression
  calc
    (gaussianCoherentSqrt y * gaussianCoordinateDiagonal y i *
          (gaussianCoherentSqrt y)⁻¹) *
        (gaussianCoherentSqrt y * gaussianCoordinateDiagonal y j *
          (gaussianCoherentSqrt y)⁻¹) =
      gaussianCoherentSqrt y * gaussianCoordinateDiagonal y i *
        ((gaussianCoherentSqrt y)⁻¹ * gaussianCoherentSqrt y) *
          gaussianCoordinateDiagonal y j * (gaussianCoherentSqrt y)⁻¹ := by
            noncomm_ring
    _ = _ := by rw [hcancel]; noncomm_ring

/-- Quartic coherent degree moment. -/
def gaussianCoherentDegreeProductMoment {d n : ℕ}
    (y : Fin n → Fin d → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, ∑ j,
    (gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j) *
      gaussianCoherentGram y *
        (gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j)

theorem gaussianCoherentDegreeSecondMoment_eq_first_add_product {d n : ℕ}
    (y : Fin n → Fin d → ℝ) :
    gaussianCoherentDegreeSecondMoment y =
      gaussianCoherentDegreeFirstMoment y + gaussianCoherentDegreeProductMoment y := by
  rfl

/-- The product energy of the coherent compression is the quartic Gram trace. -/
theorem ccrProductEnergy_gaussianCoherentCompression_eq_trace {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    ccrProductEnergy (gaussianCoherentCompression y) =
      Matrix.trace ((gaussianCoherentGram y)⁻¹ *
        gaussianCoherentDegreeProductMoment y) := by
  unfold ccrProductEnergy gaussianCoherentDegreeProductMoment
  simp only [Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussianCoherentCompression_mul y hG i j]
  have hD :
      (gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j).transpose =
        gaussianCoordinateDiagonal y i * gaussianCoordinateDiagonal y j := by
    rw [Matrix.transpose_mul, gaussianCoordinateDiagonal_transpose,
      gaussianCoordinateDiagonal_transpose, gaussianCoordinateDiagonal_commutes]
  rw [matrixHilbertSchmidtEnergy_gaussianSimilarity y hG _ hD]
  congr 1
  noncomm_ring

/-- The column-energy matrix of a coherent compression is the square-root inverse congruence of
the first degree moment. -/
theorem ccrColumnEnergyMatrix_gaussianCoherentCompression {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    ccrColumnEnergyMatrix (gaussianCoherentCompression y) =
      (gaussianCoherentSqrt y)⁻¹ * gaussianCoherentDegreeFirstMoment y *
        (gaussianCoherentSqrt y)⁻¹ := by
  have hR2 := gaussianCoherentSqrt_mul_self y hG
  unfold ccrColumnEnergyMatrix gaussianCoherentDegreeFirstMoment
  calc
    ∑ i, (gaussianCoherentCompression y i).transpose *
        gaussianCoherentCompression y i =
      ∑ i, (gaussianCoherentSqrt y)⁻¹ *
        (gaussianCoordinateDiagonal y i * gaussianCoherentGram y *
          gaussianCoordinateDiagonal y i) * (gaussianCoherentSqrt y)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [gaussianCoherentCompression_transpose]
      unfold gaussianCoherentCompression
      rw [← hR2]
      noncomm_ring
    _ = (gaussianCoherentSqrt y)⁻¹ *
        (∑ i, gaussianCoordinateDiagonal y i * gaussianCoherentGram y *
          gaussianCoordinateDiagonal y i) * (gaussianCoherentSqrt y)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]

/-- The squared column-energy trace is the quadratic first-moment Gram trace. -/
theorem trace_sq_ccrColumnEnergyMatrix_gaussianCoherentCompression {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef) :
    Matrix.trace
        (ccrColumnEnergyMatrix (gaussianCoherentCompression y) *
          ccrColumnEnergyMatrix (gaussianCoherentCompression y)) =
      Matrix.trace
        ((gaussianCoherentGram y)⁻¹ * gaussianCoherentDegreeFirstMoment y *
          (gaussianCoherentGram y)⁻¹ * gaussianCoherentDegreeFirstMoment y) := by
  rw [ccrColumnEnergyMatrix_gaussianCoherentCompression y hG]
  let Ri := (gaussianCoherentSqrt y)⁻¹
  let M := gaussianCoherentDegreeFirstMoment y
  have hRi2 : Ri * Ri = (gaussianCoherentGram y)⁻¹ :=
    (gaussianCoherentGram_inv_eq_sqrt_inv_mul y hG).symm
  change Matrix.trace ((Ri * M * Ri) * (Ri * M * Ri)) =
    Matrix.trace ((gaussianCoherentGram y)⁻¹ * M *
      (gaussianCoherentGram y)⁻¹ * M)
  rw [← hRi2]
  calc
    Matrix.trace ((Ri * M * Ri) * (Ri * M * Ri)) =
        Matrix.trace ((Ri * M * (Ri * Ri) * M) * Ri) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (Ri * (Ri * M * (Ri * Ri) * M)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Ri * Ri) * M * (Ri * Ri) * M) := by
      congr 1
      noncomm_ring

/-- The coherent Gram log-curvature jet is exactly the CCR number variance for every completion. -/
theorem gramLogCurvatureJet_gaussianCoherent_eq_ccrNumberVariance
    {d n : ℕ} {m : Type*} [Fintype m]
    (y : Fin n → Fin d → ℝ) (hG : (gaussianCoherentGram y).PosDef)
    (B : Fin d → Matrix (Fin n) m ℝ)
    (hB : IsCCRCompletion (gaussianCoherentCompression y) B) :
    gramLogCurvatureJet (gaussianCoherentGram y)
        (gaussianCoherentDegreeFirstMoment y)
        (gaussianCoherentDegreeSecondMoment y) =
      ccrNumberVariance (gaussianCoherentCompression y) B := by
  rw [ccrNumberVariance_eq_mean_add_product_sub_columnSq
    (gaussianCoherentCompression y) B (gaussianCoherentCompression_commutes y hG) hB]
  rw [ccrMeanEnergy_gaussianCoherentCompression_eq_trace y hG,
    ccrProductEnergy_gaussianCoherentCompression_eq_trace y hG,
    trace_sq_ccrColumnEnergyMatrix_gaussianCoherentCompression y hG]
  unfold gramLogCurvatureJet
  rw [gaussianCoherentDegreeSecondMoment_eq_first_add_product]
  rw [Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add]

/-- The first logarithmic-scale derivative of the coherent log determinant is exactly the
coherent compression mean energy. -/
theorem gaussianCoherentLogScale_logDet_derivative_eq_ccrMeanEnergy
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    deriv (fun s => Real.log (gaussianCoherentLogScaleGram y s).det) 0 =
      ccrMeanEnergy (gaussianCoherentCompression y) := by
  have hG := gaussianCoherentGram_posDef_of_injective y hy
  have hdet : (gaussianCoherentLogScaleGram y 0).det ≠ 0 := by
    rw [gaussianCoherentLogScaleGram_zero]
    exact hG.det_pos.ne'
  have hlog := (hasDerivAt_matrixDet (gaussianCoherentLogScaleGram y)
    (gaussianCoherentLogScaleFirst y 0) 0
    (hasDerivAt_gaussianCoherentLogScaleGram y 0)).log hdet
  rw [hlog.deriv,
    detFirstJet_eq_det_mul_trace_inv_mul _ _ hdet]
  rw [gaussianCoherentLogScaleGram_zero, gaussianCoherentLogScaleFirst_zero]
  rw [← ccrMeanEnergy_gaussianCoherentCompression_eq_trace y hG]
  field_simp [hG.det_pos.ne']

/-- The second logarithmic-scale derivative of the coherent log determinant is exactly the
coherent CCR number variance. -/
theorem gaussianCoherentLogScale_logDet_secondDerivative_eq_ccrNumberVariance
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    deriv (deriv (fun s => Real.log (gaussianCoherentLogScaleGram y s).det)) 0 =
      ccrNumberVariance (gaussianCoherentCompression y)
        (gaussianCoherentInjectiveLeakage y hy) := by
  rw [gaussianCoherentLogScale_logDet_secondDerivative_eq_gramLogCurvatureJet y hy]
  rw [gaussianCoherentLogScaleGram_zero, gaussianCoherentLogScaleFirst_zero,
    gaussianCoherentLogScaleSecond_zero]
  exact gramLogCurvatureJet_gaussianCoherent_eq_ccrNumberVariance y
    (gaussianCoherentGram_posDef_of_injective y hy)
    (gaussianCoherentInjectiveLeakage y hy)
    (gaussianCoherentInjectiveLeakage_isCCRCompletion y hy)

/-- **Exact Gaussian dimension--curvature law at unit scale.**  The deficit between ambient
dimension times log-slope and log-curvature is a literal sum of the pairwise mixed-commutator and
traceless leakage energies. -/
theorem gaussianCoherentLogScale_dimension_curvature_sumOfSquares
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    (d : ℝ) * ((d : ℝ) + 1) *
        ((d : ℝ) *
            deriv (fun s => Real.log (gaussianCoherentLogScaleGram y s).det) 0 -
          deriv (deriv (fun s =>
            Real.log (gaussianCoherentLogScaleGram y s).det)) 0) =
      (d : ℝ) ^ 2 *
          ccrPairwiseMixedCommutatorEnergy (gaussianCoherentCompression y) +
        ccrScaledTracelessLeakageEnergy (gaussianCoherentCompression y)
          (gaussianCoherentInjectiveLeakage y hy) := by
  rw [gaussianCoherentLogScale_logDet_derivative_eq_ccrMeanEnergy y hy,
    gaussianCoherentLogScale_logDet_secondDerivative_eq_ccrNumberVariance y hy]
  exact gaussianCoherentInjective_dimension_fluctuation_pairwise_identity y hy

/-- The coherent Gaussian log-determinant curvature is nonnegative. -/
theorem gaussianCoherentLogScale_logDet_secondDerivative_nonneg
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    0 ≤ deriv (deriv (fun s =>
      Real.log (gaussianCoherentLogScaleGram y s).det)) 0 := by
  rw [gaussianCoherentLogScale_logDet_secondDerivative_eq_ccrNumberVariance y hy]
  exact rectangularMatrixHilbertSchmidtEnergy_nonneg _

/-- **Gaussian dimension--curvature upper bound at unit scale.** -/
theorem gaussianCoherentLogScale_logDet_secondDerivative_le_dim_mul_derivative
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) (hd : 0 < d) :
    deriv (deriv (fun s => Real.log (gaussianCoherentLogScaleGram y s).det)) 0 ≤
      (d : ℝ) * deriv (fun s =>
        Real.log (gaussianCoherentLogScaleGram y s).det) 0 := by
  rw [gaussianCoherentLogScale_logDet_derivative_eq_ccrMeanEnergy y hy,
    gaussianCoherentLogScale_logDet_secondDerivative_eq_ccrNumberVariance y hy]
  exact gaussianCoherentInjective_numberVariance_le_dim_mul_mean y hy hd

/-! ### Every logarithmic scale -/

/-- Configuration rescaling that moves logarithmic scale `s` to unit scale. -/
def gaussianLogScaleRescaledConfiguration {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (s : ℝ) : Fin n → Fin d → ℝ :=
  fun p a => Real.sqrt (Real.exp s) * y p a

theorem gaussianLogScaleRescaledConfiguration_injective {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) (s : ℝ) :
    Function.Injective (gaussianLogScaleRescaledConfiguration y s) := by
  have hr : Real.sqrt (Real.exp s) ≠ 0 :=
    (Real.sqrt_pos.2 (Real.exp_pos s)).ne'
  intro p q hpq
  apply hy
  funext a
  exact mul_left_cancel₀ hr (congrFun hpq a)

/-- Rescaling a configuration translates its coherent logarithmic-scale Gram path. -/
theorem gaussianCoherentLogScaleGram_rescaled {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (s u : ℝ) :
    gaussianCoherentLogScaleGram (gaussianLogScaleRescaledConfiguration y s) u =
      gaussianCoherentLogScaleGram y (u + s) := by
  ext p q
  simp only [gaussianCoherentLogScaleGram]
  congr 1
  have hr2 : Real.sqrt (Real.exp s) ^ 2 = Real.exp s :=
    Real.sq_sqrt (Real.exp_pos s).le
  have hdot :
      coordinateDot (gaussianLogScaleRescaledConfiguration y s) p q =
        Real.exp s * coordinateDot y p q := by
    unfold coordinateDot gaussianLogScaleRescaledConfiguration
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    calc
      (Real.sqrt (Real.exp s) * y p a) *
          (Real.sqrt (Real.exp s) * y q a) =
        Real.sqrt (Real.exp s) ^ 2 * (y p a * y q a) := by ring
      _ = Real.exp s * (y p a * y q a) := by rw [hr2]
  rw [hdot, Real.exp_add]
  ring

private theorem deriv_logDet_shift {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (s : ℝ) :
    deriv (fun u => Real.log
      (gaussianCoherentLogScaleGram (gaussianLogScaleRescaledConfiguration y s) u).det) 0 =
      deriv (fun u => Real.log (gaussianCoherentLogScaleGram y u).det) s := by
  let H : ℝ → ℝ := fun u => Real.log (gaussianCoherentLogScaleGram y u).det
  have hfun : (fun u => Real.log
      (gaussianCoherentLogScaleGram (gaussianLogScaleRescaledConfiguration y s) u).det) =
      fun u => H (u + s) := by
    funext u
    rw [gaussianCoherentLogScaleGram_rescaled]
  rw [hfun]
  simpa [H] using deriv_comp_add_const H s 0

private theorem secondDeriv_logDet_shift {d n : ℕ}
    (y : Fin n → Fin d → ℝ) (s : ℝ) :
    deriv (deriv (fun u => Real.log
      (gaussianCoherentLogScaleGram (gaussianLogScaleRescaledConfiguration y s) u).det)) 0 =
      deriv (deriv (fun u => Real.log (gaussianCoherentLogScaleGram y u).det)) s := by
  let H : ℝ → ℝ := fun u => Real.log (gaussianCoherentLogScaleGram y u).det
  have hfun : (fun u => Real.log
      (gaussianCoherentLogScaleGram (gaussianLogScaleRescaledConfiguration y s) u).det) =
      fun u => H (u + s) := by
    funext u
    rw [gaussianCoherentLogScaleGram_rescaled]
  rw [hfun]
  have hfirst : deriv (fun u => H (u + s)) = fun u => deriv H (u + s) := by
    funext u
    exact deriv_comp_add_const H s u
  rw [hfirst]
  simpa [H] using deriv_comp_add_const (deriv H) s 0

/-- **Exact Gaussian dimension--curvature law at every scale.** -/
theorem gaussianCoherentLogScale_dimension_curvature_sumOfSquares_at
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) (s : ℝ) :
    (d : ℝ) * ((d : ℝ) + 1) *
        ((d : ℝ) * deriv (fun u =>
            Real.log (gaussianCoherentLogScaleGram y u).det) s -
          deriv (deriv (fun u =>
            Real.log (gaussianCoherentLogScaleGram y u).det)) s) =
      (d : ℝ) ^ 2 * ccrPairwiseMixedCommutatorEnergy
          (gaussianCoherentCompression (gaussianLogScaleRescaledConfiguration y s)) +
        ccrScaledTracelessLeakageEnergy
          (gaussianCoherentCompression (gaussianLogScaleRescaledConfiguration y s))
          (gaussianCoherentInjectiveLeakage (gaussianLogScaleRescaledConfiguration y s)
            (gaussianLogScaleRescaledConfiguration_injective y hy s)) := by
  have h := gaussianCoherentLogScale_dimension_curvature_sumOfSquares
    (gaussianLogScaleRescaledConfiguration y s)
    (gaussianLogScaleRescaledConfiguration_injective y hy s)
  rw [deriv_logDet_shift y s, secondDeriv_logDet_shift y s] at h
  exact h

/-- Coherent Gaussian log-determinant curvature is nonnegative at every logarithmic scale. -/
theorem gaussianCoherentLogScale_logDet_secondDerivative_nonneg_at
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) (s : ℝ) :
    0 ≤ deriv (deriv (fun u =>
      Real.log (gaussianCoherentLogScaleGram y u).det)) s := by
  have h := gaussianCoherentLogScale_logDet_secondDerivative_nonneg
    (gaussianLogScaleRescaledConfiguration y s)
    (gaussianLogScaleRescaledConfiguration_injective y hy s)
  rw [secondDeriv_logDet_shift y s] at h
  exact h

/-- Coherent Gaussian log-determinant curvature is at most dimension times log-slope at every
logarithmic scale. -/
theorem gaussianCoherentLogScale_logDet_secondDerivative_le_dim_mul_derivative_at
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y)
    (hd : 0 < d) (s : ℝ) :
    deriv (deriv (fun u => Real.log (gaussianCoherentLogScaleGram y u).det)) s ≤
      (d : ℝ) * deriv (fun u =>
        Real.log (gaussianCoherentLogScaleGram y u).det) s := by
  have h := gaussianCoherentLogScale_logDet_secondDerivative_le_dim_mul_derivative
    (gaussianLogScaleRescaledConfiguration y s)
    (gaussianLogScaleRescaledConfiguration_injective y hy s) hd
  rw [deriv_logDet_shift y s, secondDeriv_logDet_shift y s] at h
  exact h

/-! ### Global scale geometry -/

/-- A reusable strengthened form of the matrix log-determinant curvature connector: the first
derivative function itself has the Gram log-curvature jet as its derivative. -/
theorem hasDerivAt_logDetDerivative_eq_gramLogCurvatureJet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : ℝ → Matrix ι ι ℝ) (x : ℝ)
    (hA : ∀ t i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ t i j, HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t)
    (hdet : ∀ᶠ t in nhds x, (A t).det ≠ 0) :
    HasDerivAt (deriv (fun t => Real.log (A t).det))
      (gramLogCurvatureJet (A x) (A₁ x) (A₂ x)) x := by
  have hdetDeriv (t : ℝ) := hasDerivAt_matrixDet A (A₁ t) t (hA t)
  have hdetx : (A x).det ≠ 0 := mem_of_mem_nhds hdet
  have hlogDeriv :
      (fun t => deriv (fun s => Real.log (A s).det) t) =ᶠ[nhds x]
        fun t => detFirstJet (A t) (A₁ t) / (A t).det := by
    filter_upwards [hdet] with t ht
    exact ((hdetDeriv t).log ht).deriv
  have hfirstJet :=
    hasDerivAt_matrixDetFirstJet A A₁ (A₂ x) x (hA x) (hA₁ x)
  have hratio := hfirstJet.div (hdetDeriv x) hdetx
  have hactual := hratio.congr_of_eventuallyEq hlogDeriv
  have hcurvature :=
    logDet_secondDerivative_eq_gramLogCurvatureJet A A₁ A₂ x hA hA₁ hdet
  have hcoeff :
      (detSecondJet (A x) (A₁ x) (A₂ x) * (A x).det -
          detFirstJet (A x) (A₁ x) * detFirstJet (A x) (A₁ x)) /
          (A x).det ^ 2 =
        gramLogCurvatureJet (A x) (A₁ x) (A₂ x) := by
    rw [← hcurvature]
    exact hactual.deriv.symm
  rw [← hcoeff]
  exact hactual

theorem hasDerivAt_gaussianCoherentLogScale_logDet
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) (s : ℝ) :
    HasDerivAt (fun u => Real.log (gaussianCoherentLogScaleGram y u).det)
      (deriv (fun u => Real.log (gaussianCoherentLogScaleGram y u).det) s) s := by
  apply DifferentiableAt.hasDerivAt
  have hdet := (gaussianCoherentLogScaleGram_posDef_of_injective y hy s).det_pos.ne'
  exact ((hasDerivAt_matrixDet (gaussianCoherentLogScaleGram y)
    (gaussianCoherentLogScaleFirst y s) s
    (hasDerivAt_gaussianCoherentLogScaleGram y s)).log hdet).differentiableAt

theorem hasDerivAt_gaussianCoherentLogScale_logDetDerivative
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) (s : ℝ) :
    HasDerivAt (deriv (fun u => Real.log (gaussianCoherentLogScaleGram y u).det))
      (deriv (deriv (fun u => Real.log (gaussianCoherentLogScaleGram y u).det)) s) s := by
  have hdet : ∀ᶠ u in nhds s, (gaussianCoherentLogScaleGram y u).det ≠ 0 :=
    Filter.Eventually.of_forall fun u =>
      (gaussianCoherentLogScaleGram_posDef_of_injective y hy u).det_pos.ne'
  have h := hasDerivAt_logDetDerivative_eq_gramLogCurvatureJet
    (gaussianCoherentLogScaleGram y) (gaussianCoherentLogScaleFirst y)
    (gaussianCoherentLogScaleSecond y) s
    (hasDerivAt_gaussianCoherentLogScaleGram y)
    (hasDerivAt_gaussianCoherentLogScaleFirst y) hdet
  convert h using 1
  exact (logDet_secondDerivative_eq_gramLogCurvatureJet
    (gaussianCoherentLogScaleGram y) (gaussianCoherentLogScaleFirst y)
    (gaussianCoherentLogScaleSecond y) s
    (hasDerivAt_gaussianCoherentLogScaleGram y)
    (hasDerivAt_gaussianCoherentLogScaleFirst y) hdet)

/-- The coherent Gaussian log determinant is globally convex in logarithmic metric scale. -/
theorem gaussianCoherentLogScale_logDet_convex
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) :
    ConvexOn ℝ Set.univ
      (fun s => Real.log (gaussianCoherentLogScaleGram y s).det) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
  · intro s _
    exact (hasDerivAt_gaussianCoherentLogScale_logDet y hy s).continuousAt.continuousWithinAt
  · intro s _
    exact (hasDerivAt_gaussianCoherentLogScale_logDet y hy s).hasDerivWithinAt
  · intro s _
    exact (hasDerivAt_gaussianCoherentLogScale_logDetDerivative y hy s).hasDerivWithinAt
  · intro s _
    exact gaussianCoherentLogScale_logDet_secondDerivative_nonneg_at y hy s

/-- Coherent log determinant in the ambient-dimension power coordinate
`u = exp(d * s)`. -/
def gaussianDimensionPowerLogDet (d : ℕ) {n : ℕ}
    (y : Fin n → Fin d → ℝ) (u : ℝ) : ℝ :=
  Real.log (gaussianCoherentLogScaleGram y (Real.log u / (d : ℝ))).det

/-- First derivative of the Gaussian ambient-dimension power reparametrization. -/
def gaussianDimensionPowerLogDetFirst (d : ℕ) {n : ℕ}
    (y : Fin n → Fin d → ℝ) (u : ℝ) : ℝ :=
  deriv (fun s => Real.log (gaussianCoherentLogScaleGram y s).det)
      (Real.log u / (d : ℝ)) /
    ((d : ℝ) * u)

/-- Second derivative of the Gaussian ambient-dimension power reparametrization. -/
def gaussianDimensionPowerLogDetSecond (d : ℕ) {n : ℕ}
    (y : Fin n → Fin d → ℝ) (u : ℝ) : ℝ :=
  (deriv (deriv (fun s => Real.log (gaussianCoherentLogScaleGram y s).det))
        (Real.log u / (d : ℝ)) -
      (d : ℝ) * deriv (fun s =>
        Real.log (gaussianCoherentLogScaleGram y s).det)
          (Real.log u / (d : ℝ))) /
    ((d : ℝ) ^ 2 * u ^ 2)

theorem hasDerivAt_gaussianDimensionPowerLogDet
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y)
    (hd : 0 < d) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (gaussianDimensionPowerLogDet d y)
      (gaussianDimensionPowerLogDetFirst d y u) u := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hg : HasDerivAt (fun v : ℝ => Real.log v / (d : ℝ))
      (1 / ((d : ℝ) * u)) u := by
    convert (Real.hasDerivAt_log hu.ne').div_const (d : ℝ) using 1
    field_simp [hd0, hu.ne']
  have hH := hasDerivAt_gaussianCoherentLogScale_logDet y hy
    (Real.log u / (d : ℝ))
  have hcomp := hH.comp u hg
  convert hcomp using 1
  simp only [gaussianDimensionPowerLogDetFirst]
  field_simp [hd0, hu.ne']

theorem hasDerivAt_gaussianDimensionPowerLogDetFirst
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y)
    (hd : 0 < d) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (gaussianDimensionPowerLogDetFirst d y)
      (gaussianDimensionPowerLogDetSecond d y u) u := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hu0 : u ≠ 0 := hu.ne'
  have hg : HasDerivAt (fun v : ℝ => Real.log v / (d : ℝ))
      (1 / ((d : ℝ) * u)) u := by
    convert (Real.hasDerivAt_log hu0).div_const (d : ℝ) using 1
    field_simp [hd0, hu0]
  have hH₁ := hasDerivAt_gaussianCoherentLogScale_logDetDerivative y hy
    (Real.log u / (d : ℝ))
  have hcomp := hH₁.comp u hg
  have hinv : HasDerivAt (fun v : ℝ => v⁻¹) (-1 / u ^ 2) u := by
    simpa using (hasDerivAt_id u).inv hu0
  have hscaled := (hinv.mul hcomp).const_mul (1 / (d : ℝ))
  convert hscaled using 1
  · funext v
    simp only [gaussianDimensionPowerLogDetFirst, Pi.mul_apply, Function.comp_apply,
      div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [gaussianDimensionPowerLogDetSecond]
    simp only [Function.comp_apply, div_eq_mul_inv]
    field_simp [hd0, hu0]
    ring

/-- **Global Gaussian dimension-power concavity.**  For every injective finite configuration in
positive ambient dimension, the coherent Gaussian log determinant is concave after the universal
change of metric scale `u = exp(d s)`. -/
theorem gaussianDimensionPowerLogDet_concaveOn
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y) (hd : 0 < d) :
    ConcaveOn ℝ (Set.Ioi 0) (gaussianDimensionPowerLogDet d y) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
  · intro u hu
    exact (hasDerivAt_gaussianDimensionPowerLogDet y hy hd hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu ⊢
    exact (hasDerivAt_gaussianDimensionPowerLogDet y hy hd hu).hasDerivWithinAt
  · intro u hu
    rw [interior_Ioi] at hu ⊢
    exact (hasDerivAt_gaussianDimensionPowerLogDetFirst y hy hd hu).hasDerivWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    unfold gaussianDimensionPowerLogDetSecond
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr
        (gaussianCoherentLogScale_logDet_secondDerivative_le_dim_mul_derivative_at
          y hy hd (Real.log u / (d : ℝ))))
      (mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg u))

/-- **Exact Gaussian power-curvature law.**  The negative curvature in the ambient-dimension
power coordinate is exactly the mixed-commutator energy plus the trace-free leakage energy of
the rescaled coherent compression. -/
theorem gaussianDimensionPowerLogDetSecond_sumOfSquares
    {d n : ℕ} (y : Fin n → Fin d → ℝ) (hy : Function.Injective y)
    (hd : 0 < d) {u : ℝ} (hu : 0 < u) :
    -((d : ℝ) ^ 3 * ((d : ℝ) + 1) * u ^ 2 *
        gaussianDimensionPowerLogDetSecond d y u) =
      (d : ℝ) ^ 2 * ccrPairwiseMixedCommutatorEnergy
          (gaussianCoherentCompression
            (gaussianLogScaleRescaledConfiguration y (Real.log u / (d : ℝ)))) +
        ccrScaledTracelessLeakageEnergy
          (gaussianCoherentCompression
            (gaussianLogScaleRescaledConfiguration y (Real.log u / (d : ℝ))))
          (gaussianCoherentInjectiveLeakage
            (gaussianLogScaleRescaledConfiguration y (Real.log u / (d : ℝ)))
            (gaussianLogScaleRescaledConfiguration_injective y hy
              (Real.log u / (d : ℝ)))) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hu0 : u ≠ 0 := hu.ne'
  have h := gaussianCoherentLogScale_dimension_curvature_sumOfSquares_at
    y hy (Real.log u / (d : ℝ))
  rw [← h]
  unfold gaussianDimensionPowerLogDetSecond
  field_simp [hd0, hu0]
  ring

/-! ### Intrinsic finite configurations in arbitrary real Hilbert spaces -/

section HilbertSpace

variable {n : ℕ} {E : Type*} [NeZero n]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Linear span of a finite configuration after centering.  Its dimension is the affine
dimension of the configuration. -/
def gaussianCenteredSpan (x : Fin n → E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i => x i - hilbertCentroid x)

/-- Intrinsic affine dimension of a finite Hilbert configuration. -/
def gaussianAffineDimension (x : Fin n → E) : ℕ :=
  Module.finrank ℝ (gaussianCenteredSpan x)

/-- A centered point regarded as an element of the finite centered span. -/
def gaussianCenteredSpanPoint (x : Fin n → E) (i : Fin n) : gaussianCenteredSpan x :=
  ⟨x i - hilbertCentroid x,
    Submodule.subset_span (Set.mem_range_self i)⟩

/-- Canonical finite orthonormal coordinates on the centered span. -/
def gaussianCenteredSpanCoordinates (x : Fin n → E) :
    Fin n → Fin (gaussianAffineDimension x) → ℝ := by
  letI : FiniteDimensional ℝ (gaussianCenteredSpan x) :=
    FiniteDimensional.span_of_finite ℝ
      (Set.finite_range fun i => x i - hilbertCentroid x)
  exact orthonormalCoordinates (gaussianCenteredSpanPoint x)

omit [NeZero n] in
theorem gaussianCenteredSpanCoordinates_eq_orthonormalCoordinates
    (x : Fin n → E) : by
    letI : FiniteDimensional ℝ (gaussianCenteredSpan x) :=
      FiniteDimensional.span_of_finite ℝ
        (Set.finite_range fun i => x i - hilbertCentroid x)
    exact gaussianCenteredSpanCoordinates x =
      orthonormalCoordinates (gaussianCenteredSpanPoint x) := by
  rfl

omit [NeZero n] in
theorem gaussianCenteredSpanPoint_injective
    (x : Fin n → E) (hx : Function.Injective x) :
    Function.Injective (gaussianCenteredSpanPoint x) := by
  intro i j hij
  apply hx
  have hval : x i - hilbertCentroid x = x j - hilbertCentroid x :=
    congrArg Subtype.val hij
  exact sub_left_injective hval

omit [NeZero n] in
theorem gaussianCenteredSpanCoordinates_injective
    (x : Fin n → E) (hx : Function.Injective x) :
    Function.Injective (gaussianCenteredSpanCoordinates x) := by
  letI : FiniteDimensional ℝ (gaussianCenteredSpan x) :=
    FiniteDimensional.span_of_finite ℝ
      (Set.finite_range fun i => x i - hilbertCentroid x)
  intro i j hij
  apply gaussianCenteredSpanPoint_injective x hx
  apply (stdOrthonormalBasis ℝ (gaussianCenteredSpan x)).repr.injective
  ext r
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have hr := congrFun hij r
  rw [gaussianCenteredSpanCoordinates_eq_orthonormalCoordinates] at hr
  unfold orthonormalCoordinates at hr
  simpa only [real_inner_comm] using hr

omit [NeZero n] in
/-- Two or more distinct Hilbert points have positive intrinsic affine dimension. -/
theorem gaussianAffineDimension_pos_of_injective
    (x : Fin n → E) (hx : Function.Injective x) (hn : 1 < n) :
    0 < gaussianAffineDimension x := by
  letI : FiniteDimensional ℝ (gaussianCenteredSpan x) :=
    FiniteDimensional.span_of_finite ℝ
      (Set.finite_range fun i => x i - hilbertCentroid x)
  let i : Fin n := ⟨0, Nat.zero_lt_of_lt hn⟩
  let j : Fin n := ⟨1, hn⟩
  have hij : i ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    simp [i, j] at hval
  have hxij : x i ≠ x j := fun h => hij (hx h)
  have hi : x i - hilbertCentroid x ∈ gaussianCenteredSpan x :=
    Submodule.subset_span (Set.mem_range_self i)
  have hj : x j - hilbertCentroid x ∈ gaussianCenteredSpan x :=
    Submodule.subset_span (Set.mem_range_self j)
  let v : gaussianCenteredSpan x :=
    ⟨(x i - hilbertCentroid x) - (x j - hilbertCentroid x),
      Submodule.sub_mem (gaussianCenteredSpan x) hi hj⟩
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨v, ?_⟩
  intro hv
  have hval := congrArg Subtype.val hv
  change (x i - hilbertCentroid x) - (x j - hilbertCentroid x) = 0 at hval
  apply hxij
  exact sub_left_injective (sub_eq_zero.mp hval)

omit [NeZero n] in
/-- The coherent log-scale coordinate Gram is the intrinsic centered Hilbert Gram. -/
theorem gaussianCoherentLogScaleGram_centeredSpanCoordinates
    (x : Fin n → E) (s : ℝ) :
    gaussianCoherentLogScaleGram (gaussianCenteredSpanCoordinates x) s =
      hilbertExponentialInnerMatrix (fun i => x i - hilbertCentroid x)
        (Real.exp s / 2) := by
  letI : FiniteDimensional ℝ (gaussianCenteredSpan x) :=
    FiniteDimensional.span_of_finite ℝ
      (Set.finite_range fun i => x i - hilbertCentroid x)
  calc
    gaussianCoherentLogScaleGram (gaussianCenteredSpanCoordinates x) s =
        coordinateExponentialInnerMatrix (gaussianCenteredSpanCoordinates x)
          (Real.exp s / 2) := by
      ext i j
      simp only [gaussianCoherentLogScaleGram, coordinateExponentialInnerMatrix]
      congr 1
      ring
    _ = hilbertExponentialInnerMatrix (gaussianCenteredSpanPoint x)
        (Real.exp s / 2) := by
      rw [gaussianCenteredSpanCoordinates_eq_orthonormalCoordinates]
      exact coordinateExponentialInnerMatrix_orthonormalCoordinates
        (gaussianCenteredSpanPoint x) (Real.exp s / 2)
    _ = hilbertExponentialInnerMatrix (fun i => x i - hilbertCentroid x)
        (Real.exp s / 2) := by
      ext i j
      rfl

/-- Canonical coherent coordinates in the metric normalization, absorbing the factor `2` in
the centered Gaussian gauge into the feature vectors. -/
def gaussianCenteredSpanMetricScaleCoordinates (x : Fin n → E) :
    Fin n → Fin (gaussianAffineDimension x) → ℝ :=
  gaussianLogScaleRescaledConfiguration (gaussianCenteredSpanCoordinates x) (Real.log 2)

omit [NeZero n] in
theorem gaussianCenteredSpanMetricScaleCoordinates_injective
    (x : Fin n → E) (hx : Function.Injective x) :
    Function.Injective (gaussianCenteredSpanMetricScaleCoordinates x) := by
  exact gaussianLogScaleRescaledConfiguration_injective
    (gaussianCenteredSpanCoordinates x)
    (gaussianCenteredSpanCoordinates_injective x hx) (Real.log 2)

omit [NeZero n] in
/-- In metric normalization, the coherent logarithmic parameter is exactly the logarithm of the
Gaussian inverse squared bandwidth, with no residual factor `2`. -/
theorem gaussianCoherentLogScaleGram_centeredSpanMetricScaleCoordinates
    (x : Fin n → E) (s : ℝ) :
    gaussianCoherentLogScaleGram (gaussianCenteredSpanMetricScaleCoordinates x) s =
      hilbertExponentialInnerMatrix (fun i => x i - hilbertCentroid x) (Real.exp s) := by
  unfold gaussianCenteredSpanMetricScaleCoordinates
  rw [gaussianCoherentLogScaleGram_rescaled]
  rw [gaussianCoherentLogScaleGram_centeredSpanCoordinates]
  congr 2
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

/-- Intrinsic corrected Gaussian log determinant in logarithmic metric scale. -/
def gaussianCorrectedLogScale (x : Fin n → E) (s : ℝ) : ℝ :=
  Real.log (gaussianCorrectedDeterminant x (Real.exp s))

/-- Intrinsic corrected Gaussian log determinant in its affine-dimension power scale. -/
def gaussianCorrectedDimensionPowerLogDet (x : Fin n → E) (u : ℝ) : ℝ :=
  gaussianCorrectedLogScale x
    (Real.log u / (gaussianAffineDimension x : ℝ))

omit [NeZero n] in
/-- On the positive half-line, the intrinsic power coordinate is literally
`u ↦ log Z(u^(1/d))` for the corrected Gaussian determinant `Z`. -/
theorem gaussianCorrectedDimensionPowerLogDet_eq_rpow
    (x : Fin n → E) {u : ℝ} (hu : 0 < u) :
    gaussianCorrectedDimensionPowerLogDet x u =
      Real.log (gaussianCorrectedDeterminant x
        (u ^ (1 / (gaussianAffineDimension x : ℝ) : ℝ))) := by
  unfold gaussianCorrectedDimensionPowerLogDet gaussianCorrectedLogScale
  rw [Real.rpow_def_of_pos hu]
  congr 3
  ring

omit [NeZero n] in
theorem gaussianCorrectedLogScale_eq_coordinateLogDet
    (x : Fin n → E) (s : ℝ) :
    gaussianCorrectedLogScale x s =
      Real.log
        (gaussianCoherentLogScaleGram
          (gaussianCenteredSpanMetricScaleCoordinates x) s).det := by
  classical
  unfold gaussianCorrectedLogScale
  rw [gaussianCorrectedDeterminant_eq_hilbertExponentialInnerMatrix_det]
  rw [gaussianCoherentLogScaleGram_centeredSpanMetricScaleCoordinates]
  congr 1
  congr 1

omit [NeZero n] in
/-- **Universal Hilbert metric dimension sandwich.**  For every injective finite configuration in
an arbitrary real Hilbert space with positive affine dimension, the centroid-corrected Gaussian
log determinant is convex in logarithmic metric scale and concave in the affine-dimension power
scale. -/
theorem gaussianCorrectedLogScale_convex_and_dimensionPower_concave
    (x : Fin n → E) (hx : Function.Injective x)
    (hd : 0 < gaussianAffineDimension x) :
    ConvexOn ℝ Set.univ (gaussianCorrectedLogScale x) ∧
      ConcaveOn ℝ (Set.Ioi 0) (gaussianCorrectedDimensionPowerLogDet x) := by
  let y := gaussianCenteredSpanMetricScaleCoordinates x
  have hy : Function.Injective y := gaussianCenteredSpanMetricScaleCoordinates_injective x hx
  have hlog : gaussianCorrectedLogScale x =
      fun s => Real.log (gaussianCoherentLogScaleGram y s).det := by
    funext s
    exact gaussianCorrectedLogScale_eq_coordinateLogDet x s
  constructor
  · rw [hlog]
    exact gaussianCoherentLogScale_logDet_convex
      (d := gaussianAffineDimension x) (n := n) y hy
  · have hpower : gaussianCorrectedDimensionPowerLogDet x =
        gaussianDimensionPowerLogDet (gaussianAffineDimension x) y := by
      funext u
      unfold gaussianCorrectedDimensionPowerLogDet gaussianDimensionPowerLogDet
      rw [gaussianCorrectedLogScale_eq_coordinateLogDet]
    rw [hpower]
    exact gaussianDimensionPowerLogDet_concaveOn
      (d := gaussianAffineDimension x) (n := n) y hy hd

omit [NeZero n] in
/-- Assumption-free nondegenerate form of the Hilbert metric dimension sandwich: pairwise
distinctness and at least two points discharge positivity of the intrinsic affine dimension. -/
theorem gaussianCorrectedLogScale_convex_and_dimensionPower_concave_of_card_gt_one
    (x : Fin n → E) (hx : Function.Injective x) (hn : 1 < n) :
    ConvexOn ℝ Set.univ (gaussianCorrectedLogScale x) ∧
      ConcaveOn ℝ (Set.Ioi 0) (gaussianCorrectedDimensionPowerLogDet x) :=
  gaussianCorrectedLogScale_convex_and_dimensionPower_concave x hx
    (gaussianAffineDimension_pos_of_injective x hx hn)

end HilbertSpace

end

end GaloisForLFunctions.HilbertMetric
