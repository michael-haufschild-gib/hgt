import GaloisForLFunctions.HilbertMetric.GaussianFock
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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
open scoped BigOperators RealInnerProductSpace

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
    · filter_upwards with h hh
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
  filter_upwards with h hh
  dsimp [A, B, C, E]
  field_simp [hh]
  rw [Real.exp_add, Real.exp_add]
  ring

end

end GaloisForLFunctions.HilbertMetric
