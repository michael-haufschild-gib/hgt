import GaloisForLFunctions.RHTower.VonMangoldtGammaDepthOneCauchy
import GaloisForLFunctions.RHTower.VonMangoldtGammaPointedWardReconstruction

/-!
# Joint source Gram for the Julia and Gamma--Bianchi legs

The finite source-Julia Cauchy feature and the pointed Gamma--Bianchi raw feature are not two
unrelated positive models.  They use the same finite prime aperture and the same square-root
von Mangoldt mass.  This file places both feature families in one complex Euclidean prime carrier.

The resulting Gram has:

* the existing depth-one Julia/Cauchy Gram as its upper-left block;
* the complexification of the existing positive raw Bianchi Gram as its lower-right block;
* a forced mixed prime sum as its off-diagonal block.

Thus the finite cross term needed by a source colligation is canonical and the whole joint block
is positive semidefinite.  No critical factorial normalization, cofinal closability, Stinespring
defect identity, or RH statement is asserted here.
-/

open scoped BigOperators ComplexConjugate ComplexOrder

namespace RHTower

noncomputable section

/-- Coordinatewise complexification of a finite real source vector. -/
def finiteSourceVectorComplexification
    {P : Type*} [Fintype P] (v : EuclideanSpace ℝ P) : EuclideanSpace ℂ P :=
  WithLp.toLp 2 fun p => (v p : ℂ)

/-- Complexification preserves the finite Euclidean inner product exactly. -/
theorem inner_finiteSourceVectorComplexification
    {P : Type*} [Fintype P] (u v : EuclideanSpace ℝ P) :
    inner ℂ (finiteSourceVectorComplexification u)
        (finiteSourceVectorComplexification v) =
      (inner ℝ u v : ℂ) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [finiteSourceVectorComplexification, WithLp.ofLp_toLp,
    RCLike.inner_apply, conj_trivial, Complex.conj_ofReal]
  push_cast
  rfl

/-- Actual real raw Gamma--Bianchi feature on the aperture `{2, ..., M+1}`. -/
def finiteVonMangoldtGammaRawFeatureVector
    (M : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) (i : Fin n) :
    EuclideanSpace ℝ (Fin M) :=
  finiteExponentialGammaRawFeature
    (fun p : Fin M =>
      ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
    (fun p : Fin M => Real.log ((p : ℕ) + 2)) x a i

/-- Complex realization of the raw Gamma--Bianchi feature on the common prime carrier. -/
def finiteVonMangoldtGammaRawComplexVector
    (M : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) (i : Fin n) :
    EuclideanSpace ℂ (Fin M) :=
  finiteSourceVectorComplexification
    (finiteVonMangoldtGammaRawFeatureVector M x a i)

/-- The real feature vector is exactly the one whose Gram is
`finiteVonMangoldtGammaRawGram`. -/
theorem finiteVonMangoldtGammaRawFeatureVector_gram
    (M : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) (i j : Fin n) :
    inner ℝ (finiteVonMangoldtGammaRawFeatureVector M x a i)
        (finiteVonMangoldtGammaRawFeatureVector M x a j) =
      finiteVonMangoldtGammaRawGram M x a i j := by
  rfl

/-- Joint finite feature family.  The left summand is the Julia/Cauchy response and the right
summand is the pointed raw Bianchi response, both on the same prime coordinates. -/
def finiteVonMangoldtGammaJuliaBianchiJointVector
    (M : ℕ) {c b : ℕ} (w : Fin c → ℂ) (x : ℝ) (a : Fin b → ℕ) :
    Fin c ⊕ Fin b → EuclideanSpace ℂ (Fin M) :=
  Sum.elim
    (fun i => finiteExponentialDepthOneCauchyVector
      (fun p : Fin M => finiteVonMangoldtDepthOneAmplitude ((p : ℕ) + 2))
      (fun p : Fin M => finiteVonMangoldtFrequency ((p : ℕ) + 2)) (w i))
    (finiteVonMangoldtGammaRawComplexVector M x a)

/-- Canonical joint source Gram of the Julia and Bianchi feature legs. -/
def finiteVonMangoldtGammaJuliaBianchiJointGram
    (M : ℕ) {c b : ℕ} (w : Fin c → ℂ) (x : ℝ) (a : Fin b → ℕ) :
    Matrix (Fin c ⊕ Fin b) (Fin c ⊕ Fin b) ℂ :=
  Matrix.gram ℂ (finiteVonMangoldtGammaJuliaBianchiJointVector M w x a)

/-- The Julia--Julia block is exactly the existing depth-one von Mangoldt Cauchy Gram. -/
theorem finiteVonMangoldtGammaJuliaBianchiJointGram_inl_inl
    (M : ℕ) {c b : ℕ} (w : Fin c → ℂ) (x : ℝ) (a : Fin b → ℕ)
    (i j : Fin c) :
    finiteVonMangoldtGammaJuliaBianchiJointGram M w x a (Sum.inl i) (Sum.inl j) =
      finiteVonMangoldtDepthOneCauchyGram M w i j := by
  rfl

/-- The Bianchi--Bianchi block is the exact complexification of the existing positive raw Gram. -/
theorem finiteVonMangoldtGammaJuliaBianchiJointGram_inr_inr
    (M : ℕ) {c b : ℕ} (w : Fin c → ℂ) (x : ℝ) (a : Fin b → ℕ)
    (i j : Fin b) :
    finiteVonMangoldtGammaJuliaBianchiJointGram M w x a (Sum.inr i) (Sum.inr j) =
      (finiteVonMangoldtGammaRawGram M x a i j : ℂ) := by
  rw [finiteVonMangoldtGammaJuliaBianchiJointGram, Matrix.gram_apply]
  change inner ℂ
      (finiteSourceVectorComplexification
        (finiteVonMangoldtGammaRawFeatureVector M x a i))
      (finiteSourceVectorComplexification
        (finiteVonMangoldtGammaRawFeatureVector M x a j)) = _
  rw [inner_finiteSourceVectorComplexification,
    finiteVonMangoldtGammaRawFeatureVector_gram]

/-- Explicit mixed source term forced by the common prime carrier. -/
def finiteVonMangoldtGammaJuliaBianchiCross
    (M : ℕ) {c b : ℕ} (w : Fin c → ℂ) (x : ℝ) (a : Fin b → ℕ)
    (i : Fin c) (j : Fin b) : ℂ :=
  ∑ p : Fin M,
    ((finiteVonMangoldtGammaRawFeatureVector M x a j p : ℝ) : ℂ) *
      finiteVonMangoldtDepthOneCauchyFeature (w i) ((p : ℕ) + 2)

/-- The upper-right block is the explicit mixed prime sum; there is no free cross-term choice. -/
theorem finiteVonMangoldtGammaJuliaBianchiJointGram_inl_inr
    (M : ℕ) {c b : ℕ} (w : Fin c → ℂ) (x : ℝ) (a : Fin b → ℕ)
    (i : Fin c) (j : Fin b) :
    finiteVonMangoldtGammaJuliaBianchiJointGram M w x a (Sum.inl i) (Sum.inr j) =
      finiteVonMangoldtGammaJuliaBianchiCross M w x a i j := by
  rw [finiteVonMangoldtGammaJuliaBianchiJointGram, Matrix.gram_apply,
    PiLp.inner_apply]
  simp only [finiteVonMangoldtGammaJuliaBianchiJointVector, Sum.elim_inl,
    Sum.elim_inr, finiteVonMangoldtGammaRawComplexVector,
    finiteSourceVectorComplexification, finiteExponentialDepthOneCauchyVector,
    WithLp.ofLp_toLp, RCLike.inner_apply]
  rw [finiteVonMangoldtGammaJuliaBianchiCross]
  apply Finset.sum_congr rfl
  intro p hp
  rw [starRingEnd_apply, star_star]
  unfold finiteVonMangoldtDepthOneCauchyFeature
  rfl

/-- The lower-left block is forced by Hermitian symmetry of the same joint carrier. -/
theorem finiteVonMangoldtGammaJuliaBianchiJointGram_inr_inl
    (M : ℕ) {c b : ℕ} (w : Fin c → ℂ) (x : ℝ) (a : Fin b → ℕ)
    (i : Fin c) (j : Fin b) :
    finiteVonMangoldtGammaJuliaBianchiJointGram M w x a (Sum.inr j) (Sum.inl i) =
      star (finiteVonMangoldtGammaJuliaBianchiCross M w x a i j) := by
  rw [finiteVonMangoldtGammaJuliaBianchiJointGram, Matrix.gram_apply]
  rw [← finiteVonMangoldtGammaJuliaBianchiJointGram_inl_inr M w x a i j]
  rw [finiteVonMangoldtGammaJuliaBianchiJointGram, Matrix.gram_apply]
  exact (inner_conj_symm
    (finiteVonMangoldtGammaJuliaBianchiJointVector M w x a (Sum.inr j))
    (finiteVonMangoldtGammaJuliaBianchiJointVector M w x a (Sum.inl i))).symm

/-- **Finite source-Julia/Bianchi colligation positivity.**  Every joint packet, with its forced
mixed source terms, is positive semidefinite before critical normalization or passage to a cofinal
aperture. -/
theorem finiteVonMangoldtGammaJuliaBianchiJointGram_posSemidef
    (M : ℕ) {c b : ℕ} (w : Fin c → ℂ) (x : ℝ) (a : Fin b → ℕ) :
    (finiteVonMangoldtGammaJuliaBianchiJointGram M w x a).PosSemidef :=
  Matrix.posSemidef_gram ℂ _

end

end RHTower
