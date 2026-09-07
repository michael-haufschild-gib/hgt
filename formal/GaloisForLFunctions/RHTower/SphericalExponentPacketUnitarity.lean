import GaloisForLFunctions.RHTower.GenericUnitaryExponentBounds
import Mathlib.Data.Complex.BigOperators

/-!
# Positive invariant forms on finite spherical exponent packets

For a finite real exponent packet `μᵢ`, this file puts the explicit spherical rank-one
Harish-Chandra modules into one product representation.  It constructs the coordinatewise
raising/lowering operators and the orthogonal sum of complementary-series Hermitian forms.

Restriction to one coordinate proves necessity of every bound `|μᵢ| < 1/2`; the explicit
orthogonal form proves sufficiency.  Thus existence of one positive invariant Hermitian form on
the full packet is equivalent to the pointwise generic half-strip.  Applied to symmetric-power
packets, every positive degree, or only every even degree, has exact locus `{0}`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Product of the spherical rank-one Harish-Chandra models indexed by a finite exponent packet. -/
abbrev SphericalExponentPacketModel (ι : Type*) := ι → SphericalKFiniteModel

/-- Coordinatewise raising operator for an exponent packet in normalization `sᵢ = 2μᵢ`. -/
def sphericalExponentPacketE {ι : Type*} (μ : ι → ℝ) :
    Module.End ℂ (SphericalExponentPacketModel ι) where
  toFun v i := sphericalPrincipalE ((2 * μ i : ℝ) : ℂ) (v i)
  map_add' v w := by ext i m; simp
  map_smul' c v := by ext i m; simp

/-- Coordinatewise lowering operator for an exponent packet in normalization `sᵢ = 2μᵢ`. -/
def sphericalExponentPacketF {ι : Type*} (μ : ι → ℝ) :
    Module.End ℂ (SphericalExponentPacketModel ι) where
  toFun v i := sphericalPrincipalF ((2 * μ i : ℝ) : ℂ) (v i)
  map_add' v w := by ext i m; simp
  map_smul' c v := by ext i m; simp

@[simp]
theorem sphericalExponentPacketE_apply {ι : Type*} (μ : ι → ℝ)
    (v : SphericalExponentPacketModel ι) (i : ι) :
    sphericalExponentPacketE μ v i = sphericalPrincipalE ((2 * μ i : ℝ) : ℂ) (v i) := rfl

@[simp]
theorem sphericalExponentPacketF_apply {ι : Type*} (μ : ι → ℝ)
    (v : SphericalExponentPacketModel ι) (i : ι) :
    sphericalExponentPacketF μ v i = sphericalPrincipalF ((2 * μ i : ℝ) : ℂ) (v i) := rfl

/-- Orthogonal sum of Hermitian forms on the coordinate models. -/
def orthogonalSumHermitianForm {ι : Type*} [Fintype ι]
    (B : ι → ComplexHermitianForm SphericalKFiniteModel) :
    ComplexHermitianForm (SphericalExponentPacketModel ι) :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun v w ↦ ∑ i, B i (v i) (w i))
    (by intro v₁ v₂ w; simp [Finset.sum_add_distrib])
    (by intro c v w; simp [← Finset.mul_sum])
    (by intro v w₁ w₂; simp [Finset.sum_add_distrib])
    (by intro c v w; simp [← Finset.mul_sum])

@[simp]
theorem orthogonalSumHermitianForm_apply {ι : Type*} [Fintype ι]
    (B : ι → ComplexHermitianForm SphericalKFiniteModel)
    (v w : SphericalExponentPacketModel ι) :
    orthogonalSumHermitianForm B v w = ∑ i, B i (v i) (w i) := rfl

theorem orthogonalSumHermitianForm_isSymm {ι : Type*} [Fintype ι]
    (B : ι → ComplexHermitianForm SphericalKFiniteModel)
    (hB : ∀ i, (B i).IsSymm) :
    (orthogonalSumHermitianForm B).IsSymm := by
  refine ⟨?_⟩
  intro v w
  rw [orthogonalSumHermitianForm_apply, orthogonalSumHermitianForm_apply,
    starRingEnd_apply, star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hB i).eq (v i) (w i)

theorem orthogonalSumHermitianForm_self_re {ι : Type*} [Fintype ι]
    (B : ι → ComplexHermitianForm SphericalKFiniteModel)
    (v : SphericalExponentPacketModel ι) :
    (orthogonalSumHermitianForm B v v).re = ∑ i, (B i (v i) (v i)).re := by
  rw [orthogonalSumHermitianForm_apply, Complex.re_sum]

theorem orthogonalSumHermitianForm_positiveDefinite {ι : Type*} [Fintype ι]
    (B : ι → ComplexHermitianForm SphericalKFiniteModel)
    (hB : ∀ i, IsPositiveDefiniteHermitian (B i)) :
    IsPositiveDefiniteHermitian (orthogonalSumHermitianForm B) := by
  classical
  constructor
  · exact orthogonalSumHermitianForm_isSymm B (fun i ↦ (hB i).1)
  · intro v hv
    rw [orthogonalSumHermitianForm_self_re]
    apply Finset.sum_pos'
    · intro i hi
      by_cases hvi : v i = 0
      · simp [hvi]
      · exact ((hB i).2 (v i) hvi).le
    · have hex : ∃ i, v i ≠ 0 := by
        by_contra h
        apply hv
        funext i
        exact not_ne_iff.mp (not_exists.mp h i)
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_univ i, (hB i).2 (v i) hi⟩

/-- Inclusion of one spherical factor into the full packet model. -/
def sphericalExponentPacketEmbedding {ι : Type*} [Fintype ι] (i : ι) :
    SphericalKFiniteModel →ₗ[ℂ] SphericalExponentPacketModel ι := by
  classical
  exact LinearMap.single ℂ (fun _ : ι ↦ SphericalKFiniteModel) i

@[simp]
theorem sphericalExponentPacketEmbedding_same {ι : Type*} [Fintype ι]
    (i : ι) (v : SphericalKFiniteModel) :
    sphericalExponentPacketEmbedding i v i = v := by
  classical
  simp [sphericalExponentPacketEmbedding]

theorem sphericalExponentPacketEmbedding_ne_zero {ι : Type*} [Fintype ι]
    (i : ι) {v : SphericalKFiniteModel} (hv : v ≠ 0) :
    sphericalExponentPacketEmbedding i v ≠ 0 := by
  intro hzero
  have hi := congr_fun hzero i
  simp only [sphericalExponentPacketEmbedding_same] at hi
  exact hv hi

@[simp]
theorem sphericalExponentPacketE_embedding {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (i : ι) (v : SphericalKFiniteModel) :
    sphericalExponentPacketE μ (sphericalExponentPacketEmbedding i v) =
      sphericalExponentPacketEmbedding i
        (sphericalPrincipalE ((2 * μ i : ℝ) : ℂ) v) := by
  classical
  ext j m
  by_cases hji : j = i
  · subst j
    simp
  · simp [sphericalExponentPacketEmbedding, hji]

@[simp]
theorem sphericalExponentPacketF_embedding {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (i : ι) (v : SphericalKFiniteModel) :
    sphericalExponentPacketF μ (sphericalExponentPacketEmbedding i v) =
      sphericalExponentPacketEmbedding i
        (sphericalPrincipalF ((2 * μ i : ℝ) : ℂ) v) := by
  classical
  ext j m
  by_cases hji : j = i
  · subst j
    simp
  · simp [sphericalExponentPacketEmbedding, hji]

/-- Restriction of a packet Hermitian form to one coordinate factor. -/
def restrictPacketHermitianForm {ι : Type*} [Fintype ι]
    (B : ComplexHermitianForm (SphericalExponentPacketModel ι)) (i : ι) :
    ComplexHermitianForm SphericalKFiniteModel :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun v w ↦ B (sphericalExponentPacketEmbedding i v)
      (sphericalExponentPacketEmbedding i w))
    (by intro v₁ v₂ w; simp)
    (by intro c v w; simp)
    (by intro v w₁ w₂; simp)
    (by intro c v w; simp)

@[simp]
theorem restrictPacketHermitianForm_apply {ι : Type*} [Fintype ι]
    (B : ComplexHermitianForm (SphericalExponentPacketModel ι)) (i : ι)
    (v w : SphericalKFiniteModel) :
    restrictPacketHermitianForm B i v w =
      B (sphericalExponentPacketEmbedding i v) (sphericalExponentPacketEmbedding i w) := rfl

theorem restrictPacketHermitianForm_positiveDefinite {ι : Type*} [Fintype ι]
    (B : ComplexHermitianForm (SphericalExponentPacketModel ι))
    (hB : IsPositiveDefiniteHermitian B) (i : ι) :
    IsPositiveDefiniteHermitian (restrictPacketHermitianForm B i) := by
  constructor
  · exact ⟨fun v w ↦ hB.1.eq _ _⟩
  · intro v hv
    exact hB.2 _ (sphericalExponentPacketEmbedding_ne_zero i hv)

/-- Infinitesimal invariance of a packet form under all coordinate raising/lowering operators. -/
def IsSphericalExponentPacketInvariant {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (B : ComplexHermitianForm (SphericalExponentPacketModel ι)) : Prop :=
  ∀ v w, B (sphericalExponentPacketE μ v) w =
    -B v (sphericalExponentPacketF μ w)

theorem restrictPacketHermitianForm_invariant {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (B : ComplexHermitianForm (SphericalExponentPacketModel ι))
    (hB : IsSphericalExponentPacketInvariant μ B) (i : ι) :
    IsSphericalPrincipalInvariant (2 * μ i) (restrictPacketHermitianForm B i) := by
  intro v w
  have h := hB (sphericalExponentPacketEmbedding i v)
    (sphericalExponentPacketEmbedding i w)
  simpa using h

/-- Exponent packets admitting one positive-definite invariant form on the full product model. -/
def UnitarizableSphericalExponentPacket {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) : Prop :=
  ∃ B : ComplexHermitianForm (SphericalExponentPacketModel ι),
    IsPositiveDefiniteHermitian B ∧ IsSphericalExponentPacketInvariant μ B

/-- Any invariant positive form on the full packet restricts to each rank-one factor. -/
theorem unitarizableSphericalExponentPacket_pointwise_bound {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) :
    UnitarizableSphericalExponentPacket μ → ∀ i, |μ i| < 1 / 2 := by
  rintro ⟨B, hpos, hinv⟩ i
  have hi : 2 * μ i ∈ UnitarizableSphericalPrincipalParameter :=
    ⟨restrictPacketHermitianForm B i,
      restrictPacketHermitianForm_positiveDefinite B hpos i,
      restrictPacketHermitianForm_invariant μ B hinv i⟩
  have hi' : μ i ∈ Set.Ioo (-1 / 2) (1 / 2) := by
    rw [← unitarizableSphericalExponentParameter_eq_Ioo]
    exact hi
  rw [abs_lt]
  constructor <;> linarith [hi'.1, hi'.2]

/-- Explicit orthogonal complementary-series form on the full exponent-packet model. -/
def sphericalComplementaryPacketHermitianForm {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) : ComplexHermitianForm (SphericalExponentPacketModel ι) :=
  orthogonalSumHermitianForm (fun i ↦ sphericalComplementaryHermitianForm (2 * μ i))

theorem two_mul_abs_lt_one {x : ℝ} (hx : |x| < 1 / 2) : |2 * x| < 1 := by
  rw [abs_mul]
  norm_num
  linarith

/-- Pointwise half-strip bounds make the explicit packet form positive definite. -/
theorem sphericalComplementaryPacketHermitianForm_positiveDefinite
    {ι : Type*} [Fintype ι] (μ : ι → ℝ) (hμ : ∀ i, |μ i| < 1 / 2) :
    IsPositiveDefiniteHermitian (sphericalComplementaryPacketHermitianForm μ) := by
  exact orthogonalSumHermitianForm_positiveDefinite _ fun i ↦
    sphericalComplementaryHermitianForm_positiveDefinite (2 * μ i)
      (two_mul_abs_lt_one (hμ i))

/-- Pointwise half-strip bounds make the explicit packet form invariant. -/
theorem sphericalComplementaryPacketHermitianForm_invariant
    {ι : Type*} [Fintype ι] (μ : ι → ℝ) (hμ : ∀ i, |μ i| < 1 / 2) :
    IsSphericalExponentPacketInvariant μ (sphericalComplementaryPacketHermitianForm μ) := by
  intro v w
  rw [sphericalComplementaryPacketHermitianForm,
    orthogonalSumHermitianForm_apply, orthogonalSumHermitianForm_apply]
  calc
    ∑ i, sphericalComplementaryHermitianForm (2 * μ i)
        (sphericalPrincipalE ((2 * μ i : ℝ) : ℂ) (v i)) (w i) =
      ∑ i, -sphericalComplementaryHermitianForm (2 * μ i) (v i)
        (sphericalPrincipalF ((2 * μ i : ℝ) : ℂ) (w i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sphericalComplementaryHermitianForm_invariant (2 * μ i)
        (two_mul_abs_lt_one (hμ i)) (v i) (w i)
    _ = -(∑ i, sphericalComplementaryHermitianForm (2 * μ i) (v i)
        (sphericalPrincipalF ((2 * μ i : ℝ) : ℂ) (w i))) := by
      rw [Finset.sum_neg_distrib]

/-- Exact generic half-strip criterion for one positive invariant form on the full packet. -/
theorem unitarizableSphericalExponentPacket_iff {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) :
    UnitarizableSphericalExponentPacket μ ↔ ∀ i, |μ i| < 1 / 2 := by
  constructor
  · exact unitarizableSphericalExponentPacket_pointwise_bound μ
  · intro hμ
    exact ⟨sphericalComplementaryPacketHermitianForm μ,
      sphericalComplementaryPacketHermitianForm_positiveDefinite μ hμ,
      sphericalComplementaryPacketHermitianForm_invariant μ hμ⟩

/-- One positive invariant form on the full degree-`d` symmetric-power packet model. -/
def SymmetricPowerSphericalPacketUnitarizable (ν : ℝ) (d : ℕ) : Prop :=
  UnitarizableSphericalExponentPacket (fun j : Fin (d + 1) ↦
    symmetricPowerArchimedeanExponent ν d j)

/-- Exact fixed-degree spherical packet unitarity locus. -/
theorem symmetricPowerSphericalPacketUnitarizable_iff (ν : ℝ) (d : ℕ) :
    SymmetricPowerSphericalPacketUnitarizable ν d ↔
      ν ∈ genericUnitarySymPowerLocus d := by
  rw [SymmetricPowerSphericalPacketUnitarizable,
    unitarizableSphericalExponentPacket_iff]
  rfl

/-- Full product-model unitarizability in every positive symmetric-power degree has locus `{0}`. -/
theorem all_degree_symmetricPowerSphericalPacketUnitarizable :
    {ν : ℝ | ∀ d : ℕ, SymmetricPowerSphericalPacketUnitarizable ν (d + 1)} = {0} := by
  calc
    {ν : ℝ | ∀ d : ℕ, SymmetricPowerSphericalPacketUnitarizable ν (d + 1)} =
        {ν : ℝ | ∀ d : ℕ, ν ∈ genericUnitarySymPowerLocus (d + 1)} := by
      ext ν
      simp only [Set.mem_setOf_eq]
      exact forall_congr' fun d ↦
        symmetricPowerSphericalPacketUnitarizable_iff ν (d + 1)
    _ = {0} := all_degree_genericUnitarySymPowerLocus

/-- Even degrees suffice for the exact full product-model unitarity locus `{0}`. -/
theorem all_even_degree_symmetricPowerSphericalPacketUnitarizable :
    {ν : ℝ | ∀ d : ℕ,
      SymmetricPowerSphericalPacketUnitarizable ν (2 * (d + 1))} = {0} := by
  calc
    {ν : ℝ | ∀ d : ℕ,
        SymmetricPowerSphericalPacketUnitarizable ν (2 * (d + 1))} =
        {ν : ℝ | ∀ d : ℕ,
          ν ∈ genericUnitarySymPowerLocus (2 * (d + 1))} := by
      ext ν
      simp only [Set.mem_setOf_eq]
      exact forall_congr' fun d ↦
        symmetricPowerSphericalPacketUnitarizable_iff ν (2 * (d + 1))
    _ = {0} := all_even_degree_genericUnitarySymPowerLocus

end
end GaloisForLFunctions.RHTower
