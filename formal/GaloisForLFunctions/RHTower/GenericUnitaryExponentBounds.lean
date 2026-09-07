import GaloisForLFunctions.RHTower.RealSphericalUnitarity

/-!
# Finite local exponent packets and positivity

This file combines the rank-one complementary-series positivity forms attached to a finite packet
of real exponents.  The resulting block-diagonal form is positive definite exactly when every
exponent lies in `(-1/2, 1/2)`.  Applying this to symmetric-power exponent packets turns the
generic-unitary strip condition into an explicit positivity certificate.

The theorem is a closed finite-dimensional calculation.  It does not assert that every generic
unitary representation supplies this quadratic form; that identification is the remaining local
classification step.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Orthogonal sum of the rank-one factorized forms attached to a finite exponent packet. -/
def localExponentPacketForm {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (v : ι → ℝ × ℝ) : ℝ :=
  ∑ i, rankOneKTypeForm (μ i) (v i)

/-- Positive-definiteness of the block form attached to a finite exponent packet. -/
def LocalExponentPacketPositive {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) : Prop :=
  ∀ v : ι → ℝ × ℝ, v ≠ 0 → 0 < localExponentPacketForm μ v

/-- An orthogonal sum of rank-one blocks is positive definite exactly when every block is. -/
theorem localExponentPacketPositive_iff_rankOne {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) :
    LocalExponentPacketPositive μ ↔ ∀ i, RankOneKTypePositive (μ i) := by
  classical
  constructor
  · intro h i w hw
    let v : ι → ℝ × ℝ := fun j ↦ if j = i then w else 0
    have hv : v ≠ 0 := by
      intro hvzero
      have hi := congr_fun hvzero i
      simp [v, hw] at hi
    have hp := h v hv
    have hpoint : ∀ j,
        rankOneKTypeForm (μ j) (v j) =
          if j = i then rankOneKTypeForm (μ i) w else 0 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp [v]
      · simp [v, hji, rankOneKTypeForm]
    simp only [localExponentPacketForm, hpoint] at hp
    simpa using hp
  · intro h v hv
    have hex : ∃ i, v i ≠ 0 := by
      by_contra hall
      apply hv
      funext i
      exact not_ne_iff.mp (not_exists.mp hall i)
    obtain ⟨i, hi⟩ := hex
    have hnonneg : ∀ j, 0 ≤ rankOneKTypeForm (μ j) (v j) := by
      intro j
      by_cases hj : v j = 0
      · simp [hj, rankOneKTypeForm]
      · exact (h j (v j) hj).le
    rw [localExponentPacketForm,
      Finset.sum_pos_iff_of_nonneg (fun j _ ↦ hnonneg j)]
    exact ⟨i, Finset.mem_univ i, h i (v i) hi⟩

/-- Exact coordinatewise half-strip criterion for a finite exponent packet. -/
theorem localExponentPacketPositive_iff {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) :
    LocalExponentPacketPositive μ ↔ ∀ i, |μ i| < 1 / 2 := by
  rw [localExponentPacketPositive_iff_rankOne]
  simp_rw [rankOneKTypePositive_iff]

/-- Every exponent in a finite packet supplies a unitarizable spherical rank-one model after the
normalization `s=2μ`. -/
def RankOneUnitarizableExponentPacket {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) : Prop :=
  ∀ i, 2 * μ i ∈ UnitarizableSphericalPrincipalParameter

/-- Closed generic exponent bound for packets certified by invariant rank-one Hermitian forms. -/
theorem rankOneUnitarizableExponentPacket_pointwise_bound {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) :
    RankOneUnitarizableExponentPacket μ → ∀ i, |μ i| < 1 / 2 := by
  intro h i
  rw [abs_lt]
  rcases unitarizableSphericalExponentParameter_subset (h i) with ⟨hleft, hright⟩
  constructor <;> linarith

/-- Rank-one unitarizability of every exponent makes the finite packet form positive definite. -/
theorem rankOneUnitarizableExponentPacket_implies_positive {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) :
    RankOneUnitarizableExponentPacket μ → LocalExponentPacketPositive μ := by
  intro h
  rw [localExponentPacketPositive_iff]
  exact rankOneUnitarizableExponentPacket_pointwise_bound μ h

/-- Positivity certificate for the degree-`d` symmetric-power exponent packet. -/
def SymmetricPowerLocalExponentPositive (ν : ℝ) (d : ℕ) : Prop :=
  LocalExponentPacketPositive (fun j : Fin (d + 1) ↦
    symmetricPowerArchimedeanExponent ν d j)

/-- The symmetric-power packet positivity certificate is exactly membership in the formalized
generic-unitary strip locus. -/
theorem symmetricPowerLocalExponentPositive_iff (ν : ℝ) (d : ℕ) :
    SymmetricPowerLocalExponentPositive ν d ↔ ν ∈ genericUnitarySymPowerLocus d := by
  rw [SymmetricPowerLocalExponentPositive, localExponentPacketPositive_iff]
  rfl

/-- Positive local certificates in every positive symmetric-power degree force exponent zero. -/
theorem all_degree_symmetricPowerLocalExponentPositive :
    {ν : ℝ | ∀ d : ℕ, SymmetricPowerLocalExponentPositive ν (d + 1)} = {0} := by
  calc
    {ν : ℝ | ∀ d : ℕ, SymmetricPowerLocalExponentPositive ν (d + 1)} =
        {ν : ℝ | ∀ d : ℕ, ν ∈ genericUnitarySymPowerLocus (d + 1)} := by
      ext ν
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h d
        exact (symmetricPowerLocalExponentPositive_iff ν (d + 1)).mp (h d)
      · intro h d
        exact (symmetricPowerLocalExponentPositive_iff ν (d + 1)).mpr (h d)
    _ = {0} := all_degree_genericUnitarySymPowerLocus

/-- Even-degree positive local certificates already force exponent zero. -/
theorem all_even_degree_symmetricPowerLocalExponentPositive :
    {ν : ℝ | ∀ d : ℕ, SymmetricPowerLocalExponentPositive ν (2 * (d + 1))} = {0} := by
  calc
    {ν : ℝ | ∀ d : ℕ, SymmetricPowerLocalExponentPositive ν (2 * (d + 1))} =
        {ν : ℝ | ∀ d : ℕ,
          ν ∈ genericUnitarySymPowerLocus (2 * (d + 1))} := by
      ext ν
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h d
        exact (symmetricPowerLocalExponentPositive_iff ν (2 * (d + 1))).mp (h d)
      · intro h d
        exact (symmetricPowerLocalExponentPositive_iff ν (2 * (d + 1))).mpr (h d)
    _ = {0} := all_even_degree_genericUnitarySymPowerLocus

/-- Every exponent in the degree-`d` symmetric-power packet supplies a unitarizable spherical
rank-one model after the normalization `s=2μ`. -/
def SymmetricPowerRankOneUnitarizable (ν : ℝ) (d : ℕ) : Prop :=
  RankOneUnitarizableExponentPacket (fun j : Fin (d + 1) ↦
    symmetricPowerArchimedeanExponent ν d j)

/-- Rank-one unitarizability for every exponent implies positivity of the packet form. -/
theorem symmetricPowerRankOneUnitarizable_implies_positive (ν : ℝ) (d : ℕ) :
    SymmetricPowerRankOneUnitarizable ν d →
      SymmetricPowerLocalExponentPositive ν d := by
  intro h
  exact rankOneUnitarizableExponentPacket_implies_positive _ h

/-- If every positive-degree symmetric-power packet passes the rank-one unitarity obstruction,
the original exponent is zero. -/
theorem all_degree_symmetricPowerRankOneUnitarizable_subset :
    {ν : ℝ | ∀ d : ℕ, SymmetricPowerRankOneUnitarizable ν (d + 1)} ⊆ {0} := by
  intro ν hν
  have hpositive : ∀ d : ℕ, SymmetricPowerLocalExponentPositive ν (d + 1) :=
    fun d ↦ symmetricPowerRankOneUnitarizable_implies_positive ν (d + 1) (hν d)
  have hmem : ν ∈ {ν : ℝ | ∀ d : ℕ,
      SymmetricPowerLocalExponentPositive ν (d + 1)} := hpositive
  rw [all_degree_symmetricPowerLocalExponentPositive] at hmem
  exact hmem

/-- Even symmetric-power degrees suffice for the rank-one unitarity obstruction. -/
theorem all_even_degree_symmetricPowerRankOneUnitarizable_subset :
    {ν : ℝ | ∀ d : ℕ,
      SymmetricPowerRankOneUnitarizable ν (2 * (d + 1))} ⊆ {0} := by
  intro ν hν
  have hpositive : ∀ d : ℕ,
      SymmetricPowerLocalExponentPositive ν (2 * (d + 1)) :=
    fun d ↦ symmetricPowerRankOneUnitarizable_implies_positive ν (2 * (d + 1)) (hν d)
  have hmem : ν ∈ {ν : ℝ | ∀ d : ℕ,
      SymmetricPowerLocalExponentPositive ν (2 * (d + 1))} := hpositive
  rw [all_even_degree_symmetricPowerLocalExponentPositive] at hmem
  exact hmem

end

end GaloisForLFunctions.RHTower
