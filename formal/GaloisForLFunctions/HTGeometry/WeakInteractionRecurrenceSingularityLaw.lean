import GaloisForLFunctions.HTGeometry.ArithmeticTemporalRankInstability
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import GaloisForLFunctions.HTGeometry.LocalTemporalConstraintCausalityLaw
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality
import GaloisForLFunctions.HTGeometry.ResolvedRecurrenceRelationCompletenessLaw
import GaloisForLFunctions.RHTower.LocalHamiltonianCausalHorizonLaw

/-!
# Weak-interaction recurrence singularity

Every finite diagonal Hamiltonian admits an arbitrarily small Hermitian
joint perturbation whose spectrum has maximal projective rational rank.
The perturbed system therefore explores its full projective phase torus and
attains the unavoidable collision floor at every replica order.

At the same time, the dimension-free `C⋆` Duhamel law makes every
operator-normalized observable uniformly close on each fixed finite time
horizon. Thus completed recurrence is nowhere stable under arbitrarily weak
joint interaction even though every bounded-time observable is stable.

The bipartite specialization starts from the tensor-sum spectrum of any two
finite systems. The perturbation is diagonal in the uncoupled product
eigenbasis, hence is a legitimate Hermitian joint interaction; no numerical
construction or genericity hypothesis is used.
-/

open Set Filter NormedSpace
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rational independence of the complete real energy packet is stronger
than maximal projective independence. -/
theorem linearIndependent_maximallyProjectiveEnergy
    {I : Type*} [Fintype I]
    {energy : I → ℝ}
    (hlinear : LinearIndependent ℚ energy) :
    MaximallyProjectiveEnergy energy := by
  intro k _ henergy
  rw [Fintype.linearIndependent_iff] at hlinear
  have hkq :
      ∀ i, (k i : ℚ) = 0 := by
    apply hlinear
    simpa [Rat.smul_def] using henergy
  funext i
  exact_mod_cast hkq i

/-- Every finite energy packet has an arbitrarily close maximally
projective packet. -/
theorem exists_maximallyProjectiveEnergy_close
    (d : ℕ) (energy : Fin d → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ perturbed : Fin d → ℝ,
      MaximallyProjectiveEnergy perturbed ∧
      ∀ i, |perturbed i - energy i| < δ := by
  obtain ⟨perturbed, hlinear, hclose⟩ :=
    exists_linearIndependent_close d energy δ hδ
  exact ⟨perturbed,
    linearIndependent_maximallyProjectiveEnergy hlinear,
    fun i => by simpa [Real.dist_eq] using hclose i⟩

/-- Every energy packet on an arbitrary finite index type has an
arbitrarily close maximally projective packet. -/
theorem exists_maximallyProjectiveEnergy_close_fintype
    {I : Type*} [Fintype I]
    (energy : I → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ perturbed : I → ℝ,
      MaximallyProjectiveEnergy perturbed ∧
      ∀ i, |perturbed i - energy i| < δ := by
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  obtain ⟨flat, hlinear, hclose⟩ :=
    exists_linearIndependent_close
      (Fintype.card I) (fun i => energy (e.symm i)) δ hδ
  let perturbed : I → ℝ := fun i => flat (e i)
  have hlinear' : LinearIndependent ℚ perturbed := by
    exact hlinear.comp e e.injective
  refine ⟨perturbed,
    linearIndependent_maximallyProjectiveEnergy hlinear', ?_⟩
  intro i
  simpa [perturbed, Real.dist_eq] using hclose (e i)

/-- Diagonal spectral perturbations are exactly differences of diagonal
Hamiltonians. -/
theorem finiteIndexDiagonalHamiltonian_sub
    {I : Type*} [Fintype I] [DecidableEq I]
    (left right : I → ℝ) :
    RHTower.finiteIndexDiagonalHamiltonian left -
        RHTower.finiteIndexDiagonalHamiltonian right =
      RHTower.finiteIndexDiagonalHamiltonian
        (fun i => left i - right i) := by
  ext x i
  simp [sub_mul]

/-- A uniform spectral perturbation bounds the operator norm of the
corresponding diagonal Hamiltonian perturbation. -/
theorem finiteIndexDiagonalHamiltonian_norm_sub_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (left right : I → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ i, |left i - right i| ≤ δ) :
    ‖RHTower.finiteIndexDiagonalHamiltonian left -
        RHTower.finiteIndexDiagonalHamiltonian right‖ ≤ δ := by
  rw [finiteIndexDiagonalHamiltonian_sub]
  exact
    RHTower.ParityForecast.finiteIndexDiagonalHamiltonian_norm_le
      (fun i => left i - right i) δ hδ hclose

/-- Real finite diagonal Hamiltonians are self-adjoint in the `C⋆` sense
used by the finite-horizon perturbation theorem. -/
theorem finiteIndexDiagonalHamiltonian_isSelfAdjoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) :
    IsSelfAdjoint
      (RHTower.finiteIndexDiagonalHamiltonian energy) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint,
    RHTower.finiteIndexDiagonalHamiltonian_selfAdjoint]

/-- **Weak-interaction recurrence singularity.** For every finite
Hamiltonian and every positive operator-norm budget there is a perturbation
inside that budget which has full projective recurrence completion and
attains the minimum collision mass at every replica order. Nevertheless
every operator-normalized Heisenberg observable differs by at most the
dimension-free finite-time Duhamel bound. -/
theorem exists_arbitrarilyWeak_fullRecurrenceCompletion
    (d : ℕ) (energy : Fin d → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ perturbed : Fin d → ℝ,
      MaximallyProjectiveEnergy perturbed ∧
      ‖RHTower.finiteIndexDiagonalHamiltonian perturbed -
          RHTower.finiteIndexDiagonalHamiltonian energy‖ ≤ δ ∧
      (∀ (O :
          RHTower.FiniteIndexClockSpace (Fin d) →L[ℂ]
            RHTower.FiniteIndexClockSpace (Fin d)) (t : ℝ),
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian perturbed)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian perturbed))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian energy)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian energy)))‖
          ≤ 2 * |t| * δ * ‖O‖) ∧
      (∀ (weight : Fin d → ℝ), (∀ i, 0 < weight i) →
        ∀ n : ℕ,
          fidelityReplicaCollisionMass weight perturbed n =
            fidelityReplicaPermutationFloor weight n) := by
  obtain ⟨perturbed, hmax, hclose⟩ :=
    exists_maximallyProjectiveEnergy_close d energy δ hδ
  have hnorm :
      ‖RHTower.finiteIndexDiagonalHamiltonian perturbed -
          RHTower.finiteIndexDiagonalHamiltonian energy‖ ≤ δ :=
    finiteIndexDiagonalHamiltonian_norm_sub_le
      perturbed energy δ hδ.le (fun i => (hclose i).le)
  refine ⟨perturbed, hmax, hnorm, ?_, ?_⟩
  · intro O t
    have hperturbed :=
      finiteIndexDiagonalHamiltonian_isSelfAdjoint perturbed
    have henergy :=
      finiteIndexDiagonalHamiltonian_isSelfAdjoint energy
    calc
      _ ≤ 2 * |t| *
            ‖RHTower.finiteIndexDiagonalHamiltonian perturbed -
              RHTower.finiteIndexDiagonalHamiltonian energy‖ * ‖O‖ :=
        selfAdjoint_heisenbergEvolution_norm_sub_le
          (RHTower.finiteIndexDiagonalHamiltonian perturbed)
          (RHTower.finiteIndexDiagonalHamiltonian energy)
          O hperturbed henergy t
      _ ≤ 2 * |t| * δ * ‖O‖ := by gcongr
  · intro weight hweight n
    exact
      (all_fidelityReplicaCollisionMass_eq_floor_iff
        hweight perturbed).2 hmax n

/-- The weak-interaction recurrence singularity holds on every finite
index type, without choosing a particular enumeration in the statement. -/
theorem exists_arbitrarilyWeak_fullRecurrenceCompletion_fintype
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ perturbed : I → ℝ,
      MaximallyProjectiveEnergy perturbed ∧
      ‖RHTower.finiteIndexDiagonalHamiltonian perturbed -
          RHTower.finiteIndexDiagonalHamiltonian energy‖ ≤ δ ∧
      (∀ (O :
          RHTower.FiniteIndexClockSpace I →L[ℂ]
            RHTower.FiniteIndexClockSpace I) (t : ℝ),
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian perturbed)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian perturbed))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian energy)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian energy)))‖
          ≤ 2 * |t| * δ * ‖O‖) ∧
      (∀ (weight : I → ℝ), (∀ i, 0 < weight i) →
        ∀ n : ℕ,
          fidelityReplicaCollisionMass weight perturbed n =
            fidelityReplicaPermutationFloor weight n) := by
  obtain ⟨perturbed, hmax, hclose⟩ :=
    exists_maximallyProjectiveEnergy_close_fintype energy δ hδ
  have hnorm :
      ‖RHTower.finiteIndexDiagonalHamiltonian perturbed -
          RHTower.finiteIndexDiagonalHamiltonian energy‖ ≤ δ :=
    finiteIndexDiagonalHamiltonian_norm_sub_le
      perturbed energy δ hδ.le (fun i => (hclose i).le)
  refine ⟨perturbed, hmax, hnorm, ?_, ?_⟩
  · intro O t
    have hperturbed :=
      finiteIndexDiagonalHamiltonian_isSelfAdjoint perturbed
    have henergy :=
      finiteIndexDiagonalHamiltonian_isSelfAdjoint energy
    calc
      _ ≤ 2 * |t| *
            ‖RHTower.finiteIndexDiagonalHamiltonian perturbed -
              RHTower.finiteIndexDiagonalHamiltonian energy‖ * ‖O‖ :=
        selfAdjoint_heisenbergEvolution_norm_sub_le
          (RHTower.finiteIndexDiagonalHamiltonian perturbed)
          (RHTower.finiteIndexDiagonalHamiltonian energy)
          O hperturbed henergy t
      _ ≤ 2 * |t| * δ * ‖O‖ := by gcongr
  · intro weight hweight n
    exact
      (all_fidelityReplicaCollisionMass_eq_floor_iff
        hweight perturbed).2 hmax n

/-- Tensor-sum energy of two finite systems in the product eigenbasis. -/
def bipartiteProductEnergy
    {m n : ℕ} (left : Fin m → ℝ) (right : Fin n → ℝ) :
    Fin (m * n) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i
    left p.1 + right p.2

/-- Unflattened tensor-sum energy with an optional spectator index. -/
def bipartiteProductEnergyUnflattened
    {A B C : Type*}
    (left : A → ℝ) (right : B → ℝ) :
    A × B × C → ℝ :=
  fun x => left x.1 + right x.2.1

/-- Integer-valued standard rectangle character of a product spectrum. -/
def rectangleIntegerCharacter
    {A B C : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B)
    (j : RectangleContrastIndex A B C a₀ b₀) :
    A × B × C → ℤ :=
  fun x => rectangleContrastRelation (R := ℤ) a₀ b₀ j x

/-- Every standard rectangle character has zero total charge. -/
theorem rectangleIntegerCharacter_balanced
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B)
    (j : RectangleContrastIndex A B C a₀ b₀) :
    SpectralCharacterBalanced
      (rectangleIntegerCharacter a₀ b₀ j) := by
  unfold SpectralCharacterBalanced
  change
    ∑ x, rectangleContrastRelation (R := ℤ) a₀ b₀ j x = 0
  rw [← Finsupp.sum_fintype
    (rectangleContrastRelation (R := ℤ) a₀ b₀ j)
    (fun _ x => x) (fun _ => rfl)]
  simp only [rectangleContrastRelation]
  rw [Finsupp.sum_sub_index (by intros; rfl),
    Finsupp.sum_sub_index (by intros; rfl),
    Finsupp.sum_add_index' (by intros; rfl) (by intros; rfl)]
  simp

/-- Every indexed rectangle character is nonzero. -/
theorem rectangleIntegerCharacter_ne_zero
    {A B C : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a₀ : A) (b₀ : B)
    (j : RectangleContrastIndex A B C a₀ b₀) :
    rectangleIntegerCharacter a₀ b₀ j ≠ 0 := by
  intro hzero
  have h :=
    congrFun hzero (rectangleDistinguished j)
  simpa [rectangleIntegerCharacter,
    rectangleContrastRelation_apply_distinguished] using h

/-- Every rectangle character annihilates every uncoupled tensor-sum
energy, independently of its one-body spectra. -/
theorem rectangleIntegerCharacter_annihilates_productEnergy
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (left : A → ℝ) (right : B → ℝ)
    (a₀ : A) (b₀ : B)
    (j : RectangleContrastIndex A B C a₀ b₀) :
    (∑ x,
      (rectangleIntegerCharacter a₀ b₀ j x : ℝ) *
        bipartiteProductEnergyUnflattened left right x) = 0 := by
  classical
  unfold rectangleIntegerCharacter
  unfold bipartiteProductEnergyUnflattened
  rw [← Finsupp.sum_fintype
    (rectangleContrastRelation (R := ℤ) a₀ b₀ j)
    (fun x c => (c : ℝ) * (left x.1 + right x.2.1))
    (fun _ => by simp)]
  simp only [rectangleContrastRelation]
  rw [Finsupp.sum_sub_index (by intros; push_cast; ring),
    Finsupp.sum_sub_index (by intros; push_cast; ring),
    Finsupp.sum_add_index' (by intros; push_cast; ring)
      (by intros; push_cast; ring)]
  simp
  ring

/-- **Arbitrarily weak bipartite interaction rewrites completed
recurrence.** The singularity theorem applies to the uncoupled tensor-sum
spectrum of every pair of finite systems. The returned difference is a
Hermitian joint interaction diagonal in the product eigenbasis. -/
theorem exists_arbitrarilyWeak_bipartiteInteraction_fullRecurrenceCompletion
    {m n : ℕ} (left : Fin m → ℝ) (right : Fin n → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ interaction : Fin (m * n) → ℝ,
      MaximallyProjectiveEnergy
        (fun i => bipartiteProductEnergy left right i + interaction i) ∧
      ‖RHTower.finiteIndexDiagonalHamiltonian
            (fun i => bipartiteProductEnergy left right i + interaction i) -
          RHTower.finiteIndexDiagonalHamiltonian
            (bipartiteProductEnergy left right)‖ ≤ δ ∧
      (∀ (O :
          RHTower.FiniteIndexClockSpace (Fin (m * n)) →L[ℂ]
            RHTower.FiniteIndexClockSpace (Fin (m * n))) (t : ℝ),
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                (fun i =>
                  bipartiteProductEnergy left right i + interaction i))) *
              O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (fun i =>
                    bipartiteProductEnergy left right i + interaction i)))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                (bipartiteProductEnergy left right))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (bipartiteProductEnergy left right))))‖
          ≤ 2 * |t| * δ * ‖O‖) ∧
      (∀ (weight : Fin (m * n) → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight
              (fun i =>
                bipartiteProductEnergy left right i + interaction i) r =
            fidelityReplicaPermutationFloor weight r) := by
  obtain ⟨perturbed, hmax, hnorm, hfinite, hcollision⟩ :=
    exists_arbitrarilyWeak_fullRecurrenceCompletion
      (m * n) (bipartiteProductEnergy left right) δ hδ
  let interaction : Fin (m * n) → ℝ :=
    fun i => perturbed i - bipartiteProductEnergy left right i
  have hsum :
      (fun i =>
        bipartiteProductEnergy left right i + interaction i) =
        perturbed := by
    funext i
    simp [interaction]
  refine ⟨interaction, ?_, ?_, ?_, ?_⟩
  · simpa only [hsum] using hmax
  · simpa only [hsum] using hnorm
  · simpa only [hsum] using hfinite
  · simpa only [hsum] using hcollision

/-- **Exact product-constraint erasure law.** Every uncoupled `m × n`
product spectrum carries `(m - 1)(n - 1)` independent rectangle relations.
For every positive perturbation budget there is a coupled spectrum inside
that budget which erases every one of these relations, has maximal
projective recurrence completion, attains every replica collision floor,
and remains uniformly close for all bounded-time operator probes. -/
theorem
    exists_arbitrarilyWeak_bipartitePerturbation_erases_rectangleSector
    {m n : ℕ}
    (left : Fin m → ℝ) (right : Fin n → ℝ)
    (a₀ : Fin m) (b₀ : Fin n)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ perturbed : Fin m × Fin n × PUnit → ℝ,
      MaximallyProjectiveEnergy perturbed ∧
      ‖RHTower.finiteIndexDiagonalHamiltonian perturbed -
          RHTower.finiteIndexDiagonalHamiltonian
            (bipartiteProductEnergyUnflattened
              (C := PUnit) left right)‖ ≤ δ ∧
      (∀ (O :
          RHTower.FiniteIndexClockSpace (Fin m × Fin n × PUnit) →L[ℂ]
            RHTower.FiniteIndexClockSpace (Fin m × Fin n × PUnit))
          (t : ℝ),
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian perturbed)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian perturbed))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                (bipartiteProductEnergyUnflattened
                  (C := PUnit) left right))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (bipartiteProductEnergyUnflattened
                    (C := PUnit) left right))))‖
          ≤ 2 * |t| * δ * ‖O‖) ∧
      (∀ (weight : Fin m × Fin n × PUnit → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight perturbed r =
            fidelityReplicaPermutationFloor weight r) ∧
      Fintype.card
          (RectangleContrastIndex (Fin m) (Fin n) PUnit a₀ b₀) =
        (m - 1) * (n - 1) ∧
      LinearIndependent ℚ
        (rectangleProjectiveRationalCharacter a₀ b₀ :
          RectangleContrastIndex (Fin m) (Fin n) PUnit a₀ b₀ →
            ProjectiveRationalCharacter (Fin m × Fin n × PUnit)) ∧
      ∀ j : RectangleContrastIndex (Fin m) (Fin n) PUnit a₀ b₀,
        rectangleIntegerCharacter a₀ b₀ j ∈
            projectiveSpectralRelationLattice
              (bipartiteProductEnergyUnflattened
                (C := PUnit) left right) ∧
          rectangleIntegerCharacter a₀ b₀ j ∉
            projectiveSpectralRelationLattice perturbed := by
  let productEnergy : Fin m × Fin n × PUnit → ℝ :=
    bipartiteProductEnergyUnflattened (C := PUnit) left right
  obtain ⟨perturbed, hmax, hnorm, hfinite, hcollision⟩ :=
    exists_arbitrarilyWeak_fullRecurrenceCompletion_fintype
      productEnergy δ hδ
  refine ⟨perturbed, hmax, ?_, ?_, hcollision, ?_, ?_, ?_⟩
  · simpa [productEnergy] using hnorm
  · simpa [productEnergy] using hfinite
  · simpa using
      (rectangleContrastIndex_card
        (C := PUnit) a₀ b₀)
  · exact rectangleProjectiveRationalCharacter_linearIndependent a₀ b₀
  · intro j
    constructor
    · rw [mem_projectiveSpectralRelationLattice_iff]
      refine ⟨rectangleIntegerCharacter_balanced a₀ b₀ j, ?_⟩
      simpa [finiteTorusCharacterDetuning, productEnergy] using
        rectangleIntegerCharacter_annihilates_productEnergy
          left right a₀ b₀ j
    · rw [mem_projectiveSpectralRelationLattice_iff]
      rintro ⟨hbalanced, henergy⟩
      exact rectangleIntegerCharacter_ne_zero a₀ b₀ j
        (hmax (rectangleIntegerCharacter a₀ b₀ j)
          hbalanced (by
            simpa [finiteTorusCharacterDetuning] using henergy))

end

end GaloisForLFunctions.HTGeometry
