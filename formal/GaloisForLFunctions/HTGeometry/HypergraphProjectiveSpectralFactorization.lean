import GaloisForLFunctions.HTGeometry.HypergraphComponentWitness
import GaloisForLFunctions.HTGeometry.ConcatenatedSpectrumScaleShiftWitness
import GaloisForLFunctions.HTGeometry.SubsystemComponentGenericity

/-!
# Generic projective spectral rank of an arbitrary finite interaction hypergraph

The admissible Hamiltonians of a finite interaction hypergraph split over the
connected components of its two-section graph, and each component is a
connected network carrying a spanning-tree witness of maximal projective rank.
Scaling and shifting those witnesses independently makes the concatenated
component spectrum maximally projective, which is the one witness required by
the block-diagonal genericity theorem.

The conclusion is that in the exact real coefficient space of hyperedge-local
Hamiltonians the anchored projective rational spectral rank equals

```
τ(H) = ∑_{C ∈ π₀(𝔥)} (D_C - 1),      D_C = ∏_{v ∈ C} q_v
```

on a dense residual set of full Lebesgue measure.  The rank depends only on the
component factorization of the hypergraph: not on hyperedge sizes, interaction
order, vertex degrees or geometry.
-/

open Set SimpleGraph MeasureTheory Topology Filter
open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Charpoly roots of an affinely rescaled Hermitian matrix -/

/-- Rescaling and shifting a matrix rescales and shifts its characteristic
roots. -/
theorem matrixCharpolyRelation_smul_add_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (s t x : ℝ)
    (hx : matrixCharpolyRelation (M, (x : ℂ)) = 0) :
    matrixCharpolyRelation
      (s • M + t • (1 : Matrix ι ι ℂ), ((s * x + t : ℝ) : ℂ)) = 0 := by
  have hrewrite :
      (Matrix.scalar ι ((s * x + t : ℝ) : ℂ) -
          (s • M + t • (1 : Matrix ι ι ℂ))) =
        (s : ℂ) • (Matrix.scalar ι ((x : ℝ) : ℂ) - M) := by
    ext a b
    by_cases hab : a = b <;>
      simp [Matrix.scalar, hab, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, Complex.real_smul]
    ring
  have hzero : (Matrix.scalar ι ((x : ℝ) : ℂ) - M).det = 0 := hx
  show (Matrix.scalar ι ((s * x + t : ℝ) : ℂ) -
    (s • M + t • (1 : Matrix ι ι ℂ))).det = 0
  rw [hrewrite, Matrix.det_smul, hzero, mul_zero]

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)] (𝔥 : Finset (Finset V))

/-! ### Canonical coordinates of the hyperedge-local space, split by component -/

/-- Canonical Hermitian basis of the block-local space of one component. -/
def componentBlockGenerator (c : HypergraphComponent 𝔥) :
    Fin (Module.finrank ℝ (blockLocalSubmodule A 𝔥 c.1)) →
      Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1) ℂ :=
  realMatrixSubmoduleGenerator (blockLocalSubmodule A 𝔥 c.1)

omit [Nonempty V] [∀ v, Nonempty (A v)] in
theorem componentBlockGenerator_mem (c : HypergraphComponent 𝔥)
    (i : Fin (Module.finrank ℝ (blockLocalSubmodule A 𝔥 c.1))) :
    componentBlockGenerator A 𝔥 c i ∈ blockLocalSubmodule A 𝔥 c.1 :=
  (Module.finBasis ℝ (blockLocalSubmodule A 𝔥 c.1) i).2

omit [Nonempty V] in
theorem componentBlockGenerator_isHermitian (c : HypergraphComponent 𝔥)
    (i : Fin (Module.finrank ℝ (blockLocalSubmodule A 𝔥 c.1))) :
    (componentBlockGenerator A 𝔥 c i).IsHermitian :=
  isHermitian_of_mem_blockLocalSubmodule (componentBlockGenerator_mem A 𝔥 c i)

/-- One canonical coordinate of the hyperedge-local space: a component together
with a basis index of its block space. -/
abbrev HypergraphCoordinate : Type :=
  Σ c : HypergraphComponent 𝔥,
    Fin (Module.finrank ℝ (blockLocalSubmodule A 𝔥 c.1))

/-- Number of canonical coordinates of the hyperedge-local space. -/
def hypergraphCoordinateCount : ℕ := Fintype.card (HypergraphCoordinate A 𝔥)

/-- Canonical enumeration of the coordinates. -/
def hypergraphCoordinateEquiv :
    HypergraphCoordinate A 𝔥 ≃ Fin (hypergraphCoordinateCount A 𝔥) :=
  Fintype.equivFin _

/-- Ambient generator of one canonical coordinate. -/
def hypergraphGeneratorFin (j : Fin (hypergraphCoordinateCount A 𝔥)) :
    Matrix (∀ v, A v) (∀ v, A v) ℂ :=
  liftLocalMatrix ((hypergraphCoordinateEquiv A 𝔥).symm j).1.1
    (componentBlockGenerator A 𝔥 ((hypergraphCoordinateEquiv A 𝔥).symm j).1
      ((hypergraphCoordinateEquiv A 𝔥).symm j).2)

omit [Nonempty V] in
theorem hypergraphGeneratorFin_isHermitian
    (j : Fin (hypergraphCoordinateCount A 𝔥)) :
    (hypergraphGeneratorFin A 𝔥 j).IsHermitian :=
  isHermitian_liftLocalMatrix _ (componentBlockGenerator_isHermitian A 𝔥 _ _)

omit [Nonempty V] [∀ v, Nonempty (A v)] in
theorem hypergraphGeneratorFin_mem
    (j : Fin (hypergraphCoordinateCount A 𝔥)) :
    hypergraphGeneratorFin A 𝔥 j ∈ hypergraphLocalSubmodule A 𝔥 :=
  componentLocalSubmodule_le_hypergraphLocalSubmodule A 𝔥 _
    (mem_blockLocalSubmodule_iff.1 (componentBlockGenerator_mem A 𝔥 _ _))

/-- Block read by one component of one canonical coordinate: the basis element
itself at its own component, and zero at every other component. -/
def componentBlockFamily (c : HypergraphComponent 𝔥)
    (θ : HypergraphCoordinate A 𝔥) :
    Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1) ℂ :=
  if h : θ.1 = c then
    cast (congrArg (fun d : HypergraphComponent 𝔥 =>
        Matrix (LocalConfiguration A d.1) (LocalConfiguration A d.1) ℂ) h)
      (componentBlockGenerator A 𝔥 θ.1 θ.2)
  else 0

omit [Nonempty V] [∀ v, Nonempty (A v)] in
theorem componentBlockFamily_self (θ : HypergraphCoordinate A 𝔥) :
    componentBlockFamily A 𝔥 θ.1 θ = componentBlockGenerator A 𝔥 θ.1 θ.2 := by
  rw [componentBlockFamily, dif_pos rfl]
  rfl

omit [Nonempty V] [∀ v, Nonempty (A v)] in
theorem componentBlockFamily_of_ne {c : HypergraphComponent 𝔥}
    {θ : HypergraphCoordinate A 𝔥} (h : θ.1 ≠ c) :
    componentBlockFamily A 𝔥 c θ = 0 := dif_neg h

omit [Nonempty V] [∀ v, Nonempty (A v)] in
theorem componentBlockFamily_mem (c : HypergraphComponent 𝔥)
    (θ : HypergraphCoordinate A 𝔥) :
    componentBlockFamily A 𝔥 c θ ∈ blockLocalSubmodule A 𝔥 c.1 := by
  obtain ⟨d, i⟩ := θ
  by_cases h : d = c
  · subst h
    rw [componentBlockFamily_self A 𝔥 ⟨d, i⟩]
    exact componentBlockGenerator_mem A 𝔥 d i
  · rw [componentBlockFamily_of_ne A 𝔥 h]
    exact Submodule.zero_mem _

omit [Nonempty V] in
theorem componentBlockFamily_isHermitian (c : HypergraphComponent 𝔥)
    (θ : HypergraphCoordinate A 𝔥) :
    (componentBlockFamily A 𝔥 c θ).IsHermitian :=
  isHermitian_of_mem_blockLocalSubmodule (componentBlockFamily_mem A 𝔥 c θ)

/-- Component blocks in the canonical enumeration. -/
def componentBlockFamilyFin (c : HypergraphComponent 𝔥)
    (j : Fin (hypergraphCoordinateCount A 𝔥)) :
    Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1) ℂ :=
  componentBlockFamily A 𝔥 c ((hypergraphCoordinateEquiv A 𝔥).symm j)

omit [Nonempty V] in
theorem componentBlockFamilyFin_isHermitian (c : HypergraphComponent 𝔥)
    (j : Fin (hypergraphCoordinateCount A 𝔥)) :
    (componentBlockFamilyFin A 𝔥 c j).IsHermitian :=
  componentBlockFamily_isHermitian A 𝔥 c _

omit [Nonempty V] [∀ v, Nonempty (A v)] in
/-- **The component blocks reassemble each generator.** -/
theorem sum_lift_componentBlockFamily (θ : HypergraphCoordinate A 𝔥) :
    (∑ c : HypergraphComponent 𝔥,
        liftLocalMatrix c.1 (componentBlockFamily A 𝔥 c θ)) =
      liftLocalMatrix θ.1.1 (componentBlockGenerator A 𝔥 θ.1 θ.2) := by
  classical
  rw [Finset.sum_eq_single θ.1]
  · rw [componentBlockFamily_self A 𝔥 θ]
  · intro d _ hd
    rw [componentBlockFamily_of_ne A 𝔥 (Ne.symm hd), liftLocalMatrix_zero]
  · intro hc
    exact absurd (Finset.mem_univ θ.1) hc

/-! ### The parameterized Hamiltonian and its blocks -/

/-- Hyperedge-local Hamiltonian at a canonical coordinate vector. -/
def hypergraphHamiltonian (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ) :
    Matrix (∀ v, A v) (∀ v, A v) ℂ :=
  realAffineMatrix 0 (hypergraphGeneratorFin A 𝔥) p

/-- Component block at a canonical coordinate vector. -/
def hypergraphBlock (c : HypergraphComponent 𝔥)
    (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ) :
    Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1) ℂ :=
  realAffineMatrix 0 (componentBlockFamilyFin A 𝔥 c) p

omit [Nonempty V] in
theorem hypergraphHamiltonian_isHermitian
    (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ) :
    (hypergraphHamiltonian A 𝔥 p).IsHermitian :=
  realAffineMatrix_isHermitian 0 (hypergraphGeneratorFin A 𝔥)
    Matrix.isHermitian_zero (hypergraphGeneratorFin_isHermitian A 𝔥) p

omit [Nonempty V] in
theorem hypergraphBlock_isHermitian (c : HypergraphComponent 𝔥)
    (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ) :
    (hypergraphBlock A 𝔥 c p).IsHermitian :=
  realAffineMatrix_isHermitian 0 (componentBlockFamilyFin A 𝔥 c)
    Matrix.isHermitian_zero (componentBlockFamilyFin_isHermitian A 𝔥 c) p

omit [Nonempty V] [∀ v, Nonempty (A v)] in
theorem hypergraphHamiltonian_mem
    (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ) :
    hypergraphHamiltonian A 𝔥 p ∈ hypergraphLocalSubmodule A 𝔥 := by
  rw [hypergraphHamiltonian, realAffineMatrix_zero_base]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (hypergraphGeneratorFin_mem A 𝔥 j)

omit [Nonempty V] [∀ v, Nonempty (A v)] in
/-- **The blocks of the parameterized Hamiltonian reassemble it exactly.** -/
theorem hypergraphHamiltonian_eq_sum_lift
    (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ) :
    hypergraphHamiltonian A 𝔥 p =
      ∑ c : HypergraphComponent 𝔥,
        liftLocalMatrix c.1 (hypergraphBlock A 𝔥 c p) := by
  classical
  have hblock : ∀ c : HypergraphComponent 𝔥,
      liftLocalMatrix c.1 (hypergraphBlock A 𝔥 c p) =
        ∑ j, p j • liftLocalMatrix c.1 (componentBlockFamilyFin A 𝔥 c j) := by
    intro c
    rw [hypergraphBlock, realAffineMatrix_zero_base]
    rw [show (∑ j, p j • componentBlockFamilyFin A 𝔥 c j) =
        ∑ j, p j • componentBlockFamilyFin A 𝔥 c j from rfl]
    induction (Finset.univ : Finset (Fin (hypergraphCoordinateCount A 𝔥)))
      using Finset.induction_on with
    | empty => simp [liftLocalMatrix_zero]
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, liftLocalMatrix_add,
          liftLocalMatrix_smul, ih]
  simp only [hblock]
  rw [Finset.sum_comm]
  rw [hypergraphHamiltonian, realAffineMatrix_zero_base]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.smul_sum]
  have hj : (∑ x : HypergraphComponent 𝔥,
      liftLocalMatrix x.1 (componentBlockFamilyFin A 𝔥 x j)) =
      hypergraphGeneratorFin A 𝔥 j :=
    sum_lift_componentBlockFamily A 𝔥 ((hypergraphCoordinateEquiv A 𝔥).symm j)
  rw [hj]

omit [Nonempty V] [∀ v, Nonempty (A v)] in
/-- **Component coordinates read the component blocks.**  The block of the
parameterized Hamiltonian on a component is the affine family of that
component's own canonical basis. -/
theorem hypergraphBlock_eq_of_coordinates
    (q : ∀ c : HypergraphComponent 𝔥,
      Fin (Module.finrank ℝ (blockLocalSubmodule A 𝔥 c.1)) → ℝ)
    (c : HypergraphComponent 𝔥) :
    hypergraphBlock A 𝔥 c
        (fun j => q ((hypergraphCoordinateEquiv A 𝔥).symm j).1
          ((hypergraphCoordinateEquiv A 𝔥).symm j).2) =
      realAffineMatrix 0 (componentBlockGenerator A 𝔥 c) (q c) := by
  classical
  rw [hypergraphBlock, realAffineMatrix_zero_base, realAffineMatrix_zero_base]
  have hreindex :
      (∑ θ : HypergraphCoordinate A 𝔥,
          q θ.1 θ.2 • componentBlockFamily A 𝔥 c θ) =
        ∑ j, (fun j => q ((hypergraphCoordinateEquiv A 𝔥).symm j).1
          ((hypergraphCoordinateEquiv A 𝔥).symm j).2) j •
            componentBlockFamilyFin A 𝔥 c j := by
    refine Fintype.sum_equiv (hypergraphCoordinateEquiv A 𝔥)
      (fun θ => q θ.1 θ.2 • componentBlockFamily A 𝔥 c θ)
      (fun j => q ((hypergraphCoordinateEquiv A 𝔥).symm j).1
        ((hypergraphCoordinateEquiv A 𝔥).symm j).2 •
          componentBlockFamilyFin A 𝔥 c j) ?_
    intro θ
    rw [componentBlockFamilyFin, Equiv.symm_apply_apply]
  rw [← hreindex]
  rw [Fintype.sum_sigma (fun θ : HypergraphCoordinate A 𝔥 =>
    q θ.1 θ.2 • componentBlockFamily A 𝔥 c θ)]
  rw [Finset.sum_eq_single c]
  · exact Finset.sum_congr rfl fun k _ => by
      rw [componentBlockFamily_self A 𝔥 ⟨c, k⟩]
  · intro d _ hd
    exact Finset.sum_eq_zero fun k _ => by
      rw [componentBlockFamily_of_ne A 𝔥 hd, smul_zero]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-- **The canonical coordinates exhaust the hyperedge-local space.** -/
theorem exists_hypergraphHamiltonian_eq
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : H ∈ hypergraphLocalSubmodule A 𝔥) :
    ∃ p, hypergraphHamiltonian A 𝔥 p = H := by
  classical
  obtain ⟨B, -, hlift, hsum⟩ := exists_hermitian_componentBlocks A 𝔥 hH
  have hBmem : ∀ c, B c ∈ blockLocalSubmodule A 𝔥 c.1 := fun c =>
    mem_blockLocalSubmodule_iff.2 (hlift c)
  have hex : ∀ c : HypergraphComponent 𝔥,
      ∃ p : Fin (Module.finrank ℝ (blockLocalSubmodule A 𝔥 c.1)) → ℝ,
        realAffineMatrix 0
          (realMatrixSubmoduleGenerator (blockLocalSubmodule A 𝔥 c.1)) p = B c :=
    fun c => exists_realAffineMatrix_eq_of_mem_submodule
      (blockLocalSubmodule A 𝔥 c.1) (B c) (hBmem c)
  have hq : ∀ c, realAffineMatrix 0
      (realMatrixSubmoduleGenerator (blockLocalSubmodule A 𝔥 c.1))
      (Classical.choose (hex c)) = B c := fun c => Classical.choose_spec (hex c)
  refine ⟨fun j => Classical.choose
    (hex ((hypergraphCoordinateEquiv A 𝔥).symm j).1)
    ((hypergraphCoordinateEquiv A 𝔥).symm j).2, ?_⟩
  rw [hypergraphHamiltonian_eq_sum_lift, hsum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hypergraphBlock_eq_of_coordinates A 𝔥
    (fun c => Classical.choose (hex c)) c]
  exact congrArg (liftLocalMatrix c.1) (hq c)

/-! ### The witness -/

omit [Nonempty V] [∀ v, Nonempty (A v)] in
/-- **Transverse component witness.**  There is a canonical coordinate vector at
which the concatenation of all component spectra is maximally projective.  The
component witnesses are the spanning-tree Hamiltonians of the components,
rescaled and shifted by multiples of the component identities. -/
theorem exists_witness_hypergraphBlock
    (hA : ∀ v, 2 ≤ Fintype.card (A v)) :
    ∃ (p₀ : Fin (hypergraphCoordinateCount A 𝔥) → ℝ)
      (e : ∀ c : HypergraphComponent 𝔥, LocalConfiguration A c.1 → ℝ),
      MaximallyProjectiveEnergy
          (fun x : Σ c : HypergraphComponent 𝔥, LocalConfiguration A c.1 =>
            e x.1 x.2) ∧
        ∀ (c : HypergraphComponent 𝔥) (i : LocalConfiguration A c.1),
          matrixCharpolyRelation (hypergraphBlock A 𝔥 c p₀, (e c i : ℂ)) = 0 := by
  classical
  choose K hK hKmem hKmax using fun c : HypergraphComponent 𝔥 =>
    exists_maximallyProjective_mem_blockLocalSubmodule A hA 𝔥 c.2
  obtain ⟨scale, shift, hconcat⟩ :=
    exists_scale_shift_concatenated_maximallyProjective
      (fun c => (hK c).eigenvalues) hKmax
  set W : ∀ c : HypergraphComponent 𝔥,
      Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1) ℂ :=
    fun c => scale c • K c + shift c • (1 : Matrix (LocalConfiguration A c.1)
      (LocalConfiguration A c.1) ℂ) with hW
  have hWmem : ∀ c, W c ∈ blockLocalSubmodule A 𝔥 c.1 := by
    intro c
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hKmem c))
      (Submodule.smul_mem _ _
        (one_mem_blockLocalSubmodule (hypergraphComponents_nonempty c.2)))
  obtain ⟨H, hHsum⟩ : ∃ H : Matrix (∀ v, A v) (∀ v, A v) ℂ,
      H = ∑ c : HypergraphComponent 𝔥, liftLocalMatrix c.1 (W c) := ⟨_, rfl⟩
  have hHmem : H ∈ hypergraphLocalSubmodule A 𝔥 := by
    rw [hHsum]
    refine Submodule.sum_mem _ fun c _ => ?_
    exact componentLocalSubmodule_le_hypergraphLocalSubmodule A 𝔥 c.1
      (mem_blockLocalSubmodule_iff.1 (hWmem c))
  choose q hq using fun c : HypergraphComponent 𝔥 =>
    exists_realAffineMatrix_eq_of_mem_submodule
      (blockLocalSubmodule A 𝔥 c.1) (W c) (hWmem c)
  refine ⟨fun j => q ((hypergraphCoordinateEquiv A 𝔥).symm j).1
      ((hypergraphCoordinateEquiv A 𝔥).symm j).2,
    fun c i => scale c * (hK c).eigenvalues i + shift c, hconcat, ?_⟩
  intro c i
  have hblock : hypergraphBlock A 𝔥 c
      (fun j => q ((hypergraphCoordinateEquiv A 𝔥).symm j).1
        ((hypergraphCoordinateEquiv A 𝔥).symm j).2) = W c := by
    rw [hypergraphBlock_eq_of_coordinates A 𝔥 q c]
    exact hq c
  rw [hblock, hW]
  exact matrixCharpolyRelation_smul_add_smul_one (K c) (scale c) (shift c)
    ((hK c).eigenvalues i)
    (hermitianEigenvalue_matrixCharpolyRelation (K c) (hK c) i)

/-! ### The generic set and the rank law -/

/-- Component polynomial family of the hyperedge-local coordinates. -/
def hypergraphBlockPolynomial (c : HypergraphComponent 𝔥) :
    Matrix (LocalConfiguration A c.1) (LocalConfiguration A c.1)
      (MvPolynomial (Fin (hypergraphCoordinateCount A 𝔥)) ℂ) :=
  realAffineMatrixPolynomial 0 (componentBlockFamilyFin A 𝔥 c)

omit [Nonempty V] [∀ v, Nonempty (A v)] in
theorem hypergraphBlockPolynomial_eval (c : HypergraphComponent 𝔥)
    (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ) :
    (hypergraphBlockPolynomial A 𝔥 c).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ))) =
      hypergraphBlock A 𝔥 c p :=
  eval_realAffineMatrixPolynomial 0 (componentBlockFamilyFin A 𝔥 c) p

/-- Coordinates at which the component gap modules of the hyperedge-local
Hamiltonian are maximal internally and transverse externally. -/
def hypergraphComponentGenericSet :
    Set (Fin (hypergraphCoordinateCount A 𝔥) → ℝ) :=
  polynomialMatrixProjectiveGenericSet
    (Matrix.blockDiagonal' (hypergraphBlockPolynomial A 𝔥))

omit [Nonempty V] in
theorem componentProjectivelyIndependent_of_mem_hypergraphComponentGenericSet
    (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ)
    (hp : p ∈ hypergraphComponentGenericSet A 𝔥) :
    ComponentProjectivelyIndependent
      (fun c : HypergraphComponent 𝔥 =>
        (hypergraphBlock_isHermitian A 𝔥 c p).eigenvalues) := by
  have hherm : ∀ c : HypergraphComponent 𝔥,
      ((hypergraphBlockPolynomial A 𝔥 c).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (fun t => (p t : ℂ)))).IsHermitian := by
    intro c
    rw [hypergraphBlockPolynomial_eval]
    exact hypergraphBlock_isHermitian A 𝔥 c p
  have hbase := componentProjectivelyIndependent_of_mem_blockDiagonalGenericSet
    (hypergraphBlockPolynomial A 𝔥) p hherm hp
  have hfun :
      (fun c : HypergraphComponent 𝔥 => (hherm c).eigenvalues) =
        fun c : HypergraphComponent 𝔥 =>
          (hypergraphBlock_isHermitian A 𝔥 c p).eigenvalues := by
    funext c
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (hherm c)
      (hypergraphBlock_isHermitian A 𝔥 c p)).2
    rw [hypergraphBlockPolynomial_eval]
  rwa [hfun] at hbase

omit [Nonempty V] [∀ v, Nonempty (A v)] in
/-- **Arbitrary finite interaction hypergraphs have maximal generic component
spectra.**  In the exact real coefficient space of Hermitian one-site plus
hyperedge-local Hamiltonians, the coordinates whose component gap modules are
maximal internally and transverse externally form a dense residual set of full
Lebesgue measure. -/
theorem hypergraphComponentGenericSet_dense_residual_fullMeasure
    (hA : ∀ v, 2 ≤ Fintype.card (A v)) :
    Dense (hypergraphComponentGenericSet A 𝔥) ∧
      hypergraphComponentGenericSet A 𝔥 ∈
        residual (Fin (hypergraphCoordinateCount A 𝔥) → ℝ) ∧
      volume (hypergraphComponentGenericSet A 𝔥)ᶜ = 0 := by
  obtain ⟨p₀, e, hmax, hroot⟩ := exists_witness_hypergraphBlock A 𝔥 hA
  refine blockDiagonalProjectiveGenericSet_dense_residual_fullMeasure
    (hypergraphBlockPolynomial A 𝔥) p₀ e hmax ?_
  intro c i
  rw [hypergraphBlockPolynomial_eval]
  exact hroot c i

omit [Nonempty V] in
/-- **Equation `(1)`: the generic projective spectral rank of a hypergraph.**
At every coordinate of the generic set the anchored projective rational
spectral rank of the hyperedge-local Hamiltonian is the sum, over the connected
components of the two-section graph, of the component tensor dimension minus
one.  It does not depend on hyperedge sizes, interaction order, vertex degrees
or geometry. -/
theorem anchoredTemporalRank_hypergraphHamiltonian_eq_sum
    (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ)
    (hp : p ∈ hypergraphComponentGenericSet A 𝔥) (r : ∀ v, A v) :
    anchoredTemporalRank (hypergraphHamiltonian_isHermitian A 𝔥 p).eigenvalues r =
      ∑ P ∈ hypergraphComponents 𝔥, ((∏ v ∈ P, Fintype.card (A v)) - 1) :=
  anchoredTemporalRank_eq_sum_hypergraphComponents A 𝔥
    (fun c => hypergraphBlock A 𝔥 c p)
    (fun c => hypergraphBlock_isHermitian A 𝔥 c p)
    (componentProjectivelyIndependent_of_mem_hypergraphComponentGenericSet
      A 𝔥 p hp)
    (hypergraphHamiltonian_isHermitian A 𝔥 p)
    (hypergraphHamiltonian_eq_sum_lift A 𝔥 p) r

omit [Nonempty V] in
/-- **Generic spectral simplicity of a hypergraph Hamiltonian.**  At every
coordinate of the generic set the total spectrum is simple. -/
theorem injective_eigenvalues_hypergraphHamiltonian
    (p : Fin (hypergraphCoordinateCount A 𝔥) → ℝ)
    (hp : p ∈ hypergraphComponentGenericSet A 𝔥) :
    Function.Injective (hypergraphHamiltonian_isHermitian A 𝔥 p).eigenvalues :=
  injective_eigenvalues_of_componentProjectivelyIndependent A 𝔥
    (fun c => hypergraphBlock A 𝔥 c p)
    (fun c => hypergraphBlock_isHermitian A 𝔥 c p)
    (componentProjectivelyIndependent_of_mem_hypergraphComponentGenericSet
      A 𝔥 p hp)
    (hypergraphHamiltonian_isHermitian A 𝔥 p)
    (hypergraphHamiltonian_eq_sum_lift A 𝔥 p)

end

end GaloisForLFunctions.HTGeometry
