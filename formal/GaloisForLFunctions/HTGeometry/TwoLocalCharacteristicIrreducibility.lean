import GaloisForLFunctions.HTGeometry.TwoLocalCommonBaseEdgeMonodromy
import GaloisForLFunctions.HTGeometry.SpectralPathCovering
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Irreducibility of the universal two-local characteristic polynomial

Exact full spectral monodromy has an algebraic consequence stronger than
generic simplicity: the characteristic polynomial of the universal
complexified all-qubit two-local family is irreducible over its full
multivariate parameter ring.

The key transport law requires no analytic-continuation assumption.  If a
characteristic polynomial factors, then along a simple-spectrum labelled
path each root belongs to exactly one factor.  Factor membership is therefore
a clopen condition on the path interval and cannot change.  Full symmetric
common-base monodromy then makes a nonempty factor-root subset contain every
root.  Two positive-degree factors would consequently share a simple root,
which is impossible.
-/

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Evaluation of a polynomial whose coefficients are multivariate
polynomials is continuous when both the coefficient parameters and the
spectral argument vary continuously. -/
theorem continuous_nestedPolynomial_eval_along_path
    {θ : Type*}
    (A : Polynomial (MvPolynomial θ ℂ))
    {p : I → θ → ℂ} (hp : Continuous p)
    {root : I → ℂ} (hroot : Continuous root) :
    Continuous fun s =>
      (A.map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (p s))).eval
        (root s) := by
  rw [show (fun s =>
      (A.map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (p s))).eval
        (root s)) =
      fun s => A.sum fun n c =>
        MvPolynomial.eval (p s) c * root s ^ n by
    funext s
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum]
    rfl]
  apply continuous_finsetSum
  intro n hn
  exact
    ((MvPolynomial.continuous_eval (A.coeff n)).comp hp).mul
      (hroot.pow n)

/-- **Polynomial-factor transport law.** Along a labelled simple-spectrum
path, a root cannot move from one polynomial factor of the characteristic
polynomial to another.

The proof is topological.  Membership in the first factor is closed by
continuity.  Its complement is exactly membership in the second factor:
the product vanishes, while simultaneous membership would make the
characteristic root multiple.  Hence membership is clopen on the connected
unit interval. -/
theorem polynomialFactor_root_membership_transport
    {θ J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {M : Matrix J J (MvPolynomial θ ℂ)}
    {p q : θ → ℂ} {rootP rootQ : J → ℂ}
    (P : LabeledPolynomialMatrixPath M p q rootP rootQ)
    (A B : Polynomial (MvPolynomial θ ℂ))
    (hfactor : M.charpoly = A * B)
    (x : J) :
    (A.map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) p)).eval
          (rootP x) = 0 ↔
      (A.map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) q)).eval
          (rootQ x) = 0 := by
  let evalAt : I → MvPolynomial θ ℂ →+* ℂ :=
    fun s =>
      MvPolynomial.eval₂Hom
        (RingHom.id ℂ) (P.parameterPath s)
  let f : I → ℂ :=
    fun s => (A.map (evalAt s)).eval (P.rootPath x s)
  let g : I → ℂ :=
    fun s => (B.map (evalAt s)).eval (P.rootPath x s)
  have hpath : Continuous fun s => P.parameterPath s :=
    P.parameterPath.continuous
  have hf : Continuous f := by
    exact continuous_nestedPolynomial_eval_along_path
      A hpath (P.rootPath x).continuous
  have hg : Continuous g := by
    exact continuous_nestedPolynomial_eval_along_path
      B hpath (P.rootPath x).continuous
  have hprod : ∀ s, f s * g s = 0 := by
    intro s
    have hroot := P.root_is x s
    rw [Matrix.charpoly_map, hfactor, Polynomial.map_mul,
      Polynomial.eval_mul] at hroot
    exact hroot
  have hnotBoth : ∀ s, ¬ (f s = 0 ∧ g s = 0) := by
    intro s hboth
    let H :=
      M.map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (P.parameterPath s))
    have hsep : H.charpoly.Separable :=
      matrixCharpoly_separable_of_resultant_eval_ne_zero
        M (P.parameterPath s) (P.resultant_ne_zero s)
    have hroot : H.charpoly.eval (P.rootPath x s) = 0 :=
      P.root_is x s
    have hderiv :
        H.charpoly.derivative.eval (P.rootPath x s) ≠ 0 := by
      simpa using
        hsep.eval₂_derivative_ne_zero
          (RingHom.id ℂ) hroot
    have hfactorEval :
        H.charpoly = A.map (evalAt s) * B.map (evalAt s) := by
      rw [show H.charpoly =
          Polynomial.map (evalAt s) M.charpoly by
        exact Matrix.charpoly_map M (evalAt s)]
      rw [hfactor, Polynomial.map_mul]
    apply hderiv
    have hAz :
        (A.map (evalAt s)).eval (P.rootPath x s) = 0 := by
      simpa [f] using hboth.1
    have hBz :
        (B.map (evalAt s)).eval (P.rootPath x s) = 0 := by
      simpa [g] using hboth.2
    rw [hfactorEval, Polynomial.derivative_mul,
      Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, hAz, hBz]
    simp
  let S : Set I := {s | f s = 0}
  have hSclosed : IsClosed S := by
    exact isClosed_singleton.preimage hf
  have hScompl :
      Sᶜ = {s | g s = 0} := by
    ext s
    simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro hfn
      exact (mul_eq_zero.mp (hprod s)).resolve_left hfn
    · intro hgz hfz
      exact hnotBoth s ⟨hfz, hgz⟩
  have hSopen : IsOpen S := by
    rw [← isClosed_compl_iff]
    rw [hScompl]
    exact isClosed_singleton.preimage hg
  have hSclopen : IsClopen S := ⟨hSclosed, hSopen⟩
  constructor
  · intro hzero'
    have hzero : f 0 = 0 := by
      simpa [f, evalAt] using hzero'
    have hSuniv : S = Set.univ :=
      hSclopen.eq_univ ⟨0, hzero⟩
    have honeMem : (1 : I) ∈ S := by
      rw [hSuniv]
      exact Set.mem_univ 1
    have hone : f 1 = 0 := honeMem
    simpa [f, evalAt] using hone
  · intro hone'
    have hone : f 1 = 0 := by
      simpa [f, evalAt] using hone'
    have hSuniv : S = Set.univ :=
      hSclopen.eq_univ ⟨1, hone⟩
    have hzeroMem : (0 : I) ∈ S := by
      rw [hSuniv]
      exact Set.mem_univ 0
    have hzero : f 0 = 0 := hzeroMem
    simpa [f, evalAt] using hzero

/-- **Universal two-local characteristic irreducibility.** For every
positive number of qubits, the characteristic polynomial of the universal
complexified Hamiltonian containing all onsite and pair interactions is
irreducible over the multivariate polynomial ring of its two-local
couplings. -/
theorem universalTwoLocalCharacteristicPolynomial_irreducible
    (m : ℕ) :
    Irreducible
      (universalHypercubeTwoLocalPolynomialMatrix
        (m + 1)).charpoly := by
  let M :=
    universalHypercubeTwoLocalPolynomialMatrix (m + 1)
  let base :=
    commonTwoLocalDiagonalParameters m
  let root :=
    commonTwoLocalDiagonalRoot m
  let evalBase :=
    MvPolynomial.eval₂Hom (RingHom.id ℂ) base
  have hdegree :
      0 < M.charpoly.natDegree := by
    rw [Matrix.charpoly_natDegree_eq_dim]
    exact Fintype.card_pos
  rw [irreducible_iff]
  refine ⟨Polynomial.not_isUnit_of_natDegree_pos
    M.charpoly hdegree, ?_⟩
  intro A B hfactor
  have hfactorBase :
      (M.map evalBase).charpoly =
        A.map evalBase * B.map evalBase := by
    rw [Matrix.charpoly_map]
    rw [hfactor, Polynomial.map_mul]
  have hbaseMatrix :
      M.map evalBase =
        Matrix.diagonal root := by
    change
      (universalHypercubeTwoLocalPolynomialMatrix
          (m + 1)).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ)
            (commonTwoLocalDiagonalParameters m)) =
        Matrix.diagonal
          (fun x =>
            (commonTwoLocalDiagonalEnergyReal m x : ℂ))
    simpa using
      eval_commonTwoLocalDiagonalParameters m
  have hrootPacket :
      ∀ x,
        (M.map evalBase).charpoly.eval (root x) = 0 := by
    intro x
    rw [hbaseMatrix, Matrix.charpoly_diagonal,
      Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ x)
    simp
  have hseparable :
      (M.map evalBase).charpoly.Separable := by
    rw [hbaseMatrix, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr
      (commonTwoLocalDiagonalRoot_injective m)
  have hnotBothAtRoot :
      ∀ x,
        ¬ ((A.map evalBase).eval (root x) = 0 ∧
          (B.map evalBase).eval (root x) = 0) := by
    intro x hboth
    have hderiv :
        (M.map evalBase).charpoly.derivative.eval
            (root x) ≠ 0 := by
      simpa using
        hseparable.eval₂_derivative_ne_zero
          (RingHom.id ℂ) (hrootPacket x)
    apply hderiv
    rw [hfactorBase, Polynomial.derivative_mul,
      Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, hboth.1, hboth.2]
    simp
  have hfactorRootInvariant :
      ∀ (perm :
          Equiv.Perm (Fin (m + 1) → Bool)) x,
        (A.map evalBase).eval (root x) = 0 ↔
          (A.map evalBase).eval
            (root (perm x)) = 0 := by
    intro perm x
    rcases
        everyPermutation_has_exact_commonBase_twoLocalLoop
          m perm with ⟨P⟩
    simpa [M, base, root, evalBase,
      Function.comp_apply] using
      polynomialFactor_root_membership_transport
        P A B hfactor x
  have hcommonRoot_of_factorRoot :
      ∀ {C : Polynomial ℂ} {w : ℂ},
        C ∣ (M.map evalBase).charpoly →
        C.eval w = 0 →
        ∃ x, w = root x := by
    intro C w hC hCroot
    obtain ⟨D, hCD⟩ := hC
    have hcharRoot :
        (M.map evalBase).charpoly.eval w = 0 := by
      rw [hCD, Polynomial.eval_mul, hCroot, zero_mul]
    rw [hbaseMatrix, Matrix.charpoly_diagonal,
      Polynomial.eval_prod] at hcharRoot
    rw [Finset.prod_eq_zero_iff] at hcharRoot
    obtain ⟨x, _hx, hx⟩ := hcharRoot
    refine ⟨x, ?_⟩
    have hx' : w - root x = 0 := by
      simpa using hx
    exact sub_eq_zero.mp hx'
  have hlc :
      A.leadingCoeff * B.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul, ← hfactor]
    exact (Matrix.charpoly_monic M).leadingCoeff
  have hleadA : IsUnit A.leadingCoeff :=
    isUnit_iff_exists_inv.mpr
      ⟨B.leadingCoeff, hlc⟩
  have hleadB : IsUnit B.leadingCoeff :=
    isUnit_iff_exists_inv.mpr
      ⟨A.leadingCoeff, by
        simpa [mul_comm] using hlc⟩
  have hAmapDegree :
      (A.map evalBase).natDegree = A.natDegree := by
    apply Polynomial.natDegree_map_of_leadingCoeff_ne_zero
    exact (hleadA.map evalBase).ne_zero
  have hBmapDegree :
      (B.map evalBase).natDegree = B.natDegree := by
    apply Polynomial.natDegree_map_of_leadingCoeff_ne_zero
    exact (hleadB.map evalBase).ne_zero
  by_cases hAdeg :
      0 < (A.map evalBase).natDegree
  · have hAdegree :
        (A.map evalBase).degree ≠ 0 := by
      exact
        (Polynomial.natDegree_pos_iff_degree_pos.mp
          hAdeg).ne'
    obtain ⟨wA, hwA⟩ :=
      IsAlgClosed.exists_root
        (A.map evalBase) hAdegree
    have hAdiv :
        A.map evalBase ∣
          (M.map evalBase).charpoly :=
      ⟨B.map evalBase, hfactorBase⟩
    obtain ⟨xA, hxA⟩ :=
      hcommonRoot_of_factorRoot hAdiv hwA
    have hxARoot :
        (A.map evalBase).eval (root xA) = 0 := by
      rw [← hxA]
      exact hwA
    have hAall :
        ∀ y,
          (A.map evalBase).eval (root y) = 0 := by
      intro y
      simpa using
        (hfactorRootInvariant
          (Equiv.swap xA y) xA).mp hxARoot
    have hBdegZero :
        (B.map evalBase).natDegree = 0 := by
      by_contra hBzero
      have hBdeg :
          0 < (B.map evalBase).natDegree :=
        Nat.pos_of_ne_zero hBzero
      have hBdegree :
          (B.map evalBase).degree ≠ 0 :=
        (Polynomial.natDegree_pos_iff_degree_pos.mp
          hBdeg).ne'
      obtain ⟨wB, hwB⟩ :=
        IsAlgClosed.exists_root
          (B.map evalBase) hBdegree
      have hBdiv :
          B.map evalBase ∣
            (M.map evalBase).charpoly :=
        ⟨A.map evalBase, by
          rw [mul_comm]
          exact hfactorBase⟩
      obtain ⟨xB, hxB⟩ :=
        hcommonRoot_of_factorRoot hBdiv hwB
      apply hnotBothAtRoot xB
      refine ⟨hAall xB, ?_⟩
      rw [← hxB]
      exact hwB
    have hBzero : B.natDegree = 0 := by
      rw [← hBmapDegree]
      exact hBdegZero
    right
    rw [Polynomial.eq_C_of_natDegree_eq_zero hBzero]
    apply Polynomial.isUnit_C.mpr
    simpa [Polynomial.leadingCoeff, hBzero] using
      hleadB
  · have hAmapZero :
        (A.map evalBase).natDegree = 0 :=
      Nat.eq_zero_of_not_pos hAdeg
    have hAzero : A.natDegree = 0 := by
      rw [← hAmapDegree]
      exact hAmapZero
    left
    rw [Polynomial.eq_C_of_natDegree_eq_zero hAzero]
    apply Polynomial.isUnit_C.mpr
    simpa [Polynomial.leadingCoeff, hAzero] using
      hleadA

/-- The same irreducibility over the rational-function field of all
two-local coupling parameters.  Thus allowing parameter denominators does
not create a hidden spectral factor. -/
theorem
    universalTwoLocalCharacteristicPolynomial_fractionField_irreducible
    (m : ℕ) :
    Irreducible
      ((universalHypercubeTwoLocalPolynomialMatrix
        (m + 1)).charpoly.map
        (algebraMap
          (MvPolynomial
            (HypercubeTwoLocalParameter (m + 1)) ℂ)
          (FractionRing
            (MvPolynomial
              (HypercubeTwoLocalParameter (m + 1)) ℂ)))) := by
  exact
    ((Matrix.charpoly_monic
      (universalHypercubeTwoLocalPolynomialMatrix
        (m + 1))).irreducible_iff_irreducible_map_fraction_map).mp
      (universalTwoLocalCharacteristicPolynomial_irreducible m)

end

end GaloisForLFunctions.HTGeometry
