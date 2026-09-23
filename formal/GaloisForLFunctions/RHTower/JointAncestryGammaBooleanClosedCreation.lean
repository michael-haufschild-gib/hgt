import GaloisForLFunctions.RHTower.JointAncestryActualThetaAdjacentGradeShiftEscape
import GaloisForLFunctions.HTGeometry.LpReindexCompactDichotomy
import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport
import GaloisForLFunctions.HTGeometry.MaximalRealDiagonalSelfAdjoint

/-!
# JAS Gamma Boolean closed creation

The Gamma-sewn synchronized-lcm coefficients define an exact state-dependent connection on every
finite prime-support face. This module extends that connection through the Boolean vacuum and
constructs its first genuine Hilbert completion.

For each prime, maximal real diagonal multiplication by the insertion gain is followed by the
unitary that toggles that prime in `ell^(2 : ℕ)(Finset Primes)`. The diagonal vanishes on already occupied
supports. The resulting partial operator is closed and densely defined, raises each unoccupied
basis support with the literal Gamma coefficient, kills the occupied sector, has range in the
occupied corner, is not surjective, and commutes with every other prime creation on admissible
Boolean basis squares.

This supplies the compression/corner side forced by the prime-torus unit obstruction. It does not
yet tensor the construction with the actual completed-theta unbounded grade graph, establish
prime-Poisson source-linearity, or produce an Xi reflection sewing.
-/

open scoped ENNReal LinearPMap

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.LpDiagonal

def jasGammaSupportToggleFun (p : Nat.Primes)
    (P : Finset Nat.Primes) : Finset Nat.Primes :=
  if p ∈ P then P.erase p else insert p P

theorem jasGammaSupportToggleFun_involutive (p : Nat.Primes) :
    Function.Involutive (jasGammaSupportToggleFun p) := by
  intro P
  by_cases hp : p ∈ P
  · simp [jasGammaSupportToggleFun, hp, Finset.insert_erase hp]
  · simp [jasGammaSupportToggleFun, hp, Finset.erase_insert hp]

def jasGammaSupportToggle (p : Nat.Primes) :
    Finset Nat.Primes ≃ Finset Nat.Primes :=
  (jasGammaSupportToggleFun_involutive p).toPerm

@[simp] theorem jasGammaSupportToggle_apply (p : Nat.Primes)
    (P : Finset Nat.Primes) :
    jasGammaSupportToggle p P =
      if p ∈ P then P.erase p else insert p P := rfl

@[simp] theorem jasGammaSupportToggle_symm_apply (p : Nat.Primes)
    (P : Finset Nat.Primes) :
    (jasGammaSupportToggle p).symm P = jasGammaSupportToggle p P := by
  apply (jasGammaSupportToggle p).injective
  rw [Equiv.apply_symm_apply]
  exact (jasGammaSupportToggleFun_involutive p P).symm

theorem jasGammaSynchronizedLcmWeight_pos
    {x : ℝ} (hx : 0 < x) (P : Finset Nat.Primes) :
    0 < gammaSewnSynchronizedLcmWeight x P := by
  by_cases hP : P = ∅
  · subst P
    simp [gammaSewnSynchronizedLcmWeight]
  · exact jasGammaWeight_pos hx (Finset.nonempty_iff_ne_empty.mpr hP)

def jasGammaBooleanInsertionGain
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) : ℝ :=
  gammaSewnSynchronizedLcmWeight x (insert p P) /
    gammaSewnSynchronizedLcmWeight x P

theorem jasGammaBooleanInsertionGain_pos
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (P : Finset Nat.Primes) :
    0 < jasGammaBooleanInsertionGain x p P :=
  div_pos (jasGammaSynchronizedLcmWeight_pos hx _)
    (jasGammaSynchronizedLcmWeight_pos hx _)

theorem jasGammaSynchronizedLcmWeight_insert_boolean
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (P : Finset Nat.Primes) :
    gammaSewnSynchronizedLcmWeight x (insert p P) =
      jasGammaBooleanInsertionGain x p P *
        gammaSewnSynchronizedLcmWeight x P := by
  rw [jasGammaBooleanInsertionGain]
  field_simp [(jasGammaSynchronizedLcmWeight_pos hx P).ne']

theorem jasGammaBooleanInsertionGain_eq_gamma
    {x : ℝ} (hx : 0 < x) {p : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) :
    jasGammaBooleanInsertionGain x p P =
      gammaSewnSynchronizedLcmInsertionGain x p P := by
  rw [jasGammaBooleanInsertionGain,
    gammaSewnSynchronizedLcmWeight_insert hx hP hp]
  field_simp [(jasGammaSynchronizedLcmWeight_pos hx P).ne']

theorem jasGammaBooleanInsertionGain_cocycle
    {x : ℝ} (hx : 0 < x) (p q : Nat.Primes) (P : Finset Nat.Primes) :
    jasGammaBooleanInsertionGain x p P *
        jasGammaBooleanInsertionGain x q (insert p P) =
      jasGammaBooleanInsertionGain x q P *
        jasGammaBooleanInsertionGain x p (insert q P) := by
  unfold jasGammaBooleanInsertionGain
  have hP := (jasGammaSynchronizedLcmWeight_pos hx P).ne'
  have hPp := (jasGammaSynchronizedLcmWeight_pos hx (insert p P)).ne'
  have hPq := (jasGammaSynchronizedLcmWeight_pos hx (insert q P)).ne'
  field_simp [hP, hPp, hPq]
  exact congrArg (gammaSewnSynchronizedLcmWeight x)
    (Finset.insert_comm q p P)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def postUnitaryLinearPMap (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H) :
    H →ₗ.[ℂ] H where
  domain := T.domain
  toFun := U.toLinearEquiv.toLinearMap.comp T.toFun

@[simp] private theorem postUnitaryLinearPMap_apply
    (U : H ≃ₗᵢ[ℂ] H) (T : H →ₗ.[ℂ] H)
    (f : (postUnitaryLinearPMap U T).domain) :
    postUnitaryLinearPMap U T f = U (T f) := rfl

private theorem LinearPMap.IsClosed.postUnitary
    (U : H ≃ₗᵢ[ℂ] H) {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) :
    (postUnitaryLinearPMap U T).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph : ((postUnitaryLinearPMap U T).graph : Set (H × H)) =
      (fun z : H × H => (z.1, U.symm z.2)) ⁻¹' (T.graph : Set (H × H)) := by
    ext z
    change z ∈ (postUnitaryLinearPMap U T).graph ↔
      (z.1, U.symm z.2) ∈ T.graph
    rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨f, hf, hval⟩
      refine ⟨f, hf, ?_⟩
      change T f = U.symm z.2
      rw [← hval]
      simp
    · rintro ⟨f, hf, hval⟩
      refine ⟨f, hf, ?_⟩
      change U (T f) = z.2
      rw [hval]
      simp
  rw [hgraph]
  exact hT.preimage
    (continuous_fst.prodMk (U.symm.continuous.comp continuous_snd))

abbrev JASGammaBooleanL2 := DiagonalL2 (Finset Nat.Primes)

def jasGammaBooleanCreationEnergy
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) : ℝ :=
  if p ∈ P then 0 else jasGammaBooleanInsertionGain x p P

def jasGammaBooleanCreation (x : ℝ) (p : Nat.Primes) :
    JASGammaBooleanL2 →ₗ.[ℂ] JASGammaBooleanL2 :=
  postUnitaryLinearPMap (lpReindex (jasGammaSupportToggle p))
    (maximalRealDiagonal (jasGammaBooleanCreationEnergy x p))

theorem dense_jasGammaBooleanCreation_domain (x : ℝ) (p : Nat.Primes) :
    Dense ((jasGammaBooleanCreation x p).domain : Set JASGammaBooleanL2) :=
  maximalRealDiagonal_dense _

theorem jasGammaBooleanCreation_closed (x : ℝ) (p : Nat.Primes) :
    (jasGammaBooleanCreation x p).IsClosed := by
  apply LinearPMap.IsClosed.postUnitary
  exact (maximalRealDiagonal_isSelfAdjoint _).isClosed

def jasGammaBooleanBasisDomain
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) :
    (jasGammaBooleanCreation x p).domain :=
  ⟨HilbertSchmidt.lpBasis (Finset Nat.Primes) P,
    lpBasis_mem_maximalRealDiagonalDomain
      (jasGammaBooleanCreationEnergy x p) P⟩

private theorem maximalRealDiagonal_jasGammaBooleanBasis
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) :
    maximalRealDiagonal (jasGammaBooleanCreationEnergy x p)
        ⟨HilbertSchmidt.lpBasis (Finset Nat.Primes) P,
          lpBasis_mem_maximalRealDiagonalDomain
            (jasGammaBooleanCreationEnergy x p) P⟩ =
      (jasGammaBooleanCreationEnergy x p P : ℂ) •
        HilbertSchmidt.lpBasis (Finset Nat.Primes) P := by
  apply lp.ext
  funext Q
  rw [maximalRealDiagonal_apply, lp.coeFn_smul]
  change (jasGammaBooleanCreationEnergy x p Q : ℂ) *
      (HilbertSchmidt.lpBasis (Finset Nat.Primes) P :
        Finset Nat.Primes → ℂ) Q =
    (jasGammaBooleanCreationEnergy x p P : ℂ) *
      (HilbertSchmidt.lpBasis (Finset Nat.Primes) P :
        Finset Nat.Primes → ℂ) Q
  by_cases hQP : Q = P
  · subst Q
    rfl
  · rw [HilbertSchmidt.lpBasis_apply, lp.single_apply_ne _ _ _ hQP]
    simp

private theorem jasGammaBoolean_lpBasis_eq_single
    (P : Finset Nat.Primes) :
    HilbertSchmidt.lpBasis (Finset Nat.Primes) P =
      lp.single (E := fun _ : Finset Nat.Primes => ℂ) 2 P 1 := by
  apply lp.ext
  funext Q
  rw [HilbertSchmidt.lpBasis_apply]

private theorem lpReindex_jasGammaSupportToggle_basis
    (p : Nat.Primes) (P : Finset Nat.Primes) :
    lpReindex (jasGammaSupportToggle p)
        (HilbertSchmidt.lpBasis (Finset Nat.Primes) P) =
      HilbertSchmidt.lpBasis (Finset Nat.Primes)
        (jasGammaSupportToggle p P) := by
  rw [jasGammaBoolean_lpBasis_eq_single,
    jasGammaBoolean_lpBasis_eq_single]
  apply lp.ext
  funext Q
  rw [lpReindex_coe]
  simp only [lp.single_apply, Pi.single_apply, Equiv.symm_apply_eq]

/-- Literal coefficient-faithful support creation on every unoccupied Boolean basis state. -/
theorem jasGammaBooleanCreation_basis_of_not_mem
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) (hp : p ∉ P) :
    jasGammaBooleanCreation x p (jasGammaBooleanBasisDomain x p P) =
      (jasGammaBooleanInsertionGain x p P : ℂ) •
        HilbertSchmidt.lpBasis (Finset Nat.Primes) (insert p P) := by
  change lpReindex (jasGammaSupportToggle p)
      (maximalRealDiagonal (jasGammaBooleanCreationEnergy x p)
        ⟨HilbertSchmidt.lpBasis (Finset Nat.Primes) P,
          lpBasis_mem_maximalRealDiagonalDomain
            (jasGammaBooleanCreationEnergy x p) P⟩) = _
  rw [maximalRealDiagonal_jasGammaBooleanBasis, map_smul,
    lpReindex_jasGammaSupportToggle_basis]
  simp [jasGammaBooleanCreationEnergy, jasGammaSupportToggle, jasGammaSupportToggleFun, hp]

/-- On every corpus-native nonempty face, Boolean creation carries the original explicit
Gamma-sewn insertion coefficient. -/
theorem jasGammaBooleanCreation_basis_eq_gamma
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) :
    jasGammaBooleanCreation x p (jasGammaBooleanBasisDomain x p P) =
      (gammaSewnSynchronizedLcmInsertionGain x p P : ℂ) •
        HilbertSchmidt.lpBasis (Finset Nat.Primes) (insert p P) := by
  rw [jasGammaBooleanCreation_basis_of_not_mem x p P hp,
    jasGammaBooleanInsertionGain_eq_gamma hx hP hp]

/-- Creation kills a basis state whose support already contains the inserted prime. -/
theorem jasGammaBooleanCreation_basis_of_mem
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) (hp : p ∈ P) :
    jasGammaBooleanCreation x p (jasGammaBooleanBasisDomain x p P) = 0 := by
  change lpReindex (jasGammaSupportToggle p)
      (maximalRealDiagonal (jasGammaBooleanCreationEnergy x p)
        ⟨HilbertSchmidt.lpBasis (Finset Nat.Primes) P,
          lpBasis_mem_maximalRealDiagonalDomain
            (jasGammaBooleanCreationEnergy x p) P⟩) = 0
  rw [maximalRealDiagonal_jasGammaBooleanBasis]
  simp [jasGammaBooleanCreationEnergy, hp]

/-- The creation graph has no output on a support still missing the inserted prime. -/
theorem jasGammaBooleanCreation_apply_eq_zero_of_not_mem
    (x : ℝ) (p : Nat.Primes) (f : (jasGammaBooleanCreation x p).domain)
    (Q : Finset Nat.Primes) (hp : p ∉ Q) :
    (jasGammaBooleanCreation x p f : Finset Nat.Primes → ℂ) Q = 0 := by
  change (lpReindex (jasGammaSupportToggle p)
      (maximalRealDiagonal (jasGammaBooleanCreationEnergy x p) f) :
        Finset Nat.Primes → ℂ) Q = 0
  rw [lpReindex_coe, jasGammaSupportToggle_symm_apply,
    jasGammaSupportToggle_apply, if_neg hp, maximalRealDiagonal_apply]
  simp [jasGammaBooleanCreationEnergy]

/-- A prime creation is a genuine support cut, not a surjective source unit. -/
theorem jasGammaBooleanCreation_not_surjective
    (x : ℝ) (p : Nat.Primes) :
    ¬ Function.Surjective (jasGammaBooleanCreation x p) := by
  intro hsurj
  obtain ⟨f, hf⟩ := hsurj
    (HilbertSchmidt.lpBasis (Finset Nat.Primes) ∅)
  have hcoord := congrArg
    (fun z : JASGammaBooleanL2 => (z : Finset Nat.Primes → ℂ) ∅) hf
  rw [jasGammaBooleanCreation_apply_eq_zero_of_not_mem x p f ∅ (by simp)] at hcoord
  simp [HilbertSchmidt.lpBasis_apply] at hcoord

/-- Two distinct prime creations carry the same literal Gamma-sewn coefficient around every
admissible Boolean square, including the vacuum square. -/
theorem jasGammaBooleanCreation_twoPrime_basis_paths
    {x : ℝ} (hx : 0 < x) (p q : Nat.Primes) (P : Finset Nat.Primes) :
    (jasGammaBooleanInsertionGain x q (insert p P) : ℂ) •
        ((jasGammaBooleanInsertionGain x p P : ℂ) •
          HilbertSchmidt.lpBasis (Finset Nat.Primes) (insert q (insert p P))) =
      (jasGammaBooleanInsertionGain x p (insert q P) : ℂ) •
        ((jasGammaBooleanInsertionGain x q P : ℂ) •
          HilbertSchmidt.lpBasis (Finset Nat.Primes) (insert p (insert q P))) := by
  rw [smul_smul, smul_smul]
  have hgain := jasGammaBooleanInsertionGain_cocycle hx p q P
  have hscalar :
      (jasGammaBooleanInsertionGain x q (insert p P) : ℂ) *
          (jasGammaBooleanInsertionGain x p P : ℂ) =
        (jasGammaBooleanInsertionGain x p (insert q P) : ℂ) *
          (jasGammaBooleanInsertionGain x q P : ℂ) := by
    norm_cast
    rw [mul_comm
        (jasGammaBooleanInsertionGain x q (insert p P))
        (jasGammaBooleanInsertionGain x p P),
      hgain,
      mul_comm
        (jasGammaBooleanInsertionGain x q P)
        (jasGammaBooleanInsertionGain x p (insert q P))]
  rw [hscalar, Finset.insert_comm q p P]

def jasGammaBooleanScaledBasisDomain
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) (c : ℂ) :
    (jasGammaBooleanCreation x p).domain :=
  c • jasGammaBooleanBasisDomain x p P

theorem jasGammaBooleanCreation_scaledBasis
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) (c : ℂ) :
    jasGammaBooleanCreation x p
        (jasGammaBooleanScaledBasisDomain x p P c) =
      c • jasGammaBooleanCreation x p
        (jasGammaBooleanBasisDomain x p P) := by
  exact (jasGammaBooleanCreation x p).toFun.map_smul c
    (jasGammaBooleanBasisDomain x p P)

/-- The actual closed partial operators commute on every admissible two-prime Boolean square. -/
theorem jasGammaBooleanCreation_twoPrime_operator_paths
    {x : ℝ} (hx : 0 < x) {p q : Nat.Primes} {P : Finset Nat.Primes}
    (hp : p ∉ P) (hq : q ∉ P) (hpq : p ≠ q) :
    jasGammaBooleanCreation x q
        (jasGammaBooleanScaledBasisDomain x q (insert p P)
          (jasGammaBooleanInsertionGain x p P : ℂ)) =
      jasGammaBooleanCreation x p
        (jasGammaBooleanScaledBasisDomain x p (insert q P)
          (jasGammaBooleanInsertionGain x q P : ℂ)) := by
  rw [jasGammaBooleanCreation_scaledBasis,
    jasGammaBooleanCreation_scaledBasis,
    jasGammaBooleanCreation_basis_of_not_mem x q (insert p P)
      (by simp [hq, hpq.symm]),
    jasGammaBooleanCreation_basis_of_not_mem x p (insert q P)
      (by simp [hp, hpq])]
  simpa only [smul_smul, mul_comm] using
    (jasGammaBooleanCreation_twoPrime_basis_paths hx p q P)

/-- Corpus-native form: the closed operators traverse every nonempty Gamma-sewn Boolean square
with the original state-dependent insertion gains. -/
theorem jasGammaBooleanCreation_twoPrime_gamma_operator_paths
    {x : ℝ} (hx : 0 < x) {p q : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) (hq : q ∉ P) (hpq : p ≠ q) :
    jasGammaBooleanCreation x q
        (jasGammaBooleanScaledBasisDomain x q (insert p P)
          (gammaSewnSynchronizedLcmInsertionGain x p P : ℂ)) =
      jasGammaBooleanCreation x p
        (jasGammaBooleanScaledBasisDomain x p (insert q P)
          (gammaSewnSynchronizedLcmInsertionGain x q P : ℂ)) := by
  rw [← jasGammaBooleanInsertionGain_eq_gamma hx hP hp,
    ← jasGammaBooleanInsertionGain_eq_gamma hx hP hq]
  exact jasGammaBooleanCreation_twoPrime_operator_paths hx hp hq hpq

end

end RHTower
