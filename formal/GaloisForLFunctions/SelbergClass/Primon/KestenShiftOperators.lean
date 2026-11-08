import GaloisForLFunctions.SelbergClass.Primon.KestenTailCyclicity
import GaloisForLFunctions.HTGeometry.LpShift
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!+# Creation and annihilation in the likelihood Hilbert space

The likelihood unitary transports the real unilateral shift to the actual
even spectral sector. Its adjoint lowers character degree. Their commutator
is the constant-character projection, and prime likelihoods are backward
shift eigenvectors with reciprocal-prime eigenvalues.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The even character of index `n`, as a state in the closed likelihood space. -/
def kestenCharacterState (n : ℕ) : KestenLikelihoodHilbert :=
  hardyLikelihoodUnitary (lp.single 2 n (1 : ℝ))

/-- The actual prime likelihood, as a state in its closed Hilbert span. -/
def kestenPrimeState (p : Nat.Primes) : KestenLikelihoodHilbert :=
  hardyLikelihoodUnitary (primeHardyKernel p)

@[simp] theorem coe_kestenCharacterState (n : ℕ) :
    (kestenCharacterState n : SemicircleL2) = spectralCharacterVector (2 * n) :=
  hardyLikelihoodEmbedding_single n

@[simp] theorem coe_kestenPrimeState (p : Nat.Primes) :
    (kestenPrimeState p : SemicircleL2) = kestenLikelihoodVector p :=
  hardyLikelihoodUnitary_kernel p

/-- Character inner products are the coordinates of the inverse likelihood unitary. -/
theorem inner_kestenCharacterState (f : KestenLikelihoodHilbert) (n : ℕ) :
    inner ℝ (kestenCharacterState n) f = hardyLikelihoodUnitary.symm f n := by
  rw [kestenCharacterState, hardyLikelihoodUnitary.inner_map_eq_flip,
    lp.inner_single_left]
  simp only [RCLike.inner_apply, conj_trivial, mul_one]

/-- Hardy coordinates of a likelihood-space state are its actual even spectral coefficients. -/
theorem hardyLikelihoodUnitary_symm_coordinate (f : KestenLikelihoodHilbert) (n : ℕ) :
    hardyLikelihoodUnitary.symm f n =
      inner ℝ (f : SemicircleL2) (spectralCharacterVector (2 * n)) := by
  rw [← inner_kestenCharacterState]
  change inner ℝ (kestenCharacterState n : SemicircleL2) (f : SemicircleL2) = _
  rw [coe_kestenCharacterState, real_inner_comm]

/-- Isometric raising of even-character degree. -/
def kestenShift : KestenLikelihoodHilbert →ₗᵢ[ℝ] KestenLikelihoodHilbert :=
  hardyLikelihoodUnitary.toLinearIsometry.comp
    (lpShift.comp hardyLikelihoodUnitary.symm.toLinearIsometry)

/-- The bounded lowering operator is the Hilbert adjoint of the raising isometry. -/
def kestenBackshift : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert :=
  kestenShift.toContinuousLinearMap.adjoint

/-- The raising operator is exactly the transported unilateral shift. -/
theorem kestenShift_unitary (x : PrimeHardy) :
    kestenShift (hardyLikelihoodUnitary x) = hardyLikelihoodUnitary (lpShift x) := by
  change hardyLikelihoodUnitary (lpShift (hardyLikelihoodUnitary.symm
    (hardyLikelihoodUnitary x))) = _
  rw [hardyLikelihoodUnitary.symm_apply_apply]

/-- Raising inserts a zero constant coefficient and shifts every later coefficient. -/
theorem hardyCoordinate_kestenShift (f : KestenLikelihoodHilbert) (n : ℕ) :
    hardyLikelihoodUnitary.symm (kestenShift f) n =
      shiftSeq (hardyLikelihoodUnitary.symm f) n := by
  change hardyLikelihoodUnitary.symm
    (hardyLikelihoodUnitary (lpShift (hardyLikelihoodUnitary.symm f))) n = _
  rw [hardyLikelihoodUnitary.symm_apply_apply]
  rfl

/-- Raising advances the even-character index by one. -/
theorem kestenShift_character (n : ℕ) :
    kestenShift (kestenCharacterState n) = kestenCharacterState (n + 1) := by
  rw [kestenCharacterState, kestenShift_unitary, kestenCharacterState]
  congr 1
  apply lp.ext
  funext k
  cases k with
  | zero => simp [lpShift_apply, lp.single_apply, Pi.single_apply]
  | succ k => simp [lpShift_apply, lp.single_apply, Pi.single_apply]

/-- The adjoint drops the constant coordinate. -/
theorem hardyCoordinate_kestenBackshift (f : KestenLikelihoodHilbert) (n : ℕ) :
    hardyLikelihoodUnitary.symm (kestenBackshift f) n =
      hardyLikelihoodUnitary.symm f (n + 1) := by
  calc
    _ = inner ℝ (kestenCharacterState n) (kestenBackshift f) :=
      (inner_kestenCharacterState _ _).symm
    _ = inner ℝ (kestenShift (kestenCharacterState n)) f :=
      ContinuousLinearMap.adjoint_inner_right kestenShift.toContinuousLinearMap _ _
    _ = _ := by rw [kestenShift_character, inner_kestenCharacterState]

/-- The bounded lowering operator agrees with the previously constructed Hardy drop. -/
theorem kestenBackshift_unitary (x : PrimeHardy) :
    kestenBackshift (hardyLikelihoodUnitary x) = hardyLikelihoodUnitary (hardyDrop x) := by
  apply hardyLikelihoodUnitary.symm.injective
  apply lp.ext
  funext n
  rw [hardyCoordinate_kestenBackshift, hardyLikelihoodUnitary.symm_apply_apply,
    hardyLikelihoodUnitary.symm_apply_apply]
  rfl

/-- Lowering is a left inverse of raising on the entire completed likelihood space. -/
theorem kestenBackshift_shift (f : KestenLikelihoodHilbert) :
    kestenBackshift (kestenShift f) = f := by
  exact congrArg (fun T : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert => T f)
    kestenShift.adjoint_comp_self

/-- Lowering kills the constant character. -/
theorem kestenBackshift_vacuum : kestenBackshift (kestenCharacterState 0) = 0 := by
  apply hardyLikelihoodUnitary.symm.injective
  apply lp.ext
  funext n
  rw [hardyCoordinate_kestenBackshift]
  simp [kestenCharacterState, lp.single_apply, Pi.single_apply]

/-- Lowering reverses every nonconstant even-character step. -/
theorem kestenBackshift_character_succ (n : ℕ) :
    kestenBackshift (kestenCharacterState (n + 1)) = kestenCharacterState n := by
  rw [← kestenShift_character, kestenBackshift_shift]

/-- Raising after lowering removes exactly the constant-character component. -/
theorem kestenShift_backshift (f : KestenLikelihoodHilbert) :
    kestenShift (kestenBackshift f) =
      f - hardyLikelihoodUnitary.symm f 0 • kestenCharacterState 0 := by
  apply hardyLikelihoodUnitary.symm.injective
  apply lp.ext
  funext n
  rw [hardyCoordinate_kestenShift]
  cases n with
  | zero =>
      simp [shiftSeq_zero, map_sub, map_smul, kestenCharacterState, lp.single_apply]
  | succ n =>
      rw [shiftSeq_succ, hardyCoordinate_kestenBackshift]
      simp [map_sub, map_smul, kestenCharacterState, lp.single_apply, Pi.single_apply]

/-- The creation-annihilation commutator is the rank-one constant-character projection. -/
theorem kestenShift_commutator (f : KestenLikelihoodHilbert) :
    kestenBackshift (kestenShift f) - kestenShift (kestenBackshift f) =
      inner ℝ (kestenCharacterState 0) f • kestenCharacterState 0 := by
  rw [kestenBackshift_shift, kestenShift_backshift, inner_kestenCharacterState]
  abel

/-- The range of raising is exactly the zero-constant-coordinate hyperplane. -/
theorem mem_range_kestenShift_iff (f : KestenLikelihoodHilbert) :
    f ∈ Set.range kestenShift ↔ hardyLikelihoodUnitary.symm f 0 = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [hardyCoordinate_kestenShift, shiftSeq_zero]
  · intro h
    refine ⟨kestenBackshift f, ?_⟩
    rw [kestenShift_backshift, h, zero_smul, sub_zero]

/-- The kernel of lowering is precisely the constant-character line. -/
theorem kestenBackshift_eq_zero_iff (f : KestenLikelihoodHilbert) :
    kestenBackshift f = 0 ↔
      f = hardyLikelihoodUnitary.symm f 0 • kestenCharacterState 0 := by
  constructor
  · intro h
    have he := kestenShift_backshift f
    rw [h, map_zero] at he
    exact sub_eq_zero.mp he.symm
  · intro h
    rw [h, map_smul, kestenBackshift_vacuum, smul_zero]

/-- Every actual prime likelihood is a backward-shift eigenvector with eigenvalue `1/p`. -/
theorem kestenBackshift_prime (p : Nat.Primes) :
    kestenBackshift (kestenPrimeState p) = primeReciprocal p • kestenPrimeState p := by
  rw [kestenPrimeState, kestenBackshift_unitary, ← map_smul]
  congr 1
  apply lp.ext
  funext n
  simp only [hardyDrop_apply, primeHardyKernel, hardyKernel_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon

