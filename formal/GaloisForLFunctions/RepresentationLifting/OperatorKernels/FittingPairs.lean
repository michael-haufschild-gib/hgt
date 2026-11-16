import GaloisForLFunctions.RepresentationLifting.OperatorKernels.IndependentPreimages
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Intrinsic characterization of the Fitting pair

The power-torsion subspace and stable image form the unique complementary
pair whose first member is killed by one power and whose second member is
backward invariant. Forward invariance is a consequence, not an additional
condition. The resulting coordinates put every finite-dimensional operator
in a nilpotent/invertible block form.

This supplies the uniqueness step in the generalized-zero-eigenspace count
of Knospe--Shen--Van Peski's random-matrix degree law.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Vectors killed by some power of the operator. -/
def nilpotentPart (T : Module.End K V) : Submodule K V :=
  ⨆ n : ℕ, LinearMap.ker (T ^ n)

/-- Finite dimension gives one exponent annihilating the entire torsion subspace. -/
theorem nilpotentPart_uniform (T : Module.End K V) :
    ∃ n : ℕ, nilpotentPart T ≤ LinearMap.ker (T ^ n) := by
  obtain ⟨n, hn⟩ := T.eventually_iSup_ker_pow_eq.exists
  exact ⟨n, le_of_eq hn⟩

/-- Applying the operator preserves power torsion. -/
theorem nilpotentPart_preserved (T : Module.End K V) (x : V)
    (hx : x ∈ nilpotentPart T) : T x ∈ nilpotentPart T := by
  obtain ⟨n, hn⟩ := nilpotentPart_uniform T
  apply Submodule.mem_iSup_of_mem n
  change (T ^ n) (T x) = 0
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
  rw [show (T ^ n) x = 0 from hn hx, map_zero]

/-- Restriction to the power-torsion subspace. -/
def nilpotentPartOperator (T : Module.End K V) : Module.End K (nilpotentPart T) where
  toFun x := ⟨T x.1, nilpotentPart_preserved T x.1 x.2⟩
  map_add' _ _ := Subtype.ext (map_add T _ _)
  map_smul' _ _ := Subtype.ext (map_smul T _ _)

/-- Restricted iteration agrees with ambient iteration. -/
theorem nilpotentPartOperator_pow (T : Module.End K V) (n : ℕ) (x : nilpotentPart T) :
    ((nilpotentPartOperator T ^ n) x).1 = (T ^ n) x.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    change T (((nilpotentPartOperator T ^ n) x).1) = _
    rw [ih]

/-- The restricted torsion operator is nilpotent. -/
theorem nilpotentPartOperator_isNilpotent (T : Module.End K V) :
    IsNilpotent (nilpotentPartOperator T) := by
  obtain ⟨n, hn⟩ := nilpotentPart_uniform T
  refine ⟨n, LinearMap.ext fun x => Subtype.ext ?_⟩
  rw [nilpotentPartOperator_pow]
  exact hn x.2

/-- Complementarity, uniform torsion on the first side, and backward invariance on the second. -/
def IsFittingPair (T : Module.End K V) (U W : Submodule K V) : Prop :=
  IsCompl U W ∧ (∃ n : ℕ, U ≤ LinearMap.ker (T ^ n)) ∧ W ≤ W.map T

/-- The canonical power-torsion and stable-image pair satisfies the intrinsic conditions. -/
theorem canonical_isFittingPair (T : Module.End K V) :
    IsFittingPair T (nilpotentPart T) (stableImage T) := by
  refine ⟨T.isCompl_iSup_ker_pow_iInf_range_pow, nilpotentPart_uniform T, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := (stableImageEquiv T).surjective ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

/-- These conditions characterize both summands, without assuming forward invariance. -/
theorem isFittingPair_iff (T : Module.End K V) (U W : Submodule K V) :
    IsFittingPair T U W ↔ U = nilpotentPart T ∧ W = stableImage T := by
  constructor
  · rintro ⟨hc, ⟨n, hn⟩, hw⟩
    have hu : U ≤ nilpotentPart T := hn.trans (le_iSup (fun m => LinearMap.ker (T ^ m)) n)
    have hs : W ≤ stableImage T := by
      have hp : ∀ n : ℕ, W ≤ LinearMap.range (T ^ n) := by
        intro n
        induction n with
        | zero => intro x hx; exact ⟨x, rfl⟩
        | succ n ih =>
          intro x hx
          obtain ⟨y, hy, he⟩ := hw hx
          obtain ⟨z, hz⟩ := ih hy
          refine ⟨z, ?_⟩
          rw [pow_succ', Module.End.mul_apply, hz, he]
      exact le_iInf hp
    have hdim := Submodule.finrank_add_eq_of_isCompl hc
    have hcan := Submodule.finrank_add_eq_of_isCompl (canonical_isFittingPair T).1
    have hnu := Submodule.finrank_mono hu
    have hsw := Submodule.finrank_mono hs
    exact ⟨Submodule.eq_of_le_of_finrank_eq hu (by omega),
      Submodule.eq_of_le_of_finrank_eq hs (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    exact canonical_isFittingPair T

/-- Every finite-dimensional endomorphism has exactly one intrinsic Fitting pair. -/
theorem existsUnique_fittingPair (T : Module.End K V) :
    ∃! P : Submodule K V × Submodule K V, IsFittingPair T P.1 P.2 := by
  refine ⟨(nilpotentPart T, stableImage T), canonical_isFittingPair T, ?_⟩
  intro P hP
  obtain ⟨hU, hW⟩ := (isFittingPair_iff T P.1 P.2).mp hP
  exact Prod.ext hU hW


/-- Coordinates separating the nilpotent and invertible parts. -/
def fittingEquiv (T : Module.End K V) :
    (nilpotentPart T × stableImage T) ≃ₗ[K] V :=
  Submodule.prodEquivOfIsCompl _ _ (canonical_isFittingPair T).1

/-- In these coordinates every operator is exactly block diagonal. -/
theorem fittingEquiv_conj (T : Module.End K V) :
    (fittingEquiv T).conj ((nilpotentPartOperator T).prodMap (stableImageOperator T)) = T := by
  apply LinearMap.ext
  intro x
  obtain ⟨⟨u, v⟩, rfl⟩ := (fittingEquiv T).surjective x
  rw [LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change T u.1 + T v.1 = T (u.1 + v.1)
  exact (map_add T _ _).symm

#print axioms existsUnique_fittingPair
#print axioms nilpotentPartOperator_isNilpotent
#print axioms fittingEquiv_conj

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
