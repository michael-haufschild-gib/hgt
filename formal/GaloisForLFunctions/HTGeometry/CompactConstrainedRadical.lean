import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow
import GaloisForLFunctions.HTGeometry.CapocasaCatanesePositivity

/-!
# Finite constrained radicals of compact perturbations of the identity

For a closed Hilbert subspace `S`, the constrained radical of `I-K` consists of vectors in
`S` whose image under `I-K` is orthogonal to `S`. It is closed. If `K` is compact, it is
finite-dimensional: its diagonal identity bounds `K` below by one on that radical.
For self-adjoint `K`, semidefinite null vectors belong to this radical.
-/

open Complex Set
open scoped InnerProduct
noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- The radical after restricting the identity-minus-operator form to a subspace. -/
def compactConstrainedRadical (S : Submodule ℂ W) (K : W →L[ℂ] W) : Submodule ℂ W :=
  S ⊓ ⨅ v : S, ((innerSL ℂ (v : W)).comp (ContinuousLinearMap.id ℂ W - K)).ker

theorem mem_compactConstrainedRadical (S : Submodule ℂ W) (K : W →L[ℂ] W) (u : W) :
    u ∈ compactConstrainedRadical S K ↔
      u ∈ S ∧ ∀ v ∈ S, inner ℂ v (u - K u) = 0 := by
  simp only [compactConstrainedRadical, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker]
  exact and_congr_right fun _ => Subtype.forall

theorem isClosed_compactConstrainedRadical (S : Submodule ℂ W)
    (hS : IsClosed (S : Set W)) (K : W →L[ℂ] W) :
    IsClosed (compactConstrainedRadical S K : Set W) := by
  have he : (compactConstrainedRadical S K : Set W) =
      (S : Set W) ∩ ⋂ v : S, {u | inner ℂ (v : W) (u - K u) = 0} := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Subtype.forall]
    exact mem_compactConstrainedRadical S K u
  rw [he]
  exact hS.inter (isClosed_iInter fun v =>
    isClosed_eq (continuous_const.inner (continuous_id.sub K.continuous)) continuous_const)

/-- Compactness rules out an infinite-dimensional constrained radical. -/
theorem finiteDimensional_compactConstrainedRadical [CompleteSpace W] (S : Submodule ℂ W)
    (hS : IsClosed (S : Set W)) (K : W →L[ℂ] W) (hK : IsCompactOperator K) :
    FiniteDimensional ℂ (compactConstrainedRadical S K) := by
  apply finiteDimensional_of_isCompactOperator_of_bounded_below hK
    (compactConstrainedRadical S K) (isClosed_compactConstrainedRadical S hS K) zero_lt_one
  intro u hu
  by_cases hz : u = 0
  · simp [hz]
  obtain ⟨huS, hu⟩ := (mem_compactConstrainedRadical S K u).mp hu
  have hd := congrArg Complex.re (hu u huS)
  have hself : (inner ℂ u u).re = ‖u‖ ^ (2 : ℕ) :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  rw [inner_sub_right, Complex.sub_re, hself, Complex.zero_re] at hd
  have hc : (inner ℂ u (K u)).re ≤ ‖u‖ * ‖K u‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm u (K u))
  have hp := norm_pos_iff.mpr hz
  simp only [one_mul]
  nlinarith

/-- A null vector of the nonnegative restricted Hermitian form annihilates every test. -/
theorem mem_compactConstrainedRadical_of_null [CompleteSpace W] (S : Submodule ℂ W) (K : W →L[ℂ] W)
    (hK : IsSelfAdjoint K)
    (hpsd : ∀ u ∈ S, 0 ≤ (inner ℂ u (u - K u)).re)
    {u : W} (hu : u ∈ S) (hz : (inner ℂ u (u - K u)).re = 0) :
    u ∈ compactConstrainedRadical S K := by
  let H : S → S → ℂ := fun x y => inner ℂ (y : W) ((x : W) - K x)
  have hH : IsHermitianForm H := by
    constructor
    · intro x y z
      change inner ℂ (z : W) ((x : W) + y - K ((x : W) + y)) = _
      rw [map_add, add_sub_add_comm, inner_add_right]
    · intro c x y
      change inner ℂ (y : W) (c • (x : W) - K (c • (x : W))) = _
      rw [map_smul, ← smul_sub, inner_smul_right]
    · intro x y
      change inner ℂ (x : W) ((y : W) - K y) = star (inner ℂ (y : W) ((x : W) - K x))
      have hs := hK.isSymmetric (x : W) (y : W)
      change inner ℂ (K x) (y : W) = inner ℂ (x : W) (K y) at hs
      rw [Complex.star_def, inner_conj_symm, inner_sub_left, inner_sub_right, hs]
  refine (mem_compactConstrainedRadical S K u).mpr ⟨hu, ?_⟩
  intro v hv
  exact hH.eq_zero_of_self_re_eq_zero (fun x => hpsd x x.property)
    (u := (⟨u, hu⟩ : S)) hz (⟨v, hv⟩ : S)

end GaloisForLFunctions.HTGeometry
