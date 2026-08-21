import GaloisForLFunctions.HTGeometry.KleinbockMargulis.IntegerLattice

/-!
# The norm of a lattice and Lemma 5.1

For `A ∈ GL_k(ℝ)` and a rational subspace `W ⊆ ℚ^k` the number
`latticeWedgeNorm A W = ‖A v₁ ∧ … ∧ A v_j‖` — the wedge norm of the image of a `ℤ`-basis of
`W ∩ ℤ^k` — is Kleinbock–Margulis's `‖AΓ‖`.  It does not depend on the chosen basis, because two
bases differ by an integral matrix of determinant `±1`; we only need the one-sided consequence
that no integral tuple inside the lattice has a smaller wedge norm than the basis
(`wedgeNorm_le_of_int_combination`).

Lemma 5.1 then follows: adjoining a vector `v` of `W'` outside `W` to a basis of `W ∩ ℤ^k`
produces a tuple inside `W' ∩ ℤ^k` of the right length, whose wedge norm is at most
`(rank W + 1) ‖AΓ_W‖ ‖Av‖` by Laplace expansion.

Note that the constant is `rank W + 1` rather than the paper's `k`; the sharper form is what makes
the rank-one case of Theorem 5.2 (where `Γ = {0}` and `‖AΓ‖ = 1 > ρ`) come out correctly.

## Main results

* `wedgeNorm_le_of_int_combination` — the basis minimises the wedge norm.
* `lemma_5_1` — `‖AΛ‖ ≤ (rank Γ + 1) ‖AΓ‖ ‖Av‖`.
-/

open Matrix Finset Module Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {k : ℕ}

/-- The coordinatewise inclusion `ℤ^k → ℝ^k`. -/
def intToReal (v : Fin k → ℤ) : Fin k → ℝ := fun i => (v i : ℝ)

/-- `‖A·(W ∩ ℤ^k)‖`: the wedge norm of the image of a `ℤ`-basis of the lattice `W ∩ ℤ^k`. -/
noncomputable def latticeWedgeNorm (A : Matrix (Fin k) (Fin k) ℝ)
    (W : Submodule ℚ (Fin k → ℚ)) : ℝ :=
  wedgeNorm fun a => A.mulVec (intToReal (latticeBasis W a))

theorem intPoints_mono {W W' : Submodule ℚ (Fin k → ℚ)} (h : W ≤ W') :
    intPoints W ≤ intPoints W' := fun _ hv => h hv

/-- Reindexing a tuple along an equality of lengths does not change the wedge norm. -/
theorem wedgeNorm_reindex {j j' : ℕ} (h : j = j') (V : Fin j' → (Fin k → ℝ)) :
    wedgeNorm (fun a : Fin j => V (Fin.cast h a)) = wedgeNorm V := by
  subst h
  simp

/-- A tuple of lattice vectors of full length has wedge norm at least that of a basis, unless it
is degenerate: the transition matrix is integral, so its determinant is either zero or at least
one in absolute value. -/
theorem wedgeNorm_le_of_int_combination {n : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    {B U : Fin n → (Fin k → ℤ)} {T : Matrix (Fin n) (Fin n) ℤ}
    (hT : ∀ a i, U a i = ∑ b, T a b * B b i) (hdet : T.det ≠ 0) :
    wedgeNorm (fun a => A.mulVec (intToReal (B a)))
      ≤ wedgeNorm (fun a => A.mulVec (intToReal (U a))) := by
  classical
  set TR : Matrix (Fin n) (Fin n) ℝ := T.map (fun z : ℤ => (z : ℝ)) with hTR
  have hdetR : TR.det = ((T.det : ℤ) : ℝ) := by
    rw [hTR]
    exact (RingHom.map_det (Int.castRingHom ℝ) T).symm
  have habs : (1 : ℝ) ≤ |TR.det| := by
    rw [hdetR, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (by omega : T.det ≠ 0)
  have hcomb : (fun a => A.mulVec (intToReal (U a)))
      = fun a c => ∑ b, TR a b * (A.mulVec (intToReal (B b))) c := by
    funext a c
    simp only [Matrix.mulVec, dotProduct, intToReal, hTR, Matrix.map_apply]
    have hUa : ∀ d, ((U a d : ℤ) : ℝ) = ∑ b, ((T a b : ℤ) : ℝ) * ((B b d : ℤ) : ℝ) := by
      intro d
      rw [hT a d]
      push_cast
      rfl
    calc ∑ d, A c d * ((U a d : ℤ) : ℝ)
        = ∑ d, ∑ b, A c d * (((T a b : ℤ) : ℝ) * ((B b d : ℤ) : ℝ)) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [hUa d, Finset.mul_sum]
      _ = ∑ b, ∑ d, ((T a b : ℤ) : ℝ) * (A c d * ((B b d : ℤ) : ℝ)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring
      _ = ∑ b, ((T a b : ℤ) : ℝ) * ∑ d, A c d * ((B b d : ℤ) : ℝ) := by
          exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
  rw [hcomb]
  exact wedgeNorm_le_matrix_mul habs _

/-- **Lemma 5.1.**  If `W ≤ W'` are rational subspaces with `dim W' = dim W + 1` and `v` is an
integer point of `W'` outside `W`, then `‖AΓ_{W'}‖ ≤ (rank W + 1) ‖AΓ_W‖ ‖Av‖`. -/
theorem lemma_5_1 [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    {W W' : Submodule ℚ (Fin k → ℚ)} (hWW : W ≤ W') {v : Fin k → ℤ}
    (hv : v ∈ intPoints W') (hvW : intToRat v ∉ W)
    (hdim : Module.finrank ℚ W' = Module.finrank ℚ W + 1) :
    latticeWedgeNorm A W'
      ≤ ((latticeRank W : ℝ) + 1) * latticeWedgeNorm A W * ‖A.mulVec (intToReal v)‖ := by
  classical
  have hn : latticeRank W' = latticeRank W + 1 := by
    rw [latticeRank_eq_finrank, latticeRank_eq_finrank, hdim]
  set m := latticeRank W with hm
  set S : Fin (m + 1) → (Fin k → ℤ) := Fin.snoc (latticeBasis W) v with hS
  set U : Fin (latticeRank W') → (Fin k → ℤ) := fun a => S (Fin.cast hn a) with hU
  have hSmem : ∀ b : Fin (m + 1), S b ∈ intPoints W' := by
    intro b
    induction b using Fin.lastCases with
    | last => rw [hS, Fin.snoc_last]; exact hv
    | cast a' => rw [hS, Fin.snoc_castSucc]; exact intPoints_mono hWW (latticeBasis_mem W a')
  have hUmem : ∀ a, U a ∈ intPoints W' := fun a => hSmem _
  have hUcomb : ∀ a, ∃ c : Fin (latticeRank W') → ℤ,
      U a = fun i => ∑ b, c b * latticeBasis W' b i := fun a =>
    exists_int_combination W' (hUmem a)
  choose T hT using hUcomb
  set TM : Matrix (Fin (latticeRank W')) (Fin (latticeRank W')) ℤ := Matrix.of T with hTM
  -- `U` is rationally independent, so the transition matrix is nondegenerate
  have hSrat : (fun a : Fin (m + 1) => intToRat (S a))
      = Fin.snoc (fun a : Fin m => intToRat (latticeBasis W a)) (intToRat v) := by
    funext a
    induction a using Fin.lastCases with
    | last => simp [hS]
    | cast a' => simp [hS]
  have hSindep : LinearIndependent ℚ fun a : Fin (m + 1) => intToRat (S a) := by
    rw [hSrat]
    refine linearIndependent_finSnoc.mpr ⟨latticeBasis_linearIndependent W, ?_⟩
    rwa [latticeBasis_span W]
  have hUindep : LinearIndependent ℚ fun a => intToRat (U a) :=
    hSindep.comp (Fin.cast hn) (Fin.cast_injective hn)
  obtain ⟨τ, hτ⟩ := exists_plucker_ne_zero hUindep
  have hdetT : TM.det ≠ 0 := by
    intro hzero
    apply hτ
    have hcombQ : (fun a => intToRat (U a))
        = fun a c => ∑ b, (TM.map (fun z : ℤ => (z : ℚ))) a b * intToRat (latticeBasis W' b) c := by
      funext a c
      have hac := congrFun (hT a) c
      simp only [intToRat, Matrix.map_apply, hTM, Matrix.of_apply]
      rw [hac]
      push_cast
      rfl
    rw [hcombQ, plucker_matrix_mul]
    have hdmap : (TM.map (fun z : ℤ => (z : ℚ))).det = ((TM.det : ℤ) : ℚ) :=
      (RingHom.map_det (Int.castRingHom ℚ) TM).symm
    rw [hdmap, hzero]
    simp
  -- assemble
  have hstep1 : latticeWedgeNorm A W'
      ≤ wedgeNorm (fun a => A.mulVec (intToReal (U a))) := by
    refine wedgeNorm_le_of_int_combination A (T := TM) (fun a i => ?_) hdetT
    exact congrFun (hT a) i
  have hstep2 : wedgeNorm (fun a => A.mulVec (intToReal (U a)))
      = wedgeNorm (fun b : Fin (m + 1) => A.mulVec (intToReal (S b))) := by
    rw [hU]
    exact wedgeNorm_reindex hn (fun b : Fin (m + 1) => A.mulVec (intToReal (S b)))
  have hstep3 : (fun b : Fin (m + 1) => A.mulVec (intToReal (S b)))
      = Fin.snoc (fun a : Fin m => A.mulVec (intToReal (latticeBasis W a)))
          (A.mulVec (intToReal v)) := by
    funext b
    induction b using Fin.lastCases with
    | last => simp [hS]
    | cast a' => simp [hS]
  rw [hstep2, hstep3] at hstep1
  exact hstep1.trans (wedgeNorm_snoc_le _ _)

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
