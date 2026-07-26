import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow

/-!
# Equality rigidity for tight Hilbert shadows

The tight-family dimension inequality loses information only through Bessel's inequality.  This
module identifies that loss exactly: equality holds precisely when every adjoint carries the
target subspace back into the source, while strictness is witnessed by one adjoint departure.

For symmetric Fock space this says that a lowering shadow is extremal exactly when it is closed
back into the original level by every creation operator.  The weighted telescope then propagates
the local criterion through an entire graded family: global charge equality is equivalent to
two-sided lowering/creation closure at every positive-weight adjacent pair.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

private theorem tightOperatorFamily_subspace_left_trace
    {X Y J : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [Fintype J]
    (T : J → X →ₗ[ℝ] Y) (a : ℝ)
    (hleft : ∀ x, ∑ j, ‖T j x‖ ^ 2 = a * ‖x‖ ^ 2)
    (U : Submodule ℝ X) (V : Submodule ℝ Y)
    (hUV : ∀ j x, x ∈ U → T j x ∈ V) :
    a * (Module.finrank ℝ U : ℝ) =
      ∑ j, ∑ q : Fin (Module.finrank ℝ V),
        ∑ p : Fin (Module.finrank ℝ U),
          inner ℝ (((stdOrthonormalBasis ℝ U) p : U) : X)
            ((T j).adjoint (((stdOrthonormalBasis ℝ V) q : V) : Y)) ^ 2 := by
  let u := stdOrthonormalBasis ℝ U
  let v := stdOrthonormalBasis ℝ V
  have hunorm (p) : ‖((u p : U) : X)‖ ^ 2 = 1 := by
    change ‖u p‖ ^ 2 = 1
    rw [u.orthonormal.1 p]
    norm_num
  change a * (Module.finrank ℝ U : ℝ) =
    ∑ j, ∑ q, ∑ p,
      inner ℝ (((u p : U) : X)) ((T j).adjoint (((v q : V) : Y))) ^ 2
  rw [show a * (Module.finrank ℝ U : ℝ) =
      ∑ p, a * ‖((u p : U) : X)‖ ^ 2 by
        simp [hunorm, mul_comm]]
  rw [show (∑ p, a * ‖((u p : U) : X)‖ ^ 2) =
      ∑ p, ∑ j, ‖T j ((u p : U) : X)‖ ^ 2 by
        apply Finset.sum_congr rfl
        intro p _
        exact (hleft _).symm]
  rw [Finset.sum_comm]
  calc
    ∑ j, ∑ p, ‖T j ((u p : U) : X)‖ ^ 2 =
        ∑ j, ∑ p, ∑ q,
          inner ℝ ((v q : V) : Y) (T j ((u p : U) : X)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro p _
          let z : V := ⟨T j ((u p : U) : X), hUV j _ (u p).property⟩
          simpa [z] using (v.sum_sq_inner_right z).symm
    _ = ∑ j, ∑ q, ∑ p,
        inner ℝ ((u p : U) : X) ((T j).adjoint ((v q : V) : Y)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q _
          apply Finset.sum_congr rfl
          intro p _
          rw [← (T j).adjoint_inner_left, real_inner_comm]

private theorem tightOperatorFamily_subspace_right_trace
    {X Y J : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [Fintype J]
    (T : J → X →ₗ[ℝ] Y) (b : ℝ)
    (hright : ∀ y, ∑ j, ‖(T j).adjoint y‖ ^ 2 = b * ‖y‖ ^ 2)
    (V : Submodule ℝ Y) :
    b * (Module.finrank ℝ V : ℝ) =
      ∑ j, ∑ q : Fin (Module.finrank ℝ V),
        ‖(T j).adjoint (((stdOrthonormalBasis ℝ V) q : V) : Y)‖ ^ 2 := by
  let v := stdOrthonormalBasis ℝ V
  have hvnorm (q) : ‖((v q : V) : Y)‖ ^ 2 = 1 := by
    change ‖v q‖ ^ 2 = 1
    rw [v.orthonormal.1 q]
    norm_num
  change b * (Module.finrank ℝ V : ℝ) =
    ∑ j, ∑ q, ‖(T j).adjoint (((v q : V) : Y))‖ ^ 2
  rw [Finset.sum_comm]
  calc
    b * (Module.finrank ℝ V : ℝ) =
        ∑ q, b * ‖((v q : V) : Y)‖ ^ 2 := by
          simp [hvnorm, mul_comm]
    _ = ∑ q, ∑ j, ‖(T j).adjoint ((v q : V) : Y)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro q _
          exact (hright _).symm

/-- Equality in the tight-family dimension law is exactly adjoint invariance. -/
theorem tightOperatorFamily_subspace_finrank_eq_iff_adjoint_mem
    {X Y J : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [Fintype J]
    (T : J → X →ₗ[ℝ] Y) (a b : ℝ)
    (hleft : ∀ x, ∑ j, ‖T j x‖ ^ 2 = a * ‖x‖ ^ 2)
    (hright : ∀ y, ∑ j, ‖(T j).adjoint y‖ ^ 2 = b * ‖y‖ ^ 2)
    (U : Submodule ℝ X) (V : Submodule ℝ Y)
    (hUV : ∀ j x, x ∈ U → T j x ∈ V) :
    a * (Module.finrank ℝ U : ℝ) = b * (Module.finrank ℝ V : ℝ) ↔
      ∀ j y, y ∈ V → (T j).adjoint y ∈ U := by
  constructor
  · intro heq
    let u := stdOrthonormalBasis ℝ U
    let v := stdOrthonormalBasis ℝ V
    have hu : Orthonormal ℝ (fun p => ((u p : U) : X)) := by
      refine ⟨?_, ?_⟩
      · intro p
        change ‖u p‖ = 1
        exact u.orthonormal.1 p
      · intro p q hpq
        change inner ℝ (u p) (u q) = 0
        exact u.orthonormal.2 hpq
    have hleftTrace := tightOperatorFamily_subspace_left_trace T a hleft U V hUV
    have hrightTrace := tightOperatorFamily_subspace_right_trace T b hright V
    change a * (Module.finrank ℝ U : ℝ) =
      ∑ j, ∑ q, ∑ p,
        inner ℝ (((u p : U) : X)) ((T j).adjoint (((v q : V) : Y))) ^ 2
      at hleftTrace
    change b * (Module.finrank ℝ V : ℝ) =
      ∑ j, ∑ q, ‖(T j).adjoint (((v q : V) : Y))‖ ^ 2 at hrightTrace
    have hdef_nonneg (j : J) (q : Fin (Module.finrank ℝ V)) :
        0 ≤ ‖(T j).adjoint (((v q : V) : Y))‖ ^ 2 -
          ∑ p, inner ℝ (((u p : U) : X))
            ((T j).adjoint (((v q : V) : Y))) ^ 2 := by
      exact sub_nonneg.mpr (by
        simpa using (hu.sum_inner_products_le
          ((T j).adjoint (((v q : V) : Y))) (s := Finset.univ)))
    have hdef_sum :
        ∑ j, ∑ q, (‖(T j).adjoint (((v q : V) : Y))‖ ^ 2 -
          ∑ p, inner ℝ (((u p : U) : X))
            ((T j).adjoint (((v q : V) : Y))) ^ 2) = 0 := by
      simp_rw [Finset.sum_sub_distrib]
      rw [← hrightTrace, ← hleftTrace, heq, sub_self]
    have houter (j : J) :
        ∑ q, (‖(T j).adjoint (((v q : V) : Y))‖ ^ 2 -
          ∑ p, inner ℝ (((u p : U) : X))
            ((T j).adjoint (((v q : V) : Y))) ^ 2) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Finset.sum_nonneg (fun q _ => hdef_nonneg j q))).mp hdef_sum
        j (Finset.mem_univ j)
    have hdef_zero (j : J) (q : Fin (Module.finrank ℝ V)) :
        ‖(T j).adjoint (((v q : V) : Y))‖ ^ 2 -
          ∑ p, inner ℝ (((u p : U) : X))
            ((T j).adjoint (((v q : V) : Y))) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun q _ => hdef_nonneg j q)).mp (houter j) q (Finset.mem_univ q)
    have hbasis (j : J) (q : Fin (Module.finrank ℝ V)) :
        (T j).adjoint (((v q : V) : Y)) ∈ U := by
      let x := (T j).adjoint (((v q : V) : Y))
      have hs : ∑ p, inner ℝ (((u p : U) : X)) x ^ 2 = ‖x‖ ^ 2 := by
        dsimp [x]
        linarith [hdef_zero j q]
      have hproj : ‖(U.orthogonalProjection x : X)‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [← hs]
        simpa only [Submodule.coe_norm,
          Submodule.inner_orthogonalProjection_eq_of_mem_left] using
            (u.sum_sq_inner_right (U.orthogonalProjection x)).symm
      have hpy := U.orthogonalProjectionFn_norm_sq x
      have hres : ‖x - (U.orthogonalProjection x : X)‖ = 0 := by
        rw [Submodule.orthogonalProjectionFn_eq] at hpy
        nlinarith [hproj]
      have hx : x = (U.orthogonalProjection x : X) :=
        sub_eq_zero.mp (norm_eq_zero.mp hres)
      change x ∈ U
      rw [hx]
      exact (U.orthogonalProjection x).property
    intro j y hy
    let yV : V := ⟨y, hy⟩
    have hyrepr := v.sum_repr' yV
    have hycoe : y = ∑ q, inner ℝ (v q) yV • (((v q : V) : Y)) := by
      simpa using (congrArg (fun z : V => (z : Y)) hyrepr).symm
    rw [hycoe, map_sum]
    exact Submodule.sum_mem U fun q _ => by
      rw [LinearMap.map_smul]
      exact U.smul_mem _ (hbasis j q)
  · intro hVU
    apply le_antisymm
    · exact tightOperatorFamily_subspace_finrank T a b hleft hright U V hUV
    · have hrev := tightOperatorFamily_subspace_finrank
          (fun j => (T j).adjoint) b a hright
          (fun x => by simpa using hleft x) V U hVU
      simpa using hrev

/-- Strict dimension expansion is exactly witnessed by an adjoint departure. -/
theorem tightOperatorFamily_subspace_finrank_lt_iff_exists_adjoint_not_mem
    {X Y J : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [Fintype J]
    (T : J → X →ₗ[ℝ] Y) (a b : ℝ)
    (hleft : ∀ x, ∑ j, ‖T j x‖ ^ 2 = a * ‖x‖ ^ 2)
    (hright : ∀ y, ∑ j, ‖(T j).adjoint y‖ ^ 2 = b * ‖y‖ ^ 2)
    (U : Submodule ℝ X) (V : Submodule ℝ Y)
    (hUV : ∀ j x, x ∈ U → T j x ∈ V) :
    a * (Module.finrank ℝ U : ℝ) < b * (Module.finrank ℝ V : ℝ) ↔
      ∃ j y, y ∈ V ∧ (T j).adjoint y ∉ U := by
  classical
  have hle := tightOperatorFamily_subspace_finrank T a b hleft hright U V hUV
  constructor
  · intro hlt
    have hne : a * (Module.finrank ℝ U : ℝ) ≠
        b * (Module.finrank ℝ V : ℝ) := ne_of_lt hlt
    by_contra hnot
    push Not at hnot
    exact hne ((tightOperatorFamily_subspace_finrank_eq_iff_adjoint_mem
      T a b hleft hright U V hUV).2 hnot)
  · rintro ⟨j, y, hyV, hyU⟩
    apply lt_of_le_of_ne hle
    intro heq
    exact hyU ((tightOperatorFamily_subspace_finrank_eq_iff_adjoint_mem
      T a b hleft hright U V hUV).1 heq j y hyV)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Equality in the symmetric-Fock shadow law is exactly closure under every creation operator. -/
theorem symmetricFockLoweringShadow_finrank_eq_iff_adjoint_mem
    (n : ℕ) (U : Submodule ℝ (EuclideanSpace ℝ (Sym I (n + 1)))) :
    (n + 1 : ℝ) * (Module.finrank ℝ U : ℝ) =
        (n + Fintype.card I : ℝ) *
          (Module.finrank ℝ (symmetricFockLoweringShadow n U) : ℝ) ↔
      ∀ (i : I) (y : EuclideanSpace ℝ (Sym I n)),
        y ∈ symmetricFockLoweringShadow n U →
        (symmetricFockAnnihilation n i).adjoint y ∈ U := by
  exact tightOperatorFamily_subspace_finrank_eq_iff_adjoint_mem
    (X := EuclideanSpace ℝ (Sym I (n + 1)))
    (Y := EuclideanSpace ℝ (Sym I n)) (J := I)
    (T := symmetricFockAnnihilation n)
    (a := (n + 1 : ℝ)) (b := (n + Fintype.card I : ℝ))
    (symmetricFockAnnihilation_energy n)
    (symmetricFockAnnihilation_adjoint_energy n)
    U (symmetricFockLoweringShadow n U)
    (annihilation_mem_loweringShadow n U)

/-- Strict symmetric-Fock shadow expansion is exactly detected by a creation departure. -/
theorem symmetricFockLoweringShadow_finrank_lt_iff_exists_adjoint_not_mem
    (n : ℕ) (U : Submodule ℝ (EuclideanSpace ℝ (Sym I (n + 1)))) :
    (n + 1 : ℝ) * (Module.finrank ℝ U : ℝ) <
        (n + Fintype.card I : ℝ) *
          (Module.finrank ℝ (symmetricFockLoweringShadow n U) : ℝ) ↔
      ∃ (i : I) (y : EuclideanSpace ℝ (Sym I n)),
        y ∈ symmetricFockLoweringShadow n U ∧
        (symmetricFockAnnihilation n i).adjoint y ∉ U := by
  exact tightOperatorFamily_subspace_finrank_lt_iff_exists_adjoint_not_mem
    (X := EuclideanSpace ℝ (Sym I (n + 1)))
    (Y := EuclideanSpace ℝ (Sym I n)) (J := I)
    (T := symmetricFockAnnihilation n)
    (a := (n + 1 : ℝ)) (b := (n + Fintype.card I : ℝ))
    (symmetricFockAnnihilation_energy n)
    (symmetricFockAnnihilation_adjoint_energy n)
    U (symmetricFockLoweringShadow n U)
    (annihilation_mem_loweringShadow n U)

/-- Equality in the weighted endpoint charge is exactly equality at every positive-weight step. -/
theorem weightedFockShadowCharge_eq_iff
    (e M : ℕ) (h : ℕ → ℝ)
    (hstep : ∀ n < M,
      ((n + 1 : ℕ) : ℝ) * h (n + 1) ≤ ((n + e : ℕ) : ℝ) * h n) :
    (M : ℝ) * ((M : ℝ) - 1) * h M =
        ((e + 1 : ℕ) : ℝ) * ∑ n ∈ Finset.range M, (n : ℝ) * h n ↔
      ∀ n < M, 0 < n →
        ((n + 1 : ℕ) : ℝ) * h (n + 1) = ((n + e : ℕ) : ℝ) * h n := by
  have hterm_nonneg (n : ℕ) (hn : n ∈ Finset.range M) : 0 ≤
      (n : ℝ) * (((n + e : ℕ) : ℝ) * h n -
        ((n + 1 : ℕ) : ℝ) * h (n + 1)) := by
    apply mul_nonneg (Nat.cast_nonneg n)
    linarith [hstep n (Finset.mem_range.mp hn)]
  constructor
  · intro heq
    have hsum : ∑ n ∈ Finset.range M,
        (n : ℝ) * (((n + e : ℕ) : ℝ) * h n -
          ((n + 1 : ℕ) : ℝ) * h (n + 1)) = 0 := by
      rw [weightedFockShadow_telescope]
      linarith
    intro n hn hnpos
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum
      n (Finset.mem_range.mpr hn)
    have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnpos
    nlinarith
  · intro heq
    have hsum : ∑ n ∈ Finset.range M,
        (n : ℝ) * (((n + e : ℕ) : ℝ) * h n -
          ((n + 1 : ℕ) : ℝ) * h (n + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hnzero : n = 0
      · simp [hnzero]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
        rw [heq n (Finset.mem_range.mp hn) hnpos]
        ring
    rw [weightedFockShadow_telescope] at hsum
    linarith

/-- Equality in the graded Fock charge law is exactly two-sided lowering/creation closure at
every positive-weight adjacent pair. -/
theorem gradedFockLoweringCharge_eq_iff_levelwise_creator_closed
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n) :
    (M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) =
        ((Fintype.card I + 1 : ℕ) : ℝ) * gradedFockLoweringCharge M U ↔
      ∀ n < M, 0 < n →
        symmetricFockLoweringShadow n (U (n + 1)) = U n ∧
          ∀ (i : I) (y : EuclideanSpace ℝ (Sym I n)), y ∈ U n →
            (symmetricFockAnnihilation n i).adjoint y ∈ U (n + 1) := by
  let h : ℕ → ℝ := fun n => (Module.finrank ℝ (U n) : ℝ)
  have hstep : ∀ n < M,
      ((n + 1 : ℕ) : ℝ) * h (n + 1) ≤
        ((n + Fintype.card I : ℕ) : ℝ) * h n := by
    intro n hn
    dsimp [h]
    norm_num only [Nat.cast_add, Nat.cast_one]
    calc
      (n + 1 : ℝ) * (Module.finrank ℝ (U (n + 1)) : ℝ) ≤
          (n + Fintype.card I : ℝ) *
            (Module.finrank ℝ
              (symmetricFockLoweringShadow n (U (n + 1))) : ℝ) :=
        symmetricFockLoweringShadow_finrank n (U (n + 1))
      _ ≤ (n + Fintype.card I : ℝ) *
          (Module.finrank ℝ (U n) : ℝ) := by
        gcongr
        exact_mod_cast Submodule.finrank_mono (hshadow n hn)
  rw [show gradedFockLoweringCharge M U =
      ∑ n ∈ Finset.range M, (n : ℝ) * h n by rfl]
  rw [weightedFockShadowCharge_eq_iff (Fintype.card I) M h hstep]
  constructor
  · intro heq n hn hnpos
    have hlocal := heq n hn hnpos
    dsimp [h] at hlocal
    have hbase := symmetricFockLoweringShadow_finrank n (U (n + 1))
    have hmono :
        (Module.finrank ℝ
          (symmetricFockLoweringShadow n (U (n + 1))) : ℝ) ≤
            (Module.finrank ℝ (U n) : ℝ) := by
      exact_mod_cast Submodule.finrank_mono (hshadow n hn)
    have hnpos' : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hcard : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
    have hc : 0 < (n : ℝ) + (Fintype.card I : ℝ) := by
      nlinarith
    have hshadowRank :
        (Module.finrank ℝ
          (symmetricFockLoweringShadow n (U (n + 1))) : ℝ) =
            (Module.finrank ℝ (U n) : ℝ) := by
      push_cast at hbase hlocal
      nlinarith
    have hshadowRankNat :
        Module.finrank ℝ (symmetricFockLoweringShadow n (U (n + 1))) =
          Module.finrank ℝ (U n) := by
      exact_mod_cast hshadowRank
    have hspace : symmetricFockLoweringShadow n (U (n + 1)) = U n :=
      Submodule.eq_of_le_of_finrank_eq (hshadow n hn) hshadowRankNat
    have hshadowEq :
        (n + 1 : ℝ) * (Module.finrank ℝ (U (n + 1)) : ℝ) =
          (n + Fintype.card I : ℝ) *
            (Module.finrank ℝ
              (symmetricFockLoweringShadow n (U (n + 1))) : ℝ) := by
      push_cast at hbase hlocal
      nlinarith
    refine ⟨hspace, ?_⟩
    have hcreator :=
      (symmetricFockLoweringShadow_finrank_eq_iff_adjoint_mem n (U (n + 1))).1
        hshadowEq
    intro i y hy
    apply hcreator i y
    rw [hspace]
    exact hy
  · intro hclosed n hn hnpos
    rcases hclosed n hn hnpos with ⟨hspace, hcreator⟩
    have hcreatorShadow : ∀ (i : I) (y : EuclideanSpace ℝ (Sym I n)),
        y ∈ symmetricFockLoweringShadow n (U (n + 1)) →
          (symmetricFockAnnihilation n i).adjoint y ∈ U (n + 1) := by
      intro i y hy
      apply hcreator i y
      rwa [← hspace]
    have heq :=
      (symmetricFockLoweringShadow_finrank_eq_iff_adjoint_mem n (U (n + 1))).2
        hcreatorShadow
    dsimp [h]
    norm_num only [Nat.cast_add, Nat.cast_one]
    rwa [hspace] at heq

/-- A strict graded charge gap is exactly witnessed at a positive level by an incomplete lowering
shadow or by a creation operator leaving the next level. -/
theorem gradedFockLoweringCharge_lt_iff_exists_level_defect
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n) :
    (M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) <
        ((Fintype.card I + 1 : ℕ) : ℝ) * gradedFockLoweringCharge M U ↔
      ∃ n < M, 0 < n ∧
        (symmetricFockLoweringShadow n (U (n + 1)) ≠ U n ∨
          ∃ (i : I) (y : EuclideanSpace ℝ (Sym I n)), y ∈ U n ∧
            (symmetricFockAnnihilation n i).adjoint y ∉ U (n + 1)) := by
  classical
  have hle := gradedFockLoweringCharge_lower_bound M U hshadow
  constructor
  · intro hlt
    by_contra hnot
    have hclosed : ∀ n < M, 0 < n →
        symmetricFockLoweringShadow n (U (n + 1)) = U n ∧
          ∀ (i : I) (y : EuclideanSpace ℝ (Sym I n)), y ∈ U n →
            (symmetricFockAnnihilation n i).adjoint y ∈ U (n + 1) := by
      intro n hn hnpos
      have hnodefect : ¬
          (symmetricFockLoweringShadow n (U (n + 1)) ≠ U n ∨
            ∃ (i : I) (y : EuclideanSpace ℝ (Sym I n)), y ∈ U n ∧
              (symmetricFockAnnihilation n i).adjoint y ∉ U (n + 1)) := by
        intro hdefect
        exact hnot ⟨n, hn, hnpos, hdefect⟩
      have hparts := not_or.mp hnodefect
      refine ⟨not_ne_iff.mp hparts.1, ?_⟩
      intro i y hy
      by_contra hyout
      exact hparts.2 ⟨i, y, hy, hyout⟩
    have heq :=
      (gradedFockLoweringCharge_eq_iff_levelwise_creator_closed M U hshadow).2 hclosed
    exact (ne_of_lt hlt) heq
  · rintro ⟨n, hn, hnpos, hspace | ⟨i, y, hy, hyout⟩⟩
    · apply lt_of_le_of_ne hle
      intro heq
      exact hspace
        ((gradedFockLoweringCharge_eq_iff_levelwise_creator_closed M U hshadow).1
          heq n hn hnpos).1
    · apply lt_of_le_of_ne hle
      intro heq
      have hclosed :=
        (gradedFockLoweringCharge_eq_iff_levelwise_creator_closed M U hshadow).1
          heq n hn hnpos
      exact hyout (hclosed.2 i y hy)

end

end GaloisForLFunctions.HilbertMetric
