import GaloisForLFunctions.HTGeometry.TwoReplicaLocalSingletSynchronization
import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordHallSymmetryReduction

/-!
# Global physical realization of two-replica singlet synchronization

This file embeds the sitewise identity/swap coefficient model into the literal
two-replica matrix algebra on an arbitrary finite qubit register.  An explicit
Möbius coefficient extractor proves that no coefficient information is lost.
The subsequent edge-Casimir bridge identifies the coefficient synchronization
law with weight-two collective Pauli commutator squares.
-/

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reassociate two replica configurations into a configuration of local
two-replica indices. -/
def finiteTwoReplicaConfigurationEquiv (V : Type*) :
    FiniteTwoReplicaConfiguration V ≃ (V → TwoReplicaLocalIndex) where
  toFun x v := (x.1 v, x.2 v)
  invFun x := (fun v => (x v).1, fun v => (x v).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Tensor product, over sites, of arbitrary local two-replica matrices. -/
def finiteTwoReplicaLocalMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : V → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    FiniteTwoReplicaMatrix V :=
  fun x y => ∏ v, M v (x.1 v, x.2 v) (y.1 v, y.2 v)

/-- Sitewise tensor products multiply sitewise. -/
theorem finiteTwoReplicaLocalMatrix_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (M N : V → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    finiteTwoReplicaLocalMatrix M * finiteTwoReplicaLocalMatrix N =
      finiteTwoReplicaLocalMatrix fun v => M v * N v := by
  ext x z
  rw [Matrix.mul_apply]
  change (∑ y : FiniteTwoReplicaConfiguration V,
      (∏ v, M v (x.1 v, x.2 v) (y.1 v, y.2 v)) *
        (∏ v, N v (y.1 v, y.2 v) (z.1 v, z.2 v))) =
    ∏ v, ∑ y : TwoReplicaLocalIndex,
      M v (x.1 v, x.2 v) y * N v y (z.1 v, z.2 v)
  simp_rw [← Finset.prod_mul_distrib]
  calc
    (∑ y : FiniteTwoReplicaConfiguration V,
        ∏ v, M v (x.1 v, x.2 v) (y.1 v, y.2 v) *
          N v (y.1 v, y.2 v) (z.1 v, z.2 v)) =
        ∑ y : V → TwoReplicaLocalIndex,
          ∏ v, M v (x.1 v, x.2 v) (y v) *
            N v (y v) (z.1 v, z.2 v) := by
      exact Fintype.sum_equiv (finiteTwoReplicaConfigurationEquiv V) _ _
        (fun _ => rfl)
    _ = ∏ v, ∑ y : TwoReplicaLocalIndex,
          M v (x.1 v, x.2 v) y * N v y (z.1 v, z.2 v) :=
      (Fintype.prod_sum fun v (y : TwoReplicaLocalIndex) =>
        M v (x.1 v, x.2 v) y * N v y (z.1 v, z.2 v)).symm

/-- A global physical word with identity or replica swap independently at
each site. -/
def finiteTwoReplicaSwapRaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → Bool) : FiniteTwoReplicaMatrix V :=
  finiteTwoReplicaLocalMatrix fun v => twoReplicaLocalSwapRaw (x v)

/-- Physical embedding of global identity/swap coefficients. -/
def finiteTwoReplicaSwapInvariantEmbed
    {V : Type*} [Fintype V] [DecidableEq V] :
    TwoReplicaGlobalCoeff V →ₗ[ℂ] FiniteTwoReplicaMatrix V where
  toFun c := ∑ x : V → Bool, c x • finiteTwoReplicaSwapRaw x
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

/-- Local Möbius weight dual to the ordered basis `(identity, swap)`. -/
def twoReplicaSwapDualWeight (target choice : Bool) : ℂ :=
  match target, choice with
  | false, false => 1
  | false, true => -1
  | true, false => 0
  | true, true => 1

/-- Row configuration used by the global Möbius coefficient extractor. -/
def finiteTwoReplicaSwapDualRow
    {V : Type*} (choice : V → Bool) : FiniteTwoReplicaConfiguration V :=
  (fun _ => false, choice)

/-- Column configuration used by the global Möbius coefficient extractor. -/
def finiteTwoReplicaSwapDualColumn
    {V : Type*} (choice : V → Bool) : FiniteTwoReplicaConfiguration V :=
  (choice, fun _ => false)

/-- Explicit coefficient functional dual to one global identity/swap word. -/
def finiteTwoReplicaSwapCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (target : V → Bool) : FiniteTwoReplicaMatrix V →ₗ[ℂ] ℂ where
  toFun X := ∑ choice : V → Bool,
    (∏ v, twoReplicaSwapDualWeight (target v) (choice v)) *
      X (finiteTwoReplicaSwapDualRow choice)
        (finiteTwoReplicaSwapDualColumn choice)
  map_add' X Y := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z X := by
    simp only [Matrix.smul_apply, smul_eq_mul]
    change (∑ choice : V → Bool,
        (∏ v, twoReplicaSwapDualWeight (target v) (choice v)) *
          (z * X (finiteTwoReplicaSwapDualRow choice)
            (finiteTwoReplicaSwapDualColumn choice))) =
      z * ∑ choice : V → Bool,
        (∏ v, twoReplicaSwapDualWeight (target v) (choice v)) *
          X (finiteTwoReplicaSwapDualRow choice)
            (finiteTwoReplicaSwapDualColumn choice)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro choice _
    ring

@[simp] theorem twoReplicaLocalSwapRaw_dualEntry
    (word choice : Bool) :
    twoReplicaLocalSwapRaw word (false, choice) (choice, false) =
      if choice then (if word then 1 else 0) else 1 := by
  fin_cases word <;> fin_cases choice <;>
    simp [twoReplicaLocalSwapRaw, twoReplicaSwap]

@[simp] theorem twoReplicaSwapDualWeight_sum_entry
    (target word : Bool) :
    (∑ choice : Bool,
      twoReplicaSwapDualWeight target choice *
        twoReplicaLocalSwapRaw word
          (false, choice) (choice, false)) =
      if target = word then 1 else 0 := by
  fin_cases target <;> fin_cases word <;>
    norm_num [twoReplicaSwapDualWeight, Fintype.sum_bool]

theorem finite_prod_bool_delta
    {V : Type*} [Fintype V] [DecidableEq V]
    (x y : V → Bool) :
    (∏ v, if x v = y v then (1 : ℂ) else 0) =
      if x = y then 1 else 0 := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [if_neg hxy]
    have hpoint : ∃ v, x v ≠ y v := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    rcases hpoint with ⟨v, hv⟩
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv]

/-- The Möbius extractor is exactly dual to every global physical swap word. -/
@[simp] theorem finiteTwoReplicaSwapCoefficient_raw
    {V : Type*} [Fintype V] [DecidableEq V]
    (target word : V → Bool) :
    finiteTwoReplicaSwapCoefficient target
        (finiteTwoReplicaSwapRaw word) =
      if target = word then 1 else 0 := by
  change (∑ choice : V → Bool,
      (∏ v, twoReplicaSwapDualWeight (target v) (choice v)) *
        ∏ v, twoReplicaLocalSwapRaw (word v)
          (false, choice v) (choice v, false)) = _
  simp_rw [← Finset.prod_mul_distrib]
  calc
    (∑ choice : V → Bool,
        ∏ v, twoReplicaSwapDualWeight (target v) (choice v) *
          twoReplicaLocalSwapRaw (word v)
            (false, choice v) (choice v, false)) =
        ∏ v, ∑ choice : Bool,
          twoReplicaSwapDualWeight (target v) choice *
            twoReplicaLocalSwapRaw (word v)
              (false, choice) (choice, false) :=
      (Fintype.prod_sum fun v (choice : Bool) =>
        twoReplicaSwapDualWeight (target v) choice *
          twoReplicaLocalSwapRaw (word v)
            (false, choice) (choice, false)).symm
    _ = ∏ v, if target v = word v then (1 : ℂ) else 0 := by
      apply Finset.prod_congr rfl
      intro v _
      exact twoReplicaSwapDualWeight_sum_entry (target v) (word v)
    _ = if target = word then 1 else 0 := finite_prod_bool_delta target word

/-- Global identity/swap coefficients are recovered exactly from their
physical matrix embedding. -/
@[simp] theorem finiteTwoReplicaSwapCoefficient_embed
    {V : Type*} [Fintype V] [DecidableEq V]
    (target : V → Bool) (c : TwoReplicaGlobalCoeff V) :
    finiteTwoReplicaSwapCoefficient target
        (finiteTwoReplicaSwapInvariantEmbed c) = c target := by
  change finiteTwoReplicaSwapCoefficient target
      (∑ word : V → Bool, c word • finiteTwoReplicaSwapRaw word) = _
  rw [map_sum]
  simp_rw [map_smul, finiteTwoReplicaSwapCoefficient_raw]
  simp

/-- The physical global identity/swap embedding is injective on every finite
register. -/
theorem finiteTwoReplicaSwapInvariantEmbed_injective
    {V : Type*} [Fintype V] [DecidableEq V] :
    Function.Injective
      (finiteTwoReplicaSwapInvariantEmbed (V := V)) := by
  intro c d hcd
  funext target
  rw [← finiteTwoReplicaSwapCoefficient_embed target c,
    ← finiteTwoReplicaSwapCoefficient_embed target d, hcd]

/-! ## Tensor extension from one physical edge -/

/-- Sites outside an ordered edge. -/
abbrev FiniteTwoReplicaEdgeOutside
    {V : Type*} (u v : V) := {w : V // w ≠ u ∧ w ≠ v}

/-- Split a local-index configuration into its two edge endpoints and all
outside sites. -/
def finiteTwoReplicaLocalEdgeEquiv
    {V : Type*} [DecidableEq V] (u v : V) (huv : u ≠ v) :
    (V → TwoReplicaLocalIndex) ≃
      (TwoReplicaEdgeIndex ×
        (FiniteTwoReplicaEdgeOutside u v → TwoReplicaLocalIndex)) where
  toFun x := ((x u, x v), fun w => x w.1)
  invFun x w :=
    if hwu : w = u then x.1.1
    else if hwv : w = v then x.1.2
    else x.2 ⟨w, hwu, hwv⟩
  left_inv x := by
    funext w
    by_cases hwu : w = u
    · subst w
      simp
    by_cases hwv : w = v
    · subst w
      simp [hwu]
    simp [hwu, hwv]
  right_inv x := by
    rcases x with ⟨p, outside⟩
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [huv.symm]
    · funext w
      simp [w.property.1, w.property.2]

/-- Split a two-replica global configuration directly into edge endpoints
and outside local indices. -/
def finiteTwoReplicaEdgeConfigurationEquiv
    {V : Type*} [DecidableEq V] (u v : V) (huv : u ≠ v) :
    FiniteTwoReplicaConfiguration V ≃
      (TwoReplicaEdgeIndex ×
        (FiniteTwoReplicaEdgeOutside u v → TwoReplicaLocalIndex)) :=
  (finiteTwoReplicaConfigurationEquiv V).trans
    (finiteTwoReplicaLocalEdgeEquiv u v huv)

/-- Tensor an arbitrary two-site two-replica matrix with arbitrary local
matrices on every site outside the edge. -/
def finiteTwoReplicaEdgeExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V)
    (S : FiniteTwoReplicaEdgeOutside u v →
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (A : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    FiniteTwoReplicaMatrix V :=
  fun x y =>
    A ((x.1 u, x.2 u), (x.1 v, x.2 v))
        ((y.1 u, y.2 u), (y.1 v, y.2 v)) *
      ∏ w : FiniteTwoReplicaEdgeOutside u v,
        S w (x.1 w.1, x.2 w.1) (y.1 w.1, y.2 w.1)

/-- Edge extensions multiply as the edge matrix and every spectator matrix
multiply. -/
theorem finiteTwoReplicaEdgeExtension_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (S T : FiniteTwoReplicaEdgeOutside u v →
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (A B : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    finiteTwoReplicaEdgeExtension u v S A *
        finiteTwoReplicaEdgeExtension u v T B =
      finiteTwoReplicaEdgeExtension u v (fun w => S w * T w) (A * B) := by
  ext x z
  rw [Matrix.mul_apply]
  change (∑ y : FiniteTwoReplicaConfiguration V,
      (A ((x.1 u, x.2 u), (x.1 v, x.2 v))
          ((y.1 u, y.2 u), (y.1 v, y.2 v)) *
        ∏ w : FiniteTwoReplicaEdgeOutside u v,
          S w (x.1 w.1, x.2 w.1) (y.1 w.1, y.2 w.1)) *
      (B ((y.1 u, y.2 u), (y.1 v, y.2 v))
          ((z.1 u, z.2 u), (z.1 v, z.2 v)) *
        ∏ w : FiniteTwoReplicaEdgeOutside u v,
          T w (y.1 w.1, y.2 w.1) (z.1 w.1, z.2 w.1))) =
    (∑ p : TwoReplicaEdgeIndex,
      A ((x.1 u, x.2 u), (x.1 v, x.2 v)) p *
        B p ((z.1 u, z.2 u), (z.1 v, z.2 v))) *
      ∏ w : FiniteTwoReplicaEdgeOutside u v,
        ∑ q : TwoReplicaLocalIndex,
          S w (x.1 w.1, x.2 w.1) q *
            T w q (z.1 w.1, z.2 w.1)
  calc
    (∑ y : FiniteTwoReplicaConfiguration V,
        (A ((x.1 u, x.2 u), (x.1 v, x.2 v))
            ((y.1 u, y.2 u), (y.1 v, y.2 v)) *
          ∏ w : FiniteTwoReplicaEdgeOutside u v,
            S w (x.1 w.1, x.2 w.1) (y.1 w.1, y.2 w.1)) *
        (B ((y.1 u, y.2 u), (y.1 v, y.2 v))
            ((z.1 u, z.2 u), (z.1 v, z.2 v)) *
          ∏ w : FiniteTwoReplicaEdgeOutside u v,
            T w (y.1 w.1, y.2 w.1) (z.1 w.1, z.2 w.1))) =
      ∑ y : TwoReplicaEdgeIndex ×
          (FiniteTwoReplicaEdgeOutside u v → TwoReplicaLocalIndex),
        (A ((x.1 u, x.2 u), (x.1 v, x.2 v)) y.1 *
          B y.1 ((z.1 u, z.2 u), (z.1 v, z.2 v))) *
        ∏ w : FiniteTwoReplicaEdgeOutside u v,
          S w (x.1 w.1, x.2 w.1) (y.2 w) *
            T w (y.2 w) (z.1 w.1, z.2 w.1) := by
        exact Fintype.sum_equiv
            (finiteTwoReplicaEdgeConfigurationEquiv u v huv) _ _ fun y => by
          change
            (A ((x.1 u, x.2 u), (x.1 v, x.2 v))
                ((y.1 u, y.2 u), (y.1 v, y.2 v)) *
              ∏ w : FiniteTwoReplicaEdgeOutside u v,
                S w (x.1 w.1, x.2 w.1) (y.1 w.1, y.2 w.1)) *
            (B ((y.1 u, y.2 u), (y.1 v, y.2 v))
                ((z.1 u, z.2 u), (z.1 v, z.2 v)) *
              ∏ w : FiniteTwoReplicaEdgeOutside u v,
                T w (y.1 w.1, y.2 w.1) (z.1 w.1, z.2 w.1)) =
            (A ((x.1 u, x.2 u), (x.1 v, x.2 v))
                ((y.1 u, y.2 u), (y.1 v, y.2 v)) *
              B ((y.1 u, y.2 u), (y.1 v, y.2 v))
                ((z.1 u, z.2 u), (z.1 v, z.2 v))) *
            ∏ w : FiniteTwoReplicaEdgeOutside u v,
              S w (x.1 w.1, x.2 w.1) (y.1 w.1, y.2 w.1) *
                T w (y.1 w.1, y.2 w.1) (z.1 w.1, z.2 w.1)
          calc
            _ =
              (A ((x.1 u, x.2 u), (x.1 v, x.2 v))
                  ((y.1 u, y.2 u), (y.1 v, y.2 v)) *
                B ((y.1 u, y.2 u), (y.1 v, y.2 v))
                  ((z.1 u, z.2 u), (z.1 v, z.2 v))) *
              ((∏ w : FiniteTwoReplicaEdgeOutside u v,
                  S w (x.1 w.1, x.2 w.1) (y.1 w.1, y.2 w.1)) *
                ∏ w : FiniteTwoReplicaEdgeOutside u v,
                  T w (y.1 w.1, y.2 w.1) (z.1 w.1, z.2 w.1)) := by ring
            _ = _ := by rw [Finset.prod_mul_distrib]
    _ = ∑ p : TwoReplicaEdgeIndex,
        ∑ outside : FiniteTwoReplicaEdgeOutside u v → TwoReplicaLocalIndex,
          (A ((x.1 u, x.2 u), (x.1 v, x.2 v)) p *
            B p ((z.1 u, z.2 u), (z.1 v, z.2 v))) *
          ∏ w : FiniteTwoReplicaEdgeOutside u v,
            S w (x.1 w.1, x.2 w.1) (outside w) *
              T w (outside w) (z.1 w.1, z.2 w.1) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ p : TwoReplicaEdgeIndex,
        (A ((x.1 u, x.2 u), (x.1 v, x.2 v)) p *
          B p ((z.1 u, z.2 u), (z.1 v, z.2 v))) *
        ∏ w : FiniteTwoReplicaEdgeOutside u v,
          ∑ q : TwoReplicaLocalIndex,
            S w (x.1 w.1, x.2 w.1) q *
              T w q (z.1 w.1, z.2 w.1) := by
        apply Finset.sum_congr rfl
        intro p _
        let K := A ((x.1 u, x.2 u), (x.1 v, x.2 v)) p *
          B p ((z.1 u, z.2 u), (z.1 v, z.2 v))
        let f := fun (w : FiniteTwoReplicaEdgeOutside u v)
            (q : TwoReplicaLocalIndex) =>
          S w (x.1 w.1, x.2 w.1) q *
            T w q (z.1 w.1, z.2 w.1)
        change (∑ outside : FiniteTwoReplicaEdgeOutside u v →
            TwoReplicaLocalIndex, K * ∏ w, f w (outside w)) =
          K * ∏ w, ∑ q, f w q
        calc
          (∑ outside : FiniteTwoReplicaEdgeOutside u v →
              TwoReplicaLocalIndex, K * ∏ w, f w (outside w)) =
              K * ∑ outside : FiniteTwoReplicaEdgeOutside u v →
                TwoReplicaLocalIndex, ∏ w, f w (outside w) := by
            rw [Finset.mul_sum]
          _ = K * ∏ w, ∑ q, f w q := by
            rw [(Fintype.prod_sum fun w (q : TwoReplicaLocalIndex) =>
              f w q).symm]
    _ = (∑ p : TwoReplicaEdgeIndex,
        A ((x.1 u, x.2 u), (x.1 v, x.2 v)) p *
          B p ((z.1 u, z.2 u), (z.1 v, z.2 v))) *
        ∏ w : FiniteTwoReplicaEdgeOutside u v,
          ∑ q : TwoReplicaLocalIndex,
            S w (x.1 w.1, x.2 w.1) q *
              T w q (z.1 w.1, z.2 w.1) := by
        rw [Finset.sum_mul]

/-- Split a finite product into two distinguished edge factors and the
product over all outside sites. -/
theorem finite_prod_eq_edge_mul_outside
    {V : Type*} [Fintype V] [DecidableEq V]
    {M : Type*} [CommMonoid M] {u v : V} (huv : u ≠ v) (f : V → M) :
    (∏ w, f w) = f u * f v *
      ∏ w : FiniteTwoReplicaEdgeOutside u v, f w.1 := by
  rw [← Finset.mul_prod_erase Finset.univ f
    (a := u) (Finset.mem_univ u)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase u) f
    (a := v) (by simp [huv.symm])]
  rw [← Finset.prod_subtype ((Finset.univ.erase u).erase v)
    (by intro w; simp [and_comm]) f]
  simp [mul_assoc]

/-- A sitewise product is exactly the edge Kronecker product tensored with
the outside site matrices. -/
theorem finiteTwoReplicaLocalMatrix_eq_edgeExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (M : V → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    finiteTwoReplicaLocalMatrix M =
      finiteTwoReplicaEdgeExtension u v (fun w => M w.1)
        (M u ⊗ₖ M v) := by
  ext x y
  rw [finiteTwoReplicaLocalMatrix, finiteTwoReplicaEdgeExtension,
    Matrix.kroneckerMap_apply]
  exact finite_prod_eq_edge_mul_outside huv
    (fun w => M w (x.1 w, x.2 w) (y.1 w, y.2 w))

theorem finiteTwoReplicaEdgeExtension_add
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V)
    (S : FiniteTwoReplicaEdgeOutside u v →
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (A B : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    finiteTwoReplicaEdgeExtension u v S (A + B) =
      finiteTwoReplicaEdgeExtension u v S A +
        finiteTwoReplicaEdgeExtension u v S B := by
  ext x y
  simp only [finiteTwoReplicaEdgeExtension, Matrix.add_apply]
  ring

theorem finiteTwoReplicaEdgeExtension_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V)
    (S : FiniteTwoReplicaEdgeOutside u v →
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (A B : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    finiteTwoReplicaEdgeExtension u v S (A - B) =
      finiteTwoReplicaEdgeExtension u v S A -
        finiteTwoReplicaEdgeExtension u v S B := by
  ext x y
  simp only [finiteTwoReplicaEdgeExtension, Matrix.sub_apply]
  ring

theorem finiteTwoReplicaEdgeExtension_smul
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V)
    (S : FiniteTwoReplicaEdgeOutside u v →
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (z : ℂ) (A : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    finiteTwoReplicaEdgeExtension u v S (z • A) =
      z • finiteTwoReplicaEdgeExtension u v S A := by
  ext x y
  simp only [finiteTwoReplicaEdgeExtension, Matrix.smul_apply, smul_eq_mul]
  ring

theorem finiteTwoReplicaEdgeExtension_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι]
    (u v : V)
    (S : FiniteTwoReplicaEdgeOutside u v →
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (A : ι → Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    finiteTwoReplicaEdgeExtension u v S (∑ i, A i) =
      ∑ i, finiteTwoReplicaEdgeExtension u v S (A i) := by
  ext x y
  simp only [finiteTwoReplicaEdgeExtension, Matrix.sum_apply]
  rw [Finset.sum_mul]

/-- The global physical swap word is the corresponding edge swap word
tensored with its unchanged outside swap factors. -/
theorem finiteTwoReplicaSwapRaw_eq_edgeExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) (x : V → Bool) :
    finiteTwoReplicaSwapRaw x =
      finiteTwoReplicaEdgeExtension u v
        (fun w => twoReplicaLocalSwapRaw (x w.1))
        (twoReplicaEdgeSwapRaw (x u, x v)) := by
  rw [finiteTwoReplicaSwapRaw,
    finiteTwoReplicaLocalMatrix_eq_edgeExtension huv]
  rfl

/-- Phase-free Pauli string supported on one ordered edge. -/
def finiteEdgePauliLabel
    {V : Type*} [DecidableEq V]
    (u v : V) (a b : Fin 3) : V → Option (Fin 3) :=
  fun w => if w = u then some a else if w = v then some b else none

/-- Sitewise local-left realization of an edge Pauli string. -/
theorem finiteTwoReplicaPauliLeft_edge_eq_localMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (_huv : u ≠ v) (a b : Fin 3) :
    finiteTwoReplicaPauliLeft (finiteEdgePauliLabel u v a b) =
      finiteTwoReplicaLocalMatrix fun w =>
        if w = u then twoReplicaPauliLeft a
        else if w = v then twoReplicaPauliLeft b else 1 := by
  ext x y
  rw [finiteTwoReplicaPauliLeft, finitePauliMatrix_eq_finiteLocalMatrix,
    Matrix.kroneckerMap_apply]
  rw [← finiteLocalMatrix_one (sigma := V)]
  change
    (∏ w, boolPauliOption (finiteEdgePauliLabel u v a b w)
        (x.1 w) (y.1 w)) *
      (∏ w, (1 : Matrix Bool Bool ℂ) (x.2 w) (y.2 w)) =
    ∏ w,
      (if w = u then twoReplicaPauliLeft a
        else if w = v then twoReplicaPauliLeft b else 1)
        (x.1 w, x.2 w) (y.1 w, y.2 w)
  calc
    (∏ w, boolPauliOption (finiteEdgePauliLabel u v a b w)
        (x.1 w) (y.1 w)) *
        (∏ w, (1 : Matrix Bool Bool ℂ) (x.2 w) (y.2 w)) =
      ∏ w, boolPauliOption (finiteEdgePauliLabel u v a b w)
          (x.1 w) (y.1 w) *
        (1 : Matrix Bool Bool ℂ) (x.2 w) (y.2 w) :=
      Finset.prod_mul_distrib.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro w _
      by_cases hwu : w = u
      · subst w
        simp only [finiteEdgePauliLabel, if_pos, boolPauliOption,
          twoReplicaPauliLeft]
        change finiteQubitPauli a (x.1 u) (y.1 u) *
            (1 : Matrix Bool Bool ℂ) (x.2 u) (y.2 u) =
          (finiteQubitPauli a ⊗ₖ (1 : Matrix Bool Bool ℂ))
            (x.1 u, x.2 u) (y.1 u, y.2 u)
        rw [Matrix.kronecker_apply]
      by_cases hwv : w = v
      · subst w
        simp only [finiteEdgePauliLabel, if_neg hwu, if_pos,
          boolPauliOption, twoReplicaPauliLeft]
        change finiteQubitPauli b (x.1 v) (y.1 v) *
            (1 : Matrix Bool Bool ℂ) (x.2 v) (y.2 v) =
          (finiteQubitPauli b ⊗ₖ (1 : Matrix Bool Bool ℂ))
            (x.1 v, x.2 v) (y.1 v, y.2 v)
        rw [Matrix.kronecker_apply]
      · simp only [finiteEdgePauliLabel, if_neg hwu, if_neg hwv,
          boolPauliOption]
        rw [← Matrix.kronecker_apply, Matrix.one_kronecker_one]

/-- Sitewise local-right realization of an edge Pauli string. -/
theorem finiteTwoReplicaPauliRight_edge_eq_localMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (_huv : u ≠ v) (a b : Fin 3) :
    finiteTwoReplicaPauliRight (finiteEdgePauliLabel u v a b) =
      finiteTwoReplicaLocalMatrix fun w =>
        if w = u then twoReplicaPauliRight a
        else if w = v then twoReplicaPauliRight b else 1 := by
  ext x y
  rw [finiteTwoReplicaPauliRight, finitePauliMatrix_eq_finiteLocalMatrix,
    Matrix.kroneckerMap_apply]
  rw [← finiteLocalMatrix_one (sigma := V)]
  change
    (∏ w, (1 : Matrix Bool Bool ℂ) (x.1 w) (y.1 w)) *
      (∏ w, boolPauliOption (finiteEdgePauliLabel u v a b w)
        (x.2 w) (y.2 w)) =
    ∏ w,
      (if w = u then twoReplicaPauliRight a
        else if w = v then twoReplicaPauliRight b else 1)
        (x.1 w, x.2 w) (y.1 w, y.2 w)
  calc
    (∏ w, (1 : Matrix Bool Bool ℂ) (x.1 w) (y.1 w)) *
        (∏ w, boolPauliOption (finiteEdgePauliLabel u v a b w)
          (x.2 w) (y.2 w)) =
      ∏ w, (1 : Matrix Bool Bool ℂ) (x.1 w) (y.1 w) *
        boolPauliOption (finiteEdgePauliLabel u v a b w)
          (x.2 w) (y.2 w) := Finset.prod_mul_distrib.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro w _
      by_cases hwu : w = u
      · subst w
        simp only [finiteEdgePauliLabel, if_pos, boolPauliOption,
          twoReplicaPauliRight]
        change (1 : Matrix Bool Bool ℂ) (x.1 u) (y.1 u) *
            finiteQubitPauli a (x.2 u) (y.2 u) =
          ((1 : Matrix Bool Bool ℂ) ⊗ₖ finiteQubitPauli a)
            (x.1 u, x.2 u) (y.1 u, y.2 u)
        rw [Matrix.kronecker_apply]
      by_cases hwv : w = v
      · subst w
        simp only [finiteEdgePauliLabel, if_neg hwu, if_pos,
          boolPauliOption, twoReplicaPauliRight]
        change (1 : Matrix Bool Bool ℂ) (x.1 v) (y.1 v) *
            finiteQubitPauli b (x.2 v) (y.2 v) =
          ((1 : Matrix Bool Bool ℂ) ⊗ₖ finiteQubitPauli b)
            (x.1 v, x.2 v) (y.1 v, y.2 v)
        rw [Matrix.kronecker_apply]
      · simp only [finiteEdgePauliLabel, if_neg hwu, if_neg hwv,
          boolPauliOption]
        rw [← Matrix.kronecker_apply, Matrix.one_kronecker_one]

/-- Literal global collective Pauli generator on an edge equals the local
two-site collective generator tensored with spectator identities. -/
theorem finiteTwoReplicaEdgeCollective_eq_extension
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) (a b : Fin 3) :
    finiteTwoReplicaPauliLeft (finiteEdgePauliLabel u v a b) +
        finiteTwoReplicaPauliRight (finiteEdgePauliLabel u v a b) =
      finiteTwoReplicaEdgeExtension u v (fun _ => 1)
        (twoReplicaEdgeCollective a b) := by
  rw [finiteTwoReplicaPauliLeft_edge_eq_localMatrix huv,
    finiteTwoReplicaPauliRight_edge_eq_localMatrix huv]
  have hleft :
      finiteTwoReplicaLocalMatrix (fun w =>
        if w = u then twoReplicaPauliLeft a
        else if w = v then twoReplicaPauliLeft b else 1) =
      finiteTwoReplicaEdgeExtension u v (fun _ => 1)
        (twoReplicaPauliLeft a ⊗ₖ twoReplicaPauliLeft b) := by
    rw [finiteTwoReplicaLocalMatrix_eq_edgeExtension huv]
    congr 1
    · funext w
      simp [w.property.1, w.property.2]
    · simp [huv.symm]
  have hright :
      finiteTwoReplicaLocalMatrix (fun w =>
        if w = u then twoReplicaPauliRight a
        else if w = v then twoReplicaPauliRight b else 1) =
      finiteTwoReplicaEdgeExtension u v (fun _ => 1)
        (twoReplicaPauliRight a ⊗ₖ twoReplicaPauliRight b) := by
    rw [finiteTwoReplicaLocalMatrix_eq_edgeExtension huv]
    congr 1
    · funext w
      simp [w.property.1, w.property.2]
    · simp [huv.symm]
  rw [hleft, hright]
  rw [← finiteTwoReplicaEdgeExtension_add]
  rfl

/-! ## Literal weight-two edge Casimir -/

/-- Every edge label has Pauli weight exactly two. -/
theorem finitePauliWeight_finiteEdgePauliLabel
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) (a b : Fin 3) :
    finitePauliWeight (finiteEdgePauliLabel u v a b) = 2 := by
  rw [finitePauliWeight]
  have hfilter :
      Finset.univ.filter
          (fun w => finiteEdgePauliLabel u v a b w ≠ none) = {u, v} := by
    ext w
    by_cases hwu : w = u
    · subst w
      simp [finiteEdgePauliLabel]
    by_cases hwv : w = v
    · subst w
      simp [finiteEdgePauliLabel, hwu]
    · simp [finiteEdgePauliLabel, hwu, hwv]
  rw [hfilter, Finset.card_pair huv]

/-- Sum of the nine literal collective-Pauli commutator squares supported on
one ordered edge of an arbitrary finite register. -/
def finiteTwoReplicaPhysicalEdgeCasimir
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) : FiniteTwoReplicaMatrix V →ₗ[ℂ] FiniteTwoReplicaMatrix V :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    (finiteTwoReplicaCollectiveCommutatorLinear
      (finiteEdgePauliLabel u v a b)).comp
      (finiteTwoReplicaCollectiveCommutatorLinear
        (finiteEdgePauliLabel u v a b))

/-- One literal global edge commutator acts only on the edge matrix and
leaves every spectator factor unchanged. -/
theorem finiteTwoReplicaCollectiveCommutator_edgeExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (S : FiniteTwoReplicaEdgeOutside u v →
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (a b : Fin 3) (A : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (finiteEdgePauliLabel u v a b)
        (finiteTwoReplicaEdgeExtension u v S A) =
      finiteTwoReplicaEdgeExtension u v S
        (twoReplicaMatrixCommutator (twoReplicaEdgeCollective a b) A) := by
  let P := finiteEdgePauliLabel u v a b
  let X := finiteTwoReplicaEdgeExtension u v S A
  let H := twoReplicaEdgeCollective a b
  have hgenerator :
      finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P =
        finiteTwoReplicaEdgeExtension u v (fun _ => 1) H := by
    exact finiteTwoReplicaEdgeCollective_eq_extension huv a b
  change ringCommutator (finiteTwoReplicaPauliLeft P) X +
      ringCommutator (finiteTwoReplicaPauliRight P) X =
    finiteTwoReplicaEdgeExtension u v S (twoReplicaMatrixCommutator H A)
  calc
    ringCommutator (finiteTwoReplicaPauliLeft P) X +
        ringCommutator (finiteTwoReplicaPauliRight P) X =
      ringCommutator
        (finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P) X := by
          simp only [ringCommutator, Matrix.add_mul, Matrix.mul_add]
          module
    _ = ringCommutator
        (finiteTwoReplicaEdgeExtension u v (fun _ => 1) H) X := by
          rw [hgenerator]
    _ = finiteTwoReplicaEdgeExtension u v S
        (twoReplicaMatrixCommutator H A) := by
      rw [ringCommutator, twoReplicaMatrixCommutator,
        finiteTwoReplicaEdgeExtension_mul huv,
        finiteTwoReplicaEdgeExtension_mul huv]
      have honeLeft :
          (fun w : FiniteTwoReplicaEdgeOutside u v =>
            (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) * S w) =
          S := by funext w; simp
      have honeRight :
          (fun w : FiniteTwoReplicaEdgeOutside u v =>
            S w * (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)) =
          S := by funext w; simp
      rw [honeLeft, honeRight]
      rw [← finiteTwoReplicaEdgeExtension_sub]
      rfl

/-- The full literal global edge Casimir is exactly the tensor extension of
the previously computed two-site physical Casimir. -/
theorem finiteTwoReplicaPhysicalEdgeCasimir_edgeExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (S : FiniteTwoReplicaEdgeOutside u v →
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (A : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    finiteTwoReplicaPhysicalEdgeCasimir u v
        (finiteTwoReplicaEdgeExtension u v S A) =
      finiteTwoReplicaEdgeExtension u v S (twoReplicaEdgeCasimir A) := by
  change (∑ a : Fin 3, ∑ b : Fin 3,
      finiteTwoReplicaCollectiveCommutatorLinear
        (finiteEdgePauliLabel u v a b)
        (finiteTwoReplicaCollectiveCommutatorLinear
          (finiteEdgePauliLabel u v a b)
          (finiteTwoReplicaEdgeExtension u v S A))) = _
  simp_rw [finiteTwoReplicaCollectiveCommutator_edgeExtension huv]
  rw [twoReplicaEdgeCasimir_apply,
    finiteTwoReplicaEdgeExtension_sum]
  simp_rw [finiteTwoReplicaEdgeExtension_sum]

/-- On every global swap word, the literal physical edge Casimir is the
two-site physical Casimir on its endpoint word with all spectators retained. -/
theorem finiteTwoReplicaPhysicalEdgeCasimir_swapRaw
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) (x : V → Bool) :
    finiteTwoReplicaPhysicalEdgeCasimir u v
        (finiteTwoReplicaSwapRaw x) =
      finiteTwoReplicaEdgeExtension u v
        (fun w => twoReplicaLocalSwapRaw (x w.1))
        (twoReplicaEdgeCasimir (twoReplicaEdgeSwapRaw (x u, x v))) := by
  rw [finiteTwoReplicaSwapRaw_eq_edgeExtension huv,
    finiteTwoReplicaPhysicalEdgeCasimir_edgeExtension huv]

/-! ## Exact physical/coefficient intertwinement -/

/-- Reindex Boolean swap words by outside labels first and the two endpoint
labels second. -/
def finiteBoolEdgeConfigurationEquiv
    {V : Type*} [DecidableEq V] (u v : V) (huv : u ≠ v) :
    (V → Bool) ≃
      ((FiniteTwoReplicaEdgeOutside u v → Bool) × TwoReplicaEdgeLabel) where
  toFun x := (fun w => x w.1, (x u, x v))
  invFun x w :=
    if hwu : w = u then x.2.1
    else if hwv : w = v then x.2.2
    else x.1 ⟨w, hwu, hwv⟩
  left_inv x := by
    funext w
    by_cases hwu : w = u
    · subst w
      simp
    by_cases hwv : w = v
    · subst w
      simp [hwu]
    simp [hwu, hwv]
  right_inv x := by
    rcases x with ⟨outside, p⟩
    apply Prod.ext
    · funext w
      simp [w.property.1, w.property.2]
    · apply Prod.ext
      · simp
      · simp [huv.symm]

/-- Assemble one outside swap assignment and one edge endpoint label. -/
def finiteBoolEdgeAssemble
    {V : Type*} [DecidableEq V]
    (u v : V) (huv : u ≠ v)
    (outside : FiniteTwoReplicaEdgeOutside u v → Bool)
    (p : TwoReplicaEdgeLabel) : V → Bool :=
  (finiteBoolEdgeConfigurationEquiv u v huv).symm (outside, p)

@[simp] theorem finiteBoolEdgeAssemble_left
    {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (outside : FiniteTwoReplicaEdgeOutside u v → Bool)
    (p : TwoReplicaEdgeLabel) :
    finiteBoolEdgeAssemble u v huv outside p u = p.1 := by
  simp [finiteBoolEdgeAssemble, finiteBoolEdgeConfigurationEquiv]

@[simp] theorem finiteBoolEdgeAssemble_right
    {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (outside : FiniteTwoReplicaEdgeOutside u v → Bool)
    (p : TwoReplicaEdgeLabel) :
    finiteBoolEdgeAssemble u v huv outside p v = p.2 := by
  simp [finiteBoolEdgeAssemble, finiteBoolEdgeConfigurationEquiv, huv.symm]

@[simp] theorem finiteBoolEdgeAssemble_outside
    {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (outside : FiniteTwoReplicaEdgeOutside u v → Bool)
    (p : TwoReplicaEdgeLabel)
    (w : FiniteTwoReplicaEdgeOutside u v) :
    finiteBoolEdgeAssemble u v huv outside p w.1 = outside w := by
  simp [finiteBoolEdgeAssemble, finiteBoolEdgeConfigurationEquiv,
    w.property.1, w.property.2]

theorem twoReplicaSetEdgeLabel_assemble
    {V : Type*} [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (outside : FiniteTwoReplicaEdgeOutside u v → Bool)
    (p q : TwoReplicaEdgeLabel) :
    twoReplicaSetEdgeLabel u v
        (finiteBoolEdgeAssemble u v huv outside p) q =
      finiteBoolEdgeAssemble u v huv outside q := by
  funext w
  by_cases hwu : w = u
  · subst w
    simp [huv]
  by_cases hwv : w = v
  · subst w
    simp
  · have hset :
        twoReplicaSetEdgeLabel u v
            (finiteBoolEdgeAssemble u v huv outside p) q w =
          finiteBoolEdgeAssemble u v huv outside p w := by
      simp [twoReplicaSetEdgeLabel, hwu, hwv]
    rw [hset]
    have hp := finiteBoolEdgeAssemble_outside huv outside p
      (⟨w, hwu, hwv⟩ : FiniteTwoReplicaEdgeOutside u v)
    have hq := finiteBoolEdgeAssemble_outside huv outside q
      (⟨w, hwu, hwv⟩ : FiniteTwoReplicaEdgeOutside u v)
    exact hp.trans hq.symm

/-- Four coefficient coordinates in one fixed outside-label block. -/
def twoReplicaGlobalEdgeBlock
    {V : Type*} [DecidableEq V]
    (u v : V) (huv : u ≠ v)
    (c : TwoReplicaGlobalCoeff V)
    (outside : FiniteTwoReplicaEdgeOutside u v → Bool) :
    TwoReplicaEdgeCoeff :=
  fun p => c (finiteBoolEdgeAssemble u v huv outside p)

/-- The global coefficient Casimir is exactly block diagonal in outside swap
labels, with each block equal to the physical four-coordinate edge Casimir. -/
theorem twoReplicaGlobalEdgeBlock_casimir
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (c : TwoReplicaGlobalCoeff V)
    (outside : FiniteTwoReplicaEdgeOutside u v → Bool) :
    twoReplicaGlobalEdgeBlock u v huv
        (twoReplicaGlobalEdgeCasimirCoeff u v c) outside =
      twoReplicaEdgeSwapCasimirCoeff
        (twoReplicaGlobalEdgeBlock u v huv c outside) := by
  funext p
  simp only [twoReplicaGlobalEdgeBlock,
    twoReplicaGlobalEdgeCasimirCoeff, LinearMap.coe_mk, AddHom.coe_mk,
    finiteBoolEdgeAssemble_left, finiteBoolEdgeAssemble_right]
  have hslice :
      twoReplicaGlobalEdgeSlice u v c
          (finiteBoolEdgeAssemble u v huv outside p) =
        twoReplicaGlobalEdgeBlock u v huv c outside := by
    funext q
    change c (twoReplicaSetEdgeLabel u v
        (finiteBoolEdgeAssemble u v huv outside p) q) =
      c (finiteBoolEdgeAssemble u v huv outside q)
    rw [twoReplicaSetEdgeLabel_assemble huv]
  rw [hslice]

/-- Tensor extension of one edge swap word equals the assembled global swap
word with those endpoint and outside labels. -/
theorem finiteTwoReplicaEdgeExtension_swapRaw
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (outside : FiniteTwoReplicaEdgeOutside u v → Bool)
    (p : TwoReplicaEdgeLabel) :
    finiteTwoReplicaEdgeExtension u v
        (fun w => twoReplicaLocalSwapRaw (outside w))
        (twoReplicaEdgeSwapRaw p) =
      finiteTwoReplicaSwapRaw
        (finiteBoolEdgeAssemble u v huv outside p) := by
  rw [finiteTwoReplicaSwapRaw_eq_edgeExtension huv]
  congr 1
  · funext w
    rw [finiteBoolEdgeAssemble_outside huv]
  · rw [finiteBoolEdgeAssemble_left huv,
      finiteBoolEdgeAssemble_right huv]

/-- Tensor extension of an arbitrary four-coordinate edge invariant is the
corresponding physical sum of assembled global swap words. -/
theorem finiteTwoReplicaEdgeExtension_swapInvariantEmbed
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (outside : FiniteTwoReplicaEdgeOutside u v → Bool)
    (d : TwoReplicaEdgeCoeff) :
    finiteTwoReplicaEdgeExtension u v
        (fun w => twoReplicaLocalSwapRaw (outside w))
        (twoReplicaEdgeSwapInvariantEmbed d) =
      ∑ p : TwoReplicaEdgeLabel,
        d p • finiteTwoReplicaSwapRaw
          (finiteBoolEdgeAssemble u v huv outside p) := by
  change finiteTwoReplicaEdgeExtension u v
      (fun w => twoReplicaLocalSwapRaw (outside w))
      (∑ p : TwoReplicaEdgeLabel, d p • twoReplicaEdgeSwapRaw p) = _
  rw [finiteTwoReplicaEdgeExtension_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [finiteTwoReplicaEdgeExtension_smul,
    finiteTwoReplicaEdgeExtension_swapRaw huv]

/-- Exact decomposition of the global physical invariant embedding into
independent outside-label edge blocks. -/
theorem finiteTwoReplicaSwapInvariantEmbed_edgeBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v)
    (c : TwoReplicaGlobalCoeff V) :
    finiteTwoReplicaSwapInvariantEmbed c =
      ∑ outside : FiniteTwoReplicaEdgeOutside u v → Bool,
        finiteTwoReplicaEdgeExtension u v
          (fun w => twoReplicaLocalSwapRaw (outside w))
          (twoReplicaEdgeSwapInvariantEmbed
            (twoReplicaGlobalEdgeBlock u v huv c outside)) := by
  change (∑ x : V → Bool, c x • finiteTwoReplicaSwapRaw x) = _
  simp_rw [finiteTwoReplicaEdgeExtension_swapInvariantEmbed huv]
  calc
    (∑ x : V → Bool, c x • finiteTwoReplicaSwapRaw x) =
        ∑ z : (FiniteTwoReplicaEdgeOutside u v → Bool) ×
            TwoReplicaEdgeLabel,
          c (finiteBoolEdgeAssemble u v huv z.1 z.2) •
            finiteTwoReplicaSwapRaw
              (finiteBoolEdgeAssemble u v huv z.1 z.2) := by
      exact Fintype.sum_equiv (finiteBoolEdgeConfigurationEquiv u v huv)
        _ _ (fun x => by
          have hx : finiteBoolEdgeAssemble u v huv
              ((finiteBoolEdgeConfigurationEquiv u v huv x).1)
              ((finiteBoolEdgeConfigurationEquiv u v huv x).2) = x :=
            (finiteBoolEdgeConfigurationEquiv u v huv).symm_apply_apply x
          rw [hx])
    _ = ∑ outside : FiniteTwoReplicaEdgeOutside u v → Bool,
        ∑ p : TwoReplicaEdgeLabel,
          twoReplicaGlobalEdgeBlock u v huv c outside p •
            finiteTwoReplicaSwapRaw
              (finiteBoolEdgeAssemble u v huv outside p) := by
      rw [Fintype.sum_prod_type]
      rfl

/-- **Physical/coefficient bridge.** The nine literal weight-two global
collective-Pauli commutator squares intertwine exactly with the global
identity/swap coefficient Casimir. -/
theorem finiteTwoReplicaPhysicalEdgeCasimir_intertwines_swapCoeff
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) (c : TwoReplicaGlobalCoeff V) :
    finiteTwoReplicaPhysicalEdgeCasimir u v
        (finiteTwoReplicaSwapInvariantEmbed c) =
      finiteTwoReplicaSwapInvariantEmbed
        (twoReplicaGlobalEdgeCasimirCoeff u v c) := by
  rw [finiteTwoReplicaSwapInvariantEmbed_edgeBlocks huv]
  rw [map_sum]
  simp_rw [finiteTwoReplicaPhysicalEdgeCasimir_edgeExtension huv]
  simp_rw [twoReplicaEdgeCasimir_intertwines_swapCoeff]
  rw [finiteTwoReplicaSwapInvariantEmbed_edgeBlocks huv]
  apply Finset.sum_congr rfl
  intro outside _
  rw [twoReplicaGlobalEdgeBlock_casimir huv]

/-- Vanishing of a literal physical edge Casimir on the embedded invariant
sector is equivalent to the exact edge mismatch constraint on coefficients. -/
theorem finiteTwoReplicaPhysicalEdgeCasimir_embed_eq_zero_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {u v : V} (huv : u ≠ v) (c : TwoReplicaGlobalCoeff V) :
    finiteTwoReplicaPhysicalEdgeCasimir u v
        (finiteTwoReplicaSwapInvariantEmbed c) = 0 ↔
      ∀ x : V → Bool, x u ≠ x v → c x = 0 := by
  rw [finiteTwoReplicaPhysicalEdgeCasimir_intertwines_swapCoeff huv]
  have hinj := finiteTwoReplicaSwapInvariantEmbed_injective (V := V)
  have hembedZero :
      finiteTwoReplicaSwapInvariantEmbed (V := V)
          (twoReplicaGlobalEdgeCasimirCoeff u v c) = 0 ↔
        twoReplicaGlobalEdgeCasimirCoeff u v c = 0 := by
    constructor
    · intro h
      apply hinj
      simpa using h
    · intro h
      rw [h]
      exact LinearMap.map_zero _
  rw [hembedZero, twoReplicaGlobalEdgeCasimirCoeff_eq_zero_iff huv c]

/-- **Connected-graph physical kernel law.** For every finite nonempty
preconnected interaction graph, the common kernel of all literal nine-term
weight-two edge Casimirs inside the full sitewise identity/swap invariant
sector consists exactly of global identity and global replica swap. -/
theorem finiteTwoReplicaPhysical_connectedGraph_kernel_iff
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Preconnected)
    (c : TwoReplicaGlobalCoeff V) :
    (∀ ⦃u v⦄, G.Adj u v →
      finiteTwoReplicaPhysicalEdgeCasimir u v
        (finiteTwoReplicaSwapInvariantEmbed c) = 0) ↔
      ∃ a b : ℂ, c = twoReplicaGlobalSynchronizedCoeff a b := by
  rw [← twoReplicaGlobal_edgeMismatch_zero_iff hG c]
  constructor
  · intro h u v huv
    exact (finiteTwoReplicaPhysicalEdgeCasimir_embed_eq_zero_iff
      huv.ne c).mp (h huv)
  · intro h u v huv
    exact (finiteTwoReplicaPhysicalEdgeCasimir_embed_eq_zero_iff
      huv.ne c).mpr (h huv)

end

end GaloisForLFunctions.HTGeometry
