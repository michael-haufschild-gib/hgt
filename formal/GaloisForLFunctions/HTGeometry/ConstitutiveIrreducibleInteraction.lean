import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.MinimalLawLeadingJet
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Irreducible `n`-ary law, proper-face invisibility, and unbounded interaction spectrum

Fix `N ≥ 3` and let the carrier be `(Fin N → ℝ) × ℝ`: the first factor is spanned by the `N`
colors, the second is the interaction output line `ℝ z`.  The only nonzero operation is the
`N`-ary bracket

`ℓ_N (v₁, …, v_N) = det (colour coordinates of v₁, …, v_N) • z`,

the alternating extension of `ℓ_N (x₁, …, x_N) = z`, which vanishes automatically as soon as one
input has no colour component — in particular on every bracket output.

Certified here:

* `bracket_composite_eq_zero` and `linfty_identity` — every composite of brackets vanishes, so
  every generalized Jacobi identity holds for *any* sign convention: the operations really define a
  minimal law;
* `bracketFamily_comp_face_eq_zero` and `faceLaw_isAbelian` — every proper colour face is abelian,
  while `irreducibleLaw_not_isAbelian` shows the total law is not, and
  `not_isAbelian_of_equiv` propagates this along any formal-law equivalence: the total law is not
  homotopy abelian;
* `irreducibleLaw_firstNonzero` and `interactionOrder_eq` — the interaction order is exactly `N`,
  and `arityTruncation_isAbelian` shows every observer truncating below arity `N` reports an
  abelian law;
* `towerBracket_composite_eq_zero`, `towerBracket_apply_eq_zero_of_le`, `zTail_injective`,
  `zTail_range_disjoint_towerHead` — the product tower of all blocks squares to zero, an arity-`M`
  observer kills every block of order above `M`, and the resulting invisible tail is an infinite
  independent family;
* `not_locallyCompactSpace_pi_real` — the full interaction-output space with its product topology
  is not locally compact.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset HTGeometry.NomologicalHomotopyGeometry.MinimalLawLeadingJet

/-- Carrier of the irreducible `N`-ary law: `N` colours and one interaction-output line. -/
abbrev InteractionCarrier (N : ℕ) := (Fin N → ℝ) × ℝ

/-- The interaction output `z`. -/
def interactionOutput (N : ℕ) : InteractionCarrier N := (0, 1)

/-- The colour generator `x i`. -/
def colorGen {N : ℕ} (i : Fin N) : InteractionCarrier N := (Pi.single i 1, 0)

theorem interactionOutput_ne_zero (N : ℕ) : interactionOutput N ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg Prod.snd h)

/-- The irreducible `N`-ary bracket: the alternating extension of `ℓ_N (x₁, …, x_N) = z`. -/
noncomputable def interactionBracket (N : ℕ) :
    (InteractionCarrier N) [⋀^Fin N]→ₗ[ℝ] InteractionCarrier N :=
  (LinearMap.toSpanSingleton ℝ (InteractionCarrier N) (interactionOutput N)).compAlternatingMap
    (Matrix.detRowAlternating.compLinearMap (LinearMap.fst ℝ (Fin N → ℝ) ℝ))

theorem interactionBracket_apply (N : ℕ) (v : Fin N → InteractionCarrier N) :
    interactionBracket N v
      = (Matrix.det (Matrix.of fun i j => (v i).1 j)) • interactionOutput N := rfl

/-- The bracket takes the colour generators to the interaction output. -/
theorem interactionBracket_colorGen (N : ℕ) :
    interactionBracket N (fun i => colorGen i) = interactionOutput N := by
  rw [interactionBracket_apply]
  have hmat : (Matrix.of fun i j => ((colorGen i : InteractionCarrier N)).1 j)
      = (1 : Matrix (Fin N) (Fin N) ℝ) := by
    ext i j
    simp [colorGen, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hmat, Matrix.det_one, one_smul]

theorem interactionBracket_ne_zero (N : ℕ) : interactionBracket N ≠ 0 := by
  intro h
  refine interactionOutput_ne_zero N ?_
  rw [← interactionBracket_colorGen N, h]
  rfl

/-- Every bracket output has vanishing colour component. -/
theorem interactionBracket_fst (N : ℕ) (v : Fin N → InteractionCarrier N) :
    (interactionBracket N v).1 = 0 := by
  rw [interactionBracket_apply]
  simp [interactionOutput]

/-- The bracket vanishes as soon as one input has no colour component. -/
theorem interactionBracket_eq_zero_of_fst_eq_zero (N : ℕ) (v : Fin N → InteractionCarrier N)
    (i : Fin N) (hi : (v i).1 = 0) : interactionBracket N v = 0 := by
  rw [interactionBracket_apply]
  have hrow : ∀ j, (Matrix.of fun i j => (v i).1 j) i j = 0 := by
    intro j
    simpa using congrFun hi j
  rw [Matrix.det_eq_zero_of_row_eq_zero i hrow, zero_smul]

/-- The operations of the law, one for every arity: the `N`-ary bracket in arity `N`, zero
elsewhere. -/
noncomputable def bracketFamily (N r : ℕ) :
    (InteractionCarrier N) [⋀^Fin r]→ₗ[ℝ] InteractionCarrier N :=
  if h : r = N then (interactionBracket N).domDomCongr (finCongr h.symm) else 0

theorem bracketFamily_of_ne {N r : ℕ} (h : r ≠ N) : bracketFamily N r = 0 := dif_neg h

theorem bracketFamily_self (N : ℕ) : bracketFamily N N = interactionBracket N := by
  rw [bracketFamily, dif_pos rfl, finCongr_refl, AlternatingMap.domDomCongr_refl]

theorem bracketFamily_apply_fst (N r : ℕ) (v : Fin r → InteractionCarrier N) :
    (bracketFamily N r v).1 = 0 := by
  by_cases h : r = N
  · subst h
    rw [bracketFamily_self]
    exact interactionBracket_fst _ v
  · rw [bracketFamily_of_ne h]
    simp

theorem bracketFamily_eq_zero_of_fst_eq_zero (N r : ℕ) (v : Fin r → InteractionCarrier N)
    (i : Fin r) (hi : (v i).1 = 0) : bracketFamily N r v = 0 := by
  by_cases h : r = N
  · subst h
    rw [bracketFamily_self]
    exact interactionBracket_eq_zero_of_fst_eq_zero _ v i hi
  · rw [bracketFamily_of_ne h]
    simp

/-- **Every composite of brackets vanishes.**  Feeding the output of any operation into any slot of
any operation gives zero, because the output carries no colour. -/
theorem bracket_composite_eq_zero (N r s : ℕ) (v : Fin r → InteractionCarrier N)
    (w : Fin s → InteractionCarrier N) (i : Fin s) :
    bracketFamily N s (Function.update w i (bracketFamily N r v)) = 0 := by
  refine bracketFamily_eq_zero_of_fst_eq_zero N s _ i ?_
  rw [Function.update_self]
  exact bracketFamily_apply_fst N r v

/-- **Minimality: every generalized Jacobi identity holds, for any sign convention.**  Each
composite term of an `L∞` identity vanishes separately, so any signed sum of composites is zero
whatever the Koszul signs are. -/
theorem linfty_identity (N : ℕ) {T : Type*} [Fintype T] (sign : T → ℝ) (r s : T → ℕ)
    (slot : ∀ t, Fin (s t)) (inner : ∀ t, Fin (r t) → InteractionCarrier N)
    (outer : ∀ t, Fin (s t) → InteractionCarrier N) :
    ∑ t, sign t •
        bracketFamily N (s t)
          (Function.update (outer t) (slot t) (bracketFamily N (r t) (inner t))) = 0 := by
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [bracket_composite_eq_zero, smul_zero]

/-- The colour face spanned by the output line and the colours in `S`. -/
def colorFace (N : ℕ) (S : Finset (Fin N)) : Submodule ℝ (InteractionCarrier N) where
  carrier := {v | ∀ j ∉ S, v.1 j = 0}
  add_mem' hv hw := by intro j hj; simp [hv j hj, hw j hj]
  zero_mem' := by intro j _; rfl
  smul_mem' c v hv := by intro j hj; simp [hv j hj]

theorem mem_colorFace {N : ℕ} {S : Finset (Fin N)} {v : InteractionCarrier N} :
    v ∈ colorFace N S ↔ ∀ j ∉ S, v.1 j = 0 := Iff.rfl

/-- The interaction output lies in every colour face. -/
theorem interactionOutput_mem_colorFace (N : ℕ) (S : Finset (Fin N)) :
    interactionOutput N ∈ colorFace N S := by
  intro j _
  rfl

/-- **Every proper colour face is abelian.**  Restricting any operation to a proper face gives the
zero operation: a missing colour is an identically zero column of the defining determinant. -/
theorem bracketFamily_comp_face_eq_zero (N : ℕ) (S : Finset (Fin N)) (hS : S ≠ Finset.univ)
    (r : ℕ) : (bracketFamily N r).compLinearMap (colorFace N S).subtype = 0 := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin N, j₀ ∉ S := by
    by_contra hcon
    exact hS (Finset.eq_univ_iff_forall.mpr (fun x => not_not.mp (fun hx => hcon ⟨x, hx⟩)))
  refine AlternatingMap.ext fun v => ?_
  by_cases h : r = N
  · subst h
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.zero_apply,
      Submodule.coe_subtype, bracketFamily_self, interactionBracket_apply]
    have hcol : ∀ i, (Matrix.of fun i j => (((v i : InteractionCarrier _)).1 j)) i j₀ = 0 := by
      intro i
      simpa using (v i).2 j₀ hj₀
    rw [Matrix.det_eq_zero_of_column_eq_zero j₀ hcol, zero_smul]
  · rw [bracketFamily_of_ne h]
    simp

/-- The law induced on a colour face, obtained by restricting every operation. -/
noncomputable def faceBracketFamily (N : ℕ) (S : Finset (Fin N)) (r : ℕ) :
    (colorFace N S) [⋀^Fin r]→ₗ[ℝ] (colorFace N S) :=
  ((bracketFamily N r).compLinearMap (colorFace N S).subtype).codRestrict (colorFace N S)
    (fun v => by
      have h : ∀ j ∉ S, (bracketFamily N r fun i => ((v i : InteractionCarrier N))).1 j = 0 := by
        intro j _
        simp [bracketFamily_apply_fst]
      exact h)

theorem faceBracketFamily_eq_zero (N : ℕ) (S : Finset (Fin N)) (hS : S ≠ Finset.univ) (r : ℕ) :
    faceBracketFamily N S r = 0 := by
  refine AlternatingMap.ext fun v => ?_
  have h : ((bracketFamily N r).compLinearMap (colorFace N S).subtype) v = 0 := by
    rw [bracketFamily_comp_face_eq_zero N S hS r]
    rfl
  apply Subtype.ext
  simpa [faceBracketFamily] using h

section FormalLaw

variable {N : ℕ}

/-- The irreducible `N`-ary law as a minimal formal law: the `N`-ary bracket in arity `N`, zero in
every other arity. -/
noncomputable def irreducibleLaw (N : ℕ) (hN : 2 ≤ N) :
    MinimalLaw (fun r => ↥(⋀[ℝ]^r (InteractionCarrier N))) (InteractionCarrier N) where
  operation r := exteriorPower.alternatingMapLinearEquiv (bracketFamily N r)
  unary_zero := by
    rw [bracketFamily_of_ne (by omega : (1 : ℕ) ≠ N)]
    exact map_zero _

theorem irreducibleLaw_operation (hN : 2 ≤ N) (r : ℕ) :
    (irreducibleLaw N hN).operation r
      = exteriorPower.alternatingMapLinearEquiv (bracketFamily N r) := rfl

theorem irreducibleLaw_operation_eq_zero (hN : 2 ≤ N) {r : ℕ} (h : r ≠ N) :
    (irreducibleLaw N hN).operation r = 0 := by
  rw [irreducibleLaw_operation, bracketFamily_of_ne h]
  exact map_zero _

/-- The law is uncurved and minimal: the nullary and unary operations vanish. -/
theorem bracketFamily_zero_and_one (hN : 2 ≤ N) :
    bracketFamily N 0 = 0 ∧ bracketFamily N 1 = 0 :=
  ⟨bracketFamily_of_ne (by omega), bracketFamily_of_ne (by omega)⟩

theorem irreducibleLaw_operation_ne_zero (hN : 2 ≤ N) :
    (irreducibleLaw N hN).operation N ≠ 0 := by
  rw [irreducibleLaw_operation, bracketFamily_self]
  intro h
  refine interactionBracket_ne_zero N ?_
  have := congrArg (exteriorPower.alternatingMapLinearEquiv (R := ℝ)
    (M := InteractionCarrier N) (N := InteractionCarrier N) (n := N)).symm h
  simpa using this

/-- **The interaction order is exactly `N`.**  The first nonvanishing operation of the irreducible
`N`-ary law has arity `N`. -/
theorem irreducibleLaw_firstNonzero (hN : 2 ≤ N) : (irreducibleLaw N hN).FirstNonzero N :=
  ⟨hN, irreducibleLaw_operation_ne_zero hN, fun _ _ hr =>
    irreducibleLaw_operation_eq_zero hN (Nat.ne_of_lt hr)⟩

/-- **The total law is not abelian.** -/
theorem irreducibleLaw_not_isAbelian (hN : 2 ≤ N) : ¬ (irreducibleLaw N hN).IsAbelian := by
  intro habs
  exact irreducibleLaw_operation_ne_zero hN (habs N hN)

/-- **The total law is not homotopy abelian.**  No formal-law equivalence takes it to an abelian
law. -/
theorem not_isAbelian_of_equiv (hN : 2 ≤ N) {B : ℕ → Type*} {H' : Type*}
    [∀ n, AddCommGroup (B n)] [∀ n, Module ℝ (B n)] [AddCommGroup H'] [Module ℝ H']
    {Q' : MinimalLaw B H'}
    (F : MinimalLawEquiv (fun r => ↥(⋀[ℝ]^r (InteractionCarrier N))) B (InteractionCarrier N) H'
      (irreducibleLaw N hN) Q') : ¬ Q'.IsAbelian :=
  F.not_target_abelian_of_source_firstNonzero (irreducibleLaw_firstNonzero hN)

/-- **The interaction order is an invariant.**  Any law equivalent to the irreducible `N`-ary law
has first nonvanishing arity `N`. -/
theorem interactionOrder_eq (hN : 2 ≤ N) {B : ℕ → Type*} {H' : Type*}
    [∀ n, AddCommGroup (B n)] [∀ n, Module ℝ (B n)] [AddCommGroup H'] [Module ℝ H']
    {Q' : MinimalLaw B H'} {s : ℕ}
    (F : MinimalLawEquiv (fun r => ↥(⋀[ℝ]^r (InteractionCarrier N))) B (InteractionCarrier N) H'
      (irreducibleLaw N hN) Q') (hs : Q'.FirstNonzero s) : s = N :=
  (F.firstNonzero_order_eq (irreducibleLaw_firstNonzero hN) hs).symm

/-- The law seen by an observer that truncates every operation of arity above `M`. -/
def arityTruncation {A : ℕ → Type*} {H : Type*}
    [∀ n, AddCommGroup (A n)] [∀ n, Module ℝ (A n)] [AddCommGroup H] [Module ℝ H]
    (M : ℕ) (Q : MinimalLaw A H) : MinimalLaw A H where
  operation r := if r ≤ M then Q.operation r else 0
  unary_zero := by
    by_cases h : 1 ≤ M
    · rw [if_pos h, Q.unary_zero]
    · rw [if_neg h]

/-- **Truncating below the interaction order reports an abelian law.** -/
theorem arityTruncation_isAbelian (hN : 2 ≤ N) {M : ℕ} (hM : M < N) :
    (arityTruncation M (irreducibleLaw N hN)).IsAbelian := by
  intro r _
  show (if r ≤ M then (irreducibleLaw N hN).operation r else 0) = 0
  by_cases h : r ≤ M
  · rw [if_pos h]
    exact irreducibleLaw_operation_eq_zero hN (by omega)
  · rw [if_neg h]

end FormalLaw

section Tower

/-- The unbounded interaction tower: one irreducible block of every order `m + 3 ≥ 3`. -/
abbrev TowerCarrier := ∀ m : ℕ, InteractionCarrier (m + 3)

/-- The product law: the block of order `m + 3` contributes exactly in arity `m + 3`. -/
noncomputable def towerBracket (r : ℕ) : TowerCarrier [⋀^Fin r]→ₗ[ℝ] TowerCarrier :=
  AlternatingMap.pi fun m => (bracketFamily (m + 3) r).compLinearMap (LinearMap.proj m)

theorem towerBracket_apply (r : ℕ) (v : Fin r → TowerCarrier) (m : ℕ) :
    towerBracket r v m = bracketFamily (m + 3) r (fun i => v i m) := rfl

theorem towerBracket_apply_fst (r : ℕ) (v : Fin r → TowerCarrier) (m : ℕ) :
    (towerBracket r v m).1 = 0 := by
  rw [towerBracket_apply]
  exact bracketFamily_apply_fst _ _ _

/-- **The product law squares to zero.**  Every composite of tower operations vanishes. -/
theorem towerBracket_composite_eq_zero (r s : ℕ) (v : Fin r → TowerCarrier)
    (w : Fin s → TowerCarrier) (i : Fin s) :
    towerBracket s (Function.update w i (towerBracket r v)) = 0 := by
  funext m
  rw [towerBracket_apply]
  refine bracketFamily_eq_zero_of_fst_eq_zero _ _ _ i ?_
  rw [Function.update_self]
  exact towerBracket_apply_fst r v m

/-- **An arity-`M` observer kills every block of order above `M`.** -/
theorem towerBracket_apply_eq_zero_of_le {r M m : ℕ} (hr : r ≤ M) (hm : M < m + 3)
    (v : Fin r → TowerCarrier) : towerBracket r v m = 0 := by
  rw [towerBracket_apply, bracketFamily_of_ne (by omega : r ≠ m + 3)]
  rfl

/-- The head visible to an arity-`M` observer: the blocks of order at most `M`. -/
def towerHead (M : ℕ) : Submodule ℝ TowerCarrier where
  carrier := {v | ∀ m, M < m + 3 → v m = 0}
  add_mem' hv hw := by intro m hm; simp [hv m hm, hw m hm]
  zero_mem' := by intro m _; rfl
  smul_mem' c v hv := by intro m hm; simp [hv m hm]

theorem mem_towerHead {M : ℕ} {v : TowerCarrier} :
    v ∈ towerHead M ↔ ∀ m, M < m + 3 → v m = 0 := Iff.rfl

/-- **Every arity-`M` operation lands in the visible head.** -/
theorem towerBracket_mem_towerHead {r M : ℕ} (hr : r ≤ M) (v : Fin r → TowerCarrier) :
    towerBracket r v ∈ towerHead M := by
  intro m hm
  exact towerBracket_apply_eq_zero_of_le hr hm v

/-- The invisible tail of an arity-`M` observer: the product of the interaction-output lines of all
blocks of order above `M`. -/
def zTail (M : ℕ) : ({m : ℕ // M < m + 3} → ℝ) →ₗ[ℝ] TowerCarrier where
  toFun c := fun m => if h : M < m + 3 then (0, c ⟨m, h⟩) else 0
  map_add' c d := by
    funext m
    by_cases h : M < m + 3 <;> simp [h]
  map_smul' a c := by
    funext m
    by_cases h : M < m + 3 <;> simp [h]

theorem zTail_apply (M : ℕ) (c : {m : ℕ // M < m + 3} → ℝ) (m : ℕ) :
    zTail M c m = if h : M < m + 3 then (0, c ⟨m, h⟩) else 0 := rfl

theorem zTail_injective (M : ℕ) : Function.Injective (zTail M) := by
  intro c d hcd
  funext m
  have h := congrFun hcd m.1
  rw [zTail_apply, zTail_apply, dif_pos m.2, dif_pos m.2] at h
  have := congrArg Prod.snd h
  simpa using this

/-- **The invisible tail meets the visible head only at zero.** -/
theorem zTail_range_disjoint_towerHead (M : ℕ) :
    LinearMap.range (zTail M) ⊓ towerHead M = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro v ⟨⟨c, rfl⟩, hhead⟩
  refine (Submodule.mem_bot ℝ).mpr ?_
  have hc : c = 0 := by
    funext m
    have h := hhead m.1 m.2
    rw [zTail_apply, dif_pos m.2] at h
    have := congrArg Prod.snd h
    simpa using this
  rw [hc, map_zero]

/-- **The tail is annihilated by every arity-`M` operation.** -/
theorem towerBracket_eq_zero_of_mem_zTail {r M : ℕ} (hr : r ≤ M) (v : Fin r → TowerCarrier)
    (hv : ∀ i, v i ∈ LinearMap.range (zTail M)) : towerBracket r v = 0 := by
  funext m
  by_cases hm : M < m + 3
  · exact towerBracket_apply_eq_zero_of_le hr hm v
  · rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      rw [towerBracket_apply, bracketFamily_of_ne (by omega : (0 : ℕ) ≠ m + 3)]
      rfl
    · have hi : (⟨0, hr0⟩ : Fin r) = ⟨0, hr0⟩ := rfl
      rw [towerBracket_apply]
      refine bracketFamily_eq_zero_of_fst_eq_zero _ _ _ ⟨0, hr0⟩ ?_
      obtain ⟨c, hc⟩ := hv ⟨0, hr0⟩
      rw [← hc, zTail_apply, dif_neg hm]
      rfl

/-- The invisible tail of any arity-`M` observer is infinite. -/
instance instInfiniteTailIndex (M : ℕ) : Infinite {m : ℕ // M < m + 3} :=
  Set.infinite_coe_iff.mpr (Set.infinite_of_not_bddAbove (by
    rintro ⟨B, hB⟩
    exact absurd (hB (Set.mem_setOf.mpr (by omega : M < (B + M + 1) + 3))) (by omega)))

/-- **The full interaction-output space is not locally compact.**  Every neighbourhood of a point
leaves infinitely many block outputs unrestricted, so no compact set is a neighbourhood. -/
theorem not_locallyCompactSpace_pi_real : ¬ LocallyCompactSpace (ℕ → ℝ) := by
  intro hloc
  obtain ⟨K, hKcompact, hKnhds⟩ := exists_compact_mem_nhds (0 : ℕ → ℝ)
  rw [nhds_pi, Filter.mem_pi] at hKnhds
  obtain ⟨I, hIfin, t, hti, hsub⟩ := hKnhds
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ℕ, i₀ ∉ I := by
    by_contra hcon
    have huniv : I = Set.univ :=
      Set.eq_univ_of_forall (fun x => not_not.mp (fun hx => hcon ⟨x, hx⟩))
    exact Set.infinite_univ (huniv ▸ hIfin)
  have himage : (fun y : ℕ → ℝ => y i₀) '' K = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    refine ⟨Function.update (0 : ℕ → ℝ) i₀ a, hsub ?_, ?_⟩
    · intro i hi
      have hne : i ≠ i₀ := fun h => hi₀ (h ▸ hi)
      rw [Function.update_of_ne hne]
      exact mem_of_mem_nhds (hti i)
    · exact Function.update_self i₀ a (0 : ℕ → ℝ)
  have hcompactUniv : IsCompact (Set.univ : Set ℝ) := by
    rw [← himage]
    exact hKcompact.image (continuous_apply i₀)
  exact NoncompactSpace.noncompact_univ hcompactUniv

end Tower

section FaceLaw

variable {N : ℕ}

theorem faceBracketFamily_of_ne (N : ℕ) (S : Finset (Fin N)) {r : ℕ} (h : r ≠ N) :
    faceBracketFamily N S r = 0 := by
  refine AlternatingMap.ext fun v => ?_
  apply Subtype.ext
  simp [faceBracketFamily, bracketFamily_of_ne h]

/-- The minimal law induced on a colour face by restriction of every operation. -/
noncomputable def faceLaw (N : ℕ) (hN : 2 ≤ N) (S : Finset (Fin N)) :
    MinimalLaw (fun r => ↥(⋀[ℝ]^r ↥(colorFace N S))) ↥(colorFace N S) where
  operation r := exteriorPower.alternatingMapLinearEquiv (faceBracketFamily N S r)
  unary_zero := by
    rw [faceBracketFamily_of_ne N S (by omega : (1 : ℕ) ≠ N)]
    exact map_zero _

/-- **Every proper colour face is abelian.**  An observer retaining fewer than `N` colours sees the
zero law. -/
theorem faceLaw_isAbelian (hN : 2 ≤ N) (S : Finset (Fin N)) (hS : S ≠ Finset.univ) :
    (faceLaw N hN S).IsAbelian := by
  intro r _
  show exteriorPower.alternatingMapLinearEquiv (faceBracketFamily N S r) = 0
  rw [faceBracketFamily_eq_zero N S hS r]
  exact map_zero _

theorem faceLaw_isAbelian_of_card_lt (hN : 2 ≤ N) (S : Finset (Fin N)) (hS : S.card < N) :
    (faceLaw N hN S).IsAbelian := by
  refine faceLaw_isAbelian hN S ?_
  intro hcon
  rw [hcon, Finset.card_univ, Fintype.card_fin] at hS
  exact lt_irrefl N hS

/-- **Irreducible proper-face-invisible law.**  Every colour face with fewer than `N` colours
carries the zero law; the total law is not homotopy abelian; its interaction order is exactly `N`;
and every observer truncating below arity `N` reports an abelian law. -/
theorem irreducible_properFace_invisible (N : ℕ) (hN : 2 ≤ N) :
    (∀ S : Finset (Fin N), S.card < N → (faceLaw N hN S).IsAbelian) ∧
      ¬ (irreducibleLaw N hN).IsAbelian ∧
      (irreducibleLaw N hN).FirstNonzero N ∧
      (∀ M : ℕ, M < N → (arityTruncation M (irreducibleLaw N hN)).IsAbelian) :=
  ⟨fun S hS => faceLaw_isAbelian_of_card_lt hN S hS, irreducibleLaw_not_isAbelian hN,
    irreducibleLaw_firstNonzero hN, fun _ hM => arityTruncation_isAbelian hN hM⟩

end FaceLaw

section Spectrum

/-- **Unbounded interaction spectrum.**  The product tower squares to zero; an arity-`M` observer
annihilates every block of order above `M`; the resulting invisible tail is an infinite independent
family meeting the visible head only at zero; and the full interaction-output space is not locally
compact. -/
theorem unbounded_interaction_spectrum (M : ℕ) :
    (∀ (r s : ℕ) (v : Fin r → TowerCarrier) (w : Fin s → TowerCarrier) (i : Fin s),
        towerBracket s (Function.update w i (towerBracket r v)) = 0) ∧
      (∀ r ≤ M, ∀ m, M < m + 3 → ∀ v : Fin r → TowerCarrier, towerBracket r v m = 0) ∧
      Function.Injective (zTail M) ∧
      Infinite {m : ℕ // M < m + 3} ∧
      LinearMap.range (zTail M) ⊓ towerHead M = ⊥ ∧
      ¬ LocallyCompactSpace (ℕ → ℝ) :=
  ⟨fun r s v w i => towerBracket_composite_eq_zero r s v w i,
    fun _ hr _ hm v => towerBracket_apply_eq_zero_of_le hr hm v,
    zTail_injective M, instInfiniteTailIndex M, zTail_range_disjoint_towerHead M,
    not_locallyCompactSpace_pi_real⟩

end Spectrum

end GaloisForLFunctions.HTGeometry
