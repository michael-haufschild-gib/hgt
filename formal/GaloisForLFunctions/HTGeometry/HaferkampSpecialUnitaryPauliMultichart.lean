import GaloisForLFunctions.HTGeometry.HaferkampSpecialUnitaryPauliCoordinates

/-!
# Simultaneous two-qubit Pauli coordinate chart

This module combines the fifteen certified one-parameter `SU(4)` Pauli paths
into one finite real coordinate chart in the ambient matrix space.  Its
Fréchet derivative at the identity has the full fifteen-dimensional Pauli
tangent range.
-/

open Matrix
open scoped BigOperators Matrix.Norms.Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance haferkampSpecialUnitaryPauliMultichartDecidableEqPauliLabel :
    DecidableEq boolNonidentityTwoQubitPauliLabel := Classical.decEq _
local instance haferkampSpecialUnitaryPauliMultichartFintypePauliLabel :
    Fintype boolNonidentityTwoQubitPauliLabel := Fintype.ofFinite _

/-- Ambient matrix product underlying a finite collection of local Pauli paths. -/
def boolNonidentityTwoQubitPauliPathProduct
    (L : List boolNonidentityTwoQubitPauliLabel)
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (L.map fun pq =>
    (boolNonidentityTwoQubitPauliPath pq (x pq) :
      Matrix (Bool × Bool) (Bool × Bool) ℂ)).prod

private theorem boolNonidentityTwoQubitPauliPathProduct_cons
    (pq : boolNonidentityTwoQubitPauliLabel)
    (L : List boolNonidentityTwoQubitPauliLabel)
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    boolNonidentityTwoQubitPauliPathProduct (pq :: L) x =
      (boolNonidentityTwoQubitPauliPath pq (x pq) :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) *
      boolNonidentityTwoQubitPauliPathProduct L x := rfl

private theorem boolNonidentityTwoQubitPauliPathProduct_eq_one
    (L : List boolNonidentityTwoQubitPauliLabel)
    (x : boolNonidentityTwoQubitPauliLabel → ℝ)
    (hx : ∀ pq ∈ L, x pq = 0) :
    boolNonidentityTwoQubitPauliPathProduct L x = 1 := by
  apply List.prod_eq_one
  intro M hM
  rcases List.mem_map.mp hM with ⟨pq, hpq, rfl⟩
  rw [hx pq hpq, boolNonidentityTwoQubitPauliPath_zero]
  rfl

private theorem differentiableAt_boolNonidentityTwoQubitPauliPathProduct
    (L : List boolNonidentityTwoQubitPauliLabel) :
    DifferentiableAt ℝ
      (boolNonidentityTwoQubitPauliPathProduct L) 0 := by
  induction L with
  | nil =>
      exact differentiableAt_const (c :=
        (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ))
  | cons pq L ih =>
      change DifferentiableAt ℝ
        (fun x : boolNonidentityTwoQubitPauliLabel → ℝ =>
          (boolNonidentityTwoQubitPauliPath pq (x pq) :
            Matrix (Bool × Bool) (Bool × Bool) ℂ) *
          boolNonidentityTwoQubitPauliPathProduct L x) 0
      have hhead : DifferentiableAt ℝ
          (fun x : boolNonidentityTwoQubitPauliLabel → ℝ =>
            (boolNonidentityTwoQubitPauliPath pq (x pq) :
              Matrix (Bool × Bool) (Bool × Bool) ℂ)) 0 := by
        exact (HasFDerivAt.comp
          (f := fun x : boolNonidentityTwoQubitPauliLabel → ℝ => x pq)
          (g := fun t : ℝ =>
            (boolNonidentityTwoQubitPauliPath pq t :
              Matrix (Bool × Bool) (Bool × Bool) ℂ))
          0 (entrywiseHasDerivAt_boolNonidentityTwoQubitPauliPath pq).hasFDerivAt
          (hasFDerivAt_apply pq 0)).differentiableAt
      exact hhead.mul ih

private theorem boolNonidentityTwoQubitPauliPathProduct_single
    (L : List boolNonidentityTwoQubitPauliLabel)
    (pq : boolNonidentityTwoQubitPauliLabel)
    (hL : L.Nodup) (hpq : pq ∈ L) (t : ℝ) :
    boolNonidentityTwoQubitPauliPathProduct L (Pi.single pq t) =
      (boolNonidentityTwoQubitPauliPath pq t :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  induction L with
  | nil => simp at hpq
  | cons a L ih =>
      obtain ⟨haL, hLtail⟩ := List.nodup_cons.mp hL
      rw [boolNonidentityTwoQubitPauliPathProduct_cons]
      by_cases ha : a = pq
      · subst a
        have htail : boolNonidentityTwoQubitPauliPathProduct L (Pi.single pq t) = 1 :=
          boolNonidentityTwoQubitPauliPathProduct_eq_one L (Pi.single pq t) (by
            intro r hr
            have hrne : r ≠ pq := fun h => haL (h ▸ hr)
            simp [hrne])
        rw [htail]
        simp
      · have hpqL : pq ∈ L :=
          (List.mem_cons.mp hpq).resolve_left (fun h => ha h.symm)
        have htail := ih hLtail hpqL
        have hhead : (Pi.single pq t :
            boolNonidentityTwoQubitPauliLabel → ℝ) a = 0 := by
          simp [ha]
        rw [hhead, boolNonidentityTwoQubitPauliPath_zero, htail]
        simp

/-- Simultaneous ambient matrix chart from all nonidentity two-qubit Pauli
coordinates. -/
def boolNonidentityTwoQubitPauliCoordinateChart
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  boolNonidentityTwoQubitPauliPathProduct Finset.univ.toList x

/-- The simultaneous Pauli-coordinate chart as an actual `SU(4)`-valued
map, rather than only its ambient matrix coercion. -/
def boolNonidentityTwoQubitPauliCoordinateGate
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  (Finset.univ.toList.map fun pq =>
    boolNonidentityTwoQubitPauliPath pq (x pq)).prod

theorem boolNonidentityTwoQubitPauliCoordinateGate_coe
    (x : boolNonidentityTwoQubitPauliLabel → ℝ) :
    (boolNonidentityTwoQubitPauliCoordinateGate x :
      Matrix (Bool × Bool) (Bool × Bool) ℂ) =
      boolNonidentityTwoQubitPauliCoordinateChart x := by
  rw [boolNonidentityTwoQubitPauliCoordinateGate]
  change (SubmonoidClass.subtype (Matrix.specialUnitaryGroup (Bool × Bool) ℂ))
      ((Finset.univ.toList.map fun pq =>
        boolNonidentityTwoQubitPauliPath pq (x pq)).prod) = _
  rw [MonoidHom.map_list_prod]
  rw [List.map_map]
  rfl

@[simp] theorem boolNonidentityTwoQubitPauliCoordinateChart_zero :
    boolNonidentityTwoQubitPauliCoordinateChart 0 = 1 := by
  change boolNonidentityTwoQubitPauliPathProduct Finset.univ.toList 0 = 1
  apply boolNonidentityTwoQubitPauliPathProduct_eq_one
  intro pq _
  rfl

@[simp] theorem boolNonidentityTwoQubitPauliCoordinateGate_zero :
    boolNonidentityTwoQubitPauliCoordinateGate 0 = 1 := by
  apply Subtype.ext
  rw [boolNonidentityTwoQubitPauliCoordinateGate_coe,
    boolNonidentityTwoQubitPauliCoordinateChart_zero]
  rfl

theorem differentiableAt_boolNonidentityTwoQubitPauliCoordinateChart_zero :
    DifferentiableAt ℝ boolNonidentityTwoQubitPauliCoordinateChart 0 :=
  differentiableAt_boolNonidentityTwoQubitPauliPathProduct Finset.univ.toList

/-- Restricting the simultaneous coordinate chart to one coordinate line
recovers the corresponding one-parameter Pauli path exactly. -/
theorem boolNonidentityTwoQubitPauliCoordinateChart_single
    (pq : boolNonidentityTwoQubitPauliLabel) (t : ℝ) :
    boolNonidentityTwoQubitPauliCoordinateChart (Pi.single pq t) =
      (boolNonidentityTwoQubitPauliPath pq t :
        Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  exact boolNonidentityTwoQubitPauliPathProduct_single Finset.univ.toList pq
    (Finset.nodup_toList _) (by simp) t

/-- Real-linear tangent map of the simultaneous local Pauli coordinate chart. -/
def boolNonidentityTwoQubitPauliTangentMap :
    (boolNonidentityTwoQubitPauliLabel → ℝ) →L[ℝ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ where
  toFun := fun x => ∑ pq, x pq • boolNonidentityTwoQubitPauliTangent pq
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro pq _
    change (c * x pq) • boolNonidentityTwoQubitPauliTangent pq =
      c • (x pq • boolNonidentityTwoQubitPauliTangent pq)
    rw [mul_smul]

/-- The actual Fréchet derivative of the simultaneous local `SU(4)` Pauli
coordinate chart at identity is its finite Pauli tangent map. -/
theorem hasFDerivAt_boolNonidentityTwoQubitPauliCoordinateChart_zero :
    HasFDerivAt boolNonidentityTwoQubitPauliCoordinateChart
      boolNonidentityTwoQubitPauliTangentMap 0 := by
  let f : (boolNonidentityTwoQubitPauliLabel → ℝ) →
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    boolNonidentityTwoQubitPauliCoordinateChart
  have hdiff : DifferentiableAt ℝ f 0 := by
    exact differentiableAt_boolNonidentityTwoQubitPauliCoordinateChart_zero
  have hfull : HasFDerivAt f (fderiv ℝ f 0) 0 := hdiff.hasFDerivAt
  have haxis (pq : boolNonidentityTwoQubitPauliLabel) :
      (fderiv ℝ f 0) (Pi.single pq (1 : ℝ)) =
        boolNonidentityTwoQubitPauliTangent pq := by
    let singleCLM : ℝ →L[ℝ] (boolNonidentityTwoQubitPauliLabel → ℝ) :=
      ContinuousLinearMap.single ℝ
        (fun _ : boolNonidentityTwoQubitPauliLabel => ℝ) pq
    have hsingle : HasFDerivAt
        (fun t : ℝ => Pi.single pq t) singleCLM 0 := by
      change HasFDerivAt
        (singleCLM : ℝ → (boolNonidentityTwoQubitPauliLabel → ℝ)) singleCLM 0
      exact singleCLM.hasFDerivAt
    have hbase : HasFDerivAt f (fderiv ℝ f 0) (Pi.single pq (0 : ℝ)) := by
      simpa using hfull
    have hcomp := HasFDerivAt.comp
      (f := fun t : ℝ => Pi.single pq t) (g := f) 0 hbase hsingle
    have haxisExact : HasFDerivAt
        (fun t : ℝ => f (Pi.single pq t))
        (ContinuousLinearMap.toSpanSingleton ℝ
          (boolNonidentityTwoQubitPauliTangent pq)) 0 := by
      rw [show (fun t : ℝ => f (Pi.single pq t)) =
          (fun t : ℝ => (boolNonidentityTwoQubitPauliPath pq t :
            Matrix (Bool × Bool) (Bool × Bool) ℂ)) by
        funext t
        exact boolNonidentityTwoQubitPauliCoordinateChart_single pq t]
      exact (entrywiseHasDerivAt_boolNonidentityTwoQubitPauliPath pq).hasFDerivAt
    have hderiv : (fderiv ℝ f 0).comp singleCLM =
        ContinuousLinearMap.toSpanSingleton ℝ
          (boolNonidentityTwoQubitPauliTangent pq) := by
      apply hcomp.unique
      exact haxisExact
    have hvalue := congrArg (fun L : ℝ →L[ℝ]
        Matrix (Bool × Bool) (Bool × Bool) ℂ => L 1) hderiv
    change (fderiv ℝ f 0) (Pi.single pq (1 : ℝ)) = _ at hvalue
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using hvalue
  have hmap : fderiv ℝ f 0 = boolNonidentityTwoQubitPauliTangentMap := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      (fderiv ℝ f 0) x =
          (fderiv ℝ f 0) (∑ pq, Pi.single pq (x pq)) := by
            rw [Finset.univ_sum_single]
      _ = ∑ pq, (fderiv ℝ f 0) (Pi.single pq (x pq)) := by rw [map_sum]
      _ = ∑ pq, x pq • boolNonidentityTwoQubitPauliTangent pq := by
        apply Finset.sum_congr rfl
        intro pq _
        have hsingle : Pi.single pq (x pq) = x pq • Pi.single pq (1 : ℝ) := by
          ext q
          by_cases hqp : q = pq
          · subst q
            simp
          · simp [hqp]
        rw [hsingle, map_smul, haxis pq]
      _ = boolNonidentityTwoQubitPauliTangentMap x := by rfl
  rw [show boolNonidentityTwoQubitPauliCoordinateChart = f by rfl]
  exact hfull.congr_fderiv hmap

/-- Applying the chart tangent map to a single coordinate returns its
corresponding Pauli tangent. -/
theorem boolNonidentityTwoQubitPauliTangentMap_single
    (pq : boolNonidentityTwoQubitPauliLabel) (c : ℝ) :
    boolNonidentityTwoQubitPauliTangentMap (Pi.single pq c) =
      c • boolNonidentityTwoQubitPauliTangent pq := by
  change ∑ q, (Pi.single pq c : boolNonidentityTwoQubitPauliLabel → ℝ) q •
      boolNonidentityTwoQubitPauliTangent q = _
  rw [Finset.sum_eq_single pq (fun q _ hq => by simp [hq])
    (fun h => absurd (Finset.mem_univ pq) h)]
  simp

/-- The local chart's fifteen coordinate tangent images are real-linearly
independent. -/
theorem linearIndependent_boolNonidentityTwoQubitPauliTangentMap_single :
    LinearIndependent ℝ (fun pq : boolNonidentityTwoQubitPauliLabel =>
      boolNonidentityTwoQubitPauliTangentMap (Pi.single pq 1)) := by
  have hreal : LinearIndependent ℝ boolNonidentityTwoQubitPauliTangent :=
    LinearIndependent.restrict_scalars' ℝ
      linearIndependent_boolNonidentityTwoQubitPauliTangent
  simpa only [boolNonidentityTwoQubitPauliTangentMap_single, one_smul] using hreal

/-- The simultaneous local coordinate tangent map has full fifteen-direction
range rank. -/
theorem finrank_range_ge_boolNonidentityTwoQubitPauliTangentMap :
    Fintype.card boolNonidentityTwoQubitPauliLabel ≤
      Module.finrank ℝ boolNonidentityTwoQubitPauliTangentMap.range := by
  let D : (boolNonidentityTwoQubitPauliLabel → ℝ) →L[ℝ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    boolNonidentityTwoQubitPauliTangentMap
  have himages : LinearIndependent ℝ (fun pq : boolNonidentityTwoQubitPauliLabel =>
      D (Pi.single pq 1)) := by
    simpa only [D, boolNonidentityTwoQubitPauliTangentMap_single, one_smul] using
      linearIndependent_boolNonidentityTwoQubitPauliTangentMap_single
  let values : boolNonidentityTwoQubitPauliLabel → D.range :=
    fun pq => ⟨D (Pi.single pq 1), ⟨Pi.single pq 1, rfl⟩⟩
  have hcomp : LinearIndependent ℝ (D.range.subtype ∘ values) := by
    simpa [values, Function.comp_def] using himages
  have hvalues : LinearIndependent ℝ values :=
    LinearIndependent.of_comp D.range.subtype hcomp
  calc
    Fintype.card boolNonidentityTwoQubitPauliLabel =
        (Set.range values).finrank ℝ := by
          simpa using (linearIndependent_iff_card_eq_finrank_span.mp hvalues)
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range values)) := rfl
    _ ≤ Module.finrank ℝ D.range := Submodule.finrank_le _

/-- The actual Fréchet derivative of the simultaneous local coordinate chart
has the full fifteen-direction range rank. -/
theorem finrank_range_ge_fderiv_boolNonidentityTwoQubitPauliCoordinateChart :
    Fintype.card boolNonidentityTwoQubitPauliLabel ≤ Module.finrank ℝ
      (fderiv ℝ boolNonidentityTwoQubitPauliCoordinateChart 0).range := by
  have hderiv := hasFDerivAt_boolNonidentityTwoQubitPauliCoordinateChart_zero.fderiv
  rw [hderiv]
  exact finrank_range_ge_boolNonidentityTwoQubitPauliTangentMap

/-- There are exactly fifteen nonidentity two-qubit Boolean Pauli labels. -/
theorem card_boolNonidentityTwoQubitPauliLabel :
    Fintype.card boolNonidentityTwoQubitPauliLabel = 15 := by
  let p : Option (Fin 3) × Option (Fin 3) → Prop :=
    fun pq => pq = (none, none)
  have hp : ∀ pq : Option (Fin 3) × Option (Fin 3),
      (pq.1 ≠ none ∨ pq.2 ≠ none) ↔ ¬ p pq := by
    rintro ⟨a, b⟩
    constructor
    · intro h hzero
      rcases h with ha | hb
      · apply ha
        exact congrArg Prod.fst hzero
      · apply hb
        exact congrArg Prod.snd hzero
    · intro h
      by_cases ha : a = none
      · right
        intro hb
        apply h
        change (a, b) = (none, none)
        exact Prod.ext ha hb
      · exact Or.inl ha
  calc
    Fintype.card boolNonidentityTwoQubitPauliLabel =
        Fintype.card {pq : Option (Fin 3) × Option (Fin 3) // ¬ p pq} :=
      Fintype.card_congr (Equiv.subtypeEquivRight hp)
    _ = Fintype.card (Option (Fin 3) × Option (Fin 3)) -
        Fintype.card {pq : Option (Fin 3) × Option (Fin 3) // p pq} :=
      Fintype.card_subtype_compl p
    _ = 15 := by
      rw [show Fintype.card {pq : Option (Fin 3) × Option (Fin 3) // p pq} = 1 by
        exact Fintype.card_subtype_eq
          ((none, none) : Option (Fin 3) × Option (Fin 3))]
      norm_num [Fintype.card_prod]

/-- Literal full local rank: the simultaneous `SU(4)` Pauli chart derivative
has range dimension at least fifteen. -/
theorem fifteen_le_finrank_range_fderiv_boolNonidentityTwoQubitPauliCoordinateChart :
    15 ≤ Module.finrank ℝ
      (fderiv ℝ boolNonidentityTwoQubitPauliCoordinateChart 0).range := by
  rw [← card_boolNonidentityTwoQubitPauliLabel]
  exact finrank_range_ge_fderiv_boolNonidentityTwoQubitPauliCoordinateChart

/-- Exact local rank: the finite fifteen-coordinate Pauli chart has a
fifteen-dimensional derivative range at identity. -/
theorem finrank_range_fderiv_boolNonidentityTwoQubitPauliCoordinateChart :
    Module.finrank ℝ
      (fderiv ℝ boolNonidentityTwoQubitPauliCoordinateChart 0).range = 15 := by
  let D : (boolNonidentityTwoQubitPauliLabel → ℝ) →L[ℝ]
      Matrix (Bool × Bool) (Bool × Bool) ℂ :=
    fderiv ℝ boolNonidentityTwoQubitPauliCoordinateChart 0
  change Module.finrank ℝ D.range = 15
  apply le_antisymm
  · calc
      Module.finrank ℝ D.range ≤
          Module.finrank ℝ (boolNonidentityTwoQubitPauliLabel → ℝ) :=
        LinearMap.finrank_range_le D.toLinearMap
      _ = Fintype.card boolNonidentityTwoQubitPauliLabel := Module.finrank_pi ℝ
      _ = 15 := card_boolNonidentityTwoQubitPauliLabel
  · exact fifteen_le_finrank_range_fderiv_boolNonidentityTwoQubitPauliCoordinateChart

end

end GaloisForLFunctions.HTGeometry
