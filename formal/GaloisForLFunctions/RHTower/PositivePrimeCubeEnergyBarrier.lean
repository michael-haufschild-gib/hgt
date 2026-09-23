import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
/-!
# Positive prime cubes can force an intermediate energy barrier

This source-shape countermodel uses the literal unsigned prime difference on a
four-coordinate Boolean cube. Every source coefficient is strictly positive,
every first step contracts, and the complete signed source vanishes. Nevertheless
every order passes above the initial diagonal. The full background-parameter
family has the sharp threshold `e^(2 : ℕ)+e ≥ 1/8`.

This cube is not the actual arithmetic divisor source. It rules out a generic
positivity/endpoint argument, not the source-specific PE4 or SD1 statements.
All identities are symbolic; no experimental data is a proof input.
-/

open Finset
noncomputable section
namespace RHTower

abbrev FourPrimeCubeVertex := Finset (Fin 4)

def fourPrimeCubeAxes : Finset (Fin 4) := insert 0 (insert 1 (insert 2 (insert 3 ∅)))

def fourPrimeCubeEnergy (f : FourPrimeCubeVertex → ℝ) : ℝ :=
  ∑ S ∈ fourPrimeCubeAxes.powerset, (f S)^(2 : ℕ)

/-- The literal unsigned prime difference, discarding the coordinate containing that prime. -/
def fourPrimeCubeMerge (i : Fin 4) (f : FourPrimeCubeVertex → ℝ) (S : FourPrimeCubeVertex) : ℝ :=
  if i ∈ S then 0 else f S-f (insert i S)

/-- One prime difference erases every constant unsigned background. -/
theorem fourPrimeCubeMerge_add_const (i : Fin 4) (f : FourPrimeCubeVertex → ℝ) (e : ℝ) :
    fourPrimeCubeMerge i (fun S => f S+e) = fourPrimeCubeMerge i f := by
  funext S
  unfold fourPrimeCubeMerge
  split_ifs <;> ring

/-- Four even vertices of amplitude one and the complementary odd vertex of amplitude four. -/
def positivePrimeCubeBase (S : FourPrimeCubeVertex) : ℝ :=
  if S = ∅ then 1 else if S.card = 2 ∧ 0 ∈ S then 1
    else if S.card = 3 ∧ 0 ∉ S then 4 else 0

def positivePrimeCubeSource (e : ℝ) (S : FourPrimeCubeVertex) : ℝ := positivePrimeCubeBase S+e

/-- Every source coordinate is strictly positive at every positive background. -/
theorem positivePrimeCubeSource_pos {e : ℝ} (he : 0<e) (S : FourPrimeCubeVertex) :
    0 < positivePrimeCubeSource e S := by
  unfold positivePrimeCubeSource positivePrimeCubeBase
  split_ifs <;> linarith

private theorem cube_energy_explicit (f : FourPrimeCubeVertex → ℝ) :
    fourPrimeCubeEnergy f =
      f ∅^(2 : ℕ)+f {0}^(2 : ℕ)+f {1}^(2 : ℕ)+f {2}^(2 : ℕ)+f {3}^(2 : ℕ)+f {0,1}^(2 : ℕ)+f {0,2}^(2 : ℕ)+f {0,3}^(2 : ℕ)+
      f {1,2}^(2 : ℕ)+f {1,3}^(2 : ℕ)+f {2,3}^(2 : ℕ)+f {0,1,2}^(2 : ℕ)+f {0,1,3}^(2 : ℕ)+f {0,2,3}^(2 : ℕ)+
      f {1,2,3}^(2 : ℕ)+f {0,1,2,3}^(2 : ℕ) := by
  simp only [fourPrimeCubeEnergy,fourPrimeCubeAxes,
    sum_powerset_insert (by decide : (0:Fin 4) ∉ insert (1:Fin 4) (insert (2:Fin 4) (insert (3:Fin 4) ∅))),
    sum_powerset_insert (by decide : (1:Fin 4) ∉ insert (2:Fin 4) (insert (3:Fin 4) ∅)),
    sum_powerset_insert (by decide : (2:Fin 4) ∉ insert (3:Fin 4) ∅),
    sum_powerset_insert (by decide : (3:Fin 4) ∉ (∅:Finset (Fin 4))),
    powerset_empty,sum_singleton]
  simp only [insert_empty_eq]
  ring

/-- Exact initial diagonal of the complete positive source. -/
theorem positivePrimeCube_initial_energy (e : ℝ) :
    fourPrimeCubeEnergy (positivePrimeCubeSource e) = 20+16*e+16*e^(2 : ℕ) := by
  rw [cube_energy_explicit]
  norm_num [positivePrimeCubeSource,positivePrimeCubeBase,Fin.ext_iff]
  ring

/-- The first merger removes the background and leaves energy twenty, at every coordinate. -/
theorem positivePrimeCube_first_energy (e : ℝ) (i : Fin 4) :
    fourPrimeCubeEnergy (fourPrimeCubeMerge i (positivePrimeCubeSource e)) = 20 := by
  change fourPrimeCubeEnergy (fourPrimeCubeMerge i (fun S => positivePrimeCubeBase S+e)) = 20
  rw [fourPrimeCubeMerge_add_const,cube_energy_explicit]
  fin_cases i <;> norm_num [fourPrimeCubeMerge,positivePrimeCubeBase,Fin.ext_iff]

/-- Every ordered pair of distinct coordinates has the same energy barrier. -/
theorem positivePrimeCube_second_energy (e : ℝ) (i j : Fin 4) (hij : i≠j) :
    fourPrimeCubeEnergy (fourPrimeCubeMerge j (fourPrimeCubeMerge i (positivePrimeCubeSource e))) = 22 := by
  change fourPrimeCubeEnergy (fourPrimeCubeMerge j
    (fourPrimeCubeMerge i (fun S => positivePrimeCubeBase S+e))) = 22
  rw [fourPrimeCubeMerge_add_const,cube_energy_explicit]
  fin_cases i <;> fin_cases j <;> norm_num [fourPrimeCubeMerge,positivePrimeCubeBase,Fin.ext_iff] at *
set_option maxHeartbeats 1000000 in
/-- Every three distinct processed coordinates expose the same compensating triple mass. -/
theorem positivePrimeCube_third_energy (e : ℝ) (i j k : Fin 4)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    fourPrimeCubeEnergy (fourPrimeCubeMerge k (fourPrimeCubeMerge j
      (fourPrimeCubeMerge i (positivePrimeCubeSource e)))) = 18 := by
  change fourPrimeCubeEnergy (fourPrimeCubeMerge k (fourPrimeCubeMerge j
    (fourPrimeCubeMerge i (fun S => positivePrimeCubeBase S+e)))) = 18
  rw [fourPrimeCubeMerge_add_const]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Fin.ext_iff]
  all_goals rw [cube_energy_explicit]
  all_goals norm_num [fourPrimeCubeMerge,positivePrimeCubeBase,Fin.ext_iff]

set_option maxHeartbeats 1000000 in
/-- The complete signed source has zero final energy in every coordinate order. -/
theorem positivePrimeCube_fourth_energy (e : ℝ) (i j k l : Fin 4)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l) :
    fourPrimeCubeEnergy (fourPrimeCubeMerge l (fourPrimeCubeMerge k (fourPrimeCubeMerge j
      (fourPrimeCubeMerge i (positivePrimeCubeSource e))))) = 0 := by
  change fourPrimeCubeEnergy (fourPrimeCubeMerge l (fourPrimeCubeMerge k (fourPrimeCubeMerge j
    (fourPrimeCubeMerge i (fun S => positivePrimeCubeBase S+e))))) = 0
  rw [fourPrimeCubeMerge_add_const]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all [Fin.ext_iff]
  all_goals rw [cube_energy_explicit]
  all_goals norm_num [fourPrimeCubeMerge,positivePrimeCubeBase,Fin.ext_iff]

/-- The actual intermediate-energy ceiling along one four-coordinate order. -/
def positivePrimeCubeOrderWithin (e : ℝ) (i j k l : Fin 4) : Prop :=
  fourPrimeCubeEnergy (fourPrimeCubeMerge i (positivePrimeCubeSource e)) ≤
      fourPrimeCubeEnergy (positivePrimeCubeSource e) ∧
  fourPrimeCubeEnergy (fourPrimeCubeMerge j (fourPrimeCubeMerge i (positivePrimeCubeSource e))) ≤
      fourPrimeCubeEnergy (positivePrimeCubeSource e) ∧
  fourPrimeCubeEnergy (fourPrimeCubeMerge k (fourPrimeCubeMerge j
      (fourPrimeCubeMerge i (positivePrimeCubeSource e)))) ≤
      fourPrimeCubeEnergy (positivePrimeCubeSource e) ∧
  fourPrimeCubeEnergy (fourPrimeCubeMerge l (fourPrimeCubeMerge k (fourPrimeCubeMerge j
      (fourPrimeCubeMerge i (positivePrimeCubeSource e))))) ≤
      fourPrimeCubeEnergy (positivePrimeCubeSource e)

/-- Exact parameter classification: every valid order has the same ceiling threshold. -/
theorem positivePrimeCube_order_ceiling_iff (e : ℝ) (i j k l : Fin 4)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l) :
    positivePrimeCubeOrderWithin e i j k l ↔ (1:ℝ)/8 ≤ e^(2 : ℕ)+e := by
  rw [positivePrimeCubeOrderWithin,positivePrimeCube_initial_energy,
    positivePrimeCube_first_energy,positivePrimeCube_second_energy e i j hij,
    positivePrimeCube_third_energy e i j k hij hik hjk,
    positivePrimeCube_fourth_energy e i j k l hij hik hil hjk hjl hkl]
  constructor
  · intro h
    linarith only [h.2.1]
  · intro h
    constructor
    · linarith only [h]
    constructor
    · linarith only [h]
    constructor <;> linarith only [h]

/-- A strictly positive source, strictly contracting first steps and zero final source do not
prevent an order-independent second-step barrier above the original diagonal. -/
theorem positivePrimeCube_strict_counterexample :
    (∀ S, 0 < positivePrimeCubeSource (1/16) S) ∧
    fourPrimeCubeEnergy (positivePrimeCubeSource (1/16)) = (337:ℝ)/16 ∧
    (∀ i : Fin 4, fourPrimeCubeEnergy (fourPrimeCubeMerge i (positivePrimeCubeSource (1/16))) <
      fourPrimeCubeEnergy (positivePrimeCubeSource (1/16))) ∧
    (∀ i j : Fin 4, i≠j → fourPrimeCubeEnergy (fourPrimeCubeMerge j
      (fourPrimeCubeMerge i (positivePrimeCubeSource (1/16)))) -
      fourPrimeCubeEnergy (positivePrimeCubeSource (1/16)) = (15:ℝ)/16) ∧
    fourPrimeCubeEnergy (fourPrimeCubeMerge 3 (fourPrimeCubeMerge 2 (fourPrimeCubeMerge 1
      (fourPrimeCubeMerge 0 (positivePrimeCubeSource (1/16)))))) = 0 := by
  refine ⟨fun S => positivePrimeCubeSource_pos (by norm_num) S,?_,?_,?_,?_⟩
  · rw [positivePrimeCube_initial_energy]
    norm_num
  · intro i
    rw [positivePrimeCube_first_energy,positivePrimeCube_initial_energy]
    norm_num
  · intro i j hij
    rw [positivePrimeCube_second_energy (1/16) i j hij,positivePrimeCube_initial_energy]
    norm_num
  · exact positivePrimeCube_fourth_energy (1/16) 0 1 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end RHTower
