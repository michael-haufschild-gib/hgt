import GaloisForLFunctions.BiScaleUncertainty.CoprimeProjectionLattice

/-!+# Arithmetic classification of projection commutators

Bézout produces adjacent active centers for coprime spacings. A forbidden trace
then detects the commutator by the exact value one half, including spacing two.+-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

theorem exists_adjacent_coprimeCenters (d e : ℕ) (h : Nat.Coprime (d + 2) (e + 2)) :
    ∃ i j, coprimeCenter d i = coprimeCenter e j + 1 := by
  obtain ⟨k, _, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime h (by omega)
  have hkpos : 0 < k := by
    by_contra hn
    have hz : k = 0 := by omega
    simp [hz] at hk
  let a := (d + 2) * k
  let b := a - 1
  have ha : 2 ≤ a := by dsimp [a]; nlinarith
  have hbpos : 0 < b := by dsimp [b]; omega
  have hab : a = b + 1 := by dsimp [b]; omega
  have hb : e + 2 ∣ b := by
    have hm := Nat.mod_add_div a (e + 2)
    change a % (e + 2) = 1 at hk
    rw [hk] at hm
    exact ⟨a / (e + 2), by omega⟩
  have hca : coprimeCenter d (k - 1) = a := by
    simp [coprimeCenter, Nat.sub_add_cancel hkpos, a]
  have hcb := coprimeCenter_index hbpos hb
  exact ⟨k - 1, b / (e + 2) - 1, by rw [hca, hcb]; exact hab⟩

theorem primitive_coprimeProjection_forbidden (d n : ℕ) (q : Velocity)
    (hn : ¬d + 2 ∣ n) : primitive (coprimeProjection d q) n = 0 := by
  rw [coprimeProjection_eq_extension, primitive_coprimeExtension_nat]
  simp [hn]

/-- An adjacent center gives an exact commutator trace, without truncation. -/
theorem coprime_commutator_adjacent_trace (d e i j : ℕ)
    (h : coprimeCenter d i = coprimeCenter e j + 1) :
    primitive (coprimeProjection d (coprimeProjection e (tentVelocity d i)) -
      coprimeProjection e (coprimeProjection d (tentVelocity d i)))
      (coprimeCenter e j) = (1 / 2 : ℝ) := by
  have hn : ¬d + 2 ∣ coprimeCenter e j := by
    intro hn
    exact not_adjacent_of_common_divisor (by omega) hn (coprimeCenter_dvd d i) h.symm
  have hcross : ⟪tentVelocity e j, tentVelocity d i⟫ = -1 := by
    have hne : coprimeCenter e j ≠ coprimeCenter d i := by omega
    simp [inner_tentVelocity_cross, hne, h.symm]
  rw [← inner_prefixCell, inner_sub_right, inner_prefixCell, inner_prefixCell,
    primitive_coprimeProjection_forbidden d _ _ hn, coprimeProjection_tent_self,
    coprimeProjection_active_trace, ← inner_tentVelocity_velocity, hcross]
  norm_num

/-- Coprime spacings have a concrete tent witness with commutator trace one half. -/
theorem exists_coprime_commutator_witness (d e : ℕ)
    (h : Nat.Coprime (d + 2) (e + 2)) :
    ∃ i j, coprimeCenter d i = coprimeCenter e j + 1 ∧
      primitive (coprimeProjection d (coprimeProjection e (tentVelocity d i)) -
        coprimeProjection e (coprimeProjection d (tentVelocity d i)))
        (coprimeCenter e j) = (1 / 2 : ℝ) := by
  obtain ⟨i, j, hij⟩ := exists_adjacent_coprimeCenters d e h
  exact ⟨i, j, hij, coprime_commutator_adjacent_trace d e i j hij⟩

theorem coprimeProjection_not_commute (d e : ℕ)
    (h : Nat.Coprime (d + 2) (e + 2)) :
    ¬∀ q : Velocity, coprimeProjection d (coprimeProjection e q) =
      coprimeProjection e (coprimeProjection d q) := by
  intro hc
  obtain ⟨i, j, _, hw⟩ := exists_coprime_commutator_witness d e h
  rw [hc, sub_self, ← inner_prefixCell, inner_zero_right] at hw
  norm_num at hw

/-- Complete arithmetic classification for the infinite orthogonal projections. -/
theorem coprimeProjection_commute_iff (d e : ℕ) :
    (∀ q : Velocity, coprimeProjection d (coprimeProjection e q) =
      coprimeProjection e (coprimeProjection d q)) ↔
      2 ≤ Nat.gcd (d + 2) (e + 2) := by
  constructor
  · intro h
    by_contra hn
    have hp := Nat.gcd_pos_of_pos_left (e + 2) (by omega : 0 < d + 2)
    have hg : Nat.gcd (d + 2) (e + 2) = 1 := by omega
    exact coprimeProjection_not_commute d e hg h
  · exact coprimeProjection_commute_of_gcd d e

theorem coprimeProjector_commute_iff (d e : ℕ) :
    (coprimeProjector d).comp (coprimeProjector e) =
      (coprimeProjector e).comp (coprimeProjector d) ↔
      2 ≤ Nat.gcd (d + 2) (e + 2) := by
  rw [← coprimeProjection_commute_iff]
  constructor
  · intro h q
    exact congrArg (fun A : Velocity →L[ℝ] Velocity => A q) h
  · intro h
    exact ContinuousLinearMap.ext h

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
