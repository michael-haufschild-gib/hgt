import GaloisForLFunctions.HTGeometry.ConstitutiveContextResponseGeometry

/-!
# Calibrated harmonic context reconstruction

One harmonic-energy reporter on real binary formation trees, probed only by adjoining the three
fixed leaves `0`, `1`, and `-1`, reconstructs leaf count, signed endpoint sum, and positive square
mass. These three responses therefore classify every future one-hole context response. Binary
formation also forces the exact nonnegative between-block energy.
-/

namespace GaloisForLFunctions.HTGeometry

open ResponseTree ResponseContext

noncomputable section

/-- Number of generated leaves in a binary formation tree. -/
def harmonicTreeCount : ResponseTree ℝ → ℕ
  | .leaf _ => 1
  | .fork t u => harmonicTreeCount t + harmonicTreeCount u

/-- Coherent endpoint sum of the generated leaves. -/
def harmonicTreeSum : ResponseTree ℝ → ℝ
  | .leaf a => a
  | .fork t u => harmonicTreeSum t + harmonicTreeSum u

/-- Positive square mass of the generated leaves. -/
def harmonicTreeSqMass : ResponseTree ℝ → ℝ
  | .leaf a => a ^ (2 : ℕ)
  | .fork t u => harmonicTreeSqMass t + harmonicTreeSqMass u

/-- Within-block harmonic refinement energy. -/
def harmonicTreeEnergy (t : ResponseTree ℝ) : ℝ :=
  harmonicTreeSqMass t - harmonicTreeSum t ^ (2 : ℕ) / harmonicTreeCount t

@[simp] theorem harmonicTreeCount_leaf (a : ℝ) :
    harmonicTreeCount (.leaf a) = 1 := rfl

@[simp] theorem harmonicTreeCount_fork (t u : ResponseTree ℝ) :
    harmonicTreeCount (.fork t u) = harmonicTreeCount t + harmonicTreeCount u := rfl

@[simp] theorem harmonicTreeSum_leaf (a : ℝ) :
    harmonicTreeSum (.leaf a) = a := rfl

@[simp] theorem harmonicTreeSum_fork (t u : ResponseTree ℝ) :
    harmonicTreeSum (.fork t u) = harmonicTreeSum t + harmonicTreeSum u := rfl

@[simp] theorem harmonicTreeSqMass_leaf (a : ℝ) :
    harmonicTreeSqMass (.leaf a) = a ^ (2 : ℕ) := rfl

@[simp] theorem harmonicTreeSqMass_fork (t u : ResponseTree ℝ) :
    harmonicTreeSqMass (.fork t u) = harmonicTreeSqMass t + harmonicTreeSqMass u := rfl

theorem harmonicTreeCount_pos (t : ResponseTree ℝ) : 0 < harmonicTreeCount t := by
  induction t with
  | leaf a => simp
  | fork t u ht hu => simp only [harmonicTreeCount_fork]; omega

theorem harmonicTreeCount_ne_zero (t : ResponseTree ℝ) : harmonicTreeCount t ≠ 0 :=
  Nat.ne_of_gt (harmonicTreeCount_pos t)

/-- Harmonic response after adjoining one calibrated leaf. -/
def harmonicCalibrationResponse (t : ResponseTree ℝ) (a : ℝ) : ℝ :=
  harmonicTreeEnergy (.fork t (.leaf a))

theorem harmonicCalibrationResponse_formula (t : ResponseTree ℝ) (a : ℝ) :
    harmonicCalibrationResponse t a =
      harmonicTreeSqMass t + a ^ (2 : ℕ) -
        (harmonicTreeSum t + a) ^ (2 : ℕ) / (harmonicTreeCount t + 1) := by
  simp [harmonicCalibrationResponse, harmonicTreeEnergy]

/-- Second calibration difference recovers the formed population coefficient. -/
theorem harmonicCalibration_curvature (t : ResponseTree ℝ) :
    harmonicCalibrationResponse t 1 + harmonicCalibrationResponse t (-1) -
        2 * harmonicCalibrationResponse t 0 =
      2 * harmonicTreeCount t / (harmonicTreeCount t + 1) := by
  rw [harmonicCalibrationResponse_formula, harmonicCalibrationResponse_formula,
    harmonicCalibrationResponse_formula]
  have h : (harmonicTreeCount t : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The three calibration responses reconstruct the exact leaf count. -/
theorem harmonicCalibration_reconstruct_count (t : ResponseTree ℝ) :
    (harmonicTreeCount t : ℝ) =
      (harmonicCalibrationResponse t 1 + harmonicCalibrationResponse t (-1) -
          2 * harmonicCalibrationResponse t 0) /
        (2 - (harmonicCalibrationResponse t 1 + harmonicCalibrationResponse t (-1) -
          2 * harmonicCalibrationResponse t 0)) := by
  rw [harmonicCalibration_curvature]
  have h : (harmonicTreeCount t : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Odd calibration difference recovers the signed coherent endpoint. -/
theorem harmonicCalibration_difference (t : ResponseTree ℝ) :
    harmonicCalibrationResponse t (-1) - harmonicCalibrationResponse t 1 =
      4 * harmonicTreeSum t / (harmonicTreeCount t + 1) := by
  rw [harmonicCalibrationResponse_formula, harmonicCalibrationResponse_formula]
  have h : (harmonicTreeCount t : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The three calibration responses reconstruct the signed coherent endpoint. -/
theorem harmonicCalibration_reconstruct_sum (t : ResponseTree ℝ) :
    harmonicTreeSum t =
      ((harmonicTreeCount t : ℝ) + 1) / 4 *
        (harmonicCalibrationResponse t (-1) - harmonicCalibrationResponse t 1) := by
  rw [harmonicCalibration_difference]
  have h : (harmonicTreeCount t : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The zero calibration then reconstructs positive square mass. -/
theorem harmonicCalibration_reconstruct_sqMass (t : ResponseTree ℝ) :
    harmonicTreeSqMass t =
      harmonicCalibrationResponse t 0 +
        harmonicTreeSum t ^ (2 : ℕ) / (harmonicTreeCount t + 1) := by
  rw [harmonicCalibrationResponse_formula]
  ring

/-- Equality of the three source statistics generated by the harmonic response. -/
def SameHarmonicMoments (t u : ResponseTree ℝ) : Prop :=
  harmonicTreeCount t = harmonicTreeCount u ∧
    harmonicTreeSum t = harmonicTreeSum u ∧
    harmonicTreeSqMass t = harmonicTreeSqMass u

theorem sameHarmonicMoments_plug {t u : ResponseTree ℝ}
    (h : SameHarmonicMoments t u) (c : ResponseContext ℝ) :
    SameHarmonicMoments (c.plug t) (c.plug u) := by
  induction c with
  | hole => exact h
  | forkLeft c right ih =>
    rcases ih with ⟨hn, hs, hq⟩
    exact ⟨by simp [hn], by simp [hs], by simp [hq]⟩
  | forkRight left c ih =>
    rcases ih with ⟨hn, hs, hq⟩
    exact ⟨by simp [hn], by simp [hs], by simp [hq]⟩

theorem harmonicTreeEnergy_eq_of_sameMoments {t u : ResponseTree ℝ}
    (h : SameHarmonicMoments t u) : harmonicTreeEnergy t = harmonicTreeEnergy u := by
  rcases h with ⟨hn, hs, hq⟩
  simp [harmonicTreeEnergy, hn, hs, hq]

theorem contextEquivalent_harmonicTreeEnergy_of_sameMoments {t u : ResponseTree ℝ}
    (h : SameHarmonicMoments t u) : ContextEquivalent harmonicTreeEnergy t u := by
  intro c
  exact harmonicTreeEnergy_eq_of_sameMoments (sameHarmonicMoments_plug h c)

/-- Equality of the three fixed calibration-leaf responses. -/
def SameHarmonicCalibrations (t u : ResponseTree ℝ) : Prop :=
  harmonicCalibrationResponse t 0 = harmonicCalibrationResponse u 0 ∧
    harmonicCalibrationResponse t 1 = harmonicCalibrationResponse u 1 ∧
    harmonicCalibrationResponse t (-1) = harmonicCalibrationResponse u (-1)

theorem sameMoments_of_sameHarmonicCalibrations {t u : ResponseTree ℝ}
    (h : SameHarmonicCalibrations t u) : SameHarmonicMoments t u := by
  rcases h with ⟨hzero, hone, hneg⟩
  have hcountReal : (harmonicTreeCount t : ℝ) = harmonicTreeCount u := by
    calc
      (harmonicTreeCount t : ℝ) =
          (harmonicCalibrationResponse t 1 + harmonicCalibrationResponse t (-1) -
              2 * harmonicCalibrationResponse t 0) /
            (2 - (harmonicCalibrationResponse t 1 + harmonicCalibrationResponse t (-1) -
              2 * harmonicCalibrationResponse t 0)) := harmonicCalibration_reconstruct_count t
      _ = (harmonicCalibrationResponse u 1 + harmonicCalibrationResponse u (-1) -
              2 * harmonicCalibrationResponse u 0) /
            (2 - (harmonicCalibrationResponse u 1 + harmonicCalibrationResponse u (-1) -
              2 * harmonicCalibrationResponse u 0)) := by rw [hone, hneg, hzero]
      _ = harmonicTreeCount u := (harmonicCalibration_reconstruct_count u).symm
  have hcount : harmonicTreeCount t = harmonicTreeCount u := by exact_mod_cast hcountReal
  have hsum : harmonicTreeSum t = harmonicTreeSum u := by
    calc
      harmonicTreeSum t = ((harmonicTreeCount t : ℝ) + 1) / 4 *
          (harmonicCalibrationResponse t (-1) - harmonicCalibrationResponse t 1) :=
        harmonicCalibration_reconstruct_sum t
      _ = ((harmonicTreeCount u : ℝ) + 1) / 4 *
          (harmonicCalibrationResponse u (-1) - harmonicCalibrationResponse u 1) := by
        rw [hcount, hneg, hone]
      _ = harmonicTreeSum u := (harmonicCalibration_reconstruct_sum u).symm
  have hsq : harmonicTreeSqMass t = harmonicTreeSqMass u := by
    calc
      harmonicTreeSqMass t = harmonicCalibrationResponse t 0 +
          harmonicTreeSum t ^ (2 : ℕ) / (harmonicTreeCount t + 1) :=
        harmonicCalibration_reconstruct_sqMass t
      _ = harmonicCalibrationResponse u 0 +
          harmonicTreeSum u ^ (2 : ℕ) / (harmonicTreeCount u + 1) := by rw [hzero, hsum, hcount]
      _ = harmonicTreeSqMass u := (harmonicCalibration_reconstruct_sqMass u).symm
  exact ⟨hcount, hsum, hsq⟩

theorem sameHarmonicCalibrations_of_contextEquivalent {t u : ResponseTree ℝ}
    (h : ContextEquivalent harmonicTreeEnergy t u) : SameHarmonicCalibrations t u := by
  refine ⟨?_, ?_, ?_⟩
  · exact h (.forkLeft .hole (.leaf 0))
  · exact h (.forkLeft .hole (.leaf 1))
  · exact h (.forkLeft .hole (.leaf (-1)))

/-- Three fixed calibration responses classify the complete future-context response. -/
theorem sameHarmonicCalibrations_iff_contextEquivalent (t u : ResponseTree ℝ) :
    SameHarmonicCalibrations t u ↔ ContextEquivalent harmonicTreeEnergy t u := by
  constructor
  · exact fun h => contextEquivalent_harmonicTreeEnergy_of_sameMoments
      (sameMoments_of_sameHarmonicCalibrations h)
  · exact sameHarmonicCalibrations_of_contextEquivalent

/-- Equivalent classification by formed population, endpoint, and positive square mass. -/
theorem contextEquivalent_harmonicTreeEnergy_iff_sameMoments (t u : ResponseTree ℝ) :
    ContextEquivalent harmonicTreeEnergy t u ↔ SameHarmonicMoments t u := by
  constructor
  · intro h
    exact sameMoments_of_sameHarmonicCalibrations
      (sameHarmonicCalibrations_of_contextEquivalent h)
  · exact contextEquivalent_harmonicTreeEnergy_of_sameMoments

/-- Exact nonnegative between-block energy forced by binary fusion. -/
theorem harmonicTreeEnergy_fork (t u : ResponseTree ℝ) :
    harmonicTreeEnergy (.fork t u) = harmonicTreeEnergy t + harmonicTreeEnergy u +
      (((harmonicTreeCount u : ℝ) * harmonicTreeSum t -
          (harmonicTreeCount t : ℝ) * harmonicTreeSum u) ^ (2 : ℕ)) /
        ((harmonicTreeCount t : ℝ) * harmonicTreeCount u *
          (harmonicTreeCount t + harmonicTreeCount u)) := by
  have htpos : (0 : ℝ) < harmonicTreeCount t := by exact_mod_cast harmonicTreeCount_pos t
  have hupos : (0 : ℝ) < harmonicTreeCount u := by exact_mod_cast harmonicTreeCount_pos u
  have ht : (harmonicTreeCount t : ℝ) ≠ 0 := ne_of_gt htpos
  have hu : (harmonicTreeCount u : ℝ) ≠ 0 := ne_of_gt hupos
  have htu : (harmonicTreeCount t : ℝ) + harmonicTreeCount u ≠ 0 :=
    ne_of_gt (add_pos htpos hupos)
  simp only [harmonicTreeEnergy, harmonicTreeCount_fork, harmonicTreeSum_fork,
    harmonicTreeSqMass_fork, Nat.cast_add]
  field_simp
  ring

theorem harmonicTreeEnergy_fusion_surplus_nonneg (t u : ResponseTree ℝ) :
    0 ≤ harmonicTreeEnergy (.fork t u) - harmonicTreeEnergy t - harmonicTreeEnergy u := by
  rw [harmonicTreeEnergy_fork]
  have htpos : (0 : ℝ) < harmonicTreeCount t := by exact_mod_cast harmonicTreeCount_pos t
  have hupos : (0 : ℝ) < harmonicTreeCount u := by exact_mod_cast harmonicTreeCount_pos u
  have hden : 0 < (harmonicTreeCount t : ℝ) * harmonicTreeCount u *
      (harmonicTreeCount t + harmonicTreeCount u) := by
    exact mul_pos (mul_pos htpos hupos) (add_pos htpos hupos)
  have hfrac : 0 ≤ (((harmonicTreeCount u : ℝ) * harmonicTreeSum t -
      (harmonicTreeCount t : ℝ) * harmonicTreeSum u) ^ (2 : ℕ)) /
      ((harmonicTreeCount t : ℝ) * harmonicTreeCount u *
        (harmonicTreeCount t + harmonicTreeCount u)) :=
    div_nonneg (sq_nonneg _) (le_of_lt hden)
  linarith

theorem harmonicTreeEnergy_fork_eq_add_iff (t u : ResponseTree ℝ) :
    harmonicTreeEnergy (.fork t u) = harmonicTreeEnergy t + harmonicTreeEnergy u ↔
      (harmonicTreeCount u : ℝ) * harmonicTreeSum t =
        (harmonicTreeCount t : ℝ) * harmonicTreeSum u := by
  rw [harmonicTreeEnergy_fork]
  have htpos : (0 : ℝ) < harmonicTreeCount t := by exact_mod_cast harmonicTreeCount_pos t
  have hupos : (0 : ℝ) < harmonicTreeCount u := by exact_mod_cast harmonicTreeCount_pos u
  have hden : (harmonicTreeCount t : ℝ) * harmonicTreeCount u *
      (harmonicTreeCount t + harmonicTreeCount u) ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos htpos hupos) (add_pos htpos hupos))
  constructor
  · intro h
    have hz : (((harmonicTreeCount u : ℝ) * harmonicTreeSum t -
        (harmonicTreeCount t : ℝ) * harmonicTreeSum u) ^ (2 : ℕ)) /
        ((harmonicTreeCount t : ℝ) * harmonicTreeCount u *
          (harmonicTreeCount t + harmonicTreeCount u)) = 0 := by linarith
    have hsquare : ((harmonicTreeCount u : ℝ) * harmonicTreeSum t -
        (harmonicTreeCount t : ℝ) * harmonicTreeSum u) ^ (2 : ℕ) = 0 :=
      (div_eq_zero_iff).mp hz |>.resolve_right hden
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro h
    rw [h, sub_self, zero_pow (by omega : 2 ≠ 0), zero_div, add_zero]

end

end GaloisForLFunctions.HTGeometry

