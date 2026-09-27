import GaloisForLFunctions.RHTower.XiGaussianNativeHeatCutoff

/-!
# No all-orders native energy retention over a fixed positive heat step

For every pair of fixed positive times `s < t`, native unit polynomials at
`s` can have arbitrarily small native energy at every time after `t`.
The construction lies in any prescribed nonzero polynomial principal ideal,
so exact polar cancellation does not remove it. The complete arithmetic
source and every mixed term against the native unit ball at each later time
are small on the same heat half-line.

This disproves an energy-retention step that would turn an absolute heat
dissipation estimate into a relative phase bound. It does not disprove an
independent same-time phase bound or assert a negative Xi Hankel witness.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators Real
noncomputable section
namespace RHTower

/-- Degree-uniform heat retention fails even with any fixed nonzero polynomial
factor. Normalization is exact at the earlier positive time. -/
theorem exists_xiGaussian_principalIdeal_unit_heat_collapse
    (B : {B : Polynomial ℝ // B ≠ 0}) (s : {s : ℝ // 0 < s})
    (t : Set.Ioi (s : ℝ)) (ε : {ε : ℝ // 0 < ε}) :
    ∃ Q : Polynomial ℝ, B.1 ∣ Q ∧ xiGaussianNativeEnergy Q s = 1 ∧
      ∀ u : Set.Ici (t : ℝ),
        xiGaussianNativeEnergy Q
          (xiGaussianHeatAfter ⟨t, s.property.trans t.property⟩ u) < (ε : ℝ) := by
  classical
  let d : ℝ := (t : ℝ) - (s : ℝ)
  have hd : 0 < d := sub_pos.mpr t.property
  let R : ℝ := (1 - Real.log (ε : ℝ)) / d
  have he : Real.exp (-(d * R)) < (ε : ℝ) := by
    have harg : -(d * R) = Real.log (ε : ℝ) - 1 := by
      dsimp only [R]
      field_simp [hd.ne']
      ring
    rw [harg]
    calc
      _ < Real.exp (Real.log (ε : ℝ)) := Real.exp_lt_exp.mpr (by linarith)
      _ = _ := Real.exp_log ε.property
  let F := (finite_xiHeatShell R).toFinset
  let A := B.1 * xiGaussianAnnihilator F
  have hAnn : xiGaussianAnnihilator F ≠ 0 := by
    intro h
    have hz := xiGaussianAnnihilator_zero F
    rw [h, Polynomial.eval_zero] at hz
    exact zero_ne_one hz
  have hA : A ≠ 0 := mul_ne_zero B.property hAnn
  have hK : 0 < xiGaussianNativeEnergy A s := xiGaussianNativeEnergy_pos ⟨A, hA⟩ s
  let c : ℝ := (Real.sqrt (xiGaussianNativeEnergy A s))⁻¹
  let Q := Polynomial.C c * A
  have hunit : xiGaussianNativeEnergy Q s = 1 := by
    rw [xiGaussianNativeEnergy_C_mul]
    dsimp only [c]
    rw [inv_pow, Real.sq_sqrt hK.le, inv_mul_cancel₀ hK.ne']
  let t₁ : {v : ℝ // 0 < v} := ⟨t, s.property.trans t.property⟩
  have hdecay : xiGaussianNativeEnergy Q t₁ ≤ Real.exp (-(d * R)) := by
    have h := mul_le_mul_of_nonneg_left
      (xiGaussianNativeEnergy_mul_shell_annihilator_heat_le B.1 R s
        ⟨t, show (s : ℝ) ≤ (t : ℝ) from le_of_lt t.property⟩) (sq_nonneg c)
    change c ^ 2 * xiGaussianNativeEnergy A t₁ ≤
      c ^ 2 * (Real.exp (-(d * R)) * xiGaussianNativeEnergy A s) at h
    calc
      _ = c ^ 2 * xiGaussianNativeEnergy A t₁ := xiGaussianNativeEnergy_C_mul c A t₁
      _ ≤ _ := h
      _ = Real.exp (-(d * R)) * xiGaussianNativeEnergy Q s := by
        rw [xiGaussianNativeEnergy_C_mul]
        ring
      _ = _ := by rw [hunit, mul_one]
  refine ⟨Q, dvd_mul_of_dvd_right (dvd_mul_right B.1 (xiGaussianAnnihilator F)) _, hunit, ?_⟩
  intro u
  exact ((xiGaussianNativeEnergy_antitone Q u.property).trans hdecay).trans_lt he

/-- Full prime--Gamma source and all mixed terms become small after the fixed
heat step while the test has native energy exactly one before it. -/
theorem exists_xiGaussian_principalIdeal_unit_heat_source_collapse
    (B : {B : Polynomial ℝ // B ≠ 0}) (s : {s : ℝ // 0 < s})
    (t : Set.Ioi (s : ℝ)) (ε : {ε : ℝ // 0 < ε}) :
    ∃ Q : Polynomial ℝ, B.1 ∣ Q ∧ xiGaussianNativeEnergy Q s = 1 ∧
      ∀ u : Set.Ici (t : ℝ),
        let v := xiGaussianHeatAfter ⟨t, s.property.trans t.property⟩ u
        xiGaussianNativeEnergy Q v < (ε : ℝ) ^ 2 ∧
        |xiGaussianCompletedSourceResidual Q v| < π * (ε : ℝ) ^ 2 ∧
        ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P v ≤ 1},
          |xiGaussianCompletedSourceResidual (P.1 + Q) v -
            xiGaussianCompletedSourceResidual P.1 v -
            xiGaussianCompletedSourceResidual Q v| < 2 * π * (ε : ℝ) * (1 + (ε : ℝ)) := by
  obtain ⟨Q, hBQ, hunit, hQ⟩ := exists_xiGaussian_principalIdeal_unit_heat_collapse
    B s t ⟨(ε : ℝ) ^ 2, sq_pos_of_pos ε.property⟩
  refine ⟨Q, hBQ, hunit, fun u => ⟨hQ u, ?_, ?_⟩⟩
  · exact (abs_xiGaussianCompletedSourceResidual_le_energy Q _).trans_lt
      (mul_lt_mul_of_pos_left (hQ u) Real.pi_pos)
  · intro P
    let v := xiGaussianHeatAfter ⟨t, s.property.trans t.property⟩ u
    have heP : (ε : ℝ) * xiGaussianNativeEnergy P.1 v ≤ (ε : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left P.property ε.property.le
    have hcoef : 0 < 2 + 1 / (ε : ℝ) := by have he := ε.property; positivity
    have heQ := mul_lt_mul_of_pos_left (hQ u) hcoef
    have halg : (ε : ℝ) + (2 + 1 / (ε : ℝ)) * (ε : ℝ) ^ 2 =
        2 * (ε : ℝ) * (1 + (ε : ℝ)) := by
      field_simp [ε.property.ne']
      ring
    calc
      _ ≤ |xiGaussianCompletedSourceResidual (P.1 + Q) v -
            xiGaussianCompletedSourceResidual P.1 v| +
          |xiGaussianCompletedSourceResidual Q v| := abs_sub _ _
      _ ≤ π * ((ε : ℝ) * xiGaussianNativeEnergy P.1 v +
            (1 + 1 / (ε : ℝ)) * xiGaussianNativeEnergy Q v) +
          π * xiGaussianNativeEnergy Q v :=
        add_le_add (abs_xiGaussianCompletedSourceResidual_add_sub_le P.1 Q v ε)
          (abs_xiGaussianCompletedSourceResidual_le_energy Q v)
      _ = π * ((ε : ℝ) * xiGaussianNativeEnergy P.1 v +
          (2 + 1 / (ε : ℝ)) * xiGaussianNativeEnergy Q v) := by ring
      _ < π * ((ε : ℝ) + (2 + 1 / (ε : ℝ)) * (ε : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left (add_lt_add_of_le_of_lt heP heQ) Real.pi_pos
      _ = _ := by rw [halg]; ring

/-- Exact pole cancellation leaves the normalized fixed-step collapse and
every mixed source bound intact. -/
theorem exists_xiGaussian_poleFree_unit_heat_source_collapse
    (s : {s : ℝ // 0 < s}) (t : Set.Ioi (s : ℝ)) (ε : {ε : ℝ // 0 < ε}) :
    ∃ Q : Polynomial ℝ, Q.eval (-(1 / 4 : ℝ)) = 0 ∧ xiGaussianNativeEnergy Q s = 1 ∧
      ∀ u : Set.Ici (t : ℝ),
        let v := xiGaussianHeatAfter ⟨t, s.property.trans t.property⟩ u
        xiGaussianNativeEnergy Q v < (ε : ℝ) ^ 2 ∧
        |xiGaussianCompletedSourceResidual Q v| < π * (ε : ℝ) ^ 2 ∧
        ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P v ≤ 1},
          |xiGaussianCompletedSourceResidual (P.1 + Q) v -
            xiGaussianCompletedSourceResidual P.1 v -
            xiGaussianCompletedSourceResidual Q v| < 2 * π * (ε : ℝ) * (1 + (ε : ℝ)) := by
  obtain ⟨Q, ⟨D, hD⟩, hunit, hQ⟩ := exists_xiGaussian_principalIdeal_unit_heat_source_collapse
    ⟨Polynomial.X + Polynomial.C (1 / 4 : ℝ), Polynomial.X_add_C_ne_zero _⟩ s t ε
  refine ⟨Q, ?_, hunit, hQ⟩
  rw [hD]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, neg_add_cancel, zero_mul]

/-- No finite constant compares earlier native energy with later native
energy across all polynomial orders, even in any nonzero principal ideal. -/
theorem not_xiGaussian_principalIdeal_heat_inverse_bound
    (B : {B : Polynomial ℝ // B ≠ 0}) (s : {s : ℝ // 0 < s}) (t : Set.Ioi (s : ℝ)) :
    ¬ ∃ C : ℝ, ∀ P : {P : Polynomial ℝ // B.1 ∣ P},
      xiGaussianNativeEnergy P s ≤ C * xiGaussianNativeEnergy P
        ⟨t, s.property.trans t.property⟩ := by
  rintro ⟨C, hC⟩
  have hc : 0 < |C| + 1 := by positivity
  obtain ⟨Q, hBQ, hunit, hQ⟩ := exists_xiGaussian_principalIdeal_unit_heat_collapse
    B s t ⟨1 / (|C| + 1), one_div_pos.mpr hc⟩
  have hsmall := mul_lt_mul_of_pos_left
    (hQ ⟨t, show (t : ℝ) ≤ (t : ℝ) from le_rfl⟩) hc
  have hone : (|C| + 1) * (1 / (|C| + 1)) = 1 := by field_simp
  rw [hone] at hsmall
  have hb := hC ⟨Q, hBQ⟩
  rw [hunit] at hb
  have hle := mul_le_mul_of_nonneg_right
    (show C ≤ |C| + 1 by linarith [le_abs_self C])
    (xiGaussianNativeEnergy_nonneg Q ⟨t, s.property.trans t.property⟩)
  exact (not_lt_of_ge (hb.trans hle)) hsmall

/-- Native dissipation cannot be absorbed with any degree-independent
constant into the energy remaining at the target heat time. -/
theorem not_xiGaussian_principalIdeal_relative_dissipation_bound
    (B : {B : Polynomial ℝ // B ≠ 0}) (s : {s : ℝ // 0 < s}) (t : Set.Ioi (s : ℝ)) :
    ¬ ∃ C : ℝ, ∀ P : {P : Polynomial ℝ // B.1 ∣ P},
      xiGaussianNativeEnergy P s - xiGaussianNativeEnergy P ⟨t, s.property.trans t.property⟩ ≤
        C * xiGaussianNativeEnergy P ⟨t, s.property.trans t.property⟩ := by
  rintro ⟨C, hC⟩
  apply not_xiGaussian_principalIdeal_heat_inverse_bound B s t
  exact ⟨C + 1, fun P => by linarith [hC P]⟩

/-- Absolute value of the later complete signed arithmetic source cannot
recover the earlier native energy with a degree-independent constant. -/
theorem not_xiGaussian_principalIdeal_heat_source_inverse_bound
    (B : {B : Polynomial ℝ // B ≠ 0}) (s : {s : ℝ // 0 < s}) (t : Set.Ioi (s : ℝ)) :
    ¬ ∃ C : ℝ, ∀ P : {P : Polynomial ℝ // B.1 ∣ P},
      xiGaussianNativeEnergy P s ≤
        C * |xiGaussianCompletedSourceResidual P ⟨t, s.property.trans t.property⟩| := by
  rintro ⟨C, hC⟩
  apply not_xiGaussian_principalIdeal_heat_inverse_bound B s t
  refine ⟨|C| * π, fun P => (hC P).trans ?_⟩
  calc
    _ ≤ |C| * |xiGaussianCompletedSourceResidual P ⟨t, s.property.trans t.property⟩| :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
    _ ≤ |C| * (π * xiGaussianNativeEnergy P ⟨t, s.property.trans t.property⟩) :=
      mul_le_mul_of_nonneg_left (abs_xiGaussianCompletedSourceResidual_le_energy P _)
        (abs_nonneg C)
    _ = _ := (mul_assoc _ _ _).symm

end RHTower
