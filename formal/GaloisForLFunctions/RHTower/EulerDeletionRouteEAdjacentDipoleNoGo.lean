import GaloisForLFunctions.RHTower.EulerDeletionNestedProjectionCovariance
import GaloisForLFunctions.RHTower.MobiusGammaHankelMultiplierCollapse

/-!
# Adjacent modular wrap obstructs coefficient-blind Route E to EDQ transfer

The same adjacent signed atoms have additive Gamma--Hankel energy of order
`m⁻³` but physical residue energy at least of order `m⁻²`. Thus no uniform
quadratic comparison can move Route E's finite energy into the EDQ source
without paying a modular jump cost or using the actual Möbius signs.
-/

noncomputable section
open MeasureTheory
namespace RHTower
open DeletionResidueMartingale

private theorem adjacent_single_cell_le_norm_sq (v : Lp ℝ 2 cellMeasure) (j : ℕ) :
    v j ^ (2 : ℕ) * cellWeight j ≤ ‖v‖ ^ (2 : ℕ) := by
  have hi : Integrable (fun x => v x ^ (2 : ℕ)) cellMeasure := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hind : Integrable (({j} : Set ℕ).indicator (fun x => v x ^ (2 : ℕ))) cellMeasure :=
    hi.indicator (measurableSet_singleton _)
  calc
    v j ^ (2 : ℕ) * cellWeight j = ∫ x in {j}, v x ^ (2 : ℕ) ∂cellMeasure := by
      rw [integral_singleton, cellMeasure_singleton]
      simp only [smul_eq_mul]
      ring
    _ = ∫ x, ({j} : Set ℕ).indicator (fun x => v x ^ (2 : ℕ)) x ∂cellMeasure := by
      exact (integral_indicator (measurableSet_singleton _)).symm
    _ ≤ ∫ x, v x ^ (2 : ℕ) ∂cellMeasure := by
      apply integral_mono_ae hind hi
      filter_upwards with x
      by_cases hx : x = j
      · subst x
        simp
      · simp [hx, sq_nonneg]
    _ = ‖v‖ ^ (2 : ℕ) := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

private theorem adjacent_dipole_apply (m : ℕ) (hm : 0 < m) :
    (residueVec m - residueVec (m + 1)) (m - 1) = -(m : ℝ) / (m + 1 : ℝ) := by
  have hj : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hsub := Lp.coeFn_sub (residueVec m) (residueVec (m + 1))
  have hpoint :
      (residueVec m - residueVec (m + 1)) (m - 1) =
        residueVec m (m - 1) - residueVec (m + 1) (m - 1) := by
    exact (ae_iff_of_countable.mp hsub) (m - 1) (by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      change ENNReal.ofReal (cellWeight (m - 1)) ≠ 0
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by unfold cellWeight; positivity)))
  rw [hpoint, residueVec_apply_eq_residue, residueVec_apply_eq_residue]
  simp [residue, hj, Nat.mod_eq_of_lt (by omega : m < m + 1)]
  ring

/-- One physical wrap cell gives the exact `m⁻²`-scale lower bound for the
adjacent residue dipole. -/
theorem adjacent_dipole_norm_lower (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / ((m + 1 : ℝ) ^ (3 : ℕ)) ≤
      ‖residueVec m - residueVec (m + 1)‖ ^ (2 : ℕ) := by
  have h := adjacent_single_cell_le_norm_sq
    (residueVec m - residueVec (m + 1)) (m - 1)
  rw [adjacent_dipole_apply m hm] at h
  have hj : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hj2 : m - 1 + 2 = m + 1 := by omega
  have hjR : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hj
  have hjR2 : ((m - 1 : ℕ) : ℝ) + 2 = (m : ℝ) + 1 := by exact_mod_cast hj2
  unfold cellWeight at h
  rw [hjR, hjR2] at h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmR1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  convert h using 1
  field_simp

/-- The existing additive dipole estimate has `m⁻³` decay at critical order. -/
theorem adjacent_hankel_upper (m : ℕ) (hm : 0 < m) :
    finiteGammaHankelEnergy (gammaHankelDipole (m - 1) m) (m + 1) 1 ≤
      1 / (4 * (m : ℝ) ^ (3 : ℕ)) := by
  have h := gammaHankelDipole_energy_le
    (i := m - 1) (j := m) (N := m + 1)
    (by omega) (by omega) (by omega) (r := (1 : ℝ)) (by norm_num)
  have hgamma : Real.Gamma (3 : ℝ) = 2 := by norm_num
  simp only [Nat.sub_add_cancel hm] at h
  norm_num [hgamma] at h ⊢
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  convert h using 1
  field_simp [hmR]
  norm_num

/-- Quantitative obstruction: already on two adjacent atoms, the physical
residue energy exceeds `m` times the critical additive Hankel energy. -/
theorem adjacent_dipole_linear_gap (m : ℕ) (hm2 : 2 ≤ m) :
    (m : ℝ) * finiteGammaHankelEnergy
      (gammaHankelDipole (m - 1) m) (m + 1) 1 <
        ‖residueVec m - residueVec (m + 1)‖ ^ (2 : ℕ) := by
  have hm : 0 < m := by omega
  have hH := adjacent_hankel_upper m hm
  have hP := adjacent_dipole_norm_lower m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hkey : (m : ℝ) * (1 / (4 * (m : ℝ) ^ (3 : ℕ))) <
      (m : ℝ) / ((m + 1 : ℝ) ^ (3 : ℕ)) := by
    have hle : (m : ℝ) + 1 ≤ (3 / 2 : ℝ) * m := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m + 1) hle 3
    have hbound : ((m : ℝ) + 1) ^ (3 : ℕ) < 4 * (m : ℝ) ^ (3 : ℕ) := by
      nlinarith [hpow, pow_pos hmR 3]
    rw [mul_one_div]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    exact mul_lt_mul_of_pos_left hbound hmR
  exact (mul_le_mul_of_nonneg_left hH hmR.le).trans_lt (hkey.trans_le hP)

private theorem exists_adjacent_edq_gamma_hankel_gap (C : ℝ) :
    ∃ m : ℕ, 0 < m ∧
      C * finiteGammaHankelEnergy (gammaHankelDipole (m - 1) m) (m + 1) 1 <
        ‖residueVec m - residueVec (m + 1)‖ ^ (2 : ℕ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt C
  let m := n + 2
  have hm : 0 < m := by dsimp [m]; omega
  have hm2 : 2 ≤ m := by dsimp [m]; omega
  have hmC : C ≤ (m : ℝ) := by dsimp [m]; push_cast; linarith
  refine ⟨m, hm, ?_⟩
  have hG : 0 ≤ finiteGammaHankelEnergy
      (gammaHankelDipole (m - 1) m) (m + 1) 1 :=
    finiteGammaHankelEnergy_nonneg _ _ (by norm_num)
  exact (mul_le_mul_of_nonneg_right hmC hG).trans_lt (adjacent_dipole_linear_gap m hm2)

/-- No coefficient-independent constant transfers critical additive Gamma--Hankel
energy to physical residue energy: adjacent dipoles have a modular wrap jump
of order `m⁻²`, while their additive Hankel energy is order `m⁻³`. -/
theorem no_uniform_adjacent_edq_gamma_hankel_domination :
    ¬ ∃ C : ℝ, ∀ m : ℕ, 0 < m →
      ‖residueVec m - residueVec (m + 1)‖ ^ (2 : ℕ) ≤
        C * finiteGammaHankelEnergy
          (gammaHankelDipole (m - 1) m) (m + 1) 1 := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm, hgap⟩ :=
    exists_adjacent_edq_gamma_hankel_gap (max C 0)
  have hG : 0 ≤ finiteGammaHankelEnergy
      (gammaHankelDipole (m - 1) m) (m + 1) 1 :=
    finiteGammaHankelEnergy_nonneg _ _ (by norm_num)
  have hfactor : C * finiteGammaHankelEnergy
      (gammaHankelDipole (m - 1) m) (m + 1) 1 ≤
        max C 0 * finiteGammaHankelEnergy
          (gammaHankelDipole (m - 1) m) (m + 1) 1 :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) hG
  exact (not_lt_of_ge ((hC m hm).trans hfactor)) hgap

end RHTower
