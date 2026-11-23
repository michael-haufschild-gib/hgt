import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.Tomography
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CompositionRigidity

/-! # Critical composition measured by vacuum references at the pole -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- The vacuum baseline and its two opposite real displacements determine the absolute squared norm. -/
def vacuumMass (v : MissingWave) := (poleScan v 0).mass 1

theorem vacuumMass_eq (v : MissingWave) : vacuumMass v = ‖v.val‖^2 := by
  have ha : occupationWeight 0 = 1 := by rw [occupationWeight_eq]; norm_num
  have hr : poleReading v = firstMoment v.val := by rw [poleReading,omissionPartition_pole,Complex.ofReal_re]
  rw [vacuumMass,← ha]
  exact poleScan_mass _ _ (by rw [ha,hr]; exact (missing_moments v).2.1.ne)

/-- Prepare an inserted wave with the physical complex heat amplitude. -/
def preparedInsertion (a : ℕ+) (v : MissingWave) (s : ℂ) : MissingWave :=
  ⟨heat s a • (insertMissing a v).val,fun h => (insertMissing a v).property (by
    have hc := (LinearMap.range criticalOperator.toLinearMap).smul_mem (heat s a)⁻¹ h
    simpa only [smul_smul,inv_mul_cancel₀ (show heat s a ≠ 0 from Complex.exp_ne_zero _),one_smul] using hc)⟩

theorem prepared_mass (a : ℕ+) (v : MissingWave) (s : ℂ) :
    vacuumMass (preparedInsertion a v s) = ‖heat s a‖^2*vacuumMass v := by
  rw [vacuumMass_eq,vacuumMass_eq]
  change ‖heat s a • insertWave a v.val‖^2 = _
  rw [norm_smul,LinearIsometry.norm_map,mul_pow]

/-- Vacuum mass balance for one prime occupation is equivalent to isometry of the whole splitting map. -/
theorem vacuum_pole_balance (p : Nat.Primes) (v : MissingWave) (s : ℂ) :
    let a : ℕ+ := ⟨(p:ℕ),p.property.pos⟩
    (a.val:ℝ)*vacuumMass (preparedInsertion a v s) = vacuumMass v ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  let a : ℕ+ := ⟨(p:ℕ),p.property.pos⟩
  change (a.val:ℝ)*vacuumMass (preparedInsertion a v s) = _ ↔ _
  have he : energy a ≠ 0 := (Real.log_pos (show (1:ℝ) < a.val by exact_mod_cast p.property.one_lt)).ne'
  have hM : vacuumMass v ≠ 0 := by rw [vacuumMass_eq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v))
  rw [prepared_mass,← mul_assoc,← shellMass_eq,split_isometric_iff]
  constructor
  · intro h
    have hm := mul_right_cancel₀ hM (h.trans (one_mul _).symm)
    have hx := (mul_eq_zero.mp ((Real.exp_eq_one_iff _).mp hm)).resolve_right he
    linarith only [hx]
  · intro h
    simp only [shellMass,h]
    norm_num

def poleAtLabel (v : MissingWave) (n : ℕ+) := poleCoordinate v (Equiv.pnatEquivNat n)

theorem poleAtLabel_eq (v : MissingWave) (n : ℕ+) : poleAtLabel v n = v.val n := by
  rw [poleAtLabel,poleCoordinate_eq]
  exact congrArg (fun i => v.val i) (Equiv.pnatEquivNat.symm_apply_apply n)

private theorem exists_nonzero_poleCoordinate (v : MissingWave) : ∃ n, poleCoordinate v n ≠ 0 := by
  by_contra! h
  apply missingWave_ne_zero v
  apply lp.ext
  funext n
  obtain ⟨k,rfl⟩ := number_surjective n
  exact (poleCoordinate_eq v k).symm.trans (h k)

/-- First occupied label chosen directly from the pole measurements. -/
noncomputable def firstPoleLabel (v : MissingWave) : ℕ+ := by
  classical
  exact number (Nat.find (exists_nonzero_poleCoordinate v))

private theorem firstPoleLabel_ne (v : MissingWave) : v.val (firstPoleLabel v) ≠ 0 := by
  classical
  unfold firstPoleLabel
  rw [← poleCoordinate_eq]
  exact Nat.find_spec (exists_nonzero_poleCoordinate v)

/-- Complex amplitude from the two measured waves at their corresponding occupied coordinates. -/
def poleInsertionAmplitude (a : ℕ+) (v : MissingWave) (s : ℂ) :=
  poleAtLabel (preparedInsertion a v s) (a*firstPoleLabel v)/poleAtLabel v (firstPoleLabel v)

theorem poleInsertionAmplitude_eq (a : ℕ+) (v : MissingWave) (s : ℂ) :
    poleInsertionAmplitude a v s = heat s a := by
  rw [poleInsertionAmplitude,poleAtLabel_eq,poleAtLabel_eq]
  change (heat s a*insertWave a v.val (a*firstPoleLabel v))/v.val (firstPoleLabel v) = _
  rw [insertWave_at,mul_div_cancel_right₀ _ (firstPoleLabel_ne v)]

theorem two_pole_insertions_injective (v w : MissingWave) :
    Function.Injective (fun s : ℂ => (poleInsertionAmplitude 2 v s,poleInsertionAmplitude 3 w s)) := by
  simpa only [poleInsertionAmplitude_eq] using two_prime_heat_injective

#print axioms vacuumMass_eq
#print axioms prepared_mass
#print axioms vacuum_pole_balance
#print axioms poleAtLabel_eq
#print axioms poleInsertionAmplitude_eq
#print axioms two_pole_insertions_injective

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
