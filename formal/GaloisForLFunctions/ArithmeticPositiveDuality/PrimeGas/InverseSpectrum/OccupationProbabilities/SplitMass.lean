import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.LawClassification

/-! # The global composition line from the split of one exterior wave -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Squared output norm in units of the squared input norm. Existence of a reading includes square summability. -/
def splitMassReading (v : MissingWave) (s : ℂ) (r : ℝ) : Prop :=
  HasSum (fun x => ‖split s v.val x‖^2) (r*‖v.val‖^2)

theorem splitMassReading_iff (v : MissingWave) (s : ℂ) (r : ℝ) :
    splitMassReading v s r ↔ HasSum (fun k => shellMass s (number k)*occupationProbability v (number k)) r := by
  have hM := pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v))
  rw [splitMassReading,split_hasSum_iff,← Equiv.pnatEquivNat.symm.hasSum_iff]
  change HasSum (fun k => shellMass s (number k)*‖v.val (number k)‖^2) (r*‖v.val‖^2) ↔ _
  constructor
  · intro h
    have ht := h.div_const (‖v.val‖^2)
    rw [mul_div_cancel_right₀ _ hM] at ht
    simpa only [occupationProbability,mul_div_assoc] using ht
  · intro h
    have he (k : ℕ) : shellMass s (number k)*occupationProbability v (number k)*‖v.val‖^2 =
        shellMass s (number k)*‖v.val (number k)‖^2 := by
      rw [mul_assoc,occupationProbability,div_mul_cancel₀ _ hM]
    exact (congrArg (fun f : ℕ → ℝ => HasSum f (r*‖v.val‖^2)) (funext he)).mp (h.mul_right _)

/-- A relative partition germ determines both the domain and the normalized norm of every divisor split. -/
theorem splitMassReading_of_germ {v w : MissingWave} {z : ℂ} (hz : 0 < z.re)
    (hg : omissionPartition v =ᶠ[𝓝 z] omissionPartition w) (s : ℂ) (r : ℝ) :
    splitMassReading v s r ↔ splitMassReading w s r := by
  rw [splitMassReading_iff,splitMassReading_iff,(omission_germ_iff_probability v w hz).mp hg]

private theorem nonvacuum_probability (v : MissingWave) :
    ∃ k : ℕ, 0 < k ∧ 0 < occupationProbability v (number k) := by
  by_contra! h
  apply (exteriorLaw v).property.2.2
  apply (occupationProbability_sum v).summable.congr
  intro k
  change occupationProbability v (number k) = occupationProbability v (number k)/occupationWeight k
  by_cases hk : k = 0
  · subst k
    rw [occupationWeight_eq]
    norm_num
  · have hz := le_antisymm (h k (Nat.pos_of_ne_zero hk)) ((exteriorLaw v).property.1 (number k))
    rw [hz,zero_div]

theorem shellMass_antitone_re {s t : ℂ} (h : t.re ≤ s.re) (n : ℕ+) :
    shellMass s n ≤ shellMass t n :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [h])
    (Real.log_nonneg (show (1:ℝ) ≤ n.val by exact_mod_cast n.pos)))

private theorem shellMass_strict {s t : ℂ} (h : t.re < s.re) {k : ℕ} (hk : 0 < k) :
    shellMass s (number k) < shellMass t (number k) := by
  have he : 0 < energy (number k) := Real.log_pos (by
    change (1:ℝ) < ((k+1:ℕ):ℝ)
    exact_mod_cast (show 1 < k+1 by omega))
  exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right (by linarith only [h]) he)

/-- A nonvacuum occupied label makes the split mass strictly decreasing wherever both readings exist. -/
theorem splitMassReading_strict {v : MissingWave} {s t : ℂ} {r u : ℝ} (h : t.re < s.re)
    (hs : splitMassReading v s r) (ht : splitMassReading v t u) : r < u := by
  obtain ⟨k,hk,hp⟩ := nonvacuum_probability v
  have h₁ := (splitMassReading_iff v s r).mp hs
  have h₂ := (splitMassReading_iff v t u).mp ht
  rw [← h₁.tsum_eq,← h₂.tsum_eq]
  exact Summable.tsum_lt_tsum_of_nonneg
    (fun n => mul_nonneg (Real.exp_pos _).le ((exteriorLaw v).property.1 (number n)))
    (fun n => mul_le_mul_of_nonneg_right (shellMass_antitone_re h.le _) ((exteriorLaw v).property.1 _))
    (mul_lt_mul_of_pos_right (shellMass_strict h hk) hp) h₂.summable

private theorem critical_reading (v : MissingWave) {s : ℂ} (h : s.re = 1/2) : splitMassReading v s 1 := by
  apply (splitMassReading_iff v s 1).mpr
  have he (n : ℕ+) : shellMass s n = 1 := by simp [shellMass,h]
  simpa only [he,one_mul] using occupationProbability_sum v

/-- Norm conservation on any single exterior wave is equivalent to isometry on all waves. -/
theorem one_wave_split_isometric (v : MissingWave) (s : ℂ) :
    splitMassReading v s 1 ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  refine ⟨fun hs => ?_,critical_reading v⟩
  let t : ℂ := ((1/2:ℝ):ℂ)
  have ht : t.re = 1/2 := rfl
  have hc := critical_reading v ht
  rcases lt_trichotomy s.re t.re with h|h|h
  · exact ((lt_irrefl (1:ℝ)) (splitMassReading_strict h hc hs)).elim
  · exact h.trans ht
  · exact ((lt_irrefl (1:ℝ)) (splitMassReading_strict h hs hc)).elim

#print axioms splitMassReading_iff
#print axioms splitMassReading_of_germ
#print axioms shellMass_antitone_re
#print axioms splitMassReading_strict
#print axioms one_wave_split_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
