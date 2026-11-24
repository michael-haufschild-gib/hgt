import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.SplitMass

/-! # Which exterior preparations have a finite two-copy output -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Square summability of the unnormalized two-copy output. -/
def finiteSplit (v : MissingWave) (s : ℂ) : Prop := Summable (fun x => ‖split s v.val x‖^2)

/-- The domain is determined by the positive moment of the normalized occupation law. -/
theorem finiteSplit_iff_law (v : MissingWave) (s : ℂ) :
    finiteSplit v s ↔ Summable (fun k => shellMass s (number k)*occupationProbability v (number k)) := by
  constructor
  · rintro ⟨b,h⟩
    have hr : splitMassReading v s (b/‖v.val‖^2) := by
      rw [splitMassReading,div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v)))]
      exact h
    exact ((splitMassReading_iff v s _).mp hr).summable
  · rintro ⟨b,h⟩
    have ht : HasSum (fun x => ‖split s v.val x‖^2) (b*‖v.val‖^2) := (splitMassReading_iff v s b).mpr h
    exact ht.summable

theorem shellMass_zero_eq_inv_occupationWeight (k : ℕ) : shellMass 0 (number k) = (occupationWeight k)⁻¹ := by
  rw [shellMass,Complex.zero_re,mul_zero,sub_zero,one_mul,energy,
    Real.exp_log (show (0:ℝ) < (number k).val by exact_mod_cast (number k).pos),occupationWeight_eq,inv_inv]
  change ((k+1:ℕ):ℝ) = (k:ℝ)+1
  rw [Nat.cast_add,Nat.cast_one]

private theorem impossible_at_nonpositive (v : MissingWave) {s : ℂ} (hs : s.re ≤ 0) : ¬ finiteSplit v s := by
  intro hf
  apply (exteriorLaw v).property.2.2
  apply ((finiteSplit_iff_law v s).mp hf).of_nonneg_of_le
  · intro k
    exact div_nonneg ((exteriorLaw v).property.1 _) (occupationWeight_pos k).le
  · intro k
    have he := shellMass_antitone_re (s := 0) (t := s) hs (number k)
    rw [shellMass_zero_eq_inv_occupationWeight] at he
    change occupationProbability v (number k)/occupationWeight k ≤ _
    rw [div_eq_mul_inv,mul_comm]
    exact mul_le_mul_of_nonneg_right he ((exteriorLaw v).property.1 _)

private theorem finite_on_right (v : MissingWave) {s : ℂ} (hs : 1/2 ≤ s.re) : finiteSplit v s := by
  apply (finiteSplit_iff_law v s).mpr
  apply (occupationProbability_sum v).summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (Real.exp_pos _).le ((exteriorLaw v).property.1 _)
  · intro k
    have hi := shellMass_antitone_re (s := s) (t := ((1/2:ℝ):ℂ)) hs (number k)
    have hh : shellMass ((1/2:ℝ):ℂ) (number k) = 1 := by norm_num [shellMass]
    rw [hh] at hi
    exact mul_le_of_le_one_left ((exteriorLaw v).property.1 _) hi

/-- The split of the packet at t is square summable exactly when the real part of s+t exceeds one. -/
theorem packet_split_finite_iff (t : HeatVectorDomain) (s : ℂ) :
    Summable (fun x => ‖split s (packet t) x‖^2) ↔ 1 < s.re+t.val.re := by
  have he (n : ℕ+) : shellMass s n*‖packet t n‖^2 = ‖heat (s+t.val-1/2) n‖^2 := by
    simp only [shellMass,packet_apply,norm_heat,sq,← Real.exp_add,Complex.sub_re,Complex.add_re,
      Complex.div_ofNat_re,Complex.one_re]
    congr 1
    ring
  have hsum : Summable (fun x => ‖split s (packet t) x‖^2) ↔ Summable (fun n => shellMass s n*‖packet t n‖^2) :=
    exists_congr (fun r => split_hasSum_iff s (packet t) r)
  rw [hsum]
  simp_rw [he]
  rw [summable_heat_sq_iff,Complex.sub_re,Complex.add_re,Complex.div_ofNat_re,Complex.one_re]
  constructor <;> intro h <;> linarith only [h]

private def exteriorPacketAt (t : HeatVectorDomain) (h : t.val.re ≤ 1) : MissingWave :=
  ⟨packet t,fun hm => (not_lt_of_ge h) ((packet_in_range_iff t).mp hm)⟩

/-- The reciprocal packet detects the left endpoint of the union of all exterior split domains. -/
theorem exists_finiteSplit_iff (s : ℂ) : (∃ v : MissingWave, finiteSplit v s) ↔ 0 < s.re := by
  constructor
  · rintro ⟨v,h⟩
    exact lt_of_not_ge (fun hs => impossible_at_nonpositive v hs h)
  · intro hs
    let t : HeatVectorDomain := ⟨1,by norm_num⟩
    refine ⟨exteriorPacketAt t (by norm_num [t]),(packet_split_finite_iff t s).mpr ?_⟩
    change 1 < s.re+1
    linarith only [hs]

/-- The intersection of the split domains over all exterior waves is the closed right half-plane from the isometry line. -/
theorem forall_finiteSplit_iff (s : ℂ) : (∀ v : MissingWave, finiteSplit v s) ↔ 1/2 ≤ s.re := by
  refine ⟨fun hf => ?_,fun hs v => finite_on_right v hs⟩
  by_contra! hs
  have hp : 0 < s.re := (exists_finiteSplit_iff s).mp ⟨⟨reciprocalTail,reciprocalTail_outside⟩,hf _⟩
  let t : HeatVectorDomain := ⟨((1-s.re:ℝ):ℂ),by change 1/2 < 1-s.re; linarith only [hs]⟩
  have ht : t.val.re ≤ 1 := by change 1-s.re ≤ 1; linarith only [hp]
  have h := (packet_split_finite_iff t s).mp (hf (exteriorPacketAt t ht))
  change 1 < s.re+(1-s.re) at h
  linarith only [h]

#print axioms finiteSplit_iff_law
#print axioms shellMass_zero_eq_inv_occupationWeight
#print axioms packet_split_finite_iff
#print axioms exists_finiteSplit_iff
#print axioms forall_finiteSplit_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
