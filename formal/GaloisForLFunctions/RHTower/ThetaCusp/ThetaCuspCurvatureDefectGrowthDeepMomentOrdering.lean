import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthStableComponents
/-!
# All-order normalized deep-tail moment dominance

Normalized moments of the literal point-and-ray atom increase with its
spectral gap. Exact countable summation transfers this order to the full
source and its deep tail. Positive-measure Chebyshev then gives the
all-order coupled bound D_i*M_j <= M_0*D_(i+j), preserving a deep factor
without a separate D_0*M_j error. This supplies a stronger input for the
remaining higher mixed-sector absorption; no complete source sign follows.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

theorem bareMoment_zero_formula (q d : ℝ) :
    bareMoment q d 0=d+1+(3/2)*d/q := by
  norm_num [bareMoment,div_eq_mul_inv]

def barePositiveMomentTail (q d : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j,
    (j.choose (i+1):ℝ)*d^(j-(i+1))*((i+1).factorial:ℝ)/q^(i+2)

theorem bareMoment_positive_tail_decomposition (q d : ℝ) (j : ℕ) :
    bareMoment q d j=bareMoment q d 0*d^j+(3/2)*d*barePositiveMomentTail q d j := by
  rw [bareMoment,bareMoment_zero_formula,Finset.sum_range_succ']
  unfold barePositiveMomentTail
  simp only [Nat.choose_zero_right,Nat.sub_zero,Nat.factorial_zero,Nat.cast_one,
    Nat.zero_add,pow_one,mul_one,one_mul,Nat.add_assoc]
  ring

theorem bareMoment_zero_pos {q d : ℝ} (hq : 0 < q) (hd : 0 ≤ d) :
    0 < bareMoment q d 0 := by
  rw [bareMoment_zero_formula]
  positivity

theorem bareMoment_mass_gap_cross (q a d : ℝ) :
    bareMoment q a 0*d-bareMoment q d 0*a=d-a := by
  rw [bareMoment_zero_formula,bareMoment_zero_formula]
  ring

theorem bareMoment_normalized_order {q a d : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (had : a ≤ d) (j : ℕ) :
    bareMoment q d 0*bareMoment q a j ≤ bareMoment q a 0*bareMoment q d j := by
  have hd : 0 ≤ d := ha.trans had
  have hma := bareMoment_zero_pos hq ha
  have hmd := bareMoment_zero_pos hq hd
  have hbase : bareMoment q d 0*a ≤ bareMoment q a 0*d := by
    have h := bareMoment_mass_gap_cross q a d
    linarith
  have hpower (r : ℕ) : bareMoment q d 0*a*a^r ≤ bareMoment q a 0*d*d^r := by
    calc
      _ ≤ bareMoment q a 0*d*a^r := mul_le_mul_of_nonneg_right hbase (pow_nonneg ha r)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha had r) (mul_nonneg hma.le hd)
  have htail : bareMoment q d 0*a*barePositiveMomentTail q a j ≤
      bareMoment q a 0*d*barePositiveMomentTail q d j := by
    unfold barePositiveMomentTail
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hc : 0 ≤ (j.choose (i+1):ℝ)*((i+1).factorial:ℝ)/q^(i+2) := by positivity
    have h := mul_le_mul_of_nonneg_left (hpower (j-(i+1))) hc
    convert! h using 1 <;> ring
  have hfirst := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha had j) (mul_nonneg hma.le hmd.le)
  rw [bareMoment_positive_tail_decomposition q a j,bareMoment_positive_tail_decomposition q d j]
  nlinarith only [htail,hfirst]


open MeasureTheory Filter Set

theorem atomMoment_dominant_normalized_order {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) (j : ℕ) :
    atomMoment 2 q j*atomMoment n q 0 ≤ atomMoment 2 q 0*atomMoment n q j := by
  have hg : 3 ≤ thetaCuspLikelihoodGap n := by
    have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    unfold thetaCuspLikelihoodGap
    nlinarith [sq_nonneg ((n:ℝ)-2)]
  let c := Real.exp (-(3/2)*thetaCuspLikelihoodGap n)*Real.exp (-q*thetaCuspLikelihoodGap n)*
    (thetaCuspLikelihoodGap n+1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have h := mul_le_mul_of_nonneg_left (bareMoment_normalized_order hq (by norm_num : (0:ℝ) ≤ 3) hg j)
    (mul_nonneg (dominantAtomScale_pos q).le hc)
  have htwo (k : ℕ) : atomMoment 2 q k=dominantAtomScale q*bareMoment q 3 k := by
    have hg2 : thetaCuspLikelihoodGap 2=(3:ℝ) := by norm_num [thetaCuspLikelihoodGap]
    rw [atomMoment_eq_bare (by omega : 2 ≤ (2:ℕ)) hq,hg2]
    unfold dominantAtomScale
    rw [show -(3/2)*(3:ℝ)=-(9/2) by ring,show -q*(3:ℝ)=-3*q by ring]
    ring
  rw [htwo j,htwo 0,atomMoment_eq_bare hn hq 0,atomMoment_eq_bare hn hq j]
  convert! h using 1 <;> (dsimp only [c]; ring)

theorem fullMoment_dominant_normalized_order {q : ℝ} (hq : 0 < q) (j : ℕ) :
    atomMoment 2 q j*thetaCuspHigherLikelihoodSpectralMoment q 0 ≤
      atomMoment 2 q 0*thetaCuspHigherLikelihoodSpectralMoment q j := by
  exact hasSum_le (fun n => atomMoment_dominant_normalized_order (by omega) hq j)
    ((hasSum_atomMoment hq 0).mul_left _) ((hasSum_atomMoment hq j).mul_left _)

theorem fullMoment_eq_atom_add_deep {q : ℝ} (hq : 0 < q) (j : ℕ) :
    thetaCuspHigherLikelihoodSpectralMoment q j=atomMoment 2 q j+thetaCuspDeepTailMoment q j := by
  simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
    thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hq j

theorem deepMoment_dominant_normalized_order {q : ℝ} (hq : 0 < q) (j : ℕ) :
    thetaCuspDeepTailMoment q 0*atomMoment 2 q j ≤
      atomMoment 2 q 0*thetaCuspDeepTailMoment q j := by
  have h := fullMoment_dominant_normalized_order hq j
  rw [fullMoment_eq_atom_add_deep hq 0,fullMoment_eq_atom_add_deep hq j] at h
  nlinarith only [h]

theorem deepMoment_source_normalized_order {q : ℝ} (hq : 0 < q) (j : ℕ) :
    thetaCuspDeepTailMoment q 0*thetaCuspHigherLikelihoodSpectralMoment q j ≤
      thetaCuspHigherLikelihoodSpectralMoment q 0*thetaCuspDeepTailMoment q j := by
  have h := deepMoment_dominant_normalized_order hq j
  rw [fullMoment_eq_atom_add_deep hq 0,fullMoment_eq_atom_add_deep hq j]
  nlinarith only [h]

theorem deepMoment_zero_pos {q : ℝ} (hq : 0 < q) : 0 < thetaCuspDeepTailMoment q 0 := by
  have hle : thetaCuspAtomLikelihoodSpectralMeasure 3 ≤ thetaCuspDeepTailSpectralMeasure := by
    simpa only [Nat.zero_add,thetaCuspDeepTailSpectralMeasure] using
      Measure.le_sum (fun n : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (n+3)) 0
  have hn : 0 ≤ᵐ[thetaCuspDeepTailSpectralMeasure] (fun t : ℝ => t^0*Real.exp (-q*t)) := by
    filter_upwards with t
    positivity
  have h := integral_mono_measure hle hn
    (integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure 0 hq)
  have hcmp : atomMoment 3 q 0 ≤ thetaCuspDeepTailMoment q 0 := by
    simpa only [atomMoment,thetaCuspDeepTailMoment,neg_mul] using h
  have ha : 0 < atomMoment 3 q 0 := by
    rw [atomMoment_eq_bare (by omega : 2 ≤ (3:ℕ)) hq 0]
    have hg : thetaCuspLikelihoodGap 3=(8:ℝ) := by norm_num [thetaCuspLikelihoodGap]
    rw [hg]
    have hb := bareMoment_zero_pos hq (by norm_num : (0:ℝ) ≤ 8)
    positivity
  exact ha.trans_le hcmp

theorem deepMoment_mul_le_mass_mul {q : ℝ} (hq : 0 < q) (i j : ℕ) :
    thetaCuspDeepTailMoment q i*thetaCuspDeepTailMoment q j ≤
      thetaCuspDeepTailMoment q 0*thetaCuspDeepTailMoment q (i+j) := by
  let μ := componentTilt q thetaCuspDeepTailSpectralMeasure
  have hi (r : ℕ) : Integrable (fun t : ℝ => t^r) μ :=
    integrable_pow_componentTilt q _ (fun r => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure r hq) r
  letI : IsFiniteMeasure μ :=
    componentTilt_finite q _ (fun r => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure r hq)
  have hμ : ∀ᵐ t ∂μ, 0 ≤ t := by
    apply ae_lower_componentTilt
    filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
    linarith
  have hprod : ∀ᵐ z : ℝ×ℝ ∂μ.prod μ, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hμ] with s hs
    filter_upwards [hμ] with t ht
    exact ⟨hs,ht⟩
  have hkernel : ∀ᵐ z : ℝ×ℝ ∂μ.prod μ,
      0 ≤ (z.2^j-z.1^j)*(z.2^i-z.1^i) := by
    filter_upwards [hprod] with z hz
    rcases le_total z.1 z.2 with hxy | hyx
    · exact mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hz.1 hxy j))
        (sub_nonneg.mpr (pow_le_pow_left₀ hz.1 hxy i))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ hz.2 hyx j))
        (sub_nonpos.mpr (pow_le_pow_left₀ hz.2 hyx i))
  have h := HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel
    (μ := μ) (f := fun t : ℝ => t^i) (h := fun _ : ℝ => (1:ℝ)) (g := fun t : ℝ => t^j)
    (hi i) (by simpa only [pow_zero] using hi 0)
    (by simpa only [←pow_add,add_comm] using hi (i+j))
    (by simpa only [mul_one] using hi j) (by simpa only [one_mul] using hkernel)
  change (∫ t, t^j*1 ∂μ)*(∫ t, t^i ∂μ) ≤ (∫ t, t^j*t^i ∂μ)*(∫ t, (1:ℝ) ∂μ) at h
  simp only [mul_one,←pow_add] at h
  have hm (r : ℕ) : measureMoment μ r=thetaCuspDeepTailMoment q r := by
    exact measureMoment_componentTilt q thetaCuspDeepTailSpectralMeasure r
  have he : measureMoment μ i*measureMoment μ j ≤ measureMoment μ 0*measureMoment μ (i+j) := by
    simpa only [measureMoment,pow_zero,add_comm,mul_comm] using h
  simpa only [hm] using he

theorem deepMoment_mul_source_le {q : ℝ} (hq : 0 < q) (i j : ℕ) :
    thetaCuspDeepTailMoment q i*thetaCuspHigherLikelihoodSpectralMoment q j ≤
      thetaCuspHigherLikelihoodSpectralMoment q 0*thetaCuspDeepTailMoment q (i+j) := by
  have h1 := mul_le_mul_of_nonneg_left (deepMoment_source_normalized_order hq j)
    (thetaCuspDeepTailMoment_nonneg q i)
  have h2 := mul_le_mul_of_nonneg_left (deepMoment_mul_le_mass_mul hq i j)
    (thetaCuspHigherLikelihoodSpectralMoment_nonneg (B := q) 0)
  have hD := deepMoment_zero_pos hq
  have hc : thetaCuspDeepTailMoment q 0*
      (thetaCuspDeepTailMoment q i*thetaCuspHigherLikelihoodSpectralMoment q j) ≤
      thetaCuspDeepTailMoment q 0*
        (thetaCuspHigherLikelihoodSpectralMoment q 0*thetaCuspDeepTailMoment q (i+j)) := by
    nlinarith only [h1,h2]
  exact (mul_le_mul_iff_right₀ hD).mp (by simpa only [mul_comm] using hc)

end
end RHTower.ThetaCuspDefect
