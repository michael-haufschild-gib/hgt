import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateVanishesUniformlyToTheLeft
import GaloisForLFunctions.HTGeometry.HardyBoundary.DiskHalfLineCayley
import GaloisForLFunctions.RHTower.WeightedLaplaceShift

/-!
# Prime heads as Hardy transforms

Confinement controls the exponentially damped negative-half-line profile.
Each prime head is the Laplace transform of a translated restriction of this
profile. Beyond the Euler boundary the coefficients are summable, so the
profiles sum in `L²`; continuous Laplace evaluation identifies their sum with
the actual prime-head series and gives uniform vertical square bounds.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
open scoped InnerProductSpace
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Damping a negative-half-line profile uses its confinement moment. -/
def dampedNegativeProfile (F : ℝ → ℝ) (c u : ℝ) : ℂ :=
  (Real.exp (-c*u) : ℂ)*(F u : ℂ)

theorem memLp_dampedNegativeProfile {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) : MemLp (dampedNegativeProfile F c) 2 volume := by
  have hm : Measurable (dampedNegativeProfile F c) :=
    (Complex.measurable_ofReal.comp (by fun_prop : Measurable fun u : ℝ => Real.exp (-c*u))).mul
      (Complex.measurable_ofReal.comp hF.meas)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine hF.exponential.mono' (hm.norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  rcases lt_or_ge u 0 with hu | hu
  · have he : Real.exp (-c*u) ≤ Real.exp (-4*u) :=
      Real.exp_le_exp.mpr (by nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc) hu.le])
    calc
      ‖dampedNegativeProfile F c u‖^2 = Real.exp (-c*u)^2 * F u^2 := by
        rw [dampedNegativeProfile,norm_mul,Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
      _ ≤ Real.exp (-4*u)^2 * F u^2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le he 2) (sq_nonneg _)
      _ = F u^2 * Real.exp (-(8*u)) := by
        rw [sq (Real.exp (-4*u)),← Real.exp_add,
          show -4*u + -4*u = -(8*u) by ring]
        exact mul_comm _ _
  · simp [dampedNegativeProfile,hF.support u hu]

/-- A prime head is a translated restriction of the damped profile. -/
def primeHeadDatumTerm (F : ℝ → ℝ) (c : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  ((vonMangoldtAtom n*Real.exp (-c*Real.log n) : ℝ) : ℂ) *
    dampedNegativeProfile F c (v-Real.log n)

private theorem primeHead_damping_nonneg (c : ℝ) (n : ℕ) :
    0 ≤ vonMangoldtAtom n*Real.exp (-c*Real.log n) := by
  apply mul_nonneg _ (Real.exp_pos _).le
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-- The damped prime coefficients are summable beyond the Euler boundary. -/
theorem summable_primeHead_damping {c : ℝ} (hc : 1/2 < c) :
    Summable fun n : ℕ => vonMangoldtAtom n*Real.exp (-c*Real.log n) := by
  have h := (summable_vonMangoldtAtom_mul_cexp (p := -(c : ℂ))
    (by simp only [neg_re,ofReal_re]; linarith only [hc])).norm
  refine h.congr fun n => ?_
  have hn : 0 ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hn,norm_cexp_mul_ofReal]
  simp only [neg_re,ofReal_re]

theorem memLp_primeHeadDatumTerm {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (n : ℕ) :
    MemLp (primeHeadDatumTerm F c n) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have ht := (memLp_dampedNegativeProfile hF hc).comp_measurePreserving
    (measurePreserving_add_right (volume : Measure ℝ) (-Real.log n))
  have hm := (ht.const_mul ((vonMangoldtAtom n*Real.exp (-c*Real.log n) : ℝ) : ℂ)).restrict (Ioi 0)
  change MemLp (fun v => primeHeadDatumTerm F c n v) _ _
  simpa only [primeHeadDatumTerm,Function.comp_def,sub_eq_add_neg] using hm

/-- The actual translated prime profile as an element of the half-line Hilbert space. -/
def primeHeadDatumLp {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (n : ℕ) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_primeHeadDatumTerm hF hc n).toLp (primeHeadDatumTerm F c n)

/-- Translation preserves the global mass; restriction to the half-line can only reduce it. -/
theorem eLpNorm_primeHeadDatumTerm_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (n : ℕ) :
    eLpNorm (primeHeadDatumTerm F c n) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
      ENNReal.ofReal (vonMangoldtAtom n*Real.exp (-c*Real.log n)) *
        eLpNorm (dampedNegativeProfile F c) 2 volume := by
  have hG := memLp_dampedNegativeProfile hF hc
  have ht : eLpNorm (fun v => dampedNegativeProfile F c (v-Real.log n)) 2 volume =
      eLpNorm (dampedNegativeProfile F c) 2 volume := by
    simpa only [Function.comp_def,sub_eq_add_neg] using
      eLpNorm_comp_measurePreserving hG.aestronglyMeasurable
        (measurePreserving_add_right (volume : Measure ℝ) (-Real.log n))
  change eLpNorm (((vonMangoldtAtom n*Real.exp (-c*Real.log n) : ℝ) : ℂ) •
    (fun v => dampedNegativeProfile F c (v-Real.log n))) 2 _ ≤ _
  rw [eLpNorm_const_smul,← ofReal_norm,Complex.norm_real,
    Real.norm_of_nonneg (primeHead_damping_nonneg c n)]
  exact mul_le_mul' le_rfl ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq ht)

theorem norm_primeHeadDatumLp_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (n : ℕ) :
    ‖primeHeadDatumLp hF hc n‖ ≤
      (vonMangoldtAtom n*Real.exp (-c*Real.log n)) *
        (eLpNorm (dampedNegativeProfile F c) 2 volume).toReal := by
  rw [primeHeadDatumLp,Lp.norm_toLp]
  have hfinite : ENNReal.ofReal (vonMangoldtAtom n*Real.exp (-c*Real.log n)) *
      eLpNorm (dampedNegativeProfile F c) 2 volume ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_dampedNegativeProfile hF hc).2).ne
  refine (ENNReal.toReal_mono hfinite (eLpNorm_primeHeadDatumTerm_le hF hc n)).trans_eq ?_
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (primeHead_damping_nonneg c n)]

/-- Confinement makes the translated prime profiles summable in the Hilbert norm. -/
theorem summable_primeHeadDatumLp {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (hc0 : 1/2 < c) :
    Summable (primeHeadDatumLp hF hc) := by
  exact Summable.of_norm_bounded ((summable_primeHead_damping hc0).mul_right _)
    (norm_primeHeadDatumLp_le hF hc)

/-- Translation identifies the Laplace transform of each Hilbert-space summand with its prime head. -/
theorem laplaceRay_primeHeadDatumTerm (F : ℝ → ℝ) (c : ℝ) (n : ℕ) (z : ℂ) :
    laplaceRay (primeHeadDatumTerm F c n) z =
      (vonMangoldtAtom n : ℂ)*(cexp ((-(z+c))*Real.log n)*
        levyHead F (-(z+c)) (Real.log n)) := by
  let L : ℝ := Real.log n
  let p : ℂ := -(z+c)
  have hfun : (fun v => primeHeadDatumTerm F c n v*expRay z v) =
      fun v : ℝ => (vonMangoldtAtom n : ℂ)*(cexp (p*v)*(F (v-L) : ℂ)) := by
    funext v
    have he : (Real.exp (-c*L) : ℂ)*(Real.exp (-c*(v-L)) : ℂ)*cexp (-(z*v)) =
        cexp (p*v) := by
      rw [Complex.ofReal_exp,Complex.ofReal_exp,← Complex.exp_add,← Complex.exp_add]
      congr 1
      dsimp only [p]
      push_cast
      ring
    dsimp only [primeHeadDatumTerm,dampedNegativeProfile,expRay]
    change (((vonMangoldtAtom n*Real.exp (-c*L) : ℝ) : ℂ)*
      ((Real.exp (-c*(v-L)) : ℂ)*(F (v-L) : ℂ)))*cexp (-(z*v)) = _
    rw [Complex.ofReal_mul]
    calc
      _ = (vonMangoldtAtom n : ℂ)*
          ((Real.exp (-c*L) : ℂ)*(Real.exp (-c*(v-L)) : ℂ)*cexp (-(z*v)))*
          (F (v-L) : ℂ) := by ring
      _ = _ := by rw [he]; ring
  have htrans := GaloisForLFunctions.RHTower.setIntegral_Ioi_comp_add_right
    (fun u : ℝ => cexp (p*((L+u : ℝ) : ℂ))*(F u : ℂ)) (-L) (-L)
  simp only [sub_self] at htrans
  have hshift : (∫ v in Ioi (0 : ℝ), cexp (p*v)*(F (v-L) : ℂ)) =
      ∫ u in Ioi (-L), cexp (p*((L+u : ℝ) : ℂ))*(F u : ℂ) := by
    rw [← htrans]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [sub_eq_add_neg]
    congr 2
    push_cast
    ring
  rw [laplaceRay,hfun,integral_const_mul,hshift,← cexp_mul_levyHead_eq_integral]

/-- The damped prime profile, summed in the half-line Hilbert space. -/
def primeHeadProfileLp {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ∑' n : ℕ, primeHeadDatumLp hF hc n

/-- Continuous Laplace evaluation commutes with the Hilbert-space prime sum. -/
theorem laplaceRay_primeHeadProfile {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (hc0 : 1/2 < c) {z : ℂ} (hz : 0 < z.re) :
    laplaceRay (primeHeadProfileLp hF hc) z = primeHead F (-(z+c)) := by
  have h := (innerSL ℂ (halfLineLaplaceFeature z hz)).hasSum
    (summable_primeHeadDatumLp hF hc hc0).hasSum
  change HasSum (fun n => halfLineLaplaceTransform (primeHeadDatumLp hF hc n) z hz)
    (halfLineLaplaceTransform (primeHeadProfileLp hF hc) z hz) at h
  simp_rw [halfLineLaplaceTransform_eq_laplaceRay] at h
  have hterm (n : ℕ) : laplaceRay (primeHeadDatumLp hF hc n) z =
      (vonMangoldtAtom n : ℂ)*(cexp ((-(z+c))*Real.log n)*
        levyHead F (-(z+c)) (Real.log n)) := by
    rw [← laplaceRay_primeHeadDatumTerm F c n z]
    unfold laplaceRay
    refine integral_congr_ae ?_
    filter_upwards [(memLp_primeHeadDatumTerm hF hc n).coeFn_toLp] with v hv
    change (primeHeadDatumLp hF hc n : ℝ → ℂ) v * expRay z v = _
    rw [show (primeHeadDatumLp hF hc n : ℝ → ℂ) v = primeHeadDatumTerm F c n v from hv]
  exact (h.congr_fun fun n => (hterm n).symm).tsum_eq.symm

/-- The prime heads have uniformly square-integrable vertical traces beyond every Euler margin. -/
theorem isHalfPlaneHardy_primeHead {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : c ≤ 4) (hc0 : 1/2 < c) :
    IsHalfPlaneHardy (fun z => primeHead F (-(z+c)))
      (∫ s in Ioi (0 : ℝ), ‖(primeHeadProfileLp hF hc : ℝ → ℂ) s‖^2) := by
  have h := isHalfPlaneHardy_laplaceRay (Lp.memLp (primeHeadProfileLp hF hc))
  have he : EqOn (fun z => primeHead F (-(z+c))) (laplaceRay (primeHeadProfileLp hF hc))
      {z : ℂ | 0 < z.re} := fun z hz => (laplaceRay_primeHeadProfile hF hc hc0 hz).symm
  have heq (σ : ℝ) (hσ : 0 < σ) : (fun ξ => primeHead F (-(rayLine σ ξ+c))) =
      fun ξ => laplaceRay (primeHeadProfileLp hF hc) (rayLine σ ξ) :=
    funext fun ξ => he (by simpa only [mem_setOf_eq,rayLine_re] using hσ)
  refine ⟨h.holo.congr he, ?_, ?_⟩
  · intro σ hσ
    rw [heq σ hσ]
    exact h.memLp σ hσ
  · intro σ hσ
    simp_rw [congrFun (heq σ hσ)]
    exact h.bound σ hσ

end GaloisForLFunctions.ExclusionOfTheCriticalState
