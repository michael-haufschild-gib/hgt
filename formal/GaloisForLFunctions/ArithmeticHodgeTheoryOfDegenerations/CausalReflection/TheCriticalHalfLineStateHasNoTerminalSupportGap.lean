import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ThePairedReflectionPreservesArithmeticEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateHasNoPositiveLaplaceZero
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonBlockOnTheArithmeticSide
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UnrestrictedAtomicGardingFailsAndCollarGardingHolds

/-!
# Critical half-line states have no terminal support gap

The arithmetic energy is translation invariant. Translating toward the endpoint
strictly decreases the exponential square mass. A terminal gap would admit such
a translate at the critical threshold, contradicting nonnegativity of full energy.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri HTGeometry WindowTowerOfSpecZ

/-- Almost-everywhere equality preserves every literal Fourier value. -/
theorem paperFT_cx_congr_ae {F G : ℝ → ℝ} (he : F =ᵐ[volume] G) (r : ℂ) :
    paperFT (cx F) r = paperFT (cx G) r := by
  unfold paperFT
  apply integral_congr_ae
  filter_upwards [he] with u hu
  simp only [cx, hu]

/-- Domain membership passes to a measurable representative with negative support. -/
theorem CriticalHalfLineEnergyDomain.congr_ae {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hm : Measurable G)
    (he : F =ᵐ[volume] G) (hs : ∀ u, 0 ≤ u → G u = 0) :
    CriticalHalfLineEnergyDomain G := by
  refine ⟨hm, hF.integrable.congr he, ?_, ?_, hs, ?_⟩
  · exact hF.sq.congr (he.mono fun u hu => congrArg (fun x : ℝ => x ^ 2) hu)
  · apply hF.exponential.congr
    filter_upwards [he] with u hu
    rw [hu]
  · simpa only [← paperFT_cx_congr_ae he] using hF.gamma

/-- The full energy depends only on the almost-everywhere profile. -/
theorem criticalHalfLineFullEnergy_congr_ae {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (he : F =ᵐ[volume] G) (R : ℝ) :
    criticalHalfLineFullEnergy R F = criticalHalfLineFullEnergy R G := by
  have ha : archForm F = archForm G := by
    unfold archForm
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall fun r => ?_
    change ‖paperFT (cx F) (r : ℂ)‖ ^ 2 * EF.gammaBracket r =
      ‖paperFT (cx G) (r : ℂ)‖ ^ 2 * EF.gammaBracket r
    rw [paperFT_cx_congr_ae he]
  have hc (t : ℝ) : (∫ u, F u * F (u + t)) = ∫ u, G u * G (u + t) := by
    apply integral_congr_ae
    have ht := he.comp_tendsto
      (measurePreserving_add_right volume t).quasiMeasurePreserving.tendsto_ae
    filter_upwards [he, ht] with u hu htu
    exact congrArg₂ (fun x y : ℝ => x * y) hu htu
  have hp : primeSum F = primeSum G := by
    unfold primeSum
    apply tsum_congr
    intro n
    have hm := hc (-Real.log n)
    simp only [← sub_eq_add_neg] at hm
    rw [hm, hc]
  have hk (k : ℝ → ℝ) : (∫ u, F u * k u) = ∫ u, G u * k u := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    rw [hu]
  have hcos : coshHalfMoment F = coshHalfMoment G := hk _
  have hsin : sinhHalfMoment F = sinhHalfMoment G := hk _
  have hw : (∫ u, F u ^ 2 * Real.exp (-(8 * u))) =
      ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    rw [hu]
  unfold criticalHalfLineFullEnergy
  rw [ha, hp, hcos, hsin, halfLineExpMass_eq_full hF.support,
    halfLineExpMass_eq_full hG.support, hw]

/-- Translation multiplies every real Laplace moment by its exponential character. -/
theorem integral_exp_comp_add_right (F : ℝ → ℝ) (c s : ℝ) :
    (∫ u, F (u + c) * Real.exp (s * u)) =
      Real.exp (-(s * c)) * ∫ u, F u * Real.exp (s * u) := by
  have hp (u : ℝ) : F (u + c) * Real.exp (s * u) =
      Real.exp (-(s * c)) * (F (u + c) * Real.exp (s * (u + c))) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hp]
  rw [integral_const_mul]
  congr 1
  exact integral_add_right_eq_self (fun u => F u * Real.exp (s * u)) c

/-- Moving a profile left multiplies its exponential square mass by `exp(8c)`. -/
theorem exponential_square_comp_add_right (F : ℝ → ℝ) (c : ℝ) :
    (∫ u, F (u + c) ^ 2 * Real.exp (-(8 * u))) =
      Real.exp (8 * c) * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  simpa only [neg_mul, neg_neg] using
    integral_exp_comp_add_right (fun u => F u ^ 2) c (-8)

/-- Translation changes the paper Fourier transform only by a unit phase. -/
theorem norm_paperFT_cx_comp_add_right (F : ℝ → ℝ) (c r : ℝ) :
    ‖paperFT (cx (fun u => F (u + c))) r‖ = ‖paperFT (cx F) r‖ := by
  change ‖paperFT (fun u => cx F (u + c)) (r : ℂ)‖ = _
  rw [paperFT_comp_add, norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    one_mul, sub_zero, zero_add, neg_zero, Real.exp_zero, one_mul]

/-- Every translate that retains negative support stays in the full energy domain. -/
theorem CriticalHalfLineEnergyDomain.comp_add_right {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (c : ℝ)
    (hs : ∀ u, 0 ≤ u → F (u + c) = 0) :
    CriticalHalfLineEnergyDomain (fun u => F (u + c)) := by
  refine ⟨hF.meas.comp (measurable_id.add measurable_const),
    hF.integrable.comp_add_right c, hF.sq.comp_add_right c, ?_, hs, ?_⟩
  · apply ((hF.exponential.comp_add_right c).const_mul (Real.exp (8 * c))).congr
    refine Eventually.of_forall fun u => ?_
    change Real.exp (8 * c) * (F (u + c) ^ 2 * Real.exp (-(8 * (u + c)))) = _
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  · simpa only [norm_paperFT_cx_comp_add_right] using hF.gamma

/-- Opposite half-pole characters cancel in their product. -/
theorem pole_energy_comp_add_right {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (c : ℝ)
    (hs : ∀ u, 0 ≤ u → F (u + c) = 0) :
    2 * coshHalfMoment (fun u => F (u + c)) ^ 2 -
        2 * sinhHalfMoment (fun u => F (u + c)) ^ 2 =
      2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2 := by
  have hG := hF.comp_add_right c hs
  obtain ⟨hFp, hFm⟩ := negativeHalfLineLaplace_halfPole_real hF.weighted
  obtain ⟨hGp, hGm⟩ := negativeHalfLineLaplace_halfPole_real hG.weighted
  rw [negativeHalfLineLaplace_ofReal] at hFp hGp
  rw [← Complex.ofReal_neg, negativeHalfLineLaplace_ofReal] at hFm hGm
  have hp := integral_exp_comp_add_right F c (1 / 2)
  have hm := integral_exp_comp_add_right F c (-(1 / 2))
  rw [Complex.ofReal_inj.mp hFp, Complex.ofReal_inj.mp hGp] at hp
  rw [Complex.ofReal_inj.mp hFm, Complex.ofReal_inj.mp hGm] at hm
  have hprod := congrArg₂ (fun x y : ℝ => x * y) hp hm
  have he : Real.exp (-((1 / 2 : ℝ) * c)) *
      Real.exp (-(-(1 / 2 : ℝ) * c)) = 1 := by
    rw [← Real.exp_add, show -((1 / 2 : ℝ) * c) + -(-(1 / 2 : ℝ) * c) = 0 by ring,
      Real.exp_zero]
  have hp' : (coshHalfMoment (fun u => F (u + c)) + sinhHalfMoment (fun u => F (u + c))) *
      (coshHalfMoment (fun u => F (u + c)) - sinhHalfMoment (fun u => F (u + c))) =
      (coshHalfMoment F + sinhHalfMoment F) * (coshHalfMoment F - sinhHalfMoment F) := by
    calc
      _ = _ := hprod
      _ = (Real.exp (-((1 / 2 : ℝ) * c)) * Real.exp (-(-(1 / 2 : ℝ) * c))) *
          ((coshHalfMoment F + sinhHalfMoment F) * (coshHalfMoment F - sinhHalfMoment F)) := by ring
      _ = _ := by rw [he, one_mul]
  nlinarith only [hp']

/-- The translation-invariant arithmetic terms leave an exact exponential mass defect. -/
theorem criticalHalfLineFullEnergy_comp_add_right {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (c R : ℝ)
    (hs : ∀ u, 0 ≤ u → F (u + c) = 0) :
    criticalHalfLineFullEnergy R (fun u => F (u + c)) =
      criticalHalfLineFullEnergy R F + criticalAliasCoefficient R *
        (Real.exp (8 * c) - 1) * ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  have ha : archForm (fun u => F (u + c)) = archForm F := by
    unfold archForm
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall fun r => ?_
    change ‖paperFT (cx (fun u => F (u + c))) (r : ℂ)‖ ^ 2 * EF.gammaBracket r =
      ‖paperFT (cx F) (r : ℂ)‖ ^ 2 * EF.gammaBracket r
    rw [norm_paperFT_cx_comp_add_right]
  unfold criticalHalfLineFullEnergy
  rw [ha, primeSum_comp_add_right, pole_energy_comp_add_right hF c hs,
    halfLineExpMass_eq_full hs, halfLineExpMass_eq_full hF.support,
    exponential_square_comp_add_right]
  ring

/-- A unit profile's exponential mass is at least its ordinary mass. -/
theorem one_le_exponential_square_of_domain {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hn : (∫ u, F u ^ 2) = 1) :
    1 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  rw [← hn]
  apply integral_mono hF.sq hF.exponential
  intro u
  change F u ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u))
  by_cases hu : 0 ≤ u
  · rw [hF.support u hu]
    norm_num
  · have he : 1 ≤ Real.exp (-(8 * u)) := Real.one_le_exp (by linarith only [hu])
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (sq_nonneg (F u))

/-- Every terminal interval contains positive square mass of an actual critical state. -/
theorem criticalHalfLineGroundState_endpoint_mass_pos
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {d : ℝ} (hd : 0 < d) : 0 < ∫ u in Ioo (-d) 0, F u ^ 2 := by
  have hD := criticalHalfLineEnergyDomain_of_groundState hF
  by_contra hbad
  have hzero : (∫ u in Ioo (-d) 0, F u ^ 2) = 0 :=
    le_antisymm (le_of_not_gt hbad) (integral_nonneg fun _ => sq_nonneg _)
  have hsq := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => sq_nonneg (F u)) hD.sq.integrableOn).mp hzero
  have hgap : ∀ᵐ u ∂volume, u ∈ Ioo (-d) 0 → F u ^ 2 = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).mp hsq
  let G : ℝ → ℝ := (Iio (-d / 2)).indicator F
  have he : F =ᵐ[volume] G := by
    filter_upwards [hgap] with u hu
    by_cases hlt : u < -d / 2
    · exact (indicator_of_mem (show u ∈ Iio (-d / 2) from hlt) F).symm
    · rw [show G u = 0 from
        indicator_of_notMem (show u ∉ Iio (-d / 2) from hlt) F]
      by_cases hp : 0 ≤ u
      · exact hD.support u hp
      · have hz := hu ⟨by linarith only [hlt, hd], lt_of_not_ge hp⟩
        nlinarith only [hz]
  have hsG (u : ℝ) (hu : 0 ≤ u) : G u = 0 :=
    indicator_of_notMem (show u ∉ Iio (-d / 2) by
      change ¬u < -d / 2
      linarith only [hu, hd]) F
  have hG := hD.congr_ae (hD.meas.indicator measurableSet_Iio) he hsG
  have hnG : (∫ u, G u ^ 2) = 1 := by
    rw [← hF.2.2.2.1]
    exact integral_congr_ae (he.symm.mono fun u hu => congrArg (fun x : ℝ => x ^ 2) hu)
  have hmass : 0 < ∫ u, G u ^ 2 * Real.exp (-(8 * u)) :=
    lt_of_lt_of_le zero_lt_one (one_le_exponential_square_of_domain hG hnG)
  have henergy : criticalHalfLineFullEnergy W₀ G = 0 := by
    rw [← criticalHalfLineFullEnergy_congr_ae hD hG he]
    exact criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF
  have hsShift (u : ℝ) (hu : 0 ≤ u) : G (u + (-d / 2)) = 0 :=
    indicator_of_notMem (show u + (-d / 2) ∉ Iio (-d / 2) by
      change ¬u + (-d / 2) < -d / 2
      linarith only [hu]) F
  have hpos := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW hthreshold
    (hG.comp_add_right (-d / 2) hsShift)
  rw [criticalHalfLineFullEnergy_comp_add_right hG _ _ hsShift, henergy, zero_add] at hpos
  have heps : Real.exp (8 * (-d / 2)) - 1 < 0 := by
    have hh : Real.exp (8 * (-d / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hd])
    linarith only [hh]
  have hneg := mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (criticalAliasCoefficient_positive hW) heps) hmass
  exact (not_lt_of_ge hpos) hneg

/-- Failure of RH supplies a critical state with positive square mass arbitrarily
close to the endpoint of its supporting half-line. -/
theorem riemannHypothesis_or_exists_endpointFullSupport_criticalHalfLineGroundState :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ d : ℝ, 0 < d → 0 < ∫ u in Ioo (-d) 0, F u ^ 2 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF,
      fun _ hd => criticalHalfLineGroundState_endpoint_mass_pos hW ht hF hd⟩

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_or_exists_endpointFullSupport_criticalHalfLineGroundState
