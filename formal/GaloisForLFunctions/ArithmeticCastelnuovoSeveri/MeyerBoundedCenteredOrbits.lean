import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerHilbertSchmidtSource
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiAvoidingCenteredOrbitCriterion

/-!
# Bounded centered Meyer orbits are exactly critical highest jets

First-column bounds turn Hilbert–Schmidt boundedness into boundedness of each
raw Xi jet. Off-line characters force zero; on the critical line, the next
jet's affine shear kills every coefficient below the highest one. Conversely
the surviving full operator rows move by unit phases, so the norm is constant.
-/

noncomputable section
open Complex RHTower ContinuousLinearMap
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Actual sources whose only possible nonzero Xi jets are critical highest jets. -/
def MeyerCriticalTopJets (g : DeningerMeyerStrongLogTarget) : Prop :=
  ∀ (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho),
    ((rho : ℂ).re ≠ 1 / 2 ∨ j.val + 1 < xiSupportMultiplicity rho) →
      deningerMeyerStrongLogMellinJetLM j.val (rho : ℂ) g = 0

def MeyerJetOrbitBounded (g : DeningerMeyerStrongLogTarget) : Prop :=
  ∀ (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho),
    ∃ C : ℝ, ∀ c : ℝ,
      ‖deningerMeyerStrongLogMellinJetLM j.val (rho : ℂ)
        (deningerMeyerStrongLogCenteredFlow c g)‖ ≤ C

def MeyerHilbertOrbitBounded (g : DeningerMeyerStrongLogTarget) : Prop :=
  ∃ C : ℝ, ∀ c : ℝ,
    hsNorm (deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g)) ≤ C

def MeyerHilbertOrbitIsometric (g : DeningerMeyerStrongLogTarget) : Prop :=
  ∀ c : ℝ,
    hsNorm (deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g)) =
      hsNorm (deningerMeyerHilbertConvolution g)

private theorem affine_slope_zero (a b : ℂ)
    (h : ∃ C : ℝ, ∀ c : ℝ, ‖b + (c : ℂ) * a‖ ≤ C) : a = 0 := by
  obtain ⟨C, hC⟩ := h
  by_contra ha
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hCn : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let c : ℝ := (C + ‖b‖ + 1) / ‖a‖
  have hc : 0 < c := div_pos (by linarith only [hCn, norm_nonneg b]) hapos
  have hca : c * ‖a‖ = C + ‖b‖ + 1 := div_mul_cancel₀ _ hapos.ne'
  have htriangle := norm_sub_le (b + (c : ℂ) * a) b
  rw [show b + (c : ℂ) * a - b = (c : ℂ) * a by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at htriangle
  linarith only [htriangle, hC c, hca]

private theorem centered_character_norm (rho : XiDivisorSupport)
    (hr : (rho : ℂ).re = 1 / 2) (c : ℝ) :
    ‖Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2))‖ = 1 := by
  rw [Complex.norm_exp]
  have he : (((c : ℝ) : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_ofNat_re, Complex.one_re, hr, zero_mul, sub_zero, mul_zero, sub_self]
  rw [he, Real.exp_zero]

/-- An admitted Hilbert–Schmidt orbit bound controls every lower raw jet separately. -/
theorem meyerJetOrbitBounded_of_hilbert {g : DeningerMeyerStrongLogTarget}
    (h : MeyerHilbertOrbitBounded g) : MeyerJetOrbitBounded g := by
  obtain ⟨C, hC⟩ := h
  intro rho j
  refine ⟨(j.val.factorial : ℝ) * C, fun c => ?_⟩
  exact (meyerRawJet_norm_le_factorial_mul_hsNorm
    (deningerMeyerStrongLogCenteredFlow c g) rho j).trans
    (mul_le_mul_of_nonneg_left (hC c) (Nat.cast_nonneg _))

private theorem bounded_off_line_jets_zero (g : DeningerMeyerStrongLogTarget)
    (hb : MeyerJetOrbitBounded g) (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ∀ k < xiSupportMultiplicity rho, deningerMeyerStrongLogMellinJetLM k (rho : ℂ) g = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_contra hz
    have he := re_eq_zero_of_bounded_eigenfunctional_orbit
      deningerMeyerStrongLogCenteredFlow (deningerMeyerStrongLogMellinJetLM k (rho : ℂ))
      g hz ((rho : ℂ) - 1 / 2)
      (fun c => meyerCenteredSource_jet_of_lower_zero c g k (rho : ℂ)
        (fun i hi => ih i hi (hi.trans hk)))
      (hb rho ⟨k, hk⟩)
    have he' : (rho : ℂ).re - 1 / 2 = 0 := by
      simpa only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] using he
    exact hoff (by linarith only [he'])

private theorem bounded_critical_lower_jets_zero (g : DeningerMeyerStrongLogTarget)
    (hb : MeyerJetOrbitBounded g) (rho : XiDivisorSupport) (hr : (rho : ℂ).re = 1 / 2) :
    ∀ k, k + 1 < xiSupportMultiplicity rho →
      deningerMeyerStrongLogMellinJetLM k (rho : ℂ) g = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    obtain ⟨C, hC⟩ := hb rho ⟨k + 1, hk⟩
    have hzero := affine_slope_zero
      (((k + 1 : ℕ) : ℂ) * deningerMeyerStrongLogMellinJetLM k (rho : ℂ) g)
      (deningerMeyerStrongLogMellinJetLM (k + 1) (rho : ℂ) g) (by
        refine ⟨C, fun c => ?_⟩
        have hc := hC c
        rw [meyerCenteredSource_next_jet_of_lower_zero c g k (rho : ℂ)
          (fun i hi => ih i hi (by omega)), norm_mul,
          centered_character_norm rho hr c, one_mul] at hc
        rw [show ((k + 1 : ℕ) : ℂ) * (c : ℂ) *
          deningerMeyerStrongLogMellinJetLM k (rho : ℂ) g =
            (c : ℂ) * (((k + 1 : ℕ) : ℂ) *
              deningerMeyerStrongLogMellinJetLM k (rho : ℂ) g) by ring] at hc
        exact hc)
    exact (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast (show k + 1 ≠ 0 by omega))

/-- Individual bounded jet readings leave only the highest critical coefficients. -/
theorem meyerCriticalTopJets_of_jet_orbit_bounded {g : DeningerMeyerStrongLogTarget}
    (h : MeyerJetOrbitBounded g) : MeyerCriticalTopJets g := by
  intro rho j hj
  by_cases hr : (rho : ℂ).re = 1 / 2
  · exact bounded_critical_lower_jets_zero g h rho hr j.val
      (hj.resolve_left (not_not.mpr hr))
  · exact bounded_off_line_jets_zero g h rho hr j.val j.isLt

private theorem top_jet_character (g : DeningerMeyerStrongLogTarget) (hg : MeyerCriticalTopJets g)
    (c : ℝ) (rho : XiDivisorSupport) (k : ℕ) (hk : k < xiSupportMultiplicity rho) :
    deningerMeyerHasseMoment (deningerMeyerStrongLogCenteredFlow c g) k (rho : ℂ) =
      Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2)) * deningerMeyerHasseMoment g k (rho : ℂ) := by
  rw [deningerMeyerHasseMoment, meyerCenteredSource_jet_of_lower_zero c g k (rho : ℂ)
    (fun i hi => hg rho ⟨i, hi.trans hk⟩ (Or.inr (by omega))), deningerMeyerHasseMoment]
  ring

private theorem top_source_operator_row (g : DeningerMeyerStrongLogTarget)
    (hg : MeyerCriticalTopJets g) (c : ℝ) (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g) x q =
      Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2)) * deningerMeyerHilbertConvolution g x q := by
  rw [deningerMeyerHilbertConvolution_jets, deningerMeyerHilbertConvolution_jets, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k < xiSupportMultiplicity q.1 :=
    lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) q.2.isLt
  rw [top_jet_character g hg c q.1 k hkm]
  ring

/-- The surviving operator rows move by unit phases, so every Hilbert vector keeps its norm. -/
theorem meyerCriticalTopJets_operator_apply_norm (g : DeningerMeyerStrongLogTarget)
    (hg : MeyerCriticalTopJets g) (c : ℝ) (x : DeningerArithmeticJetHilbert) :
    ‖deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g) x‖ =
      ‖deningerMeyerHilbertConvolution g x‖ := by
  have hcoord (q : DeningerArithmeticJetCoordinate) :
      ‖deningerMeyerHilbertConvolution (deningerMeyerStrongLogCenteredFlow c g) x q‖ =
        ‖deningerMeyerHilbertConvolution g x q‖ := by
    rw [top_source_operator_row g hg, norm_mul]
    by_cases hr : (q.1 : ℂ).re = 1 / 2
    · rw [centered_character_norm q.1 hr c, one_mul]
    · have hz : deningerMeyerHilbertConvolution g x q = 0 := by
        rw [deningerMeyerHilbertConvolution_jets]
        apply Finset.sum_eq_zero
        intro k hk
        have hkm : k < xiSupportMultiplicity q.1 :=
          lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) q.2.isLt
        rw [deningerMeyerHasseMoment, hg q.1 ⟨k, hkm⟩ (Or.inl hr), zero_div, zero_mul]
      rw [hz, norm_zero, mul_zero]
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact tsum_congr fun q => by rw [hcoord q]

/-- Critical highest jets have an isometric full Hilbert–Schmidt centered orbit. -/
theorem meyerHilbertOrbitIsometric_of_criticalTopJets {g : DeningerMeyerStrongLogTarget}
    (h : MeyerCriticalTopJets g) : MeyerHilbertOrbitIsometric g := by
  intro c
  rw [hsNorm, hsNorm]
  congr 1
  unfold hsNormSq
  exact tsum_congr fun i => by rw [meyerCriticalTopJets_operator_apply_norm g h c]

theorem meyerHilbertOrbitBounded_of_isometric {g : DeningerMeyerStrongLogTarget}
    (h : MeyerHilbertOrbitIsometric g) : MeyerHilbertOrbitBounded g :=
  ⟨hsNorm (deningerMeyerHilbertConvolution g), fun c => (h c).le⟩

/-- The exact bounded full-operator orbit criterion. -/
theorem meyerHilbertOrbitBounded_iff_criticalTopJets (g : DeningerMeyerStrongLogTarget) :
    MeyerHilbertOrbitBounded g ↔ MeyerCriticalTopJets g :=
  ⟨fun h => meyerCriticalTopJets_of_jet_orbit_bounded (meyerJetOrbitBounded_of_hilbert h),
    fun h => meyerHilbertOrbitBounded_of_isometric (meyerHilbertOrbitIsometric_of_criticalTopJets h)⟩

theorem meyerJetOrbitBounded_iff_criticalTopJets (g : DeningerMeyerStrongLogTarget) :
    MeyerJetOrbitBounded g ↔ MeyerCriticalTopJets g :=
  ⟨meyerCriticalTopJets_of_jet_orbit_bounded, fun h =>
    meyerJetOrbitBounded_of_hilbert ((meyerHilbertOrbitBounded_iff_criticalTopJets g).mpr h)⟩

theorem meyerHilbertOrbitIsometric_iff_criticalTopJets (g : DeningerMeyerStrongLogTarget) :
    MeyerHilbertOrbitIsometric g ↔ MeyerCriticalTopJets g :=
  ⟨fun h => (meyerHilbertOrbitBounded_iff_criticalTopJets g).mp
    (meyerHilbertOrbitBounded_of_isometric h), meyerHilbertOrbitIsometric_of_criticalTopJets⟩

private theorem all_criticalTopJets_of_simple_critical (hRH : RiemannHypothesis)
    (hs : ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1)
    (g : DeningerMeyerStrongLogTarget) : MeyerCriticalTopJets g := by
  intro rho j hj
  have hr : (rho : ℂ).re = 1 / 2 :=
    (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).mp
      ((xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) rho)
  rcases hj with hoff | hj
  · exact False.elim (hoff hr)
  · rw [hs rho] at hj
    omega

/-- The existing one fixed Xi-avoiding source detects simplicity as well as criticality. -/
theorem meyerXiAvoidingHilbertOrbitBounded_iff :
    MeyerHilbertOrbitBounded deningerMeyerXiAvoidingSource ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  rw [meyerHilbertOrbitBounded_iff_criticalTopJets]
  constructor
  · intro h
    have hne (rho : XiDivisorSupport) :
        deningerMeyerStrongLogMellinJetLM 0 (rho : ℂ) deningerMeyerXiAvoidingSource ≠ 0 := by
      simpa only [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero] using
        deningerMeyerXiAvoidingSource_nonzero_on_support rho
    have hr (rho : XiDivisorSupport) : (rho : ℂ).re = 1 / 2 := by
      by_contra hoff
      exact hne rho (h rho ⟨0, xiSupportMultiplicity_pos rho⟩ (Or.inl hoff))
    refine ⟨xiBoundaryCharacterNeutral_iff_riemannHypothesis.mp (fun rho =>
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).mpr (hr rho)), ?_⟩
    intro rho
    have hp := xiSupportMultiplicity_pos rho
    by_contra hm
    have hlt : 0 + 1 < xiSupportMultiplicity rho := by omega
    exact hne rho (h rho ⟨0, hp⟩ (Or.inr hlt))
  · rintro ⟨hRH, hs⟩
    exact all_criticalTopJets_of_simple_critical hRH hs _

/-- All actual full-Hasse orbits are bounded precisely for simple critical Xi zeros. -/
theorem all_meyerHilbertOrbits_bounded_iff :
    (∀ g : DeningerMeyerStrongLogTarget, MeyerHilbertOrbitBounded g) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h
    exact meyerXiAvoidingHilbertOrbitBounded_iff.mp (h _)
  · rintro ⟨hRH, hs⟩ g
    exact (meyerHilbertOrbitBounded_iff_criticalTopJets g).mpr
      (all_criticalTopJets_of_simple_critical hRH hs g)

theorem all_meyerHilbertOrbits_isometric_iff :
    (∀ g : DeningerMeyerStrongLogTarget, MeyerHilbertOrbitIsometric g) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h
    exact all_meyerHilbertOrbits_bounded_iff.mp (fun g => meyerHilbertOrbitBounded_of_isometric (h g))
  · rintro ⟨hRH, hs⟩ g
    exact meyerHilbertOrbitIsometric_of_criticalTopJets
      (all_criticalTopJets_of_simple_critical hRH hs g)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertOrbitBounded_iff_criticalTopJets
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerJetOrbitBounded_iff_criticalTopJets
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerHilbertOrbitIsometric_iff_criticalTopJets
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerXiAvoidingHilbertOrbitBounded_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.all_meyerHilbertOrbits_bounded_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.all_meyerHilbertOrbits_isometric_iff
