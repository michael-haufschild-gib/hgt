import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixAmplitudeSummability

/-!
# A qualitative sign-recurrence criterion for the paired-eta prefix

The sharp centered-tail asymptotic determines the eventual sign of the
completed partner-minus-original amplitude. A zero to the right of the
critical line makes this difference positive at every late cutoff; reflection
reverses the sign on the left. On the critical line the difference vanishes
at every cutoff. Hence it suffices to show, for every zero, that the difference
is nonpositive at arbitrarily late cutoffs. This is an unconditional reduction
to a source-side sign-recurrence problem, not a proof of that recurrence.
-/

open Complex Filter Topology
namespace RiemannGaussian
noncomputable section

/-- Completed partner magnitude minus conjugate-original magnitude at one
finite paired-eta cutoff. -/
def topPrefixAmplitudeDifference (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent rho N‖ -
  ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent rho N‖

/-- Reflection across the critical line reverses the amplitude difference. -/
theorem topPrefixAmplitudeDifference_partner (rho : NontrivialZetaZero) (N : ℕ) :
    topPrefixAmplitudeDifference (NontrivialZetaZero.conjugatePartner rho) N =
      -topPrefixAmplitudeDifference rho N := by
  unfold topPrefixAmplitudeDifference
  rw [norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail,
    norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail,
    norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail,
    norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail]
  simp only [NontrivialZetaZero.conjugatePartner_conjugatePartner,
    analyticZetaZeroMultiplicity_conjugatePartner]
  ring

/-- A right-half zero has strictly positive difference at every sufficiently
late cutoff. -/
theorem eventually_pos_topPrefixAmplitudeDifference_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop, 0 < topPrefixAmplitudeDifference rho N := by
  have hlim :=
    tendsto_succOddEndpoint_partner_rpow_mul_topPrefixComponentNormDifference_of_half_lt_re
      rho hrho
  have hpos := hlim.eventually
    (eventually_gt_nhds (topPrefixPartnerAmplitudeSharpLimit_pos rho))
  filter_upwards [hpos] with N hN
  have hscale : 0 < (((2 * (N + 1) + 1 : ℕ) : ℝ) ^
      (NontrivialZetaZero.conjugatePartner rho).1.re) := by positivity
  change 0 < (((2 * (N + 1) + 1 : ℕ) : ℝ) ^
      (NontrivialZetaZero.conjugatePartner rho).1.re) *
      topPrefixAmplitudeDifference rho N at hN
  by_contra h
  have hnonpos : topPrefixAmplitudeDifference rho N ≤ 0 := le_of_not_gt h
  have hprod := mul_nonpos_of_nonneg_of_nonpos hscale.le hnonpos
  exact (not_le_of_gt hN) hprod

/-- A left-half zero has strictly negative difference at every sufficiently
late cutoff. -/
theorem eventually_neg_topPrefixAmplitudeDifference_of_re_lt_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, topPrefixAmplitudeDifference rho N < 0 := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  have hp : 1 / 2 < partner.1.re := by
    simp [partner, NontrivialZetaZero.conjugatePartner_coe]
    linarith
  have h := eventually_pos_topPrefixAmplitudeDifference_of_half_lt_re partner hp
  filter_upwards [h] with N hN
  rw [show rho = NontrivialZetaZero.conjugatePartner partner by
    simp [partner]]
  rw [topPrefixAmplitudeDifference_partner]
  exact neg_neg_iff_pos.mpr hN


/-- Every zero has arbitrarily late cutoffs with nonpositive completed
partner-minus-original amplitude. -/
def NoPersistentPositiveTopPrefixAmplitudeDifference : Prop :=
  ∀ rho : NontrivialZetaZero, ∀ M : ℕ,
    ∃ N : ℕ, M ≤ N ∧ topPrefixAmplitudeDifference rho N ≤ 0

/-- The qualitative sign-recurrence property is equivalent to RH. -/
theorem noPersistentPositiveTopPrefixAmplitudeDifference_iff_rh :
    NoPersistentPositiveTopPrefixAmplitudeDifference ↔ RiemannHypothesis := by
  constructor
  · intro h
    rw [riemannHypothesis_iff_spectralCoordinate_real]
    intro s hs hnontrivial hone
    let rho : NontrivialZetaZero := ⟨s, hs, hnontrivial, hone⟩
    have hnotright (q : NontrivialZetaZero) : ¬1 / 2 < q.1.re := by
      intro hright
      obtain ⟨M, hM⟩ := eventually_atTop.1
        (eventually_pos_topPrefixAmplitudeDifference_of_half_lt_re q hright)
      obtain ⟨N, hMN, hnonpos⟩ := h q M
      exact (not_le_of_gt (hM N hMN)) hnonpos
    have hr := hnotright rho
    have hp := hnotright (NontrivialZetaZero.conjugatePartner rho)
    have heq : rho.1.re = 1 / 2 := by
      simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
        Complex.one_re, Complex.conj_re] at hp
      dsimp only [rho] at hr hp ⊢
      linarith
    exact (zetaSpectralCoordinate_im_eq_zero_iff s).2 heq
  · intro hRH rho M
    refine ⟨M, le_rfl, ?_⟩
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    have hrho : rho.1.re = 1 / 2 :=
      (zetaSpectralCoordinate_im_eq_zero_iff rho.1).1 him
    have hzero := topPrefixAmplitudeImbalance_eq_zero_of_re_eq_half rho hrho M
    change (topPrefixAmplitudeDifference rho M) ^ 2 = 0 at hzero
    have hdiff : topPrefixAmplitudeDifference rho M = 0 := by
      nlinarith only [hzero]
    exact le_of_eq hdiff

end
end RiemannGaussian
