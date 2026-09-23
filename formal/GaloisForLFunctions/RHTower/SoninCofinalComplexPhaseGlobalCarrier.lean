import GaloisForLFunctions.RHTower.SoninCofinalComplexPhaseOddFisherSplice

/-!
# Global complex-phase Sonin source carrier

The pointwise complex-phase Sonin splice supplies one cofinal depth sequence
per phase.  That cannot serve as a source-defined carrier for an unknown Xi
divisor: selecting a phase from a zero would be exactly the forbidden
target-dependent diagonal.

This file closes the scheduling gap without a divisor selection.  The actual
pure-imaginary Möbius columns are strongly continuous in `ell²`; dominated
convergence supplies the proof.  Contractive strong Sonin pullback therefore
converges uniformly on each compact phase window.  Applying those windows at
stage `j` to `[-j,j]` yields one cofinal depth sequence which carries every
real phase simultaneously.

It faithfully transports the explicit odd Fisher profile; it does not claim
that profile vanishes.  Thus the remaining Route P obstruction is a genuine
source-side sign/passivity estimate, not a missing source-only schedule.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- Pure imaginary logarithmic phase is strongly continuous in the actual
squarefree Möbius Hardy source. -/
theorem continuous_pureImag_complexDampedLp
    (sigma : ℝ) (hsigma : 1 < sigma) :
    Continuous (fun t : ℝ =>
      infiniteMobiusCriticalComplexDampedSignedWeightLp sigma (I * t) hsigma (by simp)) := by
  rw [continuous_iff_continuousAt]
  intro t0
  let D : ℝ → lp (fun _ : ℕ => ℂ) 2 := fun t =>
    infiniteMobiusCriticalComplexDampedSignedWeightLp sigma (I * t) hsigma (by simp)
  have hnorm (t : ℝ) (n : ℕ) :
      ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t) n‖ =
        ‖infiniteMobiusSignedWeight sigma n‖ := by
    rw [norm_infiniteMobiusCriticalComplexDampedSignedWeight]
    simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im, zero_mul, one_mul, sub_zero]
    simp [infiniteMobiusCriticalDampedSignedWeight]
  have hsq : Tendsto (fun t : ℝ => ‖D t - D t0‖ ^ (2 : ℕ)) (𝓝 t0) (𝓝 0) := by
    rw [show (fun t : ℝ => ‖D t - D t0‖ ^ (2 : ℕ)) = fun t : ℝ =>
      ∑' n : ℕ, ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t) n -
        infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t0) n‖ ^ (2 : ℕ) by
      funext t
      rw [HilbertSchmidt.lp_norm_sq_eq, lp.coeFn_sub]
      rfl]
    have htsum : Tendsto (fun t : ℝ => ∑' n : ℕ,
        ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t) n -
          infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t0) n‖ ^ (2 : ℕ))
        (𝓝 t0) (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
      apply tendsto_tsum_of_dominated_convergence
        (𝓕 := 𝓝 t0)
        (f := fun (t : ℝ) n =>
          ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t) n -
            infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t0) n‖ ^ (2 : ℕ))
        (g := fun _ : ℕ => (0 : ℝ))
        (bound := fun n => 4 * ‖infiniteMobiusSignedWeight sigma n‖ ^ (2 : ℕ))
      · exact (summable_norm_sq_infiniteMobiusSignedWeight hsigma).mul_left 4
      · intro n
        have hcont : Continuous (fun t : ℝ =>
            infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t) n) := by
          unfold infiniteMobiusCriticalComplexDampedSignedWeight
          simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
            zero_mul, one_mul, sub_zero,
            infiniteMobiusCriticalDampedSignedWeight, neg_zero, Real.exp_zero,
            ofReal_one, one_mul]
          fun_prop
        have hzero : ContinuousAt (fun t : ℝ =>
            ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t) n -
              infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t0) n‖ ^ (2 : ℕ)) t0 :=
          (hcont.continuousAt.sub continuousAt_const).norm.pow 2
        simpa using hzero.tendsto
      · filter_upwards with t n
        have hsub := norm_sub_le
          (infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t) n)
          (infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t0) n)
        rw [hnorm t n, hnorm t0 n] at hsub
        have hnonneg : 0 ≤ ‖infiniteMobiusSignedWeight sigma n‖ := norm_nonneg _
        have hsub' :
            ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t) n -
                infiniteMobiusCriticalComplexDampedSignedWeight sigma (I * t0) n‖ ≤
              2 * ‖infiniteMobiusSignedWeight sigma n‖ := by
          linarith
        have hright : 0 ≤ 2 * ‖infiniteMobiusSignedWeight sigma n‖ := by positivity
        have hsquare := sq_le_sq₀ (norm_nonneg _) hright |>.mpr hsub'
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        calc
          _ ≤ (2 * ‖infiniteMobiusSignedWeight sigma n‖) ^ (2 : ℕ) := hsquare
          _ = 4 * ‖infiniteMobiusSignedWeight sigma n‖ ^ (2 : ℕ) := by ring
    simpa using htsum
  have hnormZero : Tendsto (fun t : ℝ => ‖D t - D t0‖) (𝓝 t0) (𝓝 0) := by
    have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (‖D t - D t0‖ ^ (2 : ℕ)))
        (𝓝 t0) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero]
      using hsqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun t : ℝ => ‖D t - D t0‖) (𝓝 t0) (𝓝 0)
  exact hnormZero

/-- Contractive strong Sonin pullback is uniformly accurate on every compact
continuous source family. -/
theorem exists_soninPullback_uniformOn_compact
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (K : Set ℝ) (hK : IsCompact K)
    (phi : ℝ → MobiusClockSourceL2) (hphi : Continuous phi)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ M : ℕ, ∀ N ≥ M, ∀ t ∈ K,
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi t) - phi t‖ < epsilon := by
  have hpoint (t : ℝ) : ∃ N : ℕ, ∀ n ≥ N,
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr n (phi t) - phi t‖ <
        epsilon / 3 := by
    have hstrong := tendsto_norm_soninCofinalPositiveSourcePullback_sub
      a c d r ha hc hcd hda hr harc (phi t)
    rw [Metric.tendsto_atTop] at hstrong
    obtain ⟨N, hN⟩ := hstrong (epsilon / 3) (div_pos hepsilon (by norm_num))
    refine ⟨N, fun n hn => ?_⟩
    simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using hN n hn
  choose cutoff hcutoff using hpoint
  let U : ℝ → Set ℝ := fun t => phi ⁻¹' Metric.ball (phi t) (epsilon / 3)
  have hUopen (t : ℝ) : IsOpen (U t) := by
    exact Metric.isOpen_ball.preimage hphi
  have hcover : K ⊆ ⋃ t, U t := by
    intro t ht
    apply Set.mem_iUnion.mpr
    refine ⟨t, ?_⟩
    change dist (phi t) (phi t) < epsilon / 3
    simpa using div_pos hepsilon (by norm_num : (0 : ℝ) < 3)
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hUopen hcover
  refine ⟨S.sup cutoff, ?_⟩
  intro N hN t ht
  have htcover : t ∈ ⋃ s ∈ S, U s := hS ht
  rcases Set.mem_iUnion.mp htcover with ⟨s, htcover⟩
  rcases Set.mem_iUnion.mp htcover with ⟨hsS, htU⟩
  have hcut :
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi s) - phi s‖ <
        epsilon / 3 :=
    hcutoff s N ((Finset.le_sup hsS).trans hN)
  change dist (phi t) (phi s) < epsilon / 3 at htU
  rw [dist_eq_norm] at htU
  have hrev : ‖phi s - phi t‖ < epsilon / 3 := by
    rw [norm_sub_rev]
    exact htU
  calc
    ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi t) - phi t‖ =
        ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi t - phi s) +
          ((soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi s) - phi s) +
            (phi s - phi t))‖ := by
      rw [map_sub]
      congr 1
      abel
    _ ≤ ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi t - phi s)‖ +
          (‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi s) - phi s‖ +
            ‖phi s - phi t‖) := by
      calc
        _ ≤ ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi t - phi s)‖ +
            ‖(soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi s) - phi s) +
              (phi s - phi t)‖ := norm_add_le _ _
        _ ≤ _ := add_le_add_right (norm_add_le _ _) _
    _ = ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi t - phi s)‖ +
          ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (phi s) - phi s‖ +
          ‖phi s - phi t‖ := by ring
    _ ≤ ‖phi t - phi s‖ + epsilon / 3 + epsilon / 3 := by
      exact add_le_add
        (add_le_add
          (norm_soninCofinalPositiveSourcePullback_apply_le
            a c d r hc hcd hr N (phi t - phi s)) hcut.le) hrev.le
    _ < epsilon := by linarith

/-- One source-defined cofinal Sonin schedule carries the complex Fisher
coefficient for every real phase.  No Xi zero or divisor copy is selected. -/
theorem exists_soninCofinalCriticalComplexFisherScore_allPhase_diagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c) :
    ∃ Nseq : ℕ → ℕ, (∀ j, j < Nseq j) ∧ ∀ t : ℝ,
      Tendsto (fun j =>
        soninCofinalCriticalComplexFisherScore a c d r hc hcd hr (I * t) (by simp)
          j (Nseq j)) atTop (nhds (2 * (I * t) / (1 + I * t) ^ (2 : ℕ))) := by
  let sigma : ℕ → ℝ := soninMobiusCriticalSigmaSequence
  let F : ℕ → MobiusClockSourceL2 := fun j =>
    infiniteMobiusCriticalFisherTangentLp (sigma j)
      (soninMobiusCriticalSigmaSequence_gt_one j)
  let D : ℕ → ℝ → MobiusClockSourceL2 := fun j t =>
    infiniteMobiusCriticalComplexDampedSignedWeightLp (sigma j) (I * t)
      (soninMobiusCriticalSigmaSequence_gt_one j) (by simp)
  let delta : ℕ → ℝ := fun j =>
    1 / ((j + 1 : ℝ) * (‖F j‖ + 1))
  have hdelta (j : ℕ) : 0 < delta j := by
    dsimp [delta]
    positivity
  have hwindow (j : ℕ) : ∃ M : ℕ, ∀ N ≥ M, ∀ t ∈ Set.Icc (-(j : ℝ)) (j : ℝ),
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (D j t) - D j t‖ <
        delta j := by
    exact exists_soninPullback_uniformOn_compact
      a c d r ha hc hcd hda hr harc
      (Set.Icc (-(j : ℝ)) (j : ℝ)) isCompact_Icc (D j)
      (continuous_pureImag_complexDampedLp (sigma j)
        (soninMobiusCriticalSigmaSequence_gt_one j))
      (hdelta j)
  choose M hM using hwindow
  let Nseq : ℕ → ℕ := fun j => max (M j) (j + 1)
  have hcofinal (j : ℕ) : j < Nseq j := by
    exact lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)
  have hscore (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-(j : ℝ)) (j : ℝ)) :
      dist (soninCofinalCriticalComplexFisherScore a c d r hc hcd hr (I * t) (by simp)
          j (Nseq j)) (inner ℂ (F j) (D j t)) < 1 / (j + 1 : ℝ) := by
    have htransport :
        ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (D j t) -
            D j t‖ < delta j :=
      hM j (Nseq j) (le_max_left _ _) t ht
    rw [soninCofinalCriticalComplexFisherScore,
      inner_soninCofinalSourceCorner_eq_pullback, dist_eq_norm, ← inner_sub_right]
    calc
      ‖inner ℂ (F j)
          (soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (D j t) -
            D j t)‖ ≤ ‖F j‖ *
          ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (D j t) -
            D j t‖ := norm_inner_le_norm _ _
      _ ≤ ‖F j‖ * delta j := by
        exact mul_le_mul_of_nonneg_left htransport.le (norm_nonneg _)
      _ < 1 / (j + 1 : ℝ) := by
        have hJ : 0 < (j + 1 : ℝ) := by positivity
        have hF : 0 < ‖F j‖ + 1 := by positivity
        dsimp [delta]
        calc
          ‖F j‖ * (1 / ((j + 1 : ℝ) * (‖F j‖ + 1))) =
              (‖F j‖ / (‖F j‖ + 1)) * (1 / (j + 1 : ℝ)) := by
            field_simp
          _ < 1 * (1 / (j + 1 : ℝ)) := by
            exact mul_lt_mul_of_pos_right
              ((div_lt_one₀ hF).2 (by linarith [norm_nonneg (F j)]))
              (one_div_pos.mpr hJ)
          _ = 1 / (j + 1 : ℝ) := by ring
  refine ⟨Nseq, hcofinal, ?_⟩
  intro t
  have hsource : Tendsto (fun j => inner ℂ (F j) (D j t)) atTop
      (nhds (2 * (I * t) / (1 + I * t) ^ (2 : ℕ))) := by
    simpa only [F, D, sigma] using
      tendsto_inner_fisherTangent_complexDamped_criticalSequence (u := I * t) (by simp)
  rw [Metric.tendsto_atTop] at hsource ⊢
  intro epsilon hepsilon
  obtain ⟨Jsource, hsource⟩ := hsource (epsilon / 2) (by linarith)
  have hinv : Tendsto (fun j : ℕ => 1 / (j + 1 : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_atTop] at hinv
  obtain ⟨Jinv, hJinv⟩ := hinv (epsilon / 2) (by linarith)
  obtain ⟨Jphase, hJphase⟩ := exists_nat_gt |t|
  refine ⟨max Jsource (max Jinv Jphase), fun j hj => ?_⟩
  have hjSource : Jsource ≤ j := le_trans (le_max_left _ _) hj
  have hjInv : Jinv ≤ j := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hj)
  have hjPhase : Jphase ≤ j := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hj)
  have habs : |t| ≤ (j : ℝ) := by
    exact (le_of_lt hJphase).trans (by exact_mod_cast hjPhase)
  have htwindow : t ∈ Set.Icc (-(j : ℝ)) (j : ℝ) := by
    constructor <;> linarith [neg_le_abs t, le_abs_self t]
  have hscore' := hscore j htwindow
  have hscoreSmall :
      dist (soninCofinalCriticalComplexFisherScore a c d r hc hcd hr (I * t) (by simp)
        j (Nseq j)) (inner ℂ (F j) (D j t)) < epsilon / 2 := by
    have hinvSmall := hJinv j hjInv
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at hinvSmall
    exact hscore'.trans_le hinvSmall.le
  have hsourceSmall : dist (inner ℂ (F j) (D j t))
      (2 * (I * t) / (1 + I * t) ^ (2 : ℕ)) < epsilon / 2 := hsource j hjSource
  calc
    dist (soninCofinalCriticalComplexFisherScore a c d r hc hcd hr (I * t) (by simp)
        j (Nseq j)) (2 * (I * t) / (1 + I * t) ^ (2 : ℕ)) ≤
        dist (soninCofinalCriticalComplexFisherScore a c d r hc hcd hr (I * t) (by simp)
          j (Nseq j)) (inner ℂ (F j) (D j t)) +
          dist (inner ℂ (F j) (D j t)) (2 * (I * t) / (1 + I * t) ^ (2 : ℕ)) :=
      dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hscoreSmall hsourceSmall
    _ = epsilon := by ring

/-- One source-defined cofinal schedule also carries the limiting Fisher profile through the
literal reporter-selected source vector at every imaginary phase.  Unlike the Sonin score, this
uniformity needs no compact phase window: phase enters the reporter only through a contractive
arithmetic clock, while the pulled-back source column itself is phase-free. -/
theorem exists_soninCofinalCriticalComplexReporter_allPhase_diagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c) :
    ∃ Nseq : ℕ → ℕ, (∀ j, j < Nseq j) ∧ ∀ t : ℝ,
      Tendsto (fun j =>
        inner ℂ
          (infiniteMobiusCriticalFisherTangentLp
            (soninMobiusCriticalSigmaSequence j)
            (soninMobiusCriticalSigmaSequence_gt_one j))
          (mobiusCriticalComplexClockDamping
            (soninMobiusCriticalSigmaSequence j) (I * t)
            (soninMobiusCriticalSigmaSequence_gt_one j) (by simp)
            (soninCofinalPulledBackMobiusSourceVector
              a c d r hc hcd hr (Nseq j)
              (soninMobiusCriticalSigmaSequence j)
              (soninMobiusCriticalSigmaSequence_gt_one j))))
        atTop (nhds (2 * (I * t) / (1 + I * t) ^ (2 : ℕ))) := by
  let sigma : ℕ → ℝ := soninMobiusCriticalSigmaSequence
  let F : ℕ → MobiusClockSourceL2 := fun j =>
    infiniteMobiusCriticalFisherTangentLp (sigma j)
      (soninMobiusCriticalSigmaSequence_gt_one j)
  let x : ℕ → MobiusClockSourceL2 := fun j =>
    infiniteMobiusSignedWeightLp (sigma j)
      (soninMobiusCriticalSigmaSequence_gt_one j)
  let delta : ℕ → ℝ := fun j =>
    1 / ((j + 1 : ℝ) * (‖F j‖ + 1))
  have hdelta (j : ℕ) : 0 < delta j := by
    dsimp [delta]
    positivity
  have hpoint (j : ℕ) : ∃ M : ℕ, ∀ N ≥ M,
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N (x j) - x j‖ < delta j := by
    have hstrong := tendsto_norm_soninCofinalPositiveSourcePullback_sub
      a c d r ha hc hcd hda hr harc (x j)
    rw [Metric.tendsto_atTop] at hstrong
    obtain ⟨M, hM⟩ := hstrong (delta j) (hdelta j)
    refine ⟨M, fun N hN => ?_⟩
    simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using hM N hN
  choose M hM using hpoint
  let Nseq : ℕ → ℕ := fun j => max (M j) (j + 1)
  have hcofinal (j : ℕ) : j < Nseq j := by
    exact lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)
  have herror (j : ℕ) :
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j) - x j‖ <
        delta j :=
    hM j (Nseq j) (le_max_left _ _)
  refine ⟨Nseq, hcofinal, ?_⟩
  intro t
  let S : ℕ → MobiusClockSourceL2 →L[ℂ] MobiusClockSourceL2 := fun j =>
    mobiusCriticalComplexClockDamping (sigma j) (I * t)
      (soninMobiusCriticalSigmaSequence_gt_one j) (by simp)
  have hsource : Tendsto (fun j => inner ℂ (F j) (S j (x j))) atTop
      (nhds (2 * (I * t) / (1 + I * t) ^ (2 : ℕ))) := by
    change Tendsto (fun j => inner ℂ
      (infiniteMobiusCriticalFisherTangentLp (sigma j)
        (soninMobiusCriticalSigmaSequence_gt_one j))
      (mobiusCriticalComplexClockDamping (sigma j) (I * t)
        (soninMobiusCriticalSigmaSequence_gt_one j) (by simp)
        (infiniteMobiusSignedWeightLp (sigma j)
          (soninMobiusCriticalSigmaSequence_gt_one j)))) atTop _
    simp_rw [mobiusCriticalComplexClockDamping_apply_source]
    simpa only [sigma] using
      tendsto_inner_fisherTangent_complexDamped_criticalSequence (u := I * t) (by simp)
  have hsmall (j : ℕ) :
      dist
          (inner ℂ (F j) (S j
            (soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j))))
          (inner ℂ (F j) (S j (x j))) < 1 / (j + 1 : ℝ) := by
    rw [dist_eq_norm, ← inner_sub_right, ← map_sub]
    calc
      ‖inner ℂ (F j) (S j
          (soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j) - x j))‖ ≤
          ‖F j‖ * ‖S j
            (soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j) - x j)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖F j‖ * (‖S j‖ *
          ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j) - x j‖) := by
        exact mul_le_mul_of_nonneg_left ((S j).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖F j‖ * (1 * delta j) := by
        apply mul_le_mul_of_nonneg_left
        exact (show ‖S j‖ *
            ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j) - x j‖ <
              1 * delta j from by
          calc
            ‖S j‖ * ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j) - x j‖ ≤
                1 * ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j) - x j‖ :=
              mul_le_mul_of_nonneg_right
                (norm_mobiusCriticalComplexClockDamping_le_one
                  (sigma j) (I * t)
                  (soninMobiusCriticalSigmaSequence_gt_one j) (by simp))
                (norm_nonneg _)
            _ < 1 * delta j := by simpa using herror j
            _ = 1 * delta j := rfl).le
        exact norm_nonneg _
      _ = ‖F j‖ * delta j := by ring
      _ < 1 / (j + 1 : ℝ) := by
        have hJ : 0 < (j + 1 : ℝ) := by positivity
        have hF : 0 < ‖F j‖ + 1 := by positivity
        dsimp [delta]
        calc
          ‖F j‖ * (1 / ((j + 1 : ℝ) * (‖F j‖ + 1))) =
              (‖F j‖ / (‖F j‖ + 1)) * (1 / (j + 1 : ℝ)) := by
            field_simp
          _ < 1 * (1 / (j + 1 : ℝ)) := by
            exact mul_lt_mul_of_pos_right
              ((div_lt_one₀ hF).2 (by linarith [norm_nonneg (F j)]))
              (one_div_pos.mpr hJ)
          _ = 1 / (j + 1 : ℝ) := by ring
  rw [Metric.tendsto_atTop] at hsource ⊢
  intro epsilon hepsilon
  obtain ⟨Jsource, hsource⟩ := hsource (epsilon / 2) (by linarith)
  have hinv : Tendsto (fun j : ℕ => 1 / (j + 1 : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_atTop] at hinv
  obtain ⟨Jinv, hJinv⟩ := hinv (epsilon / 2) (by linarith)
  refine ⟨max Jsource Jinv, fun j hj => ?_⟩
  have hjSource : Jsource ≤ j := le_trans (le_max_left _ _) hj
  have hjInv : Jinv ≤ j := le_trans (le_max_right _ _) hj
  have hsmall' := hsmall j
  have hsmallEpsilon : dist
      (inner ℂ (F j) (S j
        (soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j))))
      (inner ℂ (F j) (S j (x j))) < epsilon / 2 := by
    have hinvSmall := hJinv j hjInv
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at hinvSmall
    exact hsmall'.trans_le hinvSmall.le
  have hsourceSmall : dist (inner ℂ (F j) (S j (x j)))
      (2 * (I * t) / (1 + I * t) ^ (2 : ℕ)) < epsilon / 2 := hsource j hjSource
  calc
    dist (inner ℂ (F j) (S j
          (soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j))))
        (2 * (I * t) / (1 + I * t) ^ (2 : ℕ)) ≤
        dist (inner ℂ (F j) (S j
          (soninCofinalPositiveSourcePullback a c d r hc hcd hr (Nseq j) (x j))))
          (inner ℂ (F j) (S j (x j))) +
        dist (inner ℂ (F j) (S j (x j)))
          (2 * (I * t) / (1 + I * t) ^ (2 : ℕ)) := dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hsmallEpsilon hsourceSmall
    _ = epsilon := by ring

end RHTower
