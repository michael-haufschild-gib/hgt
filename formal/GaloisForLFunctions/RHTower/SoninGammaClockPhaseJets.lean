import GaloisForLFunctions.RHTower.SoninGammaClockHardyPhase
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# All-order admission of the original Gamma clock phase

Every positive source moment is integrable. A common derivative kernel covers
both the full compensated odd source and every retained measurable subset.
The difference between the actual full Hardy lift and its literal finite clock
cutoff is exactly the integral over the discarded source. All of its derivatives
are globally bounded by a fixed quadratic height weight times a discarded moment;
every such coefficient vanishes along the original cofinal endpoints.

This proves smooth source admission with polynomially weighted jet errors.
Exponential Schwartz convergence, the resulting tested nuclear limit, joint
arithmetic completion, and the TG sub-unit law are separate obligations.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology
namespace RHTower

/-- Every positive clock moment of the literal Gamma density is integrable. -/
theorem gammaClock_moment_integrable (n : ℕ) :
    IntegrableOn (fun u => u^(n+1)*ccmPublishedArchimedeanDensity u) (Ioi 0) := by
  have hi : IntegrableOn (fun u : ℝ => u^n*Real.exp (-u/4)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (n:ℝ)) (p := 1) (b := 1/4)
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num) (by norm_num)
    simp only [Real.rpow_one, Real.rpow_natCast] at h
    convert h using 1
    ext u
    congr 2
    ring
  have hm : AEStronglyMeasurable
      (fun u => u^(n+1)*ccmPublishedArchimedeanDensity u) volume := by
    apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    fun_prop
  apply (hi.const_mul 4).mono' hm.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (pow_pos hu _) (gammaClock_density_pos hu))]
  calc
    _ = u^n*(u*ccmPublishedArchimedeanDensity u) := by rw [pow_succ]; ring
    _ ≤ u^n*(4*Real.exp (-u/4)) :=
      mul_le_mul_of_nonneg_left (gammaClock_firstMoment_bound hu) (pow_nonneg hu.le _)
    _ = _ := by ring

/-- Exact real derivatives of the compensated odd clock kernel. -/
def gammaClockOddJetKernel : ℕ → ℝ → ℝ → ℝ
  | 0, t, u => (t*u-Real.sin (t*u))*ccmPublishedArchimedeanDensity u/u
  | 1, t, u => (1-Real.cos (t*u))*ccmPublishedArchimedeanDensity u
  | n+2, t, u => u^(n+1)*Real.sin (t*u+(n:ℝ)*Real.pi/2)*ccmPublishedArchimedeanDensity u

private theorem jet_measurable (n : ℕ) (t : ℝ) :
    Measurable (gammaClockOddJetKernel n t) := by
  rcases n with _ | (_ | n) <;> unfold gammaClockOddJetKernel ccmPublishedArchimedeanDensity <;>
    fun_prop

/-- The zeroth compensated source is controlled by its first clock moment. -/
theorem gammaClockOddJetKernel_zero_bound (t : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖gammaClockOddJetKernel 0 t u‖ ≤ 2*t^2*(u*ccmPublishedArchimedeanDensity u) := by
  rw [gammaClockOddJetKernel, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (gammaClock_density_pos hu), abs_of_pos hu]
  calc
    _ ≤ (2*(t*u)^2)*ccmPublishedArchimedeanDensity u/u :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (gammaClock_sine_remainder_bound (t*u))
          (gammaClock_density_pos hu).le) hu.le
    _ = _ := by field_simp [ne_of_gt hu]

/-- All higher clock jets are bounded by their corresponding source moments. -/
theorem gammaClockOddJetKernel_succ_succ_bound (n : ℕ) (t : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖gammaClockOddJetKernel (n+2) t u‖ ≤ u^(n+1)*ccmPublishedArchimedeanDensity u := by
  rw [gammaClockOddJetKernel, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (gammaClock_density_pos hu), abs_of_pos (pow_pos hu _)]
  calc
    _ ≤ u^(n+1)*1*ccmPublishedArchimedeanDensity u :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (pow_nonneg hu.le _))
        (gammaClock_density_pos hu).le
    _ = _ := by ring

/-- Every jet of the original compensated kernel is integrable. -/
theorem gammaClockOddJetKernel_integrable (n : ℕ) (t : ℝ) :
    IntegrableOn (gammaClockOddJetKernel n t) (Ioi 0) := by
  rcases n with _ | (_ | n)
  · exact gammaClockOddRemainder_integrable t
  · apply (gammaClock_firstMoment_integrable.const_mul |t|).mono'
      (jet_measurable 1 t).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact gammaClock_cosine_bound |t| t u le_rfl hu
  · apply (gammaClock_moment_integrable n).mono'
      (jet_measurable (n+2) t).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact gammaClockOddJetKernel_succ_succ_bound n t hu

/-- The displayed source jets are actual successive derivatives. -/
theorem hasDerivAt_gammaClockOddJetKernel (n : ℕ) (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x => gammaClockOddJetKernel n x u)
      (gammaClockOddJetKernel (n+1) t u) t := by
  rcases n with _ | (_ | n)
  · have hh := ((((hasDerivAt_id t).mul_const u).sub
        ((Real.hasDerivAt_sin (t*u)).comp t ((hasDerivAt_id t).mul_const u))).mul_const
          (ccmPublishedArchimedeanDensity u)).div_const u
    convert! hh using 1
    dsimp [gammaClockOddJetKernel]
    field_simp [ne_of_gt hu]
  · have hh := ((hasDerivAt_const t (1:ℝ)).sub
      ((Real.hasDerivAt_cos (t*u)).comp t ((hasDerivAt_id t).mul_const u))).mul_const
        (ccmPublishedArchimedeanDensity u)
    convert! hh using 1
    simp only [gammaClockOddJetKernel, Nat.cast_zero, zero_mul, zero_div, add_zero]
    ring
  · have hx := ((hasDerivAt_id t).mul_const u).add_const ((n:ℝ)*Real.pi/2)
    have hh := (((Real.hasDerivAt_sin (t*u+(n:ℝ)*Real.pi/2)).comp t hx).const_mul
      (u^(n+1))).mul_const (ccmPublishedArchimedeanDensity u)
    convert! hh using 1
    dsimp [gammaClockOddJetKernel]
    have he : t*u+((n+1:ℕ):ℝ)*Real.pi/2 = (t*u+(n:ℝ)*Real.pi/2)+Real.pi/2 := by
      push_cast
      ring
    rw [he, Real.sin_add_pi_div_two, pow_succ]
    ring

/-- Source integral of a clock jet over any retained part of the original half-line. -/
def gammaClockOddIntegralJet (s : Set ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ u in s, gammaClockOddJetKernel n t u

/-- Differentiation of the original source is valid to every order. -/
theorem hasDerivAt_gammaClockOddIntegralJet {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Ioi 0) (n : ℕ) (t : ℝ) :
    HasDerivAt (gammaClockOddIntegralJet s n) (gammaClockOddIntegralJet s (n+1) t) t := by
  have hmem : ∀ᵐ u ∂volume.restrict s, 0 < u :=
    (ae_restrict_mem hs).mono (fun u hu => hsub hu)
  have hi := (gammaClockOddJetKernel_integrable n t).mono_set hsub
  have hm (k : ℕ) (x : ℝ) : AEStronglyMeasurable (gammaClockOddJetKernel k x) (volume.restrict s) :=
    (jet_measurable k x).aestronglyMeasurable.restrict
  cases n with
  | zero =>
    let C := |t|+1
    have hn : Ioo (-C) C ∈ 𝓝 t := Ioo_mem_nhds
      (by dsimp [C]; linarith [neg_abs_le t]) (by dsimp [C]; linarith [le_abs_self t])
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x u => gammaClockOddJetKernel 0 x u)
      (F' := fun x u => gammaClockOddJetKernel 1 x u)
      (bound := fun u => C*(u*ccmPublishedArchimedeanDensity u)) hn
      (Eventually.of_forall (hm 0)) hi (hm 1 t)
      (by filter_upwards [hmem] with u hu; intro x hx
          exact gammaClock_cosine_bound C x u (abs_le.mpr ⟨hx.1.le,hx.2.le⟩) hu)
      ((gammaClock_firstMoment_integrable.mono_set hsub).const_mul C)
      (by filter_upwards [hmem] with u hu; intro x _
          exact hasDerivAt_gammaClockOddJetKernel 0 x hu)).2
  | succ n =>
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x u => gammaClockOddJetKernel (n+1) x u)
      (F' := fun x u => gammaClockOddJetKernel (n+2) x u)
      (bound := fun u => u^(n+1)*ccmPublishedArchimedeanDensity u)
      (s := univ) (univ_mem)
      (Eventually.of_forall (hm (n+1))) hi (hm (n+2) t)
      (by filter_upwards [hmem] with u hu; intro x _
          exact gammaClockOddJetKernel_succ_succ_bound n x hu)
      ((gammaClock_moment_integrable n).mono_set hsub)
      (by filter_upwards [hmem] with u hu; intro x _
          exact hasDerivAt_gammaClockOddJetKernel (n+1) x hu)).2

/-- The integral jet family agrees with iterated derivatives of its original primitive. -/
theorem iteratedDeriv_gammaClockOddIntegralJet {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Ioi 0) (n : ℕ) :
    iteratedDeriv n (gammaClockOddIntegralJet s 0) = gammaClockOddIntegralJet s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_gammaClockOddIntegralJet hs hsub n t).deriv


/-- Every retained original clock primitive is smooth. -/
theorem contDiff_gammaClockOddIntegralJet {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Ioi 0) :
    ContDiff ℝ (⊤ : ℕ∞) (gammaClockOddIntegralJet s 0) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [iteratedDeriv_gammaClockOddIntegralJet hs hsub]
  exact fun t => (hasDerivAt_gammaClockOddIntegralJet hs hsub n t).differentiableAt

/-- Mass of the discarded part of the original positive clock moment. -/
def gammaClockDiscardedMoment (n : ℕ) (ε R : ℝ) : ℝ :=
  ∫ u in Ioi (0:ℝ) \ Icc ε R, u^(n+1)*ccmPublishedArchimedeanDensity u

/-- Discarded clock moments are nonnegative for every finite cutoff. -/
theorem gammaClockDiscardedMoment_nonneg (n : ℕ) (ε R : ℝ) :
    0 ≤ gammaClockDiscardedMoment n ε R := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff measurableSet_Icc)] with u hu
  exact mul_nonneg (pow_nonneg hu.1.le _) (gammaClock_density_pos hu.1).le

/-- Cofinal removal of the original endpoints discards vanishing mass at every order. -/
theorem gammaClockDiscardedMoment_tendsto (n : ℕ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) :
    Tendsto (fun i => gammaClockDiscardedMoment n (ε i) (R i)) l (𝓝 0) := by
  have hc : AECover (volume.restrict (Ioi (0:ℝ))) l (fun i => Icc (ε i) (R i)) :=
    (aecover_Ioi_of_Ici (hε.mono_right nhdsWithin_le_nhds)).inter (aecover_Iic hR)
  have ht := hc.integral_tendsto_of_countably_generated (gammaClock_moment_integrable n)
  have hd := (tendsto_const_nhds (x := ∫ u in Ioi (0:ℝ),
    u^(n+1)*ccmPublishedArchimedeanDensity u)).sub ht
  simp only [sub_self] at hd
  apply hd.congr'
  filter_upwards [hε.eventually self_mem_nhdsWithin] with i hi
  have hsub : Icc (ε i) (R i) ⊆ Ioi 0 := fun u hu => lt_of_lt_of_le hi hu.1
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub]
  exact (setIntegral_sdiff measurableSet_Icc (gammaClock_moment_integrable n) hsub).symm

/-- The full Hardy lift is smooth as the original compensated clock source. -/
theorem contDiff_gammaClockHardyPhaseLift : ContDiff ℝ (⊤ : ℕ∞) gammaClockHardyPhaseLift :=
  (contDiff_id.mul contDiff_const).add
    (contDiff_gammaClockOddIntegralJet measurableSet_Ioi Subset.rfl)

/-- Every literal positive-endpoint cutoff gives a smooth Hardy lift. -/
theorem contDiff_gammaClockHardyPhaseCutoff {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => gammaClockHardyPhaseCutoff t ε R) :=
  (contDiff_id.mul contDiff_const).add
    (contDiff_gammaClockOddIntegralJet measurableSet_Icc (fun _ hu => lt_of_lt_of_le hε hu.1))

/-- Exact source identity: the phase error is the discarded compensated clock integral. -/
theorem gammaClockHardyPhase_error_eq_tail {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    (fun t => gammaClockHardyPhaseLift t-gammaClockHardyPhaseCutoff t ε R) =
      gammaClockOddIntegralJet (Ioi (0:ℝ) \ Icc ε R) 0 := by
  funext t
  unfold gammaClockHardyPhaseLift gammaClockHardyPhaseCutoff gammaClockOddRemainder
    gammaClockOddIntegralJet gammaClockOddJetKernel
  rw [setIntegral_sdiff measurableSet_Icc (gammaClockOddRemainder_integrable t)
    (show Icc ε R ⊆ Ioi 0 from fun _ hu => lt_of_lt_of_le hε hu.1)]
  ring

/-- All phase error derivatives retain exactly the discarded original source. -/
theorem iteratedDeriv_gammaClockHardyPhase_error {ε : ℝ} (hε : 0 < ε) (R : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => gammaClockHardyPhaseLift t-gammaClockHardyPhaseCutoff t ε R) =
      gammaClockOddIntegralJet (Ioi (0:ℝ) \ Icc ε R) n := by
  rw [gammaClockHardyPhase_error_eq_tail hε R]
  exact iteratedDeriv_gammaClockOddIntegralJet
    (measurableSet_Ioi.diff measurableSet_Icc) sdiff_subset n

/-- Global quadratic control of the original phase error by discarded source mass. -/
theorem gammaClockHardyPhase_error_bound {ε : ℝ} (hε : 0 < ε) (R t : ℝ) :
    ‖gammaClockHardyPhaseLift t-gammaClockHardyPhaseCutoff t ε R‖ ≤
      2*t^2*gammaClockDiscardedMoment 0 ε R := by
  have he := congrFun (gammaClockHardyPhase_error_eq_tail hε R) t
  rw [he]
  have hb := norm_integral_le_of_norm_le
    ((gammaClock_firstMoment_integrable.mono_set
      (show Ioi (0:ℝ) \ Icc ε R ⊆ Ioi 0 from sdiff_subset)).const_mul (2*t^2))
    (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff measurableSet_Icc)] with u hu
      exact gammaClockOddJetKernel_zero_bound t hu.1)
  simpa only [gammaClockOddIntegralJet, gammaClockDiscardedMoment, integral_const_mul,
    zero_add, pow_one] using hb

/-- Global linear control of the first phase error derivative. -/
theorem gammaClockHardyPhase_error_deriv_bound {ε : ℝ} (hε : 0 < ε) (R t : ℝ) :
    ‖iteratedDeriv 1 (fun x => gammaClockHardyPhaseLift x-gammaClockHardyPhaseCutoff x ε R) t‖ ≤
      |t| *gammaClockDiscardedMoment 0 ε R := by
  rw [iteratedDeriv_gammaClockHardyPhase_error hε R]
  have hb := norm_integral_le_of_norm_le
    ((gammaClock_firstMoment_integrable.mono_set
      (show Ioi (0:ℝ) \ Icc ε R ⊆ Ioi 0 from sdiff_subset)).const_mul |t|)
    (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff measurableSet_Icc)] with u hu
      exact gammaClock_cosine_bound |t| t u le_rfl hu.1)
  simpa only [gammaClockOddIntegralJet, gammaClockOddJetKernel, gammaClockDiscardedMoment,
    integral_const_mul, zero_add, pow_one] using hb

/-- Every higher phase error derivative is uniformly controlled by its discarded moment. -/
theorem gammaClockHardyPhase_error_iteratedDeriv_bound {ε : ℝ} (hε : 0 < ε)
    (R t : ℝ) (n : ℕ) :
    ‖iteratedDeriv (n+2) (fun x => gammaClockHardyPhaseLift x-gammaClockHardyPhaseCutoff x ε R) t‖ ≤
      gammaClockDiscardedMoment n ε R := by
  rw [iteratedDeriv_gammaClockHardyPhase_error hε R]
  exact norm_integral_le_of_norm_le
    ((gammaClock_moment_integrable n).mono_set
      (show Ioi (0:ℝ) \ Icc ε R ⊆ Ioi 0 from sdiff_subset))
    (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff measurableSet_Icc)] with u hu
      exact gammaClockOddJetKernel_succ_succ_bound n t hu.1)

/-- One vanishing coefficient controls a whole phase jet globally in height. -/
def gammaClockPhaseErrorMajorant : ℕ → ℝ → ℝ → ℝ
  | 0, ε, R => 2*gammaClockDiscardedMoment 0 ε R
  | 1, ε, R => gammaClockDiscardedMoment 0 ε R
  | n+2, ε, R => gammaClockDiscardedMoment n ε R

/-- The global phase error coefficients are nonnegative. -/
theorem gammaClockPhaseErrorMajorant_nonneg (n : ℕ) (ε R : ℝ) :
    0 ≤ gammaClockPhaseErrorMajorant n ε R := by
  rcases n with _ | (_ | n)
  · exact mul_nonneg (by norm_num) (gammaClockDiscardedMoment_nonneg 0 ε R)
  · exact gammaClockDiscardedMoment_nonneg 0 ε R
  · exact gammaClockDiscardedMoment_nonneg n ε R

/-- Every global phase error coefficient vanishes along the original cofinal cutoffs. -/
theorem gammaClockPhaseErrorMajorant_tendsto (n : ℕ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) :
    Tendsto (fun i => gammaClockPhaseErrorMajorant n (ε i) (R i)) l (𝓝 0) := by
  rcases n with _ | (_ | n)
  · simpa only [gammaClockPhaseErrorMajorant, mul_zero] using
      (gammaClockDiscardedMoment_tendsto 0 hε hR).const_mul 2
  · exact gammaClockDiscardedMoment_tendsto 0 hε hR
  · exact gammaClockDiscardedMoment_tendsto n hε hR

/-- All error derivatives are globally polynomially small, with vanishing source coefficients. -/
theorem gammaClockHardyPhase_error_weighted_bound (n : ℕ) {ε : ℝ} (hε : 0 < ε) (R t : ℝ) :
    ‖iteratedDeriv n (fun x => gammaClockHardyPhaseLift x-gammaClockHardyPhaseCutoff x ε R) t‖ ≤
      gammaClockPhaseErrorMajorant n ε R*(1+‖t‖)^2 := by
  have ht0 := norm_nonneg t
  have ht1 : 1 ≤ (1+‖t‖)^2 := one_le_pow₀ (by linarith)
  rcases n with _ | (_ | n)
  · have ht2 : t^2 ≤ (1+‖t‖)^2 := by rw [Real.norm_eq_abs]; nlinarith [sq_abs t, abs_nonneg t]
    exact (gammaClockHardyPhase_error_bound hε R t).trans (by
      simp only [gammaClockPhaseErrorMajorant]
      nlinarith [mul_le_mul_of_nonneg_left ht2 (gammaClockDiscardedMoment_nonneg 0 ε R)])
  · have ht2 : |t| ≤ (1+‖t‖)^2 := by rw [Real.norm_eq_abs]; nlinarith [sq_nonneg |t|, abs_nonneg t]
    exact (gammaClockHardyPhase_error_deriv_bound hε R t).trans (by
      simp only [gammaClockPhaseErrorMajorant]
      nlinarith [mul_le_mul_of_nonneg_left ht2 (gammaClockDiscardedMoment_nonneg 0 ε R)])
  · exact (gammaClockHardyPhase_error_iteratedDeriv_bound hε R t n).trans (by
      simp only [gammaClockPhaseErrorMajorant]
      nlinarith [mul_le_mul_of_nonneg_left ht1 (gammaClockDiscardedMoment_nonneg n ε R)])

/-- The exact discarded phase is a temperate multiplier; no source term is changed. -/
theorem gammaClockHardyPhase_error_hasTemperateGrowth {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    Function.HasTemperateGrowth
      (fun t => gammaClockHardyPhaseLift t-gammaClockHardyPhaseCutoff t ε R) := by
  refine ⟨contDiff_gammaClockHardyPhaseLift.sub (contDiff_gammaClockHardyPhaseCutoff hε R),
    fun n => ⟨2, gammaClockPhaseErrorMajorant n ε R, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact gammaClockHardyPhase_error_weighted_bound n hε R t

end RHTower
