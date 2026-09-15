import GaloisForLFunctions.RHTower.XiMassRapidityMassPhase
import GaloisForLFunctions.RHTower.XiMassCriticalTruePrimeCone
import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Two-rapidity geometry of mass-phase correlations

The diagonal restriction of a correlation between distinct mass frequencies has
phase `(h-k) sinh t`, hence is nonstationary.  This apparent cancellation does
not control the actual square of the rapidity integral: it has two independent
rapidity variables.  In the timelike region that full two-variable phase has a
stationary pair, one stationary rapidity for each frequency.  Therefore a
covariance proof needs a genuine diagonal-localization mechanism (or another
way to remove the stationary pair); pointwise diagonal cancellation alone is
not a bilinear estimate.
-/

namespace RHTower

noncomputable section

/-- Phase in the product of two mass rapidity modes, before any diagonal
restriction of the two rapidity variables. -/
def xiMassTwoRapidityCorrelationPhase (u h k t s : ℝ) : ℝ :=
  (u * Real.cosh t + h * Real.sinh t) -
    (u * Real.cosh s + k * Real.sinh s)

/-- Positive damping amplitude in the Hermitian product of two mass rapidity kernels. -/
def xiMassTwoRapidityCorrelationAmplitude (a sigma t s : ℝ) : ℂ :=
  ((Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t) *
      Real.cosh s * Real.exp (-(a * sigma) * Real.cosh s) : ℝ) : ℂ)

/-- **Literal two-rapidity attachment.** The Hermitian product of the actual mass rapidity
kernels has exactly the two-rapidity correlation phase. -/
theorem xiMassRapidityPhaseKernel_mul_star_eq_twoRapidityCorrelation
    (a sigma u h k t s : ℝ) :
    xiMassRapidityPhaseKernel a sigma u h t *
        (starRingEnd ℂ) (xiMassRapidityPhaseKernel a sigma u k s) =
      xiMassTwoRapidityCorrelationAmplitude a sigma t s *
        Complex.exp (-(Complex.I *
          ((a * xiMassTwoRapidityCorrelationPhase u h k t s : ℝ) : ℂ))) := by
  rw [xiMassRapidityPhaseKernel, xiMassRapidityPhaseKernel,
    xiMassTwoRapidityCorrelationAmplitude, xiMassTwoRapidityCorrelationPhase]
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  calc
    _ = ((Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t) *
          Real.cosh s * Real.exp (-(a * sigma) * Real.cosh s) : ℝ) : ℂ) *
        (Complex.exp (-(Complex.I *
          ((a * (u * Real.cosh t + h * Real.sinh t) : ℝ) : ℂ))) *
          Complex.exp (-(-Complex.I *
            ((a * (u * Real.cosh s + k * Real.sinh s) : ℝ) : ℂ)))) := by
      push_cast
      ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- **Literal two-rapidity covariance.** The Hermitian product of two actual mass
rapidity integrals is exactly the product-measure oscillatory integral whose phase is
`xiMassTwoRapidityCorrelationPhase`.  No diagonal substitution or cancellation estimate is
used here. -/
theorem xiMassRapidityPhaseKernel_integral_mul_star_eq_twoRapidityCorrelation
    (a sigma u h k : ℝ) :
    (∫ t : ℝ, xiMassRapidityPhaseKernel a sigma u h t) *
        (starRingEnd ℂ) (∫ s : ℝ, xiMassRapidityPhaseKernel a sigma u k s) =
      ∫ z : ℝ × ℝ, xiMassTwoRapidityCorrelationAmplitude a sigma z.1 z.2 *
        Complex.exp (-(Complex.I *
          ((a * xiMassTwoRapidityCorrelationPhase u h k z.1 z.2 : ℝ) : ℂ))) := by
  rw [← integral_conj, ← MeasureTheory.integral_prod_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  exact xiMassRapidityPhaseKernel_mul_star_eq_twoRapidityCorrelation
    a sigma u h k z.1 z.2

/-- The literal prime-cone coefficient of one rapidity mass kernel. -/
def xiMassCriticalPrimeConeRapidityWeight (a : ℝ) (k : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt (k + 2) : ℝ) : ℂ) *
    ((Real.exp (-Real.log ((k : ℝ) + 2) / 2) : ℝ) : ℂ) * (a : ℂ)

/-- The exact moving prime cone, before integration, in the rapidity variable. -/
def xiMassCriticalPrimeConeRapidityKernel (a sigma d u t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1),
    xiMassCriticalPrimeConeRapidityWeight a k *
      xiMassRapidityPhaseKernel a sigma u (Real.log ((k : ℝ) + 2)) t

/-- **Finite cone source attachment.** The actual moving prime cone is one rapidity integral.
The cutoff remains finite and mass-dependent; no limiting interchange is used. -/
theorem xiMassCriticalPrimeAtomConeSum_eq_integral_rapidityKernel
    {a sigma d u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    xiMassCriticalPrimeAtomConeSum a sigma d u =
      ∫ t : ℝ, xiMassCriticalPrimeConeRapidityKernel a sigma d u t := by
  unfold xiMassCriticalPrimeAtomConeSum xiMassCriticalPrimeConeRapidityKernel
  rw [MeasureTheory.integral_finsetSum _ (by
    intro k _
    exact (integrable_xiMassRapidityPhaseKernel ha hsigma).const_mul
      (xiMassCriticalPrimeConeRapidityWeight a k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [xiMassCriticalDampedFourierProfile_eq_integral_rapidityPhase ha hsigma,
    MeasureTheory.integral_const_mul]
  simp only [xiMassCriticalPrimeConeRapidityWeight]
  ring

/-- The finite prime-pair covariance integrand of the moving cone.  Every prime pair is retained
with its literal two-rapidity phase. -/
def xiMassCriticalPrimeConeTwoRapidityCovariance
    (a sigma d u t s : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1),
    ∑ l ∈ Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1),
      xiMassCriticalPrimeConeRapidityWeight a k *
        (starRingEnd ℂ) (xiMassCriticalPrimeConeRapidityWeight a l) *
          xiMassTwoRapidityCorrelationAmplitude a sigma t s *
            Complex.exp (-(Complex.I * ((a *
              xiMassTwoRapidityCorrelationPhase u
                (Real.log ((k : ℝ) + 2)) (Real.log ((l : ℝ) + 2)) t s : ℝ) : ℂ)))

/-- The product of finite prime-cone kernels expands exactly into the literal prime-pair
two-rapidity covariance. -/
theorem xiMassCriticalPrimeConeRapidityKernel_mul_star_eq_twoRapidityCovariance
    (a sigma d u t s : ℝ) :
    xiMassCriticalPrimeConeRapidityKernel a sigma d u t *
        (starRingEnd ℂ) (xiMassCriticalPrimeConeRapidityKernel a sigma d u s) =
      xiMassCriticalPrimeConeTwoRapidityCovariance a sigma d u t s := by
  unfold xiMassCriticalPrimeConeRapidityKernel
    xiMassCriticalPrimeConeTwoRapidityCovariance
  rw [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [map_mul]
  calc
    _ = (xiMassCriticalPrimeConeRapidityWeight a k *
        (starRingEnd ℂ) (xiMassCriticalPrimeConeRapidityWeight a l)) *
      (xiMassRapidityPhaseKernel a sigma u (Real.log ((k : ℝ) + 2)) t *
        (starRingEnd ℂ) (xiMassRapidityPhaseKernel a sigma u
          (Real.log ((l : ℝ) + 2)) s)) := by ring
    _ = _ := by
      rw [xiMassRapidityPhaseKernel_mul_star_eq_twoRapidityCorrelation]
      ring

/-- **Literal finite prime-pair covariance.** The Hermitian square of the exact moving
prime cone is the product-measure integral of its full finite prime-pair covariance.  This is an
identity, not a claimed cancellation or uniform bound. -/
theorem xiMassCriticalPrimeAtomConeSum_mul_star_eq_twoRapidityCovariance
    {a sigma d u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    xiMassCriticalPrimeAtomConeSum a sigma d u *
        (starRingEnd ℂ) (xiMassCriticalPrimeAtomConeSum a sigma d u) =
      ∫ z : ℝ × ℝ, xiMassCriticalPrimeConeTwoRapidityCovariance
        a sigma d u z.1 z.2 := by
  rw [xiMassCriticalPrimeAtomConeSum_eq_integral_rapidityKernel ha hsigma,
    ← integral_conj, ← MeasureTheory.integral_prod_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  exact xiMassCriticalPrimeConeRapidityKernel_mul_star_eq_twoRapidityCovariance
    a sigma d u z.1 z.2

/-- Stationarity equations for the two independent rapidities of a mass-mode
correlation. -/
def XiMassTwoRapidityCorrelationStationary (u h k t s : ℝ) : Prop :=
  u * Real.sinh t + h * Real.cosh t = 0 ∧
    u * Real.sinh s + k * Real.cosh s = 0

/-- On the artificial diagonal, the common timelike part cancels exactly. -/
theorem xiMassTwoRapidityCorrelationPhase_diagonal
    (u h k t : ℝ) :
    xiMassTwoRapidityCorrelationPhase u h k t t = (h - k) * Real.sinh t := by
  rw [xiMassTwoRapidityCorrelationPhase]
  ring

/-- The diagonal relative phase is nonstationary for distinct frequencies. -/
theorem hasDerivAt_xiMassTwoRapidityCorrelationPhase_diagonal
    (h k t : ℝ) :
    HasDerivAt (fun x : ℝ => (h - k) * Real.sinh x)
      ((h - k) * Real.cosh t) t := by
  simpa using (Real.hasDerivAt_sinh t).const_mul (h - k)

theorem xiMassTwoRapidityCorrelationPhase_diagonal_deriv_ne_zero
    {h k t : ℝ} (hhk : h ≠ k) :
    (h - k) * Real.cosh t ≠ 0 := by
  exact mul_ne_zero (sub_ne_zero.mpr hhk) (ne_of_gt (Real.cosh_pos t))

/-- **Two-rapidity stationary-pair obstruction.**  The unrestricted
two-variable correlation phase remains stationary throughout the timelike
region. -/
theorem exists_xiMassTwoRapidityCorrelationStationary
    {u h k : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hhu : h < u) (hku : k < u) :
    ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s := by
  refine ⟨-timelikeRapidity u h, -timelikeRapidity u k, ?_, ?_⟩
  · exact (massPhase_timelike_stationary_iff hu hh hhu _).mpr rfl
  · exact (massPhase_timelike_stationary_iff hu hk hku _).mpr rfl

/-- The stationary pair of two distinct frequencies is strictly off the
same-rapidity diagonal.  Thus an independently justified diagonal localization
would eliminate every off-diagonal timelike stationary pair. -/
theorem XiMassTwoRapidityCorrelationStationary.rapidities_ne_of_frequency_ne
    {u h k t s : ℝ} (hstat : XiMassTwoRapidityCorrelationStationary u h k t s)
    (hhk : h ≠ k) : t ≠ s := by
  intro hts
  subst s
  rcases hstat with ⟨ht, hs⟩
  have hprod : (h - k) * Real.cosh t = 0 := by
    linarith
  exact hhk (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right
    (ne_of_gt (Real.cosh_pos t))))

/-- A two-rapidity stationary pair reverses the order of its frequencies. -/
theorem XiMassTwoRapidityCorrelationStationary.rapidities_order_reverse_of_frequency_lt
    {u h k t s : ℝ} (hu : 0 < u)
    (hstat : XiMassTwoRapidityCorrelationStationary u h k t s) (hhk : h < k) :
    s < t := by
  rcases hstat with ⟨ht, hs⟩
  have htanh_t : Real.tanh t = -h / u := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hu.ne', (Real.cosh_pos t).ne']
    linarith
  have htanh_s : Real.tanh s = -k / u := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hu.ne', (Real.cosh_pos s).ne']
    linarith
  have hratio : Real.tanh s < Real.tanh t := by
    calc
      Real.tanh s = -k / u := htanh_s
      _ < -h / u := by
        rw [div_lt_iff₀ hu]
        field_simp [hu.ne']
        linarith
      _ = Real.tanh t := htanh_t.symm
  by_contra hst
  exact (not_le_of_gt hratio)
    (HTGeometry.tanh_strictMono.monotone (le_of_not_gt hst))

/-- A fixed-width rapidity neighborhood of the diagonal does not exclude distinct-frequency
timelike saddles: at sufficiently large mass it contains the stationary pair of every ordered
timelike frequency pair. -/
theorem exists_xiMassTwoRapidityCorrelationStationary_near_diagonal
    {u h k ε : ℝ} (hh : 0 ≤ h) (hhk : h < k) (hdeep : 2 * k ≤ u)
    (hε : 2 * k / u ≤ ε) :
    ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s ∧
      0 < t - s ∧ t - s ≤ ε := by
  have hk : 0 < k := lt_of_le_of_lt hh hhk
  have hu : 0 < u := lt_of_lt_of_le (by linarith) hdeep
  have hku : k < u := by linarith
  have hhu : h < u := hhk.trans hku
  have hhrapidity : 0 ≤ timelikeRapidity u h := by
    rw [timelikeRapidity]
    exact Real.arsinh_nonneg_iff.mpr
      (div_nonneg hh (Real.sqrt_nonneg _))
  have hstat : XiMassTwoRapidityCorrelationStationary u h k
      (-timelikeRapidity u h) (-timelikeRapidity u k) := by
    constructor
    · exact (massPhase_timelike_stationary_iff hu hh hhu _).mpr rfl
    · exact (massPhase_timelike_stationary_iff hu hk.le hku _).mpr rfl
  refine ⟨-timelikeRapidity u h, -timelikeRapidity u k, hstat, ?_, ?_⟩
  · exact sub_pos.mpr (hstat.rapidities_order_reverse_of_frequency_lt hu hhk)
  · have hbound : timelikeRapidity u k ≤ 2 * k / u :=
      timelikeRapidity_le_two_mul_div hk hdeep
    linarith

/-- Distinct-frequency stationary pairs lie strictly in the anti-ordered rapidity cone. -/
theorem XiMassTwoRapidityCorrelationStationary.frequency_rapidity_orientation_neg
    {u h k t s : ℝ} (hu : 0 < u)
    (hstat : XiMassTwoRapidityCorrelationStationary u h k t s) (hhk : h ≠ k) :
    (h - k) * (t - s) < 0 := by
  rcases lt_or_gt_of_ne hhk with hlt | hgt
  · exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt)
      (sub_pos.mpr (hstat.rapidities_order_reverse_of_frequency_lt hu hlt))
  · have hrev : XiMassTwoRapidityCorrelationStationary u k h s t :=
      ⟨hstat.2, hstat.1⟩
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hgt)
      (sub_neg.mpr (hrev.rapidities_order_reverse_of_frequency_lt hu hgt))

/-- Every stationary pair at unequal frequencies is excluded by same-order causal support. -/
theorem not_exists_xiMassTwoRapidityCorrelationStationary_of_same_order
    {u h k : ℝ} (hu : 0 < u) (hhk : h ≠ k) :
    ¬ ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s ∧
      0 ≤ (h - k) * (t - s) := by
  rintro ⟨t, s, hstat, horient⟩
  exact (not_le_of_gt
    (hstat.frequency_rapidity_orientation_neg hu hhk)) horient

/-- The rapidity triangle opposite to frequency order contains no stationary pair. -/
theorem not_exists_xiMassTwoRapidityCorrelationStationary_of_frequency_lt_and_rapidity_le
    {u h k : ℝ} (hu : 0 < u) (hhk : h < k) :
    ¬ ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s ∧ t ≤ s := by
  rintro ⟨t, s, hstat, hts⟩
  exact (not_le_of_gt
    (hstat.rapidities_order_reverse_of_frequency_lt hu hhk)) hts

/-- Strictly ordered timelike frequencies have a stationary pair in the opposite rapidity
triangle.  Frequency order alone therefore cannot remove the two-rapidity saddle. -/
theorem exists_xiMassTwoRapidityCorrelationStationary_with_rapidities_order_reverse
    {u h k : ℝ} (hu : 0 < u) (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hhu : h < u) (hku : k < u) (hhk : h < k) :
    ∃ t s : ℝ, XiMassTwoRapidityCorrelationStationary u h k t s ∧ s < t := by
  obtain ⟨t, s, hstat⟩ :=
    exists_xiMassTwoRapidityCorrelationStationary hu hh hk hhu hku
  exact ⟨t, s, hstat,
    hstat.rapidities_order_reverse_of_frequency_lt hu hhk⟩

end

end RHTower
