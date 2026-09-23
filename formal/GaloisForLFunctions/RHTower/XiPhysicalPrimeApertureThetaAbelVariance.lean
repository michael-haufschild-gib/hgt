import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureMertensCoboundary
import GaloisForLFunctions.RHTower.XiMassPrimeWindowAbel

/-!
# Physical FCRJ energy as a theta-discrepancy Abel variance

The exact physical support packet consists of all primes with log coordinate in `(m-A,k]`.
At every aperture position its moving `log p / p` flux is transported by Abel summation to one
boundary difference plus one integral of the Chebyshev-theta discrepancy.

Squaring after physical centering gives an exact theta-error variance formula for complete FCRJ
carrier energy. No coefficient comparison, prime-power replacement, or inequality is used.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Prime-subtype form of one exact logarithmic window. -/
def xiPhysicalPrimeLogWindowPacket (H T : ℝ) : Finset Nat.Primes :=
  (primeLogWindow H T).attach.map
    (⟨fun p => ⟨p.1, (mem_primeLogWindow.mp p.2).2⟩,
      fun _ _ h =>
        Subtype.ext (congrArg (fun q : Nat.Primes => (q : ℕ)) h)⟩ :
      {p // p ∈ primeLogWindow H T} ↪ Nat.Primes)

/-- Membership in prime-subtype window is membership of underlying natural prime. -/
theorem mem_xiPhysicalPrimeLogWindowPacket {H T : ℝ} {p : Nat.Primes} :
    p ∈ xiPhysicalPrimeLogWindowPacket H T ↔ (p : ℕ) ∈ primeLogWindow H T := by
  constructor
  · intro hp
    rw [xiPhysicalPrimeLogWindowPacket, Finset.mem_map] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    rw [← hqp]
    exact q.2
  · intro hp
    rw [xiPhysicalPrimeLogWindowPacket, Finset.mem_map]
    refine ⟨⟨(p : ℕ), hp⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

/-- Physical endpoint mass of subtype packet is exact natural-prime `log p / p` sum. -/
theorem sum_xiPhysicalPrimeLogWindowPacket_weight_eq (H T : ℝ) :
    ∑ p ∈ xiPhysicalPrimeLogWindowPacket H T, physicalPrimeEndpointWeight p =
      ∑ n ∈ primeLogWindow H T, Real.log n / (n : ℝ) := by
  rw [xiPhysicalPrimeLogWindowPacket, Finset.sum_map]
  simpa [physicalPrimeEndpointWeight] using
    (Finset.sum_attach (primeLogWindow H T)
      (fun n => Real.log n / (n : ℝ)))

/-- Floor-defined log window has expected semantic prime-log membership. -/
theorem mem_primeLogWindow_iff_log {H T : ℝ} {p : ℕ} (hp : Nat.Prime p) :
    p ∈ primeLogWindow H T ↔ H < Real.log p ∧ Real.log p ≤ T := by
  constructor
  · intro h
    exact ⟨primeLogWindow_log_lt h, primeLogWindow_log_le h⟩
  · intro h
    rw [mem_primeLogWindow]
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    refine ⟨⟨?_, ?_⟩, hp⟩
    · exact (Nat.floor_lt (Real.exp_pos H).le).2
        ((Real.lt_log_iff_exp_lt hp0).1 h.1)
    · exact (Nat.le_floor_iff (Real.exp_pos T).le).2
        ((Real.log_le_iff_le_exp hp0).1 h.2)

/-- Semantic prime-log membership for subtype window packet. -/
theorem mem_xiPhysicalPrimeLogWindowPacket_iff_log
    {H T : ℝ} {p : Nat.Primes} :
    p ∈ xiPhysicalPrimeLogWindowPacket H T ↔
      H < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ T := by
  rw [mem_xiPhysicalPrimeLogWindowPacket,
    mem_primeLogWindow_iff_log p.prop]

/-- Full physical support packet restricts at aperture position `u` to exact translated prime-log
window. -/
theorem xiPhysicalPrimeLogWindowFlux_supportPacket_eq
    (A m k : ℝ) {u : ℝ} (hu : u ∈ Icc 0 A) :
    xiPhysicalPrimeLogWindowFlux
        (xiPhysicalPrimeLogWindowPacket (m - A) k) m k u =
      ∑ n ∈ primeLogWindow (m - u) (k - u), Real.log n / (n : ℝ) := by
  rw [xiPhysicalPrimeLogWindowFlux_eq_sum_filter]
  have hfilter :
      (xiPhysicalPrimeLogWindowPacket (m - A) k).filter
          (fun p : Nat.Primes =>
            m - u < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ k - u) =
        xiPhysicalPrimeLogWindowPacket (m - u) (k - u) := by
    ext p
    simp only [Finset.mem_filter,
      mem_xiPhysicalPrimeLogWindowPacket_iff_log]
    constructor
    · intro h
      exact h.2
    · intro h
      refine ⟨⟨?_, ?_⟩, h⟩
      · linarith [hu.2]
      · linarith [hu.1]
  rw [← Finset.sum_filter, hfilter,
    sum_xiPhysicalPrimeLogWindowPacket_weight_eq]

/-- One raw prime window integrates over physical aperture to exact clipped length. -/
theorem intervalIntegral_xiPhysicalPrimeLogWindowIndicator_eq_length
    {A : ℝ} (hA : 0 ≤ A) (m k : ℝ) (p : Nat.Primes) :
    (∫ u : ℝ in 0..A, xiPhysicalPrimeLogWindowIndicator m k p u) =
      xiPhysicalPrimeLogApertureLength A m k p := by
  rw [intervalIntegral.integral_of_le hA]
  have hcongr :
      (∫ u in Ioc (0 : ℝ) A, xiPhysicalPrimeLogWindowIndicator m k p u) =
      ∫ u in Ioc (0 : ℝ) A,
        Set.indicator (xiPhysicalPrimeLogApertureSet A m k p) (fun _ => (1 : ℝ)) u := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    by_cases hp : u ∈ xiPhysicalPrimeLogApertureSet A m k p
    · rw [indicator_of_mem hp, xiPhysicalPrimeLogWindowIndicator_eq_if,
        if_pos ((mem_xiPhysicalPrimeLogApertureSet_iff_window A m k p hu).mp hp)]
    · rw [indicator_of_notMem hp, xiPhysicalPrimeLogWindowIndicator_eq_if,
        if_neg (mt (mem_xiPhysicalPrimeLogApertureSet_iff_window A m k p hu).mpr hp)]
  rw [hcongr, MeasureTheory.setIntegral_indicator
    (show MeasurableSet (xiPhysicalPrimeLogApertureSet A m k p) from measurableSet_Ioc)]
  have hinter : Ioc (0 : ℝ) A ∩ xiPhysicalPrimeLogApertureSet A m k p =
      xiPhysicalPrimeLogApertureSet A m k p :=
    Set.inter_eq_right.mpr (xiPhysicalPrimeLogApertureSet_subset A m k p)
  rw [hinter, setIntegral_const, volume_real_xiPhysicalPrimeLogApertureSet]
  simp

theorem integrable_xiPhysicalPrimeLogWindowIndicator
    (m k : ℝ) (p : Nat.Primes) :
    Integrable (xiPhysicalPrimeLogWindowIndicator m k p) := by
  unfold xiPhysicalPrimeLogWindowIndicator rectangularIntervalIndicator
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (ne_of_lt measure_Ioc_lt_top)

theorem integrable_xiPhysicalPrimeLogWindowFlux
    (P : Finset Nat.Primes) (m k : ℝ) :
    Integrable (xiPhysicalPrimeLogWindowFlux P m k) := by
  unfold xiPhysicalPrimeLogWindowFlux
  exact integrable_finsetSum _ fun p hp =>
    (integrable_xiPhysicalPrimeLogWindowIndicator m k p).const_mul
      (physicalPrimeEndpointWeight p)

theorem norm_xiPhysicalPrimeLogWindowIndicator_le_one
    (m k : ℝ) (p : Nat.Primes) (u : ℝ) :
    ‖xiPhysicalPrimeLogWindowIndicator m k p u‖ ≤ 1 := by
  rw [xiPhysicalPrimeLogWindowIndicator_eq_if]
  split <;> simp

theorem norm_xiPhysicalPrimeLogWindowFlux_le_sum_norm
    (P : Finset Nat.Primes) (m k u : ℝ) :
    ‖xiPhysicalPrimeLogWindowFlux P m k u‖ ≤
      ∑ p ∈ P, ‖physicalPrimeEndpointWeight p‖ := by
  unfold xiPhysicalPrimeLogWindowFlux
  refine (norm_sum_le P _).trans (Finset.sum_le_sum fun p hp => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (norm_xiPhysicalPrimeLogWindowIndicator_le_one m k p u)

theorem integrable_sq_xiPhysicalPrimeLogWindowFlux
    (P : Finset Nat.Primes) (m k : ℝ) :
    Integrable (fun u => xiPhysicalPrimeLogWindowFlux P m k u ^ (2 : ℕ)) := by
  have hflux := integrable_xiPhysicalPrimeLogWindowFlux P m k
  have hmul : Integrable (fun u =>
      xiPhysicalPrimeLogWindowFlux P m k u *
        xiPhysicalPrimeLogWindowFlux P m k u) :=
    hflux.bdd_mul hflux.aestronglyMeasurable
      (Filter.Eventually.of_forall
        (norm_xiPhysicalPrimeLogWindowFlux_le_sum_norm P m k))
  simpa [pow_two] using hmul

/-- Raw physical window flux integrates to exact weighted clipped-length mass. -/
theorem intervalIntegral_xiPhysicalPrimeLogWindowFlux_eq_weightedLength
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 ≤ A) (m k : ℝ) :
    (∫ u : ℝ in 0..A, xiPhysicalPrimeLogWindowFlux P m k u) =
      xiPhysicalPrimeLogApertureWeightedLengthMass P A m k := by
  unfold xiPhysicalPrimeLogWindowFlux
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_xiPhysicalPrimeLogWindowIndicator_eq_length hA]
  · intro p hp
    exact (integrable_xiPhysicalPrimeLogWindowIndicator m k p).const_mul
      (physicalPrimeEndpointWeight p) |>.intervalIntegrable

/-- Exact Abel transport from physical `log p / p` window to Chebyshev-theta discrepancy. -/
theorem sum_primeLogWindow_log_div_sub_width_eq_thetaDiscrepancy
    {H T : ℝ} (hHT : H ≤ T) :
    (∑ p ∈ primeLogWindow H T, Real.log p / (p : ℝ)) - (T - H) =
      xiMassThetaLogDiscrepancy T * Real.exp (-T) -
        xiMassThetaLogDiscrepancy H * Real.exp (-H) +
          ∫ h in H..T, xiMassThetaLogDiscrepancy h * Real.exp (-h) := by
  let G : ℝ → ℂ := fun h => ((Real.exp (-h) : ℝ) : ℂ)
  let G' : ℝ → ℂ := fun h => ((-Real.exp (-h) : ℝ) : ℂ)
  have hG : ∀ x ∈ Set.Icc H T, HasDerivAt G (G' x) x := by
    intro x hx
    dsimp only [G, G']
    simpa [Function.comp_def] using
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).ofReal_comp
  have hG' : IntervalIntegrable G' volume H T := by
    exact (by fun_prop : Continuous G').intervalIntegrable H T
  have h := primeLogWindow_quadrature_eq hHT hG hG'
  have hsum : ∑ p ∈ primeLogWindow H T,
      ((Real.log p : ℝ) : ℂ) * G (Real.log p) =
        (((∑ p ∈ primeLogWindow H T, Real.log p / (p : ℝ)) : ℝ) : ℂ) := by
    dsimp only [G]
    norm_cast
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (mem_primeLogWindow.mp hp).2.pos
    rw [Real.exp_neg, Real.exp_log hp0]
    norm_cast
  have hcont : (∫ h in H..T, G h * ((Real.exp h : ℝ) : ℂ)) =
      (((T - H : ℝ)) : ℂ) := by
    have hpoint : ∀ x ∈ Set.uIcc H T,
        G x * ((Real.exp x : ℝ) : ℂ) = (1 : ℂ) := by
      intro x hx
      dsimp only [G]
      norm_cast
      rw [Real.exp_neg]
      field_simp
    rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const]
    simp
  rw [hsum, hcont] at h
  have hintCast :
      (∫ h in H..T,
        (((xiMassThetaLogDiscrepancy h * Real.exp (-h) : ℝ)) : ℂ)) =
      (((∫ h in H..T,
        xiMassThetaLogDiscrepancy h * Real.exp (-h)) : ℝ) : ℂ) := by
    exact intervalIntegral.integral_ofReal
  dsimp only [G, G'] at h
  have hInt :
      (∫ h in H..T,
        ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) *
          ((-Real.exp (-h) : ℝ) : ℂ)) =
      -(((∫ h in H..T,
        xiMassThetaLogDiscrepancy h * Real.exp (-h)) : ℝ) : ℂ) := by
    rw [← hintCast, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    push_cast
    ring
  rw [hInt] at h
  norm_cast at h ⊢
  linarith

/-- Exact pointwise physical bridge: support-packet flux discrepancy is exponentially normalized
theta-error boundary difference plus Abel integral. -/
theorem xiPhysicalPrimeLogWindowFlux_supportPacket_sub_width_eq_thetaDiscrepancy
    (A : ℝ) {m k u : ℝ} (hmk : m ≤ k) (hu : u ∈ Icc 0 A) :
    xiPhysicalPrimeLogWindowFlux
        (xiPhysicalPrimeLogWindowPacket (m - A) k) m k u - (k - m) =
      xiMassThetaLogDiscrepancy (k - u) * Real.exp (-(k - u)) -
        xiMassThetaLogDiscrepancy (m - u) * Real.exp (-(m - u)) +
          ∫ h in (m - u)..(k - u),
            xiMassThetaLogDiscrepancy h * Real.exp (-h) := by
  rw [xiPhysicalPrimeLogWindowFlux_supportPacket_eq A m k hu]
  have h := sum_primeLogWindow_log_div_sub_width_eq_thetaDiscrepancy
    (H := m - u) (T := k - u) (by linarith)
  convert h using 1
  all_goals ring

/-- Theta-discrepancy Abel response of one moving physical log window. -/
def xiPhysicalPrimeLogThetaAbelResponse (m k u : ℝ) : ℝ :=
  xiMassThetaLogDiscrepancy (k - u) * Real.exp (-(k - u)) -
    xiMassThetaLogDiscrepancy (m - u) * Real.exp (-(m - u)) +
      ∫ h in (m - u)..(k - u),
        xiMassThetaLogDiscrepancy h * Real.exp (-h)

/-- Support-packet flux is width plus exact theta Abel response. -/
theorem xiPhysicalPrimeLogWindowFlux_supportPacket_eq_width_add_thetaAbelResponse
    (A : ℝ) {m k u : ℝ} (hmk : m ≤ k) (hu : u ∈ Icc 0 A) :
    xiPhysicalPrimeLogWindowFlux
        (xiPhysicalPrimeLogWindowPacket (m - A) k) m k u =
      (k - m) + xiPhysicalPrimeLogThetaAbelResponse m k u := by
  rw [xiPhysicalPrimeLogThetaAbelResponse]
  linarith [xiPhysicalPrimeLogWindowFlux_supportPacket_sub_width_eq_thetaDiscrepancy
    A hmk hu]

theorem intervalIntegrable_xiPhysicalPrimeLogThetaAbelResponse
    {A : ℝ} (hA : 0 < A) {m k : ℝ} (hmk : m ≤ k) :
    IntervalIntegrable (xiPhysicalPrimeLogThetaAbelResponse m k) volume 0 A := by
  let P := xiPhysicalPrimeLogWindowPacket (m - A) k
  have hbase : IntervalIntegrable
      (fun u => xiPhysicalPrimeLogWindowFlux P m k u - (k - m)) volume 0 A :=
    (integrable_xiPhysicalPrimeLogWindowFlux P m k).intervalIntegrable.sub
      (show IntervalIntegrable (fun _ : ℝ => k - m) volume 0 A from
        intervalIntegrable_const)
  refine IntervalIntegrable.congr ?_ hbase
  intro u hu
  rw [Set.uIoc_of_le hA.le] at hu
  have hfluxEq := xiPhysicalPrimeLogWindowFlux_supportPacket_eq_width_add_thetaAbelResponse
    A hmk ⟨hu.1.le, hu.2⟩
  change xiPhysicalPrimeLogWindowFlux P m k u - (k - m) = _
  dsimp only [P]
  linarith

theorem intervalIntegrable_sq_xiPhysicalPrimeLogThetaAbelResponse
    {A : ℝ} (hA : 0 < A) {m k : ℝ} (hmk : m ≤ k) :
    IntervalIntegrable
      (fun u => xiPhysicalPrimeLogThetaAbelResponse m k u ^ (2 : ℕ))
      volume 0 A := by
  let P := xiPhysicalPrimeLogWindowPacket (m - A) k
  let c := k - m
  have hflux : IntervalIntegrable (xiPhysicalPrimeLogWindowFlux P m k) volume 0 A :=
    (integrable_xiPhysicalPrimeLogWindowFlux P m k).intervalIntegrable
  have hfluxSq : IntervalIntegrable
      (fun u => xiPhysicalPrimeLogWindowFlux P m k u ^ (2 : ℕ)) volume 0 A :=
    (integrable_sq_xiPhysicalPrimeLogWindowFlux P m k).intervalIntegrable
  have hbase : IntervalIntegrable
      (fun u => (xiPhysicalPrimeLogWindowFlux P m k u - c) ^ (2 : ℕ)) volume 0 A := by
    refine IntervalIntegrable.congr ?_
      ((hfluxSq.sub (hflux.const_mul (2 * c))).add
        (show IntervalIntegrable (fun _ : ℝ => c ^ (2 : ℕ)) volume 0 A from
          intervalIntegrable_const))
    intro u hu
    ring
  refine IntervalIntegrable.congr ?_ hbase
  intro u hu
  rw [Set.uIoc_of_le hA.le] at hu
  have hfluxEq := xiPhysicalPrimeLogWindowFlux_supportPacket_eq_width_add_thetaAbelResponse
    A hmk ⟨hu.1.le, hu.2⟩
  change (xiPhysicalPrimeLogWindowFlux P m k u - c) ^ (2 : ℕ) = _
  dsimp only [P, c]
  rw [hfluxEq]
  ring

/-- Physical clipping correction is exactly aperture mean of theta Abel response. -/
theorem xiPhysicalPrimeLogApertureWeightedLengthMass_div_sub_width_eq_mean_thetaAbelResponse
    {A : ℝ} (hA : 0 < A) {m k : ℝ} (hmk : m ≤ k) :
    xiPhysicalPrimeLogApertureWeightedLengthMass
          (xiPhysicalPrimeLogWindowPacket (m - A) k) A m k / A - (k - m) =
      (1 / A) * ∫ u : ℝ in 0..A, xiPhysicalPrimeLogThetaAbelResponse m k u := by
  let P := xiPhysicalPrimeLogWindowPacket (m - A) k
  have hfluxI : IntervalIntegrable (xiPhysicalPrimeLogWindowFlux P m k) volume 0 A :=
    (integrable_xiPhysicalPrimeLogWindowFlux P m k).intervalIntegrable
  have hconstI : IntervalIntegrable (fun _ : ℝ => k - m) volume 0 A :=
    (continuous_const : Continuous (fun _ : ℝ => k - m)).intervalIntegrable 0 A
  have hresponse :
      (∫ u : ℝ in 0..A, xiPhysicalPrimeLogThetaAbelResponse m k u) =
        xiPhysicalPrimeLogApertureWeightedLengthMass P A m k - A * (k - m) := by
    calc
      (∫ u : ℝ in 0..A, xiPhysicalPrimeLogThetaAbelResponse m k u) =
          ∫ u : ℝ in 0..A, xiPhysicalPrimeLogWindowFlux P m k u - (k - m) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hA.le] at hu
        have hflux := xiPhysicalPrimeLogWindowFlux_supportPacket_eq_width_add_thetaAbelResponse
          A hmk hu
        linarith
      _ = (∫ u : ℝ in 0..A, xiPhysicalPrimeLogWindowFlux P m k u) -
          ∫ u : ℝ in 0..A, (k - m) :=
        intervalIntegral.integral_sub hfluxI hconstI
      _ = xiPhysicalPrimeLogApertureWeightedLengthMass P A m k - A * (k - m) := by
        rw [intervalIntegral_xiPhysicalPrimeLogWindowFlux_eq_weightedLength P hA.le,
          intervalIntegral.integral_const]
        simp
  dsimp only [P] at hresponse ⊢
  rw [hresponse]
  field_simp [hA.ne']

/-- Exact theta-error provider identity for complete fixed-support physical FCRJ energy. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_eq_thetaAbelVariance
    {A : ℝ} (hA : 0 < A) {m k : ℝ} (hmk : m ≤ k) :
    xiPhysicalPrimeLogApertureFusionEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) k) A m k =
      ∫ u : ℝ in 0..A,
        (xiPhysicalPrimeLogThetaAbelResponse m k u -
          (xiPhysicalPrimeLogApertureWeightedLengthMass
              (xiPhysicalPrimeLogWindowPacket (m - A) k) A m k / A - (k - m))) ^ (2 : ℕ) := by
  rw [← intervalIntegral_sq_xiPhysicalPrimeLogCenteredWindowFlux_eq_energy
    (xiPhysicalPrimeLogWindowPacket (m - A) k) hA m k]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hA.le] at hu
  change xiPhysicalPrimeLogCenteredWindowFlux
      (xiPhysicalPrimeLogWindowPacket (m - A) k) A m k u ^ (2 : ℕ) = _
  rw [xiPhysicalPrimeLogCenteredWindowFlux,
    xiPhysicalPrimeLogWindowFlux_supportPacket_eq_width_add_thetaAbelResponse A hmk hu]
  ring

/-- Lossless provider decomposition: fusion energy is raw theta-Abel `L²` mass minus its
rank-one aperture mean. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_eq_thetaAbelRaw_sub_meanSq
    {A : ℝ} (hA : 0 < A) {m k : ℝ} (hmk : m ≤ k) :
    xiPhysicalPrimeLogApertureFusionEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) k) A m k =
      (∫ u : ℝ in 0..A, xiPhysicalPrimeLogThetaAbelResponse m k u ^ (2 : ℕ)) -
        (1 / A) *
          (∫ u : ℝ in 0..A, xiPhysicalPrimeLogThetaAbelResponse m k u) ^ (2 : ℕ) := by
  rw [xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_eq_thetaAbelVariance hA hmk,
    xiPhysicalPrimeLogApertureWeightedLengthMass_div_sub_width_eq_mean_thetaAbelResponse
      hA hmk]
  let R := xiPhysicalPrimeLogThetaAbelResponse m k
  let I := ∫ u : ℝ in 0..A, R u
  let μ := (1 / A) * I
  have hR : IntervalIntegrable R volume 0 A :=
    intervalIntegrable_xiPhysicalPrimeLogThetaAbelResponse hA hmk
  have hR2 : IntervalIntegrable (fun u => R u ^ (2 : ℕ)) volume 0 A :=
    intervalIntegrable_sq_xiPhysicalPrimeLogThetaAbelResponse hA hmk
  have hlin : IntervalIntegrable (fun u => 2 * μ * R u) volume 0 A :=
    hR.const_mul (2 * μ)
  have hconst : IntervalIntegrable (fun _ : ℝ => μ ^ (2 : ℕ)) volume 0 A :=
    intervalIntegrable_const
  change (∫ u : ℝ in 0..A, (R u - μ) ^ (2 : ℕ)) =
    (∫ u : ℝ in 0..A, R u ^ (2 : ℕ)) - (1 / A) * I ^ (2 : ℕ)
  calc
    (∫ u : ℝ in 0..A, (R u - μ) ^ (2 : ℕ)) =
        (∫ u : ℝ in 0..A, R u ^ (2 : ℕ)) -
          (∫ u : ℝ in 0..A, 2 * μ * R u) +
            ∫ _u : ℝ in 0..A, μ ^ (2 : ℕ) := by
      have hpoint : ∀ u ∈ Set.uIcc (0 : ℝ) A,
          (R u - μ) ^ (2 : ℕ) = R u ^ (2 : ℕ) - 2 * μ * R u + μ ^ (2 : ℕ) := by
        intro u hu
        ring
      rw [intervalIntegral.integral_congr hpoint,
        intervalIntegral.integral_add (hR2.sub hlin) hconst,
        intervalIntegral.integral_sub hR2 hlin]
    _ = (∫ u : ℝ in 0..A, R u ^ (2 : ℕ)) - (1 / A) * I ^ (2 : ℕ) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      rw [show (∫ u : ℝ in 0..A, R u) = I from rfl]
      change (∫ u : ℝ in 0..A, R u ^ (2 : ℕ)) - 2 * μ * I + A * μ ^ (2 : ℕ) =
        (∫ u : ℝ in 0..A, R u ^ (2 : ℕ)) - (1 / A) * I ^ (2 : ℕ)
      have hmuA : μ * A = I := by
        dsimp only [μ]
        field_simp [hA.ne']
      have hmuI : μ * I = (1 / A) * I ^ (2 : ℕ) := by
        dsimp only [μ]
        ring
      rw [show A * μ ^ (2 : ℕ) = μ * I by calc
        A * μ ^ (2 : ℕ) = μ * (μ * A) := by ring
        _ = μ * I := by rw [hmuA], hmuI]
      ring

/-- Centering can only decrease theta-Abel `L²` mass. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_le_thetaAbelRaw
    {A : ℝ} (hA : 0 < A) {m k : ℝ} (hmk : m ≤ k) :
    xiPhysicalPrimeLogApertureFusionEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) k) A m k ≤
      ∫ u : ℝ in 0..A, xiPhysicalPrimeLogThetaAbelResponse m k u ^ (2 : ℕ) := by
  rw [xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_eq_thetaAbelRaw_sub_meanSq
    hA hmk]
  exact sub_le_self _ (mul_nonneg (by positivity) (sq_nonneg _))

/-- Any uniform theta-Abel response estimate gives the complete FCRJ carrier budget with exact
aperture cost. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_le_mul_sq_of_response_bound
    {A : ℝ} (hA : 0 < A) {m k B : ℝ} (hmk : m ≤ k) (hB : 0 ≤ B)
    (hresponse : ∀ u ∈ Icc (0 : ℝ) A,
      |xiPhysicalPrimeLogThetaAbelResponse m k u| ≤ B) :
    xiPhysicalPrimeLogApertureFusionEnergy
        (xiPhysicalPrimeLogWindowPacket (m - A) k) A m k ≤ A * B ^ (2 : ℕ) := by
  refine (xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_le_thetaAbelRaw
    hA hmk).trans ?_
  calc
    (∫ u : ℝ in 0..A, xiPhysicalPrimeLogThetaAbelResponse m k u ^ (2 : ℕ)) ≤
        ∫ _u : ℝ in 0..A, B ^ (2 : ℕ) := by
      apply intervalIntegral.integral_mono_on hA.le
        (intervalIntegrable_sq_xiPhysicalPrimeLogThetaAbelResponse hA hmk)
        intervalIntegrable_const
      intro u hu
      have hub := hresponse u hu
      nlinarith [abs_nonneg (xiPhysicalPrimeLogThetaAbelResponse m k u),
        sq_abs (xiPhysicalPrimeLogThetaAbelResponse m k u),
        sq_nonneg (B - |xiPhysicalPrimeLogThetaAbelResponse m k u|)]
    _ = A * B ^ (2 : ℕ) := by
      rw [intervalIntegral.integral_const]
      simp

/-- Fixed-ratio theta-error variance at physical scale `X`. -/
theorem xiPhysicalPrimeLogApertureFusionEnergy_logScale_supportPacket_eq_thetaAbelVariance
    {A : ℝ} (hA : 0 < A) (X : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    xiPhysicalPrimeLogApertureFusionEnergy
        (xiPhysicalPrimeLogWindowPacket (Real.log X - A) (Real.log X + c))
        A (Real.log X) (Real.log X + c) =
      ∫ u : ℝ in 0..A,
        (xiPhysicalPrimeLogThetaAbelResponse (Real.log X) (Real.log X + c) u -
          (xiPhysicalPrimeLogApertureWeightedLengthMass
              (xiPhysicalPrimeLogWindowPacket (Real.log X - A) (Real.log X + c))
              A (Real.log X) (Real.log X + c) / A - c)) ^ (2 : ℕ) := by
  simpa only [add_sub_cancel_left] using
    xiPhysicalPrimeLogApertureFusionEnergy_supportPacket_eq_thetaAbelVariance
      hA (m := Real.log X) (k := Real.log X + c) (by linarith)

end

end RHTower
