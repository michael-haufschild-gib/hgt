import GaloisForLFunctions.RHTower.BlaschkeLocalizedInfinitePhaseQuantile
import GaloisForLFunctions.RHTower.CountableWeightedBorelCantelli
import GaloisForLFunctions.RHTower.CountableWeightedFirstReturn
import Mathlib.Probability.ProductMeasure

/-!
# Almost-sure early-return obstruction for the infinite Blaschke packet

This file closes the lower-clock half of the Blaschke-localized recurrence
law. At shifted logarithmic scales, exact spectral-depth entropy turns every
fixed fractional subentropy deadline into a summable Gaussian event.

The final theorem specializes the measure to countable product Haar, proves
all finite heads are exact Haar marginals, and gives an explicit integer
deadline. No independence across scales is used.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

private def finRangeEquiv (M : ℕ) : Fin M ≃ ↥(Finset.range M) where
  toFun i := ⟨i, Finset.mem_range.mpr i.isLt⟩
  invFun i := ⟨i, Finset.mem_range.mp i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The first `M` coordinates of countable product Haar have exactly the
finite product Haar law. -/
theorem map_countableTorusHead_infinitePi_volume (M : ℕ) :
    Measure.map (countableTorusHead M)
        (Measure.infinitePi (fun _ : ℕ =>
          (volume : Measure UnitAddCircle))) =
      (volume : Measure (Fin M → UnitAddCircle)) := by
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  let I : Finset ℕ := Finset.range M
  let e : Fin M ≃ ↥I := finRangeEquiv M
  let reindex :
      (↥I → UnitAddCircle) → (Fin M → UnitAddCircle) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin M => UnitAddCircle) e.symm
  have hfun :
      countableTorusHead M = reindex ∘ I.restrict := by
    funext x i
    rfl
  have hrestrict :
      Measure.map I.restrict
          (Measure.infinitePi (fun _ : ℕ =>
            (volume : Measure UnitAddCircle))) =
        Measure.pi (fun _ : ↥I =>
          (volume : Measure UnitAddCircle)) := by
    simpa using
      (Measure.infinitePi_map_restrict
        (fun _ : ℕ => (volume : Measure UnitAddCircle))
        (I := I))
  have hreindex :
      Measurable reindex :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin M => UnitAddCircle) e.symm).measurable
  rw [hfun, ← Measure.map_map hreindex (Finset.measurable_restrict I),
    hrestrict]
  simpa only [MeasureTheory.volume_pi] using
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin M => UnitAddCircle) e.symm).map_eq

/-- Every active Blaschke head has mass at most one. -/
theorem blaschkeActiveHeadMass_le_one
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (L : ℝ) :
    summableWeightedHeadMass
        (blaschkeLocalizedWeight a)
        (blaschkeActiveTailRadius a L + 2) ≤ 1 := by
  let M := blaschkeActiveTailRadius a L + 2
  have hM : 1 ≤ M := by
    dsimp only [M]
    omega
  rw [summableWeightedHeadMass_blaschkeLocalizedWeight
    a ha0 ha1 M hM]
  have ha2lt : a ^ 2 < 1 := by nlinarith
  have htail :
      0 ≤ (1 - a ^ 2) * (a ^ 2) ^ (M - 1) := by positivity
  linarith

/-- The active head always contains the exceptional origin weight `a²`. -/
theorem blaschkeOriginWeight_le_activeHeadMass
    (a : ℝ) (L : ℝ) :
    a ^ 2 ≤
      summableWeightedHeadMass
        (blaschkeLocalizedWeight a)
        (blaschkeActiveTailRadius a L + 2) := by
  rw [summableWeightedHeadMass]
  have hsingle :
      blaschkeLocalizedWeight a 0 ≤
        ∑ k ∈ Finset.range (blaschkeActiveTailRadius a L + 2),
          blaschkeLocalizedWeight a k := by
    apply Finset.single_le_sum
    · intro k hk
      exact sq_nonneg (blaschkeLocalizedKernel a k)
    · simp
  simpa only [blaschkeLocalizedWeight_zero] using hsingle

/-- Once the water level reaches the origin depth, the active-head water
mass is at least one. -/
theorem one_le_blaschkeActiveHeadMass_mul_exp
    (a : ℝ) (ha0 : 0 < a)
    {L : ℝ} (hLzero : blaschkeSpectralSlope a ≤ L) :
    1 ≤
      summableWeightedHeadMass
          (blaschkeLocalizedWeight a)
          (blaschkeActiveTailRadius a L + 2) *
        Real.exp L := by
  have ha2pos : 0 < a ^ 2 := sq_pos_of_pos ha0
  have hmass :=
    blaschkeOriginWeight_le_activeHeadMass a L
  have horigin :
      1 ≤ a ^ 2 * Real.exp L := by
    rw [← Real.exp_log ha2pos, ← Real.exp_add]
    rw [Real.one_le_exp_iff]
    rw [blaschkeSpectralSlope] at hLzero
    linarith
  exact horigin.trans
    (mul_le_mul_of_nonneg_right hmass (Real.exp_pos L).le)

/-- The canonical defect `exp (-L)` is admissible for the normalized
active head. -/
theorem exp_neg_div_blaschkeActiveHeadMass_le_one
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {L : ℝ} (hLzero : blaschkeSpectralSlope a ≤ L) :
    Real.exp (-L) /
        summableWeightedHeadMass
          (blaschkeLocalizedWeight a)
          (blaschkeActiveTailRadius a L + 2) ≤ 1 := by
  let M := blaschkeActiveTailRadius a L + 2
  have hM : 1 ≤ M := by
    dsimp only [M]
    omega
  have hmass :
      0 < summableWeightedHeadMass
        (blaschkeLocalizedWeight a) M :=
    summableWeightedHeadMass_blaschkeLocalizedWeight_pos
      a ha0 ha1 M hM
  rw [div_le_iff₀ hmass]
  simp only [one_mul]
  calc
    Real.exp (-L) = 1 / Real.exp L := by
      rw [Real.exp_neg]
      exact inv_eq_one_div _
    _ ≤ summableWeightedHeadMass
          (blaschkeLocalizedWeight a) M := by
      apply (div_le_iff₀ (Real.exp_pos L)).2
      simpa only [M, mul_comm] using
        one_le_blaschkeActiveHeadMass_mul_exp
          a ha0 hLzero

/-- Normalizing the active head contributes at most `L` to its logarithmic
water prefactor. -/
theorem log_blaschkeActiveHeadMass_mul_exp_le
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (L : ℝ) :
    Real.log
        (summableWeightedHeadMass
            (blaschkeLocalizedWeight a)
            (blaschkeActiveTailRadius a L + 2) *
          Real.exp L) ≤ L := by
  let M := blaschkeActiveTailRadius a L + 2
  have hM : 1 ≤ M := by
    dsimp only [M]
    omega
  have hmass :
      0 < summableWeightedHeadMass
        (blaschkeLocalizedWeight a) M :=
    summableWeightedHeadMass_blaschkeLocalizedWeight_pos
      a ha0 ha1 M hM
  have hmassOne :
      summableWeightedHeadMass
          (blaschkeLocalizedWeight a) M ≤ 1 := by
    simpa only [M] using
      blaschkeActiveHeadMass_le_one a ha0 ha1 L
  rw [Real.log_mul hmass.ne' (Real.exp_ne_zero L), Real.log_exp]
  have hlog :
      Real.log
          (summableWeightedHeadMass
            (blaschkeLocalizedWeight a) M) ≤ 0 :=
    Real.log_nonpos hmass.le hmassOne
  linarith

/-- Integer-indexed logarithmic scale shifted beyond fixed spectral
offsets. -/
def blaschkeShiftedScale (K : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) + K

/-- Quadratic lower clock obtained from the exact Blaschke depth entropy. -/
def blaschkeShiftedQuadraticClock (a K : ℝ) (k : ℕ) : ℝ :=
  (blaschkeShiftedScale K k - blaschkeSpectralOffset a) ^ 2 /
    (4 * blaschkeSpectralSlope a)

/-- Uniform linear coefficient controlling active-head cardinality on
shifted logarithmic scales. -/
def blaschkeActiveLinearConstant (a K : ℝ) : ℝ :=
  2 + (K - blaschkeSpectralOffset a) /
      blaschkeSpectralSlope a +
    1 / blaschkeSpectralSlope a

/-- Shifting beyond the spectral offset makes the quadratic clock dominate
the unshifted square at every integer scale. -/
theorem blaschkeShiftedQuadraticClock_lower
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ} (hKtail : blaschkeSpectralOffset a ≤ K)
    (k : ℕ) :
    (k : ℝ) ^ 2 / (4 * blaschkeSpectralSlope a) ≤
      blaschkeShiftedQuadraticClock a K k := by
  have hrho : 0 < blaschkeSpectralSlope a :=
    blaschkeSpectralSlope_pos a ha0 ha1
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hshift :
      (k : ℝ) ≤
        blaschkeShiftedScale K k - blaschkeSpectralOffset a := by
    rw [blaschkeShiftedScale]
    linarith
  have hshift0 :
      0 ≤ blaschkeShiftedScale K k - blaschkeSpectralOffset a :=
    hk.trans hshift
  rw [blaschkeShiftedQuadraticClock]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (sq_le_sq₀ hk hshift0).2 hshift

/-- Active-head cardinality is bounded by an explicit linear function of
the shifted logarithmic scale. -/
theorem blaschkeActiveHeadCard_shifted_le
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ} (hKtail : blaschkeSpectralOffset a ≤ K)
    (k : ℕ) :
    ((blaschkeActiveTailRadius a
          (blaschkeShiftedScale K k) + 2 : ℕ) : ℝ) ≤
      blaschkeActiveLinearConstant a K * (1 + (k : ℝ)) := by
  let rho := blaschkeSpectralSlope a
  let c := blaschkeSpectralOffset a
  let L := blaschkeShiftedScale K k
  have hrho : 0 < rho := by
    simpa only [rho] using blaschkeSpectralSlope_pos a ha0 ha1
  have hLtail : c ≤ L := by
    dsimp only [c, L, blaschkeShiftedScale]
    have hk : 0 ≤ (k : ℝ) := by positivity
    linarith
  have hbracket :=
    blaschkeActiveTailRadius_bracket a ha0 ha1 hLtail
  have hRle :
      (blaschkeActiveTailRadius a L : ℝ) ≤ (L - c) / rho := by
    apply (le_div_iff₀ hrho).2
    simpa only [rho, c, mul_comm] using hbracket.1
  have hA : 0 ≤ 2 + (K - c) / rho := by
    have : 0 ≤ (K - c) / rho :=
      div_nonneg (sub_nonneg.mpr hKtail) hrho.le
    linarith
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hRle' :
      (blaschkeActiveTailRadius a L : ℝ) + 2 ≤
        (k : ℝ) / rho + (K - c) / rho + 2 := by
    calc
      (blaschkeActiveTailRadius a L : ℝ) + 2 ≤
          (L - c) / rho + 2 := by
            simpa only [add_comm] using add_le_add_right hRle 2
      _ = (k : ℝ) / rho + (K - c) / rho + 2 := by
        rw [show L = (k : ℝ) + K by rfl]
        ring
  have hAk :
      0 ≤ (2 + (K - c) / rho) * (k : ℝ) :=
    mul_nonneg hA hk
  have hinv : 0 < 1 / rho := by positivity
  rw [blaschkeActiveLinearConstant]
  dsimp only [L, c, rho] at hRle' hAk hinv ⊢
  push_cast
  calc
    (blaschkeActiveTailRadius a
          (blaschkeShiftedScale K k) : ℝ) + 2 ≤
        (k : ℝ) / blaschkeSpectralSlope a +
          (K - blaschkeSpectralOffset a) /
            blaschkeSpectralSlope a + 2 := hRle'
    _ ≤
        (2 + (K - blaschkeSpectralOffset a) /
              blaschkeSpectralSlope a +
            1 / blaschkeSpectralSlope a) *
          (1 + (k : ℝ)) := by
      have heq :
          (2 + (K - blaschkeSpectralOffset a) /
                blaschkeSpectralSlope a +
              1 / blaschkeSpectralSlope a) *
                (1 + (k : ℝ)) -
            ((k : ℝ) / blaschkeSpectralSlope a +
              (K - blaschkeSpectralOffset a) /
                blaschkeSpectralSlope a + 2) =
          1 / blaschkeSpectralSlope a +
            (2 + (K - blaschkeSpectralOffset a) /
              blaschkeSpectralSlope a) * (k : ℝ) := by
        ring
      nlinarith

theorem
    measureReal_countableTorusWeightedCoherenceHitUnion_blaschke_shiftedGaussian_le
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (hKnonneg : 0 ≤ K)
    (k N : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (ν : Measure (ℕ → UnitAddCircle)) [IsFiniteMeasure ν] (B : NNReal)
    (hhead :
      Measure.map
          (countableTorusHead
            (blaschkeActiveTailRadius a
              (blaschkeShiftedScale K k) + 2)) ν ≤
        B • volume)
    (hdeadline :
      (B : ℝ) * (N : ℝ) ≤
        Real.exp
          ((1 - delta) * blaschkeShiftedQuadraticClock a K k -
            blaschkeShiftedScale K k)) :
    ν.real
        (countableTorusWeightedCoherenceHitUnion
          (blaschkeLocalizedWeight a) N
          (Real.exp (-blaschkeShiftedScale K k))) ≤
      blaschkeActiveLinearConstant a K * Real.exp (Real.pi / 4) *
        (1 + (k : ℝ)) *
        Real.exp
          (-(delta / (4 * blaschkeSpectralSlope a)) *
            (k : ℝ) ^ 2) := by
  let L := blaschkeShiftedScale K k
  let M := blaschkeActiveTailRadius a L + 2
  let m := summableWeightedHeadMass (blaschkeLocalizedWeight a) M
  let Q := blaschkeShiftedQuadraticClock a K k
  have hLtail : blaschkeSpectralOffset a ≤ L := by
    dsimp only [L, blaschkeShiftedScale]
    have hk : 0 ≤ (k : ℝ) := by positivity
    linarith
  have hLzero : blaschkeSpectralSlope a ≤ L := by
    dsimp only [L, blaschkeShiftedScale]
    have hk : 0 ≤ (k : ℝ) := by positivity
    linarith
  have hwater : 1 ≤ m * Real.exp L := by
    simpa only [m, M] using
      one_le_blaschkeActiveHeadMass_mul_exp
        a ha0 hLzero
  have hη1 : Real.exp (-L) / m ≤ 1 := by
    simpa only [m, M] using
      exp_neg_div_blaschkeActiveHeadMass_le_one
        a ha0 ha1 hLzero
  have hbase :=
    measureReal_countableTorusWeightedCoherenceHitUnion_blaschke_le
      a ha0 ha1 N hLtail hLzero hη1 hwater ν B
      (by simpa only [M, L] using hhead)
  have hentropy :
      Q ≤ blaschkeDepthWaterEntropy a L := by
    simpa only [Q, L, blaschkeShiftedQuadraticClock] using
      (blaschkeDepthWaterEntropy_shifted_quadratic_bounds
        a ha0 ha1 hLtail hLzero).1
  have hlog : Real.log (m * Real.exp L) ≤ L := by
    simpa only [m, M] using
      log_blaschkeActiveHeadMass_mul_exp_le
        a ha0 ha1 L
  have hexpArg :
      (Real.pi / 4) *
            (Real.exp L * Real.exp (-L)) -
          blaschkeDepthWaterEntropy a L +
          (1 / 2 : ℝ) * Real.log (m * Real.exp L) ≤
        Real.pi / 4 - Q + L / 2 := by
    have hexpCancel : Real.exp L * Real.exp (-L) = 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [hexpCancel]
    nlinarith
  have hQ :
      (k : ℝ) ^ 2 / (4 * blaschkeSpectralSlope a) ≤ Q := by
    simpa only [Q] using
      blaschkeShiftedQuadraticClock_lower
        a ha0 ha1 hKtail k
  have hM :
      (M : ℝ) ≤
        blaschkeActiveLinearConstant a K * (1 + (k : ℝ)) := by
    simpa only [M, L] using
      blaschkeActiveHeadCard_shifted_le
        a ha0 ha1 hKtail k
  have hLnonneg : 0 ≤ L := by
    dsimp only [L, blaschkeShiftedScale]
    positivity
  have hmainExp :
      (1 - delta) * Q - L +
          (Real.pi / 4 - Q + L / 2) ≤
        Real.pi / 4 -
          (delta / (4 * blaschkeSpectralSlope a)) * (k : ℝ) ^ 2 := by
    have hdeltaQ :
        delta * ((k : ℝ) ^ 2 /
            (4 * blaschkeSpectralSlope a)) ≤ delta * Q :=
      mul_le_mul_of_nonneg_left hQ hdelta.le
    have hdeltaQ' :
        (delta / (4 * blaschkeSpectralSlope a)) * (k : ℝ) ^ 2 ≤
          delta * Q := by
      calc
        (delta / (4 * blaschkeSpectralSlope a)) * (k : ℝ) ^ 2 =
            delta * ((k : ℝ) ^ 2 /
              (4 * blaschkeSpectralSlope a)) := by ring
        _ ≤ delta * Q := hdeltaQ
    nlinarith
  have hbase' :
      ν.real
          (countableTorusWeightedCoherenceHitUnion
            (blaschkeLocalizedWeight a) N (Real.exp (-L))) ≤
        ((B : ℝ) * (N : ℝ)) * (M : ℝ) *
          Real.exp
            ((Real.pi / 4) * (Real.exp L * Real.exp (-L)) -
              blaschkeDepthWaterEntropy a L +
              (1 / 2 : ℝ) * Real.log (m * Real.exp L)) := by
    simpa only [L, M, m, mul_assoc] using hbase
  calc
    ν.real
        (countableTorusWeightedCoherenceHitUnion
          (blaschkeLocalizedWeight a) N
          (Real.exp (-blaschkeShiftedScale K k))) ≤
        ((B : ℝ) * (N : ℝ)) * (M : ℝ) *
          Real.exp
            ((Real.pi / 4) * (Real.exp L * Real.exp (-L)) -
              blaschkeDepthWaterEntropy a L +
              (1 / 2 : ℝ) * Real.log (m * Real.exp L)) := by
      simpa only [L] using hbase'
    _ ≤ Real.exp ((1 - delta) * Q - L) * (M : ℝ) *
          Real.exp (Real.pi / 4 - Q + L / 2) := by
      gcongr
    _ ≤ Real.exp
          (Real.pi / 4 -
            (delta / (4 * blaschkeSpectralSlope a)) * (k : ℝ) ^ 2) *
          (M : ℝ) := by
      rw [mul_right_comm, ← Real.exp_add]
      gcongr
    _ ≤ Real.exp
          (Real.pi / 4 -
            (delta / (4 * blaschkeSpectralSlope a)) * (k : ℝ) ^ 2) *
          (blaschkeActiveLinearConstant a K * (1 + (k : ℝ))) := by
      gcongr
    _ =
        blaschkeActiveLinearConstant a K * Real.exp (Real.pi / 4) *
          (1 + (k : ℝ)) *
          Real.exp
            (-(delta / (4 * blaschkeSpectralSlope a)) *
              (k : ℝ) ^ 2) := by
      have hexpSplit :
          Real.exp
              (Real.pi / 4 -
                delta / (4 * blaschkeSpectralSlope a) * (k : ℝ) ^ 2) =
            Real.exp (Real.pi / 4) *
              Real.exp
                (-(delta / (4 * blaschkeSpectralSlope a)) *
                  (k : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexpSplit]
      ring

/--
At every fixed positive fractional entropy gap, Blaschke-localized packets
almost surely avoid all proposed subentropy recurrence deadlines at every
sufficiently fine logarithmic scale.
-/
theorem
    ae_eventually_not_countableTorusWeightedCoherenceHitUnion_blaschke_subentropy
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (hKnonneg : 0 ≤ K)
    {delta : ℝ} (hdelta : 0 < delta)
    (ν : Measure (ℕ → UnitAddCircle)) [IsFiniteMeasure ν]
    (B : ℕ → NNReal) (N : ℕ → ℕ)
    (hhead : ∀ k,
      Measure.map
          (countableTorusHead
            (blaschkeActiveTailRadius a
              (blaschkeShiftedScale K k) + 2)) ν ≤
        B k • volume)
    (hdeadline : ∀ k,
      (B k : ℝ) * (N k : ℝ) ≤
        Real.exp
          ((1 - delta) * blaschkeShiftedQuadraticClock a K k -
            blaschkeShiftedScale K k)) :
    ∀ᵐ x ∂ν, ∀ᶠ k in Filter.atTop,
      x ∉ countableTorusWeightedCoherenceHitUnion
        (blaschkeLocalizedWeight a) (N k)
        (Real.exp (-blaschkeShiftedScale K k)) := by
  have hrho : 0 < blaschkeSpectralSlope a :=
    blaschkeSpectralSlope_pos a ha0 ha1
  have hconstant :
      0 ≤ blaschkeActiveLinearConstant a K *
        Real.exp (Real.pi / 4) := by
    have hshift :
        0 ≤ (K - blaschkeSpectralOffset a) /
          blaschkeSpectralSlope a :=
      div_nonneg (sub_nonneg.mpr hKtail) hrho.le
    have hinv : 0 < 1 / blaschkeSpectralSlope a := by positivity
    have hactive : 0 ≤ blaschkeActiveLinearConstant a K := by
      rw [blaschkeActiveLinearConstant]
      linarith
    positivity
  apply
    ae_eventually_not_countableTorusWeightedCoherenceHitUnion_of_polynomialGaussian
      ν (blaschkeLocalizedWeight a) N
        (fun k => Real.exp (-blaschkeShiftedScale K k))
      (blaschkeActiveLinearConstant a K * Real.exp (Real.pi / 4))
      hconstant 1
      (sigma := delta / (4 * blaschkeSpectralSlope a))
      (by positivity)
  intro k
  simpa only [pow_one, mul_assoc] using
    measureReal_countableTorusWeightedCoherenceHitUnion_blaschke_shiftedGaussian_le
      a ha0 ha1 hKtail hKzero hKnonneg k (N k) hdelta ν (B k)
      (hhead k) (hdeadline k)

/-- Explicit integer deadline at a fixed fractional gap below the exact
Blaschke spectral-depth clock. -/
def blaschkeHaarSubentropyDeadline
    (a K delta : ℝ) (k : ℕ) : ℕ :=
  ⌊Real.exp
      ((1 - delta) * blaschkeShiftedQuadraticClock a K k -
        blaschkeShiftedScale K k)⌋₊

/--
Unconditional product-Haar specialization. Almost every infinite phase
packet eventually has no positive recurrence through the explicit
subentropy deadline.
-/
theorem
    ae_eventually_not_countableTorusWeightedCoherenceHitUnion_blaschke_haar
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (hKnonneg : 0 ≤ K)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ =>
          (volume : Measure UnitAddCircle)),
      ∀ᶠ k in Filter.atTop,
        x ∉ countableTorusWeightedCoherenceHitUnion
          (blaschkeLocalizedWeight a)
          (blaschkeHaarSubentropyDeadline a K delta k)
          (Real.exp (-blaschkeShiftedScale K k)) := by
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  let ν : Measure (ℕ → UnitAddCircle) :=
    Measure.infinitePi (fun _ : ℕ =>
      (volume : Measure UnitAddCircle))
  have hhead : ∀ k,
      Measure.map
          (countableTorusHead
            (blaschkeActiveTailRadius a
              (blaschkeShiftedScale K k) + 2)) ν ≤
        (1 : NNReal) • volume := by
    intro k
    rw [one_smul]
    exact
      (map_countableTorusHead_infinitePi_volume
        (blaschkeActiveTailRadius a
          (blaschkeShiftedScale K k) + 2)).le
  have hdeadline : ∀ k,
      ((1 : NNReal) : ℝ) *
          (blaschkeHaarSubentropyDeadline a K delta k : ℝ) ≤
        Real.exp
          ((1 - delta) * blaschkeShiftedQuadraticClock a K k -
            blaschkeShiftedScale K k) := by
    intro k
    simp only [NNReal.coe_one, one_mul,
      blaschkeHaarSubentropyDeadline]
    exact Nat.floor_le (Real.exp_pos _).le
  simpa only [ν] using
    ae_eventually_not_countableTorusWeightedCoherenceHitUnion_blaschke_subentropy
      a ha0 ha1 hKtail hKzero hKnonneg hdelta ν
      (fun _ => (1 : NNReal))
      (blaschkeHaarSubentropyDeadline a K delta)
      hhead hdeadline

/--
Actual-first-return form of the product-Haar lower clock. Almost every
packet eventually has first coherence time strictly beyond the explicit
subentropy deadline.
-/
theorem
    ae_eventually_blaschkeHaarSubentropyDeadline_lt_firstCoherenceTime
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (hKnonneg : 0 ≤ K)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ =>
          (volume : Measure UnitAddCircle)),
      ∀ᶠ k in Filter.atTop,
        (blaschkeHaarSubentropyDeadline a K delta k :
            WithTop ℕ) <
          countableTorusWeightedFirstCoherenceTime
            (blaschkeLocalizedWeight a) x
            (Real.exp (-blaschkeShiftedScale K k)) := by
  filter_upwards [
    ae_eventually_not_countableTorusWeightedCoherenceHitUnion_blaschke_haar
      a ha0 ha1 hKtail hKzero hKnonneg hdelta] with x hx
  filter_upwards [hx] with k hk
  exact
    (not_mem_hitUnion_iff_deadline_lt_firstCoherenceTime
      (blaschkeLocalizedWeight a) x
      (blaschkeHaarSubentropyDeadline a K delta k)
      (Real.exp (-blaschkeShiftedScale K k))).mp hk

end RHTower
