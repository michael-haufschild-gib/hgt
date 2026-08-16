import GaloisForLFunctions.RHTower.XiMassCriticalTruePrimeCone
import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainderCone

/-!
# The bounded-coboundary bridge from the true-prime cone to the outgoing current

The true-prime cone and the outgoing Chebyshev current are not merely both equivalent to RH: they
differ pointwise by an explicitly decomposed uniformly bounded family.  Chaining the four exact
corpus identities

* `O = D + A` — outgoing current is the discrete Selberg current plus the floor sawtooth,
* `D = coneFlux + T` — the discrete current splits at the geometric cone edge,
* `coneFlux + E = -K(0) + C - Z` — the finite-cell Abel identity at the cone edge,
* `C + I = L` — the integer face,

with the three-layer prime split `L = P + Q + R` gives the exact coboundary identity

`P - O = K(0) + I + Z + E - Q - R - T - A`,

whose eight terms are each uniformly bounded.  Hence `P` and `O` represent the same class modulo
bounded families, and the cone depth is immaterial: two legal depths give true-prime cones with
uniformly bounded difference, which is the moving prime-annulus cancellation.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- **(14.1) The exact bounded-coboundary identity.** -/
theorem xiMassCriticalTruePrimeCone_sub_outgoingFlux_eq
    {a sigma d u : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    xiMassCriticalTruePrimeCone a sigma d u - xiMassCriticalOutgoingFlux a sigma u
      = xiMassCriticalDampedFourierProfile a sigma u 0
        + xiMassCriticalIntegerConeSum a sigma d u
        + (psiRemainder (⌊Real.exp (d * u / (d - 1 / 2))⌋₊) : ℂ)
            * xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((⌊Real.exp (d * u / (d - 1 / 2))⌋₊ : ℝ) + 1))
        + xiMassCriticalDiscreteRemainderConeOverflow a sigma d u
        - xiMassCriticalSquareCone a sigma d u
        - xiMassCriticalHighCone a sigma d u
        - xiMassCriticalDiscreteRemainderTailFlux a sigma u (d * u / (d - 1 / 2))
        - xiMassCriticalFloorSawtoothFlux a sigma u := by
  have ha : 0 < a := lt_trans (by norm_num) (lt_trans hdhalf hda)
  have hahalf : 1 / 2 < a := lt_trans hdhalf hda
  have h1 := xiMassCriticalOutgoingFlux_eq_discrete_add_floor hahalf hsigma u
  have h2 := xiMassCriticalDiscreteRemainderFlux_eq_cone_add_tail hdhalf hda hsigma hu
  have h3 := xiMassCriticalDiscreteRemainderConeFlux_add_overflow_eq_centeredAtomConeSum
    hdhalf hda hsigma hu
  have h4 := xiMassCriticalCentered_add_integer_eq_primeAtomConeSum a sigma d u
  have h5 := xiMassCriticalPrimeAtomConeSum_eq_three a sigma d u
  simp only at h3
  rw [h1, h2]
  linear_combination -h3 - h4 - h5

/-- **(14.2) The bounded coboundary.**  The true-prime cone and the outgoing current differ by a
uniformly bounded family. -/
theorem exists_norm_truePrimeCone_sub_outgoingFlux_bound
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma d u - xiMassCriticalOutgoingFlux a sigma u‖ ≤ B := by
  have ha : 0 < a := lt_trans (by norm_num) (lt_trans hdhalf hda)
  have hahalf : 1 / 2 < a := lt_trans hdhalf hda
  obtain ⟨BQ, hBQ⟩ := exists_norm_xiMassCriticalSquareCone_bound ha hsigma hdhalf hda
  set J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|)) with hJ
  set BI : ℝ := 2 * Real.pi + 2 * J / (d - 1 / 2) + 3 * J
    + 2 * xiMassCriticalOutgoingZeroShiftBound sigma with hBI
  set BR : ℝ := (∑' pk : Nat.Primes × ℕ, xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2)) * J
    with hBR
  set BE : ℝ := 8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2) with hBE
  refine ⟨J + BI + 8 * J + BE + BQ + BR + BE + 2 * xiMassCriticalOutgoingZeroShiftBound sigma,
    fun u hu => ?_⟩
  rw [xiMassCriticalTruePrimeCone_sub_outgoingFlux_eq hdhalf hda hsigma hu]
  have hK0 : ‖xiMassCriticalDampedFourierProfile a sigma u 0‖ ≤ J := by
    simpa only [hJ] using norm_xiMassCriticalDampedFourierProfile_zero_le ha hsigma
  have hI : ‖xiMassCriticalIntegerConeSum a sigma d u‖ ≤ BI := by
    simpa only [hBI, hJ] using norm_xiMassCriticalIntegerConeSum_le hahalf hsigma hdhalf hda hu
  have hZ : ‖(psiRemainder (⌊Real.exp (d * u / (d - 1 / 2))⌋₊) : ℂ)
      * xiMassCriticalDampedFourierProfile a sigma u
        (Real.log ((⌊Real.exp (d * u / (d - 1 / 2))⌋₊ : ℝ) + 1))‖ ≤ 8 * J := by
    simpa only [hJ] using norm_xiMassCriticalDiscreteRemainder_terminalFlux_le
      hdhalf hda hsigma hu
  have hE : ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ ≤ BE := by
    simpa only [hBE] using norm_xiMassCriticalDiscreteRemainderConeOverflow_le
      hdhalf hda hsigma hu
  have hRhigh : ‖xiMassCriticalHighCone a sigma d u‖ ≤ BR := by
    simpa only [hBR, hJ] using norm_xiMassCriticalHighCone_le ha hsigma d u
  have hT : ‖xiMassCriticalDiscreteRemainderTailFlux a sigma u (d * u / (d - 1 / 2))‖ ≤ BE := by
    simpa only [hBE] using norm_xiMassCriticalDiscreteRemainder_superluminalTailFlux_le
      hdhalf hda hsigma hu
  have hA : ‖xiMassCriticalFloorSawtoothFlux a sigma u‖
      ≤ 2 * xiMassCriticalOutgoingZeroShiftBound sigma :=
    norm_xiMassCriticalFloorSawtoothFlux_le ha hsigma u
  have hoct : ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : ℂ,
      ‖x₁ + x₂ + x₃ + x₄ - x₅ - x₆ - x₇ - x₈‖
        ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ + ‖x₅‖ + ‖x₆‖ + ‖x₇‖ + ‖x₈‖ := by
    intro x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈
    have e1 := norm_sub_le (x₁ + x₂ + x₃ + x₄ - x₅ - x₆ - x₇) x₈
    have e2 := norm_sub_le (x₁ + x₂ + x₃ + x₄ - x₅ - x₆) x₇
    have e3 := norm_sub_le (x₁ + x₂ + x₃ + x₄ - x₅) x₆
    have e4 := norm_sub_le (x₁ + x₂ + x₃ + x₄) x₅
    have e5 := norm_add_le (x₁ + x₂ + x₃) x₄
    have e6 := norm_add_le (x₁ + x₂) x₃
    have e7 := norm_add_le x₁ x₂
    linarith
  have hQ := hBQ u hu
  have hchain := hoct (xiMassCriticalDampedFourierProfile a sigma u 0)
    (xiMassCriticalIntegerConeSum a sigma d u)
    ((psiRemainder (⌊Real.exp (d * u / (d - 1 / 2))⌋₊) : ℂ)
      * xiMassCriticalDampedFourierProfile a sigma u
        (Real.log ((⌊Real.exp (d * u / (d - 1 / 2))⌋₊ : ℝ) + 1)))
    (xiMassCriticalDiscreteRemainderConeOverflow a sigma d u)
    (xiMassCriticalSquareCone a sigma d u)
    (xiMassCriticalHighCone a sigma d u)
    (xiMassCriticalDiscreteRemainderTailFlux a sigma u (d * u / (d - 1 / 2)))
    (xiMassCriticalFloorSawtoothFlux a sigma u)
  linarith [hchain, hK0, hI, hZ, hE, hQ, hRhigh, hT, hA]

/-- **(14.7) The prime-power face is the same class.**  The prime-atom cone and the true-prime cone
differ by a uniformly bounded family. -/
theorem exists_norm_primeAtomCone_sub_truePrimeCone_bound
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalPrimeAtomConeSum a sigma d u
        - xiMassCriticalTruePrimeCone a sigma d u‖ ≤ B := by
  have ha : 0 < a := lt_trans (by norm_num) (lt_trans hdhalf hda)
  obtain ⟨BQ, hBQ⟩ := exists_norm_xiMassCriticalSquareCone_bound ha hsigma hdhalf hda
  set BR : ℝ := (∑' pk : Nat.Primes × ℕ, xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2))
    * (∫ x : ℝ, Real.exp (-(sigma * |x|))) with hBR
  refine ⟨BQ + BR, fun u hu => ?_⟩
  have hsplit : xiMassCriticalPrimeAtomConeSum a sigma d u
      - xiMassCriticalTruePrimeCone a sigma d u
      = xiMassCriticalSquareCone a sigma d u + xiMassCriticalHighCone a sigma d u := by
    rw [xiMassCriticalPrimeAtomConeSum_eq_three]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add (hBQ u hu) ?_)
  simpa only [hBR] using norm_xiMassCriticalHighCone_le ha hsigma d u

/-- **(14.7) The centered face is the same class.**  The centered-atom cone and the prime-atom cone
differ by the uniformly bounded integer face. -/
theorem exists_norm_primeAtomCone_sub_centeredCone_bound
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalPrimeAtomConeSum a sigma d u
        - xiMassCriticalCenteredAtomConeSum a sigma d u‖ ≤ B := by
  have hahalf : 1 / 2 < a := lt_trans hdhalf hda
  refine ⟨2 * Real.pi + 2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2)
    + 3 * (∫ x : ℝ, Real.exp (-(sigma * |x|)))
    + 2 * xiMassCriticalOutgoingZeroShiftBound sigma, fun u hu => ?_⟩
  have hsplit : xiMassCriticalPrimeAtomConeSum a sigma d u
      - xiMassCriticalCenteredAtomConeSum a sigma d u
      = xiMassCriticalIntegerConeSum a sigma d u := by
    rw [← xiMassCriticalCentered_add_integer_eq_primeAtomConeSum]
    ring
  rw [hsplit]
  exact norm_xiMassCriticalIntegerConeSum_le hahalf hsigma hdhalf hda hu

/-- **(14.8) Uniform prime-annulus cancellation.**  Two legal cone depths give true-prime cones
whose difference is uniformly bounded. -/
theorem exists_norm_truePrimeCone_depth_difference_bound
    {a sigma d₁ d₂ : ℝ} (hd₁ : 1 / 2 < d₁) (hd₁a : d₁ < a) (hd₂ : 1 / 2 < d₂) (hd₂a : d₂ < a)
    (hsigma : 0 < sigma) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma d₁ u
        - xiMassCriticalTruePrimeCone a sigma d₂ u‖ ≤ B := by
  obtain ⟨B₁, hB₁⟩ := exists_norm_truePrimeCone_sub_outgoingFlux_bound hd₁ hd₁a hsigma
  obtain ⟨B₂, hB₂⟩ := exists_norm_truePrimeCone_sub_outgoingFlux_bound hd₂ hd₂a hsigma
  refine ⟨B₁ + B₂, fun u hu => ?_⟩
  have hsplit : xiMassCriticalTruePrimeCone a sigma d₁ u
      - xiMassCriticalTruePrimeCone a sigma d₂ u
      = (xiMassCriticalTruePrimeCone a sigma d₁ u - xiMassCriticalOutgoingFlux a sigma u)
        - (xiMassCriticalTruePrimeCone a sigma d₂ u - xiMassCriticalOutgoingFlux a sigma u) := by
    ring
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add (hB₁ u hu) (hB₂ u hu))

/-! ## Admissible cone slopes -/

/-- The depth realizing a prescribed cone slope. -/
noncomputable def xiMassConeDepthOfSlope (κ : ℝ) : ℝ := κ / (2 * (κ - 1))

theorem xiMassConeDepthOfSlope_slope {κ : ℝ} (hκ : 1 < κ) :
    xiMassConeDepthOfSlope κ / (xiMassConeDepthOfSlope κ - 1 / 2) = κ := by
  have hκ1 : κ - 1 > 0 := by linarith
  have hsub : xiMassConeDepthOfSlope κ - 1 / 2 = 1 / (2 * (κ - 1)) := by
    rw [xiMassConeDepthOfSlope]
    field_simp
    ring
  rw [hsub, xiMassConeDepthOfSlope]
  field_simp

theorem xiMassConeDepthOfSlope_half_lt {κ : ℝ} (hκ : 1 < κ) :
    1 / 2 < xiMassConeDepthOfSlope κ := by
  have hκ1 : (0 : ℝ) < κ - 1 := by linarith
  rw [xiMassConeDepthOfSlope, lt_div_iff₀ (by positivity)]
  linarith

/-- **The admissible slope range.**  A slope is realized by a legal depth exactly when it exceeds
the strip slope `a/(a-1/2)`. -/
theorem xiMassConeDepthOfSlope_lt_iff {a κ : ℝ} (ha : 1 / 2 < a) (hκ : 1 < κ) :
    xiMassConeDepthOfSlope κ < a ↔ a / (a - 1 / 2) < κ := by
  have hκ1 : (0 : ℝ) < κ - 1 := by linarith
  have hahalf : (0 : ℝ) < a - 1 / 2 := by linarith
  rw [xiMassConeDepthOfSlope, div_lt_iff₀ (by positivity), div_lt_iff₀ hahalf]
  constructor <;> intro h <;> nlinarith

/-! ## Endpoint stabilization of the arithmetic prefix -/

/-- The cone edge decreases in the depth. -/
theorem xiMassConeEdge_antitone {d a u : ℝ} (hd : 1 / 2 < d) (hda : d < a) (hu : 0 ≤ u) :
    a * u / (a - 1 / 2) ≤ d * u / (d - 1 / 2) := by
  have hd0 : (0 : ℝ) < d - 1 / 2 := by linarith
  have ha0 : (0 : ℝ) < a - 1 / 2 := by linarith
  rw [div_le_div_iff₀ ha0 hd0]
  nlinarith

/-- **The arithmetic prefix stabilizes at the strip endpoint.**  For each fixed height, all depths
close enough to the strip width give the same rounded cone cutoff as the endpoint depth. -/
theorem exists_depth_floor_stabilizes {a u : ℝ} (ha : 1 / 2 < a) (hu : 0 ≤ u) :
    ∃ d₀ : ℝ, 1 / 2 < d₀ ∧ d₀ < a ∧ ∀ d : ℝ, d₀ ≤ d → d < a →
      ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ = ⌊Real.exp (a * u / (a - 1 / 2))⌋₊ := by
  set N : ℕ := ⌊Real.exp (a * u / (a - 1 / 2))⌋₊ with hN
  have hlt : Real.exp (a * u / (a - 1 / 2)) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hge : (N : ℝ) ≤ Real.exp (a * u / (a - 1 / 2)) :=
    Nat.floor_le (Real.exp_pos _).le
  have ha0 : (0 : ℝ) < a - 1 / 2 := by linarith
  have hcont : ContinuousAt (fun d : ℝ => Real.exp (d * u / (d - 1 / 2))) a := by
    refine Real.continuous_exp.continuousAt.comp ?_
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    linarith
  have hev : ∀ᶠ d in nhds a, Real.exp (d * u / (d - 1 / 2)) < (N : ℝ) + 1 :=
    hcont.eventually_lt_const hlt
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨max (1 / 2 + (a - 1 / 2) / 2) (a - ε / 2), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · refine max_lt (by linarith) (by linarith)
  · intro d hd0 hda
    have hd : 1 / 2 < d := lt_of_lt_of_le (by linarith) (le_trans (le_max_left _ _) hd0)
    have hdlow : a - ε / 2 ≤ d := le_trans (le_max_right _ _) hd0
    have hdist : dist d a < ε := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    have hupper : Real.exp (d * u / (d - 1 / 2)) < (N : ℝ) + 1 := hball hdist
    have hlower : (N : ℝ) ≤ Real.exp (d * u / (d - 1 / 2)) :=
      le_trans hge (Real.exp_le_exp.2 (xiMassConeEdge_antitone hd hda hu))
    rw [Nat.floor_eq_iff (Real.exp_pos _).le]
    exact ⟨hlower, hupper⟩

end

end RHTower
