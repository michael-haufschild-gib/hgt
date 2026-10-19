import GaloisForLFunctions.BiScaleUncertainty.PoleInvisibilityOnGappedBlindGrids
import GaloisForLFunctions.BiScaleUncertainty.LogarithmicCompressionEnergy

/-!
# Square-root node density decides whether the pole constraint is visible

`PoleInvisibilityOnGappedBlindGrids` shows that the pole constraint of zero-pole blind positivity
is invisible when the blind node set has far gaps of fixed logarithmic width. Here the gaps may
shrink. A node set has *sub-square-root window density* if, along arbitrarily far windows
`X ≤ log n ≤ X + 1`, the number `K` of its nodes obeys `M (K + 1)(1 + log(K + 1)) ≤ e^{X/2}`
for every prescribed `M`.

**Mechanism.** By pigeonhole a window with `K` nodes has a node-free point `T` at logarithmic
distance `1/(2(K+1))` from every node. Compress the corpus bump by `L = K + 1`: its correlation
lives in `|x| ≤ 1/(5L)`, its normalized Lévy energy is `≤ A + log L`
(`exists_sourceRescale_logarithmic_energy_bound_of_support`), its mass is `≍ 1/L` and its
half-exponential moments are `≍ 1/L`. The distant pair `b_L(u) - σ b_L(u - T)` is then blind on
the node set, its pole term is `≍ e^{T/2}/L²` with either sign, and its archimedean part is
`O((1 + log L)/L)`. The cost of transporting unit pole mass is
`O(L (1 + log L) e^{-X/2})`, which the density hypothesis makes arbitrarily small.

**Theorems.**
* `exists_blindOn_poleMass_eq_abs_archOnly_le_of_density`: every pole mass is carried at
  arbitrarily small archimedean cost, so zero-pole and pole-free infima coincide
  (`exists_blindOn_poleMass_zero_archOnly_close_of_density`) and zero-pole positivity fails
  (`not_zeroPoleBlindPositiveOn_of_density`).
* `subSqrtWindowDensity_smooth`: for every finite set `S`, the `S`-smooth integers have at most
  `(⌊(X+1)/log 2⌋ + 1)^{|S|}` nodes in a window, polynomial in `X`, hence sub-square-root density.
* `not_zeroPoleBlindPositiveOn_smooth`: blindness at the `S`-smooth integers, for any finite
  set of primes, never suffices for zero-pole positivity, whereas blindness at all integers is
  equivalent to RH. The integers have `≍ e^{X}` nodes per window, beyond the threshold `e^{X/2}`:
  the pole weight `e^{x/2}` is what makes square-root node density critical.
-/

open MeasureTheory Set Filter Topology Complex Finsupp
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.WeilOneSided

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. The distant pair of an arbitrary source -/

/-- A real compact `C²` source as a corpus Weil test. -/
def realTest (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) : WeilTestFn :=
  ⟨fun u => ((f u : ℝ) : ℂ), Complex.ofRealCLM.contDiff.comp hf, hfc.comp_left Complex.ofReal_zero⟩

/-- A distant pair is blind at every node outside the correlation radius of the seed and of
its copy. -/
theorem logValue_realTest_subtractCopy_eq_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {D : ℝ} (hsupp : ∀ x, D < |x| → autocorr f x = 0)
    (hD : D < Real.log 2) (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) {n : ℕ} (hn : 2 ≤ n)
    (hgap : D < |Real.log n - T|) :
    logValue (realTest (subtractCopy f σ T) (contDiff_subtractCopy hf σ T)
      (hasCompactSupport_subtractCopy hfc σ T)).1 n = 0 := by
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hval : autocorr (subtractCopy f σ T) (Real.log n) = 0 := by
    rw [autocorr_subtractCopy hf.continuous hfc,
      hsupp (Real.log n) (by rw [abs_of_pos (by linarith)]; linarith), hsupp _ hgap,
      hsupp (Real.log n + T) (by rw [abs_of_pos (by linarith)]; linarith)]
    ring
  have h1 := RHTower.AutocorrelationKrein.weilTest_eq (subtractCopy f σ T) (Real.log n)
  have h2 := RHTower.AutocorrelationKrein.weilTest_eq (subtractCopy f σ T) (-Real.log n)
  rw [autocorr_neg, hval] at h2
  rw [hval] at h1
  change (EF.weilTest (fun u => ((subtractCopy f σ T u : ℝ) : ℂ))
      (fun u => ((subtractCopy f σ T u : ℝ) : ℂ)) (Real.log n) +
    EF.weilTest (fun u => ((subtractCopy f σ T u : ℝ) : ℂ))
      (fun u => ((subtractCopy f σ T u : ℝ) : ℂ)) (-Real.log n)).re / Real.sqrt n = 0
  rw [h1, h2]
  simp

/-- The pole term of a distant pair. -/
theorem pole_realTest_subtractCopy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (σ T : ℝ) :
    (weilPoleTerm (EF.weilTest (realTest (subtractCopy f σ T) (contDiff_subtractCopy hf σ T)
      (hasCompactSupport_subtractCopy hfc σ T)).1 (realTest (subtractCopy f σ T)
      (contDiff_subtractCopy hf σ T) (hasCompactSupport_subtractCopy hfc σ T)).1)).re =
      2 * ((1 - σ * Real.exp ((1 / 2) * T)) * (1 - σ * Real.exp ((-(1 / 2)) * T))) *
        ((∫ u, f u * Real.exp ((1 / 2) * u)) * ∫ u, f u * Real.exp ((-(1 / 2)) * u)) := by
  change (weilPoleTerm (EF.weilTest (fun u => ((subtractCopy f σ T u : ℝ) : ℂ))
    (fun u => ((subtractCopy f σ T u : ℝ) : ℂ)))).re = _
  rw [re_weilPoleTerm_ofReal_eq_moment_mul (contDiff_subtractCopy hf σ T).continuous
    (hasCompactSupport_subtractCopy hfc σ T),
    integral_subtractCopy_mul_exp hf.continuous hfc, integral_subtractCopy_mul_exp hf.continuous hfc]
  ring

/-- The archimedean part (without the pole) of a distant pair is bounded independently of the
separation. -/
theorem abs_archOnly_realTest_subtractCopy_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {D : ℝ} (hD : 0 ≤ D) (hsupp : ∀ x, D < |x| → autocorr f x = 0)
    {σ T : ℝ} (hσ : σ ^ 2 = 1) (hT : D + 1 ≤ T) :
    |WeilOneSided.weilArchRe (EF.weilTest (realTest (subtractCopy f σ T)
        (contDiff_subtractCopy hf σ T) (hasCompactSupport_subtractCopy hfc σ T)).1
        (realTest (subtractCopy f σ T) (contDiff_subtractCopy hf σ T)
          (hasCompactSupport_subtractCopy hfc σ T)).1) -
      (weilPoleTerm (EF.weilTest (realTest (subtractCopy f σ T) (contDiff_subtractCopy hf σ T)
        (hasCompactSupport_subtractCopy hfc σ T)).1 (realTest (subtractCopy f σ T)
        (contDiff_subtractCopy hf σ T) (hasCompactSupport_subtractCopy hfc σ T)).1)).re| ≤
      2 * |EF.gammaBracket 0| * autocorr f 0 + 2 * biScaleLevyEnergy f +
        2 / (1 - Real.exp (-2)) * ∫ x, |autocorr f x| := by
  change |WeilOneSided.weilArchRe (EF.weilTest (fun u => ((subtractCopy f σ T u : ℝ) : ℂ))
      (fun u => ((subtractCopy f σ T u : ℝ) : ℂ))) -
    (weilPoleTerm (EF.weilTest (fun u => ((subtractCopy f σ T u : ℝ) : ℂ))
      (fun u => ((subtractCopy f σ T u : ℝ) : ℂ)))).re| ≤ _
  rw [weilArchRe_ofReal_eq_pole_add_gamma_add_biScaleLevyEnergy (contDiff_subtractCopy hf σ T)
    (hasCompactSupport_subtractCopy hfc σ T),
    show ∀ a b c : ℝ, a + b + c - a = b + c from fun a b c => by ring,
    biScaleLevyEnergy_subtractCopy hf hfc hsupp hT σ]
  have h0 : autocorr (subtractCopy f σ T) 0 = 2 * autocorr f 0 := by
    rw [autocorr_subtractCopy hf.continuous hfc, zero_sub, zero_add, autocorr_neg,
      hsupp T (by rw [abs_of_pos (by linarith)]; linarith), hσ]
    ring
  rw [h0, hσ]
  have htail := abs_integral_shifted_autocorr_arch_le hf hfc hsupp hT
  have hfac : copyTailFactor D T ≤ 2 / (1 - Real.exp (-2)) := by
    unfold copyTailFactor
    have hd : 0 < 1 - Real.exp (-2) := by
      have := Real.exp_lt_one_iff.mpr (show (-2 : ℝ) < 0 by norm_num); linarith
    apply div_le_div_of_nonneg_right _ hd.le
    have : Real.exp (-(T - D) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hint : 0 ≤ ∫ x, |autocorr f x| := integral_nonneg fun _ => abs_nonneg _
  have htail' : |∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x| ≤
      2 / (1 - Real.exp (-2)) * ∫ x, |autocorr f x| :=
    htail.trans (mul_le_mul_of_nonneg_right hfac hint)
  have hσabs : |σ| = 1 := by
    have : |σ| ^ 2 = 1 := by rw [sq_abs, hσ]
    nlinarith [abs_nonneg σ]
  have hJ : 0 ≤ biScaleLevyEnergy f := biScaleLevyEnergy_nonneg hfc hf.continuous
  have h00 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg _
  have e1 : |EF.gammaBracket 0 * (2 * autocorr f 0)| = 2 * |EF.gammaBracket 0| * autocorr f 0 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * autocorr f 0)]; ring
  have e2 : |(1 + 1) * biScaleLevyEnergy f| = 2 * biScaleLevyEnergy f := by
    rw [abs_of_nonneg (by positivity)]; ring
  have e3 : |σ * ∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x| =
      |∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x| := by
    rw [abs_mul, hσabs, one_mul]
  rw [← add_assoc]
  refine (abs_add_three _ _ _).trans ?_
  rw [e1, e2, e3]
  linarith

/-! ### 2. The compressed bump -/

/-- The corpus bump compressed by the factor `L`. -/
abbrev compressedBump (L : ℝ) : ℝ → ℝ := sourceRescale pairBump L

theorem contDiff_compressedBump (L : ℝ) : ContDiff ℝ 2 (compressedBump L) :=
  contDiff_sourceRescale contDiff_pairBump L

theorem hasCompactSupport_compressedBump {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (compressedBump L) :=
  hasCompactSupport_sourceRescale hasCompactSupport_pairBump hL

theorem autocorr_pairBump_zero_pos : 0 < autocorr pairBump 0 := by
  rw [← integral_sq_eq_autocorr_zero]
  have hc : Continuous fun u => pairBump u ^ 2 := (adjBump.continuous).pow 2
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_pairBump.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num))
    (fun _ => sq_nonneg _) (x := 0) ?_
  rw [show pairBump 0 = adjBump 0 from rfl,
    adjBump.one_of_mem_closedBall (Metric.mem_closedBall_self adjBump.rIn_pos.le)]
  norm_num

theorem autocorr_compressedBump_eq_zero {L : ℝ} (hL : 0 < L) {x : ℝ} (hx : 1 / (5 * L) < |x|) :
    autocorr (compressedBump L) x = 0 := by
  rw [autocorr_sourceRescale pairBump hL, autocorr_pairBump_eq_zero, mul_zero]
  rw [abs_mul, abs_of_pos hL]
  rw [div_lt_iff₀ (by positivity)] at hx
  linarith

theorem autocorr_compressedBump_zero {L : ℝ} (hL : 0 < L) :
    autocorr (compressedBump L) 0 = L⁻¹ * autocorr pairBump 0 := by
  rw [autocorr_sourceRescale pairBump hL, mul_zero]

theorem integral_abs_autocorr_compressedBump {L : ℝ} (hL : 0 < L) :
    ∫ x, |autocorr (compressedBump L) x| = L⁻¹ * L⁻¹ * ∫ x, |autocorr pairBump x| := by
  have h : (fun x => |autocorr (compressedBump L) x|) =
      fun x => L⁻¹ * |autocorr pairBump (L * x)| := by
    funext x
    rw [autocorr_sourceRescale pairBump hL, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  rw [h, integral_const_mul, Measure.integral_comp_mul_left (fun x => |autocorr pairBump x|) L,
    abs_of_pos (inv_pos.mpr hL), smul_eq_mul, mul_assoc]

/-- Half-exponential moments of the compressed bump are at least `e^{-1/20}/L` times the bump
mass. -/
theorem moment_compressedBump_ge {L : ℝ} (hL : 1 ≤ L) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    Real.exp (-(1 / 20)) * (L⁻¹ * ∫ v, pairBump v) ≤
      ∫ u, compressedBump L u * Real.exp (s * u) := by
  have hL0 : 0 < L := by linarith
  have hchange : (∫ u, compressedBump L u * Real.exp (s * u)) =
      L⁻¹ * ∫ v, pairBump v * Real.exp (s / L * v) := by
    have h := Measure.integral_comp_mul_left (fun v => pairBump v * Real.exp (s / L * v)) L
    simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hL0)] at h
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [sourceRescale]
    congr 2
    field_simp
  rw [hchange, show Real.exp (-(1 / 20)) * (L⁻¹ * ∫ v, pairBump v) =
    L⁻¹ * (Real.exp (-(1 / 20)) * ∫ v, pairBump v) by ring]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hL0.le)
  rw [← integral_const_mul]
  have hb : Continuous pairBump := adjBump.continuous
  have hi1 : Integrable fun v => Real.exp (-(1 / 20)) * pairBump v :=
    (hb.integrable_of_hasCompactSupport hasCompactSupport_pairBump).const_mul _
  have hi2 : Integrable fun v => pairBump v * Real.exp (s / L * v) :=
    (hb.mul (by fun_prop)).integrable_of_hasCompactSupport hasCompactSupport_pairBump.mul_right
  refine integral_mono hi1 hi2 fun v => ?_
  by_cases hv : 1 / 10 ≤ |v|
  · simp [pairBump, adjBump_eq_zero hv]
  · have hv' : |v| < 1 / 10 := lt_of_not_ge hv
    have hexp : Real.exp (-(1 / 20)) ≤ Real.exp (s / L * v) := by
      apply Real.exp_le_exp.mpr
      have h1 : |s / L * v| ≤ 1 / 20 := by
        rw [abs_mul, abs_div, abs_of_pos hL0]
        have : |s| / L ≤ 1 / 2 := by
          rw [div_le_iff₀ hL0]; nlinarith [abs_nonneg s]
        nlinarith [abs_nonneg v, abs_nonneg s, div_nonneg (abs_nonneg s) hL0.le]
      linarith [neg_abs_le (s / L * v)]
    have hb0 : 0 ≤ pairBump v := adjBump.nonneg
    nlinarith

/-! ### 3. A node-free point in every window -/

/-- **Pigeonhole gap.** A finite set of reals leaves, inside `[X, X + 1]`, a point at distance at
least `1/(2(K+1))` from every element and from the window ends, where `K` is the set's size. -/
theorem exists_far_point (F : Finset ℝ) (X : ℝ) :
    ∃ T : ℝ, X + 1 / (2 * ((F.card : ℝ) + 1)) ≤ T ∧ T ≤ X + 1 - 1 / (2 * ((F.card : ℝ) + 1)) ∧
      ∀ a ∈ F, 1 / (2 * ((F.card : ℝ) + 1)) ≤ |a - T| := by
  classical
  set K : ℕ := F.card with hK
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  set idx : ℝ → ℕ := fun a => ⌊(a - X) * ((K : ℝ) + 1)⌋₊ with hidx
  have hcard : (F.image idx).card < (Finset.range (K + 1)).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Finset.card_image_le (Nat.lt_succ_self K)
  obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hjK : (j : ℝ) ≤ K := by
    have := Finset.mem_range.mp hj; exact_mod_cast Nat.lt_succ_iff.mp this
  refine ⟨X + ((j : ℝ) + 1 / 2) / ((K : ℝ) + 1), ?_, ?_, ?_⟩
  · have : (1 : ℝ) / (2 * ((K : ℝ) + 1)) = (1 / 2) / ((K : ℝ) + 1) := by field_simp
    rw [this]
    have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have := div_le_div_of_nonneg_right (show (1 : ℝ) / 2 ≤ (j : ℝ) + 1 / 2 by linarith) hK1.le
    linarith
  · have e : X + 1 - 1 / (2 * ((K : ℝ) + 1)) = X + ((K : ℝ) + 1 / 2) / ((K : ℝ) + 1) := by
      field_simp; ring
    rw [e]
    have := div_le_div_of_nonneg_right (show (j : ℝ) + 1 / 2 ≤ (K : ℝ) + 1 / 2 by linarith) hK1.le
    linarith
  · intro a ha
    by_contra hlt
    rw [not_le] at hlt
    have hmem : idx a = j := by
      rw [hidx]
      simp only
      rw [Nat.floor_eq_iff]
      · have h1 := (abs_lt.mp hlt)
        constructor
        · have : (j : ℝ) / ((K : ℝ) + 1) ≤ a - X := by
            have e : 1 / (2 * ((K : ℝ) + 1)) = (1 / 2) / ((K : ℝ) + 1) := by field_simp
            rw [e] at h1
            have := h1.1
            rw [show ((j : ℝ) + 1 / 2) / ((K : ℝ) + 1) = (j : ℝ) / ((K : ℝ) + 1) +
              (1 / 2) / ((K : ℝ) + 1) by ring] at this
            linarith
          rwa [div_le_iff₀ hK1] at this
        · have : a - X < ((j : ℝ) + 1) / ((K : ℝ) + 1) := by
            have e : 1 / (2 * ((K : ℝ) + 1)) = (1 / 2) / ((K : ℝ) + 1) := by field_simp
            rw [e] at h1
            have := h1.2
            rw [show ((j : ℝ) + 1) / ((K : ℝ) + 1) = ((j : ℝ) + 1 / 2) / ((K : ℝ) + 1) +
              (1 / 2) / ((K : ℝ) + 1) by ring]
            linarith
          rwa [lt_div_iff₀ hK1] at this
      · have h1 := (abs_lt.mp hlt).1
        have hpos : 0 ≤ a - X := by
          have : 0 ≤ ((j : ℝ) + 1 / 2) / ((K : ℝ) + 1) - 1 / (2 * ((K : ℝ) + 1)) := by
            rw [show ((j : ℝ) + 1 / 2) / ((K : ℝ) + 1) - 1 / (2 * ((K : ℝ) + 1)) =
              (j : ℝ) / ((K : ℝ) + 1) by field_simp; ring]
            positivity
          linarith
        positivity
    exact hjn (Finset.mem_image.mpr ⟨a, ha, hmem⟩)

/-! ### 4. The compressed distant pair -/

theorem one_add_nat_pos (k : ℕ) : (0 : ℝ) < (k : ℝ) + 1 := by positivity

/-- The distant pair of the bump compressed by `k + 1`. -/
def compressedCarrier (k : ℕ) (σ T : ℝ) : WeilTestFn :=
  realTest (subtractCopy (compressedBump ((k : ℝ) + 1)) σ T)
    (contDiff_subtractCopy (contDiff_compressedBump _) σ T)
    (hasCompactSupport_subtractCopy (hasCompactSupport_compressedBump (one_add_nat_pos k)) σ T)

private theorem compressed_energy_exists :
    ∃ A : ℝ, ∀ L : ℝ, 0 < L → 1 / 5 ≤ L →
      normalizedArchEnergy (sourceRescale pairBump L) ≤ A + Real.log L :=
  exists_sourceRescale_logarithmic_energy_bound_of_support contDiff_pairBump
    hasCompactSupport_pairBump autocorr_pairBump_zero_pos (by norm_num)
    (fun x hx => autocorr_pairBump_eq_zero hx.le)

/-- The logarithmic energy constant of the compressed bump. -/
def compressedEnergyConstant : ℝ := Classical.choose compressed_energy_exists

theorem normalizedArchEnergy_compressedBump_le {L : ℝ} (hL : 1 ≤ L) :
    normalizedArchEnergy (compressedBump L) ≤ compressedEnergyConstant + Real.log L :=
  Classical.choose_spec compressed_energy_exists L (by linarith) (by linarith)

/-- The archimedean constant of the compressed distant pair. -/
def compressedArchConstant : ℝ :=
  2 * |EF.gammaBracket 0| * autocorr pairBump 0 +
    2 * autocorr pairBump 0 * (|compressedEnergyConstant| + 1) +
      2 / (1 - Real.exp (-2)) * ∫ x, |autocorr pairBump x|

theorem compressedArchConstant_nonneg : 0 ≤ compressedArchConstant := by
  have h1 : 0 ≤ ∫ x, |autocorr pairBump x| := integral_nonneg fun _ => abs_nonneg _
  have h2 : 0 < 1 - Real.exp (-2) := by
    have := Real.exp_lt_one_iff.mpr (show (-2 : ℝ) < 0 by norm_num); linarith
  have := autocorr_pairBump_zero_pos
  unfold compressedArchConstant; positivity

/-- The pole constant `κ = (1 - e^{-1/2}) (e^{-1/20} ∫ b)²`. -/
def carrierPoleConstant : ℝ :=
  (1 - Real.exp (-(1 / 2))) * (Real.exp (-(1 / 20)) * ∫ v, pairBump v) ^ 2

theorem integral_pairBump_pos : 0 < ∫ v, pairBump v := by
  have hc : Continuous pairBump := adjBump.continuous
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hasCompactSupport_pairBump
    (fun _ => adjBump.nonneg) (x := 0) ?_
  rw [show pairBump 0 = adjBump 0 from rfl,
    adjBump.one_of_mem_closedBall (Metric.mem_closedBall_self adjBump.rIn_pos.le)]
  norm_num

theorem carrierPoleConstant_pos : 0 < carrierPoleConstant := by
  have h1 : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h2 : 0 < Real.exp (-(1 / 20)) * ∫ v, pairBump v :=
    mul_pos (Real.exp_pos _) integral_pairBump_pos
  unfold carrierPoleConstant; exact mul_pos (by linarith) (pow_pos h2 2)

/-- The separation factor of the pole term is at least `(1 - e^{-1/2})(e^{X/2} - 1)`. -/
theorem separation_factor_ge {σ X T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hX : 1 ≤ X) (hXT : X ≤ T) :
    (1 - Real.exp (-(1 / 2))) * (Real.exp (X / 2) - 1) ≤
      |(1 - σ * Real.exp ((1 / 2) * T)) * (1 - σ * Real.exp ((-(1 / 2)) * T))| := by
  have heT : Real.exp (X / 2) ≤ Real.exp ((1 / 2) * T) := Real.exp_le_exp.mpr (by linarith)
  have he1 : 1 ≤ Real.exp (X / 2) := Real.one_le_exp_iff.mpr (by linarith)
  have he2 : Real.exp ((-(1 / 2)) * T) ≤ Real.exp (-(1 / 2)) := Real.exp_le_exp.mpr (by linarith)
  have he2' : 0 < Real.exp ((-(1 / 2)) * T) := Real.exp_pos _
  have he3 : Real.exp (-(1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  rw [abs_mul]
  rcases hσ with rfl | rfl
  · rw [one_mul, one_mul, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    nlinarith only [heT, he1, he2, he3, he2']
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    nlinarith only [heT, he1, he2, he3, he2']

/-- The product of the half-exponential moments of the compressed bump. -/
theorem moment_product_compressedBump_ge (k : ℕ) :
    (Real.exp (-(1 / 20)) * (((k : ℝ) + 1)⁻¹ * ∫ v, pairBump v)) ^ 2 ≤
      (∫ u, compressedBump ((k : ℝ) + 1) u * Real.exp ((1 / 2) * u)) *
        ∫ u, compressedBump ((k : ℝ) + 1) u * Real.exp ((-(1 / 2)) * u) := by
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have h1 := moment_compressedBump_ge hk (s := 1 / 2) (by norm_num [abs_of_pos])
  have h2 := moment_compressedBump_ge hk (s := -(1 / 2)) (by norm_num [abs_of_pos])
  have hpos : 0 ≤ Real.exp (-(1 / 20)) * (((k : ℝ) + 1)⁻¹ * ∫ v, pairBump v) := by
    have := integral_pairBump_pos; positivity
  rw [sq]
  exact mul_le_mul h1 h2 hpos (hpos.trans h1)

/-- **Pole of the compressed carrier**, at least `2κ(e^{X/2} - 1)/(k+1)²` in size. -/
theorem abs_pole_compressedCarrier_ge (k : ℕ) {σ X T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hX : 1 ≤ X)
    (hXT : X ≤ T) :
    2 * carrierPoleConstant * (Real.exp (X / 2) - 1) * (((k : ℝ) + 1)⁻¹) ^ 2 ≤
      |(weilPoleTerm (EF.weilTest (compressedCarrier k σ T).1 (compressedCarrier k σ T).1)).re| := by
  unfold compressedCarrier
  rw [pole_realTest_subtractCopy (contDiff_compressedBump _)
    (hasCompactSupport_compressedBump (one_add_nat_pos k))]
  have hfac := separation_factor_ge hσ hX hXT
  have hmom := moment_product_compressedBump_ge k
  have hmp : 0 ≤ (∫ u, compressedBump ((k : ℝ) + 1) u * Real.exp ((1 / 2) * u)) *
      ∫ u, compressedBump ((k : ℝ) + 1) u * Real.exp ((-(1 / 2)) * u) := le_trans (sq_nonneg _) hmom
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hmp]
  have he1 : 0 ≤ Real.exp (X / 2) - 1 := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ X / 2 by linarith); linarith
  have hκ : carrierPoleConstant * (((k : ℝ) + 1)⁻¹) ^ 2 =
      (1 - Real.exp (-(1 / 2))) * (Real.exp (-(1 / 20)) * (((k : ℝ) + 1)⁻¹ * ∫ v, pairBump v)) ^ 2 := by
    unfold carrierPoleConstant; ring
  have hpos1 : 0 ≤ 1 - Real.exp (-(1 / 2)) := by
    have := Real.exp_lt_one_iff.mpr (show -(1 / 2 : ℝ) < 0 by norm_num); linarith
  calc
    2 * carrierPoleConstant * (Real.exp (X / 2) - 1) * (((k : ℝ) + 1)⁻¹) ^ 2 =
        2 * ((1 - Real.exp (-(1 / 2))) * (Real.exp (X / 2) - 1)) *
          (Real.exp (-(1 / 20)) * (((k : ℝ) + 1)⁻¹ * ∫ v, pairBump v)) ^ 2 := by
      rw [show 2 * carrierPoleConstant * (Real.exp (X / 2) - 1) * (((k : ℝ) + 1)⁻¹) ^ 2 =
        2 * (Real.exp (X / 2) - 1) * (carrierPoleConstant * (((k : ℝ) + 1)⁻¹) ^ 2) by ring, hκ]
      ring
    _ ≤ _ := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hfac (by norm_num)) hmom (sq_nonneg _)
      positivity

theorem pole_compressedCarrier_pos (k : ℕ) (T : ℝ) :
    0 < (weilPoleTerm (EF.weilTest (compressedCarrier k (-1) T).1
      (compressedCarrier k (-1) T).1)).re := by
  unfold compressedCarrier
  rw [pole_realTest_subtractCopy (contDiff_compressedBump _)
    (hasCompactSupport_compressedBump (one_add_nat_pos k))]
  have hm : 0 < (Real.exp (-(1 / 20)) * (((k : ℝ) + 1)⁻¹ * ∫ v, pairBump v)) ^ 2 := by
    have := integral_pairBump_pos; positivity
  have hmom := lt_of_lt_of_le hm (moment_product_compressedBump_ge k)
  have h1 : 0 < 1 - (-1) * Real.exp ((1 / 2) * T) := by linarith [Real.exp_pos ((1 / 2) * T)]
  have h2 : 0 < 1 - (-1) * Real.exp ((-(1 / 2)) * T) := by
    linarith [Real.exp_pos ((-(1 / 2)) * T)]
  positivity

theorem pole_compressedCarrier_neg (k : ℕ) {T : ℝ} (hT : 0 < T) :
    (weilPoleTerm (EF.weilTest (compressedCarrier k 1 T).1 (compressedCarrier k 1 T).1)).re < 0 := by
  unfold compressedCarrier
  rw [pole_realTest_subtractCopy (contDiff_compressedBump _)
    (hasCompactSupport_compressedBump (one_add_nat_pos k))]
  have hm : 0 < (Real.exp (-(1 / 20)) * (((k : ℝ) + 1)⁻¹ * ∫ v, pairBump v)) ^ 2 := by
    have := integral_pairBump_pos; positivity
  have hmom := lt_of_lt_of_le hm (moment_product_compressedBump_ge k)
  have h1 : 1 - 1 * Real.exp ((1 / 2) * T) < 0 := by
    have : 1 < Real.exp ((1 / 2) * T) := Real.one_lt_exp_iff.mpr (by linarith)
    linarith
  have h2 : 0 < 1 - 1 * Real.exp ((-(1 / 2)) * T) := by
    have : Real.exp ((-(1 / 2)) * T) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have := mul_neg_of_neg_of_pos h1 h2
  nlinarith only [this, hmom]

/-- **Archimedean part of the compressed carrier** is `O((1 + log(k+1))/(k+1))`. -/
theorem abs_archOnly_compressedCarrier_le (k : ℕ) {σ T : ℝ} (hσ : σ ^ 2 = 1) (hT : 2 ≤ T) :
    |WeilOneSided.weilArchRe (EF.weilTest (compressedCarrier k σ T).1 (compressedCarrier k σ T).1) -
        (weilPoleTerm (EF.weilTest (compressedCarrier k σ T).1 (compressedCarrier k σ T).1)).re| ≤
      ((k : ℝ) + 1)⁻¹ * (compressedArchConstant * (1 + Real.log ((k : ℝ) + 1))) := by
  set L : ℝ := (k : ℝ) + 1 with hL
  have hL1 : 1 ≤ L := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hL0 : 0 < L := by linarith
  have hsupp : ∀ x, 1 / (5 * L) < |x| → autocorr (compressedBump L) x = 0 :=
    fun x hx => autocorr_compressedBump_eq_zero hL0 hx
  have hT1 : 1 / (5 * L) + 1 ≤ T := by
    have : 1 / (5 * L) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have h := abs_archOnly_realTest_subtractCopy_le (contDiff_compressedBump L)
    (hasCompactSupport_compressedBump hL0) (by positivity) hsupp hσ hT1
  refine h.trans ?_
  rw [autocorr_compressedBump_zero hL0, integral_abs_autocorr_compressedBump hL0]
  have hm : autocorr (compressedBump L) 0 = L⁻¹ * autocorr pairBump 0 :=
    autocorr_compressedBump_zero hL0
  have h00 := autocorr_pairBump_zero_pos
  have hmpos : 0 < autocorr (compressedBump L) 0 := by rw [hm]; positivity
  have hn := normalizedArchEnergy_compressedBump_le hL1
  unfold normalizedArchEnergy at hn
  rw [div_le_iff₀ hmpos, hm] at hn
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hLinv0 : 0 < L⁻¹ := inv_pos.mpr hL0
  have hLinv : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hint : 0 ≤ ∫ x, |autocorr pairBump x| := integral_nonneg fun _ => abs_nonneg _
  have hd : 0 < 2 / (1 - Real.exp (-2)) := by
    have := Real.exp_lt_one_iff.mpr (show (-2 : ℝ) < 0 by norm_num)
    exact div_pos two_pos (by linarith)
  set a : ℝ := autocorr pairBump 0
  set E : ℝ := compressedEnergyConstant
  set I : ℝ := ∫ x, |autocorr pairBump x|
  set c : ℝ := 2 / (1 - Real.exp (-2))
  have hJ : biScaleLevyEnergy (compressedBump L) ≤ L⁻¹ * a * (|E| + 1) * (1 + Real.log L) := by
    have hla : 0 ≤ L⁻¹ * a := by positivity
    have h1 : 0 ≤ L⁻¹ * a * (|E| - E) := mul_nonneg hla (by linarith [le_abs_self E])
    have h2 : 0 ≤ L⁻¹ * a * (|E| * Real.log L) := mul_nonneg hla (mul_nonneg (abs_nonneg E) hlogL)
    have e : L⁻¹ * a * (|E| + 1) * (1 + Real.log L) - (E + Real.log L) * (L⁻¹ * a) =
        L⁻¹ * a * (|E| - E) + L⁻¹ * a * (|E| * Real.log L) + L⁻¹ * a := by ring
    linarith
  have hgoal : compressedArchConstant = 2 * |EF.gammaBracket 0| * a + 2 * a * (|E| + 1) + c * I := rfl
  rw [hgoal]
  have hcI : c * (L⁻¹ * L⁻¹ * I) ≤ L⁻¹ * (c * I) * (1 + Real.log L) := by
    have h1 : 0 ≤ c * I := mul_nonneg hd.le hint
    have h3 : 0 ≤ L⁻¹ * (c * I) := mul_nonneg hLinv0.le h1
    calc
      c * (L⁻¹ * L⁻¹ * I) = L⁻¹ * (c * I) * L⁻¹ := by ring
      _ ≤ L⁻¹ * (c * I) * 1 := mul_le_mul_of_nonneg_left hLinv h3
      _ ≤ L⁻¹ * (c * I) * (1 + Real.log L) := mul_le_mul_of_nonneg_left (by linarith) h3
  have hga : 2 * |EF.gammaBracket 0| * (L⁻¹ * a) ≤
      L⁻¹ * (2 * |EF.gammaBracket 0| * a) * (1 + Real.log L) := by
    have h1 : 0 ≤ L⁻¹ * (2 * |EF.gammaBracket 0| * a) := by positivity
    nlinarith only [h1, hlogL]
  nlinarith only [hcI, hga, hJ]

/-- The compressed carrier is blind at every node outside its correlation radius. -/
theorem logValue_compressedCarrier_eq_zero (k : ℕ) (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) {n : ℕ}
    (hn : 2 ≤ n) (hgap : 1 / (5 * ((k : ℝ) + 1)) < |Real.log n - T|) :
    logValue (compressedCarrier k σ T).1 n = 0 := by
  have hL0 := one_add_nat_pos k
  have hD : 1 / (5 * ((k : ℝ) + 1)) < Real.log 2 := by
    have h1 : 1 / (5 * ((k : ℝ) + 1)) ≤ 1 / 5 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have := Nat.cast_nonneg (α := ℝ) k; linarith
    have := Real.log_two_gt_d9; linarith
  exact logValue_realTest_subtractCopy_eq_zero (contDiff_compressedBump _)
    (hasCompactSupport_compressedBump hL0) (fun x hx => autocorr_compressedBump_eq_zero hL0 hx)
    hD σ hT hn hgap

/-! ### 5. Sub-square-root window density -/

/-- Along arbitrarily far windows `X ≤ log n ≤ X + 1` the nodes of `𝒩` are covered by a finite set
of size `K` with `M (K + 1)(1 + log(K + 1)) ≤ e^{X/2}`, for every prescribed `M`. -/
def SubSqrtWindowDensity (𝒩 : Set ℕ) : Prop :=
  ∀ M : ℝ, ∃ X : ℝ, M ≤ X ∧ ∃ F : Finset ℕ,
    (∀ n ∈ 𝒩, 2 ≤ n → X ≤ Real.log n → Real.log n ≤ X + 1 → n ∈ F) ∧
      M * ((F.card : ℝ) + 1) * (1 + Real.log ((F.card : ℝ) + 1)) ≤ Real.exp (X / 2)

/-- A point far from a covered window is far from every location in or out of the window. -/
theorem le_abs_sub_of_far_point {G : Finset ℝ} {X T w y : ℝ} (hw : 0 ≤ w) (hlo : X + w ≤ T)
    (hhi : T ≤ X + 1 - w) (hfar : ∀ a ∈ G, w ≤ |a - T|) (hy : X ≤ y → y ≤ X + 1 → y ∈ G) :
    w ≤ |y - T| := by
  rcases lt_or_ge y X with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rcases le_or_gt y (X + 1) with h' | h'
    · exact hfar y (hy h h')
    · rw [abs_of_pos (by linarith)]; linarith

/-- The final cost estimate: a pole of size `≥ 2κ(e^{X/2}-1)/L²` and an archimedean part
`≤ Cb(1 + log L)/L` give transport cost at most `ε` once
`(4|p|Cb/(εκ) + 4) L(1 + log L) ≤ e^{X/2}`. -/
theorem transport_cost_le {p ε κ Cb X L P A : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (hL : 1 ≤ L) (hX : 2 ≤ X)
    (hden : (4 * |p| * Cb / (ε * κ) + 4) * L * (1 + Real.log L) ≤ Real.exp (X / 2))
    (hP : 2 * κ * (Real.exp (X / 2) - 1) * (L⁻¹) ^ 2 ≤ |P|) (hP0 : P ≠ 0)
    (hA : |A| ≤ L⁻¹ * (Cb * (1 + Real.log L))) :
    |p| / |P| * |A| ≤ ε := by
  have hPpos : 0 < |P| := abs_pos.mpr hP0
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ 1 + Real.log L := by have := Real.log_nonneg hL; linarith
  have he : Real.exp (X / 2) / 2 ≤ Real.exp (X / 2) - 1 := by
    have := Real.add_one_le_exp (X / 2); linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hPpos]
  have hden' : (4 * |p| * Cb / (ε * κ)) * (L * (1 + Real.log L)) ≤ Real.exp (X / 2) := by
    have : 0 ≤ 4 * (L * (1 + Real.log L)) := by positivity
    nlinarith only [hden, this]
  have hεκ : 0 < ε * κ := mul_pos hε hκ
  have hkey : |p| * Cb * (L * (1 + Real.log L)) ≤ ε * κ * Real.exp (X / 2) / 4 := by
    have e : (4 * |p| * Cb / (ε * κ)) * (L * (1 + Real.log L)) =
        4 * (|p| * Cb * (L * (1 + Real.log L))) / (ε * κ) := by ring
    rw [e, div_le_iff₀ hεκ] at hden'
    linarith
  have hA' : |p| * |A| ≤ |p| * (L⁻¹ * (Cb * (1 + Real.log L))) :=
    mul_le_mul_of_nonneg_left hA (abs_nonneg p)
  have hP' : ε * (κ * Real.exp (X / 2) * (L⁻¹) ^ 2) ≤ ε * |P| := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    have : κ * Real.exp (X / 2) * (L⁻¹) ^ 2 ≤ 2 * κ * (Real.exp (X / 2) - 1) * (L⁻¹) ^ 2 := by
      have h0 : 0 ≤ κ * (L⁻¹) ^ 2 := by positivity
      nlinarith only [he, h0]
    linarith
  have hmid : |p| * (L⁻¹ * (Cb * (1 + Real.log L))) ≤ ε * (κ * Real.exp (X / 2) * (L⁻¹) ^ 2) := by
    have e1 : |p| * (L⁻¹ * (Cb * (1 + Real.log L))) = (L⁻¹) ^ 2 * (|p| * Cb * (L * (1 + Real.log L))) := by
      field_simp
    have e2 : ε * (κ * Real.exp (X / 2) * (L⁻¹) ^ 2) = (L⁻¹) ^ 2 * (ε * κ * Real.exp (X / 2)) := by ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 0 ≤ ε * κ * Real.exp (X / 2) := by positivity
    linarith
  linarith

/-- **Pole mass is free under sub-square-root density.** -/
theorem exists_blindOn_poleMass_eq_abs_archOnly_le_of_density {𝒩 : Set ℕ}
    (h𝒩 : SubSqrtWindowDensity 𝒩) (p : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn 𝒩 c ∧ nodePoleMass c = p ∧
      |nodeArchOnly c| ≤ ε := by
  classical
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, fun _ => le_rfl, fun j _ => by simp [nodeVector_eq], by simp [nodePoleMass],
      by simp [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, hε.le]⟩
  have hκ := carrierPoleConstant_pos
  have hCb := compressedArchConstant_nonneg
  obtain ⟨X, hMX, F, hcov, hden⟩ :=
    h𝒩 (4 * |p| * compressedArchConstant / (ε * carrierPoleConstant) + 4)
  have hX4 : 4 ≤ X := by
    have : 0 ≤ 4 * |p| * compressedArchConstant / (ε * carrierPoleConstant) := by positivity
    linarith
  obtain ⟨T, hTlo, hThi, hfar⟩ := exists_far_point (F.image fun n : ℕ => Real.log n) X
  set k : ℕ := (F.image fun n : ℕ => Real.log n).card with hk
  have hkF : (k : ℝ) ≤ F.card := by exact_mod_cast Finset.card_image_le
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hw : 0 ≤ 1 / (2 * ((k : ℝ) + 1)) := by positivity
  have hw1 : 1 / (2 * ((k : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hXT : X ≤ T := by linarith
  have hT2 : 2 ≤ T := by linarith
  set σ : ℝ := if 0 < p then -1 else 1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by rw [hσdef]; split_ifs <;> simp
  have hσsq : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  set g : WeilTestFn := compressedCarrier k σ T with hg
  set P : ℝ := (weilPoleTerm (EF.weilTest g.1 g.1)).re with hPdef
  have hPabs : 2 * carrierPoleConstant * (Real.exp (X / 2) - 1) * (((k : ℝ) + 1)⁻¹) ^ 2 ≤ |P| :=
    abs_pole_compressedCarrier_ge k hσ (by linarith) hXT
  have hA := abs_archOnly_compressedCarrier_le k hσsq hT2
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hPabs
    have : 1 < Real.exp (X / 2) := Real.one_lt_exp_iff.mpr (by linarith)
    have hpos : 0 < Real.exp (X / 2) - 1 := by linarith
    have : 0 < 2 * carrierPoleConstant * (Real.exp (X / 2) - 1) * (((k : ℝ) + 1)⁻¹) ^ 2 :=
      mul_pos (mul_pos (mul_pos two_pos carrierPoleConstant_pos) hpos)
        (pow_pos (inv_pos.mpr (one_add_nat_pos k)) 2)
    linarith
  have hsign : 0 < p / P := by
    rcases lt_or_gt_of_ne hp with hneg | hpos
    · have hσ1 : σ = 1 := by rw [hσdef, if_neg (not_lt.mpr hneg.le)]
      have hPneg : P < 0 := by rw [hPdef, hg, hσ1]; exact pole_compressedCarrier_neg k (by linarith)
      exact div_pos_of_neg_of_neg hneg hPneg
    · have hσ1 : σ = -1 := by rw [hσdef, if_pos hpos]
      have hPpos : 0 < P := by rw [hPdef, hg, hσ1]; exact pole_compressedCarrier_pos k T
      exact div_pos hpos hPpos
  refine ⟨Finsupp.single g (p / P), fun h => ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> [exact hsign.le; exact le_rfl]
  · rw [nodeVector_single_apply]
    have hfar' := le_abs_sub_of_far_point (y := Real.log (j : ℕ)) hw hTlo hThi hfar
      (fun hlo hhi => Finset.mem_image.mpr ⟨j, hcov j hj j.2 hlo hhi, rfl⟩)
    have hlt : 1 / (5 * ((k : ℝ) + 1)) < 1 / (2 * ((k : ℝ) + 1)) := by
      have h0 := one_add_nat_pos k
      exact one_div_lt_one_div_of_lt (mul_pos two_pos h0) (by linarith only [h0])
    have hz : logValue g.1 (j : ℕ) = 0 :=
      logValue_compressedCarrier_eq_zero k σ (le_trans (by norm_num) hT2) j.2
        (lt_of_lt_of_le hlt hfar')
    rw [hz, mul_zero]
  · rw [nodePoleMass_single, ← hPdef, div_mul_cancel₀ _ hP0]
  · rw [nodeArchOnly_single, abs_mul, abs_of_pos hsign, ← hPdef]
    have hL1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hden' : (4 * |p| * compressedArchConstant / (ε * carrierPoleConstant) + 4) *
        ((k : ℝ) + 1) * (1 + Real.log ((k : ℝ) + 1)) ≤ Real.exp (X / 2) := by
      have hmono : ((k : ℝ) + 1) * (1 + Real.log ((k : ℝ) + 1)) ≤
          ((F.card : ℝ) + 1) * (1 + Real.log ((F.card : ℝ) + 1)) := by
        have hle : (k : ℝ) + 1 ≤ (F.card : ℝ) + 1 := by linarith
        have hlog := Real.log_le_log (by linarith) hle
        have h0 : 0 ≤ 1 + Real.log ((k : ℝ) + 1) := by
          have := Real.log_nonneg hL1; linarith
        nlinarith only [hle, hlog, h0, hL1]
      have hM0 : 0 ≤ 4 * |p| * compressedArchConstant / (ε * carrierPoleConstant) + 4 := by
        positivity
      have := mul_le_mul_of_nonneg_left hmono hM0
      calc
        _ = (4 * |p| * compressedArchConstant / (ε * carrierPoleConstant) + 4) *
            (((k : ℝ) + 1) * (1 + Real.log ((k : ℝ) + 1))) := by ring
        _ ≤ _ := this.trans (by rw [← mul_assoc]; exact hden)
    have := transport_cost_le hε hκ hL1 (by linarith) hden' hPabs hP0 hA
    rw [← abs_div, abs_of_pos hsign] at this
    exact this

/-- **Pole invisibility under sub-square-root density.** -/
theorem exists_blindOn_poleMass_zero_archOnly_close_of_density {𝒩 : Set ℕ}
    (h𝒩 : SubSqrtWindowDensity 𝒩) {c₁ : WeilTestFn →₀ ℝ} (hc₁ : ∀ f, 0 ≤ c₁ f)
    (hb₁ : BlindOn 𝒩 c₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn 𝒩 c ∧ nodePoleMass c = 0 ∧
      |nodeArchOnly c - nodeArchOnly c₁| ≤ ε := by
  obtain ⟨d, hd, hbd, hpd, had⟩ :=
    exists_blindOn_poleMass_eq_abs_archOnly_le_of_density h𝒩 (-nodePoleMass c₁) hε
  refine ⟨c₁ + d, fun f => ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [Finsupp.add_apply]; exact add_nonneg (hc₁ f) (hd f)
  · rw [nodeVector_add, Finsupp.add_apply, hb₁ j hj, hbd j hj, add_zero]
  · rw [nodePoleMass_add, hpd, add_neg_cancel]
  · rw [nodeArchOnly_add, add_sub_cancel_left]; exact had

/-- **Zero-pole positivity fails under sub-square-root density.** -/
theorem not_zeroPoleBlindPositiveOn_of_density {𝒩 : Set ℕ} (h𝒩 : SubSqrtWindowDensity 𝒩) :
    ¬ ZeroPoleBlindPositiveOn 𝒩 := by
  intro hpos
  obtain ⟨c₁, hc₁, hv₁, hneg⟩ := exists_blind_nodeArchOnly_neg
  have hb₁ : BlindOn 𝒩 c₁ := fun j _ => by rw [hv₁]; rfl
  obtain ⟨c, hc, hb, hp, hclose⟩ := exists_blindOn_poleMass_zero_archOnly_close_of_density h𝒩
    hc₁ hb₁ (ε := -nodeArchOnly c₁ / 2) (by linarith)
  have hE := hpos c hc hb hp
  rw [show nodeArchEnergy c = nodeArchOnly c by rw [nodeArchOnly, hp, sub_zero]] at hE
  have := (abs_le.mp hclose).2
  linarith

/-! ### 6. Smooth integers -/

/-- The `S`-smooth integers with `log n ≤ X + 1` number at most `(⌊(X+1)/log 2⌋ + 1)^{|S|}`. -/
theorem card_smooth_window_le (S : Finset ℕ) (X : ℝ) :
    (((Finset.Icc 1 ⌊Real.exp (X + 1)⌋₊).filter fun n => n.primeFactors ⊆ S).card : ℝ) ≤
      ((⌊(X + 1) / Real.log 2⌋₊ : ℝ) + 1) ^ S.card := by
  classical
  set B : ℕ := ⌊(X + 1) / Real.log 2⌋₊ with hB
  set F := (Finset.Icc 1 ⌊Real.exp (X + 1)⌋₊).filter fun n => n.primeFactors ⊆ S with hF
  set t : Finset (S → ℕ) := Fintype.piFinset fun _ : S => Finset.range (B + 1) with ht
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmaps : Set.MapsTo (fun n : ℕ => fun p : S => n.factorization p) F t := by
    intro n hn
    rw [Finset.mem_coe, hF, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_coe, ht, Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range, Nat.lt_succ_iff]
    show n.factorization (p : ℕ) ≤ B
    have hn0 : n ≠ 0 := by omega
    rcases Nat.eq_zero_or_pos (n.factorization p) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors
        (Nat.support_factorization n ▸ Finsupp.mem_support_iff.mpr hpos.ne')
      apply Nat.le_floor
      rw [le_div_iff₀ hlog2]
      have hpow : (2 : ℝ) ^ n.factorization p ≤ n := by
        have h1 : 2 ^ n.factorization p ≤ (p : ℕ) ^ n.factorization p :=
          Nat.pow_le_pow_left hpp.two_le _
        have h2 := Nat.ordProj_le (p : ℕ) hn0
        exact_mod_cast h1.trans h2
      have hnle : (n : ℝ) ≤ Real.exp (X + 1) := by
        have := hn.1.2
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le (Real.exp_pos _).le)
      have hl := Real.log_le_log (by positivity) (hpow.trans hnle)
      rw [Real.log_pow, Real.log_exp] at hl
      exact_mod_cast hl
  have hinj : Set.InjOn (fun n : ℕ => fun p : S => n.factorization p) F := by
    intro a ha b hb hab
    rw [Finset.mem_coe, hF, Finset.mem_filter, Finset.mem_Icc] at ha hb
    apply Nat.eq_of_factorization_eq (by omega) (by omega)
    intro q
    by_cases hq : q ∈ S
    · exact congrFun hab ⟨q, hq⟩
    · have ha' : q ∉ a.primeFactors := fun h => hq (ha.2 h)
      have hb' : q ∉ b.primeFactors := fun h => hq (hb.2 h)
      rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at ha' hb'
      rw [ha', hb']
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [ht, Fintype.card_piFinset] at hcard
  simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_coe] at hcard
  exact_mod_cast hcard

/-- Polynomials are eventually below `e^{X/2}`. -/
private theorem exists_ge_pow_le_exp_half (C : ℝ) (k : ℕ) (M : ℝ) :
    ∃ X : ℝ, M ≤ X ∧ 1 ≤ X ∧ C * (X + 1) ^ k ≤ Real.exp (X / 2) := by
  set X : ℝ := max (max M 1) (2 ^ (2 * k + 1) * (|C| + 1) * (Nat.factorial (k + 1)))
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) (le_max_left _ _)
  have hXM : M ≤ X := le_trans (le_max_left _ _) (le_max_left _ _)
  have hXbig : 2 ^ (2 * k + 1) * (|C| + 1) * (Nat.factorial (k + 1)) ≤ X := le_max_right _ _
  refine ⟨X, hXM, hX1, ?_⟩
  have hX0 : 0 ≤ X / 2 := by linarith
  have hexp := Real.pow_div_factorial_le_exp (X / 2) hX0 (k + 1)
  have hfac : (0 : ℝ) < Nat.factorial (k + 1) := by exact_mod_cast Nat.factorial_pos _
  have h1 : C * (X + 1) ^ k ≤ (|C| + 1) * (2 * X) ^ k := by
    have : (X + 1) ^ k ≤ (2 * X) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ X + 1 by linarith) k, abs_nonneg C]
  have h2 : (|C| + 1) * (2 * X) ^ k ≤ (X / 2) ^ (k + 1) / (Nat.factorial (k + 1)) := by
    rw [le_div_iff₀ hfac]
    have e1 : (2 * X) ^ k = 2 ^ k * X ^ k := mul_pow 2 X k
    have e2 : (X / 2) ^ (k + 1) = X * X ^ k / 2 ^ (k + 1) := by
      rw [div_pow, pow_succ]; ring
    rw [e1, e2, le_div_iff₀ (by positivity)]
    have hXk : 0 ≤ X ^ k := pow_nonneg (by linarith) k
    have e3 : (2 : ℝ) ^ (2 * k + 1) = 2 ^ k * 2 ^ (k + 1) := by
      rw [← pow_add]; ring_nf
    have : (|C| + 1) * (2 ^ k * X ^ k) * (Nat.factorial (k + 1) : ℝ) * 2 ^ (k + 1) =
        (2 ^ (2 * k + 1) * (|C| + 1) * (Nat.factorial (k + 1))) * X ^ k := by
      rw [e3]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hXbig hXk
  linarith

/-- **Smooth integers have sub-square-root window density.** -/
theorem subSqrtWindowDensity_smooth (S : Finset ℕ) :
    SubSqrtWindowDensity {n | n.primeFactors ⊆ S} := by
  classical
  intro M
  set s : ℕ := S.card
  obtain ⟨X, hMX, hX1, hpoly⟩ := exists_ge_pow_le_exp_half (4 * (|M| + 1) * 3 ^ (2 * s)) (2 * s) M
  refine ⟨X, hMX, (Finset.Icc 1 ⌊Real.exp (X + 1)⌋₊).filter fun n => n.primeFactors ⊆ S, ?_, ?_⟩
  · intro n hn hn2 _ hhi
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, hn⟩
    apply Nat.le_floor
    have := Real.exp_log (show (0 : ℝ) < n by positivity)
    rw [← this]
    exact Real.exp_le_exp.mpr hhi
  · set K : ℝ := (((Finset.Icc 1 ⌊Real.exp (X + 1)⌋₊).filter fun n => n.primeFactors ⊆ S).card : ℝ)
    have hK := card_smooth_window_le S X
    have hB : ((⌊(X + 1) / Real.log 2⌋₊ : ℝ) + 1) ≤ 3 * (X + 1) := by
      have h1 : (⌊(X + 1) / Real.log 2⌋₊ : ℝ) ≤ (X + 1) / Real.log 2 :=
        Nat.floor_le (div_nonneg (by linarith) (Real.log_pos one_lt_two).le)
      have h2 : (X + 1) / Real.log 2 ≤ 2 * (X + 1) := by
        rw [div_le_iff₀ (Real.log_pos one_lt_two)]
        have := Real.log_two_gt_d9; nlinarith
      linarith
    have hK3 : K ≤ (3 * (X + 1)) ^ s :=
      hK.trans (pow_le_pow_left₀ (by positivity) hB s)
    have hK0 : 0 ≤ K := by positivity
    set z : ℝ := 2 * (3 * (X + 1)) ^ s with hz
    have hz1 : 1 ≤ (3 * (X + 1)) ^ s := one_le_pow₀ (by linarith)
    have hKz : K + 1 ≤ z := by linarith
    have hlog : 1 + Real.log (K + 1) ≤ K + 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < K + 1 by linarith); linarith
    have hl0 : 0 ≤ 1 + Real.log (K + 1) := by
      have := Real.log_nonneg (show 1 ≤ K + 1 by linarith); linarith
    have hprod : (K + 1) * (1 + Real.log (K + 1)) ≤ z * z :=
      mul_le_mul hKz (hlog.trans hKz) hl0 (by linarith)
    have hzz : z * z = 4 * 3 ^ (2 * s) * (X + 1) ^ (2 * s) := by
      rw [hz, show 2 * (3 * (X + 1)) ^ s * (2 * (3 * (X + 1)) ^ s) =
        4 * ((3 * (X + 1)) ^ s * (3 * (X + 1)) ^ s) by ring, ← pow_add, ← two_mul, mul_pow]
      ring
    have hM : M * ((K + 1) * (1 + Real.log (K + 1))) ≤ (|M| + 1) * (z * z) := by
      have h0 : 0 ≤ (K + 1) * (1 + Real.log (K + 1)) := mul_nonneg (by linarith) hl0
      have h1 : M * ((K + 1) * (1 + Real.log (K + 1))) ≤ (|M| + 1) * ((K + 1) * (1 + Real.log (K + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) h0
      exact h1.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
    calc
      M * (K + 1) * (1 + Real.log (K + 1)) = M * ((K + 1) * (1 + Real.log (K + 1))) := by ring
      _ ≤ (|M| + 1) * (z * z) := hM
      _ = 4 * (|M| + 1) * 3 ^ (2 * s) * (X + 1) ^ (2 * s) := by rw [hzz]; ring
      _ ≤ _ := hpoly

/-- **No finite set of primes suffices.** For every finite set `S`, zero-pole positivity on
combinations blind only at the `S`-smooth integers is false; with all integers it is RH. -/
theorem not_zeroPoleBlindPositiveOn_smooth (S : Finset ℕ) :
    ¬ ZeroPoleBlindPositiveOn {n | n.primeFactors ⊆ S} :=
  not_zeroPoleBlindPositiveOn_of_density (subSqrtWindowDensity_smooth S)

end

end GaloisForLFunctions.BiScaleUncertainty
