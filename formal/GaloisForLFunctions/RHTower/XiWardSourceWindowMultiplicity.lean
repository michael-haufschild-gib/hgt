import GaloisForLFunctions.RHTower.XiWardInteriorReflectionAbsorption
import GaloisForLFunctions.RHTower.FiniteOfflineCauchyEnergy
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Source-only Ward multiplicity bound in a height window

Every strict-right upper Xi zero copy whose height lies in a fixed window contributes a uniform
positive amount to the Ward response at one interior probe.  The amount remains positive as the
horizontal displacement tends to zero, while critical-line copies do not occur in the
strict-right index type.  Positivity of all other Schwarz-pair terms promotes the atomic estimate
to any finite multiplicity-exact packet.

Functional-equation absorption then bounds that packet by an explicit source quantity containing
only pole, Gamma, and absolutely convergent von Mangoldt terms at real part greater than one.  This
is an unconditional, source-faithful submicroscopic separator.  It does not supply the centered
quadratic estimate needed for a positive-proportion theorem.
-/

open Complex
open Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open MeasureTheory

/-! ## Raw quadratic scaling law -/

/-- Cauchy--Schwarz exposes window length as the natural conversion factor
between raw Ward mass and raw Ward quadratic energy. -/
theorem sq_setIntegral_le_length_mul_setIntegral_sq
    {U : Set ℝ} {f : ℝ → ℝ} {V : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict U))
    (hf2 : Integrable (fun t => f t ^ 2) (volume.restrict U))
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict U))
    (hV : (∫ _ : ℝ in U, (1 : ℝ)) = V) :
    (∫ t in U, f t) ^ 2 ≤ V * ∫ t in U, f t ^ 2 := by
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    (μ := volume.restrict U) (f := f) (g := fun _ => (1 : ℝ))
    hfm aestronglyMeasurable_const hf2 (by simpa using hone)
  simp only [mul_one, one_pow] at hcs
  rw [hV] at hcs
  simpa [mul_comm] using hcs

/-- Abstract mass-to-energy conversion. If a nonnegative mass `M` contains a
quantum `q` for each of `R` objects, its square forces the corresponding raw
quadratic energy. -/
theorem ward_raw_quadratic_count_sq_le
    {q R M V E : ℝ}
    (hq : 0 ≤ q) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hmass : q * R ≤ M) (hholder : M ^ 2 ≤ V * E) :
    q ^ 2 * R ^ 2 ≤ V * E := by
  have hqR : 0 ≤ q * R := mul_nonneg hq hR
  have hsq : (q * R) ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ hqR hM).2 hmass
  nlinarith

/-- **Correct raw Ward scale at the three-quarters threshold.** If the
strict-right count is at least `N/8` and each copy contributes `4π` of mass,
then window length times raw quadratic energy is at least `π² N²/4`.
Therefore a raw `O(N)` energy bound on an `O(T)` window would imply density
one, not merely the target three-quarters density. -/
theorem ward_raw_quadratic_energy_scale_at_eighth
    {R N M V E : ℝ}
    (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hcount : N / 8 ≤ R)
    (hmass : 4 * Real.pi * R ≤ M)
    (hholder : M ^ 2 ≤ V * E) :
    Real.pi ^ 2 * N ^ 2 / 4 ≤ V * E := by
  have hquantum : 0 ≤ 4 * Real.pi := by positivity
  have hlower : 4 * Real.pi * (N / 8) ≤ M :=
    (mul_le_mul_of_nonneg_left hcount hquantum).trans hmass
  have hleft : 0 ≤ 4 * Real.pi * (N / 8) := by positivity
  have hsq : (4 * Real.pi * (N / 8)) ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ hleft hM).2 hlower
  nlinarith

/-- At exact two-sided window length `2T`, the raw three-quarters threshold
is `π² N²/(8T)`, not a constant multiple of `N`. -/
theorem ward_raw_quadratic_energy_scale_at_eighth_twoTime
    {R N M T E : ℝ}
    (hN : 0 ≤ N) (hM : 0 ≤ M) (hT : 0 < T)
    (hcount : N / 8 ≤ R)
    (hmass : 4 * Real.pi * R ≤ M)
    (hholder : M ^ 2 ≤ (2 * T) * E) :
    Real.pi ^ 2 * N ^ 2 / (8 * T) ≤ E := by
  have hscale := ward_raw_quadratic_energy_scale_at_eighth
    hN hM hcount hmass hholder
  rw [div_le_iff₀ (by positivity : 0 < 8 * T)]
  nlinarith

/-- Integral form of the exact raw-energy threshold. -/
theorem ward_setIntegral_energy_scale_at_eighth
    {U : Set ℝ} {f : ℝ → ℝ} {R N V : ℝ}
    (hN : 0 ≤ N)
    (hfm : AEStronglyMeasurable f (volume.restrict U))
    (hf2 : Integrable (fun t => f t ^ 2) (volume.restrict U))
    (hone : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict U))
    (hV : (∫ _ : ℝ in U, (1 : ℝ)) = V)
    (hmass_nonneg : 0 ≤ ∫ t in U, f t)
    (hcount : N / 8 ≤ R)
    (hmass : 4 * Real.pi * R ≤ ∫ t in U, f t) :
    Real.pi ^ 2 * N ^ 2 / 4 ≤ V * ∫ t in U, f t ^ 2 := by
  apply ward_raw_quadratic_energy_scale_at_eighth
    hN hmass_nonneg hcount hmass
  exact sq_setIntegral_le_length_mul_setIntegral_sq hfm hf2 hone hV

/-- **Shallow/deep three-quarters receiver.**  Write the total divisor count as the critical-line
count plus twice the strict-right shallow and deep counts.  If positive shallow energy and the
deep census together cost at most `N / 8`, then at least three quarters of total multiplicity lies
on the critical line.  This isolates the exact numerical source target consumed by the
submicroscopic Cauchy law below. -/
theorem three_quarters_line_of_shallowEnergy_and_deepCount
    {N N₀ Rsh Rdeep h E : ℝ}
    (_hN : 0 ≤ N) (hsplit : N = N₀ + 2 * (Rsh + Rdeep))
    (hshallow : Rsh ≤ h * E)
    (hbudget : h * E + Rdeep ≤ N / 8) :
    3 * N / 4 ≤ N₀ := by
  nlinarith

/-- Every finite packet of strict-right upper zero copies is bounded by the full Ward response at
an interior probe. -/
theorem finite_sum_re_xiAntiCausalWardSchwarzPairResponse_le_continued
    (S : Finset XiRightUpperZeroCopy) {w : ℂ} (hw : 0 < w.re) :
    (∑ q ∈ S, (xiAntiCausalWardSchwarzPairResponse q w).re) ≤
      (continuedXiAntiCausalWardResponse w).re := by
  have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
  have hreal : Summable (fun q : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse q w).re) := by
    simpa only [Complex.reCLM_apply] using hsum.mapL Complex.reCLM
  have hfinite := hreal.sum_le_tsum S
    (fun q _ => (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le)
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
    Complex.re_tsum hsum]
  exact hfinite

/-- A critical-line divisor copy contributes the ordinary Poisson kernel to the complementary
trace.  Unlike the strict-right Schwarz-pair term, this is one copy rather than one reflected
pair, so its total multiplicity is retained exactly. -/
theorem re_two_I_relativeResolventTerm_critical_line_eq
    (q : XiZeroCopy) {h c : ℝ}
    (hcritical : (I * xiSpectralPoint q).re = 0) :
    (2 * I * xiRelativeResolventTerm
        (I * ((h : ℂ) + I * (c : ℂ))) q).re =
      2 * h / (h ^ 2 + (c + (xiSpectralPoint q).re) ^ 2) := by
  have hqim : (xiSpectralPoint q).im = 0 := by
    simpa [Complex.mul_re] using hcritical
  have hqeq : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hqim]
  have hz : I * ((h : ℂ) + I * (c : ℂ)) =
      (-c : ℂ) + I * (h : ℂ) := by
    rw [mul_add, ← mul_assoc I I, I_mul_I]
    ring
  rw [hqeq, hz, xiRelativeResolventTerm]
  simp [hqim, Complex.mul_re, Complex.mul_im, Complex.inv_re,
    Complex.inv_im, Complex.normSq_apply]
  ring_nf

/-- Optimal displacement-uniform lower quantum obtained from the two endpoint widths allowed by
the critical strip. -/
def xiWardSharpWindowQuantum (h δ : ℝ) : ℝ :=
  min (2 * h / (h ^ 2 + δ ^ 2))
    (2 * (h + 1 / 2) / ((h + 1 / 2) ^ 2 + δ ^ 2))

/-- The Lorentzian profile has no interior minimum as its positive width ranges from `h` to
`h + 1/2`; its minimum is attained at one of the two endpoint widths. -/
theorem xiWardSharpWindowQuantum_le_lorentzian
    {h x δ : ℝ} (hh : 0 < h) (hxlo : h ≤ x) (hxhi : x ≤ h + 1 / 2) :
    xiWardSharpWindowQuantum h δ ≤ 2 * x / (x ^ 2 + δ ^ 2) := by
  have hx : 0 < x := hh.trans_le hxlo
  have hH : 0 < h + 1 / 2 := by linarith
  have hDh : 0 < h ^ 2 + δ ^ 2 := by positivity
  have hDx : 0 < x ^ 2 + δ ^ 2 := by positivity
  have hDH : 0 < (h + 1 / 2) ^ 2 + δ ^ 2 := by positivity
  by_cases hcase : h * x ≤ δ ^ 2
  · refine (min_le_left _ _).trans ?_
    rw [div_le_div_iff₀ hDh hDx]
    have hprod : 0 ≤ (x - h) * (δ ^ 2 - h * x) :=
      mul_nonneg (sub_nonneg.mpr hxlo) (sub_nonneg.mpr hcase)
    nlinarith
  · refine (min_le_right _ _).trans ?_
    rw [div_le_div_iff₀ hDH hDx]
    have hcase' : δ ^ 2 < h * x := lt_of_not_ge hcase
    have hprod : 0 ≤ (h + 1 / 2 - x) * ((h + 1 / 2) * x - δ ^ 2) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr hxhi
      · nlinarith [mul_pos hx (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith

/-- Sharp per-pair interior window quantum. It remains strictly separated from zero as the
strict-right horizontal displacement tends to zero, while critical-line multiplicity is absent
from the index type. -/
theorem sharp_interior_pair_quantum {h c δ : ℝ} (hh : 0 < h)
    (q : XiRightUpperZeroCopy)
    (hwin : ((xiRightCenteredZero q.1).im - c) ^ 2 ≤ δ ^ 2) :
    xiWardSharpWindowQuantum h δ ≤
      (xiAntiCausalWardSchwarzPairResponse q
        (((h : ℝ) : ℂ) + I * ((c : ℝ) : ℂ))).re := by
  rw [re_xiAntiCausalWardSchwarzPairResponse_line_eq q h c]
  let x : ℝ := h + (xiRightCenteredZero q.1).re
  have hre := xiRightCenteredZero_re_pos q.1
  have hlt := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hx : 0 < x := by dsimp [x]; linarith
  have hxlo : h ≤ x := by dsimp [x]; linarith
  have hxhi : x ≤ h + 1 / 2 := by dsimp [x]; linarith
  have hDactual : 0 < x ^ 2 + (c - (xiRightCenteredZero q.1).im) ^ 2 := by
    positivity
  have hDdelta : 0 < x ^ 2 + δ ^ 2 := by positivity
  have hdenle :
      x ^ 2 + (c - (xiRightCenteredZero q.1).im) ^ 2 ≤ x ^ 2 + δ ^ 2 := by
    nlinarith [hwin]
  have hnum : 0 ≤ 2 * x := by positivity
  have hactual :
      2 * x / (x ^ 2 + δ ^ 2) ≤
        2 * x / (x ^ 2 + (c - (xiRightCenteredZero q.1).im) ^ 2) :=
    div_le_div_of_nonneg_left hnum hDactual hdenle
  have hendpoint :=
    xiWardSharpWindowQuantum_le_lorentzian (δ := δ) hh hxlo hxhi
  have hfirst : 0 ≤ 2 * (x /
      (x ^ 2 + (c + (xiRightCenteredZero q.1).im) ^ 2)) := by positivity
  dsimp [x] at hactual hfirst ⊢
  rw [show 2 * ((h + (xiRightCenteredZero q.1).re) /
      ((h + (xiRightCenteredZero q.1).re) ^ 2 +
        (c - (xiRightCenteredZero q.1).im) ^ 2)) =
      2 * (h + (xiRightCenteredZero q.1).re) /
        ((h + (xiRightCenteredZero q.1).re) ^ 2 +
          (c - (xiRightCenteredZero q.1).im) ^ 2) by ring]
  linarith

/-- A critical-line copy in the matching height window contributes the ordinary Poisson quantum
`2h/(h²+δ²)` to the complementary trace retained by reflection absorption. -/
theorem critical_line_relativeResolvent_window_quantum
    {h c δ : ℝ} (hh : 0 < h) (q : XiZeroCopy)
    (hcritical : (I * xiSpectralPoint q).re = 0)
    (hwin : (c + (xiSpectralPoint q).re) ^ 2 ≤ δ ^ 2) :
    2 * h / (h ^ 2 + δ ^ 2) ≤
      (2 * I * xiRelativeResolventTerm
        (I * ((h : ℂ) + I * (c : ℂ))) q).re := by
  rw [re_two_I_relativeResolventTerm_critical_line_eq q hcritical]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

/-- **Sharp multiplicity-exact Euler--Gamma window estimate.** Every finite strict-right packet
costs the optimal endpoint quantum, while the upper bound remains the source-only pole, Gamma,
and absolutely convergent von Mangoldt expression. -/
theorem finite_strictRight_window_card_mul_sharpQuantum_le_sourceArithmetic
    (S : Finset XiRightUpperZeroCopy) {h c δ : ℝ} (hh : 1 / 2 < h)
    (hwin : ∀ q ∈ S,
      ((xiRightCenteredZero q.1).im - c) ^ 2 ≤ δ ^ 2) :
    (S.card : ℝ) * xiWardSharpWindowQuantum h δ ≤
      xiWardInteriorSourceArithmeticBound
        ((h : ℂ) + Complex.I * (c : ℂ)) := by
  let w : ℂ := (h : ℂ) + Complex.I * (c : ℂ)
  let quantum : ℝ := xiWardSharpWindowQuantum h δ
  have hw : 0 < w.re := by
    simp [w, Complex.mul_re]
    linarith
  have hsource := re_continuedXiAntiCausalWardResponse_le_sourceArithmetic
    (w := w) (by simpa [w, Complex.mul_re] using hh)
  have hfinite :=
    finite_sum_re_xiAntiCausalWardSchwarzPairResponse_le_continued S hw
  have hquantum : (S.card : ℝ) * quantum ≤
      ∑ q ∈ S, (xiAntiCausalWardSchwarzPairResponse q w).re := by
    calc
      (S.card : ℝ) * quantum = ∑ q ∈ S, quantum := by simp
      _ ≤ ∑ q ∈ S, (xiAntiCausalWardSchwarzPairResponse q w).re := by
        apply Finset.sum_le_sum
        intro q hq
        exact sharp_interior_pair_quantum (by linarith : 0 < h) q (hwin q hq)
  change (S.card : ℝ) * quantum ≤ xiWardInteriorSourceArithmeticBound w
  exact hquantum.trans (hfinite.trans hsource)

/-- **Hybrid Euler--Gamma window estimate.**  Strict positive shifts cost the sharp
Schwarz-pair quantum, while critical-line multiplicity simultaneously costs its one-copy Poisson
quantum.  Both are bounded by the same explicit pole--Gamma--von-Mangoldt source head.

This is stronger than the strict-right-only estimate: reflection absorption previously discarded
the critical diagonal.  Retaining it makes the separation from off-line pairs exact and
multiplicity-faithful before taking any height asymptotic. -/
theorem finite_strictRight_and_critical_window_charge_le_sourceArithmetic
    (S : Finset XiRightUpperZeroCopy) (C : Finset XiZeroCopy)
    {h c δ : ℝ} (hh : 1 / 2 < h)
    (hwinRight : ∀ q ∈ S,
      ((xiRightCenteredZero q.1).im - c) ^ 2 ≤ δ ^ 2)
    (hcritical : ∀ q ∈ C, (I * xiSpectralPoint q).re = 0)
    (hwinCritical : ∀ q ∈ C,
      (c + (xiSpectralPoint q).re) ^ 2 ≤ δ ^ 2) :
    (S.card : ℝ) * xiWardSharpWindowQuantum h δ +
        (C.card : ℝ) * (2 * h / (h ^ 2 + δ ^ 2)) ≤
      xiWardInteriorSourceArithmeticBound
        ((h : ℂ) + I * (c : ℂ)) := by
  classical
  let w : ℂ := (h : ℂ) + I * (c : ℂ)
  let Cset : Set XiZeroCopy := (C : Set XiZeroCopy)
  have hw : 1 / 2 < w.re := by
    simpa [w, Complex.mul_re] using hh
  have hsource := re_continued_add_critical_tsum_le_sourceArithmetic
    hw Cset (fun q hq => hcritical q (by simpa [Cset] using hq))
  letI : Fintype Cset := C.fintypeCoeSort
  rw [tsum_fintype] at hsource
  have hright : (S.card : ℝ) * xiWardSharpWindowQuantum h δ ≤
      (continuedXiAntiCausalWardResponse w).re := by
    calc
      (S.card : ℝ) * xiWardSharpWindowQuantum h δ =
          ∑ q ∈ S, xiWardSharpWindowQuantum h δ := by simp
      _ ≤ ∑ q ∈ S, (xiAntiCausalWardSchwarzPairResponse q w).re := by
        apply Finset.sum_le_sum
        intro q hq
        exact sharp_interior_pair_quantum (by linarith : 0 < h) q
          (hwinRight q hq)
      _ ≤ (continuedXiAntiCausalWardResponse w).re :=
        finite_sum_re_xiAntiCausalWardSchwarzPairResponse_le_continued S
          (by linarith : 0 < w.re)
  have hcrit : (C.card : ℝ) * (2 * h / (h ^ 2 + δ ^ 2)) ≤
      ∑ q : Cset,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re := by
    rw [show (C.card : ℝ) * (2 * h / (h ^ 2 + δ ^ 2)) =
        ∑ _q : Cset, 2 * h / (h ^ 2 + δ ^ 2) by simp [Cset]]
    apply Finset.sum_le_sum
    intro q hq
    have hmem : q.1 ∈ C := by
      have hqprop := q.property
      change q.1 ∈ C at hqprop
      exact hqprop
    simpa only [w] using
      critical_line_relativeResolvent_window_quantum
        (by linarith : 0 < h) q.1
        (hcritical q.1 hmem) (hwinCritical q.1 hmem)
  change (S.card : ℝ) * xiWardSharpWindowQuantum h δ +
      (C.card : ℝ) * (2 * h / (h ^ 2 + δ ^ 2)) ≤
    xiWardInteriorSourceArithmeticBound w
  linarith

/-- **Multiplicity-exact Euler--Gamma window estimate.** Every finite packet of strict-right
upper zero copies in the height window `|gamma-c| <= delta` costs a uniform positive Ward quantum.
The source-only bound on the right uses only pole, Gamma, and absolutely convergent von Mangoldt
data at `s = h + 1/2 + i*c`, with `Re s > 1`. -/
theorem finite_strictRight_window_card_mul_quantum_le_sourceArithmetic
    (S : Finset XiRightUpperZeroCopy) {h c δ : ℝ} (hh : 1 / 2 < h)
    (hwin : ∀ q ∈ S,
      ((xiRightCenteredZero q.1).im - c) ^ 2 ≤ δ ^ 2) :
    (S.card : ℝ) * (2 * h / ((h + 1 / 2) ^ 2 + δ ^ 2)) ≤
      xiWardInteriorSourceArithmeticBound
        ((h : ℂ) + Complex.I * (c : ℂ)) := by
  let w : ℂ := (h : ℂ) + Complex.I * (c : ℂ)
  let quantum : ℝ := 2 * h / ((h + 1 / 2) ^ 2 + δ ^ 2)
  have hw : 0 < w.re := by
    simp [w, Complex.mul_re]
    linarith
  have hsource := re_continuedXiAntiCausalWardResponse_le_sourceArithmetic
    (w := w) (by simpa [w, Complex.mul_re] using hh)
  have hfinite :=
    finite_sum_re_xiAntiCausalWardSchwarzPairResponse_le_continued S hw
  have hquantum : (S.card : ℝ) * quantum ≤
      ∑ q ∈ S, (xiAntiCausalWardSchwarzPairResponse q w).re := by
    calc
      (S.card : ℝ) * quantum = ∑ q ∈ S, quantum := by simp
      _ ≤ ∑ q ∈ S, (xiAntiCausalWardSchwarzPairResponse q w).re := by
        apply Finset.sum_le_sum
        intro q hq
        exact interior_pair_quantum (by linarith : 0 < h) q (hwin q hq)
  change (S.card : ℝ) * quantum ≤ xiWardInteriorSourceArithmeticBound w
  exact hquantum.trans (hfinite.trans hsource)

/-- Exact real-channel diagonal energy of one strict-right Schwarz pair on an arbitrary positive
vertical line.  This is the shifted version of the Euler-edge diagonal formula. -/
theorem integral_sq_re_xiAntiCausalWardSchwarzPairResponse_line
    (q : XiRightUpperZeroCopy) {h : ℝ} (hh : 0 < h) :
    ∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        ((h : ℂ) + I * (t : ℂ))).re) ^ 2 =
      4 * Real.pi * (1 / (h + (xiRightCenteredZero q.1).re) +
        (h + (xiRightCenteredZero q.1).re) /
          ((h + (xiRightCenteredZero q.1).re) ^ 2 +
            (xiRightCenteredZero q.1).im ^ 2)) := by
  let x : ℝ := h + (xiRightCenteredZero q.1).re
  let b : ℝ := (xiRightCenteredZero q.1).im
  have hx : 0 < x := by
    dsimp [x]
    linarith [xiRightCenteredZero_re_pos q.1]
  have hpair := integral_mul_mirroredKernelPair
    (k := fun x β t : ℝ => x / (x ^ 2 + (t + β) ^ 2))
    hx hx
    (integrable_mul_lorentzianHalves_general hx hx)
    (integral_mul_lorentzianHalves_general hx hx)
    2 2 b b
    (f := fun t : ℝ => (xiAntiCausalWardSchwarzPairResponse q
      ((h : ℂ) + I * (t : ℂ))).re)
    (f' := fun t : ℝ => (xiAntiCausalWardSchwarzPairResponse q
      ((h : ℂ) + I * (t : ℂ))).re)
    (fun t => by
      rw [re_xiAntiCausalWardSchwarzPairResponse_line_eq]
      dsimp [x, b]
      ring)
    (fun t => by
      rw [re_xiAntiCausalWardSchwarzPairResponse_line_eq]
      dsimp [x, b]
      ring)
  rw [show (fun t : ℝ => ((xiAntiCausalWardSchwarzPairResponse q
      ((h : ℂ) + I * (t : ℂ))).re) ^ 2) =
      fun t : ℝ => (xiAntiCausalWardSchwarzPairResponse q
        ((h : ℂ) + I * (t : ℂ))).re *
          (xiAntiCausalWardSchwarzPairResponse q
            ((h : ℂ) + I * (t : ℂ))).re by
    funext t
    ring]
  rw [hpair]
  have hxb : 0 < x ^ 2 + b ^ 2 := by positivity
  change
    2 * (2 * 2) * Real.pi * (x + x) *
        (1 / ((x + x) ^ 2 + (b - b) ^ 2) +
          1 / ((x + x) ^ 2 + (b + b) ^ 2)) =
      4 * Real.pi * (1 / x + x / (x ^ 2 + b ^ 2))
  field_simp [hx.ne', hxb.ne']
  ring

/-- Algebraic annulus quantum.  Shifting a Cauchy width by one unit removes at least one quarter
of diagonal real-channel mass throughout the source-safe strip of widths `[3/5, 11/10]`. -/
theorem one_fourth_le_cauchy_shift_annulus
    {x g : ℝ} (hxlo : 3 / 5 ≤ x) (hxhi : x ≤ 11 / 10) (hg : 0 ≤ g) :
    1 / 4 ≤
      (1 / x - 1 / (x + 1)) +
        (x / (x ^ 2 + g) - (x + 1) / ((x + 1) ^ 2 + g)) := by
  have hx : 0 < x := by linarith
  have hxp : 0 < x + 1 := by linarith
  have hD1 : 0 < x ^ 2 + g := by positivity
  have hD2 : 0 < (x + 1) ^ 2 + g := by positivity
  have hy0 : 0 ≤ x ^ 2 + x := by positivity
  have hyhi : x ^ 2 + x ≤ 231 / 100 := by nlinarith
  have hB : 0 ≤ -2 * (x ^ 2 + x) ^ 2 + 3 * (x ^ 2 + x) + 4 := by
    have hsecond : 0 ≤ 2 * ((x ^ 2 + x) + 231 / 100) - 3 := by nlinarith
    have hfactor : 0 ≤
        (231 / 100 - (x ^ 2 + x)) *
          (2 * ((x ^ 2 + x) + 231 / 100) - 3) :=
      mul_nonneg (sub_nonneg.mpr hyhi) hsecond
    have hendpoint : 0 ≤
        -2 * (231 / 100 : ℝ) ^ 2 + 3 * (231 / 100 : ℝ) + 4 := by norm_num
    nlinarith
  have hC2 : 0 ≤ 4 - (x ^ 2 + x) := by nlinarith
  have hC0 : 0 ≤ x ^ 2 * (x + 1) ^ 2 * (8 - (x ^ 2 + x)) :=
    mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg (x + 1))) (by nlinarith)
  rw [div_le_iff₀ (show (0 : ℝ) < 4 by norm_num)]
  field_simp [hx.ne', hxp.ne', hD1.ne', hD2.ne']
  nlinarith [mul_nonneg hC2 (sq_nonneg g), mul_nonneg hB hg, hC0]

/-- **Source-safe semigroup-annulus diagonal quantum.**  Moving the Ward probe from real shift
`3/5` to `8/5` removes at least `π` of real-channel diagonal energy from every strict-right
Schwarz pair, uniformly in height and uniformly as horizontal displacement tends to zero.  A
critical-line multiplicity copy is absent from the strict-right index type. -/
theorem pi_le_realDiagonalEnergy_threeFifths_sub_eightFifths
    (q : XiRightUpperZeroCopy) :
    Real.pi ≤
      (∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        (((3 / 5 : ℝ) : ℂ) + I * (t : ℂ))).re) ^ 2) -
      ∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        (((8 / 5 : ℝ) : ℂ) + I * (t : ℂ))).re) ^ 2 := by
  rw [integral_sq_re_xiAntiCausalWardSchwarzPairResponse_line q
      (by norm_num : (0 : ℝ) < 3 / 5),
    integral_sq_re_xiAntiCausalWardSchwarzPairResponse_line q
      (by norm_num : (0 : ℝ) < 8 / 5)]
  let x : ℝ := 3 / 5 + (xiRightCenteredZero q.1).re
  let g : ℝ := (xiRightCenteredZero q.1).im ^ 2
  have hre := xiRightCenteredZero_re_pos q.1
  have hstrip := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hxlo : 3 / 5 ≤ x := by dsimp [x]; linarith
  have hxhi : x ≤ 11 / 10 := by dsimp [x]; linarith
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hquantum := one_fourth_le_cauchy_shift_annulus hxlo hxhi hg
  have hshift :
      (8 / 5 + (xiRightCenteredZero q.1).re) =
        (3 / 5 + (xiRightCenteredZero q.1).re) + 1 := by ring
  rw [hshift]
  change Real.pi ≤
    4 * Real.pi * (1 / x + x / (x ^ 2 + g)) -
      4 * Real.pi *
        (1 / (x + 1) + (x + 1) / ((x + 1) ^ 2 + g))
  have hscaled := mul_le_mul_of_nonneg_left hquantum
    (show 0 ≤ 4 * Real.pi by positivity)
  calc
    Real.pi = 4 * Real.pi * (1 / 4) := by ring
    _ ≤ 4 * Real.pi *
        ((1 / x - 1 / (x + 1)) +
          (x / (x ^ 2 + g) - (x + 1) / ((x + 1) ^ 2 + g))) := hscaled
    _ = 4 * Real.pi * (1 / x + x / (x ^ 2 + g)) -
        4 * Real.pi *
          (1 / (x + 1) + (x + 1) / ((x + 1) ^ 2 + g)) := by ring

/-- General coarse annulus lower bound.  The loss between Cauchy widths `x` and `x+d` is bounded
below by `d/(x(x+d))-1/d`, uniformly in the vertical parameter.  The proof keeps the positive
part when `g≤x(x+d)` and otherwise charges the negative part against the elementary denominator
floor `d²g`. -/
theorem cauchy_shift_annulus_ge_width_div_sub_inv
    {x d g : ℝ} (hx : 0 < x) (hd : 0 < d) (hg : 0 ≤ g) :
    d / (x * (x + d)) - 1 / d ≤
      (1 / x - 1 / (x + d)) +
        (x / (x ^ 2 + g) - (x + d) / ((x + d) ^ 2 + g)) := by
  have hxp : 0 < x + d := by positivity
  have hy : 0 < x * (x + d) := mul_pos hx hxp
  have hD1 : 0 < x ^ 2 + g := by positivity
  have hD2 : 0 < (x + d) ^ 2 + g := by positivity
  let D : ℝ := (x ^ 2 + g) * ((x + d) ^ 2 + g)
  have hD : 0 < D := by dsimp [D]; positivity
  have hfirst : 1 / x - 1 / (x + d) = d / (x * (x + d)) := by
    field_simp [hx.ne', hxp.ne']
    ring
  have hsecond :
      x / (x ^ 2 + g) - (x + d) / ((x + d) ^ 2 + g) =
        d * (x * (x + d) - g) / D := by
    dsimp [D]
    field_simp [hD1.ne', hD2.ne']
    ring
  rw [hfirst, hsecond]
  by_cases hgy : g ≤ x * (x + d)
  · have hnonneg : 0 ≤ d * (x * (x + d) - g) / D := by positivity
    have hinv : 0 < 1 / d := one_div_pos.mpr hd
    linarith
  · have hylt : x * (x + d) < g := lt_of_not_ge hgy
    have hDfloor : d ^ 2 * g ≤ D := by
      have hsquare : 0 ≤ (g + x * (x + d)) ^ 2 := sq_nonneg _
      dsimp [D]
      nlinarith
    have hnum : d ^ 2 * (g - x * (x + d)) ≤ D := by
      have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
      have hy0 : 0 ≤ x * (x + d) := hy.le
      nlinarith
    have hratio :
        (g - x * (x + d)) / D ≤ 1 / d ^ 2 := by
      rw [div_le_div_iff₀ hD (sq_pos_of_pos hd)]
      nlinarith
    have hdnonneg : 0 ≤ d := hd.le
    have hscaled := mul_le_mul_of_nonneg_left hratio hdnonneg
    have hdne : d ≠ 0 := hd.ne'
    have hcancel : d * (1 / d ^ 2) = 1 / d := by field_simp
    rw [hcancel] at hscaled
    have hneg :
        -(1 / d) ≤ d * (x * (x + d) - g) / D := by
      calc
        -(1 / d) ≤ -(d * ((g - x * (x + d)) / D)) := neg_le_neg hscaled
        _ = d * (x * (x + d) - g) / D := by ring
    linarith

/-- Source-safe numerical annulus quantum.  For every width in `[51/100,101/100]`, moving ten
units to the right loses at least `3/4` of the normalized real-channel diagonal mass. -/
theorem three_fourths_le_cauchy_shift_annulus_ten
    {x g : ℝ} (hxlo : 51 / 100 ≤ x) (hxhi : x ≤ 101 / 100) (hg : 0 ≤ g) :
    3 / 4 ≤
      (1 / x - 1 / (x + 10)) +
        (x / (x ^ 2 + g) - (x + 10) / ((x + 10) ^ 2 + g)) := by
  have hx : 0 < x := by linarith
  have hbase := cauchy_shift_annulus_ge_width_div_sub_inv
    hx (by norm_num : (0 : ℝ) < 10) hg
  have hy : 0 < x * (x + 10) := by positivity
  have hyhi : x * (x + 10) ≤ (101 / 100) * (1101 / 100) := by nlinarith
  have hnumeric : (3 / 4 : ℝ) ≤ 10 / (x * (x + 10)) - 1 / 10 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hy]
    nlinarith
  exact hnumeric.trans hbase

/-- **Three-pi source-safe annulus quantum.**  Moving the Ward probe from the absolute-Euler
shift `51/100` to `1051/100` removes at least `3π` of real-channel diagonal energy from every
strict-right Schwarz pair.  The estimate is uniform in height and in arbitrarily small positive
horizontal displacement. -/
theorem threePi_le_realDiagonalEnergy_fiftyOneHundredths_sub_tenShift
    (q : XiRightUpperZeroCopy) :
    3 * Real.pi ≤
      (∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ))).re) ^ 2) -
      ∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ))).re) ^ 2 := by
  rw [integral_sq_re_xiAntiCausalWardSchwarzPairResponse_line q
      (by norm_num : (0 : ℝ) < 51 / 100),
    integral_sq_re_xiAntiCausalWardSchwarzPairResponse_line q
      (by norm_num : (0 : ℝ) < 1051 / 100)]
  let x : ℝ := 51 / 100 + (xiRightCenteredZero q.1).re
  let g : ℝ := (xiRightCenteredZero q.1).im ^ 2
  have hre := xiRightCenteredZero_re_pos q.1
  have hstrip := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hxlo : 51 / 100 ≤ x := by dsimp [x]; linarith
  have hxhi : x ≤ 101 / 100 := by dsimp [x]; linarith
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hquantum := three_fourths_le_cauchy_shift_annulus_ten hxlo hxhi hg
  have hshift :
      (1051 / 100 + (xiRightCenteredZero q.1).re) =
        (51 / 100 + (xiRightCenteredZero q.1).re) + 10 := by ring
  rw [hshift]
  change 3 * Real.pi ≤
    4 * Real.pi * (1 / x + x / (x ^ 2 + g)) -
      4 * Real.pi *
        (1 / (x + 10) + (x + 10) / ((x + 10) ^ 2 + g))
  have hscaled := mul_le_mul_of_nonneg_left hquantum
    (show 0 ≤ 4 * Real.pi by positivity)
  calc
    3 * Real.pi = 4 * Real.pi * (3 / 4) := by ring
    _ ≤ 4 * Real.pi *
        ((1 / x - 1 / (x + 10)) +
          (x / (x ^ 2 + g) - (x + 10) / ((x + 10) ^ 2 + g))) := hscaled
    _ = 4 * Real.pi * (1 / x + x / (x ^ 2 + g)) -
        4 * Real.pi *
          (1 / (x + 10) + (x + 10) / ((x + 10) ^ 2 + g)) := by ring

/-- A far source-safe shift retains at least `39/40` of the normalized local diagonal ceiling,
uniformly for widths in `[51/100,101/100]`. -/
theorem thirtyNineFortieths_le_cauchy_shift_annulus_oneHundredFifty
    {x g : ℝ} (hxlo : 51 / 100 ≤ x) (hxhi : x ≤ 101 / 100) (hg : 0 ≤ g) :
    39 / 40 ≤
      (1 / x - 1 / (x + 150)) +
        (x / (x ^ 2 + g) - (x + 150) / ((x + 150) ^ 2 + g)) := by
  have hx : 0 < x := by linarith
  have hbase := cauchy_shift_annulus_ge_width_div_sub_inv
    hx (by norm_num : (0 : ℝ) < 150) hg
  have hy : 0 < x * (x + 150) := by positivity
  have hyhi : x * (x + 150) ≤ (101 / 100) * (15101 / 100) := by nlinarith
  have hnumeric : (39 / 40 : ℝ) ≤ 150 / (x * (x + 150)) - 1 / 150 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hy]
    nlinarith
  exact hnumeric.trans hbase

/-- **Near-four-pi source-safe annulus quantum.**  The absolute-Euler shifts `51/100` and
`15051/100` separate every strict-right Schwarz pair by at least `39π/10`, uniformly in height
and in arbitrarily small positive horizontal displacement. -/
theorem thirtyNineTenthsPi_le_realDiagonalEnergy_fiftyOneHundredths_sub_oneHundredFiftyShift
    (q : XiRightUpperZeroCopy) :
    39 * Real.pi / 10 ≤
      (∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ))).re) ^ 2) -
      ∫ t : ℝ, ((xiAntiCausalWardSchwarzPairResponse q
        (((15051 / 100 : ℝ) : ℂ) + I * (t : ℂ))).re) ^ 2 := by
  rw [integral_sq_re_xiAntiCausalWardSchwarzPairResponse_line q
      (by norm_num : (0 : ℝ) < 51 / 100),
    integral_sq_re_xiAntiCausalWardSchwarzPairResponse_line q
      (by norm_num : (0 : ℝ) < 15051 / 100)]
  let x : ℝ := 51 / 100 + (xiRightCenteredZero q.1).re
  let g : ℝ := (xiRightCenteredZero q.1).im ^ 2
  have hre := xiRightCenteredZero_re_pos q.1
  have hstrip := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hxlo : 51 / 100 ≤ x := by dsimp [x]; linarith
  have hxhi : x ≤ 101 / 100 := by dsimp [x]; linarith
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hquantum :=
    thirtyNineFortieths_le_cauchy_shift_annulus_oneHundredFifty hxlo hxhi hg
  have hshift :
      (15051 / 100 + (xiRightCenteredZero q.1).re) =
        (51 / 100 + (xiRightCenteredZero q.1).re) + 150 := by ring
  rw [hshift]
  change 39 * Real.pi / 10 ≤
    4 * Real.pi * (1 / x + x / (x ^ 2 + g)) -
      4 * Real.pi *
        (1 / (x + 150) + (x + 150) / ((x + 150) ^ 2 + g))
  have hscaled := mul_le_mul_of_nonneg_left hquantum
    (show 0 ≤ 4 * Real.pi by positivity)
  calc
    39 * Real.pi / 10 = 4 * Real.pi * (39 / 40) := by ring
    _ ≤ 4 * Real.pi *
        ((1 / x - 1 / (x + 150)) +
          (x / (x ^ 2 + g) - (x + 150) / ((x + 150) ^ 2 + g))) := hscaled
    _ = 4 * Real.pi * (1 / x + x / (x ^ 2 + g)) -
        4 * Real.pi *
          (1 / (x + 150) + (x + 150) / ((x + 150) ^ 2 + g)) := by ring

/-- Exact obstruction to promoting the diagonal annulus quantum by pointwise cross positivity.
For ordinate separation beyond `2√(x(x+d))`, the difference of the two Cauchy cross kernels is
strictly negative. -/
theorem cauchy_cross_shift_annulus_neg_of_sq_gt
    {x d Δ : ℝ} (hx : 0 < x) (hd : 0 < d)
    (hsep : 4 * x * (x + d) < Δ ^ 2) :
    2 * x / ((2 * x) ^ 2 + Δ ^ 2) -
        2 * (x + d) / ((2 * (x + d)) ^ 2 + Δ ^ 2) < 0 := by
  have hxp : 0 < x + d := by positivity
  have hD1 : 0 < (2 * x) ^ 2 + Δ ^ 2 := by positivity
  have hD2 : 0 < (2 * (x + d)) ^ 2 + Δ ^ 2 := by positivity
  rw [sub_lt_zero, div_lt_div_iff₀ hD1 hD2]
  nlinarith

/-- The spatial cross kernel of every positive real-shift annulus is integrable. -/
theorem integrable_cauchy_cross_shift_annulus
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    Integrable (fun Δ : ℝ =>
      2 * x / ((2 * x) ^ 2 + Δ ^ 2) -
        2 * (x + d) / ((2 * (x + d)) ^ 2 + Δ ^ 2)) := by
  have hx2 : 0 < 2 * x := by positivity
  have hxd2 : 0 < 2 * (x + d) := by positivity
  have h₁ := lorentzianHalf_integrable hx2 0
  have h₂ := lorentzianHalf_integrable hxd2 0
  change Integrable
    ((fun Δ : ℝ => 2 * x / ((2 * x) ^ 2 + Δ ^ 2)) -
      fun Δ : ℝ => 2 * (x + d) / ((2 * (x + d)) ^ 2 + Δ ^ 2))
  simpa only [add_zero] using h₁.sub h₂

/-- **Zero-frequency annihilation of the Ward annulus.**  Although its diagonal value is
strictly positive, the spatial annulus kernel has exactly zero total mass.  Thus a nearly
constant dense ordinate packet lies in the low-frequency blind channel: no positive multiple of
the diagonal can be recovered from the aggregate annulus quadratic form without an additional
source-side trace or decorrelation law. -/
theorem integral_cauchy_cross_shift_annulus_eq_zero
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    ∫ Δ : ℝ,
      (2 * x / ((2 * x) ^ 2 + Δ ^ 2) -
        2 * (x + d) / ((2 * (x + d)) ^ 2 + Δ ^ 2)) = 0 := by
  have hx2 : 0 < 2 * x := by positivity
  have hxd2 : 0 < 2 * (x + d) := by positivity
  have h₁ : Integrable (fun Δ : ℝ =>
      2 * x / ((2 * x) ^ 2 + Δ ^ 2)) := by
    simpa only [add_zero] using lorentzianHalf_integrable hx2 0
  have h₂ : Integrable (fun Δ : ℝ =>
      2 * (x + d) / ((2 * (x + d)) ^ 2 + Δ ^ 2)) := by
    simpa only [add_zero] using lorentzianHalf_integrable hxd2 0
  have hi₁ : (∫ Δ : ℝ,
      2 * x / ((2 * x) ^ 2 + Δ ^ 2)) = Real.pi := by
    simpa only [add_zero] using integral_lorentzianHalf hx2 0
  have hi₂ : (∫ Δ : ℝ,
      2 * (x + d) / ((2 * (x + d)) ^ 2 + Δ ^ 2)) = Real.pi := by
    simpa only [add_zero] using integral_lorentzianHalf hxd2 0
  rw [MeasureTheory.integral_sub h₁ h₂, hi₁, hi₂, sub_self]

/-- The same zero-mean annulus has a strictly positive diagonal.  Its exact diagonal value is
`d/(2x(x+d))`; zero-frequency annihilation is therefore genuine off-diagonal cancellation, not
vanishing of the local separator. -/
theorem cauchy_cross_shift_annulus_zero_eq_pos
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    2 * x / ((2 * x) ^ 2 + 0 ^ 2) -
        2 * (x + d) / ((2 * (x + d)) ^ 2 + 0 ^ 2) =
          d / (2 * x * (x + d)) ∧
      0 < d / (2 * x * (x + d)) := by
  have hxd : 0 < x + d := by positivity
  constructor
  · field_simp [hx.ne', hxd.ne']
    ring
  · positivity

/-! ## Exact first-four-moment barrier -/

/-- Expanding the extremal quadratic against the bandwidth-one sine-kernel moments
`m₁=1`, `m₂=4/3`, `m₃=2`, `m₄=13/4` leaves exactly `m₀-31/36`.

This is the square-certificate form of the `3×3` Hankel determinant
`(36m₀-31)/108`. -/
theorem firstFourSineMoment_extremalSquare_identity (positiveMass : ℝ) :
    positiveMass + 2 * (-7 / 4 : ℝ) * 1
        + (((-7 / 4 : ℝ) ^ 2) + 2 * (2 / 3 : ℝ)) * (4 / 3)
        + 2 * (-7 / 4 : ℝ) * (2 / 3) * 2
        + ((2 / 3 : ℝ) ^ 2) * (13 / 4) =
      positiveMass - 31 / 36 := by
  ring

/-- **Sharp fourth-moment positive-mass barrier.**  Nonnegativity of the square of
`1-(7/4)x+(2/3)x²`, together with the first four bandwidth-one sine-kernel moments, forces
positive spectral mass at least `31/36`. -/
theorem firstFourSineMoment_positiveMass_ge_thirtyOneThirtySixths
    {positiveMass squareEnergy : ℝ}
    (henergy : 0 ≤ squareEnergy)
    (hmoments :
      squareEnergy =
        positiveMass + 2 * (-7 / 4 : ℝ) * 1
          + (((-7 / 4 : ℝ) ^ 2) + 2 * (2 / 3 : ℝ)) * (4 / 3)
          + 2 * (-7 / 4 : ℝ) * (2 / 3) * 2
          + ((2 / 3 : ℝ) ^ 2) * (13 / 4)) :
    31 / 36 ≤ positiveMass := by
  rw [firstFourSineMoment_extremalSquare_identity] at hmoments
  linarith

/-- At equality in the first-four-moment barrier, the standard off-RH conversion
`2m₀-1` is exactly `13/18`, strictly below three quarters. -/
theorem firstFourSineMoment_lineCertificate_eq_thirteenEighteenths
    {positiveMass lineCertificate : ℝ}
    (hmass : positiveMass = 31 / 36)
    (hline : lineCertificate = 2 * positiveMass - 1) :
    lineCertificate = 13 / 18 := by
  rw [hline, hmass]
  norm_num

/-- The fourth sine-kernel moment `13/4` exceeds the `29/9` threshold required for the
same quadratic moment certificate to force a three-quarters line bound. -/
theorem twentyNineNinths_lt_thirteenFourths :
    (29 / 9 : ℝ) < 13 / 4 := by
  norm_num

/-! ## Reflection-curvature submicroscopic renormalization -/

/-- Inverse-depth normalization of the diagonal Cauchy curvature that compares an off-line
functional-equation pair with two critical-line copies at the same ordinate. -/
def horizontalCauchyCurvatureAtom (h a : ℝ) : ℝ :=
  a⁻¹ ^ 2 * ((h + a)⁻¹ + (h - a)⁻¹ - 2 * h⁻¹)

/-- **Exact horizontal reflection curvature.**  For `0<a<h`, the two reflected widths `h+a`
and `h-a` exceed the double critical width after inverse-`a²` renormalization by exactly
`2/[h(h²-a²)]`. -/
theorem horizontalCauchyCurvatureAtom_eq
    {h a : ℝ} (ha : 0 < a) (hah : a < h) :
    horizontalCauchyCurvatureAtom h a =
      2 / (h * (h ^ 2 - a ^ 2)) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hh : 0 < h := ha.trans hah
  have hh0 : h ≠ 0 := hh.ne'
  have hpa : h + a ≠ 0 := (add_pos hh ha).ne'
  have hma : h - a ≠ 0 := (sub_pos.mpr hah).ne'
  have hdiff : h ^ 2 - a ^ 2 ≠ 0 := by nlinarith
  rw [horizontalCauchyCurvatureAtom]
  field_simp [ha0, hh0, hpa, hma, hdiff]
  ring

/-- Every strict positive reflection shift carries at least `2/h³` of normalized curvature. -/
theorem two_div_cube_le_horizontalCauchyCurvatureAtom
    {h a : ℝ} (ha : 0 < a) (hah : a < h) :
    2 / h ^ 3 ≤ horizontalCauchyCurvatureAtom h a := by
  rw [horizontalCauchyCurvatureAtom_eq ha hah]
  have hh : 0 < h := ha.trans hah
  have hdiff : 0 < h ^ 2 - a ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by positivity : 0 < h ^ 3)
    (mul_pos hh hdiff)]
  nlinarith [sq_pos_of_pos ha]

/-- On the submicroscopic half-width `2a≤h`, normalized reflection curvature is also bounded by
`8/(3h³)`.  Thus its positive-shift charge stays within a fixed factor `4/3`, independently of
how closely the off-line pair approaches the critical line. -/
theorem horizontalCauchyCurvatureAtom_le_eight_div_three_cube
    {h a : ℝ} (ha : 0 < a) (hahalf : 2 * a ≤ h) :
    horizontalCauchyCurvatureAtom h a ≤ 8 / (3 * h ^ 3) := by
  have hah : a < h := by linarith
  rw [horizontalCauchyCurvatureAtom_eq ha hah]
  have hh : 0 < h := by linarith
  have hdiff : 0 < h ^ 2 - a ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (mul_pos hh hdiff)
    (by positivity : 0 < 3 * h ^ 3)]
  nlinarith [sq_nonneg (h - 2 * a)]

/-- Critical diagonal multiplicity contributes zero to the totalized normalized curvature atom. -/
theorem horizontalCauchyCurvatureAtom_zero (h : ℝ) :
    horizontalCauchyCurvatureAtom h 0 = 0 := by
  simp [horizontalCauchyCurvatureAtom]

/-! ## Plücker--Ward submicroscopic renormalization -/

/-- The exact hyperbolic lower bound behind quadratic coalescence:
`cosh(2x)-1 = 2 sinh(x)² ≥ 2x²`. -/
theorem two_mul_sq_le_cosh_two_mul_sub_one (x : ℝ) :
    2 * x ^ 2 ≤ Real.cosh (2 * x) - 1 := by
  rw [Real.cosh_two_mul]
  have hsquare : x ^ 2 ≤ Real.sinh x ^ 2 := by
    by_cases hx : 0 ≤ x
    · have hsinh : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx
      have hsinh0 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
      nlinarith
    · have hx' : x ≤ 0 := le_of_not_ge hx
      have hsinh : Real.sinh x ≤ x := Real.sinh_le_self_iff.mpr hx'
      have hsinh0 : Real.sinh x ≤ 0 := Real.sinh_nonpos_iff.mpr hx'
      nlinarith
  nlinarith [Real.cosh_sq x]

/-- **Finite-band quadratic ceiling.**  Inside the unit hyperbolic window the
coalescence gap is at most quadratic.  Together with
`two_mul_sq_le_cosh_two_mul_sub_one`, this shows that a bounded-frequency
Plücker/Gabor reader loses every off-line pair at precisely quadratic order as
its transverse displacement tends to zero. -/
theorem cosh_sub_one_le_sq_of_abs_le_one
    {x : ℝ} (hx : |x| ≤ 1) :
    Real.cosh x - 1 ≤ x ^ 2 := by
  have hxp := Real.abs_exp_sub_one_sub_id_le hx
  have hxn : |-x| ≤ 1 := by simpa using hx
  have hxm := Real.abs_exp_sub_one_sub_id_le hxn
  rw [Real.cosh_eq]
  have hp : Real.exp x - 1 - x ≤ x ^ 2 :=
    le_trans (le_abs_self _) hxp
  have hm : Real.exp (-x) - 1 + x ≤ x ^ 2 := by
    have h := le_trans
      (le_abs_self (Real.exp (-x) - 1 - (-x))) hxm
    simpa only [sub_neg_eq_add, neg_sq] using h
  linarith

/-- On a band `|2au| ≤ 1`, the Plücker coalescence gap is trapped between
`2a²u²` and `4a²u²`.  The lower half is
`two_mul_sq_le_cosh_two_mul_sub_one`; this is the matching upper half. -/
theorem coshGap_le_four_mul_sq_of_submicroscopic
    {a u : ℝ} (hband : |2 * a * u| ≤ 1) :
    Real.cosh (2 * a * u) - 1 ≤ 4 * a ^ 2 * u ^ 2 := by
  have h := cosh_sub_one_le_sq_of_abs_le_one hband
  nlinarith

/-- **Exact submicroscopic cancellation law.**  The squared self-Cauchy singularity
`1/(2a)²` exactly cancels the quadratic Gabor/Plücker coalescence
`cosh(2au)-1`.  The resulting quantum is at least `u²/2`, uniformly for every
strictly positive displacement `a`, however small. -/
theorem half_sq_le_coshGap_mul_sq_transverseCauchyKernel_self
    {a : ℝ} (ha : 0 < a) (u gamma : ℝ) :
    u ^ 2 / 2 ≤
      (Real.cosh (2 * a * u) - 1) *
        (transverseCauchyKernel a a (gamma - gamma)) ^ 2 := by
  rw [transverseCauchyKernel_self ha gamma]
  have hgap := two_mul_sq_le_cosh_two_mul_sub_one (a * u)
  have hgap' :
      2 * (a * u) ^ 2 ≤ Real.cosh (2 * a * u) - 1 := by
    simpa only [mul_assoc] using hgap
  have hden : 0 < (2 * a) ^ 2 := sq_pos_of_pos (mul_pos (by norm_num) ha)
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hden]
  nlinarith [hgap']

/-- Scalar atom formed by the collapsing Plücker gap and tensor-square Hardy diagonal. -/
def pluckerWardRenormalizedAtom (a u : ℝ) : ℝ :=
  (Real.cosh (2 * a * u) - 1) * ((2 * a)⁻¹) ^ 2

/-- The boundary-line value is zero under Lean's totalized inverse convention. -/
theorem pluckerWardRenormalizedAtom_zero (u : ℝ) :
    pluckerWardRenormalizedAtom 0 u = 0 := by
  simp [pluckerWardRenormalizedAtom]

/-- Every positive real shift carries the uniform renormalized quantum `u²/2`. -/
theorem pluckerWardRenormalizedAtom_ge_half_sq
    {a : ℝ} (ha : 0 < a) (u : ℝ) :
    u ^ 2 / 2 ≤ pluckerWardRenormalizedAtom a u := by
  have hgap := two_mul_sq_le_cosh_two_mul_sub_one (a * u)
  have hgap' :
      2 * (a * u) ^ 2 ≤ Real.cosh (2 * a * u) - 1 := by
    simpa only [mul_assoc] using hgap
  rw [pluckerWardRenormalizedAtom]
  have hden : 0 < (2 * a) ^ 2 := sq_pos_of_pos (mul_pos (by norm_num) ha)
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hden]
  nlinarith [hgap']

/-- **Quantitative submicroscopic separator.**  Once the inverse Cauchy
diagonal cancels quadratic coalescence, the positive-shift atom lies in the
fixed interval `[u²/2,u²]` throughout `|2au| ≤ 1`.  At `a=0` its value is
exactly zero, so this interval is a displacement-uniform charge carried only
by strict positive shifts. -/
theorem pluckerWardRenormalizedAtom_mem_Icc
    {a u : ℝ} (ha : 0 < a) (hband : |2 * a * u| ≤ 1) :
    pluckerWardRenormalizedAtom a u ∈ Set.Icc (u ^ 2 / 2) (u ^ 2) := by
  refine ⟨pluckerWardRenormalizedAtom_ge_half_sq ha u, ?_⟩
  have hgap := coshGap_le_four_mul_sq_of_submicroscopic hband
  have ha0 : a ≠ 0 := ha.ne'
  rw [pluckerWardRenormalizedAtom]
  field_simp [ha0]
  nlinarith

/-- **Boundary-singularity necessity.**  No function continuous at zero, vanishing there, can
carry one fixed positive quantum at every positive displacement.  This elementary topological
barrier explains why a submicroscopic separator must use a singular normalization or a genuinely
discontinuous/source-index channel. -/
theorem not_exists_uniform_positive_continuous_boundarySeparator
    (F : ℝ → ℝ) (hF : ContinuousAt F 0) (hF0 : F 0 = 0) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 < a → c ≤ F a := by
  rintro ⟨c, hc, hsep⟩
  have hseq : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      Filter.atTop (𝓝 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcomp : Filter.Tendsto
      (fun n : ℕ => F (1 / ((n : ℝ) + 1))) Filter.atTop (𝓝 0) := by
    have h := hF.tendsto.comp hseq
    rw [hF0] at h
    simpa [Function.comp_def] using h
  have hev : ∀ᶠ n : ℕ in Filter.atTop, F (1 / ((n : ℝ) + 1)) < c :=
    (tendsto_order.1 hcomp).2 c hc
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hn := hN N le_rfl
  have ha : 0 < 1 / ((N : ℝ) + 1) := by positivity
  exact (not_lt_of_ge (hsep _ ha)) hn

/-- The renormalized Plücker--Ward atom has the forced boundary discontinuity predicted by
`not_exists_uniform_positive_continuous_boundarySeparator` whenever the frequency is nonzero. -/
theorem not_continuousAt_zero_pluckerWardRenormalizedAtom
    {u : ℝ} (hu : u ≠ 0) :
    ¬ ContinuousAt (fun a => pluckerWardRenormalizedAtom a u) 0 := by
  intro hcontinuous
  apply not_exists_uniform_positive_continuous_boundarySeparator
    (fun a => pluckerWardRenormalizedAtom a u) hcontinuous
    (pluckerWardRenormalizedAtom_zero u)
  refine ⟨u ^ 2 / 2, ?_, ?_⟩
  · positivity
  · exact fun a ha => pluckerWardRenormalizedAtom_ge_half_sq ha u

/-- **Actual Euler--Gamma Ward separator at an adapted off-line node.**  The continued Ward
field dominates the inverse displacement before squaring.  Multiplying its norm square by the
collapsing Plücker gap therefore leaves a strict `2u²` quantum for every nonzero frequency `u`,
uniformly down to arbitrarily small positive horizontal displacement.  Critical-line
multiplicity is absent from `XiRightUpperZeroCopy`.

This theorem is local and zero-adapted.  A density consequence still requires a source-defined
sampling/trace law that aggregates these adapted nodes without selecting the unknown divisor. -/
theorem two_mul_sq_lt_coshGap_mul_normSq_continuedWard_at_adaptedNode
    (q : XiRightUpperZeroCopy) {u : ℝ} (hu : u ≠ 0) :
    2 * u ^ 2 <
      (Real.cosh (2 * (xiRightCenteredZero q.1).re * u) - 1) *
        Complex.normSq (continuedXiAntiCausalWardResponse
          ((starRingEnd ℂ) (xiRightCenteredZero q.1))) := by
  let a := (xiRightCenteredZero q.1).re
  let r := continuedXiAntiCausalWardResponse
    ((starRingEnd ℂ) (xiRightCenteredZero q.1))
  have ha : 0 < a := xiRightCenteredZero_re_pos q.1
  have hresponse : a⁻¹ < r.re := by
    simpa only [a, r] using
      re_continuedXiAntiCausalWardResponse_at_adaptedNode_gt_inv q
  have hresponse0 : 0 < r.re := lt_trans (inv_pos.mpr ha) hresponse
  have hinv0 : 0 < a⁻¹ := inv_pos.mpr ha
  have hre_sq : r.re ^ 2 ≤ Complex.normSq r := by
    simpa [pow_two] using Complex.re_sq_le_normSq r
  have hinv_sq : a⁻¹ ^ 2 < Complex.normSq r := by
    have hsquare : a⁻¹ ^ 2 < r.re ^ 2 := by nlinarith
    exact hsquare.trans_le hre_sq
  have hgap := two_mul_sq_le_cosh_two_mul_sub_one (a * u)
  have hgap' :
      2 * (a * u) ^ 2 ≤ Real.cosh (2 * a * u) - 1 := by
    simpa only [mul_assoc] using hgap
  have hgap_pos : 0 < Real.cosh (2 * a * u) - 1 := by
    have hau : a * u ≠ 0 := mul_ne_zero ha.ne' hu
    nlinarith [hgap', sq_pos_of_ne_zero hau]
  have hmul := mul_lt_mul_of_pos_left hinv_sq hgap_pos
  have ha0 : a ≠ 0 := ha.ne'
  dsimp [a, r] at hmul ⊢
  have hscaled :
      2 * u ^ 2 ≤
        (Real.cosh (2 * (xiRightCenteredZero q.1).re * u) - 1) *
          ((xiRightCenteredZero q.1).re)⁻¹ ^ 2 := by
    have hden : 0 < ((xiRightCenteredZero q.1).re) ^ 2 :=
      sq_pos_of_pos ha
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hden]
    nlinarith [hgap']
  exact hscaled.trans_lt hmul

/-! ## Shallow-layer Cauchy energy -/

/-- **Multiplicity-exact shallow-layer law.**  For transverse depths `0 < a_j ≤ h`, the positive
Hardy/Cauchy Gram energy on the shifted line `h + a_j` charges at least `1 / h` for every unit of
strict-right multiplicity.  No lower bound on `m_j` is needed: zero weights contribute nothing.
All off-diagonal terms have the favorable sign. -/
theorem sum_multiplicity_le_shift_mul_finiteOfflineCauchyEnergy
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) (hale : ∀ j, a j ≤ h) :
    (∑ j, (m j : ℝ)) ≤ h * finiteOfflineCauchyEnergy
      (fun j => h + a j) gamma m := by
  have hshift : ∀ j, 0 < h + a j := fun j => add_pos hh (ha j)
  have hbase := finiteOfflineCauchyEnergy_ge_two_mul_sum_sq_div
    (gamma := gamma) m hshift
  have hterm : ∀ j : Fin n,
      (m j : ℝ) / h ≤ 2 * ((m j : ℝ) ^ 2 / (h + a j)) := by
    intro j
    have hden : 0 < h + a j := hshift j
    by_cases hm0 : m j = 0
    · simp [hm0]
    · have hmreal : (1 : ℝ) ≤ m j := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
      have hmnonneg : (0 : ℝ) ≤ m j := by positivity
      rw [show 2 * ((m j : ℝ) ^ 2 / (h + a j)) =
          (2 * (m j : ℝ) ^ 2) / (h + a j) by ring]
      rw [div_le_div_iff₀ hh hden]
      have hma : (m j : ℝ) * a j ≤ (m j : ℝ) * h :=
        mul_le_mul_of_nonneg_left (hale j) hmnonneg
      have hsq : (m j : ℝ) ≤ (m j : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hmnonneg (sub_nonneg.mpr hmreal)]
      have hsqh : (m j : ℝ) * h ≤ (m j : ℝ) ^ 2 * h :=
        mul_le_mul_of_nonneg_right hsq hh.le
      nlinarith
  have hsum : (∑ j, (m j : ℝ)) / h ≤
      2 * ∑ j, (m j : ℝ) ^ 2 / (h + a j) := by
    calc
      (∑ j, (m j : ℝ)) / h = ∑ j, (m j : ℝ) / h := by
        rw [Finset.sum_div]
      _ ≤ ∑ j, 2 * ((m j : ℝ) ^ 2 / (h + a j)) :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = 2 * ∑ j, (m j : ℝ) ^ 2 / (h + a j) := by
        rw [Finset.mul_sum]
  have hdiv_le : (∑ j, (m j : ℝ)) / h ≤
      finiteOfflineCauchyEnergy (fun j => h + a j) gamma m :=
    hsum.trans hbase
  rw [div_le_iff₀ hh] at hdiv_le
  simpa only [mul_comm] using hdiv_le

/-- **Exact shallow-layer count law.**  Suppose every positive transverse displacement lies in
`0 < a_j ≤ h` and every packet multiplicity is nonzero.  Shifting the Hardy/Cauchy observation
line by `h` makes each self-diagonal cost at least `1 / h`; positivity of every cross term gives

`n ≤ h · finiteOfflineCauchyEnergy (h + a) gamma m`.

Thus choosing `h` on the submicroscopic scale `1 / log T` charges order `log T` per off-line
copy without annular zero-mode cancellation.  A density theorem still needs a source-defined
upper bound for this shifted energy at the same shrinking scale. -/
theorem card_le_shift_mul_finiteOfflineCauchyEnergy
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} {m : Fin n → ℕ}
    (ha : ∀ j, 0 < a j) (hale : ∀ j, a j ≤ h)
    (hm : ∀ j, 1 ≤ m j) :
    (n : ℝ) ≤ h * finiteOfflineCauchyEnergy
      (fun j => h + a j) gamma m := by
  have hshift : ∀ j, 0 < h + a j := fun j => add_pos hh (ha j)
  have hbase := finiteOfflineCauchyEnergy_ge_two_mul_sum_sq_div
    (gamma := gamma) m hshift
  have hterm : ∀ j : Fin n,
      1 / h ≤ 2 * ((m j : ℝ) ^ 2 / (h + a j)) := by
    intro j
    have hden : 0 < h + a j := hshift j
    have hmreal : (1 : ℝ) ≤ m j := by exact_mod_cast hm j
    rw [show 2 * ((m j : ℝ) ^ 2 / (h + a j)) =
        (2 * (m j : ℝ) ^ 2) / (h + a j) by ring]
    rw [div_le_div_iff₀ hh hden]
    nlinarith [hale j, sq_nonneg ((m j : ℝ) - 1)]
  have hsum : (n : ℝ) / h ≤
      2 * ∑ j, (m j : ℝ) ^ 2 / (h + a j) := by
    calc
      (n : ℝ) / h = ∑ _j : Fin n, 1 / h := by
        simp [div_eq_mul_inv]
      _ ≤ ∑ j, 2 * ((m j : ℝ) ^ 2 / (h + a j)) :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = 2 * ∑ j, (m j : ℝ) ^ 2 / (h + a j) := by
        rw [Finset.mul_sum]
  have hdiv_le : (n : ℝ) / h ≤
      finiteOfflineCauchyEnergy (fun j => h + a j) gamma m :=
    hsum.trans hbase
  rw [div_le_iff₀ hh] at hdiv_le
  simpa only [mul_comm] using hdiv_le

/-- Xi-zero specialization of `card_le_shift_mul_finiteOfflineCauchyEnergy`.
Critical-line zeros are absent by construction: `XiRightUpperZeroCopy` contains only strictly
positive centered real shifts. -/
theorem xiRight_shallowLayer_card_le_shift_mul_finiteOfflineCauchyEnergy
    {n : ℕ} {h : ℝ} (hh : 0 < h) (q : Fin n → XiRightUpperZeroCopy)
    (hdepth : ∀ j, (xiRightCenteredZero (q j).1).re ≤ h) :
    (n : ℝ) ≤ h * finiteOfflineCauchyEnergy
      (fun j => h + (xiRightCenteredZero (q j).1).re)
      (fun j => (xiRightCenteredZero (q j).1).im)
      (fun _ => 1) := by
  apply card_le_shift_mul_finiteOfflineCauchyEnergy hh
  · exact fun j => xiRightCenteredZero_re_pos (q j).1
  · exact hdepth
  · simp

end

end RHTower
