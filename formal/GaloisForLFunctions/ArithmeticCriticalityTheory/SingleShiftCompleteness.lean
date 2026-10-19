import GaloisForLFunctions.ArithmeticCriticalityTheory.PoleFreeShiftAveragedVariationAndCrossEnergyLaw
import GaloisForLFunctions.ArithmeticCriticalityTheory.TwoBumpProfile
import GaloisForLFunctions.RHTower.WeilMarkovHalfLineTrivialZeroCriterion

/-!
# Single-shift completeness of the shifted ground states

Fix one shift `a > 0`. Every odd `C²_c` test `F` that vanishes on a neighbourhood `(−ε, ε)` of the
origin factors through the shifted ground state with an even `C²_c` profile:

    F = m_a · u,    u = F / m_a,

because `m_a` is `C²`, odd, and vanishes only at `0`, where `u` is identically zero. Without RH such
a test with negative Markov energy exists (the half-line witness of the trivial-zero criterion), and
it is the same test for every shift. Hence for every single `a > 0`

    RH  ⟺  markovEnergy(Φ(ω_a u)) ≥ 0  for every even u ∈ C²_c(ℝ)
        ⟺  the same for every even u ∈ C²_c(ℝ) vanishing near the origin
        ⟺  the variation inequality  D_a(u) ≤ 2 S_a(u) + 4 sinh(a/2) ∫ u² dμ_a
        ⟺  the pole-free variation inequality  D_a(u) ≤ 2 S_a(u) + V_a(u)
        ⟺  remainder dominates defect  4 ∫ u² ω_a Φ (C_a − sinh(a/2) sinh(x/2)) ≤ R_N(ω_a, u).

The shift is a gauge: each frontier inequality of the theory, at any one shift, is the whole
Riemann hypothesis, not a weaker consequence. Two readings follow. The origin, where every folded
supersolution fails, is not where the zeros are detected: profiles vanishing near `0` suffice. And
averaging over shifts cannot enlarge the test class; it only changes the weight.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The Doob profile of a test relative to `ω_a`: `u = F / m_a` (zero at the origin). -/
def shiftQuotient (a : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ := F x / shiftDifference a x

theorem shiftQuotient_neg (a : ℝ) {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) (x : ℝ) :
    shiftQuotient a F (-x) = shiftQuotient a F x := by
  unfold shiftQuotient
  rw [hodd, shiftDifference_neg, neg_div_neg_eq]

theorem shiftDifference_mul_shiftQuotient {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (h0 : F 0 = 0)
    (x : ℝ) : shiftDifference a x * shiftQuotient a F x = F x := by
  unfold shiftQuotient
  rcases eq_or_ne x 0 with rfl | hx
  · rw [h0, zero_div, mul_zero]
  · exact mul_div_cancel₀ _ (shiftDifference_ne_zero_of_ne ha hx)

/-- The Doob test of `ω_a` with profile `F / m_a` is `F` itself. -/
theorem phiDoobTest_shiftedGroundState_mul_shiftQuotient {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (h0 : F 0 = 0) (x : ℝ) :
    phiDoobTest (fun y => shiftedGroundState a y * shiftQuotient a F y) x = F x := by
  unfold phiDoobTest
  rw [← mul_assoc, riemannKernelReal_mul_shiftedGroundState,
    shiftDifference_mul_shiftQuotient ha h0]

/-- A `C²` test vanishing near the origin has a `C²` profile: away from `0` it is a quotient by the
nonvanishing `m_a`, near `0` it is identically zero. -/
theorem contDiff_shiftQuotient {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hvan : ∀ x, |x| < ε → F x = 0) : ContDiff ℝ 2 (shiftQuotient a F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : |x| < ε
  · have hev : shiftQuotient a F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
      unfold shiftQuotient
      rw [hvan y hy, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (by rwa [abs_zero])
    exact hF.contDiffAt.div (contDiff_shiftDifference_two a).contDiffAt
      (shiftDifference_ne_zero_of_ne ha hx0)

theorem hasCompactSupport_shiftQuotient (a : ℝ) {F : ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (shiftQuotient a F) := by
  refine hF.mono fun x hx hFx => hx ?_
  unfold shiftQuotient
  rw [hFx, zero_div]

/-- The profile of a test vanishing on `(−ε, ε)` vanishes there too. -/
theorem shiftQuotient_eq_zero_of_abs_lt {a ε : ℝ} {F : ℝ → ℝ} (hvan : ∀ x, |x| < ε → F x = 0)
    {x : ℝ} (hx : |x| < ε) : shiftQuotient a F x = 0 := by
  unfold shiftQuotient
  rw [hvan x hx, zero_div]

/-- **The odd witness.** Without RH there is an odd `C²_c` test vanishing near the origin with
negative Markov energy. -/
theorem exists_odd_vanishing_markovEnergy_neg_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ (F : ℝ → ℝ) (ε : ℝ), ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ 0 < ε ∧
      (∀ x, F (-x) = -F x) ∧ (∀ x, |x| < ε → F x = 0) ∧
        markovEnergy (fun x => (F x : ℂ)) < 0 := by
  obtain ⟨f, ε, hf, hfc, hε, hvan, hneg⟩ :=
    exists_halfLine_markovEnergy_oddExt_neg_of_not_riemannHypothesis hRH
  refine ⟨fun x => f x - f (-x), ε, hf.sub (hf.comp contDiff_neg), ?_, hε,
    fun x => by simp only [neg_neg]; ring, fun x hx => ?_, hneg⟩
  · exact hfc.sub (hfc.comp_homeomorph (Homeomorph.neg ℝ))
  · have h1 : x < ε := lt_of_le_of_lt (le_abs_self x) hx
    have h2 : -x < ε := lt_of_le_of_lt (neg_le_abs x) hx
    simp only [hvan x h1, hvan (-x) h2, sub_zero]

/-- Without RH, for every shift `a > 0` some even `C²_c` profile vanishing near the origin has
negative Markov energy against `ω_a`; the test `Φ(ω_a u)` is the same for all shifts. -/
theorem exists_profile_vanishing_markovEnergy_neg_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) {a : ℝ} (ha : 0 < a) :
    ∃ (u : ℝ → ℝ) (ε : ℝ), ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧ 0 < ε ∧
      (∀ x, |x| < ε → u x = 0) ∧
        markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) < 0 := by
  obtain ⟨F, ε, hF, hFc, hε, hodd, hvan, hneg⟩ :=
    exists_odd_vanishing_markovEnergy_neg_of_not_riemannHypothesis hRH
  have h0 : F 0 = 0 := hvan 0 (by rwa [abs_zero])
  refine ⟨shiftQuotient a F, ε, contDiff_shiftQuotient ha hε hF hvan,
    hasCompactSupport_shiftQuotient a hFc, shiftQuotient_neg a hodd, hε,
    fun x hx => shiftQuotient_eq_zero_of_abs_lt hvan hx, ?_⟩
  have e : (fun x => (phiDoobTest (fun y => shiftedGroundState a y * shiftQuotient a F y) x : ℂ)) =
      fun x => (F x : ℂ) :=
    funext fun x => by rw [phiDoobTest_shiftedGroundState_mul_shiftQuotient ha h0]
  rwa [e]

/-- **Single-shift completeness.** For every fixed shift `a > 0`, RH holds if and only if the Markov
energy of `Φ(ω_a u)` is nonnegative for every even `u ∈ C²_c(ℝ)`. -/
theorem riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) →
        0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  refine ⟨fun hRH u hu huc heven =>
    riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg.mp hRH _
      ((contDiff_shiftedGroundState a).mul hu) huc.mul_left
      fun x => by rw [shiftedGroundState_neg, heven]; ring, fun h => by_contra fun hRH => ?_⟩
  obtain ⟨u, -, hu, huc, heven, -, -, hneg⟩ :=
    exists_profile_vanishing_markovEnergy_neg_of_not_riemannHypothesis hRH ha
  exact absurd (h u hu huc heven) (not_le.mpr hneg)

/-- **Completeness away from the origin.** For every fixed shift `a > 0`, RH holds if and only if
the Markov energy of `Φ(ω_a u)` is nonnegative for every even `u ∈ C²_c(ℝ)` vanishing on a
neighbourhood of the origin. The origin, where every folded supersolution fails, carries no zero
information. -/
theorem riemannHypothesis_iff_forall_vanishing_profile_markovEnergy_nonneg {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ (u : ℝ → ℝ) (ε : ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) → 0 < ε → (∀ x, |x| < ε → u x = 0) →
        0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  refine ⟨fun hRH u _ hu huc heven _ _ =>
    (riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg ha).mp hRH u hu huc heven,
    fun h => by_contra fun hRH => ?_⟩
  obtain ⟨u, ε, hu, huc, heven, hε, hvan, hneg⟩ :=
    exists_profile_vanishing_markovEnergy_neg_of_not_riemannHypothesis hRH ha
  exact absurd (h u ε hu huc heven hε hvan) (not_le.mpr hneg)

/-- RH holds if and only if the single-shift criterion holds at some shift, if and only if it holds
at every shift. -/
theorem riemannHypothesis_iff_exists_shift_markovEnergy_nonneg :
    RiemannHypothesis ↔ ∃ a : ℝ, 0 < a ∧ ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) →
        0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) :=
  ⟨fun hRH => ⟨1, one_pos,
      (riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg one_pos).mp hRH⟩,
    fun ⟨_, ha, h⟩ => (riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg ha).mpr h⟩

/-- **RH is the variation inequality at any single shift.** -/
theorem riemannHypothesis_iff_forall_variationInequality {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) →
        reflectedDifferenceEnergy (shiftedGroundState a) u ≤
          2 * sameSideEnergy (shiftedGroundState a) u +
            4 * Real.sinh (a / 2) *
              ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  rw [riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg ha]
  exact forall_congr' fun u => forall_congr' fun hu => forall_congr' fun huc =>
    forall_congr' fun heven => markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_variation ha hu
      huc heven

/-- **RH is the pole-free variation inequality at any single shift** (README frontier problem 1):
`D_a(u) ≤ 2 S_a(u) + V_a(u)` for every even `u ∈ C²_c(ℝ)`. -/
theorem riemannHypothesis_iff_forall_poleFreeVariationInequality {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) →
        reflectedDifferenceEnergy (shiftedGroundState a) u ≤
          2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  refine ⟨fun hRH u hu huc heven =>
    reflectedDifferenceEnergy_le_poleFree_of_riemannHypothesis hRH ha hu huc heven, fun h => ?_⟩
  rw [riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg ha]
  intro u hu huc heven
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_poleFree_add_eight_profileMoment_sq ha hu huc heven]
  nlinarith [h u hu huc heven, sq_nonneg (profileMoment a u)]

/-- **RH is the remainder-dominates-defect inequality at any single shift** (README frontier
problem 2): `4 ∫_{x>0} u² ω_a Φ (C_a − sinh(a/2) sinh(x/2)) ≤ R_N(ω_a, u)` for every even
`u ∈ C²_c(ℝ)`. -/
theorem riemannHypothesis_iff_forall_remainder_dominates_defect {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) →
        4 * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftedGroundState a x * riemannKernelReal x *
            (shiftedCollarMass a x - Real.sinh (a / 2) * Real.sinh (x / 2))) ≤
          groundRemainder (shiftedGroundState a) u := by
  rw [riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg ha]
  exact forall_congr' fun u => forall_congr' fun hu => forall_congr' fun huc =>
    forall_congr' fun heven => markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_of_contDiff ha hu
      huc heven

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
