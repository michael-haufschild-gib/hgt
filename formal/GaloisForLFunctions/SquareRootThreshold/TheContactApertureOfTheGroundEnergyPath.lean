import GaloisForLFunctions.SquareRootThreshold.TheRoutesMeasureOneAperture
import GaloisForLFunctions.SquareRootThreshold.TheRoutesMeasureOneZeroWidth
import GaloisForLFunctions.SquareRootThreshold.NearTopZerosForceNegativeGroundEnergyBeyondAnExplicitAperture

/-!
# The contact aperture of the ground-energy path

The ground-energy path `A ↦ μ(A)` of the restricted Weil operator is one function carrying the
units of three route clusters: its first sign change is the **contact aperture**, the unit of the
positivity routes; the rate at which it falls afterwards reads the **zero width**, the unit of the
prime-side and zero-side routes; and the zero that forces the contact is a **near-top zero**, the
object of the zero-indexed routes. This module defines the contact aperture and proves what the
corpus knows about it.

* **Two sets, one supremum.** The apertures with `μ(A) ≥ 0` (`groundEnergyNonnegApertures`) and
  the apertures with window positivity of the full zero form (`windowPositiveApertures`) are
  down-sets; the second is contained in the first, and every open aperture below a point of the
  first lies in the second. Both are unbounded iff RH
  (`riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures`,
  `riemannHypothesis_iff_not_bddAbove_windowPositiveApertures`); off RH they have the same
  supremum, the contact aperture `zetaContactAperture`
  (`zetaContactAperture_eq_sSup_windowPositiveApertures`).
* **The contact is a zero of the path.** Off RH, `μ(A) ≥ 0` below the contact aperture, `μ = 0` at
  it, and `μ(A) < 0` beyond it (`ccmRestrictedWeilGroundEnergy_nonneg_of_lt_contact`,
  `ccmRestrictedWeilGroundEnergy_contact_eq_zero`, `ccmRestrictedWeilGroundEnergy_neg_of_contact_lt`);
  every aperture below the contact is window positive (`zetaWindowPositive_of_lt_contact`).
* **Certificates and zeros bracket it.** The all-profile window through `3/10` gives
  `3/10 ≤ zetaContactAperture` (`threeTenths_le_zetaContactAperture`); a near-top zero `½ + z₀`
  with data `(w, η, V)` gives `zetaContactAperture ≤ V/2 + w`
  (`zetaContactAperture_le_of_near_top_zero`).
* **The fall of the path feeds every width reading.** A floor `μ(A) ≥ −Ce^{2σA}` at all large
  apertures gives `zetaZeroWidth ≤ σ` and hence every reading of the width: the regularized
  prime series converge right of `½ + σ`, the Wold energy is finite below radius `½ − σ`,
  Lagarias' criterion holds right of `½ + σ`, every cosine shift `h > σ` of `Ξ` is Laguerre–Pólya,
  every point right of `½ + σ` carries a recurrent disc, and every seam charge is at most
  `√2 log 2 sinh(σ log 2)` (`groundEnergyFloor_feeds_every_width_reading`).

What is not here is the converse of the last item (width to floor) and the contact law itself, the
relation between the contact aperture and the height and depth of the top zero.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### 1. The two aperture sets -/

/-- The apertures at which the restricted Weil ground energy is nonnegative. -/
def groundEnergyNonnegApertures : Set ℝ :=
  {A | ∃ h : 0 < A, 0 ≤ ccmRestrictedWeilGroundEnergy ⟨A, h⟩}

/-- The apertures at which the full zero form is window positive. -/
def windowPositiveApertures : Set ℝ := {A | 0 < A ∧ ZetaWindowPositive A}

theorem pos_of_mem_groundEnergyNonnegApertures {A : ℝ} (h : A ∈ groundEnergyNonnegApertures) :
    0 < A := h.1

theorem pos_of_mem_windowPositiveApertures {A : ℝ} (h : A ∈ windowPositiveApertures) : 0 < A :=
  h.1

/-- The ground-energy set is a down-set of `(0, ∞)`. -/
theorem mem_groundEnergyNonnegApertures_of_le {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hB : B ∈ groundEnergyNonnegApertures) : A ∈ groundEnergyNonnegApertures := by
  obtain ⟨hB0, hμ⟩ := hB
  exact ⟨hA, hμ.trans (ccmRestrictedWeilGroundEnergy_antitone (a := ⟨A, hA⟩) (b := ⟨B, hB0⟩) hAB)⟩

/-- The window set is a down-set of `(0, ∞)`. -/
theorem mem_windowPositiveApertures_of_le {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hB : B ∈ windowPositiveApertures) : A ∈ windowPositiveApertures :=
  ⟨hA, zetaWindowPositive_antitone hAB hB.2⟩

/-- Window positivity at an aperture gives a nonnegative ground energy there. -/
theorem windowPositiveApertures_subset : windowPositiveApertures ⊆ groundEnergyNonnegApertures :=
  fun A hA => ⟨hA.1, ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive ⟨A, hA.1⟩ hA.2⟩

/-- A nonnegative ground energy at `A` gives window positivity at every smaller aperture. -/
theorem Ioo_subset_windowPositiveApertures {A : ℝ} (hA : A ∈ groundEnergyNonnegApertures) :
    Ioo 0 A ⊆ windowPositiveApertures := by
  obtain ⟨hA0, hμ⟩ := hA
  intro B hB
  exact ⟨hB.1, zetaWindowPositive_of_ccmRestrictedWeilGroundEnergy_nonneg (A := ⟨A, hA0⟩) hB.2 hμ⟩

/-- The all-profile certificate: `3/10` is a nonnegative-ground-energy aperture. -/
theorem threeTenths_mem_groundEnergyNonnegApertures :
    (3 / 10 : ℝ) ∈ groundEnergyNonnegApertures :=
  ⟨by norm_num, le_trans (by norm_num)
    (one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths (A := ⟨3 / 10, by norm_num⟩) le_rfl)⟩

/-- The all-profile certificate: `3/10` is a window-positive aperture. -/
theorem threeTenths_mem_windowPositiveApertures : (3 / 10 : ℝ) ∈ windowPositiveApertures :=
  ⟨by norm_num, fun F hF hFc hv =>
    le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (fullZeroForm_ge_of_support_le_threeTenths hF hFc hv)⟩

theorem groundEnergyNonnegApertures_nonempty : groundEnergyNonnegApertures.Nonempty :=
  ⟨_, threeTenths_mem_groundEnergyNonnegApertures⟩

theorem windowPositiveApertures_nonempty : windowPositiveApertures.Nonempty :=
  ⟨_, threeTenths_mem_windowPositiveApertures⟩

/-! ### 2. RH is the unboundedness of either set -/

/-- **RH iff the ground energy is nonnegative at unboundedly large apertures.** -/
theorem riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures :
    RiemannHypothesis ↔ ¬ BddAbove groundEnergyNonnegApertures := by
  constructor
  · intro hRH ⟨M, hM⟩
    have hmem : max M 0 + 1 ∈ groundEnergyNonnegApertures :=
      ⟨by linarith [le_max_right M 0], ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH _⟩
    linarith [hM hmem, le_max_left M 0]
  · intro h
    rw [riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg]
    intro A
    obtain ⟨B, hB, hAB⟩ : ∃ B ∈ groundEnergyNonnegApertures, A.1 ≤ B := by
      by_contra hcon
      exact h ⟨A.1, fun B hB => le_of_not_ge fun hge => hcon ⟨B, hB, hge⟩⟩
    exact (mem_groundEnergyNonnegApertures_of_le A.2 hAB hB).2

/-- **RH iff window positivity holds at unboundedly large apertures.** -/
theorem riemannHypothesis_iff_not_bddAbove_windowPositiveApertures :
    RiemannHypothesis ↔ ¬ BddAbove windowPositiveApertures := by
  rw [riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures]
  constructor
  · intro h ⟨M, hM⟩
    refine h ⟨M, fun A hA => ?_⟩
    by_contra hlt
    have hlt' : M < A := not_le.mp hlt
    have h0 := pos_of_mem_groundEnergyNonnegApertures hA
    have hmaxlt : max M 0 < A := max_lt hlt' h0
    have hmid : (max M 0 + A) / 2 ∈ windowPositiveApertures :=
      Ioo_subset_windowPositiveApertures hA
        ⟨by linarith [le_max_right M 0], by linarith⟩
    linarith [hM hmid, le_max_left M 0]
  · intro h hb
    exact h (hb.mono windowPositiveApertures_subset)

/-! ### 3. The contact aperture -/

/-- The contact aperture: the supremum of the apertures with nonnegative ground energy. Off RH it
is the first zero of the ground-energy path; under RH the set is unbounded. -/
def zetaContactAperture : ℝ := sSup groundEnergyNonnegApertures

theorem bddAbove_groundEnergyNonnegApertures_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    BddAbove groundEnergyNonnegApertures := by
  by_contra h
  exact hRH (riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures.mpr h)

theorem bddAbove_windowPositiveApertures_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    BddAbove windowPositiveApertures := by
  by_contra h
  exact hRH (riemannHypothesis_iff_not_bddAbove_windowPositiveApertures.mpr h)

/-- **Off RH the two aperture sets have the same supremum.** -/
theorem zetaContactAperture_eq_sSup_windowPositiveApertures (hRH : ¬ RiemannHypothesis) :
    zetaContactAperture = sSup windowPositiveApertures := by
  have hS := bddAbove_groundEnergyNonnegApertures_of_not_riemannHypothesis hRH
  have hW := bddAbove_windowPositiveApertures_of_not_riemannHypothesis hRH
  apply le_antisymm
  · refine csSup_le groundEnergyNonnegApertures_nonempty fun A hA => ?_
    have hsub := Ioo_subset_windowPositiveApertures hA
    have h0 := pos_of_mem_groundEnergyNonnegApertures hA
    calc A = sSup (Ioo (0 : ℝ) A) := (csSup_Ioo h0).symm
      _ ≤ sSup windowPositiveApertures :=
        csSup_le_csSup hW ⟨A / 2, by constructor <;> linarith⟩ hsub
  · exact csSup_le_csSup hS windowPositiveApertures_nonempty windowPositiveApertures_subset

/-- **The certified aperture bounds the contact aperture from below.** -/
theorem threeTenths_le_zetaContactAperture (hRH : ¬ RiemannHypothesis) :
    (3 / 10 : ℝ) ≤ zetaContactAperture :=
  le_csSup (bddAbove_groundEnergyNonnegApertures_of_not_riemannHypothesis hRH)
    threeTenths_mem_groundEnergyNonnegApertures

theorem zetaContactAperture_pos (hRH : ¬ RiemannHypothesis) : 0 < zetaContactAperture :=
  lt_of_lt_of_le (by norm_num) (threeTenths_le_zetaContactAperture hRH)

/-- **Below the contact the path is nonnegative.** -/
theorem ccmRestrictedWeilGroundEnergy_nonneg_of_lt_contact
    {A : SuzukiPositiveAperture} (h : A.1 < zetaContactAperture) :
    0 ≤ ccmRestrictedWeilGroundEnergy A := by
  obtain ⟨B, hB, hAB⟩ := exists_lt_of_lt_csSup groundEnergyNonnegApertures_nonempty h
  exact (mem_groundEnergyNonnegApertures_of_le A.2 hAB.le hB).2

/-- **Beyond the contact the path is negative.** -/
theorem ccmRestrictedWeilGroundEnergy_neg_of_contact_lt (hRH : ¬ RiemannHypothesis)
    {A : SuzukiPositiveAperture} (h : zetaContactAperture < A.1) :
    ccmRestrictedWeilGroundEnergy A < 0 := by
  by_contra hcon
  have hmem : A.1 ∈ groundEnergyNonnegApertures := ⟨A.2, not_lt.mp hcon⟩
  exact absurd (le_csSup (bddAbove_groundEnergyNonnegApertures_of_not_riemannHypothesis hRH) hmem)
    (not_le.mpr h)

/-- **Every aperture below the contact is window positive.** -/
theorem zetaWindowPositive_of_lt_contact {A : ℝ} (h0 : 0 < A)
    (h : A < zetaContactAperture) : ZetaWindowPositive A := by
  obtain ⟨B, hB, hAB⟩ := exists_lt_of_lt_csSup groundEnergyNonnegApertures_nonempty h
  exact (Ioo_subset_windowPositiveApertures hB ⟨h0, hAB⟩).2

/-- **The contact is a zero of the path**: continuity of `μ` joins the nonnegative side below
and the negative side above. -/
theorem ccmRestrictedWeilGroundEnergy_contact_eq_zero (hRH : ¬ RiemannHypothesis) :
    ccmRestrictedWeilGroundEnergy ⟨zetaContactAperture, zetaContactAperture_pos hRH⟩ = 0 := by
  set c : SuzukiPositiveAperture := ⟨zetaContactAperture, zetaContactAperture_pos hRH⟩ with hc
  have hcont := continuous_ccmRestrictedWeilGroundEnergy.tendsto c
  apply le_antisymm
  · -- approach from above: `μ(c + 1/(n+1)) < 0`
    let a : ℕ → SuzukiPositiveAperture := fun n =>
      ⟨zetaContactAperture + 1 / ((n : ℝ) + 1), by
        linarith [zetaContactAperture_pos hRH, (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]⟩
    have hT : Tendsto a atTop (𝓝 c) := by
      rw [tendsto_subtype_rng]
      have h1 : Tendsto (fun n : ℕ => zetaContactAperture + 1 / ((n : ℝ) + 1)) atTop
          (𝓝 (zetaContactAperture + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h1
      exact h1
    refine le_of_tendsto' (hcont.comp hT) fun n => ?_
    exact (ccmRestrictedWeilGroundEnergy_neg_of_contact_lt hRH (A := a n)
      (by show zetaContactAperture < zetaContactAperture + 1 / ((n : ℝ) + 1); linarith
        [(by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))])).le
  · -- approach from below inside the set
    obtain ⟨u, -, hu, humem⟩ := exists_seq_tendsto_sSup groundEnergyNonnegApertures_nonempty
      (bddAbove_groundEnergyNonnegApertures_of_not_riemannHypothesis hRH)
    let a : ℕ → SuzukiPositiveAperture := fun n => ⟨u n, (humem n).1⟩
    have hT : Tendsto a atTop (𝓝 c) := by
      rw [tendsto_subtype_rng]
      exact hu
    exact ge_of_tendsto' (hcont.comp hT) fun n => (humem n).2

/-- **A near-top zero bounds the contact aperture from above** by half its visibility lag plus
the width of the difference test. -/
theorem zetaContactAperture_le_of_near_top_zero {w : ℝ} (hw : 0 < w)
    {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : oneParamLag w η z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    zetaContactAperture ≤ V / 2 + w := by
  refine csSup_le groundEnergyNonnegApertures_nonempty fun A hA => ?_
  obtain ⟨hA0, hμ⟩ := hA
  exact (lt_of_ccmRestrictedWeilGroundEnergy_nonneg_of_near_top_zero hw hz₀ hre₀ hη hηle hV htop
    (A := ⟨A, hA0⟩) hμ).le

/-! ### 4. The fall of the path feeds every width reading -/

/-- **A ground-energy floor at rate `2σ` is every width reading at rate `σ`.** -/
theorem groundEnergyFloor_feeds_every_width_reading {σ C A₀ : ℝ} (hσ : 0 ≤ σ)
    (hμ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A) :
    zetaZeroWidth ≤ σ ∧
    ConvergesRightOf logZetaRegCoeff (1 / 2 + σ) ∧
    (σ < 1 / 2 → ∀ t : ℝ, 0 < t → t < 1 / 2 - σ → WoldNatResidualSquareEnergy t) ∧
    (∀ s : ℂ, 1 / 2 + σ < s.re → xi s ≠ 0 → 0 ≤ (logDeriv xi s).re) ∧
    (∀ h : ℝ, σ < h →
      GaloisForLFunctions.HTGeometry.LaguerrePolya
        (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2)) ∧
    (∀ z : ℂ, 1 / 2 + σ < z.re → z.re < 1 →
      ∃ r > 0, ZetaDiscStronglyRecurrentOn (Metric.closedBall z r)) := by
  have hw : zetaZeroWidth ≤ σ := zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hμ
  refine ⟨hw, (zetaZeroWidth_le_iff_logZetaRegCoeff_converges hσ).mp hw, fun hσ' =>
    (zetaZeroWidth_le_iff_forall_woldNatResidualSquareEnergy hσ hσ').mp hw,
    fun s hs hxi => re_logDeriv_xi_nonneg_of_zetaZeroWidth_le hw hs hxi,
    fun h hh => laguerrePolya_cosineShiftXi_of_zetaZeroWidth_lt (lt_of_le_of_lt hw hh),
    (zetaZeroWidth_le_iff_forall_exists_zetaDiscStronglyRecurrentOn hσ).mp hw⟩

/-- **The contact aperture carries the units of the positivity routes.** Off RH: the apertures
with nonnegative ground energy and the window-positive apertures have one supremum; the path is
nonnegative below it, zero at it and negative beyond it; it is at least `3/10` and at most
`V/2 + w` for every near-top zero. -/
theorem theContactApertureOfTheGroundEnergyPath (hRH : ¬ RiemannHypothesis) :
    zetaContactAperture = sSup windowPositiveApertures ∧
    (3 / 10 : ℝ) ≤ zetaContactAperture ∧
    (∀ A : SuzukiPositiveAperture, A.1 < zetaContactAperture →
      0 ≤ ccmRestrictedWeilGroundEnergy A) ∧
    ccmRestrictedWeilGroundEnergy ⟨zetaContactAperture, zetaContactAperture_pos hRH⟩ = 0 ∧
    (∀ A : SuzukiPositiveAperture, zetaContactAperture < A.1 →
      ccmRestrictedWeilGroundEnergy A < 0) ∧
    (∀ A : ℝ, 0 < A → A < zetaContactAperture → ZetaWindowPositive A) :=
  ⟨zetaContactAperture_eq_sSup_windowPositiveApertures hRH, threeTenths_le_zetaContactAperture hRH,
    fun _ h => ccmRestrictedWeilGroundEnergy_nonneg_of_lt_contact h,
    ccmRestrictedWeilGroundEnergy_contact_eq_zero hRH,
    fun _ h => ccmRestrictedWeilGroundEnergy_neg_of_contact_lt hRH h,
    fun _ h0 h => zetaWindowPositive_of_lt_contact h0 h⟩

end GaloisForLFunctions.SquareRootThreshold

end
