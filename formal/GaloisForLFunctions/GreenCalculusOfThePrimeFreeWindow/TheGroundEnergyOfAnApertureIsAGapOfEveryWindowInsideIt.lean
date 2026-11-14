import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheBoundRangeEndsOnlyWhereTheGapOfTheBoundWindowsCloses
import GaloisForLFunctions.WindowTowerOfSpecZ.TheOddWeilFormHasAFloorAtAperture1881Over5000

/-!
# The ground energy of an aperture is a gap of every window inside it

A window `(R, R + J]` is an interval of length `log((R + J)/R)` in the logarithmic coordinate
and its step packets are tests of Weil's form. A floor of Weil's form on the smooth tests of an
aperture therefore passes to the window matrices, at every block size, as a gap.

* **Floor to ground energy** (`WeilFloor.le_groundEnergy`): a floor `c` of Weil's form on the
  real `C²` tests supported in `[−A, A]` is a lower bound for the ground energy of the aperture
  `A`. Weil's form splits by parity, so the floor is needed on the even and on the odd tests
  only (`WeilFloor.of_even_of_odd`).
* **Ground energy to gap** (`hasGap_neutralWindow_of_le_groundEnergy`): the ground energy of an
  aperture `A` is a gap of the neutral part of every window with `log((R + J)/R) < 2A`, at
  every block size and for every cutoff `Q` with `R + J < (Q + 1) R`: the neutral part is at
  least this energy on the charge-free packets. Where the ground energy is nonnegative the
  window has one bound state (`hermNegIndex_neutralWindow_eq_one_of_groundEnergy_nonneg`).
* **The first step.** The windows `(R, 2(R + a) + b]` with `a ≤ 3R/100`, `b ≤ 3(R + a)/50` have
  ratio at most `10609/5000`, and `log(10609/5000) < 2 · 1881/5000`
  (`log_window_lt_of_firstStep`). On the odd tests of the aperture `1881/5000` Weil's form has
  the floor `1/2000` (`oddWeilFloor_firstStep`). So a floor `c ≤ 1/2000` on the even tests of
  this aperture is a gap `c` of every window of ratio at most `10609/5000`
  (`hasGap_neutralWindow_of_even_floor`), and nonnegativity on the even tests is one bound state
  of these windows (`hermNegIndex_neutralWindow_eq_one_of_even_nonneg`), at every block size and
  for every cutoff `Q ≥ 2`.
* **The excess of a step** (`overlapSchur_form_ge_of_floor`,
  `greenForm_add_excess_le_of_floor`): a floor `c ≥ 0` of a window on its charge-free packets is
  the excess of its overlap step, `B G₊ Bᵀ + c ⪯ N_e + (Bφ)(Bφ)ᵀ/μ` on the two ends. At the
  first step the excess is the floor of the even sector (`greenForm_firstStep_of_even_floor`).

* **The sign gives the gap.** The ground energy decreases strictly with the aperture, so
  strictly inside a nonnegative aperture it is positive (`groundEnergy_pos_of_lt_of_nonneg`).
  Nonnegativity on the even tests of the aperture `1881/5000` is a common positive gap of the
  windows of ratio at most `10609/5000` (`exists_gap_firstStep_of_even_nonneg`).
* **The a priori gap is the Riemann hypothesis**
  (`riemannHypothesis_iff_exists_gap_neutralWindow`,
  `riemannHypothesis_iff_gap_of_bound_windows`): it holds iff at every cutoff the windows have a
  common positive gap, and iff the windows with exactly one bound state have one. The
  continuity method loses nothing.

The parity of a test is not a symmetry of the step packets of a window: the split is made on the
smooth tests, before the passage to the matrices.
-/

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Floors of Weil's form on an aperture -/

section Continuum

open MeasureTheory
open _root_.Zeta23 _root_.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis

/-- Weil's form is at least `c` times the mass on the real `C²` tests supported in `[−A, A]`. -/
def WeilFloor (A c : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → tsupport F ⊆ Set.Icc (-A) A → c * ∫ x, F x ^ 2 ≤ weilQuad F

/-- The floor `c` of Weil's form on the even tests of the aperture `A`. -/
def EvenWeilFloor (A c : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → tsupport F ⊆ Set.Icc (-A) A → (∀ x, F (-x) = F x) →
    c * ∫ x, F x ^ 2 ≤ weilQuad F

/-- The floor `c` of Weil's form on the odd tests of the aperture `A`. -/
def OddWeilFloor (A c : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → tsupport F ⊆ Set.Icc (-A) A → (∀ x, F (-x) = -F x) →
    c * ∫ x, F x ^ 2 ≤ weilQuad F

theorem OddWeilFloor.mono {A c c' : ℝ} (h : OddWeilFloor A c) (hc : c' ≤ c) :
    OddWeilFloor A c' := fun F hF hs ho =>
  (mul_le_mul_of_nonneg_right hc (integral_nonneg fun x => sq_nonneg (F x))).trans (h F hF hs ho)

/-- Nonnegativity of Weil's form on the even tests is the floor `0`. -/
theorem evenWeilFloor_zero_iff {A : ℝ} :
    EvenWeilFloor A 0 ↔ ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → tsupport F ⊆ Set.Icc (-A) A →
      (∀ x, F (-x) = F x) → 0 ≤ weilQuad F := by
  simp only [EvenWeilFloor, zero_mul]

/-- A function that vanishes off `[−A, A]` has its support there. -/
theorem tsupport_subset_Icc_of_forall_eq_zero {F : ℝ → ℝ} {A : ℝ}
    (h : ∀ x, A < |x| → F x = 0) : tsupport F ⊆ Set.Icc (-A) A :=
  closure_minimal (fun x hx => by
    by_contra hmem
    refine hx (h x ?_)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
    rcases hmem with h1 | h1
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
    · exact lt_of_lt_of_le h1 (le_abs_self x)) isClosed_Icc

theorem eq_zero_of_abs_gt_of_tsupport_subset {F : ℝ → ℝ} {A : ℝ}
    (hs : tsupport F ⊆ Set.Icc (-A) A) {x : ℝ} (hx : A < |x|) : F x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem =>
    absurd (abs_le.mpr (Set.mem_Icc.mp (hs hmem))) (not_le.mpr hx)

/-- Weil's form of a real test is its full zero form. -/
private theorem fullZeroForm_eq_weilQuad {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) : fullZeroForm F = weilQuad F :=
  fullZeroForm_eq_re_weilFullFunctional hF hFc

/-- **The parity split of a floor.** Weil's form and the mass are the sums of their values on
the even and on the odd part of a test, so a floor on the even tests and on the odd tests of an
aperture is a floor on all its tests. -/
theorem WeilFloor.of_even_of_odd {A c : ℝ} (he : EvenWeilFloor A c) (ho : OddWeilFloor A c) :
    WeilFloor A c := by
  intro F hF hs
  have hFc : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport F).trans hs)
  have hz : ∀ x, A < |x| → F x = 0 := fun x hx => eq_zero_of_abs_gt_of_tsupport_subset hs hx
  have hse : ∀ x, A < |x| → evenPartReal F x = 0 := fun x hx => by
    unfold evenPartReal
    rw [hz x hx, hz (-x) (by rwa [abs_neg])]
    norm_num
  have hso : ∀ x, A < |x| → oddPartReal F x = 0 := fun x hx => by
    unfold oddPartReal
    rw [hz x hx, hz (-x) (by rwa [abs_neg])]
    norm_num
  have hFe := contDiff_evenPartReal hF
  have hFo := contDiff_oddPartReal hF
  have h1 := he _ hFe (tsupport_subset_Icc_of_forall_eq_zero hse) (evenPartReal_neg F)
  have h2 := ho _ hFo (tsupport_subset_Icc_of_forall_eq_zero hso) (oddPartReal_neg F)
  rw [← fullZeroForm_eq_weilQuad hFe.continuous (hasCompactSupport_evenPartReal hFc)] at h1
  rw [← fullZeroForm_eq_weilQuad hFo.continuous (hasCompactSupport_oddPartReal hFc)] at h2
  rw [← fullZeroForm_eq_weilQuad hF.continuous hFc, fullZeroForm_eq_even_add_odd hF hFc,
    integral_sq_eq_even_add_odd hF.continuous hFc]
  linarith

/-- **A floor of Weil's form on the tests of an aperture is a lower bound for its ground
energy**: the ground energy is the infimum of the Rayleigh quotient over the smooth tests
supported inside the aperture. -/
theorem WeilFloor.le_groundEnergy {A : SuzukiPositiveAperture} {c : ℝ} (h : WeilFloor A.1 c) :
    c ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, hu, rfl⟩
  have hnorm : ‖suzukiWeilIntervalFormEmbedding A u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ := by
    change ‖suzukiPhysicalToApertureCLM A (ccmArchimedeanFormToAperture A u.toCCMFormVector)‖ = _
    exact (suzukiApertureL2Equiv A).symm.norm_map _
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, ‖u x‖ ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [hnorm, norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector]
  have hpos : 0 < suzukiWeilIntervalFormMass A u.toCCMFormVector :=
    pow_pos (norm_pos_iff.mpr hu) 2
  unfold suzukiWeilIntervalFormRayleigh
  rw [le_div_iff₀ hpos, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hmass]
  have hsupp : tsupport (u : ℝ → ℂ) ⊆ Set.Icc (-A.1) A.1 :=
    u.tsupport_subset.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact zetaZeroConfig_re_W_ge_of_window
    (fun F hF hFc hs => by
      rw [fullZeroForm_eq_weilQuad hF.continuous hFc]
      exact h F hF (tsupport_subset_Icc_of_forall_eq_zero hs))
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsupp

/-- **On the odd tests of the aperture `1881/5000` Weil's form has the floor `1/2000`.** -/
theorem oddWeilFloor_firstStep : OddWeilFloor (1881 / 5000) (1 / 2000) :=
  fun _ hF hs ho => WindowTowerOfSpecZ.weilQuad_ge_odd_at_aperture_1881_over_5000 hF hs ho

end Continuum

/-! ### From the aperture to the windows -/

section Windows

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- **Weil's form on the step packets of a window is at least the ground energy of every
aperture wider than half its logarithmic length**, at every block size. -/
theorem groundEnergy_mul_le_packetForm_stepPacket {R J Q : ℕ} (hR : 1 ≤ R)
    {A : _root_.RHTower.SuzukiPositiveAperture}
    (hA : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A.1) (hQ : R + J < (Q + 1) * R)
    (σ : ℕ → ℝ) :
    _root_.RHTower.ccmRestrictedWeilGroundEnergy A * ∑ j ∈ range J, σ j ^ 2 ≤
      packetForm Q (stepPacket R J σ) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hlogQ : Real.log ((R + J : ℕ) : ℝ) - Real.log R < Real.log ((Q : ℝ) + 1) := by
    have hpos : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
    have hlt : ((R + J : ℕ) : ℝ) < ((Q : ℝ) + 1) * R := by exact_mod_cast hQ
    have h1 := Real.log_lt_log hpos hlt
    rw [Real.log_mul (by positivity) hR'.ne'] at h1
    linarith
  rw [← packetAutocorr_stepPacket_zero hR J σ]
  simp only [stepPacket_eq_nested hR J σ]
  exact groundEnergy_mul_nested_mass_le_packetForm_of_log_lt hR (nested_bounds R J)
    (nestedCoeff J σ) hA hlogQ

/-- **The ground energy of an aperture is a floor of every window inside it on its charge-free
packets.** If `log((R + J)/R) < 2A` and `c` is at most the ground energy of the aperture `A`,
the neutral part of `(R, R + J]` is at least `c` on the packets of charge zero: there it is
Weil's form of a step packet. -/
theorem neutralWindow_floor_of_le_groundEnergy {R J Q : ℕ} (hR : 1 ≤ R)
    {A : _root_.RHTower.SuzukiPositiveAperture}
    (hA : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A.1) (hQ : R + J < (Q + 1) * R)
    {c : ℝ} (hc : c ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy A) (z : Fin J → ℝ)
    (hz : ∑ i, z i = 0) : c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z) := by
  rw [AbsoluteGeometryOfSpecZ.dotProduct_mulVec_eq_sum, neutralWindow, sum_fin_windowMatrix_eq,
    dotProduct_self_eq_sum_range_extendFin,
    sum_neutralBlock_eq_of_charge_zero
      (Or.inl ((sum_fin_eq_sum_range_extendFin z).symm.trans hz)),
    ← packetForm_stepPacket_eq_sum_blockMatrix hR Q J (extendFin z)]
  exact (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun j _ => sq_nonneg _)).trans
    (groundEnergy_mul_le_packetForm_stepPacket hR hA hQ _)

/-- **The ground energy of an aperture is a gap of every window inside it**, at every block
size. -/
theorem hasGap_neutralWindow_of_le_groundEnergy {R J Q : ℕ} (hR : 1 ≤ R)
    {A : _root_.RHTower.SuzukiPositiveAperture}
    (hA : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A.1) (hQ : R + J < (Q + 1) * R)
    {c : ℝ} (hc : c ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy A) :
    HasGap (neutralWindow Q R J) c :=
  ⟨fun _ => 1, fun y hy => neutralWindow_floor_of_le_groundEnergy hR hA hQ hc y
    (by simpa only [dotProduct, one_mul] using hy)⟩

/-- A floor of Weil's form on an aperture is a gap of every window inside it. -/
theorem WeilFloor.hasGap_neutralWindow {A c : ℝ} (hA0 : 0 < A) (h : WeilFloor A c)
    {R J Q : ℕ} (hR : 1 ≤ R) (hA : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A)
    (hQ : R + J < (Q + 1) * R) : HasGap (neutralWindow Q R J) c :=
  hasGap_neutralWindow_of_le_groundEnergy (A := ⟨A, hA0⟩) hR hA hQ
    (WeilFloor.le_groundEnergy (A := ⟨A, hA0⟩) h)

/-- **Where the ground energy of an aperture is nonnegative, every window inside it has one
bound state**, at every block size. -/
theorem hermNegIndex_neutralWindow_eq_one_of_groundEnergy_nonneg {R J Q : ℕ} (hR : 1 ≤ R)
    (hRJ : R ≤ J) {A : _root_.RHTower.SuzukiPositiveAperture}
    (hA : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A.1) (hQ : R + J < (Q + 1) * R)
    (h0 : 0 ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy A) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 :=
  hermNegIndex_neutralWindow_eq_one_of_hasGap hR hRJ le_rfl
    (hasGap_neutralWindow_of_le_groundEnergy hR hA hQ h0)

/-! ### The excess of a step -/

/-- **A floor of a window on its charge-free packets is an excess of its overlap step.** If
the neutral part of `(R, 2(R + a) + b]` is at least `c ≥ 0` on the packets of charge zero, the
Schur complement of its dyadic middle is at least `c` on the two ends: the charge of the ends
is cancelled on the ground vector of the middle. -/
theorem overlapSchur_form_ge_of_floor {Q R a b : ℕ} (hD : 1 ≤ R + a) {c : ℝ} (hc : 0 ≤ c)
    (hfloor : ∀ z : Fin (a + (R + a) + b) → ℝ, ∑ i, z i = 0 →
      c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R (a + (R + a) + b) *ᵥ z))
    (e : Fin a ⊕ Fin b → ℝ) : c * (e ⬝ᵥ e) ≤ e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) := by
  have h := schur_floor_of_charge_cancellation (oneBoundState_primeFreeMiddle hD)
    (endCoupling Q R a b) (endForm Q R a b) (fun _ => (1 : ℝ))
    (charge_groundVector_ne_zero hD) hc
    (fun y hy => by
      have h1 := floor_submatrix_equiv hfloor (overlapEquiv a (R + a) b) y hy
      rw [neutralWindow_submatrix_overlapEquiv, overlapWhole, neutralWindow_dyadic_eq] at h1
      exact h1)
    e
  exact h

/-- **The excess of a step in Green form**: with the floor `c ≥ 0` of the window on its
charge-free packets, the attraction through the positive part of the Green matrix of the
middle, plus `c` times the mass of the ends, is at most the neutral form of the ends plus the
repulsion through the bound state of the middle. -/
theorem greenForm_add_excess_le_of_floor {Q R a b : ℕ} (hD : 1 ≤ R + a) {c : ℝ} (hc : 0 ≤ c)
    (hfloor : ∀ z : Fin (a + (R + a) + b) → ℝ, ∑ i, z i = 0 →
      c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R (a + (R + a) + b) *ᵥ z))
    (e : Fin a ⊕ Fin b → ℝ) :
    (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) +
        c * (e ⬝ᵥ e) ≤
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) := by
  have h := overlapSchur_form_ge_of_floor hD hc hfloor e
  rw [overlapSchur_form_eq_channels Q R a b hD e] at h
  linarith

/-! ### The first step -/

/-- A window of ratio at most `10609/5000` is shorter than `2 · 0.37618` in the logarithmic
coordinate: `log 2 + 32 log(1.00185) < 0.69315 + 0.0592`. -/
theorem log_window_lt_of_firstStep' {R J : ℕ} (hR : 1 ≤ R) (hJ : 5000 * (R + J) ≤ 10609 * R) :
    Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * (37618 / 100000) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hle : ((R + J : ℕ) : ℝ) ≤ 2 * (10609 / 10000) * R := by
    have h : (5000 : ℝ) * ((R + J : ℕ) : ℝ) ≤ 10609 * R := by exact_mod_cast hJ
    linarith
  have hpos : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
  have h1 := Real.log_le_log hpos hle
  rw [Real.log_mul (by norm_num) hR'.ne', Real.log_mul (by norm_num) (by norm_num)] at h1
  have h3 : Real.log (10609 / 10000 : ℝ) ≤ 32 * (100185 / 100000 - 1) := by
    have hpow : (10609 / 10000 : ℝ) ≤ (100185 / 100000) ^ 32 := by norm_num
    have h := Real.log_le_log (by norm_num) hpow
    rw [Real.log_pow] at h
    have h' := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100185 / 100000)
    push_cast at h
    linarith
  have h4 := Real.log_two_lt_d9
  linarith

/-- A window of ratio at most `10609/5000` lies inside the aperture `1881/5000`. -/
theorem log_window_lt_of_firstStep {R J : ℕ} (hR : 1 ≤ R) (hJ : 5000 * (R + J) ≤ 10609 * R) :
    Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * (1881 / 5000) := by
  have h := log_window_lt_of_firstStep' hR hJ
  linarith

/-- **A floor of the even sector at the aperture `1881/5000` is a floor of every window of
ratio at most `10609/5000` on its charge-free packets**, at every block size and for every
cutoff `Q ≥ 2`: the odd sector has the floor `1/2000`. -/
theorem neutralWindow_floor_of_even_floor {c : ℝ} (hc : c ≤ 1 / 2000)
    (heven : EvenWeilFloor (1881 / 5000) c) {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hJ : 5000 * (R + J) ≤ 10609 * R) (z : Fin J → ℝ) (hz : ∑ i, z i = 0) :
    c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z) :=
  neutralWindow_floor_of_le_groundEnergy (A := ⟨1881 / 5000, by norm_num⟩) hR
    (log_window_lt_of_firstStep hR hJ)
    (lt_of_lt_of_le (by omega : R + J < 3 * R) (Nat.mul_le_mul_right R (by omega)))
    (WeilFloor.le_groundEnergy (A := ⟨1881 / 5000, by norm_num⟩)
      (WeilFloor.of_even_of_odd heven (oddWeilFloor_firstStep.mono hc))) z hz

/-- A floor of the even sector at the aperture `1881/5000` is a gap of every window of ratio at
most `10609/5000`. -/
theorem hasGap_neutralWindow_of_even_floor {c : ℝ} (hc : c ≤ 1 / 2000)
    (heven : EvenWeilFloor (1881 / 5000) c) {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hJ : 5000 * (R + J) ≤ 10609 * R) : HasGap (neutralWindow Q R J) c :=
  ⟨fun _ => 1, fun y hy => neutralWindow_floor_of_even_floor hc heven hQ hR hJ y
    (by simpa only [dotProduct, one_mul] using hy)⟩

/-- **The first step from the even sector at one aperture.** If Weil's form is
nonnegative on the even tests supported in `[−1881/5000, 1881/5000]`, every window of ratio at
most `10609/5000` has one bound state, at every block size and for every cutoff `Q ≥ 2`. -/
theorem hermNegIndex_neutralWindow_eq_one_of_even_nonneg
    (heven : EvenWeilFloor (1881 / 5000) 0) {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hRJ : R ≤ J) (hJ : 5000 * (R + J) ≤ 10609 * R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 :=
  hermNegIndex_neutralWindow_eq_one_of_hasGap hR hRJ le_rfl
    (hasGap_neutralWindow_of_even_floor (by norm_num) heven hQ hR hJ)

/-- **The first step in Green form, with its excess, from the even sector.** If Weil's form has
the floor `c`, `0 ≤ c ≤ 1/2000`, on the even tests of the aperture `1881/5000`, then on the two
ends of every window `(R, 2(R + a) + b]` with `a ≤ 3R/100`, `b ≤ 3(R + a)/50` the attraction
through the positive part of the Green matrix of the dyadic middle, plus `c` times the mass of
the ends, is at most the neutral form of the ends plus the repulsion through the bound state
of the middle. -/
theorem greenForm_firstStep_of_even_floor {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2000)
    (heven : EvenWeilFloor (1881 / 5000) c) {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) (e : Fin a ⊕ Fin b → ℝ) :
    (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) +
        c * (e ⬝ᵥ e) ≤
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) :=
  greenForm_add_excess_le_of_floor (by omega) hc0
    (neutralWindow_floor_of_even_floor hc heven hQ hR (by omega)) e

/-! ### The sign gives the gap -/

/-- **Strictly inside a nonnegative aperture the ground energy is positive**: it decreases
strictly with the aperture. -/
theorem groundEnergy_pos_of_lt_of_nonneg {A' A : _root_.RHTower.SuzukiPositiveAperture}
    (hlt : A' < A) (h0 : 0 ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy A) :
    0 < _root_.RHTower.ccmRestrictedWeilGroundEnergy A' :=
  lt_of_le_of_lt h0
    (ArithmeticContinuationAndCriticalEnergy.strictAnti_ccmRestrictedWeilGroundEnergy hlt)

/-- **At the first step the sign gives the gap.** If Weil's form is nonnegative on the even
tests of the aperture `1881/5000`, the windows of ratio at most `10609/5000` have a common
positive gap, at every block size and for every cutoff `Q ≥ 2`: they lie inside the smaller
aperture `0.37618`, whose ground energy is positive. -/
theorem exists_gap_firstStep_of_even_nonneg (heven : EvenWeilFloor (1881 / 5000) 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ Q R J : ℕ, 2 ≤ Q → 1 ≤ R → 5000 * (R + J) ≤ 10609 * R →
      HasGap (neutralWindow Q R J) c := by
  let A : _root_.RHTower.SuzukiPositiveAperture := ⟨1881 / 5000, by norm_num⟩
  let A' : _root_.RHTower.SuzukiPositiveAperture := ⟨37618 / 100000, by norm_num⟩
  have h0 : 0 ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy A :=
    WeilFloor.le_groundEnergy (A := A)
      (WeilFloor.of_even_of_odd heven (oddWeilFloor_firstStep.mono (by norm_num)))
  have hlt : A' < A := by
    change (37618 / 100000 : ℝ) < 1881 / 5000
    norm_num
  refine ⟨_, groundEnergy_pos_of_lt_of_nonneg hlt h0, fun Q R J hQ hR hJ => ?_⟩
  exact hasGap_neutralWindow_of_le_groundEnergy (A := A') hR (log_window_lt_of_firstStep' hR hJ)
    (lt_of_lt_of_le (by omega : R + J < 3 * R) (Nat.mul_le_mul_right R (by omega))) le_rfl

/-! ### The a priori gap is the Riemann hypothesis -/

/-- **Under the Riemann hypothesis the windows of a ratio have a common positive gap**: the
ground energy of every aperture is positive. -/
theorem exists_gap_neutralWindow_of_riemannHypothesis (hRH : RiemannHypothesis) {Q : ℕ}
    (hQ : 1 ≤ Q) :
    ∃ c : ℝ, 0 < c ∧ ∀ R J : ℕ, 1 ≤ R → R + J ≤ Q * R → HasGap (neutralWindow Q R J) c := by
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  let A : _root_.RHTower.SuzukiPositiveAperture := ⟨Real.log Q + 1, by positivity⟩
  refine ⟨_root_.RHTower.ccmRestrictedWeilGroundEnergy A,
    ArithmeticContinuationAndCriticalEnergy.riemannHypothesis_iff_ccmRestrictedWeilGroundEnergy_pos.mp
      hRH A, fun R J hR hRJ => ?_⟩
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hpos : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
  have hle : ((R + J : ℕ) : ℝ) ≤ (Q : ℝ) * R := by exact_mod_cast hRJ
  have h1 := Real.log_le_log hpos hle
  rw [Real.log_mul hQ'.ne' hR'.ne'] at h1
  refine hasGap_neutralWindow_of_le_groundEnergy (A := A) hR ?_ ?_ le_rfl
  · change Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * (Real.log Q + 1)
    linarith
  · rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **The a priori gap of the windows is the Riemann hypothesis.** It holds iff at every cutoff
`Q` the windows `(R, R + J]` with `R ≤ J`, `R + J ≤ Q R` have a common positive gap, and iff
those among them that hold exactly one bound state have one. -/
theorem riemannHypothesis_iff_exists_gap_neutralWindow :
    RiemannHypothesis ↔ ∀ Q : ℕ, 2 ≤ Q → ∃ c : ℝ, 0 < c ∧ ∀ R J : ℕ, 1 ≤ R → R ≤ J →
      R + J ≤ Q * R → HasGap (neutralWindow Q R J) c := by
  constructor
  · intro hRH Q hQ
    obtain ⟨c, hc, h⟩ := exists_gap_neutralWindow_of_riemannHypothesis hRH (by omega : 1 ≤ Q)
    exact ⟨c, hc, fun R J hR _ hRJ => h R J hR hRJ⟩
  · intro h
    refine riemannHypothesis_of_gap_of_bound_windows fun Q hQ => ?_
    obtain ⟨c, hc, hg⟩ := h Q hQ
    exact ⟨c, hc, fun R J h1 h2 h3 _ => hg R J h1 h2 h3⟩

theorem riemannHypothesis_iff_gap_of_bound_windows :
    RiemannHypothesis ↔ ∀ Q : ℕ, 2 ≤ Q → ∃ c : ℝ, 0 < c ∧ ∀ R J : ℕ, 1 ≤ R → R ≤ J →
      R + J ≤ Q * R →
        hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 →
          HasGap (neutralWindow Q R J) c := by
  constructor
  · intro hRH Q hQ
    obtain ⟨c, hc, h⟩ := exists_gap_neutralWindow_of_riemannHypothesis hRH (by omega : 1 ≤ Q)
    exact ⟨c, hc, fun R J hR _ hRJ _ => h R J hR hRJ⟩
  · exact riemannHypothesis_of_gap_of_bound_windows

end Windows

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
