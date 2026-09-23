import GaloisForLFunctions.RHTower.LadderLattice
import GaloisForLFunctions.RHTower.DiscExtraction
import GaloisForLFunctions.RHTower.ModulusHolography
import GaloisForLFunctions.RHTower.XiDeckCharge
import GaloisForLFunctions.RHTower.EquivariantRootDissolution

/-!
# Xi dyadic descent level universality

Every fixed rung of the Xi dyadic order ladder has the same realization in divisor, window,
analytic-root, Euler-germ, modulus, deck, and Schwarz-equivariant charts.  Unlike an RH-only
bundle, this levelwise law remains non-vacuous under failure of RH and has an exact finite phase
boundary.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- Existence of a level-`k` analytic Xi root on the open right half-plane. -/
def XiDyadicRightHalfRoot (k : ℕ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g rightHalf ∧
    ∀ s ∈ rightHalf, g s ^ (2 : ℕ) ^ k = xi s

/-- Existence of a level-`k` analytic root of the FE-descended Xi function on the slit plane. -/
def XiDyadicSlitPlaneRoot (k : ℕ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g slitPlane ∧
    ∀ w ∈ slitPlane, g w ^ (2 : ℕ) ^ k = xiDescent w

/-- Every unconditional Euler-side level-`k` root germ extends across the strip. -/
def XiDyadicEulerGermExtends (k : ℕ) : Prop :=
  ∀ g₁ : ℂ → ℂ, AnalyticOnNhd ℂ g₁ farHalf →
    (∀ s ∈ farHalf, g₁ s ^ (2 : ℕ) ^ k = xi s) →
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g rightHalf ∧
      (∀ s ∈ rightHalf, g s ^ (2 : ℕ) ^ k = xi s) ∧ Set.EqOn g g₁ farHalf

/-- Every positive truncated half-band carries a level-`k` analytic Xi root. -/
def XiDyadicAllBandRoots (k : ℕ) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g (halfBand T) ∧
      ∀ s ∈ halfBand T, g s ^ (2 : ℕ) ^ k = xi s

/-- The local two-circle modulus monodromy is trivial at every right-half Xi zero. -/
def XiDyadicCircleMonodromyTrivial (k : ℕ) : Prop :=
  ∀ ρ ∈ rightHalf, xi ρ = 0 →
    ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      exp (2 * (Real.pi : ℂ) * I *
          (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
              Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
            (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1

/-- Arbitrarily small zero-free circle pairs recover trivial level-`k` modulus monodromy. -/
def XiDyadicCleanCircleMonodromyTrivial (k : ℕ) : Prop :=
  ∀ ρ ∈ rightHalf, xi ρ = 0 →
    ∃ R₀ > 0, ∀ {r R : ℝ}, 0 < r → r < R → R ≤ R₀ →
      ∃ r₁ r₂ : ℝ, r < r₁ ∧ r₁ < r₂ ∧ r₂ < R ∧
        (∀ z : ℂ, ‖z - ρ‖ = r₁ → xi z ≠ 0) ∧
        (∀ z : ℂ, ‖z - ρ‖ = r₂ → xi z ≠ 0) ∧
        exp (2 * (Real.pi : ℂ) * I *
            (((Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
                Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
              (Real.log r₂ - Real.log r₁) : ℝ) : ℂ) / (2 ^ k : ℕ)) = 1

/-- Every finite height window realizes trivial level-`k` deck transport by actual chart roots. -/
def XiDyadicAllWindowDecksTrivial (k : ℕ) : Prop :=
  ∀ T : ℝ, ∀ ρ ∈ boxZeros T, ∃ R₀ > 0, ∀ R : ℝ, 0 < R → R ≤ R₀ →
    ∃ G₁ G₂ : ℂ → ℂ,
      AnalyticOnNhd ℂ G₁ (chartR ρ R) ∧ AnalyticOnNhd ℂ G₂ (chartL ρ R) ∧
      (∀ z ∈ chartR ρ R, G₁ z ^ (2 : ℕ) ^ k = xi z) ∧
      (∀ z ∈ chartL ρ R, G₂ z ^ (2 : ℕ) ^ k = xi z) ∧
      deckClass G₁ G₂ (ρ + ((R / 2 : ℝ) : ℂ) * I)
        (ρ - ((R / 2 : ℝ) : ℂ) * I) = 1

/-- A Schwarz-equivariant level-`k` Xi root exists off the critical line. -/
def XiDyadicOfflineEquivariantRoot (k : ℕ) : Prop :=
  ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h {s : ℂ | s.re ≠ 1 / 2} ∧
    (∀ s ∈ {s : ℂ | s.re ≠ 1 / 2}, h s ^ (2 : ℕ) ^ k = xi s) ∧
    ∀ s ∈ {s : ℂ | s.re ≠ 1 / 2}, mirrorRoot h s = h s

/-- All faithful level-`k` realizations of the Xi dyadic descent obstruction. -/
structure XiDyadicDescentLevelUniversalCertificate (k : ℕ) : Prop where
  rightHalfOrderDivisible :
    ∀ ρ ∈ rightHalf, xi ρ = 0 → 2 ^ k ∣ (analyticOrderAt xi ρ).toNat
  ladderHeightSurvives :
    ∀ ρ ∈ rightHalf, xi ρ = 0 → k ≤ ladderHeight ρ
  stripOrderDivisible :
    ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 → xi ρ = 0 →
      ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ
  upperStripOrderDivisible :
    ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 → 0 ≤ ρ.im → xi ρ = 0 →
      ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ
  lineHolography : LineHolography k
  allWindowCertificates : ∀ T : ℝ, WindowCertificate k T
  allNaturalWindowCertificates : ∀ n : ℕ, WindowCertificate k n
  rightHalfRoot : XiDyadicRightHalfRoot k
  slitPlaneRoot : XiDyadicSlitPlaneRoot k
  allBandRoots : XiDyadicAllBandRoots k
  eulerGermExtends : XiDyadicEulerGermExtends k
  circleMonodromyTrivial : XiDyadicCircleMonodromyTrivial k
  cleanCircleMonodromyTrivial : XiDyadicCleanCircleMonodromyTrivial k
  pointwiseDeckChargeTrivial :
    ∀ ρ ∈ rightHalf, xi ρ = 0 → xiDeckCharge k ρ = 1
  allWindowDecksTrivial : XiDyadicAllWindowDecksTrivial k
  offlineEquivariantRoot : XiDyadicOfflineEquivariantRoot k

/-- **Xi dyadic descent level universality law.**  One order-divisibility rung is exactly its
simultaneous realization in sixteen divisor, holographic, analytic, modulus, and deck charts. -/
theorem rhLadder_iff_dyadicDescentLevelUniversalCertificate (k : ℕ) :
    RHLadder k ↔ XiDyadicDescentLevelUniversalCertificate k := by
  constructor
  · intro hlad
    exact {
      rightHalfOrderDivisible := (rhLadder_iff_toNat_dvd k).1 hlad
      ladderHeightSurvives := (rhLadder_iff_ladderHeight_ge k).1 hlad
      stripOrderDivisible := (rhLadder_iff_strip k).1 hlad
      upperStripOrderDivisible := (rhLadder_iff_openStrip_upper k).1 hlad
      lineHolography := (rhLadder_iff_lineHolography k).1 hlad
      allWindowCertificates := (rhLadder_iff_forall_windowCertificate k).1 hlad
      allNaturalWindowCertificates := (rhLadder_iff_forall_nat_windowCertificate k).1 hlad
      rightHalfRoot := (rhLadder_iff_root k).1 hlad
      slitPlaneRoot := (rhLadder_iff_root_slitPlane k).1 hlad
      allBandRoots := (rhLadder_iff_forall_bandRoot k).1 hlad
      eulerGermExtends := (rhLadder_iff_germ_extends k).1 hlad
      circleMonodromyTrivial :=
        (rhLadder_iff_circleAverage_slope_exp_eq_one k).1 hlad
      cleanCircleMonodromyTrivial :=
        (rhLadder_iff_clean_circleAverage_slope_exp_eq_one k).1 hlad
      pointwiseDeckChargeTrivial := (rhLadder_iff_xiDeckCharge_one k).1 hlad
      allWindowDecksTrivial := (rhLadder_iff_forall_deck_trivial k).1 hlad
      offlineEquivariantRoot := (rhLadder_iff_equivariant_offline_root k).1 hlad }
  · intro hcertificate
    exact (rhLadder_iff_lineHolography k).2 hcertificate.lineHolography

/-- Line holography at depth `k` is already sufficient for the entire sixteen-chart phase. -/
theorem lineHolography_iff_dyadicDescentLevelUniversalCertificate (k : ℕ) :
    LineHolography k ↔ XiDyadicDescentLevelUniversalCertificate k :=
  (rhLadder_iff_lineHolography k).symm.trans
    (rhLadder_iff_dyadicDescentLevelUniversalCertificate k)

/-- The complete levelwise universal phase at every depth is exactly RH. -/
theorem riemannHypothesis_iff_forall_dyadicDescentLevelUniversalCertificate :
    RiemannHypothesis ↔ ∀ k : ℕ, XiDyadicDescentLevelUniversalCertificate k := by
  rw [rh_iff_forall_ladder]
  exact forall_congr' rhLadder_iff_dyadicDescentLevelUniversalCertificate

/-- If RH fails, all sixteen charts survive together exactly through the sharp finite depth. -/
theorem dyadicDescentLevelUniversalCertificate_iff_le_sharpLevel
    (hnotRH : ¬ RiemannHypothesis) (k : ℕ) :
    XiDyadicDescentLevelUniversalCertificate k ↔ k ≤ sharpLevel :=
  (rhLadder_iff_dyadicDescentLevelUniversalCertificate k).symm.trans
    (rhLadder_iff_le_sharpLevel hnotRH k)

/-- Above the sharp level, every faithful realization of the rung fails simultaneously. -/
theorem not_dyadicDescentLevelUniversalCertificate_iff_sharpLevel_lt
    (hnotRH : ¬ RiemannHypothesis) (k : ℕ) :
    ¬ XiDyadicDescentLevelUniversalCertificate k ↔ sharpLevel < k := by
  constructor
  · intro hfailure
    exact Nat.lt_of_not_ge (fun hk => hfailure
      ((dyadicDescentLevelUniversalCertificate_iff_le_sharpLevel hnotRH k).2 hk))
  · intro hk hcertificate
    exact (Nat.not_le_of_lt hk)
      ((dyadicDescentLevelUniversalCertificate_iff_le_sharpLevel hnotRH k).1 hcertificate)

/-- Under failure of RH the first simultaneous breakdown occurs at `sharpLevel + 1`. -/
theorem not_dyadicDescentLevelUniversalCertificate_succ_sharpLevel
    (hnotRH : ¬ RiemannHypothesis) :
    ¬ XiDyadicDescentLevelUniversalCertificate (sharpLevel + 1) :=
  (not_dyadicDescentLevelUniversalCertificate_iff_sharpLevel_lt
    hnotRH (sharpLevel + 1)).2 (Nat.lt_succ_self sharpLevel)

end

end RHTower
