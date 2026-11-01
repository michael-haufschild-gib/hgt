import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TelescopedConductorSplitAndOneNinthWeilPositivity
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheHodgeIndexAtGrowingOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.EveryFlippedPrimeIsSeenAtLargeOverlap

/-!
# The detection edge of the complete Weil family

A profile `φ` gives at every resolution `(c, N)` the complete Weil matrix `W_{φ,c,N}`: Weil's form
on the atoms `φ((u − log n)/w)`, `w = c/N`, `1 ≤ n ≤ N`. The **edge** at horizon `N` is the first
overlap `c ≥ 1` at which `W_{φ,c,N}` fails to be positive semidefinite (`edge`, valued in
`[1, ∞]`); the **hyperplane edge** is the same on the pole hyperplane `v₁^⊥` (`hyperplaneEdge`),
and the **twin edge** is the edge of a twisted weight (`twinEdge`).

* **RH is an infinite edge** (`riemannHypothesis_iff_forall_edge_eq_top`,
  `riemannHypothesis_iff_eventually_edge_eq_top`): for every admissible profile, RH holds iff the
  edge is `∞` at every horizon, iff it is eventually `∞`.
* **Edge ceiling for every `C²` profile** (`frequently_edge_le_of_not_riemannHypothesis`): without
  RH the edge is at most `2(log N)^β` infinitely often, for every `β > 1/4`. Second-order synthesis
  makes overlap `c_N` with `c_N⁴/log N → ∞` an RH receiver, so no admissible profile has a later
  edge.
* **The universal regime of the tilted spline** (`eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline`,
  `tendsto_edge_tiltedUnitSpline`): unconditionally the edge is eventually at least `(log N)^α` for
  every `0 < α < 1/9`, so it tends to `∞`.
* **The edge window** (`frequently_edge_mem_window_of_not_riemannHypothesis`): without RH the edge
  of the tilted spline lies in `[(log N)^α, 2(log N)^β]`, `α < 1/9`, `β > 1/4`, infinitely often.
  Either the edge is `∞` everywhere, or it is a function of `N` between two powers of `log N`.
* **The hyperplane edge** (`edge_le_hyperplaneEdge`, `frequently_hyperplaneEdge_le_of_smooth`):
  it is at least the edge; without RH it is at most `2(log N)^β` infinitely often for every
  `β > 1/2` (tilted spline) and for every `β > 0` (smooth nonnegative profiles).
* **Selectivity of the edge** (`eventually_twinEdge_primeFlip_le`, `edge_selects_zeta_from_prime_flips`):
  for every admissible profile the twin edge of a prime flip is bounded; for the tilted spline the
  edge of `ζ` tends to `∞`. The edge separates `ζ` from every prime-flip twin.

The edge is an estimate-free invariant: its location without RH is bracketed by the universal
regime from below and by the receivers from above, and RH is the statement that it does not exist.
-/

noncomputable section

open Filter Topology Finset
open scoped RealInnerProductSpace ENNReal ContDiff

namespace GaloisForLFunctions.EdgeHodgeTheory

open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-! ### First failures of a property of overlaps -/

/-- The first failure of a property of overlaps: the infimum of the overlaps `c ≥ 1` at which `P`
fails, `⊤` if it never fails. -/
def firstFailure (P : ℝ → Prop) : ℝ≥0∞ := ⨅ (c : ℝ) (_ : 1 ≤ c) (_ : ¬ P c), ENNReal.ofReal c

theorem firstFailure_eq_top_iff {P : ℝ → Prop} : firstFailure P = ⊤ ↔ ∀ c, 1 ≤ c → P c := by
  simp only [firstFailure, iInf_eq_top, ENNReal.ofReal_ne_top, imp_false, not_not]

/-- `a` is below the first failure iff `P` holds on `[1, a)`. -/
theorem ofReal_le_firstFailure_iff {P : ℝ → Prop} {a : ℝ} :
    ENNReal.ofReal a ≤ firstFailure P ↔ ∀ c, 1 ≤ c → c < a → P c := by
  simp only [firstFailure, le_iInf_iff]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith)]
  constructor
  · intro h hca
    by_contra hP
    exact absurd (h hP) (not_le.mpr hca)
  · intro h hP
    by_contra hlt
    exact hP (h (not_le.mp hlt))

theorem firstFailure_le {P : ℝ → Prop} {c : ℝ} (hc : 1 ≤ c) (h : ¬ P c) :
    firstFailure P ≤ ENNReal.ofReal c :=
  iInf₂_le_of_le c hc (iInf_le _ h)

theorem of_ofReal_lt_firstFailure {P : ℝ → Prop} {c : ℝ} (hc : 1 ≤ c)
    (h : ENNReal.ofReal c < firstFailure P) : P c := by
  by_contra hP
  exact absurd (firstFailure_le hc hP) (not_le.mpr h)

/-- A weaker property fails later. -/
theorem firstFailure_mono {P Q : ℝ → Prop} (h : ∀ c, 1 ≤ c → P c → Q c) :
    firstFailure P ≤ firstFailure Q :=
  le_iInf₂ fun c hc => le_iInf fun hQ => firstFailure_le hc fun hP => hQ (h c hc hP)

/-! ### Positivity at a resolution and the edges -/

/-- An admissible profile: `C²`, supported in `[0, 1]`, with nonzero mass and positive energy. -/
structure Admissible (φ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 φ
  supp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0
  sq_pos : 0 < ∫ u, φ u ^ 2
  int_ne : (∫ u, φ u) ≠ 0

theorem admissible_tiltedUnitSpline : Admissible tiltedUnitSpline :=
  ⟨contDiff_tiltedUnitSpline, tiltedUnitSpline_eq_zero, integral_tiltedUnitSpline_sq_pos,
    integral_tiltedUnitSpline_ne_zero⟩

/-- The complete Weil family of `φ` is positive semidefinite at the resolution `(c, N)`. -/
def PositiveAt (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) : Prop :=
  ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), 0 ≤ completeWeilEnergy φ c N x

/-- The complete Weil family of `φ` is positive semidefinite on the pole hyperplane `v₁^⊥`. -/
def HyperplanePositiveAt (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) : Prop :=
  ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
    0 ≤ completeWeilEnergy φ c N x

/-- Weil's form of the weight `λ` is nonnegative on every atomic test at the resolution `(c, N)`. -/
def TwinPositiveAt (lam : ℕ → ℝ) (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) : Prop :=
  ∀ y : ℕ → ℝ, 0 ≤ weilQuadTw lam (atomicTest N y (atomDilate φ (c / N)))

/-- **The detection edge** at horizon `N`: the first overlap at which `W_{φ,c,N}` is not
positive semidefinite. -/
def edge (φ : ℝ → ℝ) (N : ℕ) : ℝ≥0∞ := firstFailure fun c => PositiveAt φ c N

/-- The edge on the pole hyperplane. -/
def hyperplaneEdge (φ : ℝ → ℝ) (N : ℕ) : ℝ≥0∞ := firstFailure fun c => HyperplanePositiveAt φ c N

/-- The edge of the twisted weight `λ`. -/
def twinEdge (lam : ℕ → ℝ) (φ : ℝ → ℝ) (N : ℕ) : ℝ≥0∞ :=
  firstFailure fun c => TwinPositiveAt lam φ c N

theorem edge_le_hyperplaneEdge (φ : ℝ → ℝ) (N : ℕ) : edge φ N ≤ hyperplaneEdge φ N :=
  firstFailure_mono fun _ _ h x _ => h x

/-- At a positive resolution, positivity of the complete Weil family is positivity of Weil's form
on the atomic tests. -/
theorem positiveAt_iff_twinPositiveAt {φ : ℝ → ℝ} (hφ : Admissible φ) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) :
    PositiveAt φ c N ↔
      TwinPositiveAt (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) φ c N := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]; exact mul_pos hw hφ.sq_pos
  constructor
  · intro H y
    have h := H (WithLp.toLp 2 fun n : PrimeHorizonIndex N => y n)
    rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ.contDiff hφ.supp hc hN,
      ← atomicTest_restrict] at h
    exact (div_nonneg_iff.mp h).elim (fun h' => h'.1) fun h' => absurd h'.2 (not_le.mpr hG)
  · intro H x
    rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ.contDiff hφ.supp hc hN]
    exact div_nonneg (H _) hG.le

/-! ### RH is an infinite edge -/

/-- Under RH the complete Weil family is positive at every resolution. -/
theorem positiveAt_of_riemannHypothesis (hRH : RiemannHypothesis) {φ : ℝ → ℝ} (hφ : Admissible φ)
    {c : ℝ} (hc : 0 < c) (N : ℕ) : PositiveAt φ c N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · intro x
    rw [completeWeilEnergy, PiLp.inner_apply]
    refine le_of_eq (Finset.sum_eq_zero fun i _ => ?_).symm
    have := i.2
    simp only [Finset.mem_Icc] at this
    omega
  show ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), 0 ≤ completeWeilEnergy φ c N x
  rw [forall_completeWeilEnergy_nonneg_iff hφ.contDiff hφ.supp hφ.sq_pos hφ.int_ne hc hN]
  intro y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨h2, hcs⟩ := atomicTest_dilate_mem (contDiff_recentredProfile hφ.contDiff)
    (vanishesOff_recentredProfile hφ.supp) (show 0 < 2 / (c / N) by positivity) N y
  exact RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _ h2 hcs

theorem edge_eq_top_of_riemannHypothesis (hRH : RiemannHypothesis) {φ : ℝ → ℝ}
    (hφ : Admissible φ) (N : ℕ) : edge φ N = ⊤ :=
  firstFailure_eq_top_iff.mpr fun _ hc => positiveAt_of_riemannHypothesis hRH hφ (by linarith) N

/-- The receivers at overlap `2(log N)^β`, `β > 1/4`, for every admissible profile. -/
theorem riemannHypothesis_iff_eventually_positiveAt_log {φ : ℝ → ℝ} (hφ : Admissible φ) {β : ℝ}
    (hβ : 1 / 4 < β) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, PositiveAt φ (2 * Real.log N ^ β) N := by
  have hc : ∀ᶠ N : ℕ in atTop, 0 < 2 * Real.log N ^ β := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    positivity
  exact riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo hφ.contDiff hφ.supp hφ.sq_pos
    hφ.int_ne hc (by rw [RenormalizedIntersectionTheory.kappa_log_eq]; exact overlapGrowthTwo_log hβ)

theorem eventually_one_le_two_mul_rpow_log {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ 2 * Real.log N ^ β := by
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N hN
  have : 1 ≤ Real.log N ^ β := Real.one_le_rpow hN hβ
  linarith

/-- **RH is an infinite edge.** -/
theorem riemannHypothesis_iff_forall_edge_eq_top {φ : ℝ → ℝ} (hφ : Admissible φ) :
    RiemannHypothesis ↔ ∀ N, edge φ N = ⊤ := by
  refine ⟨fun hRH => edge_eq_top_of_riemannHypothesis hRH hφ, fun H => ?_⟩
  refine (riemannHypothesis_iff_eventually_positiveAt_log hφ (by norm_num : (1 : ℝ) / 4 < 1)).mpr ?_
  filter_upwards [eventually_one_le_two_mul_rpow_log zero_le_one] with N hN
  exact firstFailure_eq_top_iff.mp (H N) _ hN

theorem riemannHypothesis_iff_eventually_edge_eq_top {φ : ℝ → ℝ} (hφ : Admissible φ) :
    RiemannHypothesis ↔ ∀ᶠ N in atTop, edge φ N = ⊤ := by
  refine ⟨fun hRH => Eventually.of_forall (edge_eq_top_of_riemannHypothesis hRH hφ), fun H => ?_⟩
  refine (riemannHypothesis_iff_eventually_positiveAt_log hφ (by norm_num : (1 : ℝ) / 4 < 1)).mpr ?_
  filter_upwards [H, eventually_one_le_two_mul_rpow_log zero_le_one] with N hN h1
  exact firstFailure_eq_top_iff.mp hN _ h1

/-! ### The edge ceiling of every admissible profile -/

/-- If `P` is eventually true at a schedule `c_N ≥ 1` whenever the first failure exceeds it, a
frequent first failure below the schedule follows from the failure of eventual truth. -/
theorem frequently_firstFailure_le {P : ℕ → ℝ → Prop} {c : ℕ → ℝ}
    (h1 : ∀ᶠ N : ℕ in atTop, 1 ≤ c N) (hP : ¬ ∀ᶠ N : ℕ in atTop, P N (c N)) :
    ∃ᶠ N : ℕ in atTop, firstFailure (P N) ≤ ENNReal.ofReal (c N) := by
  intro H
  refine hP ?_
  filter_upwards [H, h1] with N hN hc
  exact of_ofReal_lt_firstFailure hc (not_le.mp hN)

/-- **Edge ceiling.** Without RH, the edge of every admissible profile is at most `2(log N)^β`
infinitely often, for every `β > 1/4`. -/
theorem frequently_edge_le_of_not_riemannHypothesis {φ : ℝ → ℝ} (hφ : Admissible φ)
    (hRH : ¬ RiemannHypothesis) {β : ℝ} (hβ : 1 / 4 < β) :
    ∃ᶠ N : ℕ in atTop, edge φ N ≤ ENNReal.ofReal (2 * Real.log N ^ β) :=
  frequently_firstFailure_le (P := fun N c => PositiveAt φ c N)
    (eventually_one_le_two_mul_rpow_log (by linarith))
    fun H => hRH ((riemannHypothesis_iff_eventually_positiveAt_log hφ hβ).mpr H)

/-- **The edge dichotomy.** For every admissible profile, either the edge is `∞` at every horizon
(this is RH), or it is at most `2(log N)^β` infinitely often for every `β > 1/4`. -/
theorem edge_dichotomy {φ : ℝ → ℝ} (hφ : Admissible φ) :
    (∀ N, edge φ N = ⊤) ∨
      ∀ β : ℝ, 1 / 4 < β → ∃ᶠ N : ℕ in atTop, edge φ N ≤ ENNReal.ofReal (2 * Real.log N ^ β) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl (edge_eq_top_of_riemannHypothesis hRH hφ)
  · exact Or.inr fun β hβ => frequently_edge_le_of_not_riemannHypothesis hφ hRH hβ

/-! ### The universal regime of the tilted spline -/

/-- **Universal regime.** Unconditionally, the edge of the tilted spline is eventually at least
`(log N)^α` for every `0 < α < 1/9`. -/
theorem eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline {α : ℝ} (hα : 0 < α)
    (hα' : α < CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (Real.log N ^ α) ≤ edge tiltedUnitSpline N := by
  filter_upwards [CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_ninth
    hα hα'] with N hN
  refine ofReal_le_firstFailure_iff.mpr fun c hc hca x => ?_
  exact RenormalizedIntersectionTheory.energy_nonneg_of_posDef (completeWeilMatrix_isHermitian _ _ _)
    (hN c hc hca.le) x

/-- The edge of the tilted spline tends to `∞`, unconditionally. -/
theorem tendsto_edge_tiltedUnitSpline : Tendsto (edge tiltedUnitSpline) atTop (𝓝 ⊤) := by
  have hα := CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent_pos
  have hlog : Tendsto (fun N : ℕ => Real.log N ^
      (CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp hlog)
    (eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline (by linarith) (by linarith))

/-- **The edge window.** Without RH, the edge of the tilted spline lies in `[(log N)^α, 2(log N)^β]`
infinitely often, for every `0 < α < 1/9` and `β > 1/4`. -/
theorem frequently_edge_mem_window_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis)
    {α β : ℝ} (hα : 0 < α) (hα' : α < CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent)
    (hβ : 1 / 4 < β) :
    ∃ᶠ N : ℕ in atTop, ENNReal.ofReal (Real.log N ^ α) ≤ edge tiltedUnitSpline N ∧
      edge tiltedUnitSpline N ≤ ENNReal.ofReal (2 * Real.log N ^ β) :=
  ((frequently_edge_le_of_not_riemannHypothesis admissible_tiltedUnitSpline hRH hβ).and_eventually
    (eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline hα hα')).mono fun _ h => ⟨h.2, h.1⟩

/-! ### The hyperplane edge -/

/-- Without RH the hyperplane edge of the tilted spline is at most `2(log N)^β` infinitely often,
`β > 1/2`. -/
theorem frequently_hyperplaneEdge_le_tiltedUnitSpline (hRH : ¬ RiemannHypothesis) {β : ℝ}
    (hβ : 1 / 2 < β) :
    ∃ᶠ N : ℕ in atTop, hyperplaneEdge tiltedUnitSpline N ≤ ENNReal.ofReal (2 * Real.log N ^ β) :=
  frequently_firstFailure_le (P := fun N c => HyperplanePositiveAt tiltedUnitSpline c N)
    (eventually_one_le_two_mul_rpow_log (by linarith))
    fun H => hRH ((RenormalizedIntersectionTheory.riemannHypothesis_iff_completeWeil_hodgeIndex_log
      hβ).mpr H)

/-- **The hyperplane edge of a smooth profile.** Without RH, for a smooth nonnegative profile on
`[0, 1]` with positive mass, the hyperplane edge is at most `2(log N)^β` infinitely often for
every `β > 0`: below every power of the logarithm. -/
theorem frequently_hyperplaneEdge_le_of_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hnn : ∀ u, 0 ≤ φ u) (hint : 0 < ∫ u, φ u)
    (hM : 0 < ∫ u, φ u ^ 2) (hRH : ¬ RiemannHypothesis) {β : ℝ} (hβ : 0 < β) :
    ∃ᶠ N : ℕ in atTop, hyperplaneEdge φ N ≤ ENNReal.ofReal (2 * Real.log N ^ β) :=
  frequently_firstFailure_le (P := fun N c => HyperplanePositiveAt φ c N)
    (eventually_one_le_two_mul_rpow_log hβ.le)
    fun H => hRH ((RenormalizedIntersectionTheory.riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log
      hφ hsupp hnn hint hM hβ).mpr H)

/-- RH is an infinite hyperplane edge, for the tilted spline. -/
theorem riemannHypothesis_iff_eventually_hyperplaneEdge_eq_top :
    RiemannHypothesis ↔ ∀ᶠ N in atTop, hyperplaneEdge tiltedUnitSpline N = ⊤ := by
  refine ⟨fun hRH => Eventually.of_forall fun N => top_unique ((edge_eq_top_of_riemannHypothesis
    hRH admissible_tiltedUnitSpline N).symm.le.trans (edge_le_hyperplaneEdge _ N)), fun H => ?_⟩
  refine (RenormalizedIntersectionTheory.riemannHypothesis_iff_completeWeil_hodgeIndex_log
    (by norm_num : (1 : ℝ) / 2 < 1)).mpr ?_
  filter_upwards [H, eventually_one_le_two_mul_rpow_log zero_le_one] with N hN h1
  exact firstFailure_eq_top_iff.mp hN _ h1

/-! ### Selectivity of the edge -/

/-- **Prime-flip twins have a bounded edge.** For every admissible profile and every prime `p`,
the twin edge of the `p`-flipped weight is eventually bounded. -/
theorem eventually_twinEdge_primeFlip_le {φ : ℝ → ℝ} (hφ : Admissible φ) {p : ℕ} (hp : p.Prime) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      twinEdge (ArithmeticCountingPositivity.primeFlipWeight p) φ N ≤ ENNReal.ofReal C := by
  obtain ⟨c₀, -, h⟩ := exists_flip_negative_at_every_large_overlap hφ.contDiff hφ.supp hφ.sq_pos hp
  refine ⟨max c₀ 1, ?_⟩
  filter_upwards [h (max c₀ 1) (le_max_left _ _)] with N hN
  exact firstFailure_le (le_max_right _ _) fun hpos => (not_le.mpr hN) (hpos _)

/-- **The edge selects `ζ` from its prime-flip twins.** The edge of the tilted spline tends to `∞`
while the twin edge of every prime flip stays bounded. -/
theorem edge_selects_zeta_from_prime_flips :
    Tendsto (edge tiltedUnitSpline) atTop (𝓝 ⊤) ∧ ∀ p : ℕ, p.Prime → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      twinEdge (ArithmeticCountingPositivity.primeFlipWeight p) tiltedUnitSpline N ≤
        ENNReal.ofReal C :=
  ⟨tendsto_edge_tiltedUnitSpline, fun _ hp => eventually_twinEdge_primeFlip_le
    admissible_tiltedUnitSpline hp⟩

/-- The edge of `ζ` is the twin edge of the von Mangoldt weight, at every positive horizon. -/
theorem twinEdge_vonMangoldt_eq_edge {φ : ℝ → ℝ} (hφ : Admissible φ) {N : ℕ} (hN : 1 ≤ N) :
    twinEdge (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) φ N = edge φ N :=
  le_antisymm
    (firstFailure_mono fun _ hc h => (positiveAt_iff_twinPositiveAt hφ (by linarith) hN).mpr h)
    (firstFailure_mono fun _ hc h => (positiveAt_iff_twinPositiveAt hφ (by linarith) hN).mp h)

end GaloisForLFunctions.EdgeHodgeTheory

#print axioms GaloisForLFunctions.EdgeHodgeTheory.eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline
#print axioms GaloisForLFunctions.EdgeHodgeTheory.tendsto_edge_tiltedUnitSpline
#print axioms GaloisForLFunctions.EdgeHodgeTheory.frequently_edge_mem_window_of_not_riemannHypothesis
