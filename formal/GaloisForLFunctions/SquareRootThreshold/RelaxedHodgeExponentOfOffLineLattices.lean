import GaloisForLFunctions.SquareRootThreshold.WeilGroundStateLawOnLagLattices
import GaloisForLFunctions.RHTower.RelaxedHodgeDictionary
import GaloisForLFunctions.RHTower.WeilFloorSpectralSeparation

/-!
# The relaxed Hodge exponent of an off-line lattice is twice its depth

The relaxed Hodge index (`RHTower.RelaxedHodgeIndexAtLevel Z θ a`) asks
`Re W(f, f) ≥ -e^{θa} ∫|f|²` on polar-constrained tests of aperture `a`, and the Weil floor
(`RHTower.WeilFloorAtLevel Z a η`) asks `Re W(f, f) ≥ -η ∫|f|²`. A zero of depth `δ` breaks the
relaxed index once `2δ` beats `θ` by the losses of an explicit construction
(`RHTower.exists_relaxed_violation`).

For the off-line lattice `{½ ± δ + 2πik/L}` the ground-state law makes both exact:

* **Exact floor** (`offLineLattice_weilFloor_iff`, `offLineLattice_relaxedHodge_iff`). For
  `a > L/2`, `n = ⌈2a/L⌉`, the Weil floor holds iff `η ≥ L(√(S₊S₋) − n)` and the relaxed index iff
  `e^{θa} ≥ L(√(S₊S₋) − n)`, `S_± = Σ_{j<n} e^{±2δjL}`.
* **The exponent is `2δ`** (`offLineLattice_relaxedHodge_eventually_of_lt`,
  `offLineLattice_not_relaxedHodge_eventually_of_lt`). For `θ > 2δ` the lattice satisfies the
  relaxed index at every large level, for every test (polar-constrained or not); for `θ < 2δ` it
  violates it at every large level, by polar-constrained tests, with any constant `C` in front of
  `e^{θa}`.

So the depth exponent `2δ` of the relaxed Hodge index is sharp, without losses, and is attained by
a configuration whose every window has `O(L)` zeros. The same exponent `2η` governs the depth and
density lower bound `RHTower.re_W_ge_of_depth_offLineDensity`, which the lattice therefore meets
up to the polynomial factor.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Two elementary growth comparisons -/

/-- A linear function is eventually below `M e^{εa}`. -/
theorem exists_linear_le_exp {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (K : ℝ) :
    ∃ a₀ : ℝ, ∀ a ≥ a₀, 2 * a + K ≤ M * Real.exp (ε * a) := by
  refine ⟨max 1 (4 * (2 + |K|) / (M * ε ^ 2)), fun a ha => ?_⟩
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  have ha2 : 4 * (2 + |K|) / (M * ε ^ 2) ≤ a := le_trans (le_max_right _ _) ha
  have hMe : 0 < M * ε ^ 2 := by positivity
  rw [div_le_iff₀ hMe] at ha2
  have hexp : (ε * a / 2) ^ 2 ≤ Real.exp (ε * a) := by
    have h1 : ε * a / 2 ≤ Real.exp (ε * a / 2) := by
      linarith [Real.add_one_le_exp (ε * a / 2)]
    have h2 : (ε * a / 2) ^ 2 ≤ Real.exp (ε * a / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rwa [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (ε * a / 2) = ε * a by push_cast; ring] at h2
  have hK : K ≤ |K| := le_abs_self K
  have hKa : |K| ≤ |K| * a := le_mul_of_one_le_right (abs_nonneg K) ha1
  have h3 : (2 + |K|) * a ≤ M * (ε * a / 2) ^ 2 := by nlinarith
  have h4 : M * (ε * a / 2) ^ 2 ≤ M * Real.exp (ε * a) := mul_le_mul_of_nonneg_left hexp hM.le
  nlinarith

/-- `e^{-εa}` is eventually below any `κ > 0`. -/
theorem exists_exp_neg_le {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ a₀ : ℝ, ∀ a ≥ a₀, Real.exp (-(ε * a)) ≤ κ := by
  refine ⟨1 / (ε * κ), fun a ha => ?_⟩
  have hεκ : 0 < ε * κ := mul_pos hε hκ
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have ha' : 1 ≤ a * (ε * κ) := (div_le_iff₀ hεκ).mp ha
  have h1 : 1 + ε * a ≤ Real.exp (ε * a) := by linarith [Real.add_one_le_exp (ε * a)]
  have h2 : κ⁻¹ ≤ Real.exp (ε * a) := by
    calc κ⁻¹ ≤ ε * a := by
          rw [inv_le_iff_one_le_mul₀ hκ]; nlinarith
      _ ≤ Real.exp (ε * a) := by linarith
  calc Real.exp (-(ε * a)) = (Real.exp (ε * a))⁻¹ := Real.exp_neg _
    _ ≤ κ := by rw [inv_le_comm₀ (Real.exp_pos _) hκ]; exact h2

/-! ### Exact floors -/

theorem offLineLattice_weil_floor_symbol {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (offLineLatticeConfig hL hδ hδ').W f f =
        ((L : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * L) * latticeSymbol L δ m :=
  fun _ hf hfc => W_offLineLatticeConfig_lag hL hδ hδ' hf hfc

/-- **The lattice floor in the corpus language.** For `a > L/2` the off-line lattice satisfies the
polar-constrained Weil floor `η` iff `η ≥ L(√(S₊S₋) − n)`. -/
theorem offLineLattice_weilFloor_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {a : ℝ} (ha : L / 2 < a) (η : ℝ) :
    WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η ↔
      -(L * latticeFloor L δ ⌈2 * a / L⌉₊) ≤ η := by
  have ha0 : 0 < a := lt_trans (by positivity) ha
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨f, hf, hfs, hp, hm, hneg⟩ := offLineLattice_hodge_floor_sharp hL hδ hδ' ha
      (μ := -η / L) (by rw [lt_div_iff₀ hL]; linarith)
    have := h f hf hfs hp hm
    rw [show L * (-η / L) = -η by field_simp] at hneg
    linarith
  · intro h f hf hfs _ _
    have h1 := offLineLattice_weil_floor hL hδ hδ' hf hfs
    have hint : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    nlinarith

/-- **The lattice and the relaxed Hodge index.** For `a > L/2`, the off-line lattice satisfies
the relaxed Hodge index with exponent `θ` iff `e^{θa} ≥ L(√(S₊S₋) − n)`. -/
theorem offLineLattice_relaxedHodge_iff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {a : ℝ} (ha : L / 2 < a) (θ : ℝ) :
    RelaxedHodgeIndexAtLevel (offLineLatticeConfig hL hδ hδ') θ a ↔
      -(L * latticeFloor L δ ⌈2 * a / L⌉₊) ≤ Real.exp (θ * a) :=
  offLineLattice_weilFloor_iff hL hδ hδ' ha _

/-! ### The exponent `2δ` -/

/-- **Above the depth exponent.** For `θ > 2δ` the off-line lattice satisfies
`Re W(f, f) ≥ -e^{θa} ∫|f|²` on every test of aperture `a`, for all large `a`; in particular the
relaxed Hodge index with exponent `θ`. -/
theorem offLineLattice_relaxedHodge_eventually_of_lt {L δ θ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hθ : 2 * δ < θ) :
    ∃ a₀ : ℝ, ∀ a ≥ a₀,
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        -(Real.exp (θ * a) * ∫ u, ‖f u‖ ^ 2) ≤ ((offLineLatticeConfig hL hδ hδ').W f f).re) ∧
      RelaxedHodgeIndexAtLevel (offLineLatticeConfig hL hδ hδ') θ a := by
  obtain ⟨a₁, ha₁⟩ := exists_linear_le_exp (sub_pos.mpr hθ) one_pos L
  refine ⟨max a₁ 1, fun a ha => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ha)
  have hfl : -Real.exp (θ * a) ≤ L * latticeFloor L δ ⌈2 * a / L⌉₊ := by
    have h1 := (latticeFloor_aperture_bounds hL hδ ha0).1
    have h2 := ha₁ a (le_trans (le_max_left _ _) ha)
    have h3 : Real.exp (θ * a) = Real.exp ((θ - 2 * δ) * a) * Real.exp (2 * δ * a) := by
      rw [← Real.exp_add]; ring_nf
    have h4 := Real.exp_pos (2 * δ * a)
    nlinarith
  have hall : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      -(Real.exp (θ * a) * ∫ u, ‖f u‖ ^ 2) ≤ ((offLineLatticeConfig hL hδ hδ').W f f).re := by
    intro f hf hfs
    have h1 := offLineLattice_weil_floor hL hδ hδ' hf hfs
    have hint : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    nlinarith
  exact ⟨hall, fun f hf hfs _ _ => hall f hf hfs⟩

/-- **Below the depth exponent.** For `θ < 2δ` and any `C > 0`, at every large level `a` some
polar-constrained test of aperture `a` has `Re W(f, f) < -C e^{θa} ∫|f|²`; in particular the
off-line lattice violates the relaxed Hodge index with exponent `θ`. -/
theorem offLineLattice_not_relaxedHodge_eventually_of_lt {L δ θ C : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hθ : θ < 2 * δ) (hC : 0 < C) :
    ∃ a₀ : ℝ, ∀ a ≥ a₀,
      (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0 ∧
          ((offLineLatticeConfig hL hδ hδ').W f f).re < -(C * Real.exp (θ * a) * ∫ u, ‖f u‖ ^ 2)) ∧
      ¬ RelaxedHodgeIndexAtLevel (offLineLatticeConfig hL hδ hδ') θ a := by
  set κ := L * Real.exp (-(δ * L)) with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨a₁, ha₁⟩ := exists_linear_le_exp (by positivity : 0 < 2 * δ)
    (by positivity : 0 < κ / 2) L
  obtain ⟨a₂, ha₂⟩ := exists_exp_neg_le (sub_pos.mpr hθ)
    (by positivity : 0 < κ / (4 * (C + 1)))
  refine ⟨max (max a₁ a₂) L, fun a ha => ?_⟩
  have haL : L ≤ a := le_trans (le_max_right _ _) ha
  have ha0 : 0 < a := lt_of_lt_of_le hL haL
  have ha2 : L / 2 < a := by linarith
  have h1 := (latticeFloor_aperture_bounds hL hδ ha0).2
  have hlin := ha₁ a (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha)
  have hexp := ha₂ a (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha)
  -- `L e^{δ(2a − L)} = κ e^{2δa}`
  have hsplit : L * Real.exp (δ * (2 * a - L)) = κ * Real.exp (2 * δ * a) := by
    rw [hκ, mul_assoc, ← Real.exp_add]; ring_nf
  -- `C e^{θa} ≤ (κ/4) e^{2δa}`
  have hθa : (C + 1) * Real.exp (θ * a) ≤ κ / 4 * Real.exp (2 * δ * a) := by
    have : Real.exp (θ * a) = Real.exp (-((2 * δ - θ) * a)) * Real.exp (2 * δ * a) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have h4 : 0 < Real.exp (2 * δ * a) := Real.exp_pos _
    have h5 : (C + 1) * Real.exp (-((2 * δ - θ) * a)) ≤ κ / 4 := by
      rw [le_div_iff₀ (by positivity)] at hexp
      nlinarith
    nlinarith
  have hfloor : L * latticeFloor L δ ⌈2 * a / L⌉₊ < -(C * Real.exp (θ * a)) := by
    have := Real.exp_pos (θ * a)
    nlinarith
  have hfloor' : latticeFloor L δ ⌈2 * a / L⌉₊ < -(C * Real.exp (θ * a)) / L := by
    rw [lt_div_iff₀ hL]; linarith
  obtain ⟨f, hf, hfs, hp, hm, hneg⟩ := offLineLattice_hodge_floor_sharp hL hδ hδ' ha2 hfloor'
  rw [show L * (-(C * Real.exp (θ * a)) / L) = -(C * Real.exp (θ * a)) by field_simp] at hneg
  refine ⟨⟨f, hf, hfs, hp, hm, by linarith⟩, fun hrel => ?_⟩
  have := (offLineLattice_relaxedHodge_iff hL hδ hδ' ha2 θ).mp hrel
  have : -(L * latticeFloor L δ ⌈2 * a / L⌉₊) > Real.exp (θ * a) := by
    have := Real.exp_pos (θ * a)
    nlinarith
  linarith

end GaloisForLFunctions.SquareRootThreshold
