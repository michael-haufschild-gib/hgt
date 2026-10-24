import GaloisForLFunctions.BiScaleUncertainty.BlindSymbolValueAndLineDesigns
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionEulerThreshold
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerTowerPairWindowSpectrum

/-!
# Prime-blind Lévy infimum against `|Ω(0)|` and the window-length slack of the prime-power cone

This module resolves the remaining two problems of §7.2 (The blind cone):

1. **The infimum of `𝒥 / h(0)` on the full blind polar class against `|Ω(0)|`
   (`blindLevyInfimum`, `zeroPoleBlindLevyInfimum`,
   `riemannHypothesis_iff_abs_gammaBracket_le_zeroPoleBlindLevyInfimum_primePowerNodes`):**
   For every nonnegative combination `c`, the combination Lévy energy
   `combinationLevyEnergy c = nodeArchOnly c - EF.gammaBracket 0 * massOf c` is nonnegative, agrees
   with `Σ c_f 𝒥(f)` on real tests, and satisfies the exact identity
   `combinationLevyEnergy c / massOf c - |EF.gammaBracket 0| = nodeArchOnly c / massOf c`.
   Consequently, the infimum of `combinationLevyEnergy c / massOf c` on `BlindOn 𝒩` is
   `|EF.gammaBracket 0| + blindSymbolValue 𝒩`, and on the zero-pole `𝒩`-blind cone is
   `|EF.gammaBracket 0| + zeroPoleBlindSymbolValue 𝒩`.
   On the full blind polar class (`𝒩 = primePowerNodes` or `Set.univ`), the unconstrained infimum
   lies strictly below `|EF.gammaBracket 0|` (`blindLevyInfimum_univ_lt_abs_gammaBracket`), and the
   polar inequality `|EF.gammaBracket 0| ≤ zeroPoleBlindLevyInfimum 𝒩` on either `primePowerNodes`
   or `Set.univ` is equivalent to the Riemann Hypothesis
   (`riemannHypothesis_iff_abs_gammaBracket_le_zeroPoleBlindLevyInfimum_primePowerNodes`,
   `riemannHypothesis_iff_abs_gammaBracket_le_zeroPoleBlindLevyInfimum_univ`).

2. **The window-length slack of the prime-power-blind cone as a function of `L`
   (`blindOn_primePowerNodes_iff_window_lt`, `windowLevyTailFloor`,
   `window_levy_tail_mul_massOf_le_nodeArchOnly`,
   `exists_windowSupported_blindOn_univ_nodeArchOnly_le`):**
   On combinations `c` whose active tests are supported in open intervals of length `L > 0`
   (`WindowSupported L c`):
   * **Exact finite-cutoff reduction:** every node `log n ≥ L` is automatically blind, so
     `BlindOn primePowerNodes c ↔ BlindOn {n ∈ primePowerNodes | Real.log n < L} c`. For
     `L ≤ log 2`, every `L`-window combination is blind at all integer nodes and has
     `nodeArchEnergy c = weilEnergy c`; for any cutoff `K`, blindness on
     `{n ∈ primePowerNodes | n ≤ K}` implies full `primePowerNodes` blindness and `A(c) = W(c)` on
     windows `L ≤ log (K + 1)`.
   * **Exact Lévy tail floor for `nodeArchOnly` and `combinationLevyEnergy`:** for any complex
     `f : WeilTestFn` supported in `Ioo a (a + L)` and any shift `x ≥ L`, `f.1` and `f.1(· + x)`
     have disjoint supports, so `∫ ‖f.1 u - f.1 (u + x)‖² = 2 ∫ ‖f.1 u‖²`. Integrating against the
     Lévy density over `(L, ∞)` yields the unconditional lower bound
     `(EF.gammaBracket 0 + windowLevyTailFloor L) * massOf c ≤ nodeArchOnly c`
     where `windowLevyTailFloor L = ∫_{Ioi L} archLevySinhWeight =
     log ((1 + e^{-L/2}) / (1 - e^{-L/2})) + 2 arctan (e^{-L/2})`.
     In particular, whenever `|EF.gammaBracket 0| ≤ windowLevyTailFloor L`, `0 ≤ nodeArchOnly c`
     holds unconditionally on all `L`-window combinations without any pole constraint.
   * **Logarithmic upper bound:** for `0 < L ≤ 1 / 5`, compressing `pairBump` by `1 / (5 L)` gives
     an `L`-window test blind at all integers with
     `nodeArchOnly c / massOf c ≤ EF.gammaBracket 0 + compressedEnergyConstant + log (1 / (5 L))`.
-/

open MeasureTheory Set Filter Topology Complex Finsupp
open scoped FourierTransform
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. Combination Lévy energy and the infimum of `𝒥 / h(0)` against `|Ω(0)|` -/

/-- The combination Lévy energy `nodeArchOnly c - EF.gammaBracket 0 * massOf c`. -/
def combinationLevyEnergy (c : WeilTestFn →₀ ℝ) : ℝ :=
  nodeArchOnly c - EF.gammaBracket 0 * massOf c

theorem combinationLevyEnergy_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) :
    0 ≤ combinationLevyEnergy c :=
  sub_nonneg.mpr (gammaBracket_zero_mul_massOf_le_nodeArchOnly hc)

theorem combinationLevyEnergy_add (c d : WeilTestFn →₀ ℝ) :
    combinationLevyEnergy (c + d) = combinationLevyEnergy c + combinationLevyEnergy d := by
  simp only [combinationLevyEnergy, nodeArchOnly_add, massOf_add]
  ring

theorem combinationLevyEnergy_single_realTest {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (t : ℝ) :
    combinationLevyEnergy (Finsupp.single (realTest g hg hgc) t) = t * biScaleLevyEnergy g := by
  rw [combinationLevyEnergy, nodeArchOnly_single, archOnly_realTest hg hgc, massOf_single,
    show (realTest g hg hgc).1 = fun x => ((g x : ℝ) : ℂ) from rfl, integral_norm_sq_ofReal]
  ring

theorem abs_gammaBracket_zero_eq_neg : |EF.gammaBracket 0| = -EF.gammaBracket 0 := by
  rw [abs_gammaBracket_zero, gammaBracket_zero_eq]
  ring

/-- The normalized Lévy energy minus `|Ω(0)|` is the normalized archimedean symbol without the
pole. -/
theorem combinationLevyEnergy_div_massOf_sub_abs_gammaBracket {c : WeilTestFn →₀ ℝ}
    (hm : 0 < massOf c) :
    combinationLevyEnergy c / massOf c - |EF.gammaBracket 0| = nodeArchOnly c / massOf c := by
  rw [combinationLevyEnergy, abs_gammaBracket_zero_eq_neg, sub_div,
    mul_div_cancel_right₀ _ hm.ne']
  ring

/-- Normalized Lévy energies `combinationLevyEnergy c / massOf c` over nonnegative `𝒩`-blind
combinations of positive mass. -/
def blindLevySet (𝒩 : Set ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn 𝒩 c ∧ 0 < massOf c ∧
    x = combinationLevyEnergy c / massOf c}

/-- The infimum of `combinationLevyEnergy c / massOf c` over nonnegative `𝒩`-blind combinations. -/
def blindLevyInfimum (𝒩 : Set ℕ) : ℝ := sInf (blindLevySet 𝒩)

/-- Normalized Lévy energies `combinationLevyEnergy c / massOf c` over nonnegative zero-pole
`𝒩`-blind combinations of positive mass. -/
def zeroPoleBlindLevySet (𝒩 : Set ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn 𝒩 c ∧ nodePoleMass c = 0 ∧
    0 < massOf c ∧ x = combinationLevyEnergy c / massOf c}

/-- The infimum of `combinationLevyEnergy c / massOf c` over nonnegative zero-pole `𝒩`-blind
combinations. -/
def zeroPoleBlindLevyInfimum (𝒩 : Set ℕ) : ℝ := sInf (zeroPoleBlindLevySet 𝒩)

theorem blindLevySet_eq_image (𝒩 : Set ℕ) :
    blindLevySet 𝒩 = (fun y => |EF.gammaBracket 0| + y) '' blindSymbolSet 𝒩 := by
  ext x
  simp only [blindLevySet, blindSymbolSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨c, hc, hb, hm, rfl⟩
    refine ⟨nodeArchOnly c / massOf c, ⟨c, hc, hb, hm, rfl⟩, ?_⟩
    linarith [combinationLevyEnergy_div_massOf_sub_abs_gammaBracket hm]
  · rintro ⟨_, ⟨c, hc, hb, hm, rfl⟩, rfl⟩
    refine ⟨c, hc, hb, hm, ?_⟩
    linarith [combinationLevyEnergy_div_massOf_sub_abs_gammaBracket hm]

theorem zeroPoleBlindLevySet_eq_image (𝒩 : Set ℕ) :
    zeroPoleBlindLevySet 𝒩 = (fun y => |EF.gammaBracket 0| + y) '' zeroPoleBlindSymbolSet 𝒩 := by
  ext x
  simp only [zeroPoleBlindLevySet, zeroPoleBlindSymbolSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨c, hc, hb, hp, hm, rfl⟩
    refine ⟨nodeArchEnergy c / massOf c, ⟨c, hc, hb, hp, hm, rfl⟩, ?_⟩
    have hA : nodeArchOnly c = nodeArchEnergy c := by rw [nodeArchOnly, hp, sub_zero]
    rw [← hA]
    linarith [combinationLevyEnergy_div_massOf_sub_abs_gammaBracket hm]
  · rintro ⟨_, ⟨c, hc, hb, hp, hm, rfl⟩, rfl⟩
    refine ⟨c, hc, hb, hp, hm, ?_⟩
    have hA : nodeArchOnly c = nodeArchEnergy c := by rw [nodeArchOnly, hp, sub_zero]
    rw [← hA]
    linarith [combinationLevyEnergy_div_massOf_sub_abs_gammaBracket hm]

/-- **Exact shift law for the blind Lévy infimum:**
`blindLevyInfimum 𝒩 = |EF.gammaBracket 0| + blindSymbolValue 𝒩`. -/
theorem blindLevyInfimum_eq_abs_gammaBracket_add_blindSymbolValue (𝒩 : Set ℕ) :
    blindLevyInfimum 𝒩 = |EF.gammaBracket 0| + blindSymbolValue 𝒩 := by
  have h1 : blindLevyInfimum 𝒩 ≤ |EF.gammaBracket 0| + blindSymbolValue 𝒩 := by
    rw [le_iff_forall_pos_lt_add]
    intro ε hε
    obtain ⟨y, hy, hlt⟩ := (csInf_lt_iff (blindSymbolSet_bddBelow 𝒩)
      (blindSymbolSet_nonempty 𝒩)).mp (show blindSymbolValue 𝒩 < blindSymbolValue 𝒩 + ε by linarith)
    have hmem : |EF.gammaBracket 0| + y ∈ blindLevySet 𝒩 := by
      rw [blindLevySet_eq_image]; exact ⟨y, hy, rfl⟩
    have hbdd : BddBelow (blindLevySet 𝒩) := by
      refine ⟨0, ?_⟩
      rintro x ⟨c, hc, -, hm, rfl⟩
      exact div_nonneg (combinationLevyEnergy_nonneg hc) hm.le
    exact (csInf_le hbdd hmem).trans_lt (by linarith)
  have h2 : |EF.gammaBracket 0| + blindSymbolValue 𝒩 ≤ blindLevyInfimum 𝒩 := by
    have hne : (blindLevySet 𝒩).Nonempty := by
      rw [blindLevySet_eq_image]; exact (blindSymbolSet_nonempty 𝒩).image _
    rw [blindLevyInfimum]
    refine le_csInf hne fun x hx => ?_
    rw [blindLevySet_eq_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := csInf_le (blindSymbolSet_bddBelow 𝒩) hy
    linarith [show blindSymbolValue 𝒩 = sInf (blindSymbolSet 𝒩) from rfl]
  exact le_antisymm h1 h2

/-- **Exact shift law for the zero-pole blind Lévy infimum:**
`zeroPoleBlindLevyInfimum 𝒩 = |EF.gammaBracket 0| + zeroPoleBlindSymbolValue 𝒩`. -/
theorem zeroPoleBlindLevyInfimum_eq_abs_gammaBracket_add_zeroPoleBlindSymbolValue (𝒩 : Set ℕ) :
    zeroPoleBlindLevyInfimum 𝒩 = |EF.gammaBracket 0| + zeroPoleBlindSymbolValue 𝒩 := by
  have h1 : zeroPoleBlindLevyInfimum 𝒩 ≤ |EF.gammaBracket 0| + zeroPoleBlindSymbolValue 𝒩 := by
    rw [le_iff_forall_pos_lt_add]
    intro ε hε
    obtain ⟨y, hy, hlt⟩ := (csInf_lt_iff (zeroPoleBlindSymbolSet_bddBelow 𝒩)
      (zeroPoleBlindSymbolSet_nonempty 𝒩)).mp
      (show zeroPoleBlindSymbolValue 𝒩 < zeroPoleBlindSymbolValue 𝒩 + ε by linarith)
    have hmem : |EF.gammaBracket 0| + y ∈ zeroPoleBlindLevySet 𝒩 := by
      rw [zeroPoleBlindLevySet_eq_image]; exact ⟨y, hy, rfl⟩
    have hbdd : BddBelow (zeroPoleBlindLevySet 𝒩) := by
      refine ⟨0, ?_⟩
      rintro x ⟨c, hc, -, -, hm, rfl⟩
      exact div_nonneg (combinationLevyEnergy_nonneg hc) hm.le
    exact (csInf_le hbdd hmem).trans_lt (by linarith)
  have h2 : |EF.gammaBracket 0| + zeroPoleBlindSymbolValue 𝒩 ≤ zeroPoleBlindLevyInfimum 𝒩 := by
    have hne : (zeroPoleBlindLevySet 𝒩).Nonempty := by
      rw [zeroPoleBlindLevySet_eq_image]; exact (zeroPoleBlindSymbolSet_nonempty 𝒩).image _
    rw [zeroPoleBlindLevyInfimum]
    refine le_csInf hne fun x hx => ?_
    rw [zeroPoleBlindLevySet_eq_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := csInf_le (zeroPoleBlindSymbolSet_bddBelow 𝒩) hy
    linarith [show zeroPoleBlindSymbolValue 𝒩 = sInf (zeroPoleBlindSymbolSet 𝒩) from rfl]
  exact le_antisymm h1 h2

/-- Without the zero-pole constraint, the blind symbol value on `Set.univ` is strictly negative, so
`blindLevyInfimum Set.univ < |EF.gammaBracket 0|`. -/
theorem blindSymbolValue_univ_neg : blindSymbolValue Set.univ < 0 := by
  obtain ⟨c, hc, hv, hneg⟩ := exists_blind_nodeArchOnly_neg
  have hm : 0 < massOf c := by
    rcases eq_or_lt_of_le (massOf_nonneg hc) with hm0 | hm
    · exfalso; rw [nodeArchOnly_eq_zero_of_massOf_eq_zero hc hm0.symm] at hneg; exact lt_irrefl 0 hneg
    · exact hm
  have hmem : nodeArchOnly c / massOf c ∈ blindSymbolSet Set.univ :=
    ⟨c, hc, fun j _ => by rw [hv]; rfl, hm, rfl⟩
  exact (csInf_le (blindSymbolSet_bddBelow Set.univ) hmem).trans_lt (div_neg_of_neg_of_pos hneg hm)

theorem blindLevyInfimum_univ_lt_abs_gammaBracket :
    blindLevyInfimum Set.univ < |EF.gammaBracket 0| := by
  rw [blindLevyInfimum_eq_abs_gammaBracket_add_blindSymbolValue]
  linarith [blindSymbolValue_univ_neg]

/-- **Equivalence of RH with the polar Lévy infimum reaching `|Ω(0)|` on `primePowerNodes`.** -/
theorem riemannHypothesis_iff_abs_gammaBracket_le_zeroPoleBlindLevyInfimum_primePowerNodes :
    RiemannHypothesis ↔ |EF.gammaBracket 0| ≤ zeroPoleBlindLevyInfimum primePowerNodes := by
  rw [riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers,
    zeroPoleBlindLevyInfimum_eq_abs_gammaBracket_add_zeroPoleBlindSymbolValue]
  have h0 : ZeroPoleBlindPositiveOn primePowerNodes ↔
      ZeroPoleBlindSymbolSlackOn primePowerNodes 0 := by
    simp [ZeroPoleBlindPositiveOn, ZeroPoleBlindSymbolSlackOn]
  rw [h0, zeroPoleBlindSymbolSlackOn_iff_zeroPoleBlindSymbolValue]
  constructor <;> intro h <;> linarith

/-- **Equivalence of RH with the polar Lévy infimum reaching `|Ω(0)|` on `Set.univ`.** -/
theorem riemannHypothesis_iff_abs_gammaBracket_le_zeroPoleBlindLevyInfimum_univ :
    RiemannHypothesis ↔ |EF.gammaBracket 0| ≤ zeroPoleBlindLevyInfimum Set.univ := by
  rw [riemannHypothesis_iff_zeroPoleBlindPositiveOn_all,
    zeroPoleBlindLevyInfimum_eq_abs_gammaBracket_add_zeroPoleBlindSymbolValue]
  have h0 : ZeroPoleBlindPositiveOn {n | 2 ≤ n} ↔
      ZeroPoleBlindSymbolSlackOn Set.univ 0 := by
    refine ⟨fun h c hc hb hp => by simpa using h c hc (fun j _ => hb j trivial) hp,
      fun h c hc hb hp => ?_⟩
    have := h c hc (fun j _ => hb j j.2) hp
    linarith
  rw [h0, zeroPoleBlindSymbolSlackOn_iff_zeroPoleBlindSymbolValue]
  constructor <;> intro h <;> linarith

/-- **Equivalence of RH with the combination Lévy uncertainty inequality on the zero-pole
`primePowerNodes`-blind cone.** -/
theorem riemannHypothesis_iff_forall_primePower_blind_zeroPole_levy_ge :
    RiemannHypothesis ↔
      ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → BlindOn primePowerNodes c → nodePoleMass c = 0 →
        |EF.gammaBracket 0| * massOf c ≤ combinationLevyEnergy c := by
  rw [riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers]
  constructor
  · intro h c hc hb hp
    have hE := h c hc hb hp
    rw [combinationLevyEnergy, nodeArchOnly, hp, sub_zero, abs_gammaBracket_zero_eq_neg]
    linarith
  · intro h c hc hb hp
    have hL := h c hc hb hp
    rw [combinationLevyEnergy, nodeArchOnly, hp, sub_zero, abs_gammaBracket_zero_eq_neg] at hL
    linarith

/-! ### 2. Window-length reduction of the prime-power-blind cone -/

/-- A combination `c` is supported in open windows of length `L` if every active test in `c.support`
is supported in some open interval `Ioo a (a + L)`. -/
def WindowSupported (L : ℝ) (c : WeilTestFn →₀ ℝ) : Prop :=
  ∀ f ∈ c.support, ∃ a : ℝ, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)

/-- On windows of length `L`, `BlindOn primePowerNodes` reduces to blindness on the finite set of
prime powers with `log n < L`. -/
theorem blindOn_primePowerNodes_iff_window_lt {L : ℝ} {c : WeilTestFn →₀ ℝ}
    (hw : WindowSupported L c) :
    BlindOn primePowerNodes c ↔ BlindOn {n ∈ primePowerNodes | Real.log n < L} c := by
  refine ⟨fun hb => blindOn_of_subset (fun _ hn => hn.1) hb, fun hb j hj => ?_⟩
  rcases lt_or_ge (Real.log (j : ℕ)) L with hlt | hge
  · exact hb j ⟨hj, hlt⟩
  · exact nodeVector_eq_zero_of_window hw j.2 hge

/-- When `L ≤ log 2`, every `L`-window-supported combination is automatically blind at all integer
nodes `n ≥ 2`. -/
theorem blindOn_univ_of_windowSupported_le_log_two {L : ℝ} (hL : L ≤ Real.log 2)
    {c : WeilTestFn →₀ ℝ} (hw : WindowSupported L c) :
    BlindOn Set.univ c := fun j _ =>
  nodeVector_eq_zero_of_window hw j.2 (hL.trans (Real.log_le_log two_pos (by exact_mod_cast j.2)))

/-- When `L ≤ log 2`, every `L`-window-supported combination satisfies `A(c) = W(c)` with no
blindness assumption. -/
theorem nodeArchEnergy_eq_weilEnergy_of_windowSupported_le_log_two {L : ℝ} (hL : L ≤ Real.log 2)
    {c : WeilTestFn →₀ ℝ} (hw : WindowSupported L c) :
    nodeArchEnergy c = weilEnergy c :=
  nodeArchEnergy_eq_weilEnergy_of_blindOn_primePowers
    (blindOn_of_subset (Set.subset_univ _) (blindOn_univ_of_windowSupported_le_log_two hL hw))

/-- For any finite cutoff `K`, a combination blind on `{n ∈ primePowerNodes | n ≤ K}` and supported
in windows of length `L ≤ log (K + 1)` is blind on all of `primePowerNodes` and satisfies
`nodeArchEnergy c = weilEnergy c`. -/
theorem blindOn_primePowerNodes_of_windowSupported_le_cutoff {K : ℕ} {L : ℝ}
    (hL : L ≤ Real.log ((K : ℝ) + 1)) {c : WeilTestFn →₀ ℝ} (hw : WindowSupported L c)
    (hb : BlindOn {n ∈ primePowerNodes | n ≤ K} c) :
    BlindOn primePowerNodes c := by
  intro j hj
  by_cases hjK : (j : ℕ) ≤ K
  · exact hb j ⟨hj, hjK⟩
  · have hK1 : (K : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast (show K + 1 ≤ (j : ℕ) by omega)
    have hlog : L ≤ Real.log (j : ℕ) := hL.trans (Real.log_le_log (by positivity) hK1)
    exact nodeVector_eq_zero_of_window hw j.2 hlog

theorem nodeArchEnergy_eq_weilEnergy_of_windowSupported_le_cutoff {K : ℕ} {L : ℝ}
    (hL : L ≤ Real.log ((K : ℝ) + 1)) {c : WeilTestFn →₀ ℝ} (hw : WindowSupported L c)
    (hb : BlindOn {n ∈ primePowerNodes | n ≤ K} c) :
    nodeArchEnergy c = weilEnergy c :=
  nodeArchEnergy_eq_weilEnergy_of_blindOn_primePowers
    (blindOn_primePowerNodes_of_windowSupported_le_cutoff hL hw hb)

/-! ### 3. The exact Lévy tail floor and window-length symbol slack -/

/-- The Lévy tail floor `∫_{x > L} archLevySinhWeight x dx` forced by support in an interval of
length `L > 0`. -/
def windowLevyTailFloor (L : ℝ) : ℝ := ∫ x in Ioi L, archLevySinhWeight x

/-- Closed form of the window Lévy tail floor:
`windowLevyTailFloor L = log ((1 + e^{-L/2}) / (1 - e^{-L/2})) + 2 arctan (e^{-L/2})`. -/
theorem windowLevyTailFloor_eq {L : ℝ} (hL : 0 < L) :
    windowLevyTailFloor L =
      Real.log ((1 + Real.exp (-L / 2)) / (1 - Real.exp (-L / 2))) +
        2 * Real.arctan (Real.exp (-L / 2)) :=
  integral_archLevySinhWeight_Ioi hL

theorem windowLevyTailFloor_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ windowLevyTailFloor L :=
  setIntegral_nonneg measurableSet_Ioi fun _ hx => (archLevySinhWeight_pos (hL.trans hx)).le

/-- For `f` supported in `Ioo a (a + L)` and `x ≥ L`, `f` and `f(· + x)` have disjoint supports, so
`∫ ‖f u - f (u + x)‖² = 2 ∫ ‖f u‖²`. -/
theorem integral_norm_sub_shift_sq_of_window {f : WeilTestFn} {a L x : ℝ}
    (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) (hx : L ≤ x) :
    (∫ u : ℝ, ‖f.1 u - f.1 (u + x)‖ ^ 2) = 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have hpt : ∀ u : ℝ, ‖f.1 u - f.1 (u + x)‖ ^ 2 = ‖f.1 u‖ ^ 2 + ‖f.1 (u + x)‖ ^ 2 := by
    intro u
    by_cases hu : f.1 u = 0
    · simp [hu]
    · have hux : f.1 (u + x) = 0 := by
        by_contra hux
        have m1 := hsupp u hu
        have m2 := hsupp (u + x) hux
        linarith [m1.1, m2.2]
      simp [hux]
  have hcs : HasCompactSupport (fun u => ‖f.1 u‖ ^ 2) :=
    f.2.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hnorm : Integrable (fun u => ‖f.1 u‖ ^ 2) :=
    (f.2.1.continuous.norm.pow 2).integrable_of_hasCompactSupport hcs
  simp_rw [hpt]
  rw [integral_add hnorm (hnorm.comp_add_right x),
    integral_add_right_eq_self (fun u => ‖f.1 u‖ ^ 2) x]
  ring

/-- **Lévy–Khintchine identity for the archimedean symbol of a general complex Weil test.** -/
theorem weilArchRe_sub_pole_eq_levy_dirichlet (f : WeilTestFn) :
    weilArchRe (EF.weilTest f.1 f.1) - (weilPoleTerm (EF.weilTest f.1 f.1)).re =
      EF.gammaBracket 0 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        (∫⁻ x in Ioi (0 : ℝ),
          ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖f.1 u - f.1 (u + x)‖ ^ 2)).toReal := by
  have hF1 : Integrable f.1 := f.2.1.continuous.integrable_of_hasCompactSupport f.2.2
  have hFL2 : MemLp f.1 2 := f.2.1.continuous.memLp_of_hasCompactSupport f.2.2
  have hintR : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r :=
    integrable_normSq_paperFT_mul_gammaBracket f
  have hint : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * π * ξ) * ‖𝓕 f.1 ξ‖ ^ 2 := by
    have h := (hintR.comp_mul_left' (R := -(2 * π)) (by
      have := Real.pi_pos; intro h; linarith)).div_const 2
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_eq_paperFT_neg_two_pi_mul,
      WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
      show -(2 * π) * ξ = -(2 * π * ξ) by ring, gammaHardyPhaseRate_neg]
    ring
  rw [weilArchRe_sub_pole_eq f, WeilLevyPole.integral_paperFT_sq_mul_gammaBracket f.1,
    integral_archSymbol_mul_normSq_fourier_eq hF1 hFL2 hint,
    WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate]

/-- **Window Lévy tail floor for a single Weil test.** For any `f : WeilTestFn` supported in
`Ioo a (a + L)` with `0 < L`,
`(EF.gammaBracket 0 + windowLevyTailFloor L) * ∫ ‖f.1 u‖² ≤ weilArchRe - Re P`. -/
theorem window_levy_tail_le_weilArchRe_sub_pole {f : WeilTestFn} {a L : ℝ} (hL : 0 < L)
    (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) :
    (EF.gammaBracket 0 + windowLevyTailFloor L) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      weilArchRe (EF.weilTest f.1 f.1) - (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
  have hF1 : Integrable f.1 := f.2.1.continuous.integrable_of_hasCompactSupport f.2.2
  have hFL2 : MemLp f.1 2 := f.2.1.continuous.memLp_of_hasCompactSupport f.2.2
  have hintR : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * EF.gammaBracket r :=
    integrable_normSq_paperFT_mul_gammaBracket f
  have hint : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * π * ξ) * ‖𝓕 f.1 ξ‖ ^ 2 := by
    have h := (hintR.comp_mul_left' (R := -(2 * π)) (by
      have := Real.pi_pos; intro h; linarith)).div_const 2
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_eq_paperFT_neg_two_pi_mul,
      WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
      show -(2 * π) * ξ = -(2 * π * ξ) by ring, gammaHardyPhaseRate_neg]
    ring
  have hfin := lintegral_archLevyDirichlet_ne_top hF1 hFL2 hint
  have hnorm0 : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hIntL : IntegrableOn (fun x => archLevySinhWeight x * ∫ u : ℝ, ‖f.1 u‖ ^ 2) (Ioi L) :=
    (integrableOn_archLevySinhWeight_Ioi hL).mul_const _
  have hnn : ∀ᵐ x ∂volume.restrict (Ioi L),
      0 ≤ archLevySinhWeight x * ∫ u : ℝ, ‖f.1 u‖ ^ 2 :=
    (ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
      mul_nonneg (archLevySinhWeight_pos (hL.trans hx)).le hnorm0
  have hl1 := ofReal_integral_eq_lintegral_ofReal hIntL hnn
  have hl2 : (∫⁻ x in Ioi L, ENNReal.ofReal (archLevySinhWeight x * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) =
      ∫⁻ x in Ioi L,
        ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖f.1 u - f.1 (u + x)‖ ^ 2) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    dsimp only [archLevySinhWeight]
    rw [integral_norm_sub_shift_sq_of_window hsupp (mem_Ioi.mp hx).le,
      exp_half_div_sinh_eq (hL.trans hx)]
    congr 1; ring
  have hl3 : (∫⁻ x in Ioi L,
        ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖f.1 u - f.1 (u + x)‖ ^ 2)) ≤
      ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖f.1 u - f.1 (u + x)‖ ^ 2) :=
    lintegral_mono_set (Ioi_subset_Ioi hL.le)
  have hle_enn : ENNReal.ofReal (windowLevyTailFloor L * ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖f.1 u - f.1 (u + x)‖ ^ 2) := by
    rw [windowLevyTailFloor, ← MeasureTheory.integral_mul_const, hl1, hl2]
    exact hl3
  have hle_real := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hle_enn
  rw [ENNReal.toReal_ofReal (mul_nonneg (windowLevyTailFloor_nonneg hL) hnorm0)] at hle_real
  rw [weilArchRe_sub_pole_eq_levy_dirichlet f, add_mul]
  linarith

/-- **Window Lévy tail floor for combinations.** On every nonnegative `L`-window-supported
combination `c` (`0 < L`),
`(EF.gammaBracket 0 + windowLevyTailFloor L) * massOf c ≤ nodeArchOnly c`. -/
theorem window_levy_tail_mul_massOf_le_nodeArchOnly {L : ℝ} (hL : 0 < L)
    {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (hw : WindowSupported L c) :
    (EF.gammaBracket 0 + windowLevyTailFloor L) * massOf c ≤ nodeArchOnly c := by
  rw [massOf, nodeArchOnly_eq_linearCombination, linearCombination_apply, Finsupp.mul_sum,
    Finsupp.sum]
  refine Finset.sum_le_sum fun f hf => ?_
  obtain ⟨a, ha⟩ := hw f hf
  simp only [smul_eq_mul]
  have h := window_levy_tail_le_weilArchRe_sub_pole hL ha
  have hcf := hc f
  nlinarith

/-- On every nonnegative `L`-window-supported combination `c` (`0 < L`),
`windowLevyTailFloor L * massOf c ≤ combinationLevyEnergy c`. -/
theorem windowLevyTailFloor_mul_massOf_le_combinationLevyEnergy {L : ℝ} (hL : 0 < L)
    {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (hw : WindowSupported L c) :
    windowLevyTailFloor L * massOf c ≤ combinationLevyEnergy c := by
  have h := window_levy_tail_mul_massOf_le_nodeArchOnly hL hc hw
  rw [combinationLevyEnergy]
  linarith

/-- **Unconditional window symbol positivity at short window length.** Whenever
`|EF.gammaBracket 0| ≤ windowLevyTailFloor L`, every nonnegative `L`-window-supported combination
has `0 ≤ nodeArchOnly c` without any pole constraint or blindness hypothesis. -/
theorem nodeArchOnly_nonneg_of_windowSupported_of_tail_ge {L : ℝ} (hL : 0 < L)
    (htail : |EF.gammaBracket 0| ≤ windowLevyTailFloor L) {c : WeilTestFn →₀ ℝ}
    (hc : ∀ f, 0 ≤ c f) (hw : WindowSupported L c) :
    0 ≤ nodeArchOnly c := by
  have h := window_levy_tail_mul_massOf_le_nodeArchOnly hL hc hw
  have hm := massOf_nonneg hc
  rw [abs_gammaBracket_zero_eq_neg] at htail
  have h0 : 0 ≤ (EF.gammaBracket 0 + windowLevyTailFloor L) * massOf c :=
    mul_nonneg (by linarith) hm
  linarith

/-- **Logarithmic upper bound on the `L`-window blind cone.** For `0 < L ≤ 1 / 5`, compressing
`pairBump` by `1 / (5 L)` produces a nonnegative `L`-window-supported combination `c` that is blind
at all integer nodes (`BlindOn Set.univ c`, hence `BlindOn primePowerNodes c`) and satisfies
`nodeArchOnly c ≤ (EF.gammaBracket 0 + compressedEnergyConstant + Real.log (1 / (5 * L))) * massOf c`. -/
theorem exists_windowSupported_blindOn_univ_nodeArchOnly_le {L : ℝ} (hL : 0 < L)
    (hL5 : L ≤ 1 / 5) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ WindowSupported L c ∧ BlindOn Set.univ c ∧
      0 < massOf c ∧
      nodeArchOnly c ≤
        (EF.gammaBracket 0 + compressedEnergyConstant + Real.log (1 / (5 * L))) * massOf c := by
  classical
  set S : ℝ := 1 / (5 * L) with hSdef
  have hS1 : 1 ≤ S := by rw [hSdef, le_div_iff₀ (by positivity)]; linarith
  have hS0 : 0 < S := by linarith
  set g : WeilTestFn := realTest (compressedBump S) (contDiff_compressedBump S)
    (hasCompactSupport_compressedBump hS0)
  have hsupp : ∀ u, g.1 u ≠ 0 → u ∈ Ioo (-L / 2) (-L / 2 + L) := by
    intro u hu
    have hbu : pairBump (S * u) ≠ 0 := fun h0 => hu (by simp [g, realTest, sourceRescale, h0])
    have habs : |S * u| < 1 / 10 := by
      by_contra hge; push Not at hge; exact hbu (adjBump_eq_zero hge)
    rw [abs_mul, abs_of_pos hS0, hSdef] at habs
    have hu_abs : |u| < L / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)] at habs
      linarith
    rw [abs_lt] at hu_abs
    exact ⟨by linarith [hu_abs.1], by linarith [hu_abs.2]⟩
  have hw : WindowSupported L (Finsupp.single g 1) := by
    intro f hf
    rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hf
    split_ifs at hf with hfg
    · subst hfg; exact ⟨-L / 2, hsupp⟩
    · exact absurd rfl hf
  have hLlog2 : L ≤ Real.log 2 := hL5.trans (by linarith [Real.log_two_gt_d9])
  have hmass : massOf (Finsupp.single g 1) = autocorr (compressedBump S) 0 := by
    rw [massOf_single, one_mul]; exact integral_norm_sq_ofReal (compressedBump S)
  have hmpos : 0 < autocorr (compressedBump S) 0 := by
    rw [autocorr_compressedBump_zero hS0]; exact mul_pos (inv_pos.mpr hS0) autocorr_pairBump_zero_pos
  have hn := normalizedArchEnergy_compressedBump_le hS1
  unfold normalizedArchEnergy at hn
  rw [div_le_iff₀ hmpos] at hn
  refine ⟨Finsupp.single g 1, fun f => by rw [Finsupp.single_apply]; split_ifs <;> norm_num,
    hw, blindOn_univ_of_windowSupported_le_log_two hLlog2 hw, by rwa [hmass], ?_⟩
  rw [nodeArchOnly_single, one_mul, archOnly_realTest, hmass]
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
