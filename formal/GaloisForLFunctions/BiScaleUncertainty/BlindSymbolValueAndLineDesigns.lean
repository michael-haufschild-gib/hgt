import GaloisForLFunctions.BiScaleUncertainty.TwoTowerBlindSlackEnclosure
import GaloisForLFunctions.BiScaleUncertainty.PowerGridMomentTheorem

/-!
# Exact blind symbol values, sub-square-root pole invisibility, and finite-cutoff line designs

For a node set `𝒩 ⊆ ℕ`, the blind symbol slack `BlindSymbolSlackOn 𝒩 M` asks that
`0 ≤ nodeArchOnly c + M * massOf c` on all nonnegative `𝒩`-blind combinations `c`, while
`ZeroPoleBlindSymbolSlackOn 𝒩 M` imposes `nodePoleMass c = 0`. This module establishes the exact
value theory of both cones, resolves pole visibility on all sub-square-root density node sets
(including smooth integers and the union of two power towers), and proves the finite-cutoff line
design realization theorem.

## Main Results

1. **Exact blind symbol values (`blindSymbolValue`, `zeroPoleBlindSymbolValue`):**
   For every node set `𝒩 ⊆ ℕ`, the sets of normalized archimedean symbol values
   `nodeArchOnly c / massOf c` on `BlindOn 𝒩` and on zero-pole `BlindOn 𝒩` are nonempty and bounded
   below by `EF.gammaBracket 0`. Their infima `blindSymbolValue 𝒩` and
   `zeroPoleBlindSymbolValue 𝒩` characterize all valid slacks:
   `BlindSymbolSlackOn 𝒩 M ↔ -blindSymbolValue 𝒩 ≤ M` and
   `ZeroPoleBlindSymbolSlackOn 𝒩 M ↔ -zeroPoleBlindSymbolValue 𝒩 ≤ M`.

2. **Pole invisibility for symbol slacks under sub-square-root density
   (`exists_blindOn_poleMass_eq_small_of_density`, `zeroPoleBlindSymbolSlackOn_iff_of_density`):**
   When `SubSqrtWindowDensity 𝒩` holds, the compressed distant pair `compressedCarrier k σ T`
   transports any prescribed pole mass `p` at arbitrarily small archimedean cost *and* arbitrarily
   small `L²` mass (`massOf d ≤ ε`). Hence for every `SubSqrtWindowDensity 𝒩` node set,
   `ZeroPoleBlindSymbolSlackOn 𝒩 M ↔ BlindSymbolSlackOn 𝒩 M` and
   `zeroPoleBlindSymbolValue 𝒩 = blindSymbolValue 𝒩`.
   Since `powerNodes q₁ ∪ powerNodes q₂` is contained in the `{q₁, q₂}`-smooth integers, it has
   sub-square-root window density (`subSqrtWindowDensity_two_towers`), so the pole constraint is
   completely invisible on the union of two power towers
   (`zeroPoleBlindSymbolSlackOn_two_towers_iff_blind`,
   `zeroPoleBlindSymbolValue_two_towers_eq`).

3. **Finite-cutoff line designs and symmetric two-tower enclosure
   (`exists_blindOn_of_lineDesign`, `blindSymbolValue_le_of_lineDesign_family`,
   `two_tower_blindSymbolValue_enclosure`):**
   Every finite frequency design `D` on `ℝ` of unit mass whose cosine moments
   `Σ_a w_a cos(ω_a log n)` vanish on the finite truncation `𝒩 ∩ [2, K]` is realized on the entire
   infinite node set `𝒩` by modulating a compressed bump whose correlation vanishes beyond
   `log (K + 1)`, with envelope energy overhead `O(1 / log (K + 1))`. On `powerNodes q₁ ∪ powerNodes q₂`,
   line duality and product designs enclose the common blind and zero-pole symbol value in
   `[max (m_{q₁} + η(q₁, q₂)) (m_{q₂} + η(q₂, q₁)), T(q₁, q₂)]`.
-/

open MeasureTheory Set Filter Topology Complex Finsupp
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. Exact blind and zero-pole symbol values -/

/-- Normalized archimedean symbol values `nodeArchOnly c / massOf c` over nonnegative `𝒩`-blind
combinations of positive mass. -/
def blindSymbolSet (𝒩 : Set ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn 𝒩 c ∧ 0 < massOf c ∧
    x = nodeArchOnly c / massOf c}

/-- The exact blind symbol value `inf { nodeArchOnly c / massOf c }` on `𝒩`-blind combinations. -/
def blindSymbolValue (𝒩 : Set ℕ) : ℝ := sInf (blindSymbolSet 𝒩)

/-- Normalized archimedean symbol values `nodeArchEnergy c / massOf c` over nonnegative zero-pole
`𝒩`-blind combinations of positive mass. -/
def zeroPoleBlindSymbolSet (𝒩 : Set ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn 𝒩 c ∧ nodePoleMass c = 0 ∧
    0 < massOf c ∧ x = nodeArchEnergy c / massOf c}

/-- The exact zero-pole blind symbol value `inf { nodeArchEnergy c / massOf c }` on zero-pole
`𝒩`-blind combinations. -/
def zeroPoleBlindSymbolValue (𝒩 : Set ℕ) : ℝ := sInf (zeroPoleBlindSymbolSet 𝒩)

/-- The anomaly `EF.gammaBracket 0` is a universal lower bound on `nodeArchOnly c / massOf c`. -/
theorem gammaBracket_zero_mul_massOf_le_nodeArchOnly {c : WeilTestFn →₀ ℝ}
    (hc : ∀ f, 0 ≤ c f) : EF.gammaBracket 0 * massOf c ≤ nodeArchOnly c := by
  have h := sum_pole_add_anomaly_le c hc
  rw [← nodePoleMass_eq_sum, ← massOf, sum_weilArchRe_eq, ← nodeArchEnergy_eq] at h
  rw [nodeArchOnly]
  linarith

theorem zeroPoleBlindSymbolSet_subset_blindSymbolSet (𝒩 : Set ℕ) :
    zeroPoleBlindSymbolSet 𝒩 ⊆ blindSymbolSet 𝒩 := by
  rintro x ⟨c, hc, hb, hp, hm, rfl⟩
  refine ⟨c, hc, hb, hm, ?_⟩
  rw [nodeArchOnly, hp, sub_zero]

theorem blindSymbolSet_bddBelow (𝒩 : Set ℕ) : BddBelow (blindSymbolSet 𝒩) := by
  refine ⟨EF.gammaBracket 0, ?_⟩
  rintro x ⟨c, hc, -, hm, rfl⟩
  exact (le_div_iff₀ hm).mpr (gammaBracket_zero_mul_massOf_le_nodeArchOnly hc)

theorem zeroPoleBlindSymbolSet_bddBelow (𝒩 : Set ℕ) :
    BddBelow (zeroPoleBlindSymbolSet 𝒩) :=
  (blindSymbolSet_bddBelow 𝒩).mono (zeroPoleBlindSymbolSet_subset_blindSymbolSet 𝒩)

/-- The corpus bump as a Weil test is blind at all integer nodes `n ≥ 2` and has positive mass. -/
def pairBumpTestFn : WeilTestFn :=
  realTest pairBump contDiff_pairBump hasCompactSupport_pairBump

theorem logVector_pairBumpTestFn : logVector pairBumpTestFn = 0 := by
  ext j
  rw [logVector_apply]
  change logValue (realTest pairBump contDiff_pairBump hasCompactSupport_pairBump).1 (j : ℕ) = 0
  rw [logValue_realTest]
  have hlog2 : (1 : ℝ) / 5 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogn : Real.log 2 ≤ Real.log (j : ℕ) := Real.log_le_log two_pos (by exact_mod_cast j.2)
  rw [autocorr_pairBump_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)]
  ring

theorem massOf_single_pairBumpTestFn :
    massOf (Finsupp.single pairBumpTestFn 1) = autocorr pairBump 0 := by
  rw [massOf_single, one_mul]
  exact integral_norm_sq_ofReal pairBump

/-- There exists a nonnegative combination blind at all integer nodes with zero pole mass and
positive mass. -/
theorem exists_all_blind_zeroPole_massOf_pos :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ nodeVector c = 0 ∧ nodePoleMass c = 0 ∧
      0 < massOf c := by
  classical
  set c₀ := Finsupp.single pairBumpTestFn (1 : ℝ)
  have hc₀ : ∀ f, 0 ≤ c₀ f := fun f => by
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  have hv₀ : nodeVector c₀ = 0 := by
    rw [nodeVector_eq, linearCombination_single, logVector_pairBumpTestFn, smul_zero]
  have hm₀ : 0 < massOf c₀ := by
    rw [massOf_single_pairBumpTestFn]; exact autocorr_pairBump_zero_pos
  obtain ⟨d, hd, hvd, hpd⟩ := exists_blind_nodePoleMass_eq (-nodePoleMass c₀)
  refine ⟨c₀ + d, fun f => add_nonneg (hc₀ f) (hd f), ?_, ?_, ?_⟩
  · rw [nodeVector_add, hv₀, hvd, add_zero]
  · rw [nodePoleMass_add, hpd, add_neg_cancel]
  · rw [massOf_add]
    exact lt_of_lt_of_le hm₀ (le_add_of_nonneg_right (massOf_nonneg hd))

theorem zeroPoleBlindSymbolSet_nonempty (𝒩 : Set ℕ) :
    (zeroPoleBlindSymbolSet 𝒩).Nonempty := by
  obtain ⟨c, hc, hv, hp, hm⟩ := exists_all_blind_zeroPole_massOf_pos
  exact ⟨nodeArchEnergy c / massOf c, c, hc, fun j _ => by rw [hv]; rfl, hp, hm, rfl⟩

theorem blindSymbolSet_nonempty (𝒩 : Set ℕ) : (blindSymbolSet 𝒩).Nonempty :=
  (zeroPoleBlindSymbolSet_nonempty 𝒩).mono (zeroPoleBlindSymbolSet_subset_blindSymbolSet 𝒩)

theorem gammaBracket_zero_le_blindSymbolValue (𝒩 : Set ℕ) :
    EF.gammaBracket 0 ≤ blindSymbolValue 𝒩 :=
  le_csInf (blindSymbolSet_nonempty 𝒩) fun _ ⟨_, hc, _, hm, h⟩ =>
    h ▸ (le_div_iff₀ hm).mpr (gammaBracket_zero_mul_massOf_le_nodeArchOnly hc)

theorem blindSymbolValue_le_zeroPoleBlindSymbolValue (𝒩 : Set ℕ) :
    blindSymbolValue 𝒩 ≤ zeroPoleBlindSymbolValue 𝒩 :=
  csInf_le_csInf (blindSymbolSet_bddBelow 𝒩) (zeroPoleBlindSymbolSet_nonempty 𝒩)
    (zeroPoleBlindSymbolSet_subset_blindSymbolSet 𝒩)

theorem gammaBracket_zero_le_zeroPoleBlindSymbolValue (𝒩 : Set ℕ) :
    EF.gammaBracket 0 ≤ zeroPoleBlindSymbolValue 𝒩 :=
  (gammaBracket_zero_le_blindSymbolValue 𝒩).trans (blindSymbolValue_le_zeroPoleBlindSymbolValue 𝒩)

theorem blindSymbolValue_mono {𝒩 𝒩' : Set ℕ} (h : 𝒩 ⊆ 𝒩') :
    blindSymbolValue 𝒩 ≤ blindSymbolValue 𝒩' :=
  csInf_le_csInf (blindSymbolSet_bddBelow 𝒩) (blindSymbolSet_nonempty 𝒩')
    fun _ ⟨c, hc, hb, hm, hx⟩ => ⟨c, hc, blindOn_of_subset h hb, hm, hx⟩

theorem zeroPoleBlindSymbolValue_mono {𝒩 𝒩' : Set ℕ} (h : 𝒩 ⊆ 𝒩') :
    zeroPoleBlindSymbolValue 𝒩 ≤ zeroPoleBlindSymbolValue 𝒩' :=
  csInf_le_csInf (zeroPoleBlindSymbolSet_bddBelow 𝒩) (zeroPoleBlindSymbolSet_nonempty 𝒩')
    fun _ ⟨c, hc, hb, hp, hm, hx⟩ => ⟨c, hc, blindOn_of_subset h hb, hp, hm, hx⟩

/-- If `massOf c = 0` for a nonnegative combination `c`, then `nodeArchOnly c = 0`. -/
theorem nodeArchOnly_eq_zero_of_massOf_eq_zero {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hm : massOf c = 0) : nodeArchOnly c = 0 := by
  have hG0 : ∀ r, 0 ≤ combinationSpectralDensity c r := combinationSpectralDensity_nonneg hc
  have hGi : Integrable (combinationSpectralDensity c) := integrable_combinationSpectralDensity c
  have hGm : ∫ r, combinationSpectralDensity c r = 0 := by
    rw [integral_combinationSpectralDensity, hm, mul_zero]
  have hGz : combinationSpectralDensity c =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hG0 hGi).mp hGm
  have hGa : ∫ r, combinationSpectralDensity c r * EF.gammaBracket r = 0 := by
    have h0 : (fun r => combinationSpectralDensity c r * EF.gammaBracket r) =ᵐ[volume]
        fun _ => (0 : ℝ) :=
      hGz.mono fun r hr => by
        show combinationSpectralDensity c r * EF.gammaBracket r = 0
        rw [Pi.zero_apply] at hr; rw [hr, zero_mul]
    rw [integral_congr_ae h0, integral_zero]
  have h1 := integral_combinationSpectralDensity_mul_gammaBracket c
  have hpi : 0 < 2 * π := by positivity
  nlinarith

/-- `blindSymbolValue 𝒩 * massOf c ≤ nodeArchOnly c` for every nonnegative `𝒩`-blind
combination. -/
theorem blindSymbolValue_mul_massOf_le {𝒩 : Set ℕ} {c : WeilTestFn →₀ ℝ}
    (hc : ∀ f, 0 ≤ c f) (hb : BlindOn 𝒩 c) :
    blindSymbolValue 𝒩 * massOf c ≤ nodeArchOnly c := by
  rcases eq_or_lt_of_le (massOf_nonneg hc) with hm0 | hm
  · rw [← hm0, mul_zero, nodeArchOnly_eq_zero_of_massOf_eq_zero hc hm0.symm]
  · have hle : blindSymbolValue 𝒩 ≤ nodeArchOnly c / massOf c :=
      csInf_le (blindSymbolSet_bddBelow 𝒩) ⟨c, hc, hb, hm, rfl⟩
    exact (le_div_iff₀ hm).mp hle

/-- `zeroPoleBlindSymbolValue 𝒩 * massOf c ≤ nodeArchEnergy c` for every nonnegative zero-pole
`𝒩`-blind combination. -/
theorem zeroPoleBlindSymbolValue_mul_massOf_le {𝒩 : Set ℕ} {c : WeilTestFn →₀ ℝ}
    (hc : ∀ f, 0 ≤ c f) (hb : BlindOn 𝒩 c) (hp : nodePoleMass c = 0) :
    zeroPoleBlindSymbolValue 𝒩 * massOf c ≤ nodeArchEnergy c := by
  rcases eq_or_lt_of_le (massOf_nonneg hc) with hm0 | hm
  · have hA0 := nodeArchOnly_eq_zero_of_massOf_eq_zero hc hm0.symm
    rw [nodeArchOnly, hp, sub_zero] at hA0
    rw [← hm0, mul_zero, hA0]
  · have hle : zeroPoleBlindSymbolValue 𝒩 ≤ nodeArchEnergy c / massOf c :=
      csInf_le (zeroPoleBlindSymbolSet_bddBelow 𝒩) ⟨c, hc, hb, hp, hm, rfl⟩
    exact (le_div_iff₀ hm).mp hle

/-- **Exact characterization of `BlindSymbolSlackOn`.** A level `M` is a valid blind symbol slack on
`𝒩` if and only if `-blindSymbolValue 𝒩 ≤ M`. -/
theorem blindSymbolSlackOn_iff_blindSymbolValue (𝒩 : Set ℕ) (M : ℝ) :
    BlindSymbolSlackOn 𝒩 M ↔ -blindSymbolValue 𝒩 ≤ M := by
  constructor
  · intro h
    have hle : -M ≤ blindSymbolValue 𝒩 :=
      le_csInf (blindSymbolSet_nonempty 𝒩) fun x ⟨c, hc, hb, hm, hx⟩ => by
        rw [hx, le_div_iff₀ hm]
        linarith [h c hc hb]
    linarith
  · intro h c hc hb
    have := blindSymbolValue_mul_massOf_le hc hb
    have := massOf_nonneg hc
    nlinarith

/-- **Exact characterization of `ZeroPoleBlindSymbolSlackOn`.** A level `M` is a valid zero-pole
blind symbol slack on `𝒩` if and only if `-zeroPoleBlindSymbolValue 𝒩 ≤ M`. -/
theorem zeroPoleBlindSymbolSlackOn_iff_zeroPoleBlindSymbolValue (𝒩 : Set ℕ) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn 𝒩 M ↔ -zeroPoleBlindSymbolValue 𝒩 ≤ M := by
  constructor
  · intro h
    have hle : -M ≤ zeroPoleBlindSymbolValue 𝒩 :=
      le_csInf (zeroPoleBlindSymbolSet_nonempty 𝒩) fun x ⟨c, hc, hb, hp, hm, hx⟩ => by
        rw [hx, le_div_iff₀ hm]
        linarith [h c hc hb hp]
    linarith
  · intro h c hc hb hp
    have := zeroPoleBlindSymbolValue_mul_massOf_le hc hb hp
    have := massOf_nonneg hc
    nlinarith

theorem isLeast_blindSymbolSlackOn (𝒩 : Set ℕ) :
    IsLeast {M | BlindSymbolSlackOn 𝒩 M} (-blindSymbolValue 𝒩) :=
  ⟨(blindSymbolSlackOn_iff_blindSymbolValue 𝒩 _).mpr le_rfl,
    fun _ hM => (blindSymbolSlackOn_iff_blindSymbolValue 𝒩 _).mp hM⟩

theorem isLeast_zeroPoleBlindSymbolSlackOn (𝒩 : Set ℕ) :
    IsLeast {M | ZeroPoleBlindSymbolSlackOn 𝒩 M} (-zeroPoleBlindSymbolValue 𝒩) :=
  ⟨(zeroPoleBlindSymbolSlackOn_iff_zeroPoleBlindSymbolValue 𝒩 _).mpr le_rfl,
    fun _ hM => (zeroPoleBlindSymbolSlackOn_iff_zeroPoleBlindSymbolValue 𝒩 _).mp hM⟩

/-! ### 2. Sub-square-root density pole invisibility for symbol slacks and two power towers -/

/-- The `L²` norm squared of the compressed carrier `compressedCarrier k σ T` is
`2 (k + 1)⁻¹ autocorr pairBump 0` once `1 ≤ T`. -/
theorem integral_norm_sq_compressedCarrier (k : ℕ) {σ T : ℝ} (hσ : σ ^ 2 = 1) (hT : 1 ≤ T) :
    ∫ x, ‖(compressedCarrier k σ T).1 x‖ ^ 2 =
      2 * (((k : ℝ) + 1)⁻¹ * autocorr pairBump 0) := by
  have hL0 := one_add_nat_pos k
  have hfar : 1 / (5 * ((k : ℝ) + 1)) < |T| := by
    rw [abs_of_pos (by linarith)]
    have : 1 / (5 * ((k : ℝ) + 1)) ≤ 1 / 5 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have := Nat.cast_nonneg (α := ℝ) k; linarith
    linarith
  unfold compressedCarrier
  change ∫ x, ‖((subtractCopy (compressedBump ((k : ℝ) + 1)) σ T x : ℝ) : ℂ)‖ ^ 2 = _
  rw [integral_norm_sq_ofReal, autocorr_subtractCopy (contDiff_compressedBump _).continuous
    (hasCompactSupport_compressedBump hL0), zero_sub, zero_add, autocorr_neg,
    autocorr_compressedBump_eq_zero hL0 hfar, hσ, autocorr_compressedBump_zero hL0]
  ring

theorem integral_norm_sq_compressedCarrier_le (k : ℕ) {σ T : ℝ} (hσ : σ ^ 2 = 1) (hT : 1 ≤ T) :
    ∫ x, ‖(compressedCarrier k σ T).1 x‖ ^ 2 ≤
      ((k : ℝ) + 1)⁻¹ * (compressedArchConstant * (1 + Real.log ((k : ℝ) + 1))) := by
  rw [integral_norm_sq_compressedCarrier k hσ hT]
  have hL1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hLinv : 0 ≤ ((k : ℝ) + 1)⁻¹ := by positivity
  have hlog : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg hL1
  have hb0 : 0 ≤ autocorr pairBump 0 := autocorr_pairBump_zero_pos.le
  have h1 : 2 * autocorr pairBump 0 ≤ compressedArchConstant := by
    unfold compressedArchConstant
    have hI : 0 ≤ ∫ x, |autocorr pairBump x| := integral_nonneg fun _ => abs_nonneg _
    have hd : 0 < 1 - Real.exp (-2) := by
      have := Real.exp_lt_one_iff.mpr (show (-2 : ℝ) < 0 by norm_num); linarith
    have hcI : 0 ≤ 2 / (1 - Real.exp (-2)) * ∫ x, |autocorr pairBump x| := by positivity
    have hga : 0 ≤ 2 * |EF.gammaBracket 0| * autocorr pairBump 0 := by positivity
    have hE : 0 ≤ 2 * autocorr pairBump 0 * |compressedEnergyConstant| := by positivity
    nlinarith
  have h2 : compressedArchConstant ≤ compressedArchConstant * (1 + Real.log ((k : ℝ) + 1)) := by
    have hC := compressedArchConstant_nonneg
    nlinarith
  calc
    2 * (((k : ℝ) + 1)⁻¹ * autocorr pairBump 0) =
        ((k : ℝ) + 1)⁻¹ * (2 * autocorr pairBump 0) := by ring
    _ ≤ ((k : ℝ) + 1)⁻¹ * (compressedArchConstant * (1 + Real.log ((k : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) hLinv

/-- **Pole mass is free with small mass under sub-square-root window density.** Every real pole mass
`p` is carried by a nonnegative `𝒩`-blind combination `d` whose archimedean symbol part
`|nodeArchOnly d|` and mass `massOf d` are both at most `ε`. -/
theorem exists_blindOn_poleMass_eq_small_of_density {𝒩 : Set ℕ}
    (h𝒩 : SubSqrtWindowDensity 𝒩) (p : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ d f) ∧ BlindOn 𝒩 d ∧ nodePoleMass d = p ∧
      |nodeArchOnly d| ≤ ε ∧ massOf d ≤ ε := by
  classical
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, fun _ => le_rfl, fun j _ => by simp [nodeVector_eq], by simp [nodePoleMass],
      by simp [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, hε.le],
      by simp [massOf_eq_linearCombination, hε.le]⟩
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
  have hcost := transport_cost_le hε hκ hL1 (by linarith) hden' hPabs hP0
    (le_of_eq (abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (by linarith))
      (mul_nonneg compressedArchConstant_nonneg (by linarith [Real.log_nonneg hL1])))))
  rw [← abs_div, abs_of_pos hsign, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (by linarith))
    (mul_nonneg compressedArchConstant_nonneg (by linarith [Real.log_nonneg hL1])))] at hcost
  refine ⟨Finsupp.single g (p / P), fun h => ?_, fun j hj => ?_, ?_, ?_, ?_⟩
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
  · rw [nodeArchOnly_single, abs_mul, abs_of_pos hsign]
    exact (mul_le_mul_of_nonneg_left hA hsign.le).trans hcost
  · rw [massOf_single]
    exact (mul_le_mul_of_nonneg_left
      (integral_norm_sq_compressedCarrier_le k hσsq (by linarith)) hsign.le).trans hcost

/-- **Sub-square-root density pole invisibility for symbol slacks.** On any node set `𝒩` with
`SubSqrtWindowDensity 𝒩`, the zero-pole constraint does not improve the blind symbol slack at any
level `M`. -/
theorem zeroPoleBlindSymbolSlackOn_iff_of_density {𝒩 : Set ℕ}
    (h𝒩 : SubSqrtWindowDensity 𝒩) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn 𝒩 M ↔ BlindSymbolSlackOn 𝒩 M := by
  refine ⟨fun h c₁ hc₁ hb₁ => ?_, fun h => h.zeroPole⟩
  by_contra hlt
  push Not at hlt
  set δ : ℝ := -(nodeArchOnly c₁ + M * massOf c₁) with hδ
  have hδpos : 0 < δ := by linarith
  set η : ℝ := δ / (2 * (1 + |M|)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨d, hd, hbd, hpd, had, hmd⟩ :=
    exists_blindOn_poleMass_eq_small_of_density h𝒩 (-nodePoleMass c₁) hηpos
  have hcd : ∀ f, 0 ≤ (c₁ + d) f := fun f => add_nonneg (hc₁ f) (hd f)
  have hbcd : BlindOn 𝒩 (c₁ + d) := fun j hj => by
    rw [nodeVector_add, Finsupp.add_apply, hb₁ j hj, hbd j hj, add_zero]
  have hpcd : nodePoleMass (c₁ + d) = 0 := by rw [nodePoleMass_add, hpd, add_neg_cancel]
  have hpos := h (c₁ + d) hcd hbcd hpcd
  have hE : nodeArchEnergy (c₁ + d) = nodeArchOnly c₁ + nodeArchOnly d := by
    rw [← nodeArchOnly_add, nodeArchOnly, hpcd, sub_zero]
  rw [hE, massOf_add] at hpos
  have hmd0 : 0 ≤ massOf d := massOf_nonneg hd
  have h2 : nodeArchOnly d ≤ η := (le_abs_self _).trans had
  have h3 : M * massOf d ≤ |M| * η :=
    (mul_le_mul_of_nonneg_right (le_abs_self M) hmd0).trans
      (mul_le_mul_of_nonneg_left hmd (abs_nonneg M))
  have h4 : (1 + |M|) * η = δ / 2 := by rw [hη]; field_simp
  linarith

/-- Under `SubSqrtWindowDensity 𝒩`, the zero-pole and unconstrained blind symbol values coincide. -/
theorem zeroPoleBlindSymbolValue_eq_of_density {𝒩 : Set ℕ} (h𝒩 : SubSqrtWindowDensity 𝒩) :
    zeroPoleBlindSymbolValue 𝒩 = blindSymbolValue 𝒩 := by
  have h := zeroPoleBlindSymbolSlackOn_iff_of_density h𝒩 (-zeroPoleBlindSymbolValue 𝒩)
  rw [zeroPoleBlindSymbolSlackOn_iff_zeroPoleBlindSymbolValue,
    blindSymbolSlackOn_iff_blindSymbolValue] at h
  exact le_antisymm (by linarith [h.mp le_rfl]) (blindSymbolValue_le_zeroPoleBlindSymbolValue 𝒩)

theorem SubSqrtWindowDensity.mono {𝒩₁ 𝒩₂ : Set ℕ} (h : 𝒩₁ ⊆ 𝒩₂)
    (h₂ : SubSqrtWindowDensity 𝒩₂) : SubSqrtWindowDensity 𝒩₁ := fun M => by
  obtain ⟨X, hMX, F, hcov, hden⟩ := h₂ M
  exact ⟨X, hMX, F, fun n hn => hcov n (h hn), hden⟩

/-- The union of two power towers `powerNodes q₁ ∪ powerNodes q₂` is contained in the
`(q₁.primeFactors ∪ q₂.primeFactors)`-smooth integers (for `n ≥ 2`), hence has sub-square-root
window density. -/
theorem subSqrtWindowDensity_two_towers (q₁ q₂ : ℕ) :
    SubSqrtWindowDensity (powerNodes q₁ ∪ powerNodes q₂) := by
  refine (subSqrtWindowDensity_smooth (q₁.primeFactors ∪ q₂.primeFactors)).mono ?_
  rintro n (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) p hp
  · rw [Nat.mem_primeFactors] at hp
    have hq₁ : q₁ ≠ 0 := fun h0 => hp.2.2 (by rw [h0, zero_pow (by omega)])
    exact Finset.mem_union_left _
      (Nat.mem_primeFactors.mpr ⟨hp.1, hp.1.dvd_of_dvd_pow hp.2.1, hq₁⟩)
  · rw [Nat.mem_primeFactors] at hp
    have hq₂ : q₂ ≠ 0 := fun h0 => hp.2.2 (by rw [h0, zero_pow (by omega)])
    exact Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hp.1, hp.1.dvd_of_dvd_pow hp.2.1, hq₂⟩)

/-- **Pole invisibility on the union of two power towers.** For any `q₁, q₂ : ℕ` and any `M : ℝ`,
the zero-pole blind symbol slack on `powerNodes q₁ ∪ powerNodes q₂` is equivalent to the
unconstrained blind symbol slack. -/
theorem zeroPoleBlindSymbolSlackOn_two_towers_iff_blind (q₁ q₂ : ℕ) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn (powerNodes q₁ ∪ powerNodes q₂) M ↔
      BlindSymbolSlackOn (powerNodes q₁ ∪ powerNodes q₂) M :=
  zeroPoleBlindSymbolSlackOn_iff_of_density (subSqrtWindowDensity_two_towers q₁ q₂) M

/-- **Equality of zero-pole and blind symbol values on two power towers.** -/
theorem zeroPoleBlindSymbolValue_two_towers_eq (q₁ q₂ : ℕ) :
    zeroPoleBlindSymbolValue (powerNodes q₁ ∪ powerNodes q₂) =
      blindSymbolValue (powerNodes q₁ ∪ powerNodes q₂) :=
  zeroPoleBlindSymbolValue_eq_of_density (subSqrtWindowDensity_two_towers q₁ q₂)

/-- **Pole invisibility on `S`-smooth integers.** -/
theorem zeroPoleBlindSymbolSlackOn_smooth_iff_blind (S : Finset ℕ) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn {n | n.primeFactors ⊆ S} M ↔
      BlindSymbolSlackOn {n | n.primeFactors ⊆ S} M :=
  zeroPoleBlindSymbolSlackOn_iff_of_density (subSqrtWindowDensity_smooth S) M

theorem zeroPoleBlindSymbolValue_smooth_eq (S : Finset ℕ) :
    zeroPoleBlindSymbolValue {n | n.primeFactors ⊆ S} =
      blindSymbolValue {n | n.primeFactors ⊆ S} :=
  zeroPoleBlindSymbolValue_eq_of_density (subSqrtWindowDensity_smooth S)

/-! ### 3. Finite-cutoff line designs and the symmetric two-tower enclosure -/

/-- The cosine moment `Σ_{(w, ω) ∈ D} w cos(ω log n)` of a finite frequency design `D` on `ℝ`
at the integer node `n`. -/
def lineDesignMoment (D : List (ℝ × ℝ)) (n : ℕ) : ℝ :=
  (D.map fun a => a.1 * Real.cos (a.2 * Real.log n)).sum

/-- The archimedean symbol value `Σ_{(w, ω) ∈ D} w γ(ω)` of a finite frequency design `D` on `ℝ`. -/
def lineDesignGamma (D : List (ℝ × ℝ)) : ℝ :=
  (D.map fun a => a.1 * EF.gammaBracket a.2).sum

/-- Cosine/sine modulations at the frequencies `ω` of a line design `D`. -/
def lineDesignCombination {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (D : List (ℝ × ℝ)) : WeilTestFn →₀ ℝ :=
  (D.map fun a => Finsupp.single (cosTest hf hfc a.2) a.1 +
    Finsupp.single (sinTest hf hfc a.2) a.1).sum

theorem lineDesignCombination_nonneg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {D : List (ℝ × ℝ)} (hD : ∀ a ∈ D, 0 ≤ a.1) (g : WeilTestFn) :
    0 ≤ lineDesignCombination hf hfc D g := by
  classical
  induction D with
  | nil => simp [lineDesignCombination]
  | cons a D ih =>
    have ha := hD a (List.mem_cons_self ..)
    have ht := ih fun b hb => hD b (List.mem_cons_of_mem _ hb)
    simp only [lineDesignCombination, List.map_cons, List.sum_cons, Finsupp.add_apply] at ht ⊢
    rw [Finsupp.single_apply, Finsupp.single_apply]
    have h1 : 0 ≤ (if cosTest hf hfc a.2 = g then a.1 else 0) := by split_ifs <;> simp [ha]
    have h2 : 0 ≤ (if sinTest hf hfc a.2 = g then a.1 else 0) := by split_ifs <;> simp [ha]
    linarith

theorem linearCombination_lineDesignCombination (φ : WeilTestFn → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (D : List (ℝ × ℝ)) :
    linearCombination ℝ φ (lineDesignCombination hf hfc D) =
      (D.map fun a => a.1 * (φ (cosTest hf hfc a.2) + φ (sinTest hf hfc a.2))).sum := by
  induction D with
  | nil => simp [lineDesignCombination]
  | cons a D ih =>
    simp only [lineDesignCombination, List.map_cons, List.sum_cons, map_add,
      linearCombination_single, smul_eq_mul] at ih ⊢
    rw [ih]; ring

theorem nodeArchOnly_lineDesignCombination_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {D : List (ℝ × ℝ)} (hD : ∀ a ∈ D, 0 ≤ a.1) :
    nodeArchOnly (lineDesignCombination hf hfc D) ≤
      autocorr f 0 * lineDesignGamma D + designMass D * biScaleLevyEnergy f := by
  rw [nodeArchOnly_eq_linearCombination, linearCombination_lineDesignCombination]
  induction D with
  | nil => simp [lineDesignGamma, designMass]
  | cons a D ih =>
    have ha := hD a (List.mem_cons_self ..)
    have ht := ih fun b hb => hD b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons, lineDesignGamma, designMass] at ht ⊢
    have hpair := mul_le_mul_of_nonneg_left (archOnly_cos_add_sin_le hf hfc a.2) ha
    linarith

/-- **Finite-cutoff line-design realization theorem.** Any finite frequency design `D` on `ℝ` of
unit mass whose cosine moments vanish on `𝒩 ∩ [2, K]` is realized on the entire node set `𝒩` by
modulating a compressed bump whose correlation vanishes past `log (K + 1)`, with envelope energy
overhead `O(1 / log (K + 1))`. -/
theorem exists_blindOn_of_lineDesign :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (𝒩 : Set ℕ) {K : ℕ}, 1 ≤ K → ∀ (D : List (ℝ × ℝ)),
      (∀ a ∈ D, 0 ≤ a.1) → designMass D = 1 →
      (∀ n ∈ 𝒩, 2 ≤ n → n ≤ K → lineDesignMoment D n = 0) →
      ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn 𝒩 c ∧ 0 < massOf c ∧
        nodeArchOnly c ≤ (lineDesignGamma D + E / Real.log (K + 1)) * massOf c := by
  obtain ⟨Mb, hMb, hinc⟩ := exists_autocorr_increment_linear_bound contDiff_pairBump
    hasCompactSupport_pairBump
  have hb0 := autocorr_pairBump_zero_pos
  have hK0 : 0 ≤ Mb * archWeightFirstMoment := mul_nonneg hMb archWeightFirstMoment_nonneg
  set E : ℝ := Mb * archWeightFirstMoment / (4 * autocorr pairBump 0) with hE
  refine ⟨E, by positivity, fun 𝒩 {K} hK D hD0 hD1 hDm => ?_⟩
  have hK2 : (2 : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hK
  have hℓ : 0 < Real.log ((K : ℝ) + 1) := Real.log_pos (by linarith)
  set δ : ℝ := 1 / (4 * Real.log ((K : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hf := contDiff_compressedBump δ
  have hfc := hasCompactSupport_compressedBump hδ
  have hf0 : autocorr (compressedBump δ) 0 =
      4 * Real.log ((K : ℝ) + 1) * autocorr pairBump 0 := by
    rw [autocorr_compressedBump_zero hδ, hδdef]; field_simp
  have hJ : biScaleLevyEnergy (compressedBump δ) ≤ Mb * archWeightFirstMoment :=
    biScaleLevyEnergy_sourceRescale_le contDiff_pairBump hasCompactSupport_pairBump hinc hδ
  set c := lineDesignCombination hf hfc D
  have hmass : massOf c = autocorr (compressedBump δ) 0 := by
    rw [massOf_eq_linearCombination, linearCombination_lineDesignCombination]
    have e : ∀ a : ℝ × ℝ, a.1 * ((∫ x, ‖(cosTest hf hfc a.2).1 x‖ ^ 2) +
        ∫ x, ‖(sinTest hf hfc a.2).1 x‖ ^ 2) = autocorr (compressedBump δ) 0 * a.1 := fun a => by
      linear_combination a.1 * massTerm_cos_add_sin hf hfc a.2
    simp only [e]
    rw [List.sum_map_mul_left, ← designMass, hD1, mul_one]
  refine ⟨c, lineDesignCombination_nonneg hf hfc hD0, ?_, ?_, ?_⟩
  · rintro ⟨n, hn2⟩ hn
    rw [nodeVector_apply_eq_linearCombination, linearCombination_lineDesignCombination]
    change (D.map fun a => a.1 * (logValue (cosTest hf hfc a.2).1 n +
      logValue (sinTest hf hfc a.2).1 n)).sum = 0
    have e : ∀ a : ℝ × ℝ, a.1 * (logValue (cosTest hf hfc a.2).1 n +
        logValue (sinTest hf hfc a.2).1 n) =
        2 * autocorr (compressedBump δ) (Real.log n) / Real.sqrt n *
          (a.1 * Real.cos (a.2 * Real.log n)) := fun a => by
      simp only [cosTest, sinTest, logValue_realTest]
      have h := autocorr_cosineSource_add_sineSource hf.continuous hfc a.2 (Real.log n)
      linear_combination (2 * a.1 / Real.sqrt n) * h
    simp only [e]
    rw [List.sum_map_mul_left]
    by_cases hnK : n ≤ K
    · rw [← lineDesignMoment, hDm n hn hn2 hnK, mul_zero]
    · have hfar : 1 / (5 * δ) < |Real.log (n : ℝ)| := by
        have hKn : (K : ℝ) + 1 ≤ n := by exact_mod_cast (show K + 1 ≤ n by omega)
        have hlogKn : Real.log ((K : ℝ) + 1) ≤ Real.log n := Real.log_le_log (by linarith) hKn
        rw [abs_of_pos (by linarith), hδdef,
          show 1 / (5 * (1 / (4 * Real.log ((K : ℝ) + 1)))) =
            4 / 5 * Real.log ((K : ℝ) + 1) by field_simp]
        linarith
      rw [autocorr_compressedBump_eq_zero hδ hfar]
      simp
  · rw [hmass, hf0]; positivity
  · have harch := nodeArchOnly_lineDesignCombination_le hf hfc hD0
    rw [hD1, one_mul] at harch
    rw [hmass]
    have hE' : Mb * archWeightFirstMoment =
        (E / Real.log ((K : ℝ) + 1)) * autocorr (compressedBump δ) 0 := by
      rw [hE, hf0]; field_simp
    linarith

/-- **Finite-cutoff line-design upper bound on `blindSymbolValue`.** If a sequence of unit-mass
line designs `D K` has vanishing cosine moments on `𝒩 ∩ [2, K]` and `lineDesignGamma (D K) ≤ V`,
then `blindSymbolValue 𝒩 ≤ V`. -/
theorem blindSymbolValue_le_of_lineDesign_family (𝒩 : Set ℕ) (V : ℝ)
    (hD : ∀ K : ℕ, 1 ≤ K → ∃ D : List (ℝ × ℝ), (∀ a ∈ D, 0 ≤ a.1) ∧ designMass D = 1 ∧
      (∀ n ∈ 𝒩, 2 ≤ n → n ≤ K → lineDesignMoment D n = 0) ∧ lineDesignGamma D ≤ V) :
    blindSymbolValue 𝒩 ≤ V := by
  by_contra hlt
  push Not at hlt
  set ε : ℝ := (blindSymbolValue 𝒩 - V) / 2 with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨E, hE0, hreal⟩ := exists_blindOn_of_lineDesign
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (E / ε))
  have hK1 : 1 ≤ K := by
    have : 1 ≤ Real.exp (E / ε) := Real.one_le_exp (by positivity)
    have : (1 : ℝ) < K := lt_of_le_of_lt this hK
    exact_mod_cast this.le
  have hlogK : E / ε < Real.log ((K : ℝ) + 1) := by
    have h1 : Real.exp (E / ε) < (K : ℝ) + 1 := by linarith
    rw [← Real.log_exp (E / ε)]
    exact Real.log_lt_log (Real.exp_pos _) h1
  have hEK : E / Real.log ((K : ℝ) + 1) ≤ ε := by
    have hℓ : 0 < Real.log ((K : ℝ) + 1) := by
      have : (2 : ℝ) ≤ (K : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hK1
      exact Real.log_pos (by linarith)
    rw [div_le_iff₀ hℓ]
    rw [div_lt_iff₀ hεpos] at hlogK
    linarith
  obtain ⟨D, hD0, hD1, hDm, hDV⟩ := hD K hK1
  obtain ⟨c, hc, hb, hm, hle⟩ := hreal 𝒩 hK1 D hD0 hD1 hDm
  have := blindSymbolValue_mul_massOf_le hc hb
  nlinarith

/-- Every line certificate for `q₁, q₂` bounds `blindSymbolValue (powerNodes q₁ ∪ powerNodes q₂)`
from below. -/
theorem LineCertificate.value_le_blindSymbolValue {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂)
    (C : LineCertificate q₁ q₂) :
    C.value ≤ blindSymbolValue (powerNodes q₁ ∪ powerNodes q₂) := by
  have h := (blindSymbolSlackOn_iff_blindSymbolValue (powerNodes q₁ ∪ powerNodes q₂) (-C.value)).mp
    (blindSymbolSlackOn_two_towers_of_certificate hq₁ hq₂ C)
  linarith

/-- **Symmetric two-tower blind and zero-pole symbol value enclosure.** For any `q₁, q₂ ≥ 2`, the
blind symbol value and zero-pole blind symbol value on `powerNodes q₁ ∪ powerNodes q₂` coincide and
lie in `[max (m_{q₁} + η(q₁, q₂)) (m_{q₂} + η(q₂, q₁)), T(q₁, q₂)]`. -/
theorem two_tower_blindSymbolValue_enclosure {q₁ q₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 2 ≤ q₂) :
    max (symbolPeriodMean q₁ + incidenceGain q₁ q₂) (symbolPeriodMean q₂ + incidenceGain q₂ q₁) ≤
        blindSymbolValue (powerNodes q₁ ∪ powerNodes q₂) ∧
      blindSymbolValue (powerNodes q₁ ∪ powerNodes q₂) ≤ productPeriodMean q₁ q₂ ∧
      zeroPoleBlindSymbolValue (powerNodes q₁ ∪ powerNodes q₂) =
        blindSymbolValue (powerNodes q₁ ∪ powerNodes q₂) := by
  obtain ⟨h₁, h₂, _⟩ := blindSymbolSlack_two_towers_enclosure hq₁ hq₂
  obtain ⟨h₁', _, _⟩ := blindSymbolSlack_two_towers_enclosure hq₂ hq₁
  rw [Set.union_comm] at h₁'
  rw [blindSymbolSlackOn_iff_blindSymbolValue] at h₁ h₁'
  have hup := h₂ (-blindSymbolValue (powerNodes q₁ ∪ powerNodes q₂))
    ((blindSymbolSlackOn_iff_blindSymbolValue _ _).mpr le_rfl)
  refine ⟨max_le (by linarith) (by linarith), by linarith,
    zeroPoleBlindSymbolValue_two_towers_eq q₁ q₂⟩

end

end GaloisForLFunctions.BiScaleUncertainty
