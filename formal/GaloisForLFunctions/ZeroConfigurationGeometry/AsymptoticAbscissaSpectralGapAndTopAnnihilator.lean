import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse

/-!
# Asymptotic Zero Abscissa, Bilateral Spectral Gap, and Single-Base Top-Layer Annihilators

Let `Θ = zetaZeroAbscissa = sup { Re ρ : ζ(ρ) = 0 }` be the global zero abscissa of the Riemann
zeta function (`1/2 ≤ Θ ≤ 1`). This module introduces the **asymptotic zero abscissa**
`Θ_∞ = zetaAsymptoticAbscissa = inf { σ ≥ 1/2 : {q : XiZeroCopy | σ < Re q}.Finite }`
and proves four unconditional structural results around `RHTower.AsymptoticAbscissaLaw`:

1. **Asymptotic abscissa and `limsup = sup` characterization**
   (`half_le_zetaAsymptoticAbscissa`, `zetaAsymptoticAbscissa_le_zetaZeroAbscissa`,
   `zerosApproachLine_iff_zetaAsymptoticAbscissa_eq_half`,
   `asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa`):
   `1/2 ≤ Θ_∞ ≤ Θ ≤ 1`, `ZerosApproachLine ↔ Θ_∞ = 1/2`, and
   `AsymptoticAbscissaLaw ↔ Θ_∞ = Θ ↔ Θ_∞ − 1/2 = Θ − 1/2`.

2. **Exact bilateral isolated spectral-gap characterization of `¬ AsymptoticAbscissaLaw`**
   (`not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`):
   `AsymptoticAbscissaLaw` fails if and only if there exist `1/2 ≤ β₁ < β_* < 1` and `T_* > 0`
   such that `ζ` vanishes on nonempty finite conjugate-symmetric top and reflected bottom layers
   at `Re s = β_*` and `Re s = 1 − β_*` of ordinate `≤ T_*`, has no zeros right of `β_*` or in
   `(0, 1 − β_*)`, has **zero-free open vertical spectral-gap strips** `(β₁, β_*)` and
   `(1 − β_*, 1 − β₁)` across all heights, and confines every remaining strip zero to
   `[1 − β₁, β₁]`.

3. **Single-base Euler top-layer annihilators** (`singleBaseTopAnnihilator`,
   `singleBaseTopAnnihilator_eq_zero_of_mem`, `norm_singleBaseTopAnnihilator_ge_of_re_le_half`,
   `singleBaseTopAnnihilator_ne_zero_of_re_le_half`):
   For any base `b > 1` and finite top zero set `F ⊂ {Re ρ > 1/2}`, the finite single-base Euler
   Dirichlet polynomial `∏_{ρ ∈ F} (1 − b^{ρ − s})^{m(ρ)}` vanishes on `F` while being strictly
   bounded away from `0` throughout `Re s ≤ 1/2` (hence at every reflected zero `1 − ρ` and
   `1 − conj ρ`).

4. **Finite-Blaschke twisted functional equation** (`finiteRightBlaschke`,
   `norm_finiteRightBlaschke_criticalLine`, `finiteRightBlaschke_one_sub_mul_conjSymm`,
   `twisted_functionalEquation_div_finiteRightBlaschke`):
   Dividing an `s ↔ 1 − s` symmetric function by the unimodular right-half-plane Blaschke product
   of a conjugate-symmetric finite off-line layer twists the `s ↔ 1 − s` functional equation by the
   nonconstant critical-line phase `B(s)²`.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.BacklundConverse RHTower.LindelofSparse RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-! ### 1. The asymptotic zero abscissa `Θ_∞` and `limsup = sup` -/

/-- Set of abscissas `σ ≥ 1/2` to the right of which `ξ` has only finitely many divisor copies. -/
def zetaAsymptoticAbscissaSet : Set ℝ :=
  {σ : ℝ | 1 / 2 ≤ σ ∧ {q : XiZeroCopy | σ < (q.1 : ℂ).re}.Finite}

/-- **The asymptotic zero abscissa** `Θ_∞ = inf { σ ≥ 1/2 : #{Re ρ > σ} < ∞ }`. -/
def zetaAsymptoticAbscissa : ℝ := sInf zetaAsymptoticAbscissaSet

theorem one_mem_zetaAsymptoticAbscissaSet : (1 : ℝ) ∈ zetaAsymptoticAbscissaSet := by
  refine ⟨by norm_num, Set.finite_empty.subset fun q hq => ?_⟩
  simp only [mem_setOf_eq] at hq
  exact absurd (xi_divisor_support_re_mem_open_unit q.1).2 (not_lt.mpr hq.le)

theorem zetaAsymptoticAbscissaSet_nonempty : zetaAsymptoticAbscissaSet.Nonempty :=
  ⟨1, one_mem_zetaAsymptoticAbscissaSet⟩

theorem bddBelow_zetaAsymptoticAbscissaSet : BddBelow zetaAsymptoticAbscissaSet :=
  ⟨1 / 2, fun _ h => h.1⟩

theorem zetaAsymptoticAbscissaSet_mono {σ₁ σ₂ : ℝ}
    (h1 : σ₁ ∈ zetaAsymptoticAbscissaSet) (hle : σ₁ ≤ σ₂) :
    σ₂ ∈ zetaAsymptoticAbscissaSet :=
  ⟨h1.1.trans hle, h1.2.subset fun _ hq => lt_of_le_of_lt hle hq⟩

/-- Growing-height characterization: `σ ∈ zetaAsymptoticAbscissaSet` iff `σ ≥ 1/2` and all zeros
above some positive height `T` satisfy `Re ρ ≤ σ`. -/
theorem mem_zetaAsymptoticAbscissaSet_iff_eventually_height {σ : ℝ} :
    σ ∈ zetaAsymptoticAbscissaSet ↔
      1 / 2 ≤ σ ∧ ∃ T : ℝ, 0 < T ∧ ∀ q : XiZeroCopy, T ≤ |(q.1 : ℂ).im| → (q.1 : ℂ).re ≤ σ := by
  constructor
  · rintro ⟨hσ, hfin⟩
    obtain ⟨M, hM⟩ := (hfin.image fun q : XiZeroCopy => |(q.1 : ℂ).im|).bddAbove
    refine ⟨hσ, max M 0 + 1, by positivity, fun q hT => ?_⟩
    by_contra hgt
    push Not at hgt
    have hleM : |(q.1 : ℂ).im| ≤ M := hM ⟨q, hgt, rfl⟩
    have := le_max_left M 0
    linarith
  · rintro ⟨hσ, T, hT0, hT⟩
    refine ⟨hσ, (xiZeroBall (⌈T + 1⌉₊)).finite_toSet.subset fun q hq => ?_⟩
    simp only [mem_setOf_eq] at hq
    simp only [Finset.mem_coe, mem_xiZeroBall]
    have him_lt : |(q.1 : ℂ).im| < T := by
      by_contra hge
      exact absurd (hT q (not_lt.mp hge)) (not_le.mpr hq)
    have hnorm := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    have hspec_im := abs_spectral_im_lt_half q
    have hceil : T + 1 ≤ (⌈T + 1⌉₊ : ℝ) := Nat.le_ceil _
    rw [spectral_re_eq] at hnorm
    linarith

/-- If every `XiZeroCopy` has real part `≤ σ` (`σ ≥ 1/2`), then `zetaZeroAbscissa ≤ σ` (trivial
zeros lie on `Re s ≤ 0 < 1/2`, and open-strip zeros come from `XiZeroCopy`). -/
theorem zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (hall : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ σ) :
    zetaZeroAbscissa ≤ σ := by
  refine csSup_le zetaZeroReSet_nonempty fun x hx => ?_
  obtain ⟨ρ, hzero, rfl⟩ := hx
  rcases le_or_gt ρ.re 0 with hle0 | hpos
  · linarith
  · have hlt1 : ρ.re < 1 := by
      by_contra hge1
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge1) hzero
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hzero hpos hlt1
    rw [← hq]
    exact hall q

theorem zetaZeroAbscissa_mem_zetaAsymptoticAbscissaSet :
    zetaZeroAbscissa ∈ zetaAsymptoticAbscissaSet := by
  refine ⟨half_le_zetaZeroAbscissa, Set.finite_empty.subset fun q hq => ?_⟩
  simp only [mem_setOf_eq] at hq
  exact absurd (re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q)) (not_le.mpr hq)

/-- Unconditional lower bound `1/2 ≤ Θ_∞`. -/
theorem half_le_zetaAsymptoticAbscissa : (1 / 2 : ℝ) ≤ zetaAsymptoticAbscissa :=
  le_csInf zetaAsymptoticAbscissaSet_nonempty fun _ h => h.1

/-- Unconditional inequality `Θ_∞ ≤ Θ`. -/
theorem zetaAsymptoticAbscissa_le_zetaZeroAbscissa :
    zetaAsymptoticAbscissa ≤ zetaZeroAbscissa :=
  csInf_le bddBelow_zetaAsymptoticAbscissaSet zetaZeroAbscissa_mem_zetaAsymptoticAbscissaSet

/-- Unconditional upper bound `Θ_∞ ≤ 1`. -/
theorem zetaAsymptoticAbscissa_le_one : zetaAsymptoticAbscissa ≤ 1 :=
  zetaAsymptoticAbscissa_le_zetaZeroAbscissa.trans zetaZeroAbscissa_le_one

/-- **`ZerosApproachLine` is `Θ_∞ = 1/2`.** -/
theorem zerosApproachLine_iff_zetaAsymptoticAbscissa_eq_half :
    ZerosApproachLine ↔ zetaAsymptoticAbscissa = 1 / 2 := by
  constructor
  · intro hZ
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) half_le_zetaAsymptoticAbscissa
    exact csInf_le bddBelow_zetaAsymptoticAbscissaSet
      ⟨by linarith, finite_re_gt_of_zerosApproachLine hZ hε⟩
  · intro heq h hh
    have hlt : zetaAsymptoticAbscissa < 1 / 2 + h := by rw [heq]; linarith
    obtain ⟨σ, hσ, hσlt⟩ := exists_lt_of_csInf_lt zetaAsymptoticAbscissaSet_nonempty hlt
    have hmem := zetaAsymptoticAbscissaSet_mono hσ hσlt.le
    refine (hmem.2.preimage xiZeroCopyReflectEquiv.injective.injOn).subset fun q hq => ?_
    have hq' : h < (xiSpectralPoint q).im := hq
    rw [spectral_im_eq] at hq'
    have hre : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl
    simp only [mem_preimage, mem_setOf_eq, hre, Complex.sub_re, Complex.one_re]
    linarith

/-- **`AsymptoticAbscissaLaw` is `Θ_∞ = Θ` (`limsup Re ρ = sup Re ρ`).** -/
theorem asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa :
    AsymptoticAbscissaLaw ↔ zetaAsymptoticAbscissa = zetaZeroAbscissa := by
  constructor
  · intro hAAL
    refine le_antisymm zetaAsymptoticAbscissa_le_zetaZeroAbscissa
      (le_csInf zetaAsymptoticAbscissaSet_nonempty fun σ hσ => ?_)
    obtain ⟨h12, hfin⟩ := hσ
    have hh : 0 ≤ σ - 1 / 2 := by linarith
    have hfin' : {q : XiZeroCopy | 1 / 2 + (σ - 1 / 2) < (q.1 : ℂ).re}.Finite := by
      simpa [add_sub_cancel] using hfin
    have hall := hAAL (σ - 1 / 2) hh hfin'
    exact zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le h12 fun q => by
      simpa [add_sub_cancel] using hall q
  · intro heq h hh hfin q
    have hmem : 1 / 2 + h ∈ zetaAsymptoticAbscissaSet := ⟨by linarith, hfin⟩
    have hΘ : zetaZeroAbscissa ≤ 1 / 2 + h := by
      rw [← heq]
      exact csInf_le bddBelow_zetaAsymptoticAbscissaSet hmem
    exact (re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q)).trans hΘ

/-- Displacement form of `limsup = sup`:
`AsymptoticAbscissaLaw ↔ Θ_∞ − 1/2 = Θ − 1/2`. -/
theorem asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_sub_half_eq :
    AsymptoticAbscissaLaw ↔
      zetaAsymptoticAbscissa - 1 / 2 = zetaZeroAbscissa - 1 / 2 := by
  rw [asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa]
  exact ⟨fun h => by rw [h], fun h => by linarith⟩

/-! ### 2. Exact bilateral isolated spectral-gap characterization of `¬ AsymptoticAbscissaLaw` -/

/-- The vertical-line zero layer `{ρ ∈ ℂ : ζ(ρ) = 0 ∧ Re ρ = σ}` at abscissa `σ`. -/
def zetaVerticalZeroLayer (σ : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = σ}

/-- **Exact bilateral isolated spectral-gap structure of a one-off zero violation.**
`¬ AsymptoticAbscissaLaw` holds if and only if there exist abscissas `1/2 ≤ β₁ < β_* < 1` and a
finite ordinate bound `T_* > 0` isolating a nonempty finite conjugate-symmetric top zero layer at
`Re s = β_*` and its reflected bottom layer at `Re s = 1 − β_*` from all other strip zeros by the
two global zero-free vertical strips `(β₁, β_*)` and `(1 − β_*, 1 − β₁)`. -/
theorem not_asymptoticAbscissaLaw_iff_bilateral_spectralGap :
    ¬ AsymptoticAbscissaLaw ↔
      ∃ (β₁ β_star T_star : ℝ),
        1 / 2 ≤ β₁ ∧ β₁ < β_star ∧ β_star < 1 ∧ 0 < T_star ∧
        (∀ s : ℂ, β_star < s.re → riemannZeta s ≠ 0) ∧
        (∀ s : ℂ, 0 < s.re → s.re < 1 - β_star → riemannZeta s ≠ 0) ∧
        (zetaVerticalZeroLayer β_star).Finite ∧ (zetaVerticalZeroLayer β_star).Nonempty ∧
        (zetaVerticalZeroLayer (1 - β_star)).Finite ∧
        (zetaVerticalZeroLayer (1 - β_star)).Nonempty ∧
        (∀ ρ ∈ zetaVerticalZeroLayer β_star,
          starRingEnd ℂ ρ ∈ zetaVerticalZeroLayer β_star ∧
          1 - ρ ∈ zetaVerticalZeroLayer (1 - β_star) ∧
          1 - starRingEnd ℂ ρ ∈ zetaVerticalZeroLayer (1 - β_star) ∧
          |ρ.im| ≤ T_star) ∧
        (∀ s : ℂ, β₁ < s.re → s.re < β_star → riemannZeta s ≠ 0) ∧
        (∀ s : ℂ, 1 - β_star < s.re → s.re < 1 - β₁ → riemannZeta s ≠ 0) ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
          ρ ∉ zetaVerticalZeroLayer β_star → ρ ∉ zetaVerticalZeroLayer (1 - β_star) →
          1 - β₁ ≤ ρ.re ∧ ρ.re ≤ β₁) ∧
        (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → T_star < |ρ.im| →
          1 - β₁ ≤ ρ.re ∧ ρ.re ≤ β₁) := by
  constructor
  · intro hnot
    have hlt_abs : zetaAsymptoticAbscissa < zetaZeroAbscissa :=
      lt_of_le_of_ne zetaAsymptoticAbscissa_le_zetaZeroAbscissa fun heq =>
        hnot (asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa.mpr heq)
    obtain ⟨σ₀, ⟨hσ₀_half, hE₀_fin⟩, hσ₀_lt⟩ :=
      exists_lt_of_csInf_lt zetaAsymptoticAbscissaSet_nonempty hlt_abs
    set E₀ : Set XiZeroCopy := {q : XiZeroCopy | σ₀ < (q.1 : ℂ).re} with hE₀_def
    have hE₀_ne : E₀.Nonempty := by
      obtain ⟨ρ, hζ, hρ1, hσρ⟩ := exists_zetaZero_mem_openStrip_lt_re hσ₀_lt
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ (by linarith) hρ1
      exact ⟨q, by simp only [hE₀_def, mem_setOf_eq, hq]; exact hσρ⟩
    -- Maximal real part `β_star` on the nonempty finite right-excess set `E₀`
    obtain ⟨q_star, hq_star_mem, hq_star_max⟩ :=
      hE₀_fin.exists_maximalFor (fun q : XiZeroCopy => (q.1 : ℂ).re) E₀ hE₀_ne
    set β_star : ℝ := (q_star.1 : ℂ).re with hβ_star_def
    have hσ₀_lt_β : σ₀ < β_star := hq_star_mem
    have hβ_lt_one : β_star < 1 := (xi_divisor_support_re_mem_open_unit q_star.1).2
    have hq_le_β : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β_star := fun q => by
      by_cases hq : q ∈ E₀
      · by_contra hgt
        push Not at hgt
        exact absurd (hq_star_max hq hgt.le) (not_le.mpr hgt)
      · simp only [hE₀_def, mem_setOf_eq, not_lt] at hq
        linarith
    have hβ_eq_Θ : β_star = zetaZeroAbscissa :=
      le_antisymm (re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q_star))
        (zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le (by linarith) hq_le_β)
    -- Next level `β₁ < β_star` below the top layer
    set E₁ : Set XiZeroCopy := {q : XiZeroCopy | σ₀ < (q.1 : ℂ).re ∧ (q.1 : ℂ).re < β_star}
    have hE₁_fin : E₁.Finite := hE₀_fin.subset fun _ h => h.1
    have hex_β₁ : ∃ β₁ : ℝ, 1 / 2 ≤ β₁ ∧ β₁ < β_star ∧
        ∀ q : XiZeroCopy, (q.1 : ℂ).re < β_star → (q.1 : ℂ).re ≤ β₁ := by
      by_cases hne₁ : E₁.Nonempty
      · obtain ⟨q₁, hq₁_mem, hq₁_max⟩ :=
          hE₁_fin.exists_maximalFor (fun q : XiZeroCopy => (q.1 : ℂ).re) E₁ hne₁
        refine ⟨max σ₀ (q₁.1 : ℂ).re, hσ₀_half.trans (le_max_left _ _),
          max_lt hσ₀_lt_β hq₁_mem.2, fun q hqlt => ?_⟩
        by_cases hq0 : σ₀ < (q.1 : ℂ).re
        · have hqE₁ : q ∈ E₁ := ⟨hq0, hqlt⟩
          have hle_q₁ : (q.1 : ℂ).re ≤ (q₁.1 : ℂ).re := by
            by_contra hgt
            push Not at hgt
            exact absurd (hq₁_max hqE₁ hgt.le) (not_le.mpr hgt)
          exact hle_q₁.trans (le_max_right _ _)
        · exact (not_lt.mp hq0).trans (le_max_left _ _)
      · refine ⟨σ₀, hσ₀_half, hσ₀_lt_β, fun q hqlt => ?_⟩
        by_contra hgt
        push Not at hgt
        exact hne₁ ⟨q, hgt, hqlt⟩
    obtain ⟨β₁, hβ₁_half, hβ₁_lt, hβ₁_bound⟩ := hex_β₁
    -- Top layer finiteness, nonemptiness, symmetries, and ordinate bound `T_star`
    have htop_fin : (zetaVerticalZeroLayer β_star).Finite := by
      refine (hE₀_fin.image fun q : XiZeroCopy => (q.1 : ℂ)).subset fun ρ ⟨hζ, hre⟩ => ?_
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ
        (by linarith) (by linarith)
      exact ⟨q, by simp only [hE₀_def, mem_setOf_eq, hq, hre]; exact hσ₀_lt_β, hq⟩
    have htop_ne : (zetaVerticalZeroLayer β_star).Nonempty :=
      ⟨(q_star.1 : ℂ), riemannZeta_eq_zero_of_xiZeroCopy q_star, rfl⟩
    have hbot_fin : (zetaVerticalZeroLayer (1 - β_star)).Finite := by
      refine (htop_fin.image fun z : ℂ => 1 - z).subset fun ρ ⟨hζ, hre⟩ => ?_
      have hrefl : riemannZeta (1 - ρ) = 0 :=
        riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ (by linarith) (by linarith)
      exact ⟨1 - ρ, ⟨hrefl, by simp [hre]⟩, by ring⟩
    have hbot_ne : (zetaVerticalZeroLayer (1 - β_star)).Nonempty := by
      obtain ⟨ρ₀, hζ₀, hre₀⟩ := htop_ne
      exact ⟨1 - ρ₀,
        riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ₀ (by linarith) (by linarith),
        by simp [hre₀]⟩
    obtain ⟨M, hM⟩ := (htop_fin.image fun ρ : ℂ => |ρ.im|).bddAbove
    set T_star : ℝ := max M 0 + 1
    have hT_pos : 0 < T_star := by positivity
    have hsymm : ∀ ρ ∈ zetaVerticalZeroLayer β_star,
        starRingEnd ℂ ρ ∈ zetaVerticalZeroLayer β_star ∧
        1 - ρ ∈ zetaVerticalZeroLayer (1 - β_star) ∧
        1 - starRingEnd ℂ ρ ∈ zetaVerticalZeroLayer (1 - β_star) ∧
        |ρ.im| ≤ T_star := by
      intro ρ ⟨hζ, hre⟩
      have hconj_ζ : riemannZeta (starRingEnd ℂ ρ) = 0 := by
        rw [riemannZeta_conj, hζ, map_zero]
      have hrefl_ζ : riemannZeta (1 - ρ) = 0 :=
        riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ (by linarith) (by linarith)
      have hrefl_conj_ζ : riemannZeta (1 - starRingEnd ℂ ρ) = 0 :=
        riemannZeta_one_sub_eq_zero_of_mem_openStrip hconj_ζ
          (by simp; linarith) (by simp; linarith)
      have him_le : |ρ.im| ≤ T_star := by
        have hleM : |ρ.im| ≤ M := hM ⟨ρ, ⟨hζ, hre⟩, rfl⟩
        have := le_max_left M 0
        linarith
      exact ⟨⟨hconj_ζ, by simp [hre]⟩, ⟨hrefl_ζ, by simp [hre]⟩,
        ⟨hrefl_conj_ζ, by simp [hre]⟩, him_le⟩
    -- Nonvanishing right of `β_star` and in `(0, 1 − β_star)`
    have hno_right : ∀ s : ℂ, β_star < s.re → riemannZeta s ≠ 0 := by
      rw [hβ_eq_Θ]
      exact fun _ hs => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hs
    have hno_left : ∀ s : ℂ, 0 < s.re → s.re < 1 - β_star → riemannZeta s ≠ 0 := by
      intro s hs0 hslt hζ
      have hrefl := riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ hs0 (by linarith)
      exact hno_right (1 - s) (by simp; linarith) hrefl
    -- Spectral gap on `(β₁, β_star)` and `(1 − β_star, 1 − β₁)`
    have hgap_right : ∀ s : ℂ, β₁ < s.re → s.re < β_star → riemannZeta s ≠ 0 := by
      intro s hs1 hs2 hζ
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ (by linarith) (by linarith)
      have hle := hβ₁_bound q (by rw [hq]; exact hs2)
      rw [hq] at hle
      linarith
    have hgap_left : ∀ s : ℂ, 1 - β_star < s.re → s.re < 1 - β₁ → riemannZeta s ≠ 0 := by
      intro s hs1 hs2 hζ
      have hrefl := riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ (by linarith) (by linarith)
      exact hgap_right (1 - s) (by simp; linarith) (by simp; linarith) hrefl
    -- Confinement of all non-top/non-bottom strip zeros to `[1 − β₁, β₁]`
    have hconfine : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        ρ ∉ zetaVerticalZeroLayer β_star → ρ ∉ zetaVerticalZeroLayer (1 - β_star) →
        1 - β₁ ≤ ρ.re ∧ ρ.re ≤ β₁ := by
      intro ρ hζ h0 h1 hnot_top hnot_bot
      have hlt_top : ρ.re < β_star := by
        rcases lt_trichotomy ρ.re β_star with hlt | heq | hgt
        · exact hlt
        · exact False.elim (hnot_top ⟨hζ, heq⟩)
        · exact False.elim (hno_right ρ hgt hζ)
      have hgt_bot : 1 - β_star < ρ.re := by
        rcases lt_trichotomy ρ.re (1 - β_star) with hlt | heq | hgt
        · exact False.elim (hno_left ρ h0 hlt hζ)
        · exact False.elim (hnot_bot ⟨hζ, heq⟩)
        · exact hgt
      have hupper : ρ.re ≤ β₁ := by
        by_contra hgt
        exact hgap_right ρ (not_le.mp hgt) hlt_top hζ
      have hlower : 1 - β₁ ≤ ρ.re := by
        by_contra hlt
        exact hgap_left ρ hgt_bot (not_le.mp hlt) hζ
      exact ⟨hlower, hupper⟩
    have hconfine_height : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        T_star < |ρ.im| → 1 - β₁ ≤ ρ.re ∧ ρ.re ≤ β₁ := by
      intro ρ hζ h0 h1 hT
      refine hconfine ρ hζ h0 h1 (fun hmem => ?_) (fun ⟨_, hre⟩ => ?_)
      · linarith [(hsymm ρ hmem).2.2.2]
      · have hrefl_mem : 1 - ρ ∈ zetaVerticalZeroLayer β_star :=
          ⟨riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ h0 h1, by simp [hre]⟩
        have him_bound := (hsymm (1 - ρ) hrefl_mem).2.2.2
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at him_bound
        linarith
    exact ⟨β₁, β_star, T_star, hβ₁_half, hβ₁_lt, hβ_lt_one, hT_pos,
      hno_right, hno_left, htop_fin, htop_ne, hbot_fin, hbot_ne, hsymm,
      hgap_right, hgap_left, hconfine, hconfine_height⟩
  · -- Converse: any isolated bilateral spectral gap refutes `AsymptoticAbscissaLaw`
    rintro ⟨β₁, β_star, T_star, hβ₁_half, hβ₁_lt, hβ_lt_one, hT_pos,
      hno_right, _, _, ⟨ρ_star, hζ_star, hre_star⟩, _, _, hsymm,
      hgap_right, _, _, _⟩ hAAL
    set h : ℝ := β₁ - 1 / 2
    have hh : 0 ≤ h := by simp only [h]; linarith
    have hfin : {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite := by
      refine (xiZeroBall (⌈T_star + 1⌉₊)).finite_toSet.subset fun q hq => ?_
      simp only [mem_setOf_eq] at hq
      have hβ₁_q : β₁ < (q.1 : ℂ).re := by simp only [h] at hq; linarith
      have hζ_q : riemannZeta (q.1 : ℂ) = 0 := riemannZeta_eq_zero_of_xiZeroCopy q
      have hre_eq : (q.1 : ℂ).re = β_star := by
        rcases lt_trichotomy (q.1 : ℂ).re β_star with hlt | heq | hgt
        · exact False.elim (hgap_right (q.1 : ℂ) hβ₁_q hlt hζ_q)
        · exact heq
        · exact False.elim (hno_right (q.1 : ℂ) hgt hζ_q)
      have him_le : |(q.1 : ℂ).im| ≤ T_star := (hsymm (q.1 : ℂ) ⟨hζ_q, hre_eq⟩).2.2.2
      simp only [Finset.mem_coe, mem_xiZeroBall]
      have hnorm := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
      have hspec_im := abs_spectral_im_lt_half q
      have hceil : T_star + 1 ≤ (⌈T_star + 1⌉₊ : ℝ) := Nat.le_ceil _
      rw [spectral_re_eq] at hnorm
      linarith
    obtain ⟨q_star, hq_star⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ_star
      (by linarith) (by linarith)
    have hall := hAAL h hh hfin q_star
    rw [hq_star, hre_star] at hall
    simp only [h] at hall
    linarith

/-! ### 3. Single-base Euler top-layer annihilator separating `F` from `Re s ≤ 1/2` -/

/-- Finite single-base Euler-type Dirichlet polynomial annihilating a finite set `F` of zeros with
prescribed multiplicities `m`: `D_{b, F, m}(s) = ∏_{ρ ∈ F} (1 − b^{ρ − s})^{m(ρ)}`. -/
def singleBaseTopAnnihilator (b : ℝ) (F : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ F, (1 - (b : ℂ) ^ (ρ - s)) ^ m ρ

/-- `singleBaseTopAnnihilator` vanishes at every `ρ₀ ∈ F` with `m(ρ₀) ≥ 1`. -/
theorem singleBaseTopAnnihilator_eq_zero_of_mem (b : ℝ) {F : Finset ℂ} {m : ℂ → ℕ} {ρ₀ : ℂ}
    (hmem : ρ₀ ∈ F) (hm : 1 ≤ m ρ₀) :
    singleBaseTopAnnihilator b F m ρ₀ = 0 := by
  unfold singleBaseTopAnnihilator
  refine Finset.prod_eq_zero hmem ?_
  rw [sub_self, Complex.cpow_zero, sub_self, zero_pow (by omega)]

/-- **Strict lower bound on `Re s ≤ 1/2`:** when `b > 1` and every `ρ ∈ F` satisfies `Re ρ > 1/2`,
every factor `1 − b^{ρ − s}` has modulus at least `b^{Re ρ − Re s} − 1 > 0` across the entire
closed half-plane `Re s ≤ 1/2`. -/
theorem norm_singleBaseTopAnnihilator_ge_of_re_le_half {b : ℝ} (hb : 1 < b)
    {F : Finset ℂ} (hF : ∀ ρ ∈ F, 1 / 2 < ρ.re) (m : ℂ → ℕ) {s : ℂ} (hs : s.re ≤ 1 / 2) :
    (∏ ρ ∈ F, (b ^ (ρ.re - s.re) - 1) ^ m ρ) ≤ ‖singleBaseTopAnnihilator b F m s‖ ∧
      0 < ∏ ρ ∈ F, (b ^ (ρ.re - s.re) - 1) ^ m ρ := by
  have hb0 : 0 < b := by linarith
  have hfactor_pos : ∀ ρ ∈ F, 0 < b ^ (ρ.re - s.re) - 1 := fun ρ hρ => by
    have hgt : 1 < b ^ (ρ.re - s.re) := Real.one_lt_rpow hb (by linarith [hF ρ hρ])
    linarith
  have hfactor_le : ∀ ρ ∈ F,
      (b ^ (ρ.re - s.re) - 1) ^ m ρ ≤ ‖(1 - (b : ℂ) ^ (ρ - s)) ^ m ρ‖ := fun ρ hρ => by
    rw [norm_pow]
    refine pow_le_pow_left₀ (hfactor_pos ρ hρ).le ?_ (m ρ)
    have hnorm_cpow : ‖(b : ℂ) ^ (ρ - s)‖ = b ^ (ρ.re - s.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hb0, Complex.sub_re]
    calc b ^ (ρ.re - s.re) - 1
        = ‖(b : ℂ) ^ (ρ - s)‖ - ‖(1 : ℂ)‖ := by rw [hnorm_cpow, norm_one]
      _ ≤ ‖(b : ℂ) ^ (ρ - s) - 1‖ := norm_sub_norm_le _ _
      _ = ‖1 - (b : ℂ) ^ (ρ - s)‖ := norm_sub_rev _ _
  refine ⟨?_, Finset.prod_pos fun ρ hρ => pow_pos (hfactor_pos ρ hρ) (m ρ)⟩
  unfold singleBaseTopAnnihilator
  rw [norm_prod]
  exact Finset.prod_le_prod (fun ρ hρ => pow_nonneg (hfactor_pos ρ hρ).le (m ρ)) hfactor_le

/-- `singleBaseTopAnnihilator` has **no zeros** in the closed left half-plane `Re s ≤ 1/2`; in
particular, dividing `ζ(s)` by `D_{b, F, m}(s)` kills the top layer `F` on the right without
introducing poles on `Re s ≤ 1/2` and without cancelling the reflected layer `1 − F`! -/
theorem singleBaseTopAnnihilator_ne_zero_of_re_le_half {b : ℝ} (hb : 1 < b)
    {F : Finset ℂ} (hF : ∀ ρ ∈ F, 1 / 2 < ρ.re) (m : ℂ → ℕ) {s : ℂ} (hs : s.re ≤ 1 / 2) :
    singleBaseTopAnnihilator b F m s ≠ 0 := by
  obtain ⟨hle, hpos⟩ := norm_singleBaseTopAnnihilator_ge_of_re_le_half hb hF m hs
  exact norm_ne_zero_iff.mp (lt_of_lt_of_le hpos hle).ne'

theorem singleBaseTopAnnihilator_reflected_ne_zero {b : ℝ} (hb : 1 < b)
    {F : Finset ℂ} (hF : ∀ ρ ∈ F, 1 / 2 < ρ.re) (m : ℂ → ℕ) {ρ₀ : ℂ} (hρ₀ : 1 / 2 ≤ ρ₀.re) :
    singleBaseTopAnnihilator b F m (1 - ρ₀) ≠ 0 ∧
      singleBaseTopAnnihilator b F m (1 - starRingEnd ℂ ρ₀) ≠ 0 :=
  ⟨singleBaseTopAnnihilator_ne_zero_of_re_le_half hb hF m (by simp; linarith),
    singleBaseTopAnnihilator_ne_zero_of_re_le_half hb hF m (by simp; linarith)⟩

/-! ### 4. Finite right-half-plane Blaschke product and twisted functional equation -/

/-- Finite Blaschke product for `Re s > 1/2` built from an off-line zero packet `(F, m)`:
`B_{F, m}(s) = ∏_{ρ ∈ F} ((s − ρ) / (s − (1 − conj ρ)))^{m(ρ)}`. -/
def finiteRightBlaschke (F : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ F, ((s - ρ) / (s - (1 - starRingEnd ℂ ρ))) ^ m ρ

/-- `B_{F, m}(s)` is unimodular (`‖B_{F, m}(s)‖ = 1`) along the entire critical line `Re s = 1/2`. -/
theorem norm_finiteRightBlaschke_criticalLine {F : Finset ℂ} (hF : ∀ ρ ∈ F, 1 / 2 < ρ.re)
    (m : ℂ → ℕ) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖finiteRightBlaschke F m s‖ = 1 := by
  unfold finiteRightBlaschke
  rw [norm_prod]
  refine Finset.prod_eq_one fun ρ hρ => ?_
  rw [norm_pow, norm_div]
  have hrel : s - (1 - starRingEnd ℂ ρ) = -starRingEnd ℂ (s - ρ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.neg_re, hs]
      ring
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, Complex.neg_im]
      ring
  have hne : ‖s - ρ‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro hc
    have hre := congrArg Complex.re hc
    simp only [Complex.sub_re, Complex.zero_re, hs] at hre
    linarith [hF ρ hρ]
  rw [hrel, norm_neg, Complex.norm_conj, div_self hne, one_pow]

/-- Reflection reciprocity `B_{F, m}(1 − s) · B_{F, m}(s) = 1` for any conjugate-symmetric finite
zero packet `(F, m)` away from `F ∪ (1 − F)`. -/
theorem finiteRightBlaschke_one_sub_mul_conjSymm {F : Finset ℂ}
    (hconj : ∀ ρ ∈ F, starRingEnd ℂ ρ ∈ F)
    {m : ℂ → ℕ} (hm : ∀ ρ ∈ F, m (starRingEnd ℂ ρ) = m ρ)
    {s : ℂ} (hs : ∀ ρ ∈ F, s ≠ ρ ∧ s ≠ 1 - ρ) :
    finiteRightBlaschke F m (1 - s) * finiteRightBlaschke F m s = 1 := by
  unfold finiteRightBlaschke
  have hreindex : (∏ ρ ∈ F, ((1 - s - ρ) / (1 - s - (1 - starRingEnd ℂ ρ))) ^ m ρ) =
      ∏ ρ ∈ F, ((1 - s - starRingEnd ℂ ρ) /
        (1 - s - (1 - starRingEnd ℂ (starRingEnd ℂ ρ)))) ^ m (starRingEnd ℂ ρ) := by
    symm
    refine Finset.prod_nbij (starRingEnd ℂ) (fun ρ hρ => hconj ρ hρ)
      (fun _ _ _ _ h => Complex.conjCLE.injective h)
      (fun ρ hρ => ⟨starRingEnd ℂ ρ, hconj ρ hρ, Complex.conj_conj ρ⟩)
      (fun _ _ => rfl)
  rw [hreindex, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun ρ hρ => ?_
  rw [hm ρ hρ, Complex.conj_conj, ← mul_pow]
  have hne1 : s - ρ ≠ 0 := sub_ne_zero.mpr (hs ρ hρ).1
  have hne2 : s - (1 - starRingEnd ℂ ρ) ≠ 0 :=
    sub_ne_zero.mpr (hs (starRingEnd ℂ ρ) (hconj ρ hρ)).2
  have hnum : 1 - s - starRingEnd ℂ ρ = -(s - (1 - starRingEnd ℂ ρ)) := by ring
  have hden : 1 - s - (1 - ρ) = -(s - ρ) := by ring
  rw [hnum, hden]
  have hcancel : (-(s - (1 - starRingEnd ℂ ρ)) / -(s - ρ)) *
      ((s - ρ) / (s - (1 - starRingEnd ℂ ρ))) = 1 := by
    field_simp
  rw [hcancel, one_pow]

/-- Dividing an `s ↔ 1 − s` symmetric function `Ξ` by `finiteRightBlaschke F m` removes `F` while
twisting the functional equation by the unimodular critical-line multiplier `B_{F, m}(s)²`. -/
theorem twisted_functionalEquation_div_finiteRightBlaschke {F : Finset ℂ}
    (hconj : ∀ ρ ∈ F, starRingEnd ℂ ρ ∈ F)
    {m : ℂ → ℕ} (hm : ∀ ρ ∈ F, m (starRingEnd ℂ ρ) = m ρ)
    {Ξ : ℂ → ℂ} {s : ℂ} (hΞ : Ξ (1 - s) = Ξ s)
    (hs : ∀ ρ ∈ F, s ≠ ρ ∧ s ≠ 1 - ρ) :
    Ξ (1 - s) / finiteRightBlaschke F m (1 - s) =
      finiteRightBlaschke F m s ^ 2 * (Ξ s / finiteRightBlaschke F m s) := by
  have hrec := finiteRightBlaschke_one_sub_mul_conjSymm hconj hm hs
  have hB1 : finiteRightBlaschke F m (1 - s) ≠ 0 :=
    fun h0 => by rw [h0, zero_mul] at hrec; exact zero_ne_one hrec
  have hB2 : finiteRightBlaschke F m s ≠ 0 :=
    fun h0 => by rw [h0, mul_zero] at hrec; exact zero_ne_one hrec
  rw [hΞ, div_eq_iff hB1]
  calc Ξ s
      = Ξ s * (finiteRightBlaschke F m s / finiteRightBlaschke F m s) *
          (finiteRightBlaschke F m (1 - s) * finiteRightBlaschke F m s) := by
            rw [div_self hB2, hrec, mul_one, mul_one]
    _ = finiteRightBlaschke F m s ^ 2 * (Ξ s / finiteRightBlaschke F m s) *
          finiteRightBlaschke F m (1 - s) := by
            field_simp; ring

end

end GaloisForLFunctions.ZeroConfigurationGeometry
