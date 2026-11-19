import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ReflectedCompositeWaveTransmission
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeErrorInOddCompositeProducts
import GaloisForLFunctions.ExceptionalLayerTheory.TheOrdinaryPrimeRadiusDetectsExactlyOneOffLineQuartet
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.EveryFiniteLayerIsRealizedByATwoSidedEdit
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheLogTwistedOscillatingSmoothPowerIsPaidExactlyAtTheDoubleZerosOfZeta
import GaloisForLFunctions.RHTower.BaezDuarteBurnolMultiplicityAllZeros
import GaloisForLFunctions.RHTower.WeilConeDilationRealnessRigidity
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# The Simple Off-Line Quartet Stratum and Reflected-Composite Factorization

This module synthesizes the complete unconditional theory of a lone *simple* off-line quartet
(`HasSimpleSingleOffLineQuartet ρ₀`, `NoSimpleSingleOffLineQuartet`) and its interaction with the
reflected composite factorization, prime-dilation recurrences, two-interval prime radii, prime edits,
and second-order multiplicity observables:

1. **Exact characterizations of `HasSimpleSingleOffLineQuartet ρ₀`**
   (`quartetCopyMult_eq_one_iff_deriv_ne_zero`, `hasSimpleSingleOffLineQuartet_tfae`):
   At any right-half-plane strip zero `ρ₀` (`1/2 < Re ρ₀`, `0 < Im ρ₀`), a lone *simple* off-line
   quartet (`HasSingleOffLineQuartet ρ₀ ∧ quartetCopyMult ρ₀ = 1`) is equivalent to:
   - `HasSingleOffLineQuartet ρ₀ ∧ deriv riemannZeta ρ₀ ≠ 0`;
   - `{q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard = 2` (equivalently `≠ 1/2` copy count `= 4`);
   - unit-amplitude `ψ - id` wave (`|ψ(x) - x + 2 Re(x^{ρ₀}/ρ₀)| ≤ K √x log² x`);
   - unit-amplitude `θ - id` wave (`|θ(x) - x + 2 Re(x^{ρ₀}/ρ₀)| ≤ K √x log² x`);
   - unit-amplitude odd-composite wave (`|oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊ + 2 Re(x^{ρ₀}/ρ₀)| ≤ K √x log² x`);
   - bounded unit-multiplicity two-interval radius `thetaRadialDiscrepancy ρ₀.re ρ₀.im 1` jointly
     with bounded `(2, 3, 6)` ordinary-prime dilation residuals.

2. **Complete absence of odd-harmonic Pythagorean aliases at unit multiplicity**
   (`unit_multiplicity_no_odd_harmonic_alias`, `unit_trial_under_noSimple_forces_ramified_quartet`):
   No simple quartet (`m' = 1`) admits a non-trivial odd-harmonic Pythagorean alias (`k = 0`,
   `m = 1`, `ω = |γ|` unconditionally). Under `NoSimpleSingleOffLineQuartet`, any bounded
   unit-multiplicity trial `¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ 1)` forces `k ≥ 2`
   and a higher-multiplicity single quartet `2 ≤ quartetCopyMult ≤ 2k` with `ζ' = 0`.

3. **Rejection of non-`ζ`-zero radius imitators vs. intrinsic Beurling/Euler-twin firewall**
   (`coprimeZeroOneSet_imitator_rejected_by_reflectedComposites`,
   `unconditional_sEdit_rejected_above_max_two_thirds_zetaZeroAbscissa`,
   `unconditional_sEdit_rejected_on_zeroFreeStrip`,
   `rh_sEdit_imitates_radius_but_violates_reflectedComposites`):
   Every `{0, 1}`-coprime integer-set imitator (`1/2 < β < 1`, `ζ(β + iγ) ≠ 0`), every `{0, 1, 2}`
   prime `sEdit` on `max (2/3) zetaZeroAbscissa < β < 1` unconditionally (in particular across the
   entire zero-free strip `20999 / 24000 < β < 1`, including all `7/8 ≤ β < 1`), and every `sEdit`
   across the complementary sub-square-root complement `2/3 < β < 1` under `RH` violates the
   ordinary-integer reflected-composite identity at scale `Ω(n^β)` while imitating the two-interval
   radius. Meanwhile, first-order reflected-composite transmission and `q`-divisible cofactor
   slicing are satisfied at every genuine zero `ζ(ρ₀) = 0`, and intrinsic Beurling composites
   (`β ∈ (1/2, 2/3)`) and positive Euler twins realize simple off-line pairs/quartets.

4. **Second-order multiplicity separation, global equivalences, and `Θ`-non-advancement**
   (`singleQuartet_simple_iff_logTwisted_unbounded`, `noSimpleSingleOffLineQuartet_tfae`,
   `corollaries_of_noSimpleSingleOffLineQuartet`,
   `abscissa_unconstrained_under_no_simple_single_layer`):
   Under `HasSingleOffLineQuartet ρ₀`, simplicity (`quartetCopyMult ρ₀ = 1`) is equivalent to
   unboundedness of both the log-twisted reflected-composite defect and the log-twisted smooth-power
   receiver. Globally, `NoSimpleSingleOffLineQuartet` is equivalent to allowing `RH`, multi-quartet /
   infinite divisors (`4 ≤ #(rightZeros)`), or one ramified quartet (`2 ≤ quartetCopyMult ρ₀`), and
   leaves the supremum abscissa `b ∈ (1/2, 14/15)` unconstrained in `{0, 1, 2}`-prime Beurling models.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Finset MeasureTheory
open scoped ComplexConjugate BigOperators
open RHTower Zeta23
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ExclusionOfTheCriticalState
open GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.WorldsOfTheZeroConfiguration
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ### 1. Simple single off-line quartet predicate and vanishing-order / derivative laws -/

/-- `ζ` has a lone **simple** off-line quartet generated by `ρ₀`: `HasSingleOffLineQuartet ρ₀` with
unit divisor multiplicity `quartetCopyMult ρ₀ = 1`. -/
def HasSimpleSingleOffLineQuartet (ρ₀ : ℂ) : Prop :=
  HasSingleOffLineQuartet ρ₀ ∧ quartetCopyMult ρ₀ = 1

/-- Global exclusion of a lone simple off-line quartet, permitting `RiemannHypothesis`, every
multi-quartet or infinite off-line configuration, and a single quartet of multiplicity `≥ 2`. -/
def NoSimpleSingleOffLineQuartet : Prop :=
  ∀ ρ₀ : ℂ, ¬ HasSimpleSingleOffLineQuartet ρ₀

private theorem analyticOnNhd_riemannZeta_compl_one :
    AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    isOpen_compl_singleton

private theorem analyticOrderAt_riemannZeta_ne_top {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  apply analyticOnNhd_riemannZeta_compl_one.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (x := 2) (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) hρ1
  rw [analyticOrderAt_eq_zero.mpr (Or.inr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re)))]
  exact ENat.zero_ne_top

/-- On `{0 < Re ρ < 1}` where `ζ(ρ) = 0`, `quartetCopyMult ρ` coincides with `analyticOrderNatAt riemannZeta ρ`. -/
theorem quartetCopyMult_eq_analyticOrderNatAt {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (_hζ : riemannZeta ρ = 0) :
    quartetCopyMult ρ = analyticOrderNatAt riemannZeta ρ := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  set g : ℂ → ℂ := fun s => s * (s - 1) / 2 * Complex.Gammaℝ s
  have hΓ : AnalyticAt ℂ Complex.Gammaℝ ρ := GaloisForLFunctions.HTGeometry.analyticAt_Gammaℝ h0
  have hg : AnalyticAt ℂ g ρ :=
    (((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div analyticAt_const two_ne_zero).mul hΓ)
  have hg0 : g ρ ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)) two_ne_zero)
      (Complex.Gammaℝ_ne_zero_of_re_pos h0)
  have hxi_ord : meromorphicOrderAt RHTower.xi ρ = meromorphicOrderAt riemannZeta ρ := by
    rw [← meromorphicOrderAt_mul_of_ne_zero (f := riemannZeta) hg hg0]
    refine meromorphicOrderAt_congr ?_
    have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds ⟨h0, hρ1⟩)] with s hs
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs.1
    rw [RHTower.xi_eq_half_mul hs0 hs.2, Pi.mul_apply, riemannZeta_def_of_ne_zero hs0]
    dsimp [g]
    field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs.1]
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOnNhd_riemannZeta_compl_one ρ hρ1
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hρ1
  have hcast := Nat.cast_analyticOrderNatAt htop
  have hm_zeta : meromorphicOrderAt riemannZeta ρ =
      ((analyticOrderNatAt riemannZeta ρ : ℤ) : WithTop ℤ) := by
    rw [han.meromorphicOrderAt_eq, ← hcast]
    rfl
  rw [hm_zeta] at hxi_ord
  have hdiv : (MeromorphicOn.divisor RHTower.xi Set.univ) ρ =
      (analyticOrderNatAt riemannZeta ρ : ℤ) := by
    rw [MeromorphicOn.divisor_apply RHTower.xi_analyticOnNhd_univ.meromorphicOn (Set.mem_univ ρ),
      hxi_ord, WithTop.untop₀_coe]
  unfold quartetCopyMult
  rw [hdiv, Int.toNat_natCast]

/-- At any strip zero `ρ ∈ zetaZeroConfig.carrier`, `quartetCopyMult ρ = 1` iff `deriv riemannZeta ρ ≠ 0`. -/
theorem quartetCopyMult_eq_one_iff_deriv_ne_zero {ρ : ℂ} (hmem : ρ ∈ zetaZeroConfig.carrier) :
    quartetCopyMult ρ = 1 ↔ deriv riemannZeta ρ ≠ 0 := by
  have ⟨hζ, h0, h1⟩ := hmem
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  rw [quartetCopyMult_eq_analyticOrderNatAt h0 h1 hζ]
  obtain ⟨hge1, hvan⟩ := RHTower.one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta hρ1 hζ
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hρ1
  constructor
  · intro heq1
    have hord1 : analyticOrderAt riemannZeta ρ = 1 := by
      rw [← Nat.cast_analyticOrderNatAt htop, heq1, Nat.cast_one]
    exact RHTower.WeilDilationRealness.deriv_riemannZeta_ne_zero_of_order_one hρ1 hord1
  · intro hder_ne
    by_contra hne1
    have hgt1 : 1 < analyticOrderNatAt riemannZeta ρ := by omega
    have hz1 := hvan 1 hgt1
    rw [iteratedDeriv_one] at hz1
    exact hder_ne hz1

/-- At any strip zero `ρ ∈ zetaZeroConfig.carrier`, `2 ≤ quartetCopyMult ρ` iff `deriv riemannZeta ρ = 0`. -/
theorem two_le_quartetCopyMult_iff_deriv_eq_zero {ρ : ℂ} (hmem : ρ ∈ zetaZeroConfig.carrier) :
    2 ≤ quartetCopyMult ρ ↔ deriv riemannZeta ρ = 0 := by
  have ⟨hζ, h0, h1⟩ := hmem
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hge1 : 1 ≤ quartetCopyMult ρ := by
    rw [quartetCopyMult_eq_analyticOrderNatAt h0 h1 hζ]
    exact (RHTower.one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta hρ1 hζ).1
  rw [← not_iff_not]
  push Not
  rw [show quartetCopyMult ρ < 2 ↔ quartetCopyMult ρ = 1 by omega]
  exact quartetCopyMult_eq_one_iff_deriv_ne_zero hmem

theorem hasSimpleSingleOffLineQuartet_iff_deriv_ne_zero (ρ₀ : ℂ) :
    HasSimpleSingleOffLineQuartet ρ₀ ↔ HasSingleOffLineQuartet ρ₀ ∧ deriv riemannZeta ρ₀ ≠ 0 :=
  and_congr_right fun hq => quartetCopyMult_eq_one_iff_deriv_ne_zero hq.2.1

/-! ### 2. Divisor-copy cardinalities and the 8-way simple-quartet equivalence -/

private theorem xiZeroCopy_mem_carrier (q : XiZeroCopy) :
    (q.1 : ℂ) ∈ zetaZeroConfig.carrier := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hne1 : (q.1 : ℂ) ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  exact ⟨(RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp
    (xi_eq_zero_of_mem_divisor_support q.1), h0, h1⟩

private theorem xi_zero_of_mem_carrier {z : ℂ} (hz : z ∈ zetaZeroConfig.carrier) :
    RHTower.xi z = 0 := by
  obtain ⟨hζ, h0, h1⟩ := hz
  have hne1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  exact (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mpr hζ

private theorem xiZeroCopy_fiber_encard {z : ℂ} (hz : z ∈ zetaZeroConfig.carrier) :
    {q : XiZeroCopy | (q.1 : ℂ) = z}.encard = (quartetCopyMult z : ℕ∞) := by
  have hxi := xi_zero_of_mem_carrier hz
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have hsupp : z ∈ (MeromorphicOn.divisor RHTower.xi Set.univ).support := hq₀ ▸ q₀.1.2
  let ρ_s : XiDivisorSupport := ⟨z, hsupp⟩
  set m := ((MeromorphicOn.divisor RHTower.xi Set.univ) z).toNat
  have himg : (fun k : Fin m => (⟨ρ_s, k⟩ : XiZeroCopy)) '' Set.univ =
      {q : XiZeroCopy | (q.1 : ℂ) = z} := by
    ext q
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, rfl⟩; rfl
    · intro hq
      have hρ : q.1 = ρ_s := Subtype.ext hq
      cases q with | mk ρ k =>
      dsimp only at hρ; subst hρ; exact ⟨k, rfl⟩
  have hinj : Function.Injective (fun k : Fin m => (⟨ρ_s, k⟩ : XiZeroCopy)) := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  rw [← himg, hinj.injOn.encard_image, Set.encard_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_fin]
  rfl

/-- Under `HasSingleOffLineQuartet ρ₀`, the number of `XiZeroCopy` copies strictly right of
`Re s = 1/2` (counted with multiplicity) is `2 * quartetCopyMult ρ₀`. -/
theorem rightXiZeroCopy_encard_of_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard =
      ((2 * quartetCopyMult ρ₀ : ℕ) : ℕ∞) := by
  have hset : {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re} =
      {q : XiZeroCopy | (q.1 : ℂ) = ρ₀} ∪ {q : XiZeroCopy | (q.1 : ℂ) = conj ρ₀} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hgt
      have hoff : (q.1 : ℂ) ∈ {z ∈ zetaZeroConfig.carrier | z.re ≠ 1 / 2} :=
        ⟨xiZeroCopy_mem_carrier q, by linarith⟩
      rw [hq.2.2] at hoff
      rcases hoff with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; rw [h] at hgt; simp at hgt; linarith [hq.1]
      · exfalso; rw [h] at hgt; simp at hgt; linarith [hq.1]
    · rintro (h | h) <;> rw [h] <;> simp <;> linarith [hq.1]
  have hne : ρ₀ ≠ conj ρ₀ := fun he => by
    apply hq.im_ne_zero; have := congrArg Complex.im he; simp at this; linarith
  have hdisj : Disjoint {q : XiZeroCopy | (q.1 : ℂ) = ρ₀}
      {q : XiZeroCopy | (q.1 : ℂ) = conj ρ₀} :=
    Set.disjoint_left.mpr fun _ h1 h2 => hne (h1.symm.trans h2)
  have hc_mem : conj ρ₀ ∈ zetaZeroConfig.carrier := by
    have : conj ρ₀ ∈ {z ∈ zetaZeroConfig.carrier | z.re ≠ 1 / 2} := by
      rw [hq.2.2]; exact Or.inr (Or.inl rfl)
    exact this.1
  rw [hset, Set.encard_union_eq hdisj, xiZeroCopy_fiber_encard hq.2.1,
    xiZeroCopy_fiber_encard hc_mem, quartetCopyMult_conj]
  push_cast; ring

/-- Under `HasSingleOffLineQuartet ρ₀`, the total number of off-line `XiZeroCopy` copies
(`Re ≠ 1/2`, counted with multiplicity) is `4 * quartetCopyMult ρ₀`. -/
theorem offLineXiZeroCopy_encard_of_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.encard =
      ((4 * quartetCopyMult ρ₀ : ℕ) : ℕ∞) := by
  classical
  have hcard_sum : (offLineCopyFinset hq.finiteOffLine).card = 4 * quartetCopyMult ρ₀ := by
    have hs := sum_offLineCopyFinset_of_singleQuartet hq (fun _ => (1 : ℂ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
    have h4 : (1 : ℂ) + 1 + 1 + 1 = (4 : ℕ) := by norm_num
    rw [h4, ← Nat.cast_mul] at hs
    exact (Nat.cast_injective (R := ℂ) hs).trans (mul_comm _ 4)
  have hset : (offLineCopyFinset hq.finiteOffLine : Set XiZeroCopy) =
      {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2} := by
    ext q
    simp only [Finset.mem_coe, mem_offLineCopyFinset, Set.mem_setOf_eq, centredZero,
      Complex.sub_re]
    norm_num
    exact ⟨fun h he => h (by linarith), fun h he => h (by linarith)⟩
  rw [← hset, Set.encard_coe_eq_coe_finsetCard, hcard_sum]

private theorem rightZeros_le_rightXiZeroCopy_encard :
    (rightZeros zetaZeroConfig).encard ≤ {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard := by
  let f : rightZeros zetaZeroConfig → {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re} := fun z => by
    have hxi := xi_zero_of_mem_carrier z.2.1
    let q := Classical.choose (exists_xiZeroCopy_of_xi_eq_zero hxi)
    have hq : (q.1 : ℂ) = z.1 := Classical.choose_spec (exists_xiZeroCopy_of_xi_eq_zero hxi)
    exact ⟨q, by rw [Set.mem_setOf_eq, hq]; exact z.2.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hq_eq : ((f a).1.1 : ℂ) = ((f b).1.1 : ℂ) := congrArg (fun u => (u.1.1 : ℂ)) hab
    have ha : ((f a).1.1 : ℂ) = a.1 :=
      Classical.choose_spec (exists_xiZeroCopy_of_xi_eq_zero (xi_zero_of_mem_carrier a.2.1))
    have hb : ((f b).1.1 : ℂ) = b.1 :=
      Classical.choose_spec (exists_xiZeroCopy_of_xi_eq_zero (xi_zero_of_mem_carrier b.2.1))
    exact Subtype.ext (ha.symm.trans (hq_eq.trans hb))
  have heq1 : (rightZeros zetaZeroConfig).encard =
      (Set.univ : Set (rightZeros zetaZeroConfig)).encard := by
    rw [← Subtype.val_injective.injOn.encard_image]; simp
  have heq2 : {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard =
      (Set.univ : Set {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}).encard := by
    rw [← Subtype.val_injective.injOn.encard_image]; simp
  rw [heq1, heq2]
  exact Set.encard_le_encard_of_injOn (f := f) (s := Set.univ) (t := Set.univ)
    (fun _ _ => Set.mem_univ _) (fun _ _ _ _ h => hinj h)

private theorem rightXiZeroCopy_le_offLineXiZeroCopy_two_mul :
    2 * {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard =
      {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.encard := by
  have hpart : {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2} =
      {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re} ∪ {q : XiZeroCopy | (q.1 : ℂ).re < 1 / 2} := by
    ext q; simp only [Set.mem_setOf_eq, Set.mem_union]; exact ne_iff_lt_or_gt.trans or_comm
  have hdisj : Disjoint {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}
      {q : XiZeroCopy | (q.1 : ℂ).re < 1 / 2} :=
    Set.disjoint_left.mpr fun _ h1 h2 => by simp only [Set.mem_setOf_eq] at h1 h2; linarith
  -- Reflection `z ↦ 1 - z` on `XiZeroCopy` preserves divisor multiplicity (`xi_divisor_one_sub`)
  let reflSupport (ρ : XiDivisorSupport) : XiDivisorSupport :=
    ⟨1 - (ρ : ℂ), by
      have h := ρ.2
      rwa [Function.mem_support, xi_divisor_one_sub]⟩
  let reflCopy (q : XiZeroCopy) : XiZeroCopy :=
    ⟨reflSupport q.1, Fin.cast (by dsimp [reflSupport]; rw [xi_divisor_one_sub]) q.2⟩
  have hcopy_ext : ∀ {q₁ q₂ : XiZeroCopy},
      (q₁.1 : ℂ) = (q₂.1 : ℂ) → (q₁.2 : ℕ) = (q₂.2 : ℕ) → q₁ = q₂ := by
    rintro ⟨ρ₁, k₁⟩ ⟨ρ₂, k₂⟩ h1 h2
    have hρ : ρ₁ = ρ₂ := Subtype.ext h1
    subst hρ
    exact congrArg (Sigma.mk ρ₁) (Fin.ext h2)
  have hrefl_inv : ∀ q : XiZeroCopy, reflCopy (reflCopy q) = q := by
    intro q
    exact hcopy_ext (by dsimp [reflCopy, reflSupport]; ring) (by simp [reflCopy])
  have hinj_r : Function.Injective reflCopy := Function.LeftInverse.injective hrefl_inv
  have himg_r : reflCopy '' {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re} =
      {q : XiZeroCopy | (q.1 : ℂ).re < 1 / 2} := by
    ext q
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, rfl⟩
      change (1 - (p.1 : ℂ)).re < 1 / 2
      simp; linarith
    · intro hlt
      refine ⟨reflCopy q, ?_, hrefl_inv q⟩
      change 1 / 2 < (1 - (q.1 : ℂ)).re
      simp; linarith
  rw [hpart, Set.encard_union_eq hdisj, ← himg_r, hinj_r.injOn.encard_image, two_mul]

/-- Unit-wave on `θ - id` implies bounded unit-multiplicity two-interval radius and bounded `(2, 3, 6)`
ordinary-prime dilation residuals. -/
private theorem unit_theta_wave_implies_radial_and_236 {β γ : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1)
    (hγ : 0 < γ)
    (hθ : ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
      |Chebyshev.theta x - x +
          2 * ((x : ℂ) ^ (((β : ℂ) + I * (γ : ℂ))) / (((β : ℂ) + I * (γ : ℂ)))).re| ≤
        K * Real.sqrt x * (Real.log x) ^ 2) :
    ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ 1) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 2 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 3 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 6 β γ) := by
  obtain ⟨K, hK⟩ := hθ
  set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  have hβ0 : 0 < β := by linarith
  -- 1. Bounded two-interval radius at `m = 1`
  have hrad : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ 1) := by
    set h := quarterPeriodStep γ
    have hh : 0 < h := quarterPeriodStep_pos hγ.ne'
    unfold thetaRadialDiscrepancy
    rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not]
    refine ⟨4 * |K| * Real.exp h * (1 + 2 * h) ^ 2, 3, fun t ht => ?_⟩
    set B_t : ℝ := |K| * Real.exp ((t + 2 * h) / 2) * (1 + (t + 2 * h)) ^ 2
    have hm_step : ∀ s : ℝ, t ≤ s → s ≤ t + 2 * h →
        |thetaLogError s + 2 * ((1 : ℕ) : ℝ) * (Complex.exp (ρ * (s : ℂ)) / ρ).re| ≤ B_t := by
      intro s hs1 hs2
      have hx16 : 16 ≤ Real.exp s := by
        have h3 : (16 : ℝ) ≤ Real.exp 3 := by
          have := Real.exp_one_gt_d9
          calc (16 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
            _ ≤ Real.exp 1 ^ 3 := by gcongr
            _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
        exact h3.trans (Real.exp_le_exp.mpr (ht.trans hs1))
      have hb := hK (Real.exp s) hx16
      have hcp : (Real.exp s : ℂ) ^ ρ = Complex.exp (ρ * (s : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'),
          ← Complex.ofReal_log (Real.exp_pos s).le, Real.log_exp, mul_comm]
      rw [hcp, ← Real.exp_half, Real.log_exp] at hb
      rw [Nat.cast_one, mul_one]
      change |Chebyshev.theta (Real.exp s) - Real.exp s +
          2 * (Complex.exp (ρ * (s : ℂ)) / ρ).re| ≤ B_t
      refine hb.trans ?_
      dsimp [B_t]
      have hexp_le : Real.exp (s / 2) ≤ Real.exp ((t + 2 * h) / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have hsq_le : s ^ 2 ≤ (1 + (t + 2 * h)) ^ 2 := by nlinarith
      calc K * Real.exp (s / 2) * s ^ 2
          ≤ |K| * Real.exp (s / 2) * s ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le) (sq_nonneg _)
        _ ≤ |K| * Real.exp ((t + 2 * h) / 2) * (1 + (t + 2 * h)) ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hexp_le (abs_nonneg _)) hsq_le (sq_nonneg _)
              (by positivity)
    have hdisc := abs_radialDiscrepancyOf_le_of_mode_error (f := thetaLogError) (t := t)
      hβ0.le hγ.ne' 1 (hm_step t le_rfl (by linarith))
      (hm_step (t + h) (by linarith) (by linarith))
      (hm_step (t + 2 * h) (by linarith) le_rfl)
    refine hdisc.trans ?_
    dsimp [B_t]
    have hexp_sp : Real.exp ((t + 2 * h) / 2) = Real.exp h * Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h1t : (1 + (t + 2 * h)) ^ 2 ≤ (1 + 2 * h) ^ 2 * (1 + t) ^ 2 := by
      have : 1 + (t + 2 * h) ≤ (1 + 2 * h) * (1 + t) := by nlinarith [ht, hh]
      exact (pow_le_pow_left₀ (by linarith) this 2).trans_eq (mul_pow _ _ 2)
    rw [hexp_sp]
    calc 4 * (|K| * (Real.exp h * Real.exp (t / 2)) * (1 + (t + 2 * h)) ^ 2)
        ≤ 4 * (|K| * (Real.exp h * Real.exp (t / 2)) * ((1 + 2 * h) ^ 2 * (1 + t) ^ 2)) := by
          gcongr
      _ = 4 * |K| * Real.exp h * (1 + 2 * h) ^ 2 * Real.exp (t / 2) * (1 + t) ^ 2 := by ring
  -- 2. Bounded `(2, 3, 6)` ordinary-prime dilation residuals
  have hdil (a : ℝ) (ha1 : 1 ≤ a) :
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual a β γ) := by
    let W (x : ℝ) : ℝ := -(2 * ((x : ℂ) ^ ρ / ρ).re)
    let R_rem (x : ℝ) : ℝ := (Chebyshev.theta x - x) - W x
    have hrem_b : ∀ x : ℝ, 16 ≤ x → |R_rem x| ≤ |K| * Real.sqrt x * (Real.log x) ^ 2 := by
      intro x hx
      have hb := hK x hx
      dsimp [R_rem, W]
      rw [sub_neg_eq_add]
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.sqrt_nonneg x)) (sq_nonneg _))
    obtain ⟨C_d, X_d, _, hC_d⟩ :=
      abs_dilationRecurrenceOp_le_of_sqrt_log_sq (β := β) (γ := γ) ha1 (abs_nonneg K) hrem_b
    rw [isSqrtLogSqUnbounded_iff_not_eventually_le, not_not]
    refine ⟨C_d, max X_d 16, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith [le_max_right X_d 16, hx]
    have ha0 : 0 < a := zero_lt_one.trans_le ha1
    -- `dilationRecurrenceOp a β γ W x = 0` for `x > 0`
    have hW_zero : dilationRecurrenceOp a β γ W x = 0 := by
      unfold dilationRecurrenceOp
      dsimp [W]
      have hcp_a (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
          ((u * v : ℝ) : ℂ) ^ ρ = (u : ℂ) ^ ρ * (v : ℂ) ^ ρ := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hu hv).ne'),
          Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
          Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne'),
          ← Complex.ofReal_log (mul_pos hu hv).le, ← Complex.ofReal_log hu.le,
          ← Complex.ofReal_log hv.le, Real.log_mul hu.ne' hv.ne', Complex.ofReal_add,
          add_mul, Complex.exp_add]
      have ha2 : ((a ^ 2 * x : ℝ) : ℂ) ^ ρ = ((a : ℂ) ^ ρ) ^ 2 * (x : ℂ) ^ ρ := by
        rw [sq a, mul_assoc, hcp_a a (a * x) ha0 (mul_pos ha0 hx0), hcp_a a x ha0 hx0,
          sq ((a : ℂ) ^ ρ), mul_assoc]
      have hchar : ((a : ℂ) ^ ρ) ^ 2 -
          (((2 * a ^ β * Real.cos (γ * Real.log a) : ℝ) : ℂ)) * (a : ℂ) ^ ρ +
          ((a ^ (2 * β) : ℝ) : ℂ) = 0 := by
        have hap : (a : ℂ) ^ ρ =
            ((a ^ β : ℝ) : ℂ) * Complex.exp (((γ * Real.log a : ℝ) : ℂ) * I) := by
          rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha0.ne'),
            ← Complex.ofReal_log ha0.le, Real.rpow_def_of_pos ha0, Complex.ofReal_exp,
            ← Complex.exp_add]
          congr 1; dsimp [ρ]; push_cast; ring
        have ha2b : a ^ (2 * β) = (a ^ β) ^ 2 := by
          rw [sq, ← Real.rpow_add ha0, two_mul]
        rw [hap, ha2b, Complex.exp_mul_I]
        have hsc : Complex.cos (((γ * Real.log a : ℝ) : ℂ)) ^ 2 +
            Complex.sin (((γ * Real.log a : ℝ) : ℂ)) ^ 2 = 1 :=
          Complex.cos_sq_add_sin_sq _
        have hc1 : (((2 * a ^ β * Real.cos (γ * Real.log a) : ℝ) : ℂ)) =
            2 * ((a ^ β : ℝ) : ℂ) * Complex.cos (((γ * Real.log a : ℝ) : ℂ)) := by
          push_cast; rfl
        have hc2 : (((a ^ β) ^ 2 : ℝ) : ℂ) = ((a ^ β : ℝ) : ℂ) ^ 2 := by push_cast; rfl
        have hI2 : (I : ℂ) ^ 2 = -1 := Complex.I_sq
        rw [hc1, hc2]
        linear_combination -(((a ^ β : ℝ) : ℂ) ^ 2) * hsc +
          (((a ^ β : ℝ) : ℂ) ^ 2 * Complex.sin (((γ * Real.log a : ℝ) : ℂ)) ^ 2) * hI2
      have hcomb : (((a ^ 2 * x : ℝ) : ℂ) ^ ρ / ρ) -
          (((2 * a ^ β * Real.cos (γ * Real.log a) : ℝ) : ℂ)) * (((a * x : ℝ) : ℂ) ^ ρ / ρ) +
          ((a ^ (2 * β) : ℝ) : ℂ) * ((x : ℂ) ^ ρ / ρ) = 0 := by
        rw [ha2, hcp_a a x ha0 hx0]
        linear_combination ((x : ℂ) ^ ρ / ρ) * hchar
      have hre := congrArg Complex.re hcomb
      simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.zero_re] at hre
      linarith only [hre]
    have htheta_eq : ordinaryThetaDilationResidual a β γ x =
        dilationRecurrenceOp a β γ R_rem x := by
      have hfun : (fun y => Chebyshev.theta y - y) = fun y => W y + R_rem y := by
        funext y; dsimp [R_rem]; ring
      change dilationRecurrenceOp a β γ (fun y => Chebyshev.theta y - y) x = _
      rw [hfun, dilationRecurrenceOp_add, hW_zero, zero_add]
    rw [htheta_eq]
    exact hC_d x ((le_max_left X_d 16).trans hx)
  exact ⟨hrad, hdil 2 (by norm_num), hdil 3 (by norm_num), hdil 6 (by norm_num)⟩

/-- **Eight-way unconditional equivalence characterizing a lone simple off-line quartet.** -/
theorem hasSimpleSingleOffLineQuartet_tfae {ρ₀ : ℂ} (hre : 1 / 2 < ρ₀.re) (him : 0 < ρ₀.im)
    (hmem : ρ₀ ∈ zetaZeroConfig.carrier) :
    [HasSimpleSingleOffLineQuartet ρ₀,
      HasSingleOffLineQuartet ρ₀ ∧ deriv riemannZeta ρ₀ ≠ 0,
      {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard = 2,
      {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.encard = 4,
      ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
        |Chebyshev.psi x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re| ≤ K * Real.sqrt x * (Real.log x) ^ 2,
      ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
        |Chebyshev.theta x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re| ≤ K * Real.sqrt x * (Real.log x) ^ 2,
      ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
        |oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊ +
            2 * ((x : ℂ) ^ ρ₀ / ρ₀).re| ≤ K * Real.sqrt x * (Real.log x) ^ 2,
      ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy ρ₀.re ρ₀.im 1) ∧
        ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 2 ρ₀.re ρ₀.im) ∧
        ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 3 ρ₀.re ρ₀.im) ∧
        ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 6 ρ₀.re ρ₀.im)].TFAE := by
  have hρ_eq : ((ρ₀.re : ℂ) + I * (ρ₀.im : ℂ)) = ρ₀ := by
    apply Complex.ext <;> simp
  tfae_have 1 ↔ 2 := hasSimpleSingleOffLineQuartet_iff_deriv_ne_zero ρ₀
  tfae_have 3 ↔ 4 := by
    rw [← rightXiZeroCopy_le_offLineXiZeroCopy_two_mul]
    constructor
    · intro h2; rw [h2]; norm_num
    · intro h4
      cases hc : {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard with
      | top => rw [hc] at h4; simp at h4
      | coe n =>
        rw [hc] at h4
        have hn : 2 * n = 4 := by exact_mod_cast h4
        exact_mod_cast (show n = 2 by omega)
  tfae_have 1 → 3 := by
    rintro ⟨hq, hm1⟩
    rw [rightXiZeroCopy_encard_of_singleQuartet hq, hm1]
    norm_num
  tfae_have 3 → 1 := by
    intro h2
    have hle2 : (rightZeros zetaZeroConfig).encard ≤ 2 :=
      rightZeros_le_rightXiZeroCopy_encard.trans h2.le
    have hne_conj : ρ₀ ≠ conj ρ₀ := fun he => by
      have := congrArg Complex.im he; simp at this; linarith
    have hc_mem : conj ρ₀ ∈ zetaZeroConfig.carrier := by
      have hxi_c : RHTower.xi (conj ρ₀) = 0 := by
        rw [xi_conj, xi_zero_of_mem_carrier hmem, map_zero]
      obtain ⟨qc, hqc⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi_c
      exact hqc ▸ xiZeroCopy_mem_carrier qc
    have hsub : ({ρ₀, conj ρ₀} : Set ℂ) ⊆ rightZeros zetaZeroConfig := by
      rintro z (rfl | rfl)
      · exact ⟨hmem, hre⟩
      · exact ⟨hc_mem, by simp; linarith [hre]⟩
    have hrz2 : (rightZeros zetaZeroConfig).encard = 2 :=
      le_antisymm hle2 ((Set.encard_pair hne_conj) ▸ Set.encard_mono hsub)
    have hright_eq : ({ρ₀, conj ρ₀} : Set ℂ) = rightZeros zetaZeroConfig :=
      ((Set.finite_singleton _).insert _).eq_of_subset_of_encard_le hsub
        (by rw [hrz2, Set.encard_pair hne_conj])
    have hq : HasSingleOffLineQuartet ρ₀ := by
      refine ⟨hre, hmem, ?_⟩
      ext z
      simp only [Set.mem_setOf_eq, zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hz_mem, hz_ne⟩
        rcases lt_or_gt_of_ne hz_ne with hlt | hgt
        · have hxi_z := xi_zero_of_mem_carrier hz_mem
          have hr_xi : RHTower.xi (1 - z) = 0 := by rw [xi_one_sub]; exact hxi_z
          obtain ⟨qr, hqr⟩ := exists_xiZeroCopy_of_xi_eq_zero hr_xi
          have hrefl : 1 - z ∈ rightZeros zetaZeroConfig :=
            ⟨hqr ▸ xiZeroCopy_mem_carrier qr, by simp; linarith⟩
          rw [← hright_eq] at hrefl
          rcases hrefl with h1 | h2'
          · right; right; left; linear_combination -h1
          · rw [Set.mem_singleton_iff] at h2'
            right; right; right; linear_combination -h2'
        · have hright : z ∈ rightZeros zetaZeroConfig := ⟨hz_mem, hgt⟩
          rw [← hright_eq] at hright
          rcases hright with rfl | h2'
          · exact Or.inl rfl
          · rw [Set.mem_singleton_iff] at h2'; exact Or.inr (Or.inl h2')
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨hmem, by linarith⟩
        · exact ⟨hc_mem, by simp; linarith⟩
        · have hr_xi : RHTower.xi (1 - ρ₀) = 0 := by
            rw [xi_one_sub]; exact xi_zero_of_mem_carrier hmem
          obtain ⟨qr, hqr⟩ := exists_xiZeroCopy_of_xi_eq_zero hr_xi
          exact ⟨hqr ▸ xiZeroCopy_mem_carrier qr, by simp; linarith⟩
        · have hrc_xi : RHTower.xi (1 - conj ρ₀) = 0 := by
            rw [xi_one_sub, xi_conj, xi_zero_of_mem_carrier hmem, map_zero]
          obtain ⟨qrc, hqrc⟩ := exists_xiZeroCopy_of_xi_eq_zero hrc_xi
          exact ⟨hqrc ▸ xiZeroCopy_mem_carrier qrc, by simp; linarith⟩
    have hcopy := rightXiZeroCopy_encard_of_singleQuartet hq
    rw [h2] at hcopy
    have hm_eq : 2 * quartetCopyMult ρ₀ = 2 := by exact_mod_cast hcopy.symm
    exact ⟨hq, by omega⟩
  tfae_have 1 → 5 := by
    rintro ⟨hq, hm1⟩
    obtain ⟨K, hK⟩ := (hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hre hmem).mp hq
    refine ⟨K, fun x hx => ?_⟩
    have hb := hK x hx
    rwa [hm1, Nat.cast_one, mul_one] at hb
  tfae_have 5 ↔ 6 := by
    obtain ⟨A, hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
    have hdiff (x : ℝ) (hx : 16 ≤ x) :
        |Chebyshev.psi x - Chebyshev.theta x| ≤ |A| * Real.sqrt x * (Real.log x) ^ 2 := by
      have hx0 : 0 < x := by linarith
      have hl1 : 1 ≤ Real.log x :=
        (Real.le_log_iff_exp_le hx0).mpr (by linarith [Real.exp_one_lt_three, hx])
      rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
      exact (hA x).trans ((mul_le_mul_of_nonneg_right (le_abs_self A) (Real.sqrt_nonneg x)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl1)))
    constructor
    · rintro ⟨K, hK⟩
      refine ⟨K + |A|, fun x hx => ?_⟩
      have htri := abs_sub (Chebyshev.psi x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re)
        (Chebyshev.psi x - Chebyshev.theta x)
      rw [show (Chebyshev.psi x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re) -
          (Chebyshev.psi x - Chebyshev.theta x) =
          Chebyshev.theta x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re by ring] at htri
      linarith only [htri, hK x hx, hdiff x hx]
    · rintro ⟨K, hK⟩
      refine ⟨K + |A|, fun x hx => ?_⟩
      have htri := abs_add_le (Chebyshev.theta x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re)
        (Chebyshev.psi x - Chebyshev.theta x)
      rw [show (Chebyshev.theta x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re) +
          (Chebyshev.psi x - Chebyshev.theta x) =
          Chebyshev.psi x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re by ring] at htri
      linarith only [htri, hK x hx, hdiff x hx]
  tfae_have 5 ↔ 7 := by
    obtain ⟨A, hA0, hodd⟩ := odd_composite_baseline_prime_error
    have hdiff (x : ℝ) (hx : 16 ≤ x) :
        |(oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) -
            (Chebyshev.psi x - x)| ≤ (A + 1) * Real.sqrt x * (Real.log x) ^ 2 := by
      have hx1 : 1 ≤ x := by linarith
      have hx0 : 0 < x := by linarith
      have hj : 0 < ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
      have hlo := Nat.floor_le hx0.le
      have hhi := Nat.lt_floor_add_one x
      have hb := hodd hj
      have hs := Real.sqrt_le_sqrt hlo
      have hs1 := Real.one_le_sqrt.mpr hx1
      have hl1 : 1 ≤ Real.log x :=
        (Real.le_log_iff_exp_le hx0).mpr (by linarith [Real.exp_one_lt_three, hx])
      have heq : (oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) -
          (Chebyshev.psi x - x) =
          ((oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) -
            (Chebyshev.psi ⌊x⌋₊ - ⌊x⌋₊)) + (x - ⌊x⌋₊) := by
        rw [Chebyshev.psi_eq_psi_coe_floor x]; ring
      rw [heq]
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
      refine le_trans (b := (A + 1) * Real.sqrt x) ?_
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl1))
      linarith only [hb, mul_le_mul_of_nonneg_left hs hA0, hs1, hhi]
    constructor
    · rintro ⟨K, hK⟩
      refine ⟨K + A + 1, fun x hx => ?_⟩
      have htri := abs_add_le
        ((oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) - (Chebyshev.psi x - x))
        (Chebyshev.psi x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re)
      rw [show (oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊ - (Chebyshev.psi x - x)) +
          (Chebyshev.psi x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re) =
          oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊ +
            2 * ((x : ℂ) ^ ρ₀ / ρ₀).re by ring] at htri
      linarith only [htri, hdiff x hx, hK x hx]
    · rintro ⟨K, hK⟩
      refine ⟨K + A + 1, fun x hx => ?_⟩
      have htri := abs_sub
        (oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊ + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re)
        ((oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) - (Chebyshev.psi x - x))
      rw [show (oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊ +
            2 * ((x : ℂ) ^ ρ₀ / ρ₀).re) -
          ((oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) - (Chebyshev.psi x - x)) =
          Chebyshev.psi x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re by ring] at htri
      linarith only [htri, hdiff x hx, hK x hx]
  tfae_have 6 → 8 := by
    intro hθ
    refine unit_theta_wave_implies_radial_and_236 hre hmem.2.2 him ?_
    rwa [hρ_eq]
  tfae_have 8 → 1 := by
    intro h8
    have hq_m := (radial_and_ordinary_236_iff_singleQuartet_with_mult hre hmem.2.2 him
      (le_refl 1)).mp h8
    rwa [hρ_eq] at hq_m
  tfae_finish

/-! ### 3. Complete absence of odd-harmonic Pythagorean aliases at unit multiplicity -/

/-- **Complete non-aliasing of any simple quartet (`m' = 1`).**
For any `γ ≠ 0` and `m ≥ 1`, if `IsOddHarmonicPythagoreanAlias β γ m ω 1 k` holds, then `k = 0`,
`m = 1`, and `ω = |γ|` — no simple off-line quartet can ever be aliased at a subharmonic trial,
even for rational `(γ / β)²`. -/
theorem unit_multiplicity_no_odd_harmonic_alias {β γ ω : ℝ} {m k : ℕ} (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (halias : IsOddHarmonicPythagoreanAlias β γ m ω 1 k) :
    k = 0 ∧ m = 1 ∧ ω = |γ| := by
  obtain ⟨hω, hpyth⟩ := halias
  rw [Nat.cast_one, one_pow, one_mul, hω] at hpyth
  have hγ2 : 0 < γ ^ 2 := sq_pos_of_ne_zero hγ
  have hmR1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hmR1]
  have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2k1 : 1 ≤ (2 * (k : ℝ) + 1) ^ 2 := by nlinarith only [hk_nn]
  have hk0R : (k : ℝ) = 0 := by
    by_contra hkne
    have hk_pos : 0 < (k : ℝ) := lt_of_le_of_ne hk_nn (Ne.symm hkne)
    have hgt : 1 < (2 * (k : ℝ) + 1) ^ 2 := by nlinarith only [hk_pos]
    have h1 : β ^ 2 + γ ^ 2 < β ^ 2 + (2 * (k : ℝ) + 1) ^ 2 * γ ^ 2 := by
      nlinarith only [hgt, hγ2]
    have h2 : β ^ 2 + (2 * (k : ℝ) + 1) ^ 2 * |γ| ^ 2 ≤
        (m : ℝ) ^ 2 * (β ^ 2 + ((2 * (k : ℝ) + 1) * |γ|) ^ 2) := by
      have hnn : 0 ≤ β ^ 2 + ((2 * (k : ℝ) + 1) * |γ|) ^ 2 := by positivity
      have he : β ^ 2 + (2 * (k : ℝ) + 1) ^ 2 * |γ| ^ 2 =
          1 * (β ^ 2 + ((2 * (k : ℝ) + 1) * |γ|) ^ 2) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hm2 hnn
    rw [sq_abs] at h2
    linarith only [hpyth, h1, h2]
  have hk0 : k = 0 := Nat.cast_eq_zero.mp hk0R
  subst hk0
  simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, sq_abs] at hpyth hω
  have hden : 0 < β ^ 2 + γ ^ 2 := by positivity
  have hm_sq1 : (m : ℝ) ^ 2 = 1 := by nlinarith only [hpyth, hden]
  have hm1R : (m : ℝ) = 1 := by nlinarith only [hm_sq1, hmR1]
  exact ⟨rfl, by exact_mod_cast hm1R, hω⟩

/-- Under `NoSimpleSingleOffLineQuartet`, any bounded unit-multiplicity trial
`¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ 1)` (`1/2 < β < 1`, `0 < γ`) forces `k ≥ 2`
and a ramified single off-line quartet at `β + i(2k + 1)γ` with `2 ≤ quartetCopyMult ≤ 2k` and
`deriv riemannZeta = 0`. -/
theorem unit_trial_under_noSimple_forces_ramified_quartet
    (hno : NoSimpleSingleOffLineQuartet) {β γ : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hbdd : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ 1)) :
    ∃ k : ℕ, 2 ≤ k ∧
      let ρ_k : ℂ := (β : ℂ) + I * (((2 * (k : ℝ) + 1) * γ : ℝ) : ℂ)
      HasSingleOffLineQuartet ρ_k ∧
      2 ≤ quartetCopyMult ρ_k ∧
      quartetCopyMult ρ_k ≤ 2 * k ∧
      deriv riemannZeta ρ_k = 0 := by
  obtain ⟨k, hq, halias⟩ :=
    (not_radialUnbounded_iff_singleQuartet_alias hβ hβ1 hγ (le_refl 1)).mp hbdd
  set ρ_k : ℂ := (β : ℂ) + I * (((2 * (k : ℝ) + 1) * γ : ℝ) : ℂ)
  have hm_ne1 : quartetCopyMult ρ_k ≠ 1 := fun hm1 => hno ρ_k ⟨hq, hm1⟩
  have hm_pos : 1 ≤ quartetCopyMult ρ_k := hq.quartetCopyMult_pos
  have hm_ge2 : 2 ≤ quartetCopyMult ρ_k := by omega
  have hder0 : deriv riemannZeta ρ_k = 0 :=
    (two_le_quartetCopyMult_iff_deriv_eq_zero hq.2.1).mp hm_ge2
  obtain ⟨hω, hpyth⟩ := halias
  rw [Nat.cast_one, one_pow, one_mul] at hpyth
  rw [abs_of_pos hγ] at hω
  have hk_ne0 : k ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul] at hpyth
    have hden : 0 < β ^ 2 + γ ^ 2 := by positivity
    have hm_sq : (quartetCopyMult ρ_k : ℝ) ^ 2 = 1 :=
      mul_right_cancel₀ hden.ne' (hpyth.trans (one_mul _).symm)
    have hm1R : (quartetCopyMult ρ_k : ℝ) = 1 := by
      nlinarith only [hm_sq, show (0 : ℝ) ≤ quartetCopyMult ρ_k by positivity]
    exact hm_ne1 (by exact_mod_cast hm1R)
  have hk_ge1 : 1 ≤ k := by omega
  have hm_le_2k : quartetCopyMult ρ_k ≤ 2 * k := by
    have hβ2 : 0 < β ^ 2 := by positivity
    have hden : 0 < β ^ 2 + γ ^ 2 := by positivity
    have hlt_sq : (quartetCopyMult ρ_k : ℝ) ^ 2 * (β ^ 2 + γ ^ 2) <
        ((2 * (k : ℝ) + 1) ^ 2) * (β ^ 2 + γ ^ 2) := by
      rw [hpyth]
      have hkR1 : (1 : ℝ) ≤ k := by exact_mod_cast hk_ge1
      nlinarith only [hβ2, hkR1]
    have hm_lt : (quartetCopyMult ρ_k : ℝ) ^ 2 < (2 * (k : ℝ) + 1) ^ 2 :=
      lt_of_mul_lt_mul_right hlt_sq hden.le
    have hm_lt' : (quartetCopyMult ρ_k : ℝ) < 2 * (k : ℝ) + 1 := by
      nlinarith only [hm_lt, show (0 : ℝ) ≤ quartetCopyMult ρ_k by positivity,
        show (0 : ℝ) ≤ 2 * (k : ℝ) + 1 by positivity]
    have hm_nat : quartetCopyMult ρ_k < 2 * k + 1 := by exact_mod_cast hm_lt'
    omega
  have hk_ne1 : k ≠ 1 := by
    rintro rfl
    have hm2 : quartetCopyMult ρ_k = 2 := by omega
    rw [hm2] at hpyth
    simp only [Nat.cast_one, Nat.cast_ofNat] at hpyth
    -- `4 * (β² + γ²) = β² + 9 γ²` gives `9 γ² = (27 / 5) β² < 16`, contradicting `4 < |Im ρ_k| = 3 γ`
    have h5γ2 : 5 * γ ^ 2 = 3 * β ^ 2 := by linarith only [hpyth]
    have h4_im := hq.four_lt_abs_im
    have him_eq : ρ_k.im = 3 * γ := by
      dsimp [ρ_k]; simp; ring
    rw [him_eq, abs_of_pos (by positivity)] at h4_im
    have h9 : 16 < (3 * γ) ^ 2 := by nlinarith only [h4_im]
    have hβ_sq1 : β ^ 2 < 1 := by nlinarith only [hβ, hβ1]
    nlinarith only [h5γ2, h9, hβ_sq1]
  exact ⟨k, by omega, hq, hm_ge2, hm_le_2k, hder0⟩

/-! ### 4. Reflected-composite rejection of radius imitators vs. intrinsic Beurling / twin models -/

private theorem clippedCofactorOp_add (n P : ℕ) (F G : ℝ → ℝ) :
    clippedCofactorOp n P (fun x => F x + G x) =
      clippedCofactorOp n P F + clippedCofactorOp n P G :=
  clippedCofactorSliceOp_add n P 1 F G

/-- General power-growth triangle bound for `clippedCofactorOp n ⌊2√n⌋₊`: if
`|h x| ≤ C * x ^ σ * (1 + log x) ^ r` (`0 ≤ σ < 1`) for `x ≥ 1`, then summing over the `≤ 4 n / P`
active cofactors yields `O(n^{(1 + σ) / 2} (1 + log(4n)) ^ r)`. -/
private theorem clippedCofactorOp_abs_le_of_rpow {h : ℝ → ℝ} {C σ : ℝ} {r : ℕ}
    (hC : 0 ≤ C) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hh : ∀ x : ℝ, 1 ≤ x → |h x| ≤ C * x ^ σ * (1 + Real.log x) ^ r) {n : ℕ} (hn : 1 ≤ n) :
    |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ h| ≤
      (64 * C / (1 - σ)) * (n : ℝ) ^ ((1 + σ) / 2) * (1 + Real.log (4 * (n : ℝ))) ^ r := by
  classical
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set P := ⌊2 * Real.sqrt n⌋₊
  have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
  have hlt_fl : 2 * Real.sqrt n < (P : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : Real.sqrt n ≤ (P : ℝ) := by linarith only [hsq1, hlt_fl]
  have hP1 : 1 ≤ P :=
    Nat.le_floor (by exact_mod_cast (by linarith only [hsq1] : (1 : ℝ) ≤ 2 * Real.sqrt n))
  have hP_le_4n : (P : ℝ) ≤ 4 * (n : ℝ) := by
    have hhi : (P : ℝ) ≤ 2 * Real.sqrt n := Nat.floor_le (by positivity)
    have hsq_n : Real.sqrt n ≤ n := by
      nlinarith only [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n), hsq1]
    linarith only [hhi, hsq_n, hnR]
  -- Active cofactors satisfy `v ≤ 4 * n / P`: when `4 * n / v ≤ P`, all three `max` equal `P`!
  let gv (v : ℕ) : ℝ :=
    h (max P (4 * n / v) : ℕ) - 2 * h (max P (3 * n / v) : ℕ) + h (max P (2 * n / v) : ℕ)
  set M := 4 * n / P
  have hsupp : clippedCofactorOp n P h =
      ∑ v ∈ ((Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ 1 ∣ v)).filter (· ≤ M), gv v := by
    unfold clippedCofactorOp clippedCofactorSliceOp
    change ∑ v ∈ (Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ 1 ∣ v), gv v = _
    rw [← Finset.sum_subset
      (Finset.filter_subset (· ≤ M) ((Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ 1 ∣ v)))]
    intro v hv hvnot
    have hv0 : 0 < v := by linarith [(mem_Icc.mp (mem_filter.mp hv).1).1]
    have hgt : M < v := not_le.mp fun hle => hvnot (mem_filter.mpr ⟨hv, hle⟩)
    have hmul : 4 * n < v * P := (Nat.div_lt_iff_lt_mul (by omega : 0 < P)).mp hgt
    have h4 : 4 * n / v < P :=
      (Nat.div_lt_iff_lt_mul hv0).mpr (by rw [mul_comm P v]; exact hmul)
    have h3 : 3 * n / v ≤ P := (Nat.div_le_div_right (by omega : 3 * n ≤ 4 * n)).trans h4.le
    have h2 : 2 * n / v ≤ P := (Nat.div_le_div_right (by omega : 2 * n ≤ 4 * n)).trans h4.le
    dsimp [gv]
    rw [max_eq_left h4.le, max_eq_left h3, max_eq_left h2]
    ring
  -- Bound each active `|gv v|` for `v ∈ Icc 1 M` by `4 * C * (8 * n / v)^σ * (1 + log(4n))^r`
  have hgv_le (v : ℕ) (hv1 : 1 ≤ v) (hvM : v ≤ M) :
      |gv v| ≤ 16 * C * (n : ℝ) ^ σ * (v : ℝ) ^ (-σ) * (1 + Real.log (4 * (n : ℝ))) ^ r := by
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv1
    have hPv : v * P ≤ 4 * n := (Nat.le_div_iff_mul_le (by omega : 0 < P)).mp hvM
    have hP_le_4nv : P ≤ 4 * n / v :=
      (Nat.le_div_iff_mul_le hv1).mpr (by rwa [mul_comm])
    have hk_b (k : ℕ) (hk4 : k ≤ 4) :
        |h (max P (k * n / v) : ℕ)| ≤
          4 * C * (n : ℝ) ^ σ * (v : ℝ) ^ (-σ) * (1 + Real.log (4 * (n : ℝ))) ^ r := by
      set x := ((max P (k * n / v) : ℕ) : ℝ)
      have hx1 : 1 ≤ x := by
        dsimp [x]; exact_mod_cast hP1.trans (le_max_left P _)
      have hx_4nv : x ≤ 4 * (n : ℝ) / v := by
        dsimp [x]
        have hm1 : max P (k * n / v) ≤ 4 * n / v :=
          max_le hP_le_4nv (Nat.div_le_div_right (Nat.mul_le_mul_right n hk4))
        exact (by exact_mod_cast hm1 : ((max P (k * n / v) : ℕ) : ℝ) ≤ ((4 * n / v : ℕ) : ℝ)).trans
          (Nat.cast_div_le.trans_eq (by push_cast; rfl))
      have hx_4n : x ≤ 4 * (n : ℝ) :=
        hx_4nv.trans (div_le_self (by positivity) (by exact_mod_cast hv1))
      have hrp : x ^ σ ≤ 4 * (n : ℝ) ^ σ * (v : ℝ) ^ (-σ) := by
        have h1 := Real.rpow_le_rpow (by positivity) hx_4nv hσ0
        rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by norm_num) hn0.le, Real.inv_rpow hvR.le,
          ← Real.rpow_neg hvR.le] at h1
        have h4s : (4 : ℝ) ^ σ ≤ 4 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hσ1.le
        exact h1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h4s (Real.rpow_nonneg hn0.le σ))
          (Real.rpow_nonneg hvR.le _))
      have hlg : (1 + Real.log x) ^ r ≤ (1 + Real.log (4 * (n : ℝ))) ^ r :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hx1])
          (by linarith [Real.log_le_log (by linarith) hx_4n]) r
      calc |h x| ≤ C * x ^ σ * (1 + Real.log x) ^ r := hh x hx1
        _ ≤ C * (4 * (n : ℝ) ^ σ * (v : ℝ) ^ (-σ)) * (1 + Real.log (4 * (n : ℝ))) ^ r :=
            mul_le_mul (mul_le_mul_of_nonneg_left hrp hC) hlg
              (pow_nonneg (by linarith [Real.log_nonneg hx1]) r) (by positivity)
        _ = 4 * C * (n : ℝ) ^ σ * (v : ℝ) ^ (-σ) * (1 + Real.log (4 * (n : ℝ))) ^ r := by ring
    dsimp [gv]
    obtain ⟨l4, u4⟩ := abs_le.mp (hk_b 4 (by decide))
    obtain ⟨l3, u3⟩ := abs_le.mp (hk_b 3 (by decide))
    obtain ⟨l2, u2⟩ := abs_le.mp (hk_b 2 (by decide))
    rw [abs_le]; constructor <;> linarith only [l4, u4, l3, u3, l2, u2]
  -- Bound `∑_{v ∈ Icc 1 M} (v : ℝ) ^ (-σ) ≤ (1 / (1 - σ)) * (M : ℝ) ^ (1 - σ)` by MVT telescoping
  have hsum_vpow (K_m : ℕ) :
      ∑ v ∈ Icc 1 K_m, (v : ℝ) ^ (-σ) ≤ (1 / (1 - σ)) * (K_m : ℝ) ^ (1 - σ) := by
    have ha_pos : 0 < 1 - σ := sub_pos.mpr hσ1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha_pos, Finset.sum_mul]
    induction K_m with
    | zero =>
      simp [Real.zero_rpow ha_pos.ne']
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp; linarith
      · have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
        -- MVT: `(1 - σ) * (m + 1)^{-σ} ≤ (m + 1)^{1 - σ} - m^{1 - σ}`
        have hstep : ((m + 1 : ℕ) : ℝ) ^ (-σ) * (1 - σ) ≤
            ((m + 1 : ℕ) : ℝ) ^ (1 - σ) - (m : ℝ) ^ (1 - σ) := by
          have h0_mem : (0 : ℝ) ∉ Set.uIcc (m : ℝ) ((m + 1 : ℕ) : ℝ) := by
            rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ m)]
            intro hmem; linarith [hmem.1]
          have hint := integral_rpow (a := (m : ℝ)) (b := ((m + 1 : ℕ) : ℝ)) (r := -σ)
            (Or.inr ⟨by linarith, h0_mem⟩)
          have hexp1 : -σ + 1 = 1 - σ := by ring
          rw [hexp1] at hint
          have heq_int : ((m + 1 : ℕ) : ℝ) ^ (1 - σ) - (m : ℝ) ^ (1 - σ) =
              (1 - σ) * ∫ u in (m : ℝ)..((m + 1 : ℕ) : ℝ), u ^ (-σ) := by
            rw [hint]; field_simp [ha_pos.ne']
          rw [heq_int, mul_comm _ (1 - σ)]
          refine mul_le_mul_of_nonneg_left ?_ ha_pos.le
          have hconst_int : ∫ _u in (m : ℝ)..((m + 1 : ℕ) : ℝ), ((m + 1 : ℕ) : ℝ) ^ (-σ) =
              ((m + 1 : ℕ) : ℝ) ^ (-σ) := by
            rw [intervalIntegral.integral_const,
              show ((m + 1 : ℕ) : ℝ) - (m : ℝ) = 1 by push_cast; ring, one_smul]
          rw [← hconst_int]
          refine intervalIntegral.integral_mono_on (by exact_mod_cast Nat.le_succ m)
            intervalIntegrable_const
            (intervalIntegral.intervalIntegrable_rpow (Or.inr h0_mem)) fun u hu => ?_
          exact Real.rpow_le_rpow_of_nonpos (hmR.trans_le hu.1) hu.2 (by linarith)
        linarith only [ih, hstep]
  have hM_le : (M : ℝ) ≤ 4 * Real.sqrt n := by
    dsimp [M]
    have h1 : ((4 * n / P : ℕ) : ℝ) ≤ 4 * (n : ℝ) / (P : ℝ) := by
      exact Nat.cast_div_le.trans_eq (by push_cast; rfl)
    have h2 : 4 * (n : ℝ) / (P : ℝ) ≤ 4 * (n : ℝ) / Real.sqrt n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlo
    have h3 : 4 * (n : ℝ) / Real.sqrt n = 4 * Real.sqrt n := by
      rw [div_eq_iff (by positivity), mul_assoc, Real.mul_self_sqrt (by positivity)]
    exact h1.trans (h2.trans_eq h3)
  rw [hsupp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsub_M : ((Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ 1 ∣ v)).filter (· ≤ M) ⊆
      Icc 1 M := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := mem_filter.mp hv
    exact mem_Icc.mpr ⟨by linarith [(mem_Icc.mp (mem_filter.mp hv1).1).1], hv2⟩
  calc ∑ v ∈ ((Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ 1 ∣ v)).filter (· ≤ M), |gv v|
      ≤ ∑ v ∈ ((Icc 2 (4 * n)).filter (fun v => n.Coprime v ∧ 1 ∣ v)).filter (· ≤ M),
          16 * C * (n : ℝ) ^ σ * (v : ℝ) ^ (-σ) * (1 + Real.log (4 * (n : ℝ))) ^ r :=
        Finset.sum_le_sum fun v hv => hgv_le v
          (by linarith [(mem_Icc.mp (mem_filter.mp (mem_filter.mp hv).1).1).1])
          (mem_filter.mp hv).2
    _ ≤ ∑ v ∈ Icc 1 M,
          16 * C * (n : ℝ) ^ σ * (v : ℝ) ^ (-σ) * (1 + Real.log (4 * (n : ℝ))) ^ r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_M fun v _ _ =>
          mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hn0.le σ))
            (Real.rpow_nonneg (Nat.cast_nonneg v) _))
            (pow_nonneg (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * n)]) r)
    _ = 16 * C * (n : ℝ) ^ σ * (1 + Real.log (4 * (n : ℝ))) ^ r *
          ∑ v ∈ Icc 1 M, (v : ℝ) ^ (-σ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ 16 * C * (n : ℝ) ^ σ * (1 + Real.log (4 * (n : ℝ))) ^ r *
          ((1 / (1 - σ)) * (M : ℝ) ^ (1 - σ)) :=
        mul_le_mul_of_nonneg_left (hsum_vpow M)
          (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hn0.le σ))
            (pow_nonneg (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * n)]) r))
    _ ≤ 16 * C * (n : ℝ) ^ σ * (1 + Real.log (4 * (n : ℝ))) ^ r *
          ((1 / (1 - σ)) * (4 * (n : ℝ) ^ ((1 - σ) / 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hn0.le σ))
            (pow_nonneg (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * n)]) r))
        have hr1 := Real.rpow_le_rpow (z := 1 - σ) (Nat.cast_nonneg M) hM_le (by linarith)
        rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg n), Real.sqrt_eq_rpow,
          ← Real.rpow_mul hn0.le, show (1 / 2 : ℝ) * (1 - σ) = (1 - σ) / 2 by ring] at hr1
        have h4_le : (4 : ℝ) ^ (1 - σ) ≤ 4 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) (by linarith)
        exact hr1.trans (mul_le_mul_of_nonneg_right h4_le (Real.rpow_nonneg hn0.le _))
    _ = (64 * C / (1 - σ)) * ((n : ℝ) ^ σ * (n : ℝ) ^ ((1 - σ) / 2)) *
          (1 + Real.log (4 * (n : ℝ))) ^ r := by ring
    _ = (64 * C / (1 - σ)) * (n : ℝ) ^ ((1 + σ) / 2) * (1 + Real.log (4 * (n : ℝ))) ^ r := by
        rw [← Real.rpow_add hn0]; congr 3; ring

/-- Master non-`ζ`-zero lower bound: if `|F(x) - x - quartetWaveModel z m x| ≤ C x^σ (1 + log x)^r`
with `(1 + σ) / 2 < Re z` and `riemannZeta z ≠ 0` (`m ≠ 0`), then `F` violates the reflected-composite
identity at scale `Ω(n^{Re z})` along infinitely many prime powers coprime to any modulus `Q`. -/
private theorem reflectedComposite_violated_of_mode_approx {F : ℝ → ℝ} {z : ℂ} {m C σ : ℝ}
    {r Q : ℕ} (hQ : 1 ≤ Q) (hz0 : 1 / 2 < z.re) (hz1 : z.re < 1) (hzim : z.im ≠ 0) (hm : m ≠ 0)
    (hζ_ne : riemannZeta z ≠ 0) (hC : 0 ≤ C) (hσ0 : 0 ≤ σ) (hσ_lt : (1 + σ) / 2 < z.re)
    (hmode : ∀ x : ℝ, 1 ≤ x → |F x - x - quartetWaveModel z m x| ≤ C * x ^ σ * (1 + Real.log x) ^ r) :
    ∃ (p : ℕ) (c₀ : ℝ), p.Prime ∧ Q < p ∧ 0 < c₀ ∧
      ∀ᶠ k : ℕ in atTop,
        ∃ n ∈ ({p ^ k, p ^ (k + 1)} : Finset ℕ),
          n.Coprime Q ∧ squarefreeDivisorMass n = 2 ∧
          c₀ * (n : ℝ) ^ z.re ≤
            |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ F - reflectedDensity * (n.totient : ℝ) -
                midpointSecondDiff n F| := by
  have hz_pos : 0 < z.re := by linarith
  have hzne0 : z ≠ 0 := fun he => by rw [he, Complex.zero_re] at hz_pos; exact lt_irrefl 0 hz_pos
  have hσ1 : σ < 1 := by linarith
  have hA_ne : (midpointMultiplier z / z) * riemannZeta z ≠ 0 :=
    mul_ne_zero (div_ne_zero (midpointMultiplier_ne_zero hz_pos hz1) hzne0) hζ_ne
  obtain ⟨p, c, hp, hQp, hc_pos, hpeaks⟩ :=
    exists_prime_power_re_lower_bound hQ hz_pos hzim hA_ne
  set c₀ : ℝ := |m| * c
  have hc₀_pos : 0 < c₀ := mul_pos (abs_pos.mpr hm) hc_pos
  refine ⟨p, c₀, hp, hQp, hc₀_pos, ?_⟩
  -- Pick intermediate exponent `η = ((1 + σ) / 2 + z.re) / 2 ∈ ((1 + σ)/2, z.re)` to absorb logs and `√n`
  set η : ℝ := (max (1 / 2) ((1 + σ) / 2) + z.re) / 2
  have hη_gt_half : 1 / 2 < η := by
    dsimp [η]; linarith [le_max_left (1 / 2) ((1 + σ) / 2)]
  have hη_gt_sig : (1 + σ) / 2 < η := by
    dsimp [η]; linarith [le_max_right (1 / 2) ((1 + σ) / 2)]
  have hη_lt_re : η < z.re := by
    dsimp [η]; linarith [max_lt hz0 hσ_lt]
  -- Coarse bound `(1 + log(4 * y)) ^ r ≤ B_lg * y ^ (η - (1 + σ) / 2)` for `y ≥ 1`
  have hlog_pow_le : ∃ B_lg : ℝ, 0 ≤ B_lg ∧ ∀ y : ℝ, 1 ≤ y →
      (1 + Real.log (4 * y)) ^ r ≤ B_lg * y ^ (η - (1 + σ) / 2) := by
    set δ : ℝ := (η - (1 + σ) / 2) / ((r : ℝ) + 1)
    have hδ : 0 < δ := div_pos (by linarith) (by positivity)
    refine ⟨(3 + 1 / δ) ^ r, by positivity, fun y hy => ?_⟩
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    have h1_term : 1 + Real.log (4 * y) ≤ (3 + 1 / δ) * y ^ δ := by
      have hyδ_pos : 0 < y ^ δ := Real.rpow_pos_of_pos hy0 δ
      have hl_y := Real.log_le_sub_one_of_pos hyδ_pos
      rw [Real.log_rpow hy0] at hl_y
      have hlog4 : 1 + Real.log 4 ≤ 3 := by
        have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; rfl
        linarith
      have hlog_mul : 1 + Real.log (4 * y) = 1 + Real.log 4 + (1 / δ) * (δ * Real.log y) := by
        rw [Real.log_mul (by norm_num) hy0.ne']; field_simp [hδ.ne']; ring
      have hyδ1 : 1 ≤ y ^ δ := Real.one_le_rpow hy hδ.le
      have h1_d : (1 / δ) * (δ * Real.log y) ≤ (1 / δ) * y ^ δ :=
        mul_le_mul_of_nonneg_left (by linarith only [hl_y]) (by positivity)
      have h3 : 1 + Real.log 4 ≤ 3 * y ^ δ := by linarith only [hlog4, hyδ1]
      linarith only [hlog_mul, h3, h1_d]
    calc (1 + Real.log (4 * y)) ^ r
        ≤ ((3 + 1 / δ) * y ^ δ) ^ r :=
          pow_le_pow_left₀ (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * y)])
            h1_term r
      _ = (3 + 1 / δ) ^ r * (y ^ δ) ^ r := mul_pow _ _ _
      _ = (3 + 1 / δ) ^ r * y ^ (δ * (r : ℝ)) := by
          rw [← Real.rpow_natCast (y ^ δ) r, ← Real.rpow_mul hy0.le]
      _ ≤ (3 + 1 / δ) ^ r * y ^ (η - (1 + σ) / 2) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy ?_) (by positivity)
          have hrr1 : (r : ℝ) ≤ (r : ℝ) + 1 := by linarith
          calc δ * (r : ℝ) ≤ δ * ((r : ℝ) + 1) := mul_le_mul_of_nonneg_left hrr1 hδ.le
            _ = η - (1 + σ) / 2 := div_mul_cancel₀ _ (by positivity)
  obtain ⟨B_lg, hB_lg, hlg⟩ := hlog_pow_le
  let R (x : ℝ) : ℝ := F x - x - quartetWaveModel z m x
  have hF_split : F = fun x => (x + quartetWaveModel z m x) + R x := by
    funext x; dsimp [R]; ring
  set K_err : ℝ :=
    2 * (68 + 6 * |m| * waveTransmissionRate z) + (64 * C / (1 - σ) + 16 * C) * B_lg
  have hK_err_nn : 0 ≤ K_err := by
    have hw_nn := waveTransmissionRate_nonneg hz_pos
    dsimp [K_err]; positivity
  -- Uniform `O(n^η)` bound on all non-oscillatory and remainder pieces when `squarefreeDivisorMass n = 2`
  have herr_n (n : ℕ) (hn2 : 2 ≤ n) (hmass2 : squarefreeDivisorMass n = 2) :
      |(clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ F - reflectedDensity * (n.totient : ℝ) -
            midpointSecondDiff n F) -
          2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
            ((n : ℝ) : ℂ) ^ z).re| ≤
        K_err * (n : ℝ) ^ η := by
    have hn1 : 1 ≤ n := by omega
    have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hnR1
    set P := ⌊2 * Real.sqrt n⌋₊
    have hbase := clippedCofactorOp_linear_add_wave_defect hn1 hz_pos hz1 m
    rw [hmass2] at hbase
    have hsqrt_le : Real.sqrt n ≤ (n : ℝ) ^ η := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hnR1 hη_gt_half.le
    have hbase' :
        |(clippedCofactorOp n P (fun x => x + quartetWaveModel z m x) -
              reflectedDensity * (n.totient : ℝ) -
              midpointSecondDiff n (fun x => x + quartetWaveModel z m x)) -
            2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
              ((n : ℝ) : ℂ) ^ z).re| ≤
          2 * (68 + 6 * |m| * waveTransmissionRate z) * (n : ℝ) ^ η := by
      have hw_nn := waveTransmissionRate_nonneg hz_pos
      calc _ ≤ (68 + 6 * |m| * waveTransmissionRate z) * Real.sqrt n * 2 := hbase
        _ = 2 * (68 + 6 * |m| * waveTransmissionRate z) * Real.sqrt n := by ring
        _ ≤ 2 * (68 + 6 * |m| * waveTransmissionRate z) * (n : ℝ) ^ η :=
            mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
    have hclip_R : |clippedCofactorOp n P R| ≤ (64 * C / (1 - σ)) * B_lg * (n : ℝ) ^ η := by
      have hcR := clippedCofactorOp_abs_le_of_rpow (h := R) hC hσ0 hσ1 hmode hn1
      calc |clippedCofactorOp n P R|
          ≤ (64 * C / (1 - σ)) * (n : ℝ) ^ ((1 + σ) / 2) * (1 + Real.log (4 * (n : ℝ))) ^ r := hcR
        _ ≤ (64 * C / (1 - σ)) * (n : ℝ) ^ ((1 + σ) / 2) *
              (B_lg * (n : ℝ) ^ (η - (1 + σ) / 2)) :=
            mul_le_mul_of_nonneg_left (hlg n hnR1)
              (mul_nonneg (by positivity) (Real.rpow_nonneg hn0.le _))
        _ = (64 * C / (1 - σ)) * B_lg *
              ((n : ℝ) ^ ((1 + σ) / 2) * (n : ℝ) ^ (η - (1 + σ) / 2)) := by ring
        _ = (64 * C / (1 - σ)) * B_lg * (n : ℝ) ^ η := by
            rw [← Real.rpow_add hn0, add_sub_cancel]
    have hmid_R : |midpointSecondDiff n R| ≤ 16 * C * B_lg * (n : ℝ) ^ η := by
      have hk_R (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
          |R (k * n : ℕ)| ≤ 4 * C * B_lg * (n : ℝ) ^ η := by
        have hkn1 : (1 : ℝ) ≤ (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk1 hn1
        have hkn_4n : ((k * n : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by
          push_cast; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk4) hn0.le
        have hr_kn : ((k * n : ℕ) : ℝ) ^ σ ≤ 4 * (n : ℝ) ^ ((1 + σ) / 2) := by
          have h1 := Real.rpow_le_rpow (by positivity) hkn_4n hσ0
          rw [Real.mul_rpow (by norm_num) hn0.le] at h1
          have h4 : (4 : ℝ) ^ σ ≤ 4 := by
            simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hσ1.le
          have hn_sig : (n : ℝ) ^ σ ≤ (n : ℝ) ^ ((1 + σ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)
          exact h1.trans (mul_le_mul h4 hn_sig (Real.rpow_nonneg hn0.le _) (by norm_num))
        have hlg_kn : (1 + Real.log (k * n : ℕ)) ^ r ≤ B_lg * (n : ℝ) ^ (η - (1 + σ) / 2) := by
          refine (pow_le_pow_left₀ (by linarith [Real.log_nonneg hkn1])
            (by linarith [Real.log_le_log (by positivity) hkn_4n] :
              1 + Real.log (k * n : ℕ) ≤ 1 + Real.log (4 * (n : ℝ))) r).trans (hlg n hnR1)
        calc |R (k * n : ℕ)|
            ≤ C * ((k * n : ℕ) : ℝ) ^ σ * (1 + Real.log (k * n : ℕ)) ^ r := hmode _ hkn1
          _ ≤ C * (4 * (n : ℝ) ^ ((1 + σ) / 2)) * (B_lg * (n : ℝ) ^ (η - (1 + σ) / 2)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hr_kn hC) hlg_kn (by positivity)
                (mul_nonneg hC (by positivity))
          _ = 4 * C * B_lg * ((n : ℝ) ^ ((1 + σ) / 2) * (n : ℝ) ^ (η - (1 + σ) / 2)) := by ring
          _ = 4 * C * B_lg * (n : ℝ) ^ η := by rw [← Real.rpow_add hn0, add_sub_cancel]
      unfold midpointSecondDiff
      obtain ⟨l2, u2⟩ := abs_le.mp (hk_R 2 (by decide) (by decide))
      obtain ⟨l3, u3⟩ := abs_le.mp (hk_R 3 (by decide) (by decide))
      obtain ⟨l4, u4⟩ := abs_le.mp (hk_R 4 (by decide) (by decide))
      rw [abs_le]; constructor <;> linarith only [l2, u2, l3, u3, l4, u4]
    have hmid_add : midpointSecondDiff n F =
        midpointSecondDiff n (fun x => x + quartetWaveModel z m x) + midpointSecondDiff n R := by
      unfold midpointSecondDiff; dsimp [R]; ring
    rw [hmid_add]
    conv_lhs => rw [hF_split]
    rw [clippedCofactorOp_add]
    set B₀ := (clippedCofactorOp n P (fun x => x + quartetWaveModel z m x) -
        reflectedDensity * (n.totient : ℝ) -
        midpointSecondDiff n (fun x => x + quartetWaveModel z m x)) -
      2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
        ((n : ℝ) : ℂ) ^ z).re
    have hid_tot :
        (clippedCofactorOp n P (fun x => x + quartetWaveModel z m x) + clippedCofactorOp n P R -
            reflectedDensity * (n.totient : ℝ) -
            (midpointSecondDiff n (fun x => x + quartetWaveModel z m x) + midpointSecondDiff n R)) -
          2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
            ((n : ℝ) : ℂ) ^ z).re =
        B₀ + clippedCofactorOp n P R - midpointSecondDiff n R := by dsimp [B₀]; ring
    change |(clippedCofactorOp n P (fun x => x + quartetWaveModel z m x) +
          clippedCofactorOp n P R - reflectedDensity * (n.totient : ℝ) - _) - _| ≤ _
    rw [hid_tot]
    have htri := (abs_sub (B₀ + clippedCofactorOp n P R) (midpointSecondDiff n R)).trans
      (add_le_add (abs_add_le B₀ (clippedCofactorOp n P R)) le_rfl)
    rw [show K_err =
      2 * (68 + 6 * |m| * waveTransmissionRate z) + (64 * C / (1 - σ) + 16 * C) * B_lg from rfl]
    linarith only [htri, hbase', hclip_R, hmid_R]
  -- Asymptotically `2 c₀ n^{z.re} - K_err n^η ≥ c₀ n^{z.re}` since `η < z.re`
  have hgap : 0 < z.re - η := sub_pos.mpr hη_lt_re
  have hpow_tend : Tendsto (fun k : ℕ => ((p ^ k : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => by exact_mod_cast (Nat.lt_pow_self hp.one_lt).le)
      tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun k : ℕ => ((p ^ k : ℕ) : ℝ) ^ (z.re - η)) atTop atTop :=
    (_root_.tendsto_rpow_atTop hgap).comp hpow_tend
  filter_upwards [eventually_ge_atTop 1, htend.eventually_ge_atTop (K_err / c₀)] with k hk1 hbig
  obtain ⟨n, hn_mem, hncop, hmass2, hpk⟩ := hpeaks k hk1
  refine ⟨n, hn_mem, hncop, hmass2, ?_⟩
  have hn_ge_pk : p ^ k ≤ n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn_mem
    rcases hn_mem with rfl | rfl
    · exact le_rfl
    · exact Nat.pow_le_pow_right hp.pos (Nat.le_succ k)
  have hn2 : 2 ≤ n := (by simpa using hp.two_le : 2 ≤ p ^ 1).trans
    ((Nat.pow_le_pow_right hp.pos hk1).trans hn_ge_pk)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have herr := herr_n n hn2 hmass2
  have hosc_ge : 2 * c₀ * (n : ℝ) ^ z.re ≤
      |2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
        ((n : ℝ) : ℂ) ^ z).re| := by
    rw [show c₀ = |m| * c from rfl]
    conv_rhs => rw [abs_mul, abs_mul, abs_of_pos two_pos]
    calc 2 * (|m| * c) * (n : ℝ) ^ z.re
        = 2 * |m| * (c * (n : ℝ) ^ z.re) := by ring
      _ ≤ 2 * |m| * |((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
            ((n : ℝ) : ℂ) ^ z).re| :=
          mul_le_mul_of_nonneg_left hpk (mul_nonneg zero_le_two (abs_nonneg m))
  have hrpow_n : K_err / c₀ ≤ (n : ℝ) ^ (z.re - η) :=
    hbig.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_ge_pk) hgap.le)
  have hK_le : K_err * (n : ℝ) ^ η ≤ c₀ * (n : ℝ) ^ z.re := by
    have hm1 := (div_le_iff₀ hc₀_pos).mp hrpow_n
    have hm2 := mul_le_mul_of_nonneg_right hm1 (Real.rpow_nonneg hn0.le η)
    rwa [mul_comm _ c₀, mul_assoc, ← Real.rpow_add hn0, sub_add_cancel] at hm2
  set D := clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ F - reflectedDensity * (n.totient : ℝ) -
    midpointSecondDiff n F
  set W_osc := 2 * m * ((midpointMultiplier z / z) * riemannZeta z * coprimeEulerFactor n z *
    ((n : ℝ) : ℂ) ^ z).re
  have htri : |W_osc| ≤ |D - W_osc| + |D| := by
    have h := abs_add_le (W_osc - D) D
    rwa [sub_add_cancel, abs_sub_comm W_osc D] at h
  linarith only [htri, herr, hosc_ge, hK_le]

/-- **Reflected-composite rejection of `{0, 1}`-coprime radius imitators across all `1/2 < β < 1`.**
At any non-`ζ`-zero `(β, γ)` (`1/2 < β < 1`, `γ ≠ 0`, `ζ(β + iγ) ≠ 0`), `exists_coprimeZeroOneSet_realizing_twoIntervalRadius`
produces a `{0, 1}`-valued coprime indicator `w : ℕ → ℕ` whose log-summatory `θ_w` simultaneously
realizes bounded two-interval radius and bounded dilation recurrences (`a ≥ 1`), yet violates the
ordinary-integer reflected-composite identity at scale `Ω(n^β)` along infinitely many prime powers. -/
theorem coprimeZeroOneSet_imitator_rejected_by_reflectedComposites {β γ : ℝ} {m Q : ℕ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : γ ≠ 0) (hm : 1 ≤ m) (hQ : 1 ≤ Q)
    (hζ_ne : riemannZeta ((β : ℂ) + I * (γ : ℂ)) ≠ 0) :
    ∃ w : ℕ → ℕ,
      (∀ n : ℕ, (w n = 0 ∨ w n = 1) ∧ (w n = 1 → 2 ≤ n ∧ Nat.Coprime n Q)) ∧
      let θ_w : ℝ → ℝ := fun x => ∑ k ∈ Icc 1 ⌊x⌋₊, (w k : ℝ) * Real.log k
      let E_w : ℝ → ℝ := fun t => θ_w (Real.exp t) - Real.exp t
      ¬ IsLogSqrtSqUnbounded (radialDiscrepancyOf E_w β γ m) ∧
      HasPositivePowerLimsup (fun x => θ_w x - x) β ∧
      (∀ a : ℝ, 1 ≤ a → ¬ IsSqrtLogSqUnbounded (dilationRecurrenceOp a β |γ| (fun x => θ_w x - x))) ∧
      (∃ (p : ℕ) (c₀ : ℝ), p.Prime ∧ Q < p ∧ 0 < c₀ ∧
        ∀ᶠ k : ℕ in atTop,
          ∃ n ∈ ({p ^ k, p ^ (k + 1)} : Finset ℕ),
            n.Coprime Q ∧ squarefreeDivisorMass n = 2 ∧
            c₀ * (n : ℝ) ^ β ≤
              |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ θ_w - reflectedDensity * (n.totient : ℝ) -
                  midpointSecondDiff n θ_w|) := by
  obtain ⟨w, hw_props, hrest⟩ :=
    exists_coprimeZeroOneSet_realizing_twoIntervalRadius hβ hβ1 hγ hm hQ
  refine ⟨w, hw_props, ?_⟩
  intro θ_w E_w
  obtain ⟨⟨C, hC, hmode⟩, _, _, hrad, hlim, hdil⟩ := hrest
  set z : ℂ := (β : ℂ) + I * (γ : ℂ)
  have hz_re : z.re = β := by simp [z]
  have hz_im : z.im = γ := by simp [z]
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hmode' : ∀ x : ℝ, 1 ≤ x →
      |θ_w x - x - quartetWaveModel z (m : ℝ) x| ≤ C * x ^ (0 : ℝ) * (1 + Real.log x) ^ 1 := by
    intro x hx
    rw [Real.rpow_zero, mul_one, pow_one, quartetWaveModel, sub_neg_eq_add]
    exact hmode x hx
  obtain ⟨p, c₀, hp, hQp, hc₀, hviol⟩ := reflectedComposite_violated_of_mode_approx hQ
    (hz_re.symm ▸ hβ) (hz_re.symm ▸ hβ1) (hz_im.symm ▸ hγ) hm_ne hζ_ne hC le_rfl
    (by rw [hz_re]; linarith) hmode'
  rw [hz_re] at hviol
  exact ⟨hrad, hlim, hdil, ⟨p, c₀, hp, hQp, hc₀, hviol⟩⟩

/-- Perturbation transfer around `Chebyshev.theta`: because `Chebyshev.theta` unconditionally
satisfies `large_prime_cofactor_centering` within `O(√n squarefreeDivisorMass n)`, adding any
perturbation `Δ` with `|Δ(x) - quartetWaveModel z m x| ≤ C x^σ (1 + log x)^r` (`(1 + σ)/2 < Re z`,
`ζ(z) ≠ 0`) forces `Chebyshev.theta + Δ` to violate reflected-composite balance at scale `Ω(n^{Re z})`
without paying the `θ(x) - x` prime-error exponent. -/
private theorem reflectedComposite_theta_perturbation_violated {Δ : ℝ → ℝ} {z : ℂ} {m C σ : ℝ}
    {r Q : ℕ} (hQ : 1 ≤ Q) (hz0 : 1 / 2 < z.re) (hz1 : z.re < 1) (hzim : z.im ≠ 0) (hm : m ≠ 0)
    (hζ_ne : riemannZeta z ≠ 0) (hC : 0 ≤ C) (hσ0 : 0 ≤ σ) (hσ_lt : (1 + σ) / 2 < z.re)
    (hΔ : ∀ x : ℝ, 1 ≤ x → |Δ x - quartetWaveModel z m x| ≤ C * x ^ σ * (1 + Real.log x) ^ r) :
    ∃ (p : ℕ) (c₀ : ℝ), p.Prime ∧ Q < p ∧ 0 < c₀ ∧
      ∀ᶠ k : ℕ in atTop,
        ∃ n ∈ ({p ^ k, p ^ (k + 1)} : Finset ℕ),
          n.Coprime Q ∧ squarefreeDivisorMass n = 2 ∧
          c₀ * (n : ℝ) ^ z.re ≤
            |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (fun x => Chebyshev.theta x + Δ x) -
                reflectedDensity * (n.totient : ℝ) -
                midpointSecondDiff n (fun x => Chebyshev.theta x + Δ x)| := by
  let G (x : ℝ) : ℝ := x + Δ x
  let F (x : ℝ) : ℝ := Chebyshev.theta x + Δ x
  have hG_mode : ∀ x : ℝ, 1 ≤ x →
      |G x - x - quartetWaveModel z m x| ≤ C * x ^ σ * (1 + Real.log x) ^ r := by
    intro x hx; dsimp [G]; rw [add_sub_cancel_left]; exact hΔ x hx
  obtain ⟨p, c₁, hp, hQp, hc₁_pos, hG_viol⟩ :=
    reflectedComposite_violated_of_mode_approx hQ hz0 hz1 hzim hm hζ_ne hC hσ0 hσ_lt hG_mode
  obtain ⟨A_pt, hA_pt⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set K_θid : ℝ := 2 * (83 + 2 * |A_pt|)
  refine ⟨p, c₁ / 2, hp, hQp, half_pos hc₁_pos, ?_⟩
  have hdiff_FG (n : ℕ) (hn2 : 2 ≤ n) (hmass2 : squarefreeDivisorMass n = 2) :
      |(clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ F - reflectedDensity * (n.totient : ℝ) -
            midpointSecondDiff n F) -
          (clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ G - reflectedDensity * (n.totient : ℝ) -
            midpointSecondDiff n G)| ≤
        K_θid * Real.sqrt n := by
    have hn1 : 1 ≤ n := by omega
    have hn1_lt : 1 < n := by omega
    have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR1
    set P := ⌊2 * Real.sqrt n⌋₊
    have hhi : (P : ℝ) ≤ 2 * Real.sqrt n := Nat.floor_le (by positivity)
    have h1_P : 1 ≤ P :=
      Nat.le_floor (by exact_mod_cast (by linarith only [hsq1] : (1 : ℝ) ≤ 2 * Real.sqrt n))
    have hP_2n : P ≤ 2 * n := by
      have hsq_n : Real.sqrt n ≤ n := by
        nlinarith only [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n), hsq1]
      exact_mod_cast (by linarith only [hhi, hsq_n] : (P : ℝ) ≤ 2 * n)
    have hF_op : clippedCofactorOp n P F = largePrimeCofactorPrice n P + clippedCofactorOp n P Δ := by
      dsimp [F]
      rw [clippedCofactorOp_add, ← largePrimeCofactorPrice_eq_clippedCofactorOp hn1 le_rfl]
    have hG_op : clippedCofactorOp n P G = clippedCofactorOp n P id + clippedCofactorOp n P Δ := by
      dsimp [G]; exact clippedCofactorOp_add n P id Δ
    have hF_mid : midpointSecondDiff n F = primeMidpointPrice n + midpointSecondDiff n Δ := by
      rw [prime_midpoint_price_eq]; unfold midpointSecondDiff; dsimp [F]; ring
    have hG_mid : midpointSecondDiff n G = midpointSecondDiff n Δ := by
      unfold midpointSecondDiff; dsimp [G]; push_cast; ring
    have hid_eq :
        (clippedCofactorOp n P F - reflectedDensity * (n.totient : ℝ) - midpointSecondDiff n F) -
          (clippedCofactorOp n P G - reflectedDensity * (n.totient : ℝ) - midpointSecondDiff n G) =
        (largePrimeCofactorPrice n P - reflectedDensity * (n.totient : ℝ) - primeMidpointPrice n) -
          (clippedCofactorOp n P id - reflectedDensity * (n.totient : ℝ)) := by
      rw [hF_op, hG_op, hF_mid, hG_mid]; ring
    rw [hid_eq]
    have hcent := large_prime_cofactor_centering hn1_lt hP_2n
    rw [hmass2] at hcent
    have hcent_cost :
        7 * (P : ℝ) + (Chebyshev.psi (4 * n : ℕ) - Chebyshev.theta (4 * n : ℕ)) + 1 ≤
          (15 + 2 * |A_pt|) * Real.sqrt n := by
      have hsq4 : Real.sqrt (4 * n : ℕ) = 2 * Real.sqrt n := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num),
          show Real.sqrt 4 = 2 by norm_num]
      have hpt : Chebyshev.psi (4 * n : ℕ) - Chebyshev.theta (4 * n : ℕ) ≤
          2 * |A_pt| * Real.sqrt n :=
        (hA_pt (4 * n : ℕ)).trans
          ((mul_le_mul_of_nonneg_right (le_abs_self A_pt) (Real.sqrt_nonneg _)).trans_eq
            (by rw [hsq4]; ring))
      linarith only [hhi, hsq1, hpt]
    have hcent' : |largePrimeCofactorPrice n P - reflectedDensity * (n.totient : ℝ) -
        primeMidpointPrice n| ≤ 2 * (15 + 2 * |A_pt|) * Real.sqrt n :=
      hcent.trans ((mul_le_mul_of_nonneg_right hcent_cost zero_le_two).trans_eq (by ring))
    have hlin := clippedCofactorSliceOp_linear hn1 h1_P hP_2n le_rfl (Nat.coprime_one_right n)
    rw [Nat.cast_one, div_one, one_mul, hmass2] at hlin
    have hlin_cost : 20 * ((P : ℝ) + 1) + 12 * (n : ℝ) / ((P : ℝ) + 1) ≤ 68 * Real.sqrt n := by
      have hlt_fl : 2 * Real.sqrt n < (P : ℝ) + 1 := Nat.lt_floor_add_one _
      have hdiv : 12 * (n : ℝ) / ((P : ℝ) + 1) ≤ 6 * Real.sqrt n := by
        rw [div_le_iff₀ (by positivity)]
        have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
        nlinarith only [hlt_fl, hsq, Real.sqrt_nonneg n]
      linarith only [hhi, hsq1, hdiv]
    have hlin' : |clippedCofactorOp n P id - reflectedDensity * (n.totient : ℝ)| ≤
        136 * Real.sqrt n :=
      hlin.trans ((mul_le_mul_of_nonneg_right hlin_cost zero_le_two).trans_eq (by ring))
    have htri := abs_sub
      (largePrimeCofactorPrice n P - reflectedDensity * (n.totient : ℝ) - primeMidpointPrice n)
      (clippedCofactorOp n P id - reflectedDensity * (n.totient : ℝ))
    dsimp [K_θid]
    linarith only [htri, hcent', hlin']
  have hgap : 0 < z.re - 1 / 2 := sub_pos.mpr hz0
  have hpow_tend : Tendsto (fun k : ℕ => ((p ^ k : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => by exact_mod_cast (Nat.lt_pow_self hp.one_lt).le)
      tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun k : ℕ => ((p ^ k : ℕ) : ℝ) ^ (z.re - 1 / 2)) atTop atTop :=
    (_root_.tendsto_rpow_atTop hgap).comp hpow_tend
  filter_upwards [eventually_ge_atTop 1, hG_viol,
    htend.eventually_ge_atTop (K_θid / (c₁ / 2))] with k hk1 hGk hbig
  obtain ⟨n, hn_mem, hncop, hmass2, hGn⟩ := hGk
  refine ⟨n, hn_mem, hncop, hmass2, ?_⟩
  have hn_ge_pk : p ^ k ≤ n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn_mem
    rcases hn_mem with rfl | rfl
    · exact le_rfl
    · exact Nat.pow_le_pow_right hp.pos (Nat.le_succ k)
  have hn2 : 2 ≤ n := (by simpa using hp.two_le : 2 ≤ p ^ 1).trans
    ((Nat.pow_le_pow_right hp.pos hk1).trans hn_ge_pk)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdiff := hdiff_FG n hn2 hmass2
  have hrpow_n : K_θid / (c₁ / 2) ≤ (n : ℝ) ^ (z.re - 1 / 2) :=
    hbig.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_ge_pk) hgap.le)
  have hK_le : K_θid * Real.sqrt n ≤ (c₁ / 2) * (n : ℝ) ^ z.re := by
    have hm1 := (div_le_iff₀ (half_pos hc₁_pos)).mp hrpow_n
    calc K_θid * Real.sqrt n
        ≤ ((n : ℝ) ^ (z.re - 1 / 2) * (c₁ / 2)) * Real.sqrt n :=
          mul_le_mul_of_nonneg_right hm1 (Real.sqrt_nonneg n)
      _ = (c₁ / 2) * ((n : ℝ) ^ (z.re - 1 / 2) * (n : ℝ) ^ (1 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow]; ring
      _ = (c₁ / 2) * (n : ℝ) ^ z.re := by
          rw [← Real.rpow_add hn0, sub_add_cancel]
  set DF := clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ F - reflectedDensity * (n.totient : ℝ) -
    midpointSecondDiff n F
  set DG := clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ G - reflectedDensity * (n.totient : ℝ) -
    midpointSecondDiff n G
  have htri : |DG| ≤ |DF - DG| + |DF| := by
    have h := abs_add_le (DG - DF) DF
    rwa [sub_add_cancel, abs_sub_comm DG DF] at h
  linarith only [htri, hGn, hdiff, hK_le]

/-- Sharp partial-summation wave approximation under an integer Chebyshev power bound
`|θ(n) - n| ≤ K_θ n^{θ₀}` (`1/2 ≤ θ₀ < 1`): because the factor `n^{β - 1}` damps `θ(n) - n` to
`n^{θ₀ + β - 1}` while `n^{β - 2}` (`β < 1`) is summable, `2 ∑_{p ≤ x} p^{β - 1} cos(γ log p) log p`
approximates `2 Re(x^{β + iγ} / (β + iγ))` within `O(x^{max (1/4) (θ₀ + β - 1)})` across `x ≥ 1`. -/
private theorem theta_power_prime_wave_approx {θ₀ β K_θ : ℝ} (_hθ_lo : 1 / 2 ≤ θ₀) (hθ_hi : θ₀ < 1)
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hK : 0 ≤ K_θ)
    (hθ : ∀ n : ℕ, 1 ≤ n → |Chebyshev.theta (n : ℝ) - (n : ℝ)| ≤ K_θ * (n : ℝ) ^ θ₀) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |2 * (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p) -
        2 * (((x : ℂ) ^ (((β : ℂ) + I * (γ : ℂ))) / (((β : ℂ) + I * (γ : ℂ)))).re)| ≤
        C * x ^ (max (1 / 4) (θ₀ + β - 1)) := by
  set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
  set μ : ℝ := max (1 / 4) (θ₀ + β - 1)
  have hβ0 : 0 < β := by linarith
  have hμ_lo : 1 / 4 ≤ μ := le_max_left _ _
  have hμ_ge : θ₀ + β - 1 ≤ μ := le_max_right _ _
  have hμ_hi : μ < 1 := max_lt (by norm_num) (by linarith)
  have hμ0 : 0 < μ := by linarith
  have hρ_re0 : 0 < ρ.re := by simp [ρ, hβ0]
  have hρ_re1 : ρ.re ≤ 1 := by simp [ρ, hβ1.le]
  have hρ_ne : ρ ≠ 0 := fun he => by rw [he, Complex.zero_re] at hρ_re0; exact lt_irrefl 0 hρ_re0
  have hρ_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
  -- Integral comparison `∑_{1 ≤ n ≤ M} n^{μ - 1} ≤ 4 * M^μ` for `1/4 ≤ μ < 1`
  have hsum_μpow (M : ℕ) (hM1 : 1 ≤ M) :
      ∑ n ∈ Icc 1 M, (n : ℝ) ^ (μ - 1) ≤ 4 * (M : ℝ) ^ μ := by
    induction M, hM1 using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have hkR1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hkR1
      have hsplit : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by rw [mem_Icc]; omega)]
      have hstep : ((k + 1 : ℕ) : ℝ) ^ (μ - 1) ≤
          (((k + 1 : ℕ) : ℝ) ^ μ - (k : ℝ) ^ μ) / μ := by
        have h0_not : (0 : ℝ) ∉ Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ) := by
          rw [Set.uIcc_of_le (by exact_mod_cast Nat.le_succ k)]; intro h; linarith [h.1]
        have hint := integral_rpow (a := (k : ℝ)) (b := ((k + 1 : ℕ) : ℝ)) (r := μ - 1)
          (Or.inr ⟨by linarith, h0_not⟩)
        rw [sub_add_cancel] at hint
        rw [← hint]
        have hconst : ((k + 1 : ℕ) : ℝ) ^ (μ - 1) =
            ∫ _t in (k : ℝ)..((k + 1 : ℕ) : ℝ), ((k + 1 : ℕ) : ℝ) ^ (μ - 1) := by
          rw [intervalIntegral.integral_const,
            show ((k + 1 : ℕ) : ℝ) - (k : ℝ) = 1 by push_cast; ring, one_smul]
        rw [hconst]
        refine intervalIntegral.integral_mono_on (by exact_mod_cast Nat.le_succ k)
          intervalIntegrable_const (intervalIntegral.intervalIntegrable_rpow' (by linarith)) ?_
        intro t ht
        exact Real.rpow_le_rpow_of_nonpos (hk0.trans_le ht.1) ht.2 (by linarith)
      have hstep4 : (((k + 1 : ℕ) : ℝ) ^ μ - (k : ℝ) ^ μ) / μ ≤
          4 * (((k + 1 : ℕ) : ℝ) ^ μ - (k : ℝ) ^ μ) := by
        have hdiff_nn : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ μ - (k : ℝ) ^ μ :=
          sub_nonneg.mpr (Real.rpow_le_rpow hk0.le (by exact_mod_cast Nat.le_succ k) hμ0.le)
        rw [div_eq_mul_inv]
        have hinv4 : μ⁻¹ ≤ 4 := by
          rw [inv_le_comm₀ hμ0 (by norm_num)]; norm_num at hμ_lo ⊢; exact hμ_lo
        exact (mul_le_mul_of_nonneg_left hinv4 hdiff_nn).trans_eq (mul_comm _ _)
      linarith only [ih, hstep, hstep4]
  have hmvt_g {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁₂ : x₁ ≤ x₂) :
      ‖(x₂ : ℂ) ^ (ρ - 1) - (x₁ : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ - 1‖ * (x₂ - x₁) * x₁ ^ (β - 2) := by
    have h0 : (0 : ℝ) ∉ Set.uIcc x₁ x₂ := by
      rw [Set.uIcc_of_le hx₁₂]; intro h; linarith [h.1]
    have hne_neg1 : ρ - 2 ≠ -1 := fun he => by
      have := congrArg Complex.re he; simp [ρ] at this; linarith
    have hint := integral_cpow (a := x₁) (b := x₂) (r := ρ - 2) (Or.inr ⟨hne_neg1, h0⟩)
    rw [show ρ - 2 + 1 = ρ - 1 by ring] at hint
    have hρ1_ne : ρ - 1 ≠ 0 := fun he => hne_neg1 (by linear_combination he)
    have heq : (x₂ : ℂ) ^ (ρ - 1) - (x₁ : ℂ) ^ (ρ - 1) =
        (ρ - 1) * ∫ s in x₁..x₂, (s : ℂ) ^ (ρ - 2) := by
      rw [hint]; field_simp [hρ1_ne]
    rw [heq, norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hbound : ∀ s ∈ Set.uIoc x₁ x₂, ‖(s : ℂ) ^ (ρ - 2)‖ ≤ x₁ ^ (β - 2) := by
      intro s hs
      rw [Set.uIoc_of_le hx₁₂] at hs
      have hs0 : 0 < s := hx₁.trans hs.1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hs0, show (ρ - 2).re = β - 2 by simp [ρ]]
      exact Real.rpow_le_rpow_of_nonpos hx₁ hs.1.le (by linarith)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [abs_of_nonneg (sub_nonneg.mpr hx₁₂)] at h
    linarith
  set C_tot : ℝ := 2 * (K_θ + 4 * K_θ * ‖ρ - 1‖ + 4 * ‖ρ - 1‖ + 1 / ‖ρ‖ + 1)
  refine ⟨C_tot, by dsimp [C_tot]; positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxμ1 : 1 ≤ x ^ μ := Real.one_le_rpow hx hμ0.le
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hNR1
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  let g (n : ℕ) : ℝ := ((n : ℂ) ^ (ρ - 1)).re
  let δ (n : ℕ) : ℝ := Chebyshev.theta (n : ℝ) - (n : ℝ)
  have hδ0 : δ 0 = 0 := by simp [δ, Chebyshev.theta]
  have hg_prime (n : ℕ) (hn : 1 ≤ n) :
      g n = (n : ℝ) ^ (β - 1) * Real.cos (γ * Real.log n) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [g]
    have hcp : (n : ℂ) ^ (ρ - 1) =
        (((n : ℝ) ^ (β - 1) : ℝ) : ℂ) * Complex.exp (((γ * Real.log n : ℝ) : ℂ) * I) := by
      have hnC : ((n : ℝ) : ℂ) = (n : ℂ) := Complex.ofReal_natCast n
      rw [← hnC, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn0.ne'),
        ← Complex.ofReal_log hn0.le, Real.rpow_def_of_pos hn0, Complex.ofReal_exp,
        ← Complex.exp_add]
      congr 1; dsimp [ρ]; push_cast; ring
    rw [hcp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hjump (n : ℕ) (hn : 1 ≤ n) :
      (if n.Prime then Real.log n else 0) = δ n - δ (n - 1) + 1 := by
    let fn (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
    have hp_sum (m : ℕ) : Chebyshev.theta (m : ℝ) = ∑ k ∈ Icc 1 m, fn k := by
      rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_Icc_one, Finset.sum_filter]
    have hsplit : Icc 1 n = Icc 1 (n - 1) ∪ {n} := by
      ext k; simp only [mem_Icc, mem_union, mem_singleton]; omega
    have hdisj : Disjoint (Icc 1 (n - 1)) {n} := by
      rw [Finset.disjoint_singleton_right, mem_Icc]; omega
    dsimp [δ]
    rw [hp_sum n, hp_sum (n - 1), hsplit, Finset.sum_union hdisj, Finset.sum_singleton,
      Nat.cast_sub hn, Nat.cast_one]
    dsimp [fn]; ring
  have hprime_split : (∑ p ∈ (Finset.Iic N).filter Nat.Prime,
      (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p) =
      (∑ n ∈ Icc 1 N, (δ n - δ (n - 1)) * g n) + ∑ n ∈ Icc 1 N, g n := by
    rw [Finset.sum_filter]
    have hset : Finset.Iic N = insert 0 (Icc 1 N) := by
      ext n; simp only [mem_Iic, mem_insert, mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp), if_neg Nat.not_prime_zero, zero_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hj := hjump n hn1
    rw [← hg_prime n hn1]
    by_cases hnp : n.Prime
    · rw [if_pos hnp] at hj ⊢; linarith [congrArg (· * g n) hj]
    · rw [if_neg hnp] at hj ⊢; linarith [congrArg (· * g n) hj]
  have habel_id (M : ℕ) (hM : 1 ≤ M) :
      ∑ n ∈ Icc 1 M, (δ n - δ (n - 1)) * g n =
        δ M * g M - ∑ n ∈ Icc 1 (M - 1), δ n * (g (n + 1) - g n) := by
    induction M, hM using Nat.le_induction with
    | base => simp [hδ0]
    | succ M hM ih =>
      have h1 : Icc 1 (M + 1) = insert (M + 1) (Icc 1 M) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      have h2 : Icc 1 M = insert M (Icc 1 (M - 1)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [h1, Finset.sum_insert (by rw [mem_Icc]; omega), ih, Nat.add_sub_cancel, h2,
        Finset.sum_insert (by rw [mem_Icc]; omega)]
      ring
  have habel_bound : |∑ n ∈ Icc 1 N, (δ n - δ (n - 1)) * g n| ≤
      (K_θ + 4 * K_θ * ‖ρ - 1‖) * x ^ μ := by
    rw [habel_id N hN1]
    have hbdry : |δ N * g N| ≤ K_θ * x ^ μ := by
      rw [abs_mul]
      have hgN : |g N| ≤ (N : ℝ) ^ (β - 1) := by
        rw [hg_prime N hN1, abs_mul, abs_of_nonneg (Real.rpow_nonneg hN0.le _)]
        exact mul_le_of_le_one_right (Real.rpow_nonneg hN0.le _) (Real.abs_cos_le_one _)
      calc |δ N| * |g N| ≤ (K_θ * (N : ℝ) ^ θ₀) * (N : ℝ) ^ (β - 1) :=
            mul_le_mul (hθ N hN1) hgN (abs_nonneg _) (by positivity)
        _ = K_θ * ((N : ℝ) ^ θ₀ * (N : ℝ) ^ (β - 1)) := by ring
        _ = K_θ * (N : ℝ) ^ (θ₀ + β - 1) := by rw [← Real.rpow_add hN0, add_sub_assoc]
        _ ≤ K_θ * (N : ℝ) ^ μ :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hNR1 hμ_ge) hK
        _ ≤ K_θ * x ^ μ :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0.le hNx hμ0.le) hK
    have hsum_diff : |∑ n ∈ Icc 1 (N - 1), δ n * (g (n + 1) - g n)| ≤
        4 * K_θ * ‖ρ - 1‖ * x ^ μ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ n ∈ Icc 1 (N - 1),
          |δ n * (g (n + 1) - g n)| ≤ K_θ * ‖ρ - 1‖ * (n : ℝ) ^ (μ - 1) := by
        intro n hn
        have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hg_diff : |g (n + 1) - g n| ≤ ‖ρ - 1‖ * (n : ℝ) ^ (β - 2) := by
          dsimp [g]
          rw [← Complex.sub_re]
          refine (Complex.abs_re_le_norm _).trans ?_
          have hm := hmvt_g hn0 (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ (n + 1 : ℕ))
          simpa [show ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 by push_cast; ring] using hm
        have hrpow_comb : (n : ℝ) ^ θ₀ * (n : ℝ) ^ (β - 2) ≤ (n : ℝ) ^ (μ - 1) := by
          rw [← Real.rpow_add hn0]
          exact Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)
        rw [abs_mul]
        calc |δ n| * |g (n + 1) - g n|
            ≤ (K_θ * (n : ℝ) ^ θ₀) * (‖ρ - 1‖ * (n : ℝ) ^ (β - 2)) :=
              mul_le_mul (hθ n hn1) hg_diff (abs_nonneg _) (by positivity)
          _ = K_θ * ‖ρ - 1‖ * ((n : ℝ) ^ θ₀ * (n : ℝ) ^ (β - 2)) := by ring
          _ ≤ K_θ * ‖ρ - 1‖ * (n : ℝ) ^ (μ - 1) :=
              mul_le_mul_of_nonneg_left hrpow_comb (by positivity)
      calc ∑ n ∈ Icc 1 (N - 1), |δ n * (g (n + 1) - g n)|
          ≤ ∑ n ∈ Icc 1 (N - 1), K_θ * ‖ρ - 1‖ * (n : ℝ) ^ (μ - 1) := Finset.sum_le_sum hterm
        _ ≤ ∑ n ∈ Icc 1 N, K_θ * ‖ρ - 1‖ * (n : ℝ) ^ (μ - 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right (Nat.sub_le N 1)) (fun _ _ _ => by positivity)
        _ = K_θ * ‖ρ - 1‖ * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (μ - 1) := by rw [← Finset.mul_sum]
        _ ≤ K_θ * ‖ρ - 1‖ * (4 * (N : ℝ) ^ μ) :=
            mul_le_mul_of_nonneg_left (hsum_μpow N hN1) (by positivity)
        _ ≤ K_θ * ‖ρ - 1‖ * (4 * x ^ μ) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0.le hNx hμ0.le) (by norm_num))
              (by positivity)
        _ = 4 * K_θ * ‖ρ - 1‖ * x ^ μ := by ring
    exact (abs_sub _ _).trans ((add_le_add hbdry hsum_diff).trans_eq (by ring))
  have hmain_bound : |(∑ n ∈ Icc 1 N, g n) - ((x : ℂ) ^ ρ / ρ).re| ≤
      (4 * ‖ρ - 1‖ + 1 / ‖ρ‖ + 1) * x ^ μ := by
    have hstep_int : ∀ n ∈ Icc 1 N,
        |g n - ((((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ).re)| ≤
          ‖ρ - 1‖ * (n : ℝ) ^ (μ - 1) := by
      intro n hn
      have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have h0_mem : (0 : ℝ) ∉ Set.uIcc (n : ℝ) (n + 1 : ℝ) := by
        rw [Set.uIcc_of_le (by linarith)]; intro hm; linarith [hm.1]
      have hint_n := integral_cpow (a := (n : ℝ)) (b := ((n + 1 : ℕ) : ℝ)) (r := ρ - 1)
        (Or.inl (by simp [ρ]; linarith))
      rw [sub_add_cancel] at hint_n
      have hint_const : ∫ _u in (n : ℝ)..((n + 1 : ℕ) : ℝ), (n : ℂ) ^ (ρ - 1) =
          (n : ℂ) ^ (ρ - 1) := by
        rw [intervalIntegral.integral_const,
          show ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 by push_cast; ring, one_smul]
      have hdiff_int : (n : ℂ) ^ (ρ - 1) - (((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ) =
          ∫ u in (n : ℝ)..((n + 1 : ℕ) : ℝ), ((n : ℂ) ^ (ρ - 1) - (u : ℂ) ^ (ρ - 1)) := by
        have hi1 : IntervalIntegrable (fun _u : ℝ => (n : ℂ) ^ (ρ - 1)) volume
            (n : ℝ) ((n + 1 : ℕ) : ℝ) := intervalIntegrable_const
        have hi2 : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (ρ - 1)) volume
            (n : ℝ) ((n + 1 : ℕ) : ℝ) :=
          intervalIntegral.intervalIntegrable_cpow (Or.inr (by push_cast; exact h0_mem))
        rw [intervalIntegral.integral_sub hi1 hi2, hint_const, hint_n, sub_div]
        push_cast; rfl
      have hre_le := Complex.abs_re_le_norm ((n : ℂ) ^ (ρ - 1) -
        (((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ))
      rw [Complex.sub_re] at hre_le
      refine hre_le.trans ?_
      rw [hdiff_int]
      have hpt_u : ∀ u ∈ Set.uIoc (n : ℝ) ((n + 1 : ℕ) : ℝ),
          ‖(n : ℂ) ^ (ρ - 1) - (u : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ - 1‖ * (n : ℝ) ^ (β - 2) := by
        intro u hu
        rw [Set.uIoc_of_le (by exact_mod_cast Nat.le_succ n)] at hu
        rw [norm_sub_rev]
        have hm := hmvt_g hn0 hu.1.le
        have hudiff : u - (n : ℝ) ≤ 1 := by
          have : u ≤ (n : ℝ) + 1 := by simpa using hu.2
          linarith
        exact hm.trans (mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right (norm_nonneg _) hudiff) (Real.rpow_nonneg hn0.le _))
      have hni := intervalIntegral.norm_integral_le_of_norm_le_const hpt_u
      rw [show |((n + 1 : ℕ) : ℝ) - (n : ℝ)| = 1 by
        rw [show ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 by push_cast; ring, abs_one], mul_one] at hni
      exact hni.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)) (norm_nonneg _))
    have htel : ∑ n ∈ Icc 1 N, ((((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ).re) =
        ((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((1 : ℂ) ^ ρ / ρ).re) := by
      have hIoc : Icc 1 N = Ioc 0 N := by ext k; simp only [mem_Icc, mem_Ioc]; omega
      rw [hIoc]
      have key : ∀ M : ℕ, ∑ n ∈ Ioc 0 M, ((((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ).re) =
          ((((M + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((1 : ℂ) ^ ρ / ρ).re) := by
        intro M
        induction M with
        | zero => simp
        | succ M ih =>
          rw [Finset.sum_Ioc_succ_top (Nat.zero_le M), ih, Complex.sub_re]; ring
      exact key N
    have hsum_err : |(∑ n ∈ Icc 1 N, g n) -
        (((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((1 : ℂ) ^ ρ / ρ).re))| ≤
        4 * ‖ρ - 1‖ * x ^ μ := by
      rw [← htel, ← Finset.sum_sub_distrib]
      calc |∑ n ∈ Icc 1 N, (g n - ((((n + 1 : ℕ) : ℂ) ^ ρ / ρ - (n : ℂ) ^ ρ / ρ).re))|
          ≤ ∑ n ∈ Icc 1 N, ‖ρ - 1‖ * (n : ℝ) ^ (μ - 1) :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hstep_int)
        _ = ‖ρ - 1‖ * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (μ - 1) := by rw [← Finset.mul_sum]
        _ ≤ ‖ρ - 1‖ * (4 * (N : ℝ) ^ μ) :=
            mul_le_mul_of_nonneg_left (hsum_μpow N hN1) (norm_nonneg _)
        _ ≤ ‖ρ - 1‖ * (4 * x ^ μ) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0.le hNx hμ0.le) (by norm_num))
              (norm_nonneg _)
        _ = 4 * ‖ρ - 1‖ * x ^ μ := by ring
    have hend1 : |(((1 : ℂ) ^ ρ / ρ).re)| ≤ 1 / ‖ρ‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      simp only [Complex.one_cpow, norm_div, norm_one, le_refl]
    have hendN : |((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((x : ℂ) ^ ρ / ρ).re)| ≤ 1 := by
      rw [← Complex.sub_re]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [← sub_div, norm_div, div_le_iff₀ hρ_pos]
      have hxN1 : x ≤ ((N + 1 : ℕ) : ℝ) := (Nat.lt_floor_add_one x).le.trans_eq (by push_cast; rfl)
      have hm := RHTower.norm_ofReal_cpow_sub_cpow_le hx0 hxN1 hρ_re0 hρ_re1
      rw [show ((N + 1 : ℕ) : ℂ) = (((N + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl]
      have hdiff_le1 : ((N + 1 : ℕ) : ℝ) - x ≤ 1 := by push_cast; linarith [hNx]
      have hrpow_le1 : x ^ (ρ.re - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx (by simp [ρ]; linarith)
      calc ‖(((N + 1 : ℕ) : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ‖
          ≤ ‖ρ‖ * (((N + 1 : ℕ) : ℝ) - x) * x ^ (ρ.re - 1) := hm
        _ ≤ ‖ρ‖ * 1 * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hdiff_le1 hρ_pos.le) hrpow_le1
              (Real.rpow_nonneg hx0.le _) (by positivity)
        _ = 1 * ‖ρ‖ := by ring
    have hcomb : |(∑ n ∈ Icc 1 N, g n) - (((x : ℂ) ^ ρ / ρ).re)| ≤
        4 * ‖ρ - 1‖ * x ^ μ + 1 / ‖ρ‖ + 1 := by
      have hsplit : (∑ n ∈ Icc 1 N, g n) - (((x : ℂ) ^ ρ / ρ).re) =
          ((∑ n ∈ Icc 1 N, g n) -
            (((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re) - (((1 : ℂ) ^ ρ / ρ).re))) +
            ((((N + 1 : ℕ) : ℂ) ^ ρ / ρ).re - (((x : ℂ) ^ ρ / ρ).re)) -
            (((1 : ℂ) ^ ρ / ρ).re) := by ring
      rw [hsplit]
      exact ((abs_sub _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add hsum_err hendN)) hend1)).trans_eq (by ring)
    have h2 : 1 / ‖ρ‖ + 1 ≤ (1 / ‖ρ‖ + 1) * x ^ μ :=
      le_mul_of_one_le_right (by positivity) hxμ1
    linarith only [hcomb, h2]
  rw [hprime_split, show 2 * ((∑ n ∈ Icc 1 N, (δ n - δ (n - 1)) * g n) + ∑ n ∈ Icc 1 N, g n) -
      2 * (((x : ℂ) ^ ρ / ρ).re) =
    2 * (∑ n ∈ Icc 1 N, (δ n - δ (n - 1)) * g n) +
      2 * ((∑ n ∈ Icc 1 N, g n) - (((x : ℂ) ^ ρ / ρ).re)) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos two_pos]
  dsimp [C_tot]
  linarith only [habel_bound, hmain_bound]

/-- **Sharp unconditional reflected-composite rejection of `{0, 1, 2}`-prime `sEdit` above `max(2/3, Θ)`.**
Whenever `max (2 / 3) zetaZeroAbscissa < β < 1` and `γ ≠ 0`, `riemannZeta (β + iγ) ≠ 0` holds
unconditionally and for every `α ∈ (β, min 1 (4β - 2))` (in particular `α = (β + min 1 (4β - 2)) / 2`),
the `{0, 1, 2}`-rational-prime edit `e = sEdit α β γ k₀` violates the ordinary-integer
reflected-composite identity at scale `Ω(n^β)` along infinitely many prime powers coprime to `Q`. -/
theorem unconditional_sEdit_rejected_above_max_two_thirds_zetaZeroAbscissa {α β γ : ℝ} {Q : ℕ}
    (hQ : 1 ≤ Q) (k₀ : ℕ) (hβ_lo : max (2 / 3) RHTower.zetaZeroAbscissa < β) (hβα : β < α)
    (hα_hi : α < min 1 (4 * β - 2)) (hγ : γ ≠ 0) :
    let e := sEdit α β γ k₀
    riemannZeta ((β : ℂ) + I * (γ : ℂ)) ≠ 0 ∧
      IsEdit e ∧
      ∃ (p : ℕ) (c₀ : ℝ), p.Prime ∧ Q < p ∧ 0 < c₀ ∧
        ∀ᶠ k : ℕ in atTop,
          ∃ n ∈ ({p ^ k, p ^ (k + 1)} : Finset ℕ),
            n.Coprime Q ∧ squarefreeDivisorMass n = 2 ∧
            c₀ * (n : ℝ) ^ β ≤
              |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (editedTheta e) -
                  reflectedDensity * (n.totient : ℝ) -
                  midpointSecondDiff n (editedTheta e)| := by
  intro e
  have hΘ_half : 1 / 2 ≤ RHTower.zetaZeroAbscissa := RHTower.half_le_zetaZeroAbscissa
  have hβ_23 : 2 / 3 < β := (le_max_left _ _).trans_lt hβ_lo
  have hΘ_lt_β : RHTower.zetaZeroAbscissa < β := (le_max_right _ _).trans_lt hβ_lo
  have hα1 : α < 1 := hα_hi.trans_le (min_le_left _ _)
  have hα_4β : α < 4 * β - 2 := hα_hi.trans_le (min_le_right _ _)
  have hβ1 : β < 1 := hβα.trans hα1
  have hβ_half : 1 / 2 < β := by linarith
  set z : ℂ := (β : ℂ) + I * (γ : ℂ)
  have hz_re : z.re = β := by simp [z]
  have hz_im : z.im = γ := by simp [z]
  have hζ_ne : riemannZeta z ≠ 0 :=
    RHTower.riemannZeta_ne_zero_of_zetaZeroAbscissa_lt (by rw [hz_re]; exact hΘ_lt_β)
  -- Pick `θ₀ = (Θ + β) / 2 ∈ (Θ, β)` so `(1 + (θ₀ + β - 1)) / 2 = (θ₀ + β) / 2 < β`
  set ε : ℝ := (β - RHTower.zetaZeroAbscissa) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  set θ₀ : ℝ := RHTower.zetaZeroAbscissa + ε
  have hθ_lo : 1 / 2 < θ₀ := by dsimp [θ₀]; linarith
  have hθ_lt_β : θ₀ < β := by dsimp [θ₀, ε]; linarith
  have hθ_hi : θ₀ < 1 := hθ_lt_β.trans hβ1
  obtain ⟨C_ψ, hC_ψ, hψ_rem⟩ := RHTower.exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  set K_θ : ℝ := C_ψ + 3 * (Real.log 4 + 4)
  have hK_θ : 0 ≤ K_θ := by dsimp [K_θ]; positivity
  have hθ_nat : ∀ n : ℕ, 1 ≤ n → |Chebyshev.theta (n : ℝ) - (n : ℝ)| ≤ K_θ * (n : ℝ) ^ θ₀ := by
    intro n hn
    have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hψn : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤ C_ψ * (n : ℝ) ^ θ₀ := by
      have hb := hψ_rem n hn
      rwa [RHTower.psiRemainder, RHTower.chebyshevPsi_eq_psi] at hb
    have hpt : |Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)| ≤
        3 * (Real.log 4 + 4) * (n : ℝ) ^ θ₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
      have h1 := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt (n : ℝ)
      have hsq_le : Real.sqrt n ≤ (n : ℝ) ^ θ₀ := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hnR1 hθ_lo.le
      exact h1.trans (mul_le_mul_of_nonneg_left hsq_le (by positivity))
    have htri := abs_sub (Chebyshev.psi (n : ℝ) - (n : ℝ))
      (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))
    rw [show (Chebyshev.psi (n : ℝ) - (n : ℝ)) -
        (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) =
        Chebyshev.theta (n : ℝ) - (n : ℝ) by ring] at htri
    dsimp [K_θ]
    linarith only [htri, hψn, hpt]
  obtain ⟨C₁, hC₁, hedit⟩ := sEdit_primeLog_wave_approx (by linarith) hβα hα1 γ k₀
  obtain ⟨C₂, hC₂, hwave⟩ :=
    theta_power_prime_wave_approx hθ_lo.le hθ_hi hβ_half hβ1 hK_θ hθ_nat γ
  set μ : ℝ := max (1 / 4) (θ₀ + β - 1)
  set σ : ℝ := max (α / 2) μ
  have hσ0 : 0 ≤ σ := le_trans (by linarith) (le_max_left (α / 2) μ)
  have hσ_lt : (1 + σ) / 2 < β := by
    have hμ_lt : (1 + μ) / 2 < β := by
      dsimp [μ]
      rcases max_choice (1 / 4) (θ₀ + β - 1) with h | h <;> rw [h] <;> linarith
    dsimp [σ]
    rcases max_choice (α / 2) μ with h | h <;> rw [h] <;> linarith
  let Δ_e (x : ℝ) : ℝ := ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (e p : ℝ) * Real.log p
  have hΔ_bound : ∀ x : ℝ, 1 ≤ x →
      |Δ_e x - quartetWaveModel z 1 x| ≤ (C₁ + C₂) * x ^ σ * (1 + Real.log x) ^ 2 := by
    intro x hx
    have h1_sq : 1 ≤ (1 + Real.log x) ^ 2 := by nlinarith [Real.log_nonneg hx]
    have hedit' : |∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        ((e p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) * Real.log p| ≤
        C₁ * x ^ σ * (1 + Real.log x) ^ 2 := by
      refine (hedit x hx).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)) hC₁)
        (sq_nonneg _)
    have hwave' : |2 * (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p) -
        2 * ((x : ℂ) ^ z / z).re| ≤ C₂ * x ^ σ * (1 + Real.log x) ^ 2 := by
      refine (hwave x hx).trans ?_
      have hrp : x ^ μ ≤ x ^ σ := Real.rpow_le_rpow_of_exponent_le hx (le_max_right _ _)
      exact (mul_le_mul_of_nonneg_left hrp hC₂).trans (le_mul_of_one_le_right (by positivity) h1_sq)
    have hsum_id : Δ_e x - quartetWaveModel z 1 x =
        (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          ((e p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) * Real.log p) -
        (2 * (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
            (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p) -
          2 * ((x : ℂ) ^ z / z).re) := by
      dsimp [Δ_e]; unfold quartetWaveModel
      have hlin : (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          ((e p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) * Real.log p) =
          (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (e p : ℝ) * Real.log p) +
            2 * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
              (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hlin]; ring
    rw [hsum_id]
    exact (abs_sub _ _).trans ((add_le_add hedit' hwave').trans_eq (by ring))
  obtain ⟨p, c₀, hp, hQp, hc₀, hviol⟩ := reflectedComposite_theta_perturbation_violated hQ
    (hz_re.symm ▸ hβ_half) (hz_re.symm ▸ hβ1) (hz_im.symm ▸ hγ) one_ne_zero hζ_ne
    (add_nonneg hC₁ hC₂) hσ0 (hz_re.symm ▸ hσ_lt) hΔ_bound
  rw [hz_re] at hviol
  exact ⟨hζ_ne, isEdit_sEdit _ _ _ _, ⟨p, c₀, hp, hQp, hc₀, hviol⟩⟩

/-- **Concrete unconditional reflected-composite rejection of `sEdit` across `20999 / 24000 < β < 1`
(including all `7 / 8 ≤ β < 1`).** -/
theorem unconditional_sEdit_rejected_on_zeroFreeStrip {β γ : ℝ} {Q : ℕ} (hQ : 1 ≤ Q)
    (hβ : 20999 / 24000 < β) (hβ1 : β < 1) (hγ : γ ≠ 0) :
    let α := (β + min 1 (4 * β - 2)) / 2
    let e := sEdit α β γ 0
    riemannZeta ((β : ℂ) + I * (γ : ℂ)) ≠ 0 ∧
      IsEdit e ∧
      ∃ (p : ℕ) (c₀ : ℝ), p.Prime ∧ Q < p ∧ 0 < c₀ ∧
        ∀ᶠ k : ℕ in atTop,
          ∃ n ∈ ({p ^ k, p ^ (k + 1)} : Finset ℕ),
            n.Coprime Q ∧ squarefreeDivisorMass n = 2 ∧
            c₀ * (n : ℝ) ^ β ≤
              |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (editedTheta e) -
                  reflectedDensity * (n.totient : ℝ) -
                  midpointSecondDiff n (editedTheta e)| := by
  have hΘ := ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths
  have hmin : β < min 1 (4 * β - 2) := lt_min hβ1 (by linarith)
  exact unconditional_sEdit_rejected_above_max_two_thirds_zetaZeroAbscissa hQ 0
    (max_lt (by linarith) (hΘ.trans_lt hβ)) (by linarith) (by linarith) hγ

/-- **Sharp simultaneous prime-radius imitation and reflected-composite violation across `2/3 < β < 1`
under `RiemannHypothesis`.**
Above the `2/3` sub-square-root Beurling threshold (`2/3 < β < 1`), the `{0, 1, 2}`-rational-prime
edit `e = sEdit ((β + min 1 (4β - 2)) / 2) β γ 0` simultaneously imitates the unit-multiplicity
two-interval prime radius (`¬ IsLogSqrtSqUnbounded`) and violates the ordinary-integer
reflected-composite identity at scale `Ω(n^β)` along infinitely many prime powers coprime to `Q`. -/
theorem rh_sEdit_imitates_radius_but_violates_reflectedComposites (hRH : RiemannHypothesis)
    {β γ : ℝ} {Q : ℕ} (hQ : 1 ≤ Q) (hβ : 2 / 3 < β) (hβ1 : β < 1) (hγ : γ ≠ 0) :
    let α := (β + min 1 (4 * β - 2)) / 2
    let e := sEdit α β γ 0
    IsEdit e ∧
      ¬ IsLogSqrtSqUnbounded
          (radialDiscrepancyOf (fun t => editedTheta e (Real.exp t) - Real.exp t) β γ 1) ∧
      ∃ (p : ℕ) (c₀ : ℝ), p.Prime ∧ Q < p ∧ 0 < c₀ ∧
        ∀ᶠ k : ℕ in atTop,
          ∃ n ∈ ({p ^ k, p ^ (k + 1)} : Finset ℕ),
            n.Coprime Q ∧ squarefreeDivisorMass n = 2 ∧
            c₀ * (n : ℝ) ^ β ≤
              |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (editedTheta e) -
                  reflectedDensity * (n.totient : ℝ) -
                  midpointSecondDiff n (editedTheta e)| := by
  set α : ℝ := (β + min 1 (4 * β - 2)) / 2
  set e := sEdit α β γ 0
  have hmin : β < min 1 (4 * β - 2) := lt_min hβ1 (by linarith)
  have hβα : β < α := by dsimp [α]; linarith
  have hα_hi : α < min 1 (4 * β - 2) := by dsimp [α]; linarith
  have hα1 : α < 1 := hα_hi.trans_le (min_le_left _ _)
  have hΘ : RHTower.zetaZeroAbscissa = 1 / 2 :=
    RHTower.zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH
  obtain ⟨_, he, hviol⟩ := unconditional_sEdit_rejected_above_max_two_thirds_zetaZeroAbscissa
    (α := α) hQ 0 (by rw [hΘ]; exact max_lt hβ (by linarith)) hβα hα_hi hγ
  -- Prove `¬ IsLogSqrtSqUnbounded` for `editedTheta e` at `(β, γ, 1)` under `hRH`
  have hrad : ¬ IsLogSqrtSqUnbounded
      (radialDiscrepancyOf (fun t => editedTheta e (Real.exp t) - Real.exp t) β γ 1) := by
    obtain ⟨C₁, hC₁, hedit⟩ := sEdit_primeLog_wave_approx (by linarith) hβα hα1 γ 0
    -- Integer `θ` bound at exponent `3 / 5` (since `β - 2 / 5 < 1 / 2`? No: we need `O(√x log² x)`!)
    -- Bound `|Chebyshev.theta y - y| ≤ K_rh √y (1 + log y)²` for `y ≥ 1` under `hRH`
    set M₁₆ : ℝ := Chebyshev.psi 16 + 16
    have hM₁₆_nn : 0 ≤ M₁₆ := by have := Chebyshev.psi_nonneg 16; dsimp [M₁₆]; linarith
    set K_rh : ℝ := |200 * (RHTower.xiLineTwoLogDerivConstant + 2)| + M₁₆ + 3 * (Real.log 4 + 4)
    have hK_rh : 0 ≤ K_rh := by dsimp [K_rh]; positivity
    have hθ_rh : ∀ y : ℝ, 1 ≤ y →
        |Chebyshev.theta y - y| ≤ K_rh * Real.sqrt y * (1 + Real.log y) ^ 2 := by
      intro y hy
      have h1_sq : 1 ≤ (1 + Real.log y) ^ 2 := by nlinarith [Real.log_nonneg hy]
      have hsqrt1 : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy
      have hpt : |Chebyshev.psi y - Chebyshev.theta y| ≤
          3 * (Real.log 4 + 4) * Real.sqrt y * (1 + Real.log y) ^ 2 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
        exact (GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt y).trans
          (le_mul_of_one_le_right (by positivity) h1_sq)
      have hpsi : |Chebyshev.psi y - y| ≤
          (|200 * (RHTower.xiLineTwoLogDerivConstant + 2)| + M₁₆) *
            Real.sqrt y * (1 + Real.log y) ^ 2 := by
        by_cases hy16 : 16 ≤ y
        · have h1 := (RHTower.abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH hy16).trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)) (sq_nonneg _))
          have hsq : Real.log y ^ 2 ≤ (1 + Real.log y) ^ 2 := by nlinarith [Real.log_nonneg hy]
          exact h1.trans ((mul_le_mul_of_nonneg_left hsq (by positivity)).trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith [hM₁₆_nn]) (Real.sqrt_nonneg y))
              (sq_nonneg _)))
        · have hy_lt : y ≤ 16 := (not_le.mp hy16).le
          have h5 : |Chebyshev.psi y - y| ≤ M₁₆ := by
            have hnn := Chebyshev.psi_nonneg y
            have hmo := Chebyshev.psi_mono hy_lt
            dsimp [M₁₆]; rw [abs_le]; constructor <;> linarith only [hnn, hmo, hy, hy_lt]
          have hprod : 1 ≤ Real.sqrt y * (1 + Real.log y) ^ 2 :=
            one_le_mul_of_one_le_of_one_le hsqrt1 h1_sq
          calc |Chebyshev.psi y - y| ≤ M₁₆ := h5
            _ ≤ (|200 * (RHTower.xiLineTwoLogDerivConstant + 2)| + M₁₆) *
                  (Real.sqrt y * (1 + Real.log y) ^ 2) :=
                (by linarith [abs_nonneg (200 * (RHTower.xiLineTwoLogDerivConstant + 2))] :
                  M₁₆ ≤ |200 * (RHTower.xiLineTwoLogDerivConstant + 2)| + M₁₆).trans
                  (le_mul_of_one_le_right (by positivity) hprod)
            _ = _ := by ring
      have htri := abs_sub (Chebyshev.psi y - y) (Chebyshev.psi y - Chebyshev.theta y)
      rw [show (Chebyshev.psi y - y) - (Chebyshev.psi y - Chebyshev.theta y) =
        Chebyshev.theta y - y by ring] at htri
      dsimp [K_rh]; linarith only [htri, hpsi, hpt]
    -- Use `exists_psiRemainder_le_rpow_zetaZeroAbscissa` at `θ₀ = (3 - 2β)/2`? Even simpler:
    -- `θ₀ = 1/2 + (1 - β)/2 = 1 - β/2 ∈ (1/2, 2/3)`: then `θ₀ + β - 1 = β/2 < 1/2`!!
    set ε_rh : ℝ := (1 - β) / 2
    have hε_rh : 0 < ε_rh := by dsimp [ε_rh]; linarith
    obtain ⟨C_ψ, hC_ψ, hψ_rh⟩ := RHTower.exists_psiRemainder_le_rpow_zetaZeroAbscissa ε_rh hε_rh
    rw [hΘ] at hψ_rh
    set θ_rh : ℝ := 1 / 2 + ε_rh
    have hθ_nat_rh : ∀ n : ℕ, 1 ≤ n →
        |Chebyshev.theta (n : ℝ) - (n : ℝ)| ≤ (C_ψ + 3 * (Real.log 4 + 4)) * (n : ℝ) ^ θ_rh := by
      intro n hn
      have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hψn : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤ C_ψ * (n : ℝ) ^ θ_rh := by
        have hb := hψ_rh n hn
        rwa [RHTower.psiRemainder, RHTower.chebyshevPsi_eq_psi] at hb
      have hpt : |Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)| ≤
          3 * (Real.log 4 + 4) * (n : ℝ) ^ θ_rh := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
        have h1 := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt (n : ℝ)
        have hsq_le : Real.sqrt n ≤ (n : ℝ) ^ θ_rh := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le hnR1 (by dsimp [θ_rh]; linarith)
        exact h1.trans (mul_le_mul_of_nonneg_left hsq_le (by positivity))
      have htri := abs_sub (Chebyshev.psi (n : ℝ) - (n : ℝ))
        (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))
      rw [show (Chebyshev.psi (n : ℝ) - (n : ℝ)) -
          (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) =
          Chebyshev.theta (n : ℝ) - (n : ℝ) by ring] at htri
      linarith only [htri, hψn, hpt]
    obtain ⟨C₂, hC₂, hwave⟩ := theta_power_prime_wave_approx
      (by dsimp [θ_rh]; linarith) (by dsimp [θ_rh, ε_rh]; linarith) (by linarith) hβ1
      (by positivity) hθ_nat_rh γ
    -- Notice `max (1/4) (θ_rh + β - 1) = max (1/4) (β / 2) ≤ 1 / 2` AND `α / 2 ≤ 1 / 2`!
    set C_all : ℝ := K_rh + C₁ + C₂
    have hC_all : 0 ≤ C_all := by dsimp [C_all]; positivity
    set ρ : ℂ := (β : ℂ) + I * (γ : ℂ)
    have hmode_s : ∀ s : ℝ, 0 ≤ s →
        |editedTheta e (Real.exp s) - Real.exp s +
            2 * ((1 : ℕ) : ℝ) * (Complex.exp (ρ * (s : ℂ)) / ρ).re| ≤
          C_all * Real.exp (s / 2) * (1 + s) ^ 2 := by
      intro s hs
      set x := Real.exp s
      have hx1 : 1 ≤ x := Real.one_le_exp hs
      have h1_sq : 1 ≤ (1 + Real.log x) ^ 2 := by rw [Real.log_exp]; nlinarith
      have hb_θ := hθ_rh x hx1
      have hb_ed : |∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          ((e p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) * Real.log p| ≤
          C₁ * Real.sqrt x * (1 + Real.log x) ^ 2 := by
        refine (hedit x hx1).trans ?_
        have hrp : x ^ (α / 2) ≤ Real.sqrt x := by
          rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrp hC₁) (sq_nonneg _)
      have hb_wv : |2 * (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
            (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p) -
          2 * (Complex.exp (ρ * (s : ℂ)) / ρ).re| ≤
          C₂ * Real.sqrt x * (1 + Real.log x) ^ 2 := by
        have hcp : (x : ℂ) ^ ρ = Complex.exp (ρ * (s : ℂ)) := by
          dsimp [x]
          rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'),
            ← Complex.ofReal_log (Real.exp_pos s).le, Real.log_exp, mul_comm]
        rw [← hcp]
        refine (hwave x hx1).trans ?_
        have hrp : x ^ (max (1 / 4) (θ_rh + β - 1)) ≤ Real.sqrt x := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le hx1
            (max_le (by norm_num) (by dsimp [θ_rh, ε_rh]; linarith))
        exact (mul_le_mul_of_nonneg_left hrp hC₂).trans
          (le_mul_of_one_le_right (by positivity) h1_sq)
      have hsum_id : editedTheta e x - x +
          2 * ((1 : ℕ) : ℝ) * (Complex.exp (ρ * (s : ℂ)) / ρ).re =
          (Chebyshev.theta x - x) +
            (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
              ((e p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) * Real.log p) -
            (2 * (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
                (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p) -
              2 * (Complex.exp (ρ * (s : ℂ)) / ρ).re) := by
        unfold editedTheta
        rw [Nat.cast_one, mul_one]
        have hlin : (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
            ((e p : ℝ) + 2 * (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p)) * Real.log p) =
            (∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (e p : ℝ) * Real.log p) +
              2 * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
                (p : ℝ) ^ (β - 1) * Real.cos (γ * Real.log p) * Real.log p := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [hlin]; ring
      rw [hsum_id]
      have htri := (abs_sub _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add hb_θ hb_ed)) hb_wv)
      have hsqrt_x : Real.sqrt x = Real.exp (s / 2) := (Real.exp_half s).symm
      have hlog_x : Real.log x = s := Real.log_exp s
      rw [hsqrt_x, hlog_x] at htri
      dsimp [C_all]
      linarith only [htri]
    set h := quarterPeriodStep γ
    have hh : 0 < h := quarterPeriodStep_pos hγ
    rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not]
    refine ⟨4 * C_all * Real.exp h * (1 + 2 * h) ^ 2, 0, fun t ht => ?_⟩
    set B_t : ℝ := C_all * Real.exp ((t + 2 * h) / 2) * (1 + (t + 2 * h)) ^ 2
    have hm_step : ∀ s : ℝ, t ≤ s → s ≤ t + 2 * h →
        |editedTheta e (Real.exp s) - Real.exp s +
            2 * ((1 : ℕ) : ℝ) * (Complex.exp (ρ * (s : ℂ)) / ρ).re| ≤ B_t := by
      intro s hs1 hs2
      refine (hmode_s s (ht.trans hs1)).trans ?_
      dsimp [B_t]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC_all)
        (pow_le_pow_left₀ (by linarith) (by linarith) 2) (sq_nonneg _) (by positivity)
    have hr := abs_radialDiscrepancyOf_le_of_mode_error
      (f := fun s => editedTheta e (Real.exp s) - Real.exp s) (t := t) (by linarith) hγ 1
      (hm_step t le_rfl (by linarith))
      (hm_step (t + h) (by linarith) (by linarith))
      (hm_step (t + 2 * h) (by linarith) le_rfl)
    refine hr.trans ?_
    dsimp [B_t]
    have hexp_sp : Real.exp ((t + 2 * h) / 2) = Real.exp h * Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h1t : (1 + (t + 2 * h)) ^ 2 ≤ (1 + 2 * h) ^ 2 * (1 + t) ^ 2 := by
      have : 1 + (t + 2 * h) ≤ (1 + 2 * h) * (1 + t) := by nlinarith [ht, hh]
      exact (pow_le_pow_left₀ (by linarith) this 2).trans_eq (mul_pow _ _ 2)
    rw [hexp_sp]
    calc 4 * (C_all * (Real.exp h * Real.exp (t / 2)) * (1 + (t + 2 * h)) ^ 2)
        ≤ 4 * (C_all * (Real.exp h * Real.exp (t / 2)) * ((1 + 2 * h) ^ 2 * (1 + t) ^ 2)) := by
          gcongr
      _ = 4 * C_all * Real.exp h * (1 + 2 * h) ^ 2 * Real.exp (t / 2) * (1 + t) ^ 2 := by ring
  exact ⟨he, hrad, hviol⟩

/-! ### 5. Second-order multiplicity separation at a single off-line quartet -/

/-- **Exact second-order characterization of simplicity under `HasSingleOffLineQuartet ρ₀`.**
For any lone off-line quartet `HasSingleOffLineQuartet ρ₀`, unit multiplicity is equivalent to:
1. `deriv riemannZeta ρ₀ ≠ 0`;
2. unboundedness of the log-twisted reflected-composite defect against `√n squarefreeDivisorMass n`;
3. unboundedness of the log-twisted smooth-power receiver `logOscillatingSmoothPower (1 - Re ρ₀) (Im ρ₀)`. -/
theorem singleQuartet_simple_iff_logTwisted_unbounded {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    [HasSimpleSingleOffLineQuartet ρ₀,
      deriv riemannZeta ρ₀ ≠ 0,
      ¬ (∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
        |clippedCofactorOp n ⌊2 * Real.sqrt n⌋₊ (logTwistedWaveModel ρ₀) -
            midpointSecondDiff n (logTwistedWaveModel ρ₀)| ≤
          C * Real.sqrt n * squarefreeDivisorMass n),
      ¬ ReceiverBounded (logOscillatingSmoothPower (1 - ρ₀.re) ρ₀.im)].TFAE := by
  tfae_have 1 ↔ 2 := by
    rw [hasSimpleSingleOffLineQuartet_iff_deriv_ne_zero]
    exact ⟨And.right, fun hd => ⟨hq, hd⟩⟩
  tfae_have 2 ↔ 3 :=
    (logTwisted_wave_compatible_iff_deriv_zero hq.1 hq.re_lt_one hq.im_ne_zero hq.2.1.1).not.symm
  tfae_have 2 ↔ 4 := by
    have hε : 0 < 1 - ρ₀.re := by linarith [hq.re_lt_one]
    have hε2 : 1 - ρ₀.re ≤ 1 / 2 := by linarith [hq.1]
    have hρ_eq : (((1 - (1 - ρ₀.re) : ℝ) : ℂ) + (ρ₀.im : ℂ) * I) = ρ₀ := by
      apply Complex.ext <;> simp
    rw [receiverBounded_logOscillatingSmoothPower_iff hε hε2 ρ₀.im, hρ_eq, not_and]
    exact ⟨fun hne _ => hne, fun h => h hq.2.1.1⟩
  tfae_finish

/-! ### 6. Global equivalences, corollaries, and `Θ`-non-advancement of `NoSimpleSingleOffLineQuartet` -/

/-- **Six-way global equivalence characterizing `NoSimpleSingleOffLineQuartet`.** -/
theorem noSimpleSingleOffLineQuartet_tfae :
    [NoSimpleSingleOffLineQuartet,
      RiemannHypothesis ∨ 4 ≤ (rightZeros zetaZeroConfig).encard ∨
        ∃ ρ₀ : ℂ, HasSingleOffLineQuartet ρ₀ ∧ 2 ≤ quartetCopyMult ρ₀,
      {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard ≠ 2,
      {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.encard ≠ 4,
      ∀ β γ : ℝ, 1 / 2 < β → β < 1 → 0 < γ →
        IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ 1) ∨
          IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 2 β γ) ∨
          IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 3 β γ) ∨
          IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 6 β γ),
      ∀ β γ : ℝ, 1 / 2 < β → β < 1 → 0 < γ →
        ¬ ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
          |oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊ +
              2 * ((x : ℂ) ^ (((β : ℂ) + I * (γ : ℂ))) /
                (((β : ℂ) + I * (γ : ℂ)))).re| ≤
            K * Real.sqrt x * (Real.log x) ^ 2].TFAE := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hno
      by_cases hex : ∃ ρ₀ : ℂ, HasSingleOffLineQuartet ρ₀
      · obtain ⟨ρ₀, hq⟩ := hex
        have hm1 : quartetCopyMult ρ₀ ≠ 1 := fun h1 => hno ρ₀ ⟨hq, h1⟩
        have hm_pos := hq.quartetCopyMult_pos
        exact Or.inr (Or.inr ⟨ρ₀, hq, by omega⟩)
      · push Not at hex
        rcases no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros.mp hex with hrh | h4
        · exact Or.inl hrh
        · exact Or.inr (Or.inl h4)
    · rintro (hrh | h4 | ⟨ρ₀, hq₀, hm2⟩) ρ ⟨hq, hm1⟩
      · exact (no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros.mpr (Or.inl hrh)) ρ hq
      · exact (no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros.mpr (Or.inr h4)) ρ hq
      · have hc1 := rightXiZeroCopy_encard_of_singleQuartet hq
        have hc0 := rightXiZeroCopy_encard_of_singleQuartet hq₀
        rw [hc0] at hc1
        have heq : 2 * quartetCopyMult ρ₀ = 2 * quartetCopyMult ρ := Nat.cast_injective hc1
        omega
  tfae_have 3 ↔ 4 := by
    rw [← rightXiZeroCopy_le_offLineXiZeroCopy_two_mul]
    refine not_congr ?_
    constructor
    · intro h2; rw [h2]; norm_num
    · intro h4
      cases hc : {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard with
      | top => rw [hc] at h4; simp at h4
      | coe n =>
        rw [hc] at h4
        have hn : 2 * n = 4 := by exact_mod_cast h4
        exact_mod_cast (show n = 2 by omega)
  tfae_have 1 ↔ 3 := by
    rw [← not_iff_not]
    unfold NoSimpleSingleOffLineQuartet
    push Not
    constructor
    · rintro ⟨ρ₀, hq, hm1⟩
      rw [rightXiZeroCopy_encard_of_singleQuartet hq, hm1]
      norm_num
    · intro h2
      have hne : {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.Nonempty :=
        Set.encard_ne_zero.mp (by rw [h2]; norm_num)
      obtain ⟨q₀, hq₀⟩ := hne
      set z₀ : ℂ := (q₀.1 : ℂ)
      have hz_mem : z₀ ∈ zetaZeroConfig.carrier := xiZeroCopy_mem_carrier q₀
      have hz_re : 1 / 2 < z₀.re := hq₀
      have hz_im_ne : z₀.im ≠ 0 := by
        intro him0
        exact RHTower.riemannZeta_ne_zero_of_abs_im_lt_four hz_mem.2.1 hz_mem.2.2
          (by rw [him0, abs_zero]; norm_num) hz_mem.1
      by_cases him_pos : 0 < z₀.im
      · exact ⟨z₀, ((hasSimpleSingleOffLineQuartet_tfae hz_re him_pos hz_mem).out 2 0).mp h2⟩
      · have hconj_im : 0 < (conj z₀).im := by
          simp; exact lt_of_le_of_ne (not_lt.mp him_pos) hz_im_ne
        have hconj_mem : conj z₀ ∈ zetaZeroConfig.carrier := by
          have hxi_c : RHTower.xi (conj z₀) = 0 := by
            rw [xi_conj, xi_zero_of_mem_carrier hz_mem, map_zero]
          obtain ⟨qc, hqc⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi_c
          exact hqc ▸ xiZeroCopy_mem_carrier qc
        have hconj_re : 1 / 2 < (conj z₀).re := by simp; linarith [hz_re]
        exact ⟨conj z₀,
          ((hasSimpleSingleOffLineQuartet_tfae hconj_re hconj_im hconj_mem).out 2 0).mp h2⟩
  tfae_have 1 ↔ 5 := by
    constructor
    · intro hno β γ hβ hβ1 hγ
      by_contra! hall
      exact hno ((β : ℂ) + I * (γ : ℂ))
        ((radial_and_ordinary_236_iff_singleQuartet_with_mult hβ hβ1 hγ (le_refl 1)).mp hall)
    · intro h5 ρ₀ ⟨hq, hm1⟩
      by_cases him_pos : 0 < ρ₀.im
      · have hρ_eq : ((ρ₀.re : ℂ) + I * (ρ₀.im : ℂ)) = ρ₀ := by apply Complex.ext <;> simp
        have h8 := ((hasSimpleSingleOffLineQuartet_tfae hq.1 him_pos hq.2.1).out 0 7).mp
          (⟨hq, hm1⟩ : HasSimpleSingleOffLineQuartet ρ₀)
        rcases h5 ρ₀.re ρ₀.im hq.1 hq.re_lt_one him_pos with h | h | h | h
        · exact h8.1 h
        · exact h8.2.1 h
        · exact h8.2.2.1 h
        · exact h8.2.2.2 h
      · have him_lt : ρ₀.im < 0 := lt_of_le_of_ne (not_lt.mp him_pos) hq.im_ne_zero
        have hqc : HasSingleOffLineQuartet (conj ρ₀) := by
          refine ⟨by simp; linarith [hq.1], ?_, ?_⟩
          · have : conj ρ₀ ∈ {z ∈ zetaZeroConfig.carrier | z.re ≠ 1 / 2} := by
              rw [hq.2.2]; exact Or.inr (Or.inl rfl)
            exact this.1
          · rw [hq.2.2]
            ext z
            simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff, conj_conj]
            tauto
        have hmc1 : quartetCopyMult (conj ρ₀) = 1 := by rwa [quartetCopyMult_conj]
        have hcim : 0 < (conj ρ₀).im := by simp; linarith
        have h8 := ((hasSimpleSingleOffLineQuartet_tfae hqc.1 hcim hqc.2.1).out 0 7).mp
          (⟨hqc, hmc1⟩ : HasSimpleSingleOffLineQuartet (conj ρ₀))
        rcases h5 (conj ρ₀).re (conj ρ₀).im hqc.1 hqc.re_lt_one hcim with h | h | h | h
        · exact h8.1 h
        · exact h8.2.1 h
        · exact h8.2.2.1 h
        · exact h8.2.2.2 h
  tfae_have 5 → 6 := by
    intro h5 β γ hβ hβ1 hγ ⟨K, hK⟩
    set ρ₀ : ℂ := (β : ℂ) + I * (γ : ℂ)
    obtain ⟨A_odd, hA_odd0, hodd⟩ := odd_composite_baseline_prime_error
    obtain ⟨A_pt, hA_pt⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
    have hθ : ∃ K' : ℝ, ∀ x : ℝ, 16 ≤ x →
        |Chebyshev.theta x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re| ≤
          K' * Real.sqrt x * (Real.log x) ^ 2 := by
      refine ⟨K + A_odd + 1 + |A_pt|, fun x hx => ?_⟩
      have hx1 : 1 ≤ x := by linarith
      have hx0 : 0 < x := by linarith
      have hj : 0 < ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
      have hlo := Nat.floor_le hx0.le
      have hhi := Nat.lt_floor_add_one x
      have hb := hodd hj
      have hs := Real.sqrt_le_sqrt hlo
      have hs1 := Real.one_le_sqrt.mpr hx1
      have hl1 : 1 ≤ Real.log x :=
        (Real.le_log_iff_exp_le hx0).mpr (by linarith [Real.exp_one_lt_three, hx])
      have hd_odd : |(oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) -
          (Chebyshev.psi x - x)| ≤ (A_odd + 1) * Real.sqrt x * (Real.log x) ^ 2 := by
        have heq : (oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) -
            (Chebyshev.psi x - x) =
            ((oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) -
              (Chebyshev.psi ⌊x⌋₊ - ⌊x⌋₊)) + (x - ⌊x⌋₊) := by
          rw [Chebyshev.psi_eq_psi_coe_floor x]; ring
        rw [heq]
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
        refine le_trans (b := (A_odd + 1) * Real.sqrt x) ?_
          (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl1))
        linarith only [hb, mul_le_mul_of_nonneg_left hs hA_odd0, hs1, hhi]
      have hd_pt : |Chebyshev.psi x - Chebyshev.theta x| ≤
          |A_pt| * Real.sqrt x * (Real.log x) ^ 2 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
        exact (hA_pt x).trans ((mul_le_mul_of_nonneg_right (le_abs_self A_pt) (Real.sqrt_nonneg x)).trans
          (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl1)))
      set U := oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊ +
        2 * ((x : ℂ) ^ ρ₀ / ρ₀).re
      set V := (oddCompositeBaseline ⌊x⌋₊ - oddCompositePrimeMass ⌊x⌋₊) - (Chebyshev.psi x - x)
      have hid : Chebyshev.theta x - x + 2 * ((x : ℂ) ^ ρ₀ / ρ₀).re =
          U - V - (Chebyshev.psi x - Chebyshev.theta x) := by
        dsimp [U, V]; ring
      rw [hid]
      have htri := (abs_sub (U - V) (Chebyshev.psi x - Chebyshev.theta x)).trans
        (add_le_add (abs_sub U V) le_rfl)
      linarith only [htri, hK x hx, hd_odd, hd_pt]
    have h8 := unit_theta_wave_implies_radial_and_236 hβ hβ1 hγ hθ
    rcases h5 β γ hβ hβ1 hγ with h | h | h | h
    · exact h8.1 h
    · exact h8.2.1 h
    · exact h8.2.2.1 h
    · exact h8.2.2.2 h
  tfae_have 6 → 1 := by
    intro h6 ρ₀ ⟨hq, hm1⟩
    by_cases him_pos : 0 < ρ₀.im
    · have hρ_eq : ((ρ₀.re : ℂ) + I * (ρ₀.im : ℂ)) = ρ₀ := by apply Complex.ext <;> simp
      have h7 := ((hasSimpleSingleOffLineQuartet_tfae hq.1 him_pos hq.2.1).out 0 6).mp
        (⟨hq, hm1⟩ : HasSimpleSingleOffLineQuartet ρ₀)
      rw [← hρ_eq] at h7
      exact h6 ρ₀.re ρ₀.im hq.1 hq.re_lt_one him_pos h7
    · have him_lt : ρ₀.im < 0 := lt_of_le_of_ne (not_lt.mp him_pos) hq.im_ne_zero
      have hqc : HasSingleOffLineQuartet (conj ρ₀) := by
        refine ⟨by simp; linarith [hq.1], ?_, ?_⟩
        · have : conj ρ₀ ∈ {z ∈ zetaZeroConfig.carrier | z.re ≠ 1 / 2} := by
            rw [hq.2.2]; exact Or.inr (Or.inl rfl)
          exact this.1
        · rw [hq.2.2]
          ext z
          simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff, conj_conj]
          tauto
      have hmc1 : quartetCopyMult (conj ρ₀) = 1 := by rwa [quartetCopyMult_conj]
      have hcim : 0 < (conj ρ₀).im := by simp; linarith
      have hρc_eq : (((conj ρ₀).re : ℂ) + I * ((conj ρ₀).im : ℂ)) = conj ρ₀ := by
        apply Complex.ext <;> simp
      have h7 := ((hasSimpleSingleOffLineQuartet_tfae hqc.1 hcim hqc.2.1).out 0 6).mp
        (⟨hqc, hmc1⟩ : HasSimpleSingleOffLineQuartet (conj ρ₀))
      rw [← hρc_eq] at h7
      exact h6 (conj ρ₀).re (conj ρ₀).im hqc.1 hqc.re_lt_one hcim h7
  tfae_finish

/-- **Collected structural corollaries of `NoSimpleSingleOffLineQuartet`.**
1. Under `SimpleZerosConjecture` (`∀ ρ, ζ(ρ) = 0 → ζ'(ρ) ≠ 0`), `NoSimpleSingleOffLineQuartet`
   upgrades to full `∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀` (`RH ∨ 4 ≤ #(rightZeros)`).
2. Whenever `¬ RiemannHypothesis` holds, the off-line `XiZeroCopy` divisor has cardinality `≥ 8`
   (right-half-plane `XiZeroCopy` cardinality `≥ 4`), either via `≥ 2` distinct quartets or one
   ramified quartet with `ζ'(ρ₀) = 0`, bounded log-twisted reflected-composite defect, and bounded
   `logOscillatingSmoothPower` receiver.
3. Every bounded unit-multiplicity two-interval prime-radius trial forces a higher-multiplicity
   odd-harmonic alias `k ≥ 2` (`2 ≤ quartetCopyMult ≤ 2k`). -/
theorem corollaries_of_noSimpleSingleOffLineQuartet (hno : NoSimpleSingleOffLineQuartet) :
    ((∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → deriv riemannZeta ρ ≠ 0) →
      (RiemannHypothesis ∨ 4 ≤ (rightZeros zetaZeroConfig).encard)) ∧
    (¬ RiemannHypothesis →
      4 ≤ {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard ∧
        8 ≤ {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.encard ∧
        (4 ≤ (rightZeros zetaZeroConfig).encard ∨
          ∃ ρ₀ : ℂ, HasSingleOffLineQuartet ρ₀ ∧ 2 ≤ quartetCopyMult ρ₀ ∧
            deriv riemannZeta ρ₀ = 0 ∧
            ReceiverBounded (logOscillatingSmoothPower (1 - ρ₀.re) ρ₀.im))) ∧
    (∀ {β γ : ℝ}, 1 / 2 < β → β < 1 → 0 < γ →
      ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ 1) →
      ∃ k : ℕ, 2 ≤ k ∧
        HasSingleOffLineQuartet ((β : ℂ) + I * (((2 * (k : ℝ) + 1) * γ : ℝ) : ℂ)) ∧
        2 ≤ quartetCopyMult ((β : ℂ) + I * (((2 * (k : ℝ) + 1) * γ : ℝ) : ℂ)) ∧
        quartetCopyMult ((β : ℂ) + I * (((2 * (k : ℝ) + 1) * γ : ℝ) : ℂ)) ≤ 2 * k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hsimple
    rcases (noSimpleSingleOffLineQuartet_tfae.out 0 1).mp hno with hrh | h4 | ⟨ρ₀, hq₀, hm2⟩
    · exact Or.inl hrh
    · exact Or.inr h4
    · exfalso
      exact hsimple ρ₀ hq₀.1 hq₀.re_lt_one hq₀.2.1.1
        ((two_le_quartetCopyMult_iff_deriv_eq_zero hq₀.2.1).mp hm2)
  · intro hnrh
    rcases (noSimpleSingleOffLineQuartet_tfae.out 0 1).mp hno with hrh | h4 | ⟨ρ₀, hq₀, hm2⟩
    · exact (hnrh hrh).elim
    · have hge4 : 4 ≤ {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard :=
        h4.trans rightZeros_le_rightXiZeroCopy_encard
      have hge8 : 8 ≤ {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.encard := by
        rw [← rightXiZeroCopy_le_offLineXiZeroCopy_two_mul]
        calc (8 : ℕ∞) = 2 * 4 := by norm_num
          _ ≤ 2 * {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard :=
              mul_le_mul_right hge4 2
      exact ⟨hge4, hge8, Or.inl h4⟩
    · have hge4 : 4 ≤ {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re}.encard := by
        rw [rightXiZeroCopy_encard_of_singleQuartet hq₀]
        exact_mod_cast (show 4 ≤ 2 * quartetCopyMult ρ₀ by omega)
      have hge8 : 8 ≤ {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.encard := by
        rw [offLineXiZeroCopy_encard_of_singleQuartet hq₀]
        exact_mod_cast (show 8 ≤ 4 * quartetCopyMult ρ₀ by omega)
      have hder0 : deriv riemannZeta ρ₀ = 0 :=
        (two_le_quartetCopyMult_iff_deriv_eq_zero hq₀.2.1).mp hm2
      have hrec : ReceiverBounded (logOscillatingSmoothPower (1 - ρ₀.re) ρ₀.im) := by
        have h4_iff := (singleQuartet_simple_iff_logTwisted_unbounded hq₀).out 1 3
        exact not_not.mp (mt h4_iff.mpr (not_not.mpr hder0))
      exact ⟨hge4, hge8, Or.inr ⟨ρ₀, hq₀, hm2, hder0, hrec⟩⟩
  · intro β γ hβ hβ1 hγ hbdd
    obtain ⟨k, hk2, hq, hm2, hm2k, _⟩ :=
      unit_trial_under_noSimple_forces_ramified_quartet hno hβ hβ1 hγ hbdd
    exact ⟨k, hk2, hq, hm2, hm2k⟩

/-- **`Θ`-non-advancement of excluding a lone simple off-line layer across `(1/2, 14/15)`.**
For every abscissa `b ∈ (1/2, 14/15)` and every norm-error exponent `β ∈ (b, 1)`, `{0, 1, 2}`-prime
two-sided edits unconditionally realize:
1. a **double** single right-half-plane pair at `b ± i` (`IsLayerTwin` on `Fin 2` with constant map
   `b + i`), and
2. **two distinct simple** right-half-plane pairs at `b ± i` and `b ± 2i`,
both avoiding the lone-simple-pair configuration while attaining supremum abscissa `b`. -/
theorem abscissa_unconstrained_under_no_simple_single_layer {b β : ℝ} (hb0 : 1 / 2 < b)
    (hb : b < 14 / 15) (hβ : b < β) (hβ1 : β < 1) :
    (∃ e₁ : ℕ → ℤ, IsEdit e₁ ∧ IsIntegerNormFakeAt (editSystem e₁) β ∧
      IsLayerTwin (editSystem e₁) Finset.univ (fun _ : Fin 2 => (b : ℂ) + I) ∧
      HasFakeZeroSet (editSystem e₁)
        {z : ℂ | ∃ _ : Fin 2, z = (b : ℂ) + I ∨ z = (starRingEnd ℂ) ((b : ℂ) + I)}) ∧
    (∃ e₂ : ℕ → ℤ, IsEdit e₂ ∧ IsIntegerNormFakeAt (editSystem e₂) β ∧
      IsLayerTwin (editSystem e₂) Finset.univ
        (fun j : Bool => if j then (b : ℂ) + I else (b : ℂ) + 2 * I) ∧
      HasFakeZeroSet (editSystem e₂)
        {z : ℂ | ∃ j : Bool,
          z = (if j then (b : ℂ) + I else (b : ℂ) + 2 * I) ∨
          z = (starRingEnd ℂ) (if j then (b : ℂ) + I else (b : ℂ) + 2 * I)}) := by
  have hb_pos : 0 < b := by linarith
  have hb_lt1 : b < 1 := by linarith
  have hζ1 : riemannZeta ((b : ℂ) + I) ≠ 0 :=
    RHTower.riemannZeta_ne_zero_of_abs_im_lt_four (by simp [hb_pos]) (by simp [hb_lt1]) (by simp)
  refine ⟨?_, ?_⟩
  · simpa only [Finset.mem_univ, true_and] using
      exists_isEdit_fake_with_layer Finset.univ (fun _ : Fin 2 => (b : ℂ) + I) hb0 hb
        (fun _ _ => by simp; linarith [hb0]) ⟨0, Finset.mem_univ 0, hζ1⟩ hβ hβ1
  · simpa only [Finset.mem_univ, true_and] using
      exists_isEdit_fake_with_layer Finset.univ
        (fun j : Bool => if j then (b : ℂ) + I else (b : ℂ) + 2 * I) hb0 hb
        (fun j _ => by cases j <;> simp <;> linarith [hb0])
        ⟨true, Finset.mem_univ true, by simpa using hζ1⟩ hβ hβ1

#print axioms quartetCopyMult_eq_one_iff_deriv_ne_zero
#print axioms hasSimpleSingleOffLineQuartet_tfae
#print axioms unit_multiplicity_no_odd_harmonic_alias
#print axioms unit_trial_under_noSimple_forces_ramified_quartet
#print axioms coprimeZeroOneSet_imitator_rejected_by_reflectedComposites
#print axioms unconditional_sEdit_rejected_above_max_two_thirds_zetaZeroAbscissa
#print axioms unconditional_sEdit_rejected_on_zeroFreeStrip
#print axioms rh_sEdit_imitates_radius_but_violates_reflectedComposites
#print axioms singleQuartet_simple_iff_logTwisted_unbounded
#print axioms noSimpleSingleOffLineQuartet_tfae
#print axioms corollaries_of_noSimpleSingleOffLineQuartet
#print axioms abscissa_unconstrained_under_no_simple_single_layer

end GaloisForLFunctions.ExceptionalLayerTheory
