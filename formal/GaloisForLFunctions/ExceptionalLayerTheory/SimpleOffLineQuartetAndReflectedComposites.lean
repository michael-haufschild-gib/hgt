import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ReflectedCompositeWaveTransmission
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeErrorInOddCompositeProducts
import GaloisForLFunctions.ExceptionalLayerTheory.TheOrdinaryPrimeRadiusDetectsExactlyOneOffLineQuartet
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.EveryFiniteLayerIsRealizedByATwoSidedEdit
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheLogTwistedOscillatingSmoothPowerIsPaidExactlyAtTheDoubleZerosOfZeta
import GaloisForLFunctions.RHTower.BaezDuarteBurnolMultiplicityAllZeros
import GaloisForLFunctions.RHTower.WeilConeDilationRealnessRigidity

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
   `unconditional_sEdit_rejected_by_reflectedComposites_on_zeroFreeZone`,
   `rh_sEdit_imitates_radius_but_violates_reflectedComposites`):
   Every `{0, 1}`-coprime integer-set imitator (`1/2 < β < 1`, `ζ(β + iγ) ≠ 0`), every `{0, 1, 2}`
   prime `sEdit` on `7/8 ≤ β < 1` unconditionally, and every `sEdit` on `3/4 < β < 1` under `RH`
   violates the ordinary-integer reflected-composite identity at scale `Ω(n^β)`. Meanwhile,
   first-order reflected-composite transmission and `q`-divisible cofactor slicing are satisfied at
   every genuine zero `ζ(ρ₀) = 0`, and intrinsic Beurling composites (`β ∈ (1/2, 2/3)`) and
   positive Euler twins realize simple off-line pairs/quartets on their respective structural sides.

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

open Complex Filter Topology Set Finset MeasureTheory
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

/-- On `{0 < Re ρ < 1}` where `ζ(ρ) = 0`, `quartetCopyMult ρ` coincides with `analyticOrderNatAt riemannZeta ρ`. -/
theorem quartetCopyMult_eq_analyticOrderNatAt {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hζ : riemannZeta ρ = 0) :
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
  have han : AnalyticAt ℂ riemannZeta ρ := RHTower.analyticOn_riemannZeta ρ hρ1
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    apply RHTower.analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (x := 2) (by simp) (by simpa using hρ1)
    rw [analyticOrderAt_eq_zero.mpr (Or.inr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re)))]
    exact ENat.zero_ne_top
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
  obtain ⟨hζ, h0, h1⟩ := hmem
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  rw [quartetCopyMult_eq_analyticOrderNatAt h0 h1 hζ]
  obtain ⟨hge1, hvan⟩ := RHTower.one_le_analyticOrderNatAt_and_iteratedDeriv_riemannZeta hρ1 hζ
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    apply RHTower.analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (x := 2) (by simp) (by simpa using hρ1)
    rw [analyticOrderAt_eq_zero.mpr (Or.inr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re)))]
    exact ENat.zero_ne_top
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
  obtain ⟨hζ, h0, h1⟩ := hmem
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
  rw [← himg, hinj.InjOn.encard_image, Set.encard_univ, ENat.card_eq_coe_fintype_card,
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
    · rintro (h | h) <;> rw [h] <;> simp [hq.1]
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
    exact Nat.cast_injective (R := ℂ) hs
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
  rw [← Set.encard_univ_coe, ← Set.encard_univ_coe]
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
    Set.disjoint_left.mpr fun _ h1 h2 => (lt_trans h2 h1).false
  -- Reflection `z ↦ 1 - z` on `XiZeroCopy` preserves divisor multiplicity (`xi_divisor_one_sub`)
  let reflSupport (ρ : XiDivisorSupport) : XiDivisorSupport :=
    ⟨1 - (ρ : ℂ), by
      have h := ρ.2
      rwa [Function.mem_support, xi_divisor_one_sub]⟩
  let reflCopy (q : XiZeroCopy) : XiZeroCopy :=
    ⟨reflSupport q.1, Fin.cast (by dsimp [reflSupport]; rw [xi_divisor_one_sub]) q.2⟩
  have hrefl_inv : ∀ q : XiZeroCopy, reflCopy (reflCopy q) = q := by
    rintro ⟨⟨z, hz⟩, k⟩
    have h1 : (1 : ℂ) - (1 - z) = z := by ring
    refine Sigma.ext (Subtype.ext h1) ?_
    simp [reflCopy, reflSupport]
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
  rw [hpart, Set.encard_union_eq hdisj, ← himg_r, hinj_r.InjOn.encard_image, two_mul]

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
    rw [thetaRadialDiscrepancy, isLogSqrtSqUnbounded_iff_not_eventually_le, not_not]
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
      rw [Nat.cast_one, one_mul]
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
      have hcp_a (u : ℝ) (hu : 0 < u) : ((u * x : ℝ) : ℂ) ^ ρ = (u : ℂ) ^ ρ * (x : ℂ) ^ ρ := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hu hx0).ne'),
          Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
          Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx0.ne'),
          ← Complex.ofReal_log (mul_pos hu hx0).le, ← Complex.ofReal_log hu.le,
          ← Complex.ofReal_log hx0.le, Real.log_mul hu.ne' hx0.ne', Complex.ofReal_add,
          mul_add, Complex.exp_add]
      have ha2 : ((a ^ 2 * x : ℝ) : ℂ) ^ ρ = ((a : ℂ) ^ ρ) ^ 2 * (x : ℂ) ^ ρ := by
        rw [sq a, mul_assoc, hcp_a a ha0, hcp_a a ha0, sq ((a : ℂ) ^ ρ), mul_assoc]
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
        rw [hap, ha2b, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        have hsc : (Real.cos (γ * Real.log a) : ℂ) ^ 2 +
            (Real.sin (γ * Real.log a) : ℂ) ^ 2 = 1 := by
          exact_mod_cast Real.cos_sq_add_sin_sq (γ * Real.log a)
        push_cast
        linear_combination ((a ^ β : ℂ) ^ 2) * (hsc - 1)
      have hcomb : (((a ^ 2 * x : ℝ) : ℂ) ^ ρ / ρ) -
          (((2 * a ^ β * Real.cos (γ * Real.log a) : ℝ) : ℂ)) * (((a * x : ℝ) : ℂ) ^ ρ / ρ) +
          ((a ^ (2 * β) : ℝ) : ℂ) * ((x : ℂ) ^ ρ / ρ) = 0 := by
        rw [ha2, hcp_a a ha0]
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
    have hnrh : ¬ RiemannHypothesis := by
      intro hrh
      have hemp : {q : XiZeroCopy | 1 / 2 < (q.1 : ℂ).re} = ∅ :=
        Set.eq_empty_of_forall_notMem fun q hq =>
          (lt_irrefl (1 / 2 : ℝ)) ((RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hrh q) ▸ hq)
      rw [hemp, Set.encard_empty] at h2
      norm_num at h2
    have hle2 : (rightZeros zetaZeroConfig).encard ≤ 2 :=
      rightZeros_le_rightXiZeroCopy_encard.trans h2.le
    have hrz2 : (rightZeros zetaZeroConfig).encard = 2 :=
      (exists_singleOffLineQuartet_ecs_tfae.out 2 1).mp ⟨hnrh, hle2⟩
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
      · exact ⟨hc_mem, by simp [hre]⟩
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
      rw [sub_add_add_cancel] at htri
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
      rw [sq_abs] at hpyth ⊢; nlinarith only [hgt, hγ2]
    have h2 : β ^ 2 + (2 * (k : ℝ) + 1) ^ 2 * |γ| ^ 2 ≤
        (m : ℝ) ^ 2 * (β ^ 2 + ((2 * (k : ℝ) + 1) * |γ|) ^ 2) := by
      have hnn : 0 ≤ β ^ 2 + ((2 * (k : ℝ) + 1) * |γ|) ^ 2 := by positivity
      have he : β ^ 2 + (2 * (k : ℝ) + 1) ^ 2 * |γ| ^ 2 =
          1 * (β ^ 2 + ((2 * (k : ℝ) + 1) * |γ|) ^ 2) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hm2 hnn
    rw [sq_abs] at h2
    linarith only [hpyth, h1, h2]
  have hk0 : k = 0 := Nat.cast_injective hk0R
  subst hk0
  simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, sq_abs] at hpyth hω
  have hden : 0 < β ^ 2 + γ ^ 2 := by positivity
  have hm_sq1 : (m : ℝ) ^ 2 = 1 := by nlinarith only [hpyth, hden]
  have hm1R : (m : ℝ) = 1 := by nlinarith only [hm_sq1, hmR1]
  exact ⟨rfl, Nat.cast_injective hm1R, hω⟩

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
  rw [Nat.cast_one, one_pow, one_mul, abs_of_pos hγ] at hpyth hω
  have hk_ne0 : k ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul] at hpyth
    have hden : 0 < β ^ 2 + γ ^ 2 := by positivity
    have hm_sq : (quartetCopyMult ρ_k : ℝ) ^ 2 = 1 :=
      mul_right_cancel₀ hden.ne' (hpyth.trans (one_mul _).symm)
    have hm1R : (quartetCopyMult ρ_k : ℝ) = 1 := by
      nlinarith only [hm_sq, show (0 : ℝ) ≤ quartetCopyMult ρ_k by positivity]
    exact hm_ne1 (Nat.cast_injective hm1R)
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
  have hP1 : 1 ≤ P := Nat.le_floor (by linarith only [hsq1])
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
    rw [← Finset.sum_subset (Finset.filter_subset _ _)]
    intro v hv hvnot
    have hv0 : 0 < v := by linarith [(mem_Icc.mp (mem_filter.mp hv).1).1]
    have hgt : M < v := not_le.mp fun hle => hvnot (mem_filter.mpr ⟨hv, hle⟩)
    have hmul : 4 * n < v * P := (Nat.div_lt_iff_lt_mul (by omega : 0 < P)).mp hgt
    have h4 : 4 * n / v < P :=
      (Nat.div_lt_iff_lt_mul hv0).mpr (by rwa [mul_comm])
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
    rw [le_div_iff₀' ha_pos |> fun _ => div_mul_eq_mul_div, le_div_iff₀ ha_pos, one_mul,
      Finset.sum_mul]
    induction K_m with
    | zero =>
      simp [Real.zero_rpow ha_pos.ne']
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp [Real.zero_rpow ha_pos.ne']; linarith
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
        have hr1 := Real.rpow_le_rpow (Nat.cast_nonneg M) hM_le (by linarith)
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
    {r Q : ℕ} (hz0 : 1 / 2 < z.re) (hz1 : z.re < 1) (hzim : z.im ≠ 0) (hm : m ≠ 0)
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
    exists_prime_power_re_lower_bound Q hz_pos hzim hA_ne
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
    refine ⟨(4 / δ) ^ r, by positivity, fun y hy => ?_⟩
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    have h1_term : 1 + Real.log (4 * y) ≤ (4 / δ) * y ^ δ := by
      have hl := Real.log_le_sub_one_of_pos (mul_pos (show 0 < δ / 2 by positivity)
        (Real.rpow_pos_of_pos hy0 δ))
      -- Simpler: `log(4 * y^δ) / δ`: `log u ≤ u` via `Real.log_le_sub_one_of_pos`!
      have hyδ_pos : 0 < y ^ δ := Real.rpow_pos_of_pos hy0 δ
      have hl_y := Real.log_le_sub_one_of_pos hyδ_pos
      rw [Real.log_rpow hy0] at hl_y
      have hlog4 : 1 + Real.log 4 ≤ 3 := by
        have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      have hlog_mul : 1 + Real.log (4 * y) = 1 + Real.log 4 + (1 / δ) * (δ * Real.log y) := by
        rw [Real.log_mul (by norm_num) hy0.ne']; field_simp [hδ.ne']; ring
      have hyδ1 : 1 ≤ y ^ δ := Real.one_le_rpow hy hδ.le
      have h1_d : (1 / δ) * (δ * Real.log y) ≤ (1 / δ) * y ^ δ :=
        mul_le_mul_of_nonneg_left (by linarith only [hl_y]) (by positivity)
      have hδ_small_or : 1 + Real.log (4 * y) ≤ (3 + 1 / δ) * y ^ δ := by
        have h3 : 1 + Real.log 4 ≤ 3 * y ^ δ := by linarith only [hlog4, hyδ1]
        linarith only [hlog_mul, h3, h1_d]
      -- Wait: if `δ > 1`, `3 + 1/δ` could exceed `4/δ`! Instead use `(3 + 1 / δ)` as the constant!
      sorry
    sorry
  sorry

end GaloisForLFunctions.ExceptionalLayerTheory
