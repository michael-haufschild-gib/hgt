import GaloisForLFunctions.RHTower.WeilConditionalDeviationRH
import GaloisForLFunctions.RHTower.WeilConeCriticalZeroCarriedRigidity
import GaloisForLFunctions.RHTower.WeilDeletionZeroSide
import GaloisForLFunctions.RHTower.WeilDeletionTestKit
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper

/-!
# Constant sign up to a conditionally convergent error

**Theorem** (`eq_vonMangoldt_of_constant_sign_add_conditional`).  Let `lam` be full-cone
Weil-positive and `lam − Λ = u + w` on `n ≥ 2`, where `u` has constant sign and the partial sums of
`Σ w(n) n^{−1/2−it}` converge for every real `t`.  Then `lam = Λ` on `n ≥ 2` (and RH holds).

**Proof.**  By `WeilConditional.Decomposition.riemannHypothesis`, RH holds, so `Λ` is Weil-positive
with boundary measure `μ_Λ`, whose atoms are the orders `ord_{1/2+ia} ξ`; and the atoms of the
boundary measure `μ` of `lam` satisfy `|ord_{1/2+ia} ξ − μ{a}| ≤ μ{0}`
(`Decomposition.abs_atom_sub_le_atom_zero`).

Let `φ` be a smooth probability density supported in `[−17/50, 17/50]` with
`|φ̂(γ)| ≤ 1/((8/25)|γ|)` (`gapTest`) and `K = |φ̂|²`.  Its autocorrelation vanishes at `±log n`
for `n ≥ 2`, since `17/25 < log 2`, so the prime sides of `lam` and `Λ` agree on it and the explicit
formula gives `∫ K dμ = Σ_ρ m_ρ K(γ_ρ)`; under RH this is `Σ_{a ∈ Z} ord(a) K(a)` over the critical
ordinates `Z`.  The zero sum is small: `Σ_ρ m_ρ K(γ_ρ) ≤ (625/64)·(11/10)·(2 + γ − log 4π) < 1 =
K(0)`.  Comparing `∫ K dμ` with its atoms (`measure_compl_eq_zero_of_atoms`) forces `μ{0} = 0` and
`μ(ℝ ∖ Z) = 0`: `μ` is carried by the critical zeros.  A full-cone Weil-positive system carried by
the critical zeros is `Λ` (`eq_vonMangoldt_of_boundaryMeasure_criticalZeros`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace RHTower.WeilConditional

open WeilSpectral Zeta23

/-! ## A measure carried by a countable set up to one atom -/

/-- Let `Z` be countable with `0 ∉ Z`, and `K ≥ 0` measurable with countably many zeros.  If
`∫ K dμ ≤ Σ_{a ∈ Z} K(a) ord(a) < ∞`, `ord(a) ≤ μ{a} + μ{0}` on `Z`, `μ{a} ≤ μ{0}` off `Z`, and
`Σ_{a ∈ Z} K(a) < K(0)`, then `μ(ℝ ∖ Z) = 0`. -/
theorem measure_compl_eq_zero_of_atoms {μ : Measure ℝ} {Z : Set ℝ} (hZ : Z.Countable)
    (h0 : (0 : ℝ) ∉ Z) {K : ℝ → ℝ≥0∞} (hK : Measurable K) (hN : {r | K r = 0}.Countable)
    (ord : ℝ → ℝ≥0∞) (hfin : ∫⁻ r, K r ∂μ ≠ ⊤)
    (hEF : ∫⁻ r, K r ∂μ ≤ ∑' a : Z, K a * ord a)
    (hatom : ∀ a ∈ Z, ord a ≤ μ {a} + μ {0})
    (hoff : ∀ a ∉ Z, μ {a} ≤ μ {0})
    (hsmall : ∑' a : Z, K a < K 0) :
    μ Zᶜ = 0 := by
  have hZm : MeasurableSet Z := hZ.measurableSet
  have hsplit : (∑' a : Z, K a * μ {(a : ℝ)}) + (K 0 * μ {0} + ∫⁻ r in Zᶜ \ {0}, K r ∂μ) =
      ∫⁻ r, K r ∂μ := by
    have hinter : Zᶜ ∩ {0} = {0} := inter_eq_right.mpr (singleton_subset_iff.mpr h0)
    have h2 := lintegral_inter_add_sdiff (μ := μ) K Zᶜ (measurableSet_singleton (0 : ℝ))
    rw [hinter, lintegral_singleton] at h2
    rw [← lintegral_add_compl (μ := μ) K hZm, lintegral_countable (μ := μ) K hZ, ← h2]
  set A := ∑' a : Z, K a * μ {(a : ℝ)} with hA
  set α := μ {0} with hαdef
  set Y := ∫⁻ r in Zᶜ \ {0}, K r ∂μ with hY
  have hA_le : A ≤ ∫⁻ r, K r ∂μ := le_self_add.trans_eq hsplit
  have hAfin : A ≠ ⊤ := ne_top_of_le_ne_top hfin hA_le
  have hupper : ∑' a : Z, K a * ord a ≤ A + (∑' a : Z, K a) * α := by
    calc ∑' a : Z, K a * ord a ≤ ∑' a : Z, (K a * μ {(a : ℝ)} + K a * α) :=
          ENNReal.tsum_le_tsum fun a => by rw [← mul_add]; exact mul_le_mul_right (hatom a a.2) _
      _ = A + (∑' a : Z, K a) * α := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  have hkey : K 0 * α + Y ≤ (∑' a : Z, K a) * α :=
    (ENNReal.add_le_add_iff_left hAfin).mp ((hsplit.trans_le hEF).trans hupper)
  have hK0 : K 0 ≠ 0 := (lt_of_le_of_lt zero_le hsmall).ne'
  have hα : α = 0 := by
    by_contra hα
    have hαtop : α ≠ ⊤ := by
      intro htop
      have hle : K 0 * α ≤ ∫⁻ r, K r ∂μ :=
        (le_self_add.trans le_add_self).trans_eq hsplit
      rw [htop, ENNReal.mul_top hK0] at hle
      exact hfin (top_le_iff.mp hle)
    exact absurd (le_self_add.trans hkey) (not_le.mpr (ENNReal.mul_lt_mul_left hα hαtop hsmall))
  have hY0 : Y = 0 := by
    rw [hα, mul_zero, mul_zero, zero_add] at hkey
    exact le_antisymm hkey zero_le
  have hS : MeasurableSet (Zᶜ \ {0}) := hZm.compl.diff (measurableSet_singleton 0)
  have hae := (setLIntegral_eq_zero_iff hS hK).mp hY0
  rw [ae_iff] at hae
  have h1 : μ {r | r ∈ Zᶜ \ {0} ∧ K r ≠ 0} = 0 :=
    measure_mono_null (show {r | r ∈ Zᶜ \ {0} ∧ K r ≠ 0} ⊆ {a | ¬(a ∈ Zᶜ \ {0} → K a = 0)} from
      fun r hr h => hr.2 (h hr.1)) hae
  have h2 : μ (Zᶜ ∩ {r | K r = 0}) = 0 := by
    have hc : (Zᶜ ∩ {r | K r = 0}).Countable := hN.mono inter_subset_right
    rw [← biUnion_of_singleton (Zᶜ ∩ {r | K r = 0}), measure_biUnion_null_iff hc]
    intro a ha
    exact le_antisymm ((hoff a ha.1).trans hα.le) zero_le
  have hcover : Zᶜ ⊆ ({0} ∪ {r | r ∈ Zᶜ \ {0} ∧ K r ≠ 0}) ∪ (Zᶜ ∩ {r | K r = 0}) := by
    intro r hr
    by_cases hr0 : r = 0
    · exact Or.inl (Or.inl hr0)
    by_cases hKr : K r = 0
    · exact Or.inr ⟨hr, hKr⟩
    · exact Or.inl (Or.inr ⟨⟨hr, hr0⟩, hKr⟩)
  exact measure_mono_null hcover (measure_union_null (measure_union_null hα h1) h2)

/-! ## Zeros of an entire function -/

/-- A nonzero entire function has countably many zeros. -/
theorem countable_setOf_eq_zero_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {z₀ : ℂ} (hz₀ : F z₀ ≠ 0) : {z | F z = 0}.Countable := by
  have han : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
  rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact absurd (h (mem_univ z₀)) hz₀
  · have hd : IsDiscrete ({z | F z = 0} ∩ univ) :=
      isDiscrete_of_codiscreteWithin (by rw [compl_setOf]; exact h)
    rw [inter_univ] at hd
    have : DiscreteTopology {z | F z = 0} := isDiscrete_iff_discreteTopology.mp hd
    exact countable_coe_iff.mp (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)

/-! ## The critical ordinates -/

/-- The ordinates of the zeros of `ζ` on the critical line. -/
def criticalOrdinates : Set ℝ := {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) = 0}

theorem half_add_mul_I_re (a : ℝ) : ((1 / 2 : ℂ) + a * I).re = 1 / 2 := by simp

theorem xi_eq_zero_iff_mem_criticalOrdinates (a : ℝ) :
    xi ((1 / 2 : ℂ) + a * I) = 0 ↔ a ∈ criticalOrdinates :=
  xi_zero_iff_zeta_zero_of_mem_strip (by rw [half_add_mul_I_re]; norm_num)
    (by rw [half_add_mul_I_re]; norm_num)

theorem zero_notMem_criticalOrdinates : (0 : ℝ) ∉ criticalOrdinates := by
  rw [← xi_eq_zero_iff_mem_criticalOrdinates]
  have := xi_ne_zero_of_real (1 / 2)
  simpa using this

theorem countable_carrier : (zetaZeroConfig.carrier).Countable := by
  have hcover : zetaZeroConfig.carrier ⊆
      ⋃ n : ℕ, zetaZeroConfig.carrier ∩ {ρ | -(n : ℝ) < ρ.im ∧ ρ.im ≤ n} := by
    intro ρ hρ
    obtain ⟨n, hn⟩ := exists_nat_gt |ρ.im|
    exact mem_iUnion.mpr ⟨n, hρ, by linarith [neg_abs_le ρ.im], by linarith [le_abs_self ρ.im]⟩
  exact (countable_iUnion fun n => (zetaZeroConfig.finite_window _ _).countable).mono hcover

theorem countable_criticalOrdinates : criticalOrdinates.Countable :=
  (countable_carrier.image Complex.im).mono fun r (hr : r ∈ criticalOrdinates) =>
    (⟨((criticalZero hr : zetaZeroConfig.carrier) : ℂ), (criticalZero hr).2, by simp [criticalZero]⟩ :
      r ∈ Complex.im '' zetaZeroConfig.carrier)

/-! ## The zero configuration under RH -/

theorem re_eq_half_of_carrier (hRH : RiemannHypothesis) (ρ : zetaZeroConfig.carrier) :
    (ρ : ℂ).re = 1 / 2 := by
  obtain ⟨hζ, h0, h1⟩ : IsNontrivialZero (ρ : ℂ) := ρ.2
  refine hRH _ hζ ?_ ?_
  · rintro ⟨n, hn⟩
    have hre : (ρ : ℂ).re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · intro h
    rw [h] at h1
    simp at h1

theorem eq_half_add_im (hRH : RiemannHypothesis) (ρ : zetaZeroConfig.carrier) :
    (ρ : ℂ) = (1 / 2 : ℂ) + (((ρ : ℂ).im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [re_eq_half_of_carrier hRH ρ]

theorem gammaOf_carrier_eq (hRH : RiemannHypothesis) (ρ : zetaZeroConfig.carrier) :
    gammaOf (ρ : ℂ) = (((ρ : ℂ).im : ℝ) : ℂ) := by
  conv_lhs => rw [eq_half_add_im hRH ρ]
  exact gammaOf_half_add _

/-- Under RH, the nontrivial zeros correspond to the critical ordinates. -/
def carrierEquiv (hRH : RiemannHypothesis) : zetaZeroConfig.carrier ≃ criticalOrdinates where
  toFun ρ := ⟨(ρ : ℂ).im, by
    show riemannZeta ((1 / 2 : ℂ) + (((ρ : ℂ).im : ℝ) : ℂ) * I) = 0
    rw [← eq_half_add_im hRH ρ]
    exact (show IsNontrivialZero (ρ : ℂ) from ρ.2).1⟩
  invFun r := criticalZero r.2
  left_inv ρ := Subtype.ext (eq_half_add_im hRH ρ).symm
  right_inv r := Subtype.ext (by simp [criticalZero])

theorem mult_eq_analyticOrderNatAt (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.mult ρ = analyticOrderNatAt xi (ρ : ℂ) := by
  obtain ⟨-, h0, h1⟩ : IsNontrivialZero (ρ : ℂ) := ρ.2
  show zeroMult (ρ : ℂ) = _
  unfold zeroMult analyticOrderNatAt
  rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩]

theorem mult_criticalZero {a : ℝ} (ha : a ∈ criticalOrdinates) :
    zetaZeroConfig.mult (criticalZero ha : ℂ) = analyticOrderNatAt xi ((1 / 2 : ℂ) + a * I) :=
  mult_eq_analyticOrderNatAt (criticalZero ha)

theorem one_le_analyticOrderNatAt {a : ℝ} (ha : a ∈ criticalOrdinates) :
    1 ≤ analyticOrderNatAt xi ((1 / 2 : ℂ) + a * I) := by
  rw [← mult_criticalZero ha]
  exact zetaZeroConfig.one_le_mult _ (criticalZero ha).2

theorem analyticOrderNatAt_eq_zero {a : ℝ} (ha : a ∉ criticalOrdinates) :
    analyticOrderNatAt xi ((1 / 2 : ℂ) + a * I) = 0 := by
  have hxi : xi ((1 / 2 : ℂ) + a * I) ≠ 0 := fun h =>
    ha ((xi_eq_zero_iff_mem_criticalOrdinates a).mp h)
  have h0 : analyticOrderAt xi ((1 / 2 : ℂ) + a * I) = 0 :=
    (xi_differentiable.analyticAt _).analyticOrderAt_eq_zero.mpr hxi
  rw [analyticOrderNatAt, h0]
  rfl

/-! ## The gap test -/

/-- A smooth probability density supported in `[−17/50, 17/50]`. -/
def gapTest : ℝ → ℝ := WeilDeletion.phi (1 / 50) (by norm_num) (8 / 25) 0

abbrev gapTestC : ℝ → ℂ := fun u => (gapTest u : ℂ)

theorem gapTest_contDiff : ContDiff ℝ 2 gapTestC :=
  Complex.ofRealCLM.contDiff.comp (WeilDeletion.phi_contDiff _ _ _)

theorem gapTest_hasCompactSupport : HasCompactSupport gapTest :=
  WeilDeletion.phi_hasCompactSupport _ _ _

theorem gapTestC_hasCompactSupport : HasCompactSupport gapTestC :=
  gapTest_hasCompactSupport.comp_left Complex.ofReal_zero

theorem gapTest_eq_zero {t : ℝ} (ht : 17 / 50 < |t|) : gapTest t = 0 := by
  by_contra h
  have hmem := WeilDeletion.support_phi_subset (r := 1 / 50) (by norm_num) (w := 8 / 25)
    (by norm_num) 0 h
  norm_num at hmem
  have : |t| ≤ 17 / 50 := abs_le.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  linarith

theorem paperFT_gapTest_zero : paperFT gapTestC 0 = 1 := by
  unfold paperFT
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, gapTest,
    WeilDeletion.integral_phi (r := 1 / 50) (by norm_num) (w := 8 / 25) (by norm_num) 0]
  simp

theorem norm_paperFT_gapTest_le {γ : ℝ} (hγ : γ ≠ 0) :
    ‖paperFT gapTestC γ‖ ≤ 1 / ((8 / 25) * |γ|) := by
  have h := WeilDeletion.norm_paperFT_phi_le (r := 1 / 50) (by norm_num) (w := 8 / 25)
    (by norm_num) 0 (z := (γ : ℂ)) (by exact_mod_cast hγ)
  simp only [Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, Real.cosh_zero, one_mul,
    zero_add, pow_one, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem differentiable_paperFT_gapTest : Differentiable ℂ (paperFT gapTestC) :=
  WeilEF.differentiable_paperFT gapTest_contDiff.continuous gapTestC_hasCompactSupport

/-- The autocorrelation of the gap test vanishes at every `±log n`, `n ≥ 2`. -/
theorem atomPairing_gapTest (v : ℕ → ℝ) : atomPairing v (crossCorr gapTest gapTest) = 0 := by
  unfold atomPairing
  refine (tsum_congr fun n => ?_).trans tsum_zero
  split_ifs with hn
  · have hlog2 := Real.log_two_gt_d9
    have hlog : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hpos : 0 < Real.log n := by linarith
    rw [crossCorr_eq_zero (fun t ht => gapTest_eq_zero ht) (fun t ht => gapTest_eq_zero ht)
        (y := Real.log n) (by rw [abs_of_pos hpos]; linarith),
      crossCorr_eq_zero (fun t ht => gapTest_eq_zero ht) (fun t ht => gapTest_eq_zero ht)
        (y := -Real.log n) (by rw [abs_neg, abs_of_pos hpos]; linarith)]
    ring
  · ring

/-- **The explicit formula at the gap test**: `∫ |φ̂|² dμ_lam = Re W_ζ(φ, φ)`. -/
theorem toReal_lintegral_gapTest {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    (∫⁻ r, (specDensity gapTestC r : ℝ≥0∞) ∂boundaryMeasure hW).toReal =
      (zetaZeroConfig.W gapTestC gapTestC).re := by
  obtain ⟨-, heq⟩ := weilFullFunctional_weilTest_eq_lintegral hW gapTest_contDiff
    gapTestC_hasCompactSupport
  have h := re_weilFullFunctional_add_eq (fun n => lam n - ArithmeticFunction.vonMangoldt n)
    (F := gapTest) gapTest_contDiff gapTest_hasCompactSupport
  simp only [add_sub_cancel] at h
  rw [atomPairing_gapTest, sub_zero] at h
  rw [← h, heq, Complex.ofReal_re]

/-- The zero side of `W(f, f)` is summable for a `C²` test of compact support. -/
theorem summable_Wsummand {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ) := by
  have hkd := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨hsum, -⟩ := WeilEF.EF_lit_zetaZeroConfig _ hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc
  refine hsum.congr fun ρ => ?_
  simp only [ZeroConfig.Wsummand, hfac, mul_assoc]

/-- The zero-side summand under RH: `m_ρ |f̂(γ_ρ)|²`. -/
def zeroTerm (f : ℝ → ℂ) (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2

theorem zeroTerm_nonneg (f : ℝ → ℂ) (ρ : zetaZeroConfig.carrier) : 0 ≤ zeroTerm f ρ := by
  unfold zeroTerm; positivity

theorem Wsummand_eq_zeroTerm (hRH : RiemannHypothesis) (f : ℝ → ℂ)
    (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.Wsummand f f ρ = (zeroTerm f ρ : ℂ) := by
  rw [ZeroConfig.Wsummand, gammaOf_carrier_eq hRH ρ, Complex.conj_ofReal, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, zeroTerm]
  push_cast
  ring

theorem summable_zeroTerm (hRH : RiemannHypothesis) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : Summable (zeroTerm f) :=
  ((summable_Wsummand hf hfc).mapL Complex.reCLM).congr fun ρ => by
    simp [Wsummand_eq_zeroTerm hRH f ρ]

/-- Under RH, `Re W_ζ(f, f) = Σ_ρ m_ρ |f̂(γ_ρ)|²`. -/
theorem re_W_eq_tsum_zeroTerm (hRH : RiemannHypothesis) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : (zetaZeroConfig.W f f).re = ∑' ρ, zeroTerm f ρ := by
  rw [ZeroConfig.W, Complex.re_tsum (summable_Wsummand hf hfc)]
  exact tsum_congr fun ρ => by rw [Wsummand_eq_zeroTerm hRH f ρ, Complex.ofReal_re]

/-! ## The size of the zero sum -/

theorem five_halves_lt_log_four_mul_pi : 5 / 2 < Real.log (4 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have h := Real.exp_bound (x := 1 / 2) (by norm_num) (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  rw [abs_le] at h
  have hx : Real.exp (1 / 2) ≤ 1649 / 1000 := by linarith [h.2]
  have h5 : Real.exp (5 / 2) = Real.exp (1 / 2) ^ (5 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpi := Real.pi_gt_d2
  rw [h5]
  calc Real.exp (1 / 2) ^ (5 : ℕ) ≤ (1649 / 1000) ^ (5 : ℕ) := by
        gcongr
    _ < 4 * Real.pi := by norm_num; linarith

theorem poleSharpConstant_lt_gap : (625 / 64) * ((11 / 10) * poleSharpConstant) < 1 := by
  unfold poleSharpConstant
  have := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have := five_halves_lt_log_four_mul_pi
  linarith

/-- Under RH, `Σ_ρ m_ρ |φ̂(γ_ρ)|² < 1`. -/
theorem tsum_zeroTerm_lt_one (hRH : RiemannHypothesis) : ∑' ρ, zeroTerm gapTestC ρ < 1 := by
  set g : ℂ → ℝ := fun z => (625 / 64) * (1 / ‖gammaOf z‖ ^ (2 : ℕ)) with hg
  have hle : ∑' ρ, zeroTerm gapTestC ρ ≤ ∑' q : XiZeroCopy, g (q.1 : ℂ) := by
    refine WeilDeletion.carrier_tsum_le zetaSeam g (fun q => by positivity) ?_ (zeroTerm gapTestC)
      fun ρ => ?_
    · simp only [hg, WeilDeletion.gammaOf_eq_xiSpectralPoint]
      exact xiSpectralPoint_inv_sq_summable.mul_left _
    · have hγ := gammaOf_carrier_eq hRH ρ
      have hne : ((ρ : ℂ).im : ℝ) ≠ 0 := by
        have h := WeilDeletion.gammaOf_ne_zero_of_nontrivialZero
          (show IsNontrivialZero (ρ : ℂ) from ρ.2)
        rw [hγ] at h
        exact_mod_cast h
      have hb := norm_paperFT_gapTest_le hne
      have hn : ‖gammaOf (ρ : ℂ)‖ = |(ρ : ℂ).im| := by rw [hγ, Complex.norm_real, Real.norm_eq_abs]
      have hpos : 0 < |(ρ : ℂ).im| := abs_pos.mpr hne
      have hsq : ‖paperFT gapTestC (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2 ≤
          (625 / 64) * (1 / ‖gammaOf (ρ : ℂ)‖ ^ (2 : ℕ)) := by
        rw [hn]
        calc ‖paperFT gapTestC (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2 ≤ (1 / ((8 / 25) * |(ρ : ℂ).im|)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ = (625 / 64) * (1 / |(ρ : ℂ).im| ^ (2 : ℕ)) := by field_simp; norm_num
      unfold zeroTerm
      exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
  have hsum : ∑' q : XiZeroCopy, g (q.1 : ℂ) =
      (625 / 64) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    simp only [hg, WeilDeletion.gammaOf_eq_xiSpectralPoint]
    exact tsum_mul_left
  have hzs := WeilDeletion.tsum_inv_normSq_spectralPoint_le
  have hc := poleSharpConstant_lt_gap
  rw [hsum] at hle
  nlinarith

/-! ## The boundary measure is carried by the critical zeros -/

theorem boundaryMeasure_singleton_ne_top {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a : ℝ) :
    boundaryMeasure hW {a} ≠ ⊤ := by
  obtain ⟨hint, -⟩ := integrable_inv_one_add_sq_boundaryMeasure hW
  have hlt := hint.lintegral_lt_top
  have hle := setLIntegral_le_lintegral {a} (fun r : ℝ => ENNReal.ofReal (1 / (1 + r ^ 2)))
    (μ := boundaryMeasure hW)
  rw [lintegral_singleton] at hle
  have hpos : ENNReal.ofReal (1 / (1 + a ^ 2)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  intro htop
  rw [htop, ENNReal.mul_top hpos] at hle
  exact (lt_of_le_of_lt hle hlt).ne rfl

theorem coe_specDensity (f : ℝ → ℂ) (r : ℝ) :
    (specDensity f r : ℝ≥0∞) = ENNReal.ofReal (‖paperFT f r‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, specDensity]
  simp [enorm]

/-- **The boundary measure is carried by the critical zeros.** -/
theorem boundaryMeasure_compl_criticalOrdinates {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (D : Decomposition lam) : boundaryMeasure hW criticalOrdinatesᶜ = 0 := by
  have hRH := D.riemannHypothesis hW
  have hΛ := riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH
  set μ := boundaryMeasure hW with hμ
  set K : ℝ → ℝ≥0∞ := fun r => (specDensity gapTestC r : ℝ≥0∞) with hKdef
  set ord : ℝ → ℝ≥0∞ := fun a => (analyticOrderNatAt xi ((1 / 2 : ℂ) + a * I) : ℝ≥0∞) with hord
  have hint : Integrable gapTestC := gapTest_contDiff.continuous.integrable_of_hasCompactSupport
    gapTestC_hasCompactSupport
  have hKm : Measurable K := (measurable_specDensity hint).coe_nnreal_ennreal
  obtain ⟨hfinlt, -⟩ := weilFullFunctional_weilTest_eq_lintegral hW gapTest_contDiff
    gapTestC_hasCompactSupport
  have hfin : ∫⁻ r, K r ∂μ ≠ ⊤ := hfinlt.ne
  -- the explicit formula as an identity of atom sums
  have hEFeq : ∫⁻ r, K r ∂μ = ∑' a : criticalOrdinates, K a * ord a := by
    rw [← ENNReal.ofReal_toReal hfin, toReal_lintegral_gapTest hW,
      re_W_eq_tsum_zeroTerm hRH gapTest_contDiff gapTestC_hasCompactSupport,
      ENNReal.ofReal_tsum_of_nonneg (zeroTerm_nonneg _)
        (summable_zeroTerm hRH gapTest_contDiff gapTestC_hasCompactSupport),
      ← (carrierEquiv hRH).symm.tsum_eq]
    refine tsum_congr fun a => ?_
    simp only [hKdef, hord, coe_specDensity, zeroTerm]
    change ENNReal.ofReal ((zetaZeroConfig.mult (criticalZero a.2 : ℂ) : ℝ) *
      ‖paperFT gapTestC ((((1 / 2 : ℂ) + (a : ℝ) * I).im : ℝ) : ℂ)‖ ^ 2) = _
    rw [mult_criticalZero a.2, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      mul_comm]
    congr 3
    simp
  have hatoms : ∀ a : ℝ, |(analyticOrderNatAt xi ((1 / 2 : ℂ) + a * I) : ℝ) - μ.real {a}| ≤
      μ.real {0} := fun a => by
    have := D.abs_atom_sub_le_atom_zero hW hΛ a
    rwa [boundaryMeasure_vonMangoldt_real_singleton hΛ a] at this
  have hreal : ∀ a : ℝ, μ {a} = ENNReal.ofReal (μ.real {a}) := fun a =>
    (ENNReal.ofReal_toReal (boundaryMeasure_singleton_ne_top hW a)).symm
  have hatom : ∀ a ∈ criticalOrdinates, ord a ≤ μ {a} + μ {0} := by
    intro a _
    rw [hreal a, hreal 0, ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
    simp only [hord]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (hatoms a)).2])
  have hoff : ∀ a ∉ criticalOrdinates, μ {a} ≤ μ {0} := by
    intro a ha
    have h := hatoms a
    rw [analyticOrderNatAt_eq_zero ha, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg measureReal_nonneg] at h
    rw [hreal a, hreal 0]
    exact ENNReal.ofReal_le_ofReal h
  have hN : {r | K r = 0}.Countable := by
    refine ((countable_setOf_eq_zero_of_differentiable differentiable_paperFT_gapTest
      (z₀ := 0) (by rw [paperFT_gapTest_zero]; norm_num)).preimage
      Complex.ofReal_injective).mono fun r hr => ?_
    simp only [mem_setOf_eq, hKdef, ENNReal.coe_eq_zero, specDensity, pow_eq_zero_iff,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, nnnorm_eq_zero] at hr
    exact hr
  have hK0 : K 0 = 1 := by
    simp only [hKdef, specDensity, Complex.ofReal_zero, paperFT_gapTest_zero]
    simp
  have hsmall : ∑' a : criticalOrdinates, K a < K 0 := by
    calc ∑' a : criticalOrdinates, K a ≤ ∑' a : criticalOrdinates, K a * ord a :=
          ENNReal.tsum_le_tsum fun a => by
            conv_lhs => rw [← mul_one (K a)]
            gcongr
            simp only [hord]
            exact_mod_cast one_le_analyticOrderNatAt a.2
      _ = ENNReal.ofReal (∑' ρ, zeroTerm gapTestC ρ) := by
          rw [← hEFeq, ← ENNReal.ofReal_toReal hfin, toReal_lintegral_gapTest hW,
            re_W_eq_tsum_zeroTerm hRH gapTest_contDiff gapTestC_hasCompactSupport]
      _ < K 0 := by
          rw [hK0, ← ENNReal.ofReal_one]
          exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (tsum_zeroTerm_lt_one hRH)
  exact measure_compl_eq_zero_of_atoms countable_criticalOrdinates zero_notMem_criticalOrdinates
    hKm hN ord hfin hEFeq.le hatom hoff hsmall

/-- The trivial decomposition of `Λ` itself. -/
def vonMangoldtDecomposition : Decomposition fun n => (ArithmeticFunction.vonMangoldt n : ℝ) where
  ε := 1
  hε := Or.inl rfl
  u := fun _ => 0
  w := fun _ => 0
  u_nonneg := fun _ => le_rfl
  u_small := fun _ _ => rfl
  w_small := fun _ _ => rfl
  dec := fun n _ => by ring
  conv := fun t => ⟨0, by
    have h : ∀ N : ℕ, ∑ n ∈ Finset.range N,
        LSeries.term (fun n => (((0 : ℝ)) : ℂ)) ((1 / 2 : ℂ) + t * I) n = 0 := fun N =>
      Finset.sum_eq_zero fun n _ => by simp [LSeries.term_def]
    simp only [h]
    exact tendsto_const_nhds⟩

/-- **Under RH, `μ_Λ` lives on the critical zeros**: `μ_Λ(ℝ ∖ Z) = 0`, and its atoms are the
orders `μ_Λ{γ} = ord_{1/2+iγ} ξ` (`boundaryMeasure_vonMangoldt_real_singleton`), so
`μ_Λ = Σ_ρ m_ρ δ_{γ_ρ}`. -/
theorem boundaryMeasure_vonMangoldt_compl_criticalOrdinates
    (hΛ : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :
    boundaryMeasure hΛ criticalOrdinatesᶜ = 0 :=
  boundaryMeasure_compl_criticalOrdinates hΛ vonMangoldtDecomposition

/-! ## The theorem -/

/-- A Weil-positive system that is constant sign up to a conditionally convergent error is `Λ`
(decomposition form). -/
theorem Decomposition.eq_vonMangoldt {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (D : Decomposition lam) : ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine eq_vonMangoldt_of_boundaryMeasure_criticalZeros hW ?_
  have h := boundaryMeasure_compl_criticalOrdinates hW D
  rwa [criticalOrdinates, compl_setOf] at h

/-- **Constant sign up to a conditionally convergent error.**  If `lam` is full-cone
Weil-positive, `lam − Λ = u + w` on `n ≥ 2` with `u` of constant sign there, and the partial sums of
`Σ_{n} w(n) n^{−1/2−it}` converge for every real `t`, then `lam = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_constant_sign_add_conditional {lam u w : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hdec : ∀ n, 2 ≤ n → lam n - ArithmeticFunction.vonMangoldt n = u n + w n)
    (hsign : (∀ n, 2 ≤ n → 0 ≤ u n) ∨ ∀ n, 2 ≤ n → u n ≤ 0)
    (hconv : ∀ t : ℝ, ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      LSeries.term (fun n => (w n : ℂ)) ((1 / 2 : ℂ) + t * I) n) atTop (𝓝 L)) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set w' : ℕ → ℝ := fun n => if 2 ≤ n then w n else 0 with hw'
  have hconv' : ∀ t : ℝ, ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
      LSeries.term (fun n => (w' n : ℂ)) ((1 / 2 : ℂ) + t * I) n) atTop (𝓝 L) := by
    intro t
    obtain ⟨L, hL⟩ := hconv t
    set s : ℂ := (1 / 2 : ℂ) + t * I
    refine ⟨L - LSeries.term (fun n => (w n : ℂ)) s 1, ?_⟩
    refine (hL.sub_const _).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [Finset.sum_range_add, Finset.sum_range_add]
    have hlow : ∑ x ∈ Finset.range 2, LSeries.term (fun n => (w' n : ℂ)) s x = 0 := by
      simp [Finset.sum_range_succ, hw', LSeries.term_def]
    have hlow' : ∑ x ∈ Finset.range 2, LSeries.term (fun n => (w n : ℂ)) s x =
        LSeries.term (fun n => (w n : ℂ)) s 1 := by
      simp [Finset.sum_range_succ, LSeries.term_def]
    have hhigh : ∀ x ∈ Finset.range M, LSeries.term (fun n => (w' n : ℂ)) s (2 + x) =
        LSeries.term (fun n => (w n : ℂ)) s (2 + x) := by
      intro x _
      simp [hw']
    rw [hlow, hlow', Finset.sum_congr rfl hhigh]
    ring
  rcases hsign with hpos | hneg
  · let D : Decomposition lam :=
      { ε := 1, hε := Or.inl rfl
        u := fun n => if 2 ≤ n then u n else 0
        w := w'
        u_nonneg := fun n => by
          by_cases hn : 2 ≤ n
          · simp only [if_pos hn]; exact hpos n hn
          · simp only [if_neg hn, le_refl]
        u_small := fun n hn => if_neg (by omega)
        w_small := fun n hn => if_neg (by omega)
        dec := fun n hn => by simp only [if_pos hn, one_mul, hw']; exact hdec n hn
        conv := hconv' }
    exact D.eq_vonMangoldt hW
  · let D : Decomposition lam :=
      { ε := -1, hε := Or.inr rfl
        u := fun n => if 2 ≤ n then -u n else 0
        w := w'
        u_nonneg := fun n => by
          by_cases hn : 2 ≤ n
          · simp only [if_pos hn]; linarith [hneg n hn]
          · simp only [if_neg hn, le_refl]
        u_small := fun n hn => if_neg (by omega)
        w_small := fun n hn => if_neg (by omega)
        dec := fun n hn => by simp only [if_pos hn, hw']; linarith [hdec n hn]
        conv := hconv' }
    exact D.eq_vonMangoldt hW

end RHTower.WeilConditional
