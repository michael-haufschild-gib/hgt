import GaloisForLFunctions.RHTower.DeckPoincareRowOrbits
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral

/-!
# Fourier coefficients of deck Poincaré series

For a cusp vector `v` with `ρ(T) v = e(μ) v` and a deck field `G`, the function
`x ↦ e(-μx) ⟨v, G(x + iy)⟩` is `1`-periodic; `deckCuspCoeff μ v G y` is its integral over one period.

* `integral_inner_poincSeries_eq_deckCuspCoeff`: the unfolding of the Selberg–Poincaré series
  `P(· | y^s e(μ·), v)` against `G` in coordinates,
  `∫_𝒟 ⟨P, G⟩ = 2 ∫_0^∞ y^{s̄ - 2} e^{-2πμy} deckCuspCoeff μ v G y dy`.
* `deckCuspCoeff_poincSeries`: for a compatible pair `(h, w)`, the coefficient of `P(· | h, w)` splits into
  the rows `±(0, 1)`, which give `∫_0^1 e(-μx) h(x + iy) dx · ⟨v, w + ρ(-1)⁻¹ w⟩`, and one integral over
  the whole line for each reduced row `(c, d)`, `0 ≤ d < |c|`: the translates `(c, d + kc)` of a
  reduced row tile the line (`coeffTerm_rowShift`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry
open _root_.RHTower (rowPlus rowMinus rowPlus_ne_rowMinus first_zero_iff)

noncomputable section

variable {N : ℕ}

/-! ## Horizontal lines -/

/-- The point `x + iy` of `ℍ`. -/
def hLine {y : ℝ} (hy : 0 < y) (x : ℝ) : ℍ := ⟨⟨x, y⟩, hy⟩

theorem ofComplex_eq_hLine {y : ℝ} (hy : 0 < y) (x : ℝ) :
    (ofComplex (⟨x, y⟩ : ℂ) : ℍ) = hLine hy x :=
  ofComplex_apply_of_im_pos (z := ⟨x, y⟩) hy

theorem hLine_im {y : ℝ} (hy : 0 < y) (x : ℝ) : (hLine hy x).im = y := rfl

theorem coe_hLine {y : ℝ} (hy : 0 < y) (x : ℝ) :
    (hLine hy x : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [hLine]

theorem continuous_hLine {y : ℝ} (hy : 0 < y) : Continuous (hLine hy) := by
  refine UpperHalfPlane.isOpenEmbedding_coe.isInducing.continuous_iff.2 ?_
  refine (Complex.continuous_ofReal.add (continuous_const (y := ((y : ℂ) * Complex.I)))).congr
    fun x => ?_
  exact (coe_hLine hy x).symm

theorem T_zpow_smul_hLine {y : ℝ} (hy : 0 < y) (k : ℤ) (x : ℝ) :
    ModularGroup.T ^ k • hLine hy x = hLine hy (x + k) := by
  rw [modular_T_zpow_smul]
  apply UpperHalfPlane.ext
  rw [coe_vadd, coe_hLine, coe_hLine]
  push_cast
  ring

/-! ## The coefficient -/

/-- The additive character `e(-μx)`. -/
def cuspChar (μ x : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * μ * x))

theorem norm_cuspChar (μ x : ℝ) : ‖cuspChar μ x‖ = 1 := by
  rw [cuspChar, Complex.norm_exp]
  simp

theorem continuous_cuspChar (μ : ℝ) : Continuous (cuspChar μ) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg

theorem cuspChar_add (μ x : ℝ) (k : ℤ) :
    cuspChar μ (x + k) = cuspChar μ x * Complex.exp (-(2 * Real.pi * Complex.I * μ * k)) := by
  rw [cuspChar, cuspChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The `μ`-th Fourier coefficient at height `y` of `x ↦ ⟨v, G(x + iy)⟩` over one period. -/
def deckCuspCoeff (μ : ℝ) (v : DeckSpace N) (G : ℍ → DeckSpace N) (y : ℝ) : ℂ :=
  ∫ x in Ico (0 : ℝ) 1, cuspChar μ x * ⟪v, G (ofComplex ⟨x, y⟩)⟫_ℂ

/-! ## Unfolding in coordinates -/

theorem conj_poincProfile_hLine (s : ℂ) (μ : ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    conj (poincProfile s μ (hLine hy x)) =
      (y : ℂ) ^ (conj s) * (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) * cuspChar μ x := by
  have harg : (y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]
    exact Real.pi_pos.ne
  have h1 : conj ((y : ℂ) ^ s) = (y : ℂ) ^ (conj s) := by
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  have h2 : conj (Complex.exp (2 * Real.pi * Complex.I * μ * (hLine hy x : ℂ))) =
      (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) * cuspChar μ x := by
    rw [← Complex.exp_conj, cuspChar, Complex.ofReal_exp, ← Complex.exp_add, coe_hLine]
    congr 1
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    linear_combination (2 * Real.pi * μ * y : ℂ) * Complex.I_sq
  rw [poincProfile, map_mul, hLine_im, h1, h2]
  ring

theorem integrableOn_poincIntegrand_strip_profile {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 < μ)
    {v : DeckSpace N} (hv : IsCuspEigen μ v) {G : ℍ → DeckSpace N} (hGc : Continuous G)
    (hGe : deckEquivariant N G) (hGL : MemLp G 2 cellMeasure) :
    IntegrableOn (poincIntegrand (poincProfile s μ) v G) modularStrip volume :=
  integrableOn_poincIntegrand_strip (cuspCompatible_poincProfile s hv) (continuous_poincProfile s μ)
    hGc hGe hGL (summable_norm_poincProfile hs hμ.le) (memLp_tsum_norm_poincProfile hs hμ)

/-- **Unfolding in coordinates**:
`∫_𝒟 ⟨P(· | y^s e(μ·), v), G⟩ = 2 ∫_0^∞ y^{-2} y^{s̄} e^{-2πμy} deckCuspCoeff μ v G y dy`. -/
theorem integral_inner_poincSeries_eq_deckCuspCoeff {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 < μ)
    {v : DeckSpace N} (hv : IsCuspEigen μ v) {G : ℍ → DeckSpace N} (hGc : Continuous G)
    (hGe : deckEquivariant N G) (hGL : MemLp G 2 cellMeasure) :
    ∫ z in fd, ⟪poincSeries (poincProfile s μ) v z, G z⟫_ℂ =
      2 * ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ •
        ((y : ℂ) ^ (conj s) * (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) * deckCuspCoeff μ v G y) := by
  rw [integral_inner_poincSeries_profile hs hμ hv hGc hGe hGL,
    setIntegral_modularStrip_eq_iterated _
      (integrableOn_poincIntegrand_strip_profile hs hμ hv hGc hGe hGL)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  congr 1
  rw [deckCuspCoeff, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  rw [ofComplex_eq_hLine hy, poincIntegrand, conj_poincProfile_hLine]
  ring

/-! ## The terms of the coefficient integrand -/

/-- The `p`-th term `e(-μx) ⟨v, h(M_p(x + iy)) ρ(M_p)⁻¹ w⟩` of the coefficient integrand. -/
def coeffTerm (μ : ℝ) (v : DeckSpace N) (h : ℍ → ℂ) (w : DeckSpace N) {y : ℝ} (hy : 0 < y)
    (p : gammaSet 1 1 0) (x : ℝ) : ℂ :=
  cuspChar μ x * ⟪v, poincTerm h w p (hLine hy x)⟫_ℂ

variable {μ : ℝ} {v : DeckSpace N} {h : ℍ → ℂ} {w : DeckSpace N} {y : ℝ} (hy : 0 < y)

include hy in
theorem norm_coeffTerm_le (p : gammaSet 1 1 0) (x : ℝ) :
    ‖coeffTerm μ v h w hy p x‖ ≤ ‖v‖ * ‖w‖ * ‖h (gammaSetMatrix p • hLine hy x)‖ := by
  rw [coeffTerm, norm_mul, norm_cuspChar, one_mul]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [norm_poincTerm, mul_comm ‖h _‖, ← mul_assoc]

include hy in
theorem continuous_coeffTerm (hhc : Continuous h) (p : gammaSet 1 1 0) :
    Continuous (coeffTerm μ v h w hy p) :=
  (continuous_cuspChar μ).mul (continuous_const.inner
    ((hhc.comp ((continuous_modular_smul _).comp (continuous_hLine hy))).smul continuous_const))

include hy in
/-- Translating a row by `T^k` translates the coefficient integrand by `k`. -/
theorem coeffTerm_rowShift (hc : CuspCompatible h w) (hv : IsCuspEigen μ v) (k : ℤ)
    (p : gammaSet 1 1 0) (x : ℝ) :
    coeffTerm μ v h w hy (rowShift k p) x = coeffTerm μ v h w hy p (x + k) := by
  rw [coeffTerm, coeffTerm, poincTerm_rowShift hc, T_zpow_smul_hLine,
    ← LinearIsometryEquiv.inner_map_eq_flip, deckRho_T_zpow_eigen hv, inner_smul_left,
    ← Complex.exp_conj, cuspChar_add]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
  rw [show (2 * (Real.pi : ℂ) * -Complex.I * μ * k) = -(2 * Real.pi * Complex.I * μ * k) by ring]
  ring

theorem poincTerm_of_eq_T_zpow_mul (hc : CuspCompatible h w) {p : gammaSet 1 1 0} {n : ℤ}
    {B : SL(2, ℤ)} (hp : gammaSetMatrix p = ModularGroup.T ^ n * B) (z : ℍ) :
    poincTerm h w p z = h (B • z) • (deckRho N B).symm w := by
  have hsymm : (deckRho N (ModularGroup.T ^ n * B)).symm w =
      (deckRho N B).symm ((deckRho N (ModularGroup.T ^ n)).symm w) := by
    refine symm_eq_of_apply_eq ?_
    rw [deckRho_mul, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [poincTerm, hp, hsymm, mul_smul, ← map_smul, hc n (B • z), map_smul]

theorem poincTerm_rowPlus (hc : CuspCompatible h w) (z : ℍ) : poincTerm h w rowPlus z = h z • w := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix rowPlus) 1
    (by simp [rowPlus]) (by simp [rowPlus])
  rw [poincTerm_of_eq_T_zpow_mul hc hn, one_smul]
  congr 1
  exact (deckRho N 1).symm_apply_eq.2 (deckRho_one w).symm

theorem poincTerm_rowMinus (hc : CuspCompatible h w) (z : ℍ) :
    poincTerm h w rowMinus z = h z • (deckRho N (-1)).symm w := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix rowMinus) (-1)
    (by simp [rowMinus]) (by simp [rowMinus])
  rw [poincTerm_of_eq_T_zpow_mul hc hn, SL_neg_smul, one_smul]

/-! ## Summability -/

include hy in
theorem lintegral_tsum_coeffTerm_ne_top (hhc : Continuous h)
    (hsum : ∀ z, Summable fun p : gammaSet 1 1 0 => ‖h (gammaSetMatrix p • z)‖)
    (hH : Continuous fun z => ∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) :
    ∑' p, ∫⁻ x in Ico (0 : ℝ) 1, ‖coeffTerm μ v h w hy p x‖ₑ ≠ ⊤ := by
  set F : ℝ → ℝ := fun x => ‖v‖ * ‖w‖ * ∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • hLine hy x)‖
  have hFc : Continuous F := continuous_const.mul (hH.comp (continuous_hLine hy))
  have hFi : IntegrableOn F (Ico (0 : ℝ) 1) volume :=
    (hFc.continuousOn.integrableOn_Icc (a := 0) (b := 1)).mono_set Ico_subset_Icc_self
  rw [← lintegral_tsum fun p => (continuous_coeffTerm hy hhc p).enorm.aemeasurable]
  refine (lt_of_le_of_lt (lintegral_mono fun x => ?_) hFi.hasFiniteIntegral).ne
  have hs : Summable fun p => ‖coeffTerm μ v h w hy p x‖ :=
    ((hsum (hLine hy x)).mul_left (‖v‖ * ‖w‖)).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun p => norm_coeffTerm_le hy p x
  have hF0 : 0 ≤ F x :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (tsum_nonneg fun _ => norm_nonneg _)
  calc ∑' p, ‖coeffTerm μ v h w hy p x‖ₑ = ENNReal.ofReal (∑' p, ‖coeffTerm μ v h w hy p x‖) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
        simp only [ofReal_norm]
    _ ≤ ENNReal.ofReal (F x) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show F x = ∑' p : gammaSet 1 1 0, ‖v‖ * ‖w‖ * ‖h (gammaSetMatrix p • hLine hy x)‖ from
          tsum_mul_left.symm]
        exact hs.tsum_le_tsum (fun p => norm_coeffTerm_le hy p x) ((hsum _).mul_left _)
    _ = ‖F x‖ₑ := by rw [← ofReal_norm, Real.norm_of_nonneg hF0]

include hy in
theorem summable_integral_norm_coeffTerm (hhc : Continuous h)
    (hsum : ∀ z, Summable fun p : gammaSet 1 1 0 => ‖h (gammaSetMatrix p • z)‖)
    (hH : Continuous fun z => ∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) :
    Summable fun p : gammaSet 1 1 0 => ∫ x in Ico (0 : ℝ) 1, ‖coeffTerm μ v h w hy p x‖ := by
  refine (ENNReal.summable_toReal (lintegral_tsum_coeffTerm_ne_top (μ := μ) (v := v) (w := w) hy hhc hsum hH)).congr fun p => ?_
  rw [integral_norm_eq_lintegral_enorm (continuous_coeffTerm hy hhc p).aestronglyMeasurable]

include hy in
theorem deckCuspCoeff_poincSeries_eq_tsum (hhc : Continuous h)
    (hsum : ∀ z, Summable fun p : gammaSet 1 1 0 => ‖h (gammaSetMatrix p • z)‖)
    (hH : Continuous fun z => ∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) :
    deckCuspCoeff μ v (poincSeries h w) y =
      ∑' p, ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy p x := by
  rw [← integral_tsum (fun p => (continuous_coeffTerm hy hhc p).aestronglyMeasurable)
    (lintegral_tsum_coeffTerm_ne_top (μ := μ) (v := v) (w := w) hy hhc hsum hH), deckCuspCoeff]
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  have hs : Summable fun p => poincTerm h w p (hLine hy x) :=
    Summable.of_norm (((hsum (hLine hy x)).mul_right ‖w‖).congr fun p =>
      (norm_poincTerm h w p _).symm)
  rw [ofComplex_eq_hLine hy, poincSeries, ← innerSL_apply_apply, (innerSL ℂ v).map_tsum hs,
    ← tsum_mul_left]
  rfl

/-- One period of a translate is the translated period. -/
theorem setIntegral_Ico_comp_add_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (k : ℤ) :
    ∫ x in Ico (0 : ℝ) 1, g (x + k) = ∫ x in Ico (k : ℝ) (k + 1), g x := by
  rw [integral_Ico_eq_integral_Ioc, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_add_right, zero_add, add_comm (1 : ℝ)]

/-- The periods tile the line. -/
theorem hasSum_setIntegral_Ico_int {g : ℝ → ℂ} (hg : Continuous g)
    (hs : Summable fun k : ℤ => ∫ x in Ico (k : ℝ) (k + 1), ‖g x‖) :
    Integrable g ∧ HasSum (fun k : ℤ => ∫ x in Ico (k : ℝ) (k + 1), g x) (∫ x, g x) := by
  have hint : IntegrableOn g (⋃ k : ℤ, Ico (k : ℝ) (k + 1)) volume :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun k => (hg.continuousOn.integrableOn_Icc).mono_set Ico_subset_Icc_self) hs
  have hsum := hasSum_integral_iUnion (fun k : ℤ => measurableSet_Ico)
    (pairwise_disjoint_Ico_intCast ℝ) hint
  rw [iUnion_Ico_intCast ℝ, setIntegral_univ] at hsum
  rw [iUnion_Ico_intCast ℝ, integrableOn_univ] at hint
  exact ⟨hint, hsum⟩

/-- The rows with `c = 0` contribute `∫_0^1 e(-μx) h(x + iy) dx · ⟨v, w + ρ(-1)⁻¹ w⟩`. -/
theorem tsum_indicator_zeroRow (hc : CuspCompatible h w) (hhc : Continuous h) :
    ∑' p : gammaSet 1 1 0, {p : gammaSet 1 1 0 | p.1 0 = 0}.indicator
        (fun p => ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy p x) p =
      (∫ x in Ico (0 : ℝ) 1, cuspChar μ x * h (hLine hy x)) *
        ⟪v, w + (deckRho N (-1)).symm w⟫_ℂ := by
  classical
  rw [tsum_eq_sum (s := {rowPlus, rowMinus}) fun p hp => Set.indicator_of_notMem (fun hp0 => hp ?_) _,
    Finset.sum_pair rowPlus_ne_rowMinus, Set.indicator_of_mem (by simp [rowPlus]),
    Set.indicator_of_mem (by simp [rowMinus]), ← integral_add, ← integral_mul_const]
  · refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
    simp only [coeffTerm, poincTerm_rowPlus hc, poincTerm_rowMinus hc, inner_smul_right, inner_add_right]
    ring
  · exact ((continuous_coeffTerm hy hhc rowPlus).continuousOn.integrableOn_Icc).mono_set
      Ico_subset_Icc_self
  · exact ((continuous_coeffTerm hy hhc rowMinus).continuousOn.integrableOn_Icc).mono_set
      Ico_subset_Icc_self
  · rcases (first_zero_iff p).1 hp0 with h1 | h1 <;> simp [h1]

include hy in
/-- Along the translates `(c, d + kc)` of a reduced row, the one-period integrals sum to the integral
over the whole line, which converges absolutely. -/
theorem integrable_coeffTerm_and_hasSum (hc : CuspCompatible h w) (hv : IsCuspEigen μ v)
    (hhc : Continuous h)
    (hsum : ∀ z, Summable fun p : gammaSet 1 1 0 => ‖h (gammaSetMatrix p • z)‖)
    (hH : Continuous fun z => ∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) (r : ReducedRow) :
    Integrable (coeffTerm μ v h w hy r.1) ∧
      HasSum (fun k : ℤ => ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy (rowShift k r.1) x)
        (∫ x, coeffTerm μ v h w hy r.1 x) := by
  have hb := summable_integral_norm_coeffTerm (μ := μ) (v := v) (w := w) hy hhc hsum hH
  have h1 : Summable fun q : NonzeroRow => ∫ x in Ico (0 : ℝ) 1, ‖coeffTerm μ v h w hy q.1 x‖ :=
    hb.subtype {p : gammaSet 1 1 0 | p.1 0 ≠ 0}
  have h2 : Summable fun rk : ReducedRow × ℤ =>
      ∫ x in Ico (0 : ℝ) 1, ‖coeffTerm μ v h w hy (rowShift rk.2 rk.1.1) x‖ :=
    (reducedRowShiftEquiv.summable_iff
      (f := fun q : NonzeroRow => ∫ x in Ico (0 : ℝ) 1, ‖coeffTerm μ v h w hy q.1 x‖)).2 h1
  have hnorm : ∀ k : ℤ, ∫ x in Ico (0 : ℝ) 1, ‖coeffTerm μ v h w hy (rowShift k r.1) x‖ =
      ∫ x in Ico (k : ℝ) (k + 1), ‖coeffTerm μ v h w hy r.1 x‖ := fun k => by
    simp_rw [coeffTerm_rowShift hy hc hv]
    exact setIntegral_Ico_comp_add_int (fun x => ‖coeffTerm μ v h w hy r.1 x‖) k
  have hshift : (fun k : ℤ => ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy (rowShift k r.1) x) =
      fun k : ℤ => ∫ x in Ico (k : ℝ) (k + 1), coeffTerm μ v h w hy r.1 x := funext fun k => by
    simp_rw [coeffTerm_rowShift hy hc hv]
    exact setIntegral_Ico_comp_add_int (coeffTerm μ v h w hy r.1) k
  obtain ⟨hint, hs⟩ := hasSum_setIntegral_Ico_int (continuous_coeffTerm hy hhc r.1)
    ((h2.prod_factor r).congr hnorm)
  rw [hshift]
  exact ⟨hint, hs⟩

include hy in
/-- **Fourier coefficient of a deck Poincaré series.**  For a compatible pair `(h, w)` and a cusp
vector `v` of frequency `μ`,
`deckCuspCoeff μ v P(· | h, w) y = ∫_0^1 e(-μx) h(x + iy) dx · ⟨v, w + ρ(-1)⁻¹ w⟩ +
  Σ_{(c,d) reduced} ∫_ℝ e(-μx) ⟨v, h(M_{c,d}(x + iy)) ρ(M_{c,d})⁻¹ w⟩ dx`. -/
theorem deckCuspCoeff_poincSeries (hc : CuspCompatible h w) (hv : IsCuspEigen μ v) (hhc : Continuous h)
    (hsum : ∀ z, Summable fun p : gammaSet 1 1 0 => ‖h (gammaSetMatrix p • z)‖)
    (hH : Continuous fun z => ∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) :
    deckCuspCoeff μ v (poincSeries h w) y =
      (∫ x in Ico (0 : ℝ) 1, cuspChar μ x * h (hLine hy x)) * ⟪v, w + (deckRho N (-1)).symm w⟫_ℂ +
        ∑' r : ReducedRow, ∫ x, coeffTerm μ v h w hy r.1 x := by
  have hb := summable_integral_norm_coeffTerm (μ := μ) (v := v) (w := w) hy hhc hsum hH
  have ha : Summable fun p : gammaSet 1 1 0 => ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy p x :=
    Summable.of_norm (hb.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun _ => norm_integral_le_integral_norm _)
  have hsplit : ∑' p : gammaSet 1 1 0, ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy p x =
      ∑' p : gammaSet 1 1 0, {p : gammaSet 1 1 0 | p.1 0 = 0}.indicator
          (fun p => ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy p x) p +
        ∑' p : gammaSet 1 1 0, {p : gammaSet 1 1 0 | p.1 0 = 0}ᶜ.indicator
          (fun p => ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy p x) p := by
    rw [← (ha.indicator _).tsum_add (ha.indicator _)]
    exact tsum_congr fun p => (Set.indicator_self_add_compl_apply {p : gammaSet 1 1 0 | p.1 0 = 0}
      (fun p => ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy p x) p).symm
  rw [deckCuspCoeff_poincSeries_eq_tsum hy hhc hsum hH, hsplit, tsum_indicator_zeroRow hy hc hhc]
  congr 1
  rw [← tsum_subtype]
  change ∑' q : NonzeroRow, ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy q.1 x = _
  have hprod : Summable fun rk : ReducedRow × ℤ =>
      ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy (rowShift rk.2 rk.1.1) x :=
    (reducedRowShiftEquiv.summable_iff
      (f := fun q : NonzeroRow => ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy q.1 x)).2
      (ha.subtype {p : gammaSet 1 1 0 | p.1 0 ≠ 0})
  refine (reducedRowShiftEquiv.tsum_eq
    (fun q : NonzeroRow => ∫ x in Ico (0 : ℝ) 1, coeffTerm μ v h w hy q.1 x)).symm.trans ?_
  refine hprod.tsum_prod.trans ?_
  exact tsum_congr fun r => (integrable_coeffTerm_and_hasSum hy hc hv hhc hsum hH r).2.tsum_eq

end

end GaloisForLFunctions.RHTower.DeckPointPair
