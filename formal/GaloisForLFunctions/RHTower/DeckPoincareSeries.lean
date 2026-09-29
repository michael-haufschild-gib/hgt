import GaloisForLFunctions.RHTower.DeckEisensteinSpectralIsometry
import GaloisForLFunctions.HTGeometry.ModularStripLIntegralUnfolding

/-!
# Deck Poincaré series

For a profile `h : ℍ → ℂ` and `v ∈ ℂ^Deck` put
`P(z | h, v) = Σ_{(c,d) coprime} h(M_{c,d} z) ρ(M_{c,d})⁻¹ v` (`poincSeries`).

* If `(h, v)` is compatible with the stabilizer of `∞`, `h(T^n w) ρ(T^n)⁻¹ v = h(w) v`
  (`CuspCompatible`), the series is deck equivariant (`poincSeries_smul`).
* **Unfolding** (`integral_inner_poincSeries`): for continuous equivariant `G ∈ L²(𝒟)` and a square
  integrable majorant `z ↦ Σ |h(M_{c,d} z)|`,
  `∫_𝒟 ⟨P(·|h,v), G⟩ = 2 ∫_{0 ≤ Re w < 1} conj h(w) ⟨v, G(w)⟩`.
  Integrability on the strip is obtained from the unfolding of `|·|` (no hypothesis on the strip).
* The Selberg profile `h(w) = (Im w)^s e(μ w)` (`poincProfile`), with `ρ(T) v = e(μ) v`, gives the
  deck form of the Poincaré series `U_{𝔞m}(z; s)` at all cusps at once; for `Re s > 1`, `μ > 0` the
  series is continuous and square integrable, with majorant `C y^{1-σ} + 2 y^σ e^{-2πμy}` on `𝒟`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries Complex
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## Local uniform bounds by the row heights -/

theorem rowHeight_eq_norm (p : gammaSet 1 1 0) (z : ℍ) :
    RHTower.rowHeight p z = z.im / ‖((p.1 0 : ℤ) : ℂ) * (z : ℂ) + ((p.1 1 : ℤ) : ℂ)‖ ^ 2 := by
  rw [RHTower.rowHeight, im_gammaSetMatrix_smul, Complex.normSq_eq_norm_sq]

/-- **Local M-test.** A series of continuous terms dominated by `K · Im(M_{c,d} z)^σ`, `σ > 1`,
has a continuous sum. -/
theorem continuous_tsum_of_rowHeight_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : gammaSet 1 1 0 → ℍ → E} (hF : ∀ p, Continuous (F p)) {σ K : ℝ} (hσ : 1 < σ) (hK : 0 ≤ K)
    (hb : ∀ p z, ‖F p z‖ ≤ K * RHTower.rowHeight p z ^ σ) :
    Continuous fun z => ∑' p, F p z := by
  rw [continuous_iff_continuousAt]
  intro z₀
  set A := |z₀.re| + 1
  set B := z₀.im / 2
  set T := 2 * z₀.im
  have hB : 0 < B := by have := z₀.im_pos; simp only [B]; positivity
  set U : Set ℍ := {z | |z.re| < A ∧ B < z.im ∧ z.im < T}
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const).inter
      ((isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const))
  have hz₀ : z₀ ∈ U := by
    have := z₀.im_pos
    exact ⟨by simp only [A]; linarith, by simp only [B]; linarith, by simp only [T]; linarith⟩
  set r₀ := r ⟨⟨A, B⟩, hB⟩
  have hr₀ : 0 < r₀ := r_pos _
  have h2σ : 2 < 2 * σ := by linarith
  set u : gammaSet 1 1 0 → ℝ := fun p => K * (T ^ σ * ((r₀ * ‖p.1‖) ^ (-(2 * σ))))
  have hu : Summable u := by
    have h := ((summable_one_div_norm_rpow h2σ).comp_injective
      (Subtype.val_injective : Function.Injective (Subtype.val : gammaSet 1 1 0 → Fin 2 → ℤ))).mul_left
      (K * (T ^ σ * r₀ ^ (-(2 * σ))))
    refine h.congr fun p => ?_
    simp only [u, Function.comp_apply]
    rw [Real.mul_rpow hr₀.le (norm_nonneg _)]
    ring
  have hcont : ContinuousOn (fun z => ∑' p, F p z) U := by
    refine continuousOn_tsum (fun p => (hF p).continuousOn) hu fun p z hz => ?_
    refine (hb p z).trans (mul_le_mul_of_nonneg_left ?_ hK)
    have hstrip : z ∈ UpperHalfPlane.verticalStrip A B := ⟨hz.1.le, hz.2.1.le⟩
    have hrz : r₀ ≤ r z := r_lower_bound_on_verticalStrip z hB hstrip
    have hx : p.1 ≠ 0 := gammaSet_val_ne_zero p
    have hmul := r_mul_max_le z hx
    have hnx : 0 < ‖p.1‖ := norm_pos_iff.mpr hx
    set D := ‖((p.1 0 : ℤ) : ℂ) * (z : ℂ) + ((p.1 1 : ℤ) : ℂ)‖
    have hD : r₀ * ‖p.1‖ ≤ D := (mul_le_mul_of_nonneg_right hrz hnx.le).trans hmul
    have hpos : 0 < r₀ * ‖p.1‖ := by positivity
    have hDpos : 0 < D := hpos.trans_le hD
    have hrow : RHTower.rowHeight p z ^ σ = z.im ^ σ * D ^ (-(2 * σ)) := by
      rw [rowHeight_eq_norm, Real.div_rpow z.im_pos.le (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hDpos.le, Real.rpow_neg hDpos.le, div_eq_mul_inv]
      norm_num
    rw [hrow]
    exact mul_le_mul (Real.rpow_le_rpow z.im_pos.le hz.2.2.le (by linarith))
      (Real.rpow_le_rpow_of_nonpos hpos hD (by linarith)) (by positivity) (by positivity)
  exact hcont.continuousAt (hUo.mem_nhds hz₀)

/-! ## The series -/

/-- One term `h(M_{c,d} z) ρ(M_{c,d})⁻¹ v`. -/
def poincTerm (h : ℍ → ℂ) (v : DeckSpace N) (p : gammaSet 1 1 0) (z : ℍ) : DeckSpace N :=
  h (gammaSetMatrix p • z) • (deckRho N (gammaSetMatrix p)).symm v

/-- **The deck Poincaré series** `P(z | h, v) = Σ_{(c,d)} h(M_{c,d} z) ρ(M_{c,d})⁻¹ v`. -/
def poincSeries (h : ℍ → ℂ) (v : DeckSpace N) (z : ℍ) : DeckSpace N :=
  ∑' p : gammaSet 1 1 0, poincTerm h v p z

/-- Compatibility of a profile and a vector with the stabilizer `⟨T⟩` of `∞`. -/
def CuspCompatible (h : ℍ → ℂ) (v : DeckSpace N) : Prop :=
  ∀ (n : ℤ) (w : ℍ), h (ModularGroup.T ^ n • w) • (deckRho N (ModularGroup.T ^ n)).symm v = h w • v

theorem norm_poincTerm (h : ℍ → ℂ) (v : DeckSpace N) (p : gammaSet 1 1 0) (z : ℍ) :
    ‖poincTerm h v p z‖ = ‖h (gammaSetMatrix p • z)‖ * ‖v‖ := by
  rw [poincTerm, norm_smul, LinearIsometryEquiv.norm_map]

theorem poincTerm_smul {h : ℍ → ℂ} {v : DeckSpace N} (hc : CuspCompatible h v) (A : SL(2, ℤ))
    (p : gammaSet 1 1 0) (z : ℍ) :
    poincTerm h v p (A • z) = deckRho N A (poincTerm h v (gammaSetSelfEquiv A p) z) := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix p * A)
    (gammaSetMatrix (gammaSetSelfEquiv A p))
    (by rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_zero, gammaSetSelfEquiv_apply_val])
    (by rw [gammaSetMatrix_mul_apply_one, gammaSetMatrix_apply_one_one, gammaSetSelfEquiv_apply_val])
  set M := gammaSetMatrix p
  set M' := gammaSetMatrix (gammaSetSelfEquiv A p)
  have hz : M • A • z = ModularGroup.T ^ n • (M' • z) := by rw [← mul_smul, hn, mul_smul]
  have hvec : (deckRho N M).symm v =
      deckRho N A ((deckRho N M').symm ((deckRho N (ModularGroup.T ^ n)).symm v)) := by
    refine symm_eq_of_apply_eq ?_
    rw [← deckRho_mul, hn, deckRho_mul, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply]
  have hkey := hc n (M' • z)
  calc poincTerm h v p (A • z)
      = h (ModularGroup.T ^ n • (M' • z)) •
          deckRho N A ((deckRho N M').symm ((deckRho N (ModularGroup.T ^ n)).symm v)) := by
        rw [poincTerm, hz, hvec]
    _ = deckRho N A ((deckRho N M').symm (h (ModularGroup.T ^ n • (M' • z)) •
          (deckRho N (ModularGroup.T ^ n)).symm v)) := by rw [map_smul, map_smul]
    _ = deckRho N A (poincTerm h v (gammaSetSelfEquiv A p) z) := by
        rw [hkey, map_smul]
        rfl

/-- **Deck equivariance** `P(Az) = ρ(A) P(z)`. -/
theorem poincSeries_smul {h : ℍ → ℂ} {v : DeckSpace N} (hc : CuspCompatible h v) (A : SL(2, ℤ))
    (z : ℍ) : poincSeries h v (A • z) = deckRho N A (poincSeries h v z) := by
  unfold poincSeries
  simp_rw [poincTerm_smul hc A _ z]
  rw [(gammaSetSelfEquiv A).tsum_eq (fun p => deckRho N A (poincTerm h v p z))]
  exact ((deckRho N A).toContinuousLinearEquiv.map_tsum).symm

theorem deckEquivariant_poincSeries {h : ℍ → ℂ} {v : DeckSpace N} (hc : CuspCompatible h v) :
    deckEquivariant N (poincSeries h v) := fun A z => poincSeries_smul hc A z

/-! ## Unfolding -/

theorem inner_tsum_left {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {f : ι → E} (hf : Summable f) (y : E) :
    ⟪∑' i, f i, y⟫_ℂ = ∑' i, ⟪f i, y⟫_ℂ := by
  calc ⟪∑' i, f i, y⟫_ℂ = conj ⟪y, ∑' i, f i⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (∑' i, ⟪y, f i⟫_ℂ) := by
        rw [← innerSL_apply_apply, ContinuousLinearMap.map_tsum _ hf]
        rfl
    _ = ∑' i, ⟪f i, y⟫_ℂ := by
        rw [Complex.conj_tsum]
        simp only [inner_conj_symm]

/-- The unfolded integrand `conj h(w) ⟨v, G(w)⟩`. -/
def poincIntegrand (h : ℍ → ℂ) (v : DeckSpace N) (G : ℍ → DeckSpace N) (w : ℍ) : ℂ :=
  conj (h w) * ⟪v, G w⟫_ℂ

theorem inner_poincTerm {G : ℍ → DeckSpace N} (hGe : deckEquivariant N G) (h : ℍ → ℂ)
    (v : DeckSpace N) (p : gammaSet 1 1 0) (z : ℍ) :
    ⟪poincTerm h v p z, G z⟫_ℂ = poincIntegrand h v G (gammaSetMatrix p • z) := by
  rw [poincTerm, inner_smul_left, poincIntegrand, hGe]
  congr 1
  rw [← (deckRho N (gammaSetMatrix p)).inner_map_map ((deckRho N (gammaSetMatrix p)).symm v) (G z),
    LinearIsometryEquiv.apply_symm_apply]

theorem poincIntegrand_T_zpow {h : ℍ → ℂ} {v : DeckSpace N} (hc : CuspCompatible h v)
    {G : ℍ → DeckSpace N} (hGe : deckEquivariant N G) (n : ℤ) (w : ℍ) :
    poincIntegrand h v G (ModularGroup.T ^ n • w) = poincIntegrand h v G w := by
  rw [poincIntegrand, poincIntegrand, hGe, ← inner_smul_left, ← inner_smul_left, ← hc n w]
  rw [inner_smul_left, inner_smul_left]
  congr 1
  rw [← (deckRho N (ModularGroup.T ^ n)).inner_map_map ((deckRho N (ModularGroup.T ^ n)).symm v) (G w),
    LinearIsometryEquiv.apply_symm_apply]

/-- **Unfolding of the deck Poincaré series** against square-integrable equivariant fields. -/
theorem integral_inner_poincSeries {h : ℍ → ℂ} {v : DeckSpace N} (hc : CuspCompatible h v)
    (hhc : Continuous h) {G : ℍ → DeckSpace N} (hGc : Continuous G) (hGe : deckEquivariant N G)
    (hGL : MemLp G 2 cellMeasure)
    (hsum : ∀ z, Summable fun p : gammaSet 1 1 0 => ‖h (gammaSetMatrix p • z)‖)
    (hH : MemLp (fun z => ∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) 2 cellMeasure) :
    ∫ z in fd, ⟪poincSeries h v z, G z⟫_ℂ =
      2 * ∫ w in modularStrip, poincIntegrand h v G w := by
  set f := poincIntegrand h v G
  have hT : ∀ (n : ℤ) (w : ℍ), f (ModularGroup.T ^ n • w) = f w := poincIntegrand_T_zpow hc hGe
  have hfc : Continuous f :=
    (Complex.continuous_conj.comp hhc).mul (continuous_const.inner hGc)
  -- integrability on the strip from the unfolding of `‖f‖`
  have hstrip : IntegrableOn f modularStrip volume := by
    refine ⟨hfc.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hg : ∀ (n : ℤ) (z : ℍ), ‖f (ModularGroup.T ^ n • z)‖ₑ = ‖f z‖ₑ := fun n z => by rw [hT]
    have hunf := tsum_lintegral_fd_eq_two_mul_lintegral_strip (g := fun z => ‖f z‖ₑ) hg
    have hswap : ∑' p : gammaSet 1 1 0, ∫⁻ z in fd, ‖f (gammaSetMatrix p • z)‖ₑ =
        ∫⁻ z in fd, ∑' p : gammaSet 1 1 0, ‖f (gammaSetMatrix p • z)‖ₑ :=
      (lintegral_tsum fun p => (hfc.comp (continuous_modular_smul _)).enorm.aemeasurable).symm
    have hpt : ∀ z, ∑' p : gammaSet 1 1 0, ‖f (gammaSetMatrix p • z)‖ₑ ≤
        ENNReal.ofReal ((∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) * (‖v‖ * ‖G z‖)) := by
      intro z
      rw [ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _),
        ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsum z), ← ENNReal.tsum_mul_right]
      refine ENNReal.tsum_le_tsum fun p => ?_
      show ‖poincIntegrand h v G (gammaSetMatrix p • z)‖ₑ ≤ _
      rw [← inner_poincTerm hGe, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans ?_)
      rw [norm_poincTerm, mul_assoc]
    have hint : Integrable (fun z => (∑' p : gammaSet 1 1 0, ‖h (gammaSetMatrix p • z)‖) *
        (‖v‖ * ‖G z‖)) cellMeasure := by
      have h1 := hH.integrable_mul (hGL.norm.const_mul ‖v‖) (p := 2) (q := 2)
      exact h1
    have hfin : ∫⁻ z in fd, ∑' p : gammaSet 1 1 0, ‖f (gammaSetMatrix p • z)‖ₑ < ∞ :=
      (lintegral_mono hpt).trans_lt (hint.lintegral_lt_top)
    rw [← hswap, hunf] at hfin
    exact lt_of_le_of_lt (le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hfin
  have hsum' : Summable fun p : gammaSet 1 1 0 => ∫ z in fd, ‖f (gammaSetMatrix p • z)‖ := by
    have hφ : ∀ (n : ℤ) (z : ℍ), ((‖f (ModularGroup.T ^ n • z)‖ : ℝ) : ℂ) = ((‖f z‖ : ℝ) : ℂ) :=
      fun n z => by rw [hT]
    have h := summable_fdUnfoldTerm hφ hstrip.norm.ofReal
    refine Complex.summable_ofReal.1 (h.congr fun p => ?_)
    exact integral_complex_ofReal
  have hterm : ∀ p : gammaSet 1 1 0, IntegrableOn (fun z => f (gammaSetMatrix p • z)) fd volume :=
    fun p => (integrableOn_smul_set_iff _ _ _).1 (integrableOn_smul_fd_of_periodic hT hstrip _)
  have hmain := (integral_fd_tsum_eq_two_mul_strip hT hterm hsum').2
  rw [← hmain]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  have hs : Summable fun p => poincTerm h v p z :=
    Summable.of_norm ((hsum z).mul_right ‖v‖ |>.congr fun p => (norm_poincTerm h v p z).symm)
  rw [poincSeries, inner_tsum_left hs]
  exact tsum_congr fun p => inner_poincTerm hGe h v p z

/-! ## The Selberg profile -/

/-- **The Selberg profile** `h_{s,μ}(w) = (Im w)^s e(μ w)`. -/
def poincProfile (s : ℂ) (μ : ℝ) (w : ℍ) : ℂ :=
  ((w.im : ℝ) : ℂ) ^ s * cexp (2 * Real.pi * Complex.I * μ * (w : ℂ))

theorem norm_poincProfile (s : ℂ) (μ : ℝ) (w : ℍ) :
    ‖poincProfile s μ w‖ = w.im ^ s.re * Real.exp (-(2 * Real.pi * μ * w.im)) := by
  rw [poincProfile, norm_mul, norm_cpow_eq_rpow_re_of_pos w.im_pos, Complex.norm_exp]
  congr 2
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (μ : ℂ) * (w : ℂ)) =
      ((2 * Real.pi * μ : ℝ) : ℂ) * (Complex.I * (w : ℂ)) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

theorem norm_poincProfile_le {s : ℂ} {μ : ℝ} (hμ : 0 ≤ μ) (w : ℍ) :
    ‖poincProfile s μ w‖ ≤ w.im ^ s.re := by
  rw [norm_poincProfile]
  refine mul_le_of_le_one_right (Real.rpow_nonneg w.im_pos.le _) (Real.exp_le_one_iff.2 ?_)
  have := w.im_pos
  have := Real.pi_pos
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hμ) this.le]

theorem continuous_poincProfile (s : ℂ) (μ : ℝ) : Continuous (poincProfile s μ) := by
  refine ((continuous_ofReal.comp UpperHalfPlane.continuous_im).cpow continuous_const fun w => ?_).mul
    (Complex.continuous_exp.comp (continuous_const.mul UpperHalfPlane.continuous_coe))
  exact ofReal_mem_slitPlane.2 w.im_pos

/-- `ρ(T) v = e(μ) v`: `v` is a cusp vector of frequency `μ`. -/
def IsCuspEigen (μ : ℝ) (v : DeckSpace N) : Prop :=
  deckRho N ModularGroup.T v = cexp (2 * Real.pi * Complex.I * μ) • v

theorem deckRho_T_zpow_eigen {μ : ℝ} {v : DeckSpace N} (hv : IsCuspEigen μ v) (n : ℤ) :
    deckRho N (ModularGroup.T ^ n) v = cexp (2 * Real.pi * Complex.I * μ * n) • v := by
  induction n using Int.induction_on with
  | zero => simpa using deckRho_one v
  | succ n ih =>
      rw [zpow_add_one, deckRho_mul, hv, map_smul, ih, smul_smul, ← Complex.exp_add]
      congr 2
      push_cast
      ring
  | pred n ih =>
      rw [zpow_sub_one, deckRho_mul, deckRho_inv]
      have hinv : (deckRho N ModularGroup.T).symm v = cexp (-(2 * Real.pi * Complex.I * μ)) • v := by
        refine symm_eq_of_apply_eq ?_
        rw [map_smul, hv, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
      rw [hinv, map_smul, ih, smul_smul, ← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem poincProfile_T_zpow (s : ℂ) (μ : ℝ) (n : ℤ) (w : ℍ) :
    poincProfile s μ (ModularGroup.T ^ n • w) = cexp (2 * Real.pi * Complex.I * μ * n) * poincProfile s μ w := by
  rw [poincProfile, poincProfile, modular_T_zpow_smul, vadd_im, UpperHalfPlane.coe_vadd,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem cuspCompatible_poincProfile (s : ℂ) {μ : ℝ} {v : DeckSpace N} (hv : IsCuspEigen μ v) :
    CuspCompatible (poincProfile s μ) v := fun n w => by
  have hinv : (deckRho N (ModularGroup.T ^ n)).symm v = cexp (-(2 * Real.pi * Complex.I * μ * n)) • v := by
    refine symm_eq_of_apply_eq ?_
    rw [map_smul, deckRho_T_zpow_eigen hv, smul_smul, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, one_smul]
  rw [hinv, poincProfile_T_zpow, smul_smul]
  congr 1
  rw [mul_right_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem summable_norm_poincProfile {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 ≤ μ) (z : ℍ) :
    Summable fun p : gammaSet 1 1 0 => ‖poincProfile s μ (gammaSetMatrix p • z)‖ :=
  (summable_rowHeight_rpow hs z).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun _ => norm_poincProfile_le hμ _

theorem continuous_poincSeries_profile {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 ≤ μ)
    (v : DeckSpace N) : Continuous (poincSeries (poincProfile s μ) v) :=
  continuous_tsum_of_rowHeight_bound
    (fun p => ((continuous_poincProfile s μ).comp (continuous_modular_smul _)).smul continuous_const)
    hs (norm_nonneg v) fun p z => by
      rw [norm_poincTerm, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_poincProfile_le hμ _) (norm_nonneg _)

theorem continuous_tsum_norm_poincProfile {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 ≤ μ) :
    Continuous fun z : ℍ => ∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖ :=
  continuous_tsum_of_rowHeight_bound (F := fun p z => ‖poincProfile s μ (gammaSetMatrix p • z)‖)
    (fun p => ((continuous_poincProfile s μ).comp (continuous_modular_smul _)).norm) hs zero_le_one
    fun p z => by
      rw [norm_norm, one_mul]
      exact norm_poincProfile_le hμ _

/-! ## The majorant on `𝒟` and square integrability -/

theorem rowHeight_le_inv_of_ne_zero {p : gammaSet 1 1 0} (hc : p.1 0 ≠ 0) (z : ℍ) :
    RHTower.rowHeight p z ≤ z.im⁻¹ := by
  rw [RHTower.rowHeight, im_gammaSetMatrix_smul, _root_.RHTower.normSq_int_mul_add]
  have hy := z.im_pos
  have hc1 : (1 : ℝ) ≤ ((p.1 0 : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (p.1 0) ^ 2 := by
      have := sq_pos_of_ne_zero hc
      omega
    exact_mod_cast this
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((p.1 0 : ℤ) * z.im) ^ 2 +
    ((p.1 0 : ℤ) * z.re + (p.1 1 : ℤ)) ^ 2)]
  rw [inv_mul_eq_div, le_div_iff₀ hy]
  nlinarith [sq_nonneg (((p.1 0 : ℤ) : ℝ) * z.re + (p.1 1 : ℤ)), mul_pos hy hy]

/-- On `𝒟`: `Σ |h_{s,μ}(M_{c,d} z)| ≤ C y^{1-σ} + 2 y^σ e^{-2πμy}`. -/
theorem exists_tsum_norm_poincProfile_le_fd {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ fd, ∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖ ≤
      C * z.im ^ (1 - s.re) + 2 * (z.im ^ s.re * Real.exp (-(2 * Real.pi * μ * z.im))) := by
  obtain ⟨C, hC0, hC⟩ := exists_realTruncatedRowSum_le hs (Y := 2) (by norm_num)
  refine ⟨C, hC0, fun z hz => ?_⟩
  have hy : 1 / 2 < z.im := RHTower.half_lt_im_of_mem_fd' hz
  set b := z.im ^ s.re * Real.exp (-(2 * Real.pi * μ * z.im))
  have hb0 : 0 ≤ b := mul_nonneg (Real.rpow_nonneg z.im_pos.le _) (Real.exp_pos _).le
  set A : gammaSet 1 1 0 → ℝ := fun p =>
    if RHTower.rowHeight p z ≤ 2 then RHTower.rowHeight p z ^ s.re else 0
  set B : gammaSet 1 1 0 → ℝ := fun p => if p = RHTower.rowPlus ∨ p = RHTower.rowMinus then b else 0
  have hA : Summable A := RHTower.summable_realTruncated_term hs 2 z
  have hB : Summable B := summable_of_ne_finset_zero (s := {RHTower.rowPlus, RHTower.rowMinus})
    fun p hp => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [B, if_neg hp]
  have hBsum : ∑' p, B p = 2 * b := by
    rw [tsum_eq_sum (s := {RHTower.rowPlus, RHTower.rowMinus}) fun p hp => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        simp only [B, if_neg hp],
      Finset.sum_pair RHTower.rowPlus_ne_rowMinus]
    simp only [B, true_or, or_true, if_true]
    ring
  have hle : ∀ p, ‖poincProfile s μ (gammaSetMatrix p • z)‖ ≤ A p + B p := fun p => by
    have hB0 : 0 ≤ B p := by simp only [B]; split_ifs <;> simp [hb0]
    by_cases h2 : RHTower.rowHeight p z ≤ 2
    · have hA' : A p = RHTower.rowHeight p z ^ s.re := by simp only [A, if_pos h2]
      rw [hA']
      exact (norm_poincProfile_le hμ _).trans (le_add_of_nonneg_right hB0)
    · have hc : p.1 0 = 0 := by
        by_contra hc
        have h1 := rowHeight_le_inv_of_ne_zero hc z
        have h3 : z.im⁻¹ < 2 := by
          rw [inv_lt_comm₀ z.im_pos (by norm_num)]
          linarith
        exact h2 (h1.trans h3.le)
      have hpm := (RHTower.first_zero_iff p).1 hc
      have hrow : RHTower.rowHeight p z = z.im := by
        rcases hpm with rfl | rfl
        · exact RHTower.rowHeight_rowPlus z
        · exact RHTower.rowHeight_rowMinus z
      have hA' : A p = 0 := by simp only [A, if_neg h2]
      have hB' : B p = b := by simp only [B, if_pos hpm]
      rw [hA', hB', zero_add, norm_poincProfile]
      show (gammaSetMatrix p • z).im ^ s.re * _ ≤ b
      rw [show (gammaSetMatrix p • z).im = z.im from hrow]
  calc ∑' p, ‖poincProfile s μ (gammaSetMatrix p • z)‖ ≤ ∑' p, (A p + B p) :=
        (summable_norm_poincProfile hs hμ z).tsum_le_tsum hle (hA.add hB)
    _ = ∑' p, A p + ∑' p, B p := hA.tsum_add hB
    _ ≤ C * z.im ^ (1 - s.re) + 2 * b := add_le_add (hC z hz) (le_of_eq hBsum)

/-- The majorant `z ↦ Σ |h_{s,μ}(M_{c,d} z)|` is square integrable on `𝒟` for `Re s > 1`, `μ > 0`. -/
theorem memLp_tsum_norm_poincProfile {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 < μ) :
    MemLp (fun z : ℍ => ∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖) 2
      cellMeasure := by
  obtain ⟨C, hC0, hC⟩ := exists_tsum_norm_poincProfile_le_fd hs hμ.le
  set K₀ := (s.re / (2 * Real.pi * μ)) ^ s.re
  have hK₀ : 0 ≤ K₀ := Real.rpow_nonneg (by have := Real.pi_pos; positivity) _
  have hdecay : ∀ y : ℝ, 0 < y → y ^ s.re * Real.exp (-(2 * Real.pi * μ * y)) ≤ K₀ := fun y hy => by
    have h := SelbergPoincareBounded.rpow_mul_exp_le (by linarith : 0 < s.re)
      (by have := Real.pi_pos; positivity : 0 < 2 * Real.pi * μ) hy.le
    rwa [show -(2 * Real.pi * μ) * y = -(2 * Real.pi * μ * y) by ring] at h
  have hcont := continuous_tsum_norm_poincProfile hs hμ.le
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  set C' := max (2 * C ^ 2) (8 * K₀ ^ 2)
  have hint := integrableOn_fd_of_norm_le_two (g := fun z : ℍ =>
      (((‖∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖‖ ^ 2 : ℝ)) : ℂ))
    ((Complex.continuous_ofReal.comp (hcont.norm.pow 2)).aestronglyMeasurable)
    (β₁ := 2 - 2 * s.re) (β₂ := 0) (C := C') (by linarith) (by norm_num) fun z hz => by
      have hH := hC z hz
      have hH0 : 0 ≤ ∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖ :=
        tsum_nonneg fun _ => norm_nonneg _
      have hd := hdecay z.im z.im_pos
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg hH0, Real.rpow_zero]
      have hy1 : 0 ≤ z.im ^ (1 - s.re) := Real.rpow_nonneg z.im_pos.le _
      have hsq : (z.im ^ (1 - s.re)) ^ 2 = z.im ^ (2 - 2 * s.re) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul z.im_pos.le]
        norm_num
        ring_nf
      calc (∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖) ^ 2
          ≤ (C * z.im ^ (1 - s.re) + 2 * K₀) ^ 2 := by
            gcongr
            exact hH.trans (by linarith)
        _ ≤ 2 * C ^ 2 * (z.im ^ (1 - s.re)) ^ 2 + 8 * K₀ ^ 2 := by
            nlinarith [sq_nonneg (C * z.im ^ (1 - s.re) - 2 * K₀)]
        _ ≤ C' * (z.im ^ (2 - 2 * s.re) + 1) := by
            rw [hsq]
            have h1 : 2 * C ^ 2 ≤ C' := le_max_left _ _
            have h2 : 8 * K₀ ^ 2 ≤ C' := le_max_right _ _
            have h3 : 0 ≤ z.im ^ (2 - 2 * s.re) := Real.rpow_nonneg z.im_pos.le _
            nlinarith
  exact hint.re.congr (Eventually.of_forall fun z => Complex.ofReal_re _)

theorem memLp_poincSeries_profile {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 < μ)
    (v : DeckSpace N) : MemLp (poincSeries (poincProfile s μ) v) 2 cellMeasure := by
  refine ((memLp_tsum_norm_poincProfile hs hμ).const_mul ‖v‖).of_le
    (continuous_poincSeries_profile hs hμ.le v).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  have hsum := summable_norm_poincProfile hs hμ.le z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _))]
  calc ‖poincSeries (poincProfile s μ) v z‖ ≤ ∑' p, ‖poincTerm (poincProfile s μ) v p z‖ :=
        norm_tsum_le_tsum_norm (hsum.mul_right ‖v‖ |>.congr fun p =>
          (norm_poincTerm _ v p z).symm)
    _ = ‖v‖ * ∑' p : gammaSet 1 1 0, ‖poincProfile s μ (gammaSetMatrix p • z)‖ := by
        simp_rw [norm_poincTerm]
        rw [tsum_mul_right, mul_comm]

/-- **Unfolding of the Selberg–Poincaré series.** -/
theorem integral_inner_poincSeries_profile {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 < μ)
    {v : DeckSpace N} (hv : IsCuspEigen μ v) {G : ℍ → DeckSpace N} (hGc : Continuous G)
    (hGe : deckEquivariant N G) (hGL : MemLp G 2 cellMeasure) :
    ∫ z in fd, ⟪poincSeries (poincProfile s μ) v z, G z⟫_ℂ =
      2 * ∫ w in modularStrip, poincIntegrand (poincProfile s μ) v G w :=
  integral_inner_poincSeries (cuspCompatible_poincProfile s hv) (continuous_poincProfile s μ) hGc hGe
    hGL (summable_norm_poincProfile hs hμ.le) (memLp_tsum_norm_poincProfile hs hμ)

end

end GaloisForLFunctions.RHTower.DeckPointPair
