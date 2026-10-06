import GaloisForLFunctions.RHTower.KuznetsovLargeSieveSummability

/-!
# The same-sign Kuznetsov identity at `σ = 1` for rapid weights

Letting `σ ↓ 1` in `kuznetsov_same_sign_weight_sigma` gives, for every rapid same-sign weight
`(h, G)` and two finite families of cusp vectors,

`Σ_{k,l} b̄_k b'_l [2 diag_{kl} ∫h + 2 Σ_{(c,d)} w⁺ c^{−2} Ψ_1^G(4π√(μ_kμ'_l)/|c|)]
   = 4 Σ_j A_j Ā'_j ∫ h |W(1+it, ν_j)|² dt + π⁻¹ ∫ Σ_i B_i B̄'_i ∫ h |W(1+it, ir)|² dt dr`

(`kuznetsov_same_sign_weight`), with `Ψ_1^G(X) = 2∫G(w) tanh w sin(X cosh w) dw` (`weightKernel_one`).

The geometric side converges by Tannery (`|Ψ_σ^G(X)| ≤ π X ∫|G sinh|`).  On the spectral side the
coefficients are dominated, uniformly in `1 ≤ σ ≤ 2`, by the majorants `Σ_k |b_k| m_k |ρ_j(v_k)|`,
`m_k = (2πμ_k)^{−½} + (2πμ_k)^{−3/2}`, the weights by `C e^{−πκ}(1+κ)^{−4}`
(`exists_bound_specWeight_specParam`, `exists_bound_specWeight_imag`), and the products are summable
(resp. integrable) by the large sieve (`summable_cuspCoeff_sq_weight`, `integrable_eisCoeff_sq_weight`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry KuznetsovGauss

noncomputable section

variable {N : ℕ} {ι : Type*} (W : SameSignWeight)

/-! ## The geometric side -/

theorem tendsto_weightRow {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (v w : DeckSpace N) :
    Tendsto (fun σ : ℝ => weightRow W σ μ ν v w) (𝓝[>] 1) (𝓝 (weightRow W 1 μ ν v w)) := by
  unfold weightRow
  refine (((tendsto_diagPlus hμ v w).mono_left nhdsWithin_le_nhds).const_mul 2 |>.mul_const _).add
    (Tendsto.const_mul 2 ?_)
  set C : ℝ := ‖v‖ * ‖w‖ * (Real.pi * (4 * Real.pi * Real.sqrt (μ * ν)) * weightSinhMass W)
  have hCm := weightSinhMass_nonneg W
  refine tendsto_tsum_of_dominated_convergence (bound := fun r => C * rowSq r ^ (-(3 / 2 : ℝ)))
    ((summable_reducedRow_rpow (τ := 3 / 2) (by norm_num)).mul_left C) (fun r => ?_) ?_
  · have hq := rowSq_pos r
    have h1 : Tendsto (fun σ : ℝ => ((rowSq r ^ (-σ) : ℝ) : ℂ)) (𝓝[>] 1)
        (𝓝 ((rowSq r ^ (-(1 : ℝ)) : ℝ) : ℂ)) :=
      ((Complex.continuous_ofReal.tendsto _).comp
        (((Real.continuousAt_const_rpow hq.ne').comp continuous_neg.continuousAt).tendsto)).mono_left
        nhdsWithin_le_nhds
    have hX : 0 ≤ 4 * Real.pi * Real.sqrt (μ * ν / rowSq r) := by positivity
    exact (h1.const_mul _).mul (tendsto_weightKernel W hX)
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ) r
    have hq := rowSq_pos r
    have hq1 := one_le_rowSq r
    have hX : 0 ≤ 4 * Real.pi * Real.sqrt (μ * ν / rowSq r) := by positivity
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 := norm_rowWeightPlus_le μ ν v w r.1
    have h2 := norm_weightKernel_le W hσ.le hX
    have h3 : rowSq r ^ (-σ) ≤ rowSq r ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have h4 : Real.sqrt (μ * ν / rowSq r) = Real.sqrt (μ * ν) * rowSq r ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_div' _ hq.le, Real.sqrt_eq_rpow (rowSq r), Real.rpow_neg hq.le, div_eq_mul_inv]
    have h5 : rowSq r ^ (-(1 : ℝ)) * rowSq r ^ (-(1 / 2 : ℝ)) = rowSq r ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hq]; norm_num
    calc ‖rowWeightPlus μ ν v w r.1‖ * rowSq r ^ (-σ) *
          ‖weightKernel W σ (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))‖
        ≤ ‖v‖ * ‖w‖ * rowSq r ^ (-(1 : ℝ)) *
          (Real.pi * (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)) * weightSinhMass W) := by
          gcongr
      _ = C * (rowSq r ^ (-(1 : ℝ)) * rowSq r ^ (-(1 / 2 : ℝ))) := by rw [h4]; ring
      _ = C * rowSq r ^ (-(3 / 2 : ℝ)) := by rw [h5]

theorem tendsto_weightForm (s s' : Finset ι) {μ μ' : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    (hμ' : ∀ k, 0 < μ' k) (v v' : ι → DeckSpace N) (b b' : ι → ℂ) :
    Tendsto (fun σ : ℝ => weightForm W σ s s' μ μ' v v' b b') (𝓝[>] 1)
      (𝓝 (weightForm W 1 s s' μ μ' v v' b b')) :=
  tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ =>
    (tendsto_weightRow W (hμ k) (hμ' l) (v k) (v' l)).const_mul _

/-! ## Majorants of the coefficients -/

/-- `m(x) = x^{−½} + x^{−3/2}` bounds `x^{½−σ}` for `1 ≤ σ ≤ 2`. -/
theorem norm_cpow_line_le {x : ℝ} (hx : 0 < x) {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) :
    ‖((x : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2))‖ ≤ x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 / 2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-((σ : ℂ) - 1 / 2)).re = 1 / 2 - σ := by simp
  rw [hre]
  rcases le_total 1 x with hx1 | hx1
  · have := Real.rpow_le_rpow_of_exponent_le hx1 (show 1 / 2 - σ ≤ -(1 / 2 : ℝ) by linarith)
    linarith [Real.rpow_nonneg hx.le (-(3 / 2 : ℝ))]
  · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show -(3 / 2 : ℝ) ≤ 1 / 2 - σ by linarith)
    linarith [Real.rpow_nonneg hx.le (-(1 / 2 : ℝ))]

/-- `m_k = (2πμ_k)^{−½} + (2πμ_k)^{−3/2}`. -/
def lineMaj (μ : ℝ) : ℝ := (2 * Real.pi * μ) ^ (-(1 / 2 : ℝ)) + (2 * Real.pi * μ) ^ (-(3 / 2 : ℝ))

theorem lineMaj_nonneg {μ : ℝ} (hμ : 0 < μ) : 0 ≤ lineMaj μ := by unfold lineMaj; positivity

/-- The discrete majorant `Σ_k |b_k| m_k |ρ_j(v_k)|`. -/
def specMaj (j : CuspEigenIndex N) (s : Finset ι) (μ : ι → ℝ) (v : ι → DeckSpace N) (b : ι → ℂ) : ℝ :=
  ∑ k ∈ s, ‖b k‖ * lineMaj (μ k) * ‖cuspCoeff j (μ k) (v k)‖

theorem norm_specCoeff_le_specMaj (j : CuspEigenIndex N) {σ : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2)
    (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k) (v : ι → DeckSpace N) (b : ι → ℂ) :
    ‖specCoeff j σ s μ v b‖ ≤ specMaj j s μ v b := by
  unfold specCoeff specMaj
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have := norm_cpow_line_le (by have := hμ k; positivity : (0 : ℝ) < 2 * Real.pi * μ k) h1 h2
  calc ‖b k‖ * ‖cuspCoeff j (μ k) (v k)‖ * ‖((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2))‖
      ≤ ‖b k‖ * ‖cuspCoeff j (μ k) (v k)‖ * lineMaj (μ k) := by unfold lineMaj; gcongr
    _ = _ := by ring

theorem specMaj_nonneg (j : CuspEigenIndex N) (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    (v : ι → DeckSpace N) (b : ι → ℂ) : 0 ≤ specMaj j s μ v b :=
  Finset.sum_nonneg fun k _ => by have := lineMaj_nonneg (hμ k); positivity

/-- `Σ_j (specMaj_j)² e^{−πκ_j}(1+κ_j)^{−4} < ∞`. -/
theorem summable_specMaj_sq_weight (hN : 2 ≤ N) (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k)) {n : ι → ℤ}
    (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k) (b : ι → ℂ) :
    Summable fun j : CuspEigenIndex N => specMaj j s μ v b ^ 2 *
      (Real.exp (-(Real.pi * specKappa j.1)) / (1 + specKappa j.1) ^ 4) := by
  have hsum : Summable fun j : CuspEigenIndex N => (s.card : ℝ) * ∑ k ∈ s,
      (‖b k‖ * lineMaj (μ k)) ^ 2 * (‖cuspCoeff j (μ k) (v k)‖ ^ 2 *
        (Real.exp (-(Real.pi * specKappa j.1)) / (1 + specKappa j.1) ^ 4)) :=
    (summable_sum fun k _ => (summable_cuspCoeff_sq_weight hN (hμ k) (hv k) (hn k)).mul_left _).mul_left _
  refine hsum.of_nonneg_of_le (fun j => by positivity) fun j => ?_
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun k => ‖b k‖ * lineMaj (μ k) *
    ‖cuspCoeff j (μ k) (v k)‖)
  unfold specMaj
  rw [Finset.mul_sum]
  calc (∑ k ∈ s, ‖b k‖ * lineMaj (μ k) * ‖cuspCoeff j (μ k) (v k)‖) ^ 2 *
        (Real.exp (-(Real.pi * specKappa j.1)) / (1 + specKappa j.1) ^ 4)
      ≤ ((s.card : ℝ) * ∑ k ∈ s, (‖b k‖ * lineMaj (μ k) * ‖cuspCoeff j (μ k) (v k)‖) ^ 2) *
        (Real.exp (-(Real.pi * specKappa j.1)) / (1 + specKappa j.1) ^ 4) := by
        gcongr
    _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring

/-- The continuous majorant `Σ_k |b_k| m_k |η_i(v_k, r)|`. -/
def eisMaj (i : Fin (Module.finrank ℂ (cuspVecSub N))) (r : ℝ) (s : Finset ι) (μ : ι → ℝ)
    (v : ι → DeckSpace N) (n : ι → ℤ) (b : ι → ℂ) : ℝ :=
  ∑ k ∈ s, ‖b k‖ * lineMaj (μ k) * ‖eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k)‖

theorem norm_eisSpecCoeff_le_eisMaj (i : Fin (Module.finrank ℂ (cuspVecSub N))) {σ : ℝ}
    (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (r : ℝ) (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    (v : ι → DeckSpace N) (n : ι → ℤ) (b : ι → ℂ) :
    ‖eisSpecCoeff i σ r s μ v n b‖ ≤ eisMaj i r s μ v n b := by
  unfold eisSpecCoeff eisMaj
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have := norm_cpow_line_le (by have := hμ k; positivity : (0 : ℝ) < 2 * Real.pi * μ k) h1 h2
  calc ‖b k‖ * ‖eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k)‖ *
        ‖((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2))‖
      ≤ ‖b k‖ * ‖eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k)‖ * lineMaj (μ k) := by
        unfold lineMaj; gcongr
    _ = _ := by ring

theorem eisMaj_nonneg (i : Fin (Module.finrank ℂ (cuspVecSub N))) (r : ℝ) (s : Finset ι)
    {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k) (v : ι → DeckSpace N) (n : ι → ℤ) (b : ι → ℂ) :
    0 ≤ eisMaj i r s μ v n b :=
  Finset.sum_nonneg fun k _ => by have := lineMaj_nonneg (hμ k); positivity

/-- `∫ Σ_i (eisMaj_i)² e^{−π|r|}(1+|r|)^{−4} dr < ∞`. -/
theorem integrable_eisMaj_sq_weight (hN : 2 ≤ N) (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k)) {n : ι → ℤ}
    (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k) (b : ι → ℂ) :
    Integrable fun r : ℝ => (∑ i, eisMaj i r s μ v n b ^ 2) *
      (Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4) := by
  have hint : Integrable fun r : ℝ => (s.card : ℝ) * ∑ k ∈ s, (‖b k‖ * lineMaj (μ k)) ^ 2 *
      ((∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k)‖ ^ 2) *
        (Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4)) :=
    (integrable_finsetSum _ fun k _ =>
      (integrable_eisCoeff_sq_weight hN (hμ k) (hv k) (hn k)).const_mul _).const_mul _
  have hm : AEStronglyMeasurable (fun r : ℝ => (∑ i, eisMaj i r s μ v n b ^ 2) *
      (Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4)) volume := by
    refine (Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_).mul
      ((by fun_prop : Continuous fun r : ℝ => Real.exp (-(Real.pi * |r|))).div (by fun_prop)
        fun r => by positivity).aestronglyMeasurable
    unfold eisMaj
    exact (Finset.aestronglyMeasurable_fun_sum _ fun k _ => aestronglyMeasurable_const.mul
      (aestronglyMeasurable_eisCoeff_line _ _ _).norm).pow 2
  refine hint.mono' hm (Eventually.of_forall fun r => ?_)
  have hw : 0 ≤ Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4 := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => by positivity) hw)]
  calc (∑ i, eisMaj i r s μ v n b ^ 2) * (Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4)
      ≤ (∑ i, (s.card : ℝ) * ∑ k ∈ s, (‖b k‖ * lineMaj (μ k)) ^ 2 *
          ‖eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k)‖ ^ 2) *
        (Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4) := by
        gcongr with i
        unfold eisMaj
        have := sq_sum_le_card_mul_sum_sq (s := s) (f := fun k => ‖b k‖ * lineMaj (μ k) *
          ‖eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k)‖)
        calc _ ≤ (s.card : ℝ) * ∑ k ∈ s, (‖b k‖ * lineMaj (μ k) *
              ‖eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k)‖) ^ 2 := by
              exact_mod_cast this
          _ = _ := by congr 1; refine Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm, mul_assoc, Finset.sum_mul]
        congr 1; refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, mul_assoc]


/-! ## The spectral weights as `σ ↓ 1` -/

theorem tendsto_specWeight_specParam (hW : W.IsRapid) {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun σ : ℝ => specWeight W σ (specParam lam)) (𝓝[>] 1)
      (𝓝 (specWeight W 1 (specParam lam))) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_weight_whittMellin_specParam W hW 0
  unfold specWeight
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => C * Real.exp (-(Real.pi * specKappa lam)) * (1 + t ^ 2)⁻¹) ?_ ?_
    (integrable_inv_one_add_sq.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    exact W.continuous_h.aestronglyMeasurable.mul (Complex.measurable_ofReal.comp
      (measurable_specCoeff_line lam hlam hσ.le)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simpa using hb σ t lam hσ.1.le hσ.2.le hlam
  · filter_upwards [Measure.ae_ne volume 0] with t ht
    have hc : ContinuousAt (fun σ : ℝ => whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)) 1 :=
      (continuousAt_whittMellin_specParam hlam (le_refl 1) (Or.inl ht)).comp
        (f := fun σ : ℝ => (σ : ℂ) + t * Complex.I) (by fun_prop : Continuous fun σ : ℝ =>
          (σ : ℂ) + t * Complex.I).continuousAt
    exact (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
      ((hc.norm.pow 2).tendsto))).mono_left nhdsWithin_le_nhds

theorem tendsto_specWeight_imag (hW : W.IsRapid) (r : ℝ) :
    Tendsto (fun σ : ℝ => specWeight W σ (r * Complex.I)) (𝓝[>] 1)
      (𝓝 (specWeight W 1 (r * Complex.I))) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_weight_whittMellin_imag W hW 0
  unfold specWeight
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => C * Real.exp (-(Real.pi * |r|)) * (1 + t ^ 2)⁻¹) ?_ ?_
    (integrable_inv_one_add_sq.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    exact W.continuous_h.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
      ((continuous_whittMellin_line_imag (by linarith) r).norm.pow 2)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simpa using hb σ t r hσ.1.le hσ.2.le
  · refine Eventually.of_forall fun t => ?_
    have hc : ContinuousAt (fun σ : ℝ => whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)) 1 :=
      (continuousAt_whittMellin_imag (t := t) (r := r) (by norm_num)).comp
        (f := fun σ : ℝ => (σ, t, r)) (by fun_prop : Continuous fun σ : ℝ =>
          ((σ, t, r) : ℝ × ℝ × ℝ)).continuousAt
    exact (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
      ((hc.norm.pow 2).tendsto))).mono_left nhdsWithin_le_nhds

/-! ## The two spectral parts as `σ ↓ 1` -/

theorem tendsto_cusp_part (hN : 2 ≤ N) (hW : W.IsRapid) (s s' : Finset ι) {μ μ' : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k))
    {n n' : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k)
    (hn' : ∀ k, μ' k * ((N + 1 : ℕ) : ℝ) = n' k) (b b' : ι → ℂ) :
    Tendsto (fun σ : ℝ => ∑' j : CuspEigenIndex N,
      4 * (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')) * specWeight W σ (specParam j.1))
      (𝓝[>] 1) (𝓝 (∑' j : CuspEigenIndex N,
        4 * (specCoeff j 1 s μ v b * conj (specCoeff j 1 s' μ' v' b')) *
          specWeight W 1 (specParam j.1))) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_specWeight_specParam W hW 4
  set w : CuspEigenIndex N → ℝ := fun j =>
    Real.exp (-(Real.pi * specKappa j.1)) / (1 + specKappa j.1) ^ 4
  have hsum : Summable fun j : CuspEigenIndex N =>
      4 * C * ((specMaj j s μ v b ^ 2 * w j + specMaj j s' μ' v' b' ^ 2 * w j) / 2) :=
    (((summable_specMaj_sq_weight hN s hμ hv hn b).add
      (summable_specMaj_sq_weight hN s' hμ' hv' hn' b')).div_const 2).mul_left _
  refine tendsto_tsum_of_dominated_convergence hsum (fun j => ?_) ?_
  · exact (((continuous_specCoeff j s hμ v b).tendsto 1).mul
      ((Complex.continuous_conj.tendsto _).comp ((continuous_specCoeff j s' hμ' v' b').tendsto 1))
        |>.const_mul 4 |>.mono_left nhdsWithin_le_nhds).mul
      (tendsto_specWeight_specParam W hW (cuspEigenBasis_lam_nonneg j))
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ j
    have hκ0 : 0 ≤ specKappa j.1 := Real.sqrt_nonneg _
    have hκ : 0 < (1 + specKappa j.1) ^ 4 := pow_pos (by linarith) 4
    have hS : ‖specWeight W σ (specParam j.1)‖ ≤ C * w j := by
      have := (hb σ j.1 hσ.1.le hσ.2.le (cuspEigenBasis_lam_nonneg j)).2
      simp only [w]; rw [mul_div_assoc', le_div_iff₀ hκ]; exact this
    have hA := norm_specCoeff_le_specMaj j hσ.1.le hσ.2.le s hμ v b
    have hA' := norm_specCoeff_le_specMaj j hσ.1.le hσ.2.le s' hμ' v' b'
    have h0 := specMaj_nonneg j s hμ v b
    have h0' := specMaj_nonneg j s' hμ' v' b'
    have hw : 0 ≤ w j := by simp only [w]; positivity
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, RCLike.norm_ofNat]
    calc 4 * (‖specCoeff j σ s μ v b‖ * ‖specCoeff j σ s' μ' v' b'‖) * ‖specWeight W σ (specParam j.1)‖
        ≤ 4 * (specMaj j s μ v b * specMaj j s' μ' v' b') * (C * w j) := by gcongr
      _ ≤ _ := by
          have := two_mul_le_add_sq (specMaj j s μ v b) (specMaj j s' μ' v' b')
          nlinarith [mul_nonneg hC hw]

theorem tendsto_eis_part (hN : 2 ≤ N) (hW : W.IsRapid) (s s' : Finset ι) {μ μ' : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k))
    {n n' : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k)
    (hn' : ∀ k, μ' k * ((N + 1 : ℕ) : ℝ) = n' k) (b b' : ι → ℂ) :
    Tendsto (fun σ : ℝ => ∫ r : ℝ, (∑ i, eisSpecCoeff i σ r s μ v n b *
        conj (eisSpecCoeff i σ r s' μ' v' n' b')) * specWeight W σ (r * Complex.I))
      (𝓝[>] 1) (𝓝 (∫ r : ℝ, (∑ i, eisSpecCoeff i 1 r s μ v n b *
        conj (eisSpecCoeff i 1 r s' μ' v' n' b')) * specWeight W 1 (r * Complex.I))) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_specWeight_imag W hW 4
  set w : ℝ → ℝ := fun r => Real.exp (-(Real.pi * |r|)) / (1 + |r|) ^ 4
  have hint : Integrable fun r : ℝ => C * (((∑ i, eisMaj i r s μ v n b ^ 2) * w r +
      (∑ i, eisMaj i r s' μ' v' n' b' ^ 2) * w r) / 2) :=
    (((integrable_eisMaj_sq_weight hN s hμ hv hn b).add
      (integrable_eisMaj_sq_weight hN s' hμ' hv' hn' b')).div_const 2).const_mul _
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hint ?_
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    have hsw : AEStronglyMeasurable (fun r : ℝ => specWeight W σ (r * Complex.I)) volume := by
      have hcont : Continuous fun p : ℝ × ℝ => W.h p.2 *
          ((‖whittMellin ((σ : ℂ) + p.2 * Complex.I) (p.1 * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
        have hWc : Continuous fun p : ℝ × ℝ =>
            whittMellin ((σ : ℂ) + p.2 * Complex.I) (p.1 * Complex.I) :=
          continuous_iff_continuousAt.2 fun p =>
            (continuousAt_whittMellin_imag (t := p.2) (r := p.1) (by linarith)).comp
              (f := fun p : ℝ × ℝ => (σ, p.2, p.1)) (by fun_prop : Continuous fun p : ℝ × ℝ =>
                ((σ, p.2, p.1) : ℝ × ℝ × ℝ)).continuousAt
        exact (W.continuous_h.comp continuous_snd).mul
          (Complex.continuous_ofReal.comp (hWc.norm.pow 2))
      exact (hcont.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).aestronglyMeasurable
    exact (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (aestronglyMeasurable_eisSpecCoeff i σ s μ v n b).mul
        (Complex.continuous_conj.comp_aestronglyMeasurable
          (aestronglyMeasurable_eisSpecCoeff i σ s' μ' v' n' b'))).mul hsw
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with σ hσ
    refine Eventually.of_forall fun r => ?_
    have hκ : 0 < (1 + |r|) ^ 4 := pow_pos (by linarith [abs_nonneg r]) 4
    have hS : ‖specWeight W σ (r * Complex.I)‖ ≤ C * w r := by
      have := (hb σ r hσ.1.le hσ.2.le).2
      simp only [w]; rw [mul_div_assoc', le_div_iff₀ hκ]; exact this
    have hw : 0 ≤ w r := by simp only [w]; positivity
    rw [norm_mul]
    have hsum : ‖∑ i, eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b')‖ ≤
        ((∑ i, eisMaj i r s μ v n b ^ 2) + ∑ i, eisMaj i r s' μ' v' n' b' ^ 2) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, Complex.norm_conj]
      have h1 := norm_eisSpecCoeff_le_eisMaj i hσ.1.le hσ.2.le r s hμ v n b
      have h2 := norm_eisSpecCoeff_le_eisMaj i hσ.1.le hσ.2.le r s' hμ' v' n' b'
      have := two_mul_le_add_sq (eisMaj i r s μ v n b) (eisMaj i r s' μ' v' n' b')
      nlinarith [norm_nonneg (eisSpecCoeff i σ r s μ v n b),
        norm_nonneg (eisSpecCoeff i σ r s' μ' v' n' b'),
        mul_le_mul h1 h2 (norm_nonneg _) (eisMaj_nonneg i r s hμ v n b)]
    calc _ ≤ ((∑ i, eisMaj i r s μ v n b ^ 2) + ∑ i, eisMaj i r s' μ' v' n' b' ^ 2) / 2 * (C * w r) :=
          mul_le_mul hsum hS (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · refine Eventually.of_forall fun r => ?_
    exact (tendsto_finsetSum _ fun i _ =>
      (((continuous_eisSpecCoeff_sigma i r s hμ v n b).tendsto 1).mul
        ((Complex.continuous_conj.tendsto _).comp
          ((continuous_eisSpecCoeff_sigma i r s' hμ' v' n' b').tendsto 1))).mono_left
            nhdsWithin_le_nhds).mul (tendsto_specWeight_imag W hW r)

/-! ## The identity at `σ = 1` -/

/-- **The same-sign Kuznetsov identity at `σ = 1` for rapid weights.** -/
theorem kuznetsov_same_sign_weight (hN : 2 ≤ N) (hW : W.IsRapid) (s s' : Finset ι)
    {μ μ' : ι → ℝ} (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k))
    {n n' : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k)
    (hn' : ∀ k, μ' k * ((N + 1 : ℕ) : ℝ) = n' k) (b b' : ι → ℂ) :
    weightForm W 1 s s' μ μ' v v' b b' =
      (∑' j : CuspEigenIndex N, 4 * (specCoeff j 1 s μ v b * conj (specCoeff j 1 s' μ' v' b')) *
        specWeight W 1 (specParam j.1)) +
      (Real.pi : ℂ)⁻¹ * ∫ r : ℝ, (∑ i, eisSpecCoeff i 1 r s μ v n b *
        conj (eisSpecCoeff i 1 r s' μ' v' n' b')) * specWeight W 1 (r * Complex.I) := by
  refine tendsto_nhds_unique (tendsto_weightForm W s s' hμ hμ' v v' b b') ?_
  refine ((tendsto_cusp_part W hN hW s s' hμ hμ' hv hv' hn hn' b b').add
    ((tendsto_eis_part W hN hW s s' hμ hμ' hv hv' hn hn' b b').const_mul _)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  exact (kuznetsov_same_sign_weight_sigma W hN hσ s s' hμ hμ' hv hv' hn hn' b b').symm

end

end GaloisForLFunctions.RHTower.DeckPointPair
