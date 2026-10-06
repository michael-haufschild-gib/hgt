import GaloisForLFunctions.RHTower.KuznetsovSpectralWeightLower

/-!
# The full spectrum: Parseval for `F_t` and the continuous large sieve

For `F_t = Σ_k b_k (2πμ_k)^{−it} U(·| σ−it, μ_k, v_k)` (`σ > 1`), Parseval over the full spectrum gives

`‖F_t‖² = 4 Σ_j |W(σ+it, ν_j)|² |A_j(σ)|² + π⁻¹ ∫ Σ_i |W(σ+it, ir)|² |B_i(σ, r)|² dr`,
`B_i(σ, r) = Σ_k b̄_k η_i(v_k, r) (2πμ_k)^{½−σ}`

(`norm_famL2_sq_eq_parseval`), with `η_i(v, r)` the Eisenstein coefficients against the orthonormal basis
`e_i` of the cusp vectors.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex Filter Topology
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry KuznetsovGauss

noncomputable section

variable {N : ℕ} {ι : Type*}

/-- `B_i(σ, r) = Σ_k b̄_k η_i(v_k, r) (2πμ_k)^{½−σ}`. -/
def eisSpecCoeff (i : Fin (Module.finrank ℂ (cuspVecSub N))) (σ r : ℝ) (s : Finset ι) (μ : ι → ℝ)
    (v : ι → DeckSpace N) (n : ι → ℤ) (b : ι → ℂ) : ℂ :=
  ∑ k ∈ s, conj (b k) * eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k) *
    ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2))

theorem famL2_mem_central {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι) {μ : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k)) (b : ι → ℂ) :
    famL2 hσ t s hμ v b ∈ deckCentralFixedL2 N :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (toDeckL2_mem_deckCentralFixedL2
    (deckEquivariant_poincSeries (cuspCompatible_poincProfile _ (hv k))) _)

theorem inner_onesL2_famL2 {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι) {μ : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k)) (b : ι → ℂ) :
    ⟪onesL2 N, famL2 hσ t s hμ v b⟫_ℂ = 0 := by
  rw [famL2, inner_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [inner_smul_right, ← inner_conj_symm, inner_poincL2_onesL2 (by simpa using hσ) (hμ k) (hv k),
    map_zero, mul_zero]

theorem ae_coeFn_finset_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ι) (c : ι → ℂ) (f : ι → Lp E 2 (volume : Measure ℝ)) :
    ∀ᵐ r : ℝ ∂volume, ((∑ k ∈ s, c k • f k : Lp E 2 (volume : Measure ℝ)) : ℝ → E) r =
      ∑ k ∈ s, c k • (f k : ℝ → E) r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards with r
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (c a • f a) (∑ k ∈ s, c k • f k), Lp.coeFn_smul (c a) (f a), ih]
        with r h1 h2 h3
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, Finset.sum_insert ha]

/-- The Eisenstein coefficients of `F_t`: `2 ⟨T̄F_t(r), e_i⟩ = 2 W(σ+it, ir) B_i(σ, r)`. -/
theorem eisTransformL2_famL2_inner (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι)
    {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k))
    {n : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k) (b : ι → ℂ)
    (i : Fin (Module.finrank ℂ (cuspVecSub N))) :
    ∀ᵐ r : ℝ ∂volume, 2 * ⟪(eisTransformL2 hN (famL2 hσ t s hμ v b) : ℝ → DeckSpace N) r,
      cuspBasisVec N i⟫_ℂ = 2 * whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I) *
        eisSpecCoeff i σ r s μ v n b := by
  have hs : 1 < ((σ : ℂ) - t * Complex.I).re := by simpa using hσ
  have hconj : conj ((σ : ℂ) - t * Complex.I) = (σ : ℂ) + t * Complex.I := by
    simp [map_sub, Complex.conj_ofReal]
  set β : ι → ℂ := fun k => b k * ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))
  set U : ι → DeckL2 N := fun k => toDeckL2 _ (memLp_poincSeries_profile
    (s := (σ : ℂ) - t * Complex.I) hs (hμ k) (v k))
  have hF : eisTransformL2 hN (famL2 hσ t s hμ v b) = ∑ k ∈ s, β k • eisTransformL2 hN (U k) := by
    rw [famL2, map_sum]
    exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
  have hsum := ae_coeFn_finset_sum s β fun k => eisTransformL2 hN (U k)
  have hk : ∀ᵐ r : ℝ ∂volume, ∀ k ∈ s, 2 * ⟪(eisTransformL2 hN (U k) : ℝ → DeckSpace N) r,
      cuspBasisVec N i⟫_ℂ = poincEisPairing ((σ : ℂ) - t * Complex.I) (μ k) (v k) (cuspBasisVec N i)
        (n k) (1 / 2 + r * Complex.I) :=
    (eventually_all_finset s).2 fun k _ =>
      eisTransformL2_poinc_inner hN hs (hμ k) (hv k) (hn k) (isCuspVec_cuspBasisVec i)
  filter_upwards [hsum, hk] with r h1 h2
  rw [hF, h1, sum_inner, Finset.mul_sum, eisSpecCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hks => ?_
  have hx : (0 : ℝ) < 2 * Real.pi * μ k := by have := hμ k; positivity
  have hxc : ((2 * Real.pi * μ k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [inner_smul_left, ← mul_assoc, mul_comm 2, mul_assoc, h2 k hks, poincEisPairing_eq, hconj,
    show (1 / 2 + (r : ℂ) * Complex.I) - 1 / 2 = r * Complex.I by ring]
  simp only [β, map_mul]
  rw [conj_ofReal_cpow_neg_mul_I hx.le]
  have hexp : ((2 * Real.pi * μ k : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) *
      ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2)) =
      ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2)) := by
    rw [← Complex.cpow_add _ _ hxc]; congr 1; ring
  calc conj (b k) * ((2 * Real.pi * μ k : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) *
        (2 * (eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k) *
          ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2)) *
          whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)))
      = 2 * whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I) *
        (conj (b k) * eisCoeff (1 / 2 + r * Complex.I) (v k) (cuspBasisVec N i) (n k) *
          (((2 * Real.pi * μ k : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) *
          ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2)))) := by ring
    _ = _ := by rw [hexp]

/-- **Parseval for `F_t`.** -/
theorem norm_famL2_sq_eq_parseval (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι)
    {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k))
    {n : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k) (b : ι → ℂ) :
    Integrable (fun r : ℝ => ∑ i, ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 *
      ‖eisSpecCoeff i σ r s μ v n b‖ ^ 2) ∧
    ‖famL2 hσ t s hμ v b‖ ^ 2 =
      ∑' j : CuspEigenIndex N, 4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j σ s μ v b‖ ^ 2 +
      Real.pi⁻¹ * ∫ r : ℝ, ∑ i, ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 *
        ‖eisSpecCoeff i σ r s μ v n b‖ ^ 2 := by
  set F := famL2 hσ t s hμ v b
  obtain ⟨hint, hval⟩ := integrable_and_integral_sum_norm_sq hN F
    (fun i => eisTransformL2_famL2_inner hN hσ t s hμ hv hn b i)
  have hΦ : ∀ r : ℝ, ∑ i, ‖2 * whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I) *
      eisSpecCoeff i σ r s μ v n b‖ ^ 2 = 4 * ∑ i, ‖whittMellin ((σ : ℂ) + t * Complex.I)
        (r * Complex.I)‖ ^ 2 * ‖eisSpecCoeff i σ r s μ v n b‖ ^ 2 := fun r => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_two]; ring
  simp_rw [hΦ] at hint hval
  have hint' := hint.const_mul (1 / 4 : ℝ)
  simp_rw [← mul_assoc, show (1 / 4 : ℝ) * 4 = 1 by norm_num, one_mul] at hint'
  refine ⟨hint', ?_⟩
  rw [integral_const_mul] at hval
  have hTF : ‖eisTransformL2 hN F‖ ^ 2 = ∫ r : ℝ, ∑ i, ‖whittMellin ((σ : ℂ) + t * Complex.I)
      (r * Complex.I)‖ ^ 2 * ‖eisSpecCoeff i σ r s μ v n b‖ ^ 2 := by linarith
  have hP := inner_eq_cusp_add_eisTransform hN (famL2_mem_central hσ t s hμ hv b)
    (famL2_mem_central hσ t s hμ hv b) (inner_onesL2_famL2 hσ t s hμ hv b)
  have hj : ∀ j : CuspEigenIndex N, ⟪F, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ *
      ⟪(cuspEigenBasis N j : DeckL2 N), F⟫_ℂ =
      ((4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j σ s μ v b‖ ^ 2 : ℝ) : ℂ) := fun j => by
    rw [← inner_conj_symm, Complex.conj_mul', inner_cuspEigenBasis_famL2 hσ t s hμ hv b j,
      norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, Complex.norm_two]
    push_cast; ring
  have hsum := (summable_and_tsum_norm_whittMellin_sq_mul_le hσ t s hμ hv b).1
  rw [tsum_congr hj, ← Complex.ofReal_tsum, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at hP
  have hP2 : ((‖F‖ ^ 2 : ℝ) : ℂ) = ((∑' j : CuspEigenIndex N, 4 *
      ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 * ‖specCoeff j σ s μ v b‖ ^ 2 +
      Real.pi⁻¹ * ‖eisTransformL2 hN F‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
    exact hP
  rw [Complex.ofReal_injective hP2, hTF]

/-! ## Integration against `g_K` and the limit `σ ↓ 1` -/

theorem lintegral_gaussWeight_mul_norm_famL2_sq {σ K : ℝ} (hσ : 1 < σ) (hK : 0 < K) (s : Finset ι)
    {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k))
    (b : ι → ℂ) :
    ∫⁻ t : ℝ, ENNReal.ofReal (gaussWeight K t * ‖famL2 hσ t s hμ v b‖ ^ 2) =
      ENNReal.ofReal (geomForm σ K s μ v b).re := by
  set G : ℝ → ℂ := fun t => ∑ k ∈ s, ∑ l ∈ s, conj (b k) * b l *
    ((gaussWeight K t : ℂ) * linePair σ t (μ k) (μ l) (v k) (v l)) with hG
  have hI := fun k l => (integrable_and_integral_gaussWeight_mul_linePair hσ hK (hμ k) (hμ l)
    (v k) (v l))
  have hGint : Integrable G := integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    ((hI k l).1.const_mul _)
  have hGval : ∫ t, G t = geomForm σ K s μ v b := by
    rw [hG, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ((hI k l).1.const_mul _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => ((hI k l).1.const_mul _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, (hI k l).2]
  have hFG : ∀ t, gaussWeight K t * ‖famL2 hσ t s hμ v b‖ ^ 2 = (G t).re := fun t => by
    have h := congrArg Complex.re (norm_famL2_sq hσ t s hμ hv b)
    rw [Complex.ofReal_re] at h
    rw [h, hG, ← Complex.re_ofReal_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hFint : Integrable fun t => gaussWeight K t * ‖famL2 hσ t s hμ v b‖ ^ 2 := by
    simp_rw [hFG]; exact hGint.re
  rw [← ofReal_integral_eq_lintegral_ofReal hFint
    (Eventually.of_forall fun t => mul_nonneg (gaussWeight_nonneg K t) (by positivity))]
  simp_rw [hFG]
  have h := integral_re hGint
  simp only [RCLike.re_to_complex] at h
  rw [h, hGval]

theorem measurable_specCoeff_line (lam : ℝ) (hlam : 0 ≤ lam) {σ : ℝ} (hσ : 1 ≤ σ) :
    Measurable fun t : ℝ => ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam)‖ ^ 2 :=
  (measurable_whittMellin_line hlam hσ).norm.pow_const 2

theorem continuousAt_whittMellin_imag {σ t r : ℝ} (hσ : 1 / 2 < σ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ =>
      whittMellin ((p.1 : ℂ) + p.2.1 * Complex.I) (p.2.2 * Complex.I)) (σ, t, r) := by
  unfold whittMellin
  have hG : ∀ (f : ℝ × ℝ × ℝ → ℂ), Continuous f → (∀ m : ℕ, f (σ, t, r) ≠ -(m : ℂ)) →
      ContinuousAt (fun p => Complex.Gamma (f p)) (σ, t, r) := fun f hf hs =>
    (Complex.differentiableAt_Gamma _ hs).continuousAt.comp hf.continuousAt
  have hre : ∀ m : ℕ, ∀ c : ℂ, 0 < c.re → c ≠ -(m : ℂ) := fun m c hc => ne_neg_nat_of_re_pos hc m
  refine ContinuousAt.div (ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_) ?_) ?_
    (Complex.Gamma_ne_zero fun m => hre m _ (by simp; linarith))
  · exact ((by fun_prop : Continuous fun p : ℝ × ℝ × ℝ =>
      (p.1 : ℂ) + p.2.1 * Complex.I - 1 / 2 - 1).const_cpow (Or.inl two_ne_zero)).continuousAt
  · exact hG _ (by fun_prop) fun m => hre m _ (by simp; linarith)
  · exact hG _ (by fun_prop) fun m => hre m _ (by simp; linarith)
  · exact hG _ (by fun_prop) fun m => hre m _ (by simp; linarith)
  · exact hG _ (by fun_prop) fun m => hre m _ (by simp; linarith)

theorem continuous_eisSpecCoeff_sigma (i : Fin (Module.finrank ℂ (cuspVecSub N))) (r : ℝ)
    (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k) (v : ι → DeckSpace N) (n : ι → ℤ)
    (b : ι → ℂ) : Continuous fun σ : ℝ => eisSpecCoeff i σ r s μ v n b := by
  unfold eisSpecCoeff
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  have hx : ((2 * Real.pi * μ k : ℝ) : ℂ) ≠ 0 := by
    have := hμ k; exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi * μ k).ne'
  exact (by fun_prop : Continuous fun σ : ℝ => -((σ : ℂ) - 1 / 2)).const_cpow (Or.inl hx)

theorem aestronglyMeasurable_eisSpecCoeff (i : Fin (Module.finrank ℂ (cuspVecSub N))) (σ : ℝ)
    (s : Finset ι) (μ : ι → ℝ) (v : ι → DeckSpace N) (n : ι → ℤ) (b : ι → ℂ) :
    AEStronglyMeasurable (fun r : ℝ => eisSpecCoeff i σ r s μ v n b) volume := by
  unfold eisSpecCoeff
  exact Finset.aestronglyMeasurable_fun_sum s fun k _ =>
    (aestronglyMeasurable_const.mul (aestronglyMeasurable_eisCoeff_line _ _ _)).mul
      aestronglyMeasurable_const

/-- The continuous-spectrum density `g_K(t) π⁻¹ Σ_i |W(σ+it, ir)|² |B_i(σ, r)|²`. -/
def contDensity (σ K : ℝ) (s : Finset ι) (μ : ι → ℝ) (v : ι → DeckSpace N) (n : ι → ℤ)
    (b : ι → ℂ) (p : ℝ × ℝ) : ℝ :=
  gaussWeight K p.1 * (Real.pi⁻¹ * ∑ i, ‖whittMellin ((σ : ℂ) + p.1 * Complex.I)
    (p.2 * Complex.I)‖ ^ 2 * ‖eisSpecCoeff i σ p.2 s μ v n b‖ ^ 2)

theorem contDensity_nonneg (σ K : ℝ) (s : Finset ι) (μ : ι → ℝ) (v : ι → DeckSpace N)
    (n : ι → ℤ) (b : ι → ℂ) (p : ℝ × ℝ) : 0 ≤ contDensity σ K s μ v n b p :=
  mul_nonneg (gaussWeight_nonneg K p.1) (mul_nonneg (inv_nonneg.2 Real.pi_pos.le)
    (Finset.sum_nonneg fun i _ => by positivity))

theorem aemeasurable_contDensity {σ : ℝ} (hσ : 1 / 2 < σ) (K : ℝ) (s : Finset ι) (μ : ι → ℝ)
    (v : ι → DeckSpace N) (n : ι → ℤ) (b : ι → ℂ) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (contDensity σ K s μ v n b p))
      ((volume : Measure ℝ).prod volume) := by
  refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
  have hg : Continuous fun p : ℝ × ℝ => gaussWeight K p.1 := by unfold gaussWeight; fun_prop
  have hW : Continuous fun p : ℝ × ℝ => whittMellin ((σ : ℂ) + p.1 * Complex.I) (p.2 * Complex.I) :=
    continuous_iff_continuousAt.2 fun p => (continuousAt_whittMellin_imag hσ).comp
      (f := fun p : ℝ × ℝ => (σ, p.1, p.2)) (by fun_prop)
  refine (hg.aestronglyMeasurable.mul (aestronglyMeasurable_const.mul
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_))).aemeasurable
  exact (hW.norm.pow 2).aestronglyMeasurable.mul
    (((aestronglyMeasurable_eisSpecCoeff i σ s μ v n b).norm.pow 2).comp_snd)

/-- **The integrated Parseval inequality at `σ > 1`.** -/
theorem lintegral_parseval_le (hN : 2 ≤ N) {σ K : ℝ} (hσ : 1 < σ) (hK : 0 < K) (s : Finset ι)
    {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k))
    {n : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k) (b : ι → ℂ) :
    (∑' j : CuspEigenIndex N, ∫⁻ t : ℝ, ENNReal.ofReal (gaussWeight K t *
      (4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j σ s μ v b‖ ^ 2))) +
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (contDensity σ K s μ v n b p) ∂((volume : Measure ℝ).prod volume)
      ≤ ENNReal.ofReal (geomForm σ K s μ v b).re := by
  set a : CuspEigenIndex N → ℝ → ℝ := fun j t => gaussWeight K t *
    (4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 * ‖specCoeff j σ s μ v b‖ ^ 2)
    with ha
  have hg : Continuous (gaussWeight K) := by unfold gaussWeight; fun_prop
  have hmeas : ∀ j, Measurable (a j) := fun j =>
    hg.measurable.mul (((measurable_specCoeff_line j.1 (cuspEigenBasis_lam_nonneg j) hσ.le).const_mul
      4).mul_const _)
  have hnn : ∀ j t, 0 ≤ a j t := fun j t => mul_nonneg (gaussWeight_nonneg K t) (by positivity)
  have hL : (∑' j : CuspEigenIndex N, ∫⁻ t : ℝ, ENNReal.ofReal (gaussWeight K t *
      (4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j σ s μ v b‖ ^ 2))) = ∑' j, ∫⁻ t, ENNReal.ofReal (a j t) := rfl
  rw [hL, ← lintegral_gaussWeight_mul_norm_famL2_sq hσ hK s hμ hv b,
    ← lintegral_tsum (f := fun j t => ENNReal.ofReal (a j t))
      fun j => (ENNReal.measurable_ofReal.comp (hmeas j)).aemeasurable,
    lintegral_prod _ (aemeasurable_contDensity (by linarith) K s μ v n b),
    ← lintegral_add_left (f := fun t => ∑' j, ENNReal.ofReal (a j t))
      (Measurable.tsum fun j => ENNReal.measurable_ofReal.comp (hmeas j))]
  refine lintegral_mono fun t => le_of_eq ?_
  obtain ⟨hint, hpar⟩ := norm_famL2_sq_eq_parseval hN hσ t s hμ hv hn b
  have hsum : Summable fun j => a j t := (summable_and_tsum_norm_whittMellin_sq_mul_le hσ t s hμ hv
    b).1.mul_left _
  have hcint : Integrable fun r : ℝ => contDensity σ K s μ v n b (t, r) := by
    simp only [contDensity]
    exact (hint.const_mul _).const_mul _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => hnn j t) hsum,
    ← ofReal_integral_eq_lintegral_ofReal hcint
      (Eventually.of_forall fun r => contDensity_nonneg σ K s μ v n b (t, r)),
    ← ENNReal.ofReal_add (tsum_nonneg fun j => hnn j t)
      (integral_nonneg fun r => contDensity_nonneg σ K s μ v n b (t, r))]
  congr 1
  simp only [ha, contDensity]
  rw [tsum_mul_left, integral_const_mul, integral_const_mul, hpar]
  ring

theorem liminf_add_liminf_le (D C : ℕ → ENNReal) :
    liminf D atTop + liminf C atTop ≤ liminf (fun n => D n + C n) atTop := by
  have h := tsum_liminf_le_liminf_tsum (fun n (x : Bool) => if x then D n else C n)
  simpa [tsum_bool, add_comm] using h

theorem tendsto_whittMellin_imag_sigma (t r : ℝ) :
    Tendsto (fun σ : ℝ => whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)) (𝓝 1)
      (𝓝 (whittMellin (((1 : ℝ) : ℂ) + t * Complex.I) (r * Complex.I))) := by
  have h1 := (continuousAt_whittMellin_imag (σ := 1) (t := t) (r := r) (by norm_num)).tendsto
  have h2 : Tendsto (fun σ : ℝ => ((σ, t, r) : ℝ × ℝ × ℝ)) (𝓝 1) (𝓝 ((1 : ℝ), t, r)) :=
    (by fun_prop : Continuous fun σ : ℝ => ((σ, t, r) : ℝ × ℝ × ℝ)).tendsto 1
  have h3 := h1.comp h2
  simp only [Function.comp_def] at h3
  exact h3

theorem tendsto_contDensity (K : ℝ) (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    (v : ι → DeckSpace N) (n : ι → ℤ) (b : ι → ℂ) (p : ℝ × ℝ) :
    Tendsto (fun σ : ℝ => contDensity σ K s μ v n b p) (𝓝 1) (𝓝 (contDensity 1 K s μ v n b p)) := by
  unfold contDensity
  refine tendsto_const_nhds.mul (tendsto_const_nhds.mul (tendsto_finsetSum _ fun i _ => ?_))
  exact ((tendsto_whittMellin_imag_sigma p.1 p.2).norm.pow 2).mul
    (((continuous_eisSpecCoeff_sigma i p.2 s hμ v n b).tendsto 1).norm.pow 2)

theorem lintegral_contDensity_le_liminf {K : ℝ} (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    (v : ι → DeckSpace N) (n : ι → ℤ) (b : ι → ℂ) {σn : ℕ → ℝ} (hσn : ∀ m, 1 < σn m)
    (hσt : Tendsto σn atTop (𝓝[>] 1)) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (contDensity 1 K s μ v n b p) ∂((volume : Measure ℝ).prod volume) ≤
      liminf (fun m => ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (contDensity (σn m) K s μ v n b p)
        ∂((volume : Measure ℝ).prod volume)) atTop := by
  have hpt : ∀ p : ℝ × ℝ, Tendsto (fun m => ENNReal.ofReal (contDensity (σn m) K s μ v n b p))
      atTop (𝓝 (ENNReal.ofReal (contDensity 1 K s μ v n b p))) := fun p =>
    ENNReal.tendsto_ofReal ((tendsto_contDensity K s hμ v n b p).comp
      (hσt.mono_right nhdsWithin_le_nhds))
  calc ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (contDensity 1 K s μ v n b p) ∂((volume : Measure ℝ).prod volume)
      = ∫⁻ p : ℝ × ℝ, liminf (fun m => ENNReal.ofReal (contDensity (σn m) K s μ v n b p)) atTop
          ∂((volume : Measure ℝ).prod volume) :=
        lintegral_congr fun p => ((hpt p).liminf_eq).symm
    _ ≤ _ := lintegral_liminf_le' fun m => aemeasurable_contDensity (by linarith [hσn m]) K s μ v n b

theorem tsum_lintegral_one_le_liminf {K : ℝ} (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    (v : ι → DeckSpace N) (b : ι → ℂ) {σn : ℕ → ℝ} (hσn : ∀ m, 1 < σn m)
    (hσt : Tendsto σn atTop (𝓝[>] 1)) :
    ∑' j : CuspEigenIndex N, ∫⁻ t : ℝ, ENNReal.ofReal (gaussWeight K t *
      (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j 1 s μ v b‖ ^ 2)) ≤
      liminf (fun m => ∑' j : CuspEigenIndex N, ∫⁻ t : ℝ, ENNReal.ofReal (gaussWeight K t *
        (4 * ‖whittMellin ((σn m : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
          ‖specCoeff j (σn m) s μ v b‖ ^ 2))) atTop := by
  set F : ℕ → CuspEigenIndex N → ℝ → ENNReal := fun m j t => ENNReal.ofReal (gaussWeight K t *
    (4 * ‖whittMellin ((σn m : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
      ‖specCoeff j (σn m) s μ v b‖ ^ 2))
  set f : CuspEigenIndex N → ℝ → ENNReal := fun j t => ENNReal.ofReal (gaussWeight K t *
    (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
      ‖specCoeff j 1 s μ v b‖ ^ 2))
  have hg : Continuous (gaussWeight K) := by unfold gaussWeight; fun_prop
  have hconv : ∀ j, ∀ t : ℝ, t ≠ 0 → Tendsto (fun m => F m j t) atTop (𝓝 (f j t)) := by
    intro j t ht
    have hW : Tendsto (fun σ : ℝ => whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)) (𝓝 1)
        (𝓝 (whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1))) :=
      (continuousAt_whittMellin_specParam (cuspEigenBasis_lam_nonneg j) le_rfl (Or.inl ht)).tendsto.comp
        ((by fun_prop : Continuous fun σ : ℝ => (σ : ℂ) + t * Complex.I).tendsto 1)
    have hA := (continuous_specCoeff j s hμ v b).tendsto 1
    exact ENNReal.tendsto_ofReal (((((hW.norm.pow 2).const_mul 4).mul (hA.norm.pow 2)).const_mul
      (gaussWeight K t)).comp (hσt.mono_right nhdsWithin_le_nhds))
  have hmeasF : ∀ m j, Measurable (F m j) := fun m j =>
    ENNReal.measurable_ofReal.comp (hg.measurable.mul
      ((((measurable_whittMellin_line (cuspEigenBasis_lam_nonneg j) (hσn m).le).norm.pow_const
        2).const_mul 4).mul_const _))
  have hfatou : ∀ j, ∫⁻ t, f j t ≤ liminf (fun m => ∫⁻ t, F m j t) atTop := by
    intro j
    have hae : (fun t => f j t) =ᵐ[volume] fun t => liminf (fun m => F m j t) atTop := by
      have h0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
        rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
        exact measure_singleton 0
      filter_upwards [h0] with t ht
      exact ((hconv j t ht).liminf_eq).symm
    rw [lintegral_congr_ae hae]
    exact lintegral_liminf_le fun m => hmeasF m j
  exact (ENNReal.tsum_le_tsum hfatou).trans (tsum_liminf_le_liminf_tsum _)

/-- **The integrated Parseval inequality at `σ = 1`.** -/
theorem lintegral_parseval_le_one (hN : 2 ≤ N) {K : ℝ} (hK : 0 < K) (s : Finset ι) {μ : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k))
    {n : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k) (b : ι → ℂ) :
    (∑' j : CuspEigenIndex N, ∫⁻ t : ℝ, ENNReal.ofReal (gaussWeight K t *
      (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j 1 s μ v b‖ ^ 2))) +
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (contDensity 1 K s μ v n b p) ∂((volume : Measure ℝ).prod volume)
      ≤ ENNReal.ofReal (geomForm 1 K s μ v b).re := by
  set σn : ℕ → ℝ := fun m => 1 + 1 / ((m : ℝ) + 1)
  have hσn : ∀ m, 1 < σn m := fun m => by
    simp only [σn]; have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  have hσt : Tendsto σn atTop (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hσn⟩
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    simpa [σn] using this
  have hgeom : Tendsto (fun m => ENNReal.ofReal (geomForm (σn m) K s μ v b).re) atTop
      (𝓝 (ENNReal.ofReal (geomForm 1 K s μ v b).re)) :=
    ENNReal.tendsto_ofReal ((Complex.continuous_re.tendsto _).comp
      ((tendsto_geomForm hK s hμ v b).comp hσt))
  refine (add_le_add (tsum_lintegral_one_le_liminf s hμ v b hσn hσt)
    (lintegral_contDensity_le_liminf (K := K) s hμ v n b hσn hσt)).trans
    ((liminf_add_liminf_le _ _).trans ?_)
  refine (liminf_le_liminf (Eventually.of_forall fun m =>
    lintegral_parseval_le hN (hσn m) hK s hμ hv hn b)).trans (le_of_eq hgeom.liminf_eq)

/-! ## The full large-sieve inequality -/

theorem whittMellin_mul_I_eq_abs (b : ℂ) (r : ℝ) :
    whittMellin b ((r : ℂ) * Complex.I) = whittMellin b (Complex.I * (|r| : ℝ)) := by
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr, mul_comm]
  · rw [abs_of_neg hr, ← whittMellin_neg]; congr 1; push_cast; ring

/-- `∫ contDensity(t, r) dt ≥ (4π)⁻¹ c₀ (|r|+1) e^{−π|r|} Σ_i |B_i(1, r)|²` for `|r| ≤ K`. -/
theorem lintegral_contDensity_ge {K r : ℝ} (hK : 1 ≤ K) (hr : |r| ≤ K) (s : Finset ι)
    (μ : ι → ℝ) (v : ι → DeckSpace N) (n : ι → ℤ) (b : ι → ℂ) :
    ENNReal.ofReal ((4 * Real.pi)⁻¹ * (specWeightConst * (|r| + 1) * Real.exp (-(Real.pi * |r|))) *
      ∑ i, ‖eisSpecCoeff i 1 r s μ v n b‖ ^ 2) ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (contDensity 1 K s μ v n b (t, r)) := by
  set Y : ℝ := (4 * Real.pi)⁻¹ * ∑ i, ‖eisSpecCoeff i 1 r s μ v n b‖ ^ 2
  have hY : 0 ≤ Y := mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => by positivity)
  have hpt : ∀ t : ℝ, ENNReal.ofReal (contDensity 1 K s μ v n b (t, r)) =
      ENNReal.ofReal (gaussWeight K t *
        (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (Complex.I * (|r| : ℝ))‖ ^ 2)) *
        ENNReal.ofReal Y := fun t => by
    rw [← ENNReal.ofReal_mul (mul_nonneg (gaussWeight_nonneg K t) (by positivity))]
    congr 1
    simp only [contDensity, Y, ← whittMellin_mul_I_eq_abs]
    rw [← Finset.mul_sum]
    field_simp
  simp_rw [hpt]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, show (4 * Real.pi)⁻¹ *
    (specWeightConst * (|r| + 1) * Real.exp (-(Real.pi * |r|))) *
      ∑ i, ‖eisSpecCoeff i 1 r s μ v n b‖ ^ 2 =
    (specWeightConst * (|r| + 1) * Real.exp (-(Real.pi * |r|))) * Y by simp only [Y]; ring,
    ENNReal.ofReal_mul (by have := specWeightConst_pos; positivity)]
  exact mul_le_mul_left (lintegral_gaussWeight_mul_whittMellin_imag_ge hK (abs_nonneg r) hr) _

/-- **The large-sieve inequality for the full spectrum** (`K ≥ 1`):
`Σ_j c₀(κ_j+1)e^{−πκ_j}[λ_j ≤ ¼+K²] |A_j|² + (4π)⁻¹ ∫_{−K}^{K} c₀(|r|+1)e^{−π|r|} Σ_i |B_i(r)|² dr
  ≤ |Σ_{k,l} b̄_k b_l geomRow_{kl}(1, K)|`. -/
theorem large_sieve_full (hN : 2 ≤ N) {K : ℝ} (hK : 1 ≤ K) (s : Finset ι) {μ : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k))
    {n : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k) (b : ι → ℂ) :
    (∑' j : CuspEigenIndex N, ENNReal.ofReal (sieveWeight K j.1 * ‖specCoeff j 1 s μ v b‖ ^ 2)) +
      ∫⁻ r in Icc (-K) K, ENNReal.ofReal ((4 * Real.pi)⁻¹ *
        (specWeightConst * (|r| + 1) * Real.exp (-(Real.pi * |r|))) *
          ∑ i, ‖eisSpecCoeff i 1 r s μ v n b‖ ^ 2)
      ≤ ENNReal.ofReal ‖geomForm 1 K s μ v b‖ := by
  have hK0 : 0 < K := by linarith
  refine le_trans ?_ ((lintegral_parseval_le_one hN hK0 s hμ hv hn b).trans
    (ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)))
  refine add_le_add (ENNReal.tsum_le_tsum fun j => ?_) ?_
  · have hpt : ∀ t : ℝ, ENNReal.ofReal (gaussWeight K t *
        (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
          ‖specCoeff j 1 s μ v b‖ ^ 2)) =
        ENNReal.ofReal (gaussWeight K t *
          (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2)) *
          ENNReal.ofReal (‖specCoeff j 1 s μ v b‖ ^ 2) := fun t => by
      rw [← ENNReal.ofReal_mul (mul_nonneg (gaussWeight_nonneg K t) (by positivity))]
      ring_nf
    simp_rw [hpt]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_mul (sieveWeight_nonneg K j.1)]
    refine mul_le_mul_left ?_ _
    unfold sieveWeight
    split_ifs with h
    · exact lintegral_gaussWeight_mul_whittMellin_ge hK h
    · simp
  · rw [lintegral_prod_symm _ (aemeasurable_contDensity (by norm_num) K s μ v n b)]
    refine (setLIntegral_mono' measurableSet_Icc fun r hr => ?_).trans
      (setLIntegral_le_lintegral _ _)
    exact lintegral_contDensity_ge hK (abs_le.2 ⟨by linarith [hr.1], hr.2⟩) s μ v n b

end

end GaloisForLFunctions.RHTower.DeckPointPair
