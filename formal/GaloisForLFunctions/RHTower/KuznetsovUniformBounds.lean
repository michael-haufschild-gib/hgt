import GaloisForLFunctions.RHTower.KuznetsovBesselIdentity

/-!
# Uniform bounds for the spectral data on vertical lines

The Poincaré series `U(·|s, μ, v)` and the conjugate series `P(·|h̄_{s,ν}, w)` are dominated by
`‖v‖ A_{Re s}` resp. `‖w‖ A_{Re s}` with the majorant `A_σ = Σ_p |h_{σ,μ}(M_p ·)|`, so their `L²`
norms are bounded on every vertical line (`norm_poincL2_le`, `norm_conjL2_le`).  Bessel's inequality
for the cuspidal eigenbasis and Parseval on the full spectrum (`‖T̄f‖² ≤ π‖f‖²`,
`norm_eisTransformL2_sq_le`) then bound the spectral coefficients uniformly on the line:

`Σ_j |ρ_j(v)| |ρ_j(w)| |W(σ+it, ν_j)|² ≤ D`  for all real `t`         (`tsum_cuspCoeff_line_le`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex EisensteinSeries
open scoped MatrixGroups ComplexConjugate InnerProductSpace ENNReal

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry MaassWhittaker

noncomputable section

variable {N : ℕ}

/-! ## `L²` bounds on vertical lines -/

/-- `‖A_σ‖₂` for the majorant `A_σ(z) = Σ_p |h_{σ,μ}(M_p z)|`. -/
def poincMajorantNorm (σ μ : ℝ) : ℝ :=
  (eLpNorm (fun z : ℍ => ∑' p : gammaSet 1 1 0, ‖poincProfile (σ : ℂ) μ (gammaSetMatrix p • z)‖) 2
    cellMeasure).toReal

theorem poincMajorantNorm_nonneg (σ μ : ℝ) : 0 ≤ poincMajorantNorm σ μ := ENNReal.toReal_nonneg

theorem norm_toDeckL2_le_of_le {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) {g : ℍ → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (hg : MemLp g 2 cellMeasure) (h : ∀ z, ‖F z‖ ≤ c * g z) :
    ‖toDeckL2 F hF‖ ≤ c * (eLpNorm g 2 cellMeasure).toReal := by
  rw [toDeckL2, Lp.norm_toLp]
  have h1 : eLpNorm F 2 cellMeasure ≤ eLpNorm (c • g) 2 cellMeasure :=
    eLpNorm_mono_real fun z => by simpa [smul_eq_mul] using h z
  rw [eLpNorm_const_smul] at h1
  have hfin : ‖c‖ₑ * eLpNorm g 2 cellMeasure ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hg.eLpNorm_ne_top
  calc (eLpNorm F 2 cellMeasure).toReal ≤ (‖c‖ₑ * eLpNorm g 2 cellMeasure).toReal :=
        ENNReal.toReal_mono hfin h1
    _ = c * (eLpNorm g 2 cellMeasure).toReal := by
        rw [ENNReal.toReal_mul, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg hc]

theorem norm_poincProfile_re (s : ℂ) (μ : ℝ) (w : ℍ) :
    ‖poincProfile s μ w‖ = ‖poincProfile (s.re : ℂ) μ w‖ := by
  rw [norm_poincProfile, norm_poincProfile, Complex.ofReal_re]

/-- **`‖U(·|s, μ, v)‖ ≤ ‖v‖ ‖A_{Re s}‖₂`.** -/
theorem norm_poincL2_le {s : ℂ} (hs : 1 < s.re) {μ : ℝ} (hμ : 0 < μ) (v : DeckSpace N) :
    ‖toDeckL2 _ (memLp_poincSeries_profile hs hμ v)‖ ≤ ‖v‖ * poincMajorantNorm s.re μ := by
  have hs' : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  refine norm_toDeckL2_le_of_le _ (norm_nonneg v) (memLp_tsum_norm_poincProfile hs' hμ)
    fun z => ?_
  refine (norm_poincSeries_le _ v (summable_norm_poincProfile hs hμ.le z)).trans_eq ?_
  simp_rw [norm_poincProfile_re s μ]

/-- **`‖P(·|h̄_{s,ν}, w)‖ ≤ ‖w‖ ‖A_{Re s}‖₂`.** -/
theorem norm_conjL2_le {s : ℂ} (hs : 1 < s.re) {ν : ℝ} (hν : 0 < ν) (w : DeckSpace N) :
    ‖toDeckL2 _ (memLp_poincSeries_conjProfile hs hν w)‖ ≤ ‖w‖ * poincMajorantNorm s.re ν := by
  have hs' : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
  refine norm_toDeckL2_le_of_le _ (norm_nonneg w) (memLp_tsum_norm_poincProfile hs' hν)
    fun z => ?_
  refine (norm_poincSeries_le _ w (summable_norm_conjProfile hs hν.le z)).trans_eq ?_
  simp_rw [norm_conjProfile, norm_poincProfile_re s ν]

/-! ## Bessel's inequality and Parseval -/

theorem orthonormal_cuspEigenBasis :
    Orthonormal ℂ (fun j : CuspEigenIndex N => (cuspEigenBasis N j : DeckL2 N)) :=
  (cuspEigenBasis N).orthonormal.comp_linearIsometry (cuspidalL2Closure N).subtypeₗᵢ

theorem norm_inner_mul_inner_le (a b : ℂ) : ‖conj a * b‖ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- `Σ_j |⟨f, u_j⟩ ⟨u_j, g⟩|` converges and is at most `(‖f‖² + ‖g‖²)/2`. -/
theorem summable_and_tsum_norm_inner_cusp_le (f g : DeckL2 N) :
    Summable (fun j : CuspEigenIndex N =>
      ‖⟪f, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ * ⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ‖) ∧
    ∑' j : CuspEigenIndex N,
      ‖⟪f, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ * ⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ‖ ≤
        (‖f‖ ^ 2 + ‖g‖ ^ 2) / 2 := by
  have ho := orthonormal_cuspEigenBasis (N := N)
  have hf := ho.inner_products_summable f
  have hg := ho.inner_products_summable g
  have hpt : ∀ j : CuspEigenIndex N,
      ‖⟪f, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ * ⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ‖ ≤
        (‖⟪(cuspEigenBasis N j : DeckL2 N), f⟫_ℂ‖ ^ 2 +
          ‖⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ‖ ^ 2) / 2 := fun j => by
    rw [← inner_conj_symm]; exact norm_inner_mul_inner_le _ _
  have hs : Summable (fun j : CuspEigenIndex N =>
      (‖⟪(cuspEigenBasis N j : DeckL2 N), f⟫_ℂ‖ ^ 2 +
        ‖⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ‖ ^ 2) / 2) := (hf.add hg).div_const 2
  refine ⟨hs.of_nonneg_of_le (fun _ => norm_nonneg _) hpt, ?_⟩
  calc ∑' j, ‖⟪f, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ * ⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ‖
      ≤ ∑' j : CuspEigenIndex N, (‖⟪(cuspEigenBasis N j : DeckL2 N), f⟫_ℂ‖ ^ 2 +
          ‖⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ‖ ^ 2) / 2 :=
        (hs.of_nonneg_of_le (fun _ => norm_nonneg _) hpt).tsum_le_tsum hpt hs
    _ = ((∑' j : CuspEigenIndex N, ‖⟪(cuspEigenBasis N j : DeckL2 N), f⟫_ℂ‖ ^ 2) +
          ∑' j : CuspEigenIndex N, ‖⟪(cuspEigenBasis N j : DeckL2 N), g⟫_ℂ‖ ^ 2) / 2 := by
        rw [tsum_div_const, hf.tsum_add hg]
    _ ≤ (‖f‖ ^ 2 + ‖g‖ ^ 2) / 2 := by
        have := ho.tsum_inner_products_le f
        have := ho.tsum_inner_products_le g
        linarith

/-- **`‖T̄f‖² ≤ π‖f‖²`** for central `f ⊥ 𝟙`. -/
theorem norm_eisTransformL2_sq_le (hN : 2 ≤ N) {f : DeckL2 N} (hf : f ∈ deckCentralFixedL2 N)
    (h1 : ⟪onesL2 N, f⟫_ℂ = 0) :
    ‖eisTransformL2 hN f‖ ^ 2 ≤ Real.pi * ‖f‖ ^ 2 := by
  have h := inner_eq_cusp_add_eisTransform hN hf hf h1
  have ho := orthonormal_cuspEigenBasis (N := N)
  have hsum := ho.inner_products_summable f
  have hterm : ∀ j : CuspEigenIndex N,
      ⟪f, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ * ⟪(cuspEigenBasis N j : DeckL2 N), f⟫_ℂ =
        ((‖⟪(cuspEigenBasis N j : DeckL2 N), f⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun j => by
    rw [← inner_conj_symm, Complex.conj_mul', Complex.ofReal_pow]
  simp_rw [hterm] at h
  rw [← Complex.ofReal_tsum, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  set S := ∑' j : CuspEigenIndex N, ‖⟪(cuspEigenBasis N j : DeckL2 N), f⟫_ℂ‖ ^ 2
  have hpos : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hreal : ‖f‖ ^ 2 = S + Real.pi⁻¹ * ‖eisTransformL2 hN f‖ ^ 2 := by
    have h' : ((‖f‖ ^ 2 : ℝ) : ℂ) = ((S + Real.pi⁻¹ * ‖eisTransformL2 hN f‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; exact h
    exact_mod_cast h'
  have hπ := Real.pi_pos
  have : Real.pi⁻¹ * ‖eisTransformL2 hN f‖ ^ 2 ≤ ‖f‖ ^ 2 := by linarith
  rwa [inv_mul_le_iff₀ hπ] at this

/-! ## The discrete spectrum on a vertical line -/

theorem norm_two_pi_cpow (σ t : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ‖((2 * Real.pi * μ : ℝ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I - 1 / 2))‖ =
      (2 * Real.pi * μ) ^ (1 / 2 - σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  congr 1; simp

theorem norm_two_pi_cpow' (σ t : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ‖((2 * Real.pi * μ : ℝ) : ℂ) ^ (-((σ : ℂ) - t * Complex.I - 1 / 2))‖ =
      (2 * Real.pi * μ) ^ (1 / 2 - σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  congr 1; simp

theorem norm_whittMellin_conj_line (σ t : ℝ) (ν : ℂ) (hν : conj ν = ν ∨ conj ν = -ν) :
    ‖whittMellin ((σ : ℂ) - t * Complex.I) ν‖ = ‖whittMellin ((σ : ℂ) + t * Complex.I) ν‖ := by
  rw [← Complex.norm_conj (whittMellin ((σ : ℂ) + t * Complex.I) ν), conj_whittMellin,
    conj_ofReal_add_mul_I]
  rcases hν with h | h
  · rw [h]
  · rw [h, whittMellin_neg]

/-- **The product of the two cusp coefficients on the line** in terms of inner products. -/
theorem norm_cuspCoeff_line_eq {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    {v w : DeckSpace N} (hv : IsCuspEigen μ v) (hw : IsCuspEigen (-ν) w) (j : CuspEigenIndex N) :
    ‖cuspCoeff j μ v‖ * ‖cuspCoeff j (-ν) w‖ *
        ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 =
      ‖⟪toDeckL2 _ (memLp_poincSeries_profile (s := (σ : ℂ) - t * Complex.I) (by simpa using hσ)
          hμ v), (cuspEigenBasis N j : DeckL2 N)⟫_ℂ *
        ⟪(cuspEigenBasis N j : DeckL2 N), toDeckL2 _ (memLp_poincSeries_conjProfile
          (s := (σ : ℂ) + t * Complex.I) (by simpa using hσ) hν w)⟫_ℂ‖ /
        (4 * (2 * Real.pi * μ) ^ (1 / 2 - σ) * (2 * Real.pi * ν) ^ (1 / 2 - σ)) := by
  rw [inner_poincL2_cuspEigenBasis (by simpa using hσ) hμ hv j,
    inner_cuspEigenBasis_conjL2 (by simpa using hσ) hν hw j, conj_ofReal_sub_mul_I,
    conj_ofReal_add_mul_I]
  have hW := norm_whittMellin_conj_line σ t (specParam j.1) (conj_specParam j.1)
  simp only [norm_mul, Complex.norm_conj, norm_two_pi_cpow σ t hμ, norm_two_pi_cpow' σ t hν, hW,
    Complex.norm_two]
  have h1 : 0 < (2 * Real.pi * μ) ^ (1 / 2 - σ) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : 0 < (2 * Real.pi * ν) ^ (1 / 2 - σ) := Real.rpow_pos_of_pos (by positivity) _
  field_simp
  ring

/-- **Uniform bound on a vertical line**:
`Σ_j |ρ_j(v)| |ρ_j(w)| |W(σ+it, ν_j)|² ≤ D` for every real `t`. -/
theorem summable_and_tsum_cuspCoeff_line_le {σ : ℝ} (hσ : 1 < σ) {μ ν : ℝ} (hμ : 0 < μ)
    (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v) (hw : IsCuspEigen (-ν) w) (t : ℝ) :
    Summable (fun j : CuspEigenIndex N => ‖cuspCoeff j μ v‖ * ‖cuspCoeff j (-ν) w‖ *
        ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2) ∧
      ∑' j : CuspEigenIndex N, ‖cuspCoeff j μ v‖ * ‖cuspCoeff j (-ν) w‖ *
          ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 ≤
        ((‖v‖ * poincMajorantNorm σ μ) ^ 2 + (‖w‖ * poincMajorantNorm σ ν) ^ 2) / 2 /
          (4 * (2 * Real.pi * μ) ^ (1 / 2 - σ) * (2 * Real.pi * ν) ^ (1 / 2 - σ)) := by
  have hs₁ : 1 < ((σ : ℂ) - t * Complex.I).re := by simpa using hσ
  have hs₂ : 1 < ((σ : ℂ) + t * Complex.I).re := by simpa using hσ
  set U := toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v)
  set P := toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w)
  obtain ⟨hsum, hle⟩ := summable_and_tsum_norm_inner_cusp_le U P
  have hc : 0 < 4 * (2 * Real.pi * μ) ^ (1 / 2 - σ) * (2 * Real.pi * ν) ^ (1 / 2 - σ) := by
    have h1 : 0 < (2 * Real.pi * μ) ^ (1 / 2 - σ) := Real.rpow_pos_of_pos (by positivity) _
    have h2 : 0 < (2 * Real.pi * ν) ^ (1 / 2 - σ) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  have heq := fun j => norm_cuspCoeff_line_eq hσ t hμ hν hv hw (N := N) j
  simp_rw [heq]
  refine ⟨hsum.div_const _, ?_⟩
  rw [tsum_div_const]
  refine div_le_div_of_nonneg_right (hle.trans ?_) hc.le
  have hU : ‖U‖ ≤ ‖v‖ * poincMajorantNorm σ μ := by
    have h := norm_poincL2_le hs₁ hμ v; simpa using h
  have hP : ‖P‖ ≤ ‖w‖ * poincMajorantNorm σ ν := by
    have h := norm_conjL2_le hs₂ hν w; simpa using h
  have hU0 := norm_nonneg U
  have hP0 := norm_nonneg P
  have := pow_le_pow_left₀ hU0 hU 2
  have := pow_le_pow_left₀ hP0 hP 2
  linarith

/-! ## The continuous spectrum on a vertical line -/

/-- **Parseval in `V_∞`.** -/
theorem sum_norm_inner_cuspBasisVec_sq {x : DeckSpace N} (hx : IsCuspVec x) :
    ∑ i, ‖⟪x, cuspBasisVec N i⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := (cuspBasis N).sum_sq_norm_inner_left (⟨x, hx⟩ : cuspVecSub N)
  simp only [Submodule.coe_inner, Submodule.coe_norm] at h
  exact h

/-- If `2⟨T̄F(r), e_i⟩ = Φ_i(r)` almost everywhere, then `∫ Σ_i |Φ_i|² = 4‖T̄F‖²`. -/
theorem integrable_and_integral_sum_norm_sq (hN : 2 ≤ N) (F : DeckL2 N)
    {Φ : Fin (Module.finrank ℂ (cuspVecSub N)) → ℝ → ℂ}
    (hΦ : ∀ i, ∀ᵐ r : ℝ ∂volume,
      2 * ⟪(eisTransformL2 hN F : ℝ → DeckSpace N) r, cuspBasisVec N i⟫_ℂ = Φ i r) :
    Integrable (fun r : ℝ => ∑ i, ‖Φ i r‖ ^ 2) ∧
      ∫ r : ℝ, ∑ i, ‖Φ i r‖ ^ 2 = 4 * ‖eisTransformL2 hN F‖ ^ 2 := by
  set X := eisTransformL2 hN F
  have hX := eisTransformL2_mem_symSpace hN F
  have hae : (fun r : ℝ => ∑ i, ‖Φ i r‖ ^ 2) =ᵐ[volume]
      fun r => 4 * ‖(X : ℝ → DeckSpace N) r‖ ^ 2 := by
    filter_upwards [hX, ae_all_iff.2 hΦ] with r h1 h2
    rw [← sum_norm_inner_cuspBasisVec_sq h1.1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← h2 i, norm_mul, Complex.norm_two]; ring
  have hint : Integrable (fun r : ℝ => 4 * ‖(X : ℝ → DeckSpace N) r‖ ^ 2) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp X).1).1 (Lp.memLp X)).const_mul 4
  refine ⟨hint.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul]
  congr 1
  have h := L2.inner_def (𝕜 := ℂ) X X
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : ∀ r, ⟪(X : ℝ → DeckSpace N) r, (X : ℝ → DeckSpace N) r⟫_ℂ =
      ((‖(X : ℝ → DeckSpace N) r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [h'] at h
  rw [integral_complex_ofReal] at h
  norm_cast at h
  exact Complex.ofReal_injective h.symm

theorem norm_poincEisPairing_line {σ : ℝ} (t : ℝ) {μ : ℝ} (hμ : 0 < μ) (v w : DeckSpace N) (n : ℤ)
    (r : ℝ) :
    ‖poincEisPairing ((σ : ℂ) - t * Complex.I) μ v w n (1 / 2 + r * Complex.I)‖ =
      2 * ‖eisCoeff (1 / 2 + r * Complex.I) v w n‖ * (2 * Real.pi * μ) ^ (1 / 2 - σ) *
        ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ := by
  rw [poincEisPairing_eq, conj_ofReal_sub_mul_I, show (1 / 2 + (r : ℂ) * Complex.I) - 1 / 2 =
    r * Complex.I by ring]
  simp only [norm_mul, Complex.norm_two, norm_two_pi_cpow σ t hμ]
  ring

theorem norm_conjEisPairing_line {σ : ℝ} (t : ℝ) {ν : ℝ} (hν : 0 < ν) (v w : DeckSpace N) (m : ℤ)
    (r : ℝ) :
    ‖poincEisPairing (conj ((σ : ℂ) + t * Complex.I)) ν v w m (1 / 2 + r * Complex.I)‖ =
      2 * ‖eisCoeff (1 / 2 + r * Complex.I) v w m‖ * (2 * Real.pi * ν) ^ (1 / 2 - σ) *
        ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ := by
  rw [poincEisPairing_eq, Complex.conj_conj, show (1 / 2 + (r : ℂ) * Complex.I) - 1 / 2 =
    r * Complex.I by ring]
  simp only [norm_mul, Complex.norm_two, norm_two_pi_cpow σ t hν]
  ring

/-- **Uniform bound for the continuous spectrum on a vertical line**. -/
theorem integrable_and_integral_eisCoeff_line_le (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) {μ ν : ℝ}
    (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v) (hw : IsCuspEigen (-ν) w)
    {n m : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n) (hm : -ν * ((N + 1 : ℕ) : ℝ) = m) (t : ℝ) :
    Integrable (fun r : ℝ => ∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ *
        ‖eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m‖ *
        ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2) ∧
      ∫ r : ℝ, ∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ *
          ‖eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m‖ *
          ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 ≤
        Real.pi * ((‖v‖ * poincMajorantNorm σ μ) ^ 2 + (‖w‖ * poincMajorantNorm σ ν) ^ 2) /
          (2 * ((2 * Real.pi * μ) ^ (1 / 2 - σ) * (2 * Real.pi * ν) ^ (1 / 2 - σ))) := by
  have hs₁ : 1 < ((σ : ℂ) - t * Complex.I).re := by simpa using hσ
  have hs₂ : 1 < ((σ : ℂ) + t * Complex.I).re := by simpa using hσ
  set U := toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v)
  set P := toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w)
  set ΦU : Fin (Module.finrank ℂ (cuspVecSub N)) → ℝ → ℂ := fun i r =>
    poincEisPairing ((σ : ℂ) - t * Complex.I) μ v (cuspBasisVec N i) n (1 / 2 + r * Complex.I)
  set ΦP : Fin (Module.finrank ℂ (cuspVecSub N)) → ℝ → ℂ := fun i r =>
    poincEisPairing (conj ((σ : ℂ) + t * Complex.I)) ν w (cuspBasisVec N i) m (1 / 2 + r * Complex.I)
  obtain ⟨hUi, hUe⟩ := integrable_and_integral_sum_norm_sq hN U (Φ := ΦU) fun i =>
    eisTransformL2_poinc_inner hN hs₁ hμ hv hn (isCuspVec_cuspBasisVec i)
  obtain ⟨hPi, hPe⟩ := integrable_and_integral_sum_norm_sq hN P (Φ := ΦP) fun i =>
    eisTransformL2_conj_inner hN hs₂ hν hw hm (isCuspVec_cuspBasisVec i)
  set c : ℝ := (2 * Real.pi * μ) ^ (1 / 2 - σ) * (2 * Real.pi * ν) ^ (1 / 2 - σ)
  have hc : 0 < c := mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos (by positivity) _)
  have hpt : ∀ r : ℝ, (∑ i, ‖eisCoeff (1 / 2 + r * Complex.I) v (cuspBasisVec N i) n‖ *
      ‖eisCoeff (1 / 2 + r * Complex.I) w (cuspBasisVec N i) m‖ *
      ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2) =
      (4 * c)⁻¹ * ∑ i, ‖ΦU i r‖ * ‖ΦP i r‖ := fun r => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ΦU, ΦP]
    rw [norm_poincEisPairing_line t hμ, norm_conjEisPairing_line t hν]
    field_simp
    simp only [c]
    ring_nf
  have hle : ∀ r : ℝ, ∑ i, ‖ΦU i r‖ * ‖ΦP i r‖ ≤
      (∑ i, ‖ΦU i r‖ ^ 2 + ∑ i, ‖ΦP i r‖ ^ 2) / 2 := fun r => by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [sq_nonneg (‖ΦU i r‖ - ‖ΦP i r‖)]
  have hmeas : ∀ i, AEStronglyMeasurable (fun r => ‖ΦU i r‖ * ‖ΦP i r‖) volume := fun i =>
    ((memLp_poincEisPairing_half hs₁ μ v (cuspBasisVec N i)
        (int_ne_zero_of_mul_eq hμ.ne' hn)).1.norm).mul
      ((memLp_poincEisPairing_half (by rwa [Complex.conj_re]) ν w (cuspBasisVec N i)
        (int_ne_zero_of_mul_eq (neg_ne_zero.mpr hν.ne') hm)).1.norm)
  have hdom : Integrable (fun r => ∑ i, ‖ΦU i r‖ * ‖ΦP i r‖) := by
    refine ((hUi.add hPi).div_const 2).mono'
      (Finset.aestronglyMeasurable_fun_sum _ fun i _ => hmeas i)
      (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
    exact hle r
  simp_rw [hpt]
  refine ⟨hdom.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hint : ∫ r, ∑ i, ‖ΦU i r‖ * ‖ΦP i r‖ ≤
      ((∫ r, ∑ i, ‖ΦU i r‖ ^ 2) + ∫ r, ∑ i, ‖ΦP i r‖ ^ 2) / 2 := by
    rw [← integral_add hUi hPi, ← integral_div]
    exact integral_mono hdom ((hUi.add hPi).div_const 2) hle
  rw [hUe, hPe] at hint
  have hTU := norm_eisTransformL2_sq_le hN
    (toDeckL2_mem_deckCentralFixedL2 (deckEquivariant_poincSeries (cuspCompatible_poincProfile _ hv)) _)
    (by rw [← inner_conj_symm, inner_poincL2_onesL2 hs₁ hμ hv, map_zero])
  have hTP := norm_eisTransformL2_sq_le hN
    (toDeckL2_mem_deckCentralFixedL2 (deckEquivariant_poincSeries (cuspCompatible_conjProfile _ hw)) _)
    (by rw [← inner_conj_symm, inner_conjL2_onesL2 hs₂ hν hw, map_zero])
  have hU : ‖U‖ ≤ ‖v‖ * poincMajorantNorm σ μ := by
    have h := norm_poincL2_le hs₁ hμ v; simpa using h
  have hP : ‖P‖ ≤ ‖w‖ * poincMajorantNorm σ ν := by
    have h := norm_conjL2_le hs₂ hν w; simpa using h
  have hU2 := pow_le_pow_left₀ (norm_nonneg U) hU 2
  have hP2 := pow_le_pow_left₀ (norm_nonneg P) hP 2
  rw [inv_mul_le_iff₀ (by positivity)]
  have hπ := Real.pi_pos
  have : ∫ r, ∑ i, ‖ΦU i r‖ * ‖ΦP i r‖ ≤
      2 * (Real.pi * ((‖v‖ * poincMajorantNorm σ μ) ^ 2 + (‖w‖ * poincMajorantNorm σ ν) ^ 2)) := by
    nlinarith
  calc ∫ r, ∑ i, ‖ΦU i r‖ * ‖ΦP i r‖
      ≤ 2 * (Real.pi * ((‖v‖ * poincMajorantNorm σ μ) ^ 2 + (‖w‖ * poincMajorantNorm σ ν) ^ 2)) :=
        this
    _ = 4 * c * (Real.pi * ((‖v‖ * poincMajorantNorm σ μ) ^ 2 + (‖w‖ * poincMajorantNorm σ ν) ^ 2) /
          (2 * c)) := by field_simp; ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
