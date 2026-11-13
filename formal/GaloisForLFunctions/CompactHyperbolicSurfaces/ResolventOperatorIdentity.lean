import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventOperators

/-!
# The resolvent identity for the operators `T_s`

On a compact quotient, for `1 < a < s` and `c = s(s − 1) − a(a − 1)`:

* `T_a − T_s` is the operator of the difference kernel `Σ_γ D_{a,s}(u(z, γw))` (`resOp_sub`);
* the composed kernel of `T_s T_a` unfolds to `Σ_δ (k_s ⋆ k_a)(z, δw)` (`setLIntegral_autK_mul`),
  which the kernel identity turns into `Σ_δ D_{a,s}(u(z, δw))/c`, so

  `T_s T_a = c⁻¹ (T_a − T_s)`   (`resOp_comp`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real
open scoped ENNReal MatrixGroups Pointwise

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchurKernel

noncomputable section

namespace CompactQuotient

variable (X : CompactQuotient)

/-- The resolvent operator `T_s`, `s > 1`. -/
def resOp {s : ℝ} (hs : 1 < s) : Lp ℂ 2 X.μ →L[ℂ] Lp ℂ 2 X.μ :=
  (X.profileKernel (measurable_resKernel s) (lintegral_resKernel_mass_lt_top hs)).op

theorem isSelfAdjoint_resOp {s : ℝ} (hs : 1 < s) : IsSelfAdjoint (X.resOp hs) :=
  X.isSelfAdjoint_profileKernel _ _

theorem norm_resOp_le {s : ℝ} (hs : 1 < s) : ‖X.resOp hs‖ ≤ 1 / (s * (s - 1)) := by
  refine (X.norm_profileKernel_le _ _).trans (le_of_eq ?_)
  rw [lintegral_resKernel_mass hs, ENNReal.toReal_ofReal (by
    have : 0 < s * (s - 1) := by nlinarith
    positivity)]

/-- Off the orbit of `z`, the automorphic kernel of `k_s` is finite. -/
theorem autK_resKernel_lt_top {s : ℝ} (hs : 1 < s) {z ξ : ℍ}
    (hξ : ξ ∉ Set.range fun γ : X.Γ => (γ : SL(2, ℝ))⁻¹ • z) : autK X.Γ (resKernel s) z ξ < ∞ := by
  obtain ⟨C, hC0, hC⟩ := exists_resKernel_le_rpow_neg (by linarith : (1 / 2 : ℝ) < s)
  obtain ⟨M, hM, hle⟩ := X.cocompactFree.exists_tsum_rpow_le hs
  obtain ⟨Cc, -, hcount⟩ := X.cocompactFree.exists_card_le
  obtain ⟨hfin, -⟩ := hcount z ξ 1 zero_le_one
  set S := {γ : X.Γ | pairU z ((γ : SL(2, ℝ)) • ξ) ≤ 1}
  have hpos : ∀ γ : X.Γ, 0 < pairU z ((γ : SL(2, ℝ)) • ξ) := by
    intro γ
    rcases (pairU_nonneg z ((γ : SL(2, ℝ)) • ξ)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [pairU_eq_cosh] at h
      have h1 : Real.cosh (dist z ((γ : SL(2, ℝ)) • ξ)) = 1 := by linarith
      have h2 : dist z ((γ : SL(2, ℝ)) • ξ) = 0 := by
        by_contra hne; have := Real.one_lt_cosh.mpr hne; linarith
      have h3 : (γ : SL(2, ℝ)) • ξ = z := (dist_eq_zero.mp h2).symm
      exact hξ ⟨γ, show (γ : SL(2, ℝ))⁻¹ • z = ξ by rw [← h3, inv_smul_smul]⟩
  have hb : ∀ γ : X.Γ, resKernel s (pairU z ((γ : SL(2, ℝ)) • ξ)) ≤
      S.indicator (fun γ => resKernel s (pairU z ((γ : SL(2, ℝ)) • ξ))) γ +
        ENNReal.ofReal (C * 2 ^ s) * ENNReal.ofReal ((1 + pairU z ((γ : SL(2, ℝ)) • ξ)) ^ (-s)) := by
    intro γ
    by_cases hγ : γ ∈ S
    · rw [indicator_of_mem hγ]; exact le_self_add
    · rw [indicator_of_notMem hγ, zero_add]
      have hu : 1 < pairU z ((γ : SL(2, ℝ)) • ξ) := lt_of_not_ge hγ
      refine (hC _ (hpos γ)).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : pairU z ((γ : SL(2, ℝ)) • ξ) ^ (-s) ≤
          2 ^ s * (1 + pairU z ((γ : SL(2, ℝ)) • ξ)) ^ (-s) := by
        have h2 : (1 + pairU z ((γ : SL(2, ℝ)) • ξ)) ≤ 2 * pairU z ((γ : SL(2, ℝ)) • ξ) := by linarith
        have h3 := Real.rpow_le_rpow_of_nonpos (by linarith) h2 (show -s ≤ 0 by linarith)
        rw [Real.mul_rpow (by norm_num) (by linarith)] at h3
        have h4 : (2 : ℝ) ^ s * 2 ^ (-s) = 1 := by
          rw [← Real.rpow_add (by norm_num)]; simp
        calc pairU z ((γ : SL(2, ℝ)) • ξ) ^ (-s)
            = 2 ^ s * (2 ^ (-s) * pairU z ((γ : SL(2, ℝ)) • ξ) ^ (-s)) := by
              rw [← mul_assoc, h4, one_mul]
          _ ≤ 2 ^ s * (1 + pairU z ((γ : SL(2, ℝ)) • ξ)) ^ (-s) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
      calc C * pairU z ((γ : SL(2, ℝ)) • ξ) ^ (-s)
          ≤ C * (2 ^ s * (1 + pairU z ((γ : SL(2, ℝ)) • ξ)) ^ (-s)) :=
            mul_le_mul_of_nonneg_left h1 hC0
        _ = C * 2 ^ s * (1 + pairU z ((γ : SL(2, ℝ)) • ξ)) ^ (-s) := by ring
  have hS : ∑' γ : X.Γ, S.indicator (fun γ => resKernel s (pairU z ((γ : SL(2, ℝ)) • ξ))) γ < ∞ := by
    haveI := hfin.fintype
    rw [← tsum_subtype, tsum_fintype]
    exact ENNReal.sum_lt_top.mpr fun γ _ => resKernel_lt_top (by linarith) (hpos γ)
  calc autK X.Γ (resKernel s) z ξ
      ≤ ∑' γ : X.Γ, (S.indicator (fun γ => resKernel s (pairU z ((γ : SL(2, ℝ)) • ξ))) γ +
          ENNReal.ofReal (C * 2 ^ s) *
            ENNReal.ofReal ((1 + pairU z ((γ : SL(2, ℝ)) • ξ)) ^ (-s))) := ENNReal.tsum_le_tsum hb
    _ = ∑' γ : X.Γ, S.indicator (fun γ => resKernel s (pairU z ((γ : SL(2, ℝ)) • ξ))) γ +
          ENNReal.ofReal (C * 2 ^ s) *
            ∑' γ : X.Γ, ENNReal.ofReal ((1 + pairU z ((γ : SL(2, ℝ)) • ξ)) ^ (-s)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hS, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((hle z ξ).trans_lt hM)⟩

theorem measurable_autK_fst {k : ℝ → ℝ≥0∞} (hk : Measurable k) (w : ℍ) :
    Measurable fun ξ : ℍ => autK X.Γ k ξ w :=
  (measurable_autK (Γ := X.Γ) hk).of_uncurry_right

/-- **Unfolding a product of automorphic kernels.**
`∫_F K(z, ξ) K'(ξ, w) dξ = Σ_δ (k ⋆ k')(z, δw)`. -/
theorem setLIntegral_autK_mul {k k' : ℝ → ℝ≥0∞} (hk : Measurable k) (hk' : Measurable k')
    (z w : ℍ) : ∫⁻ ξ in X.F, autK X.Γ k z ξ * autK X.Γ k' ξ w =
      ∑' δ : X.Γ, convK k k' z ((δ : SL(2, ℝ)) • w) := by
  have hm : Measurable fun ξ : ℍ => k (pairU z ξ) * autK X.Γ k' ξ w :=
    (hk.comp (continuous_pairU.comp (continuous_const.prodMk continuous_id)).measurable).mul
      (measurable_autK_fst X hk' w)
  have e1 : ∀ ξ : ℍ, autK X.Γ k z ξ * autK X.Γ k' ξ w =
      ∑' γ : X.Γ, k (pairU z ((γ : SL(2, ℝ)) • ξ)) * autK X.Γ k' ((γ : SL(2, ℝ)) • ξ) w := by
    intro ξ
    rw [autK, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun γ => ?_
    rw [autK_smul_left]
  have hδ : ∀ δ : X.Γ, Measurable fun ξ : ℍ =>
      k (pairU z ξ) * k' (pairU ξ ((δ : SL(2, ℝ)) • w)) := fun δ =>
    (hk.comp (continuous_pairU.comp (continuous_const.prodMk continuous_id)).measurable).mul
      (hk'.comp (continuous_pairU.comp (continuous_id.prodMk continuous_const)).measurable)
  calc ∫⁻ ξ in X.F, autK X.Γ k z ξ * autK X.Γ k' ξ w
      = ∫⁻ ξ in X.F, ∑' γ : X.Γ, k (pairU z ((γ : SL(2, ℝ)) • ξ)) *
          autK X.Γ k' ((γ : SL(2, ℝ)) • ξ) w := lintegral_congr e1
    _ = ∑' γ : X.Γ, ∫⁻ ξ in X.F, k (pairU z ((γ : SL(2, ℝ)) • ξ)) *
          autK X.Γ k' ((γ : SL(2, ℝ)) • ξ) w :=
        lintegral_tsum fun γ => (hm.comp (measurable_const_smul ((γ : SL(2, ℝ))))).aemeasurable
    _ = ∫⁻ ξ, k (pairU z ξ) * autK X.Γ k' ξ w :=
        (X.isFundamentalDomain.lintegral_eq_tsum'' (fun ξ => k (pairU z ξ) * autK X.Γ k' ξ w)).symm
    _ = ∫⁻ ξ, ∑' δ : X.Γ, k (pairU z ξ) * k' (pairU ξ ((δ : SL(2, ℝ)) • w)) :=
        lintegral_congr fun ξ => by rw [autK, ENNReal.tsum_mul_left]
    _ = ∑' δ : X.Γ, ∫⁻ ξ, k (pairU z ξ) * k' (pairU ξ ((δ : SL(2, ℝ)) • w)) :=
        lintegral_tsum fun δ => (hδ δ).aemeasurable
    _ = ∑' δ : X.Γ, convK k k' z ((δ : SL(2, ℝ)) • w) := rfl

/-- Points off the orbit of `z` (a.e. point). -/
theorem ae_not_mem_orbit (z : ℍ) :
    ∀ᵐ ξ : ℍ, ξ ∉ Set.range fun γ : X.Γ => (γ : SL(2, ℝ))⁻¹ • z := by
  have : (Set.range fun γ : X.Γ => (γ : SL(2, ℝ))⁻¹ • z) =
      Set.range fun γ : X.Γ => (γ : SL(2, ℝ)) • z := by
    ext ξ
    constructor
    · rintro ⟨γ, rfl⟩; exact ⟨γ⁻¹, by simp⟩
    · rintro ⟨γ, rfl⟩; exact ⟨γ⁻¹, by simp⟩
  rw [this]
  exact measure_eq_zero_iff_ae_notMem.mp (X.volume_orbit z)

theorem pairU_pos_of_not_mem_orbit {z w : ℍ}
    (hw : w ∉ Set.range fun γ : X.Γ => (γ : SL(2, ℝ))⁻¹ • z) (γ : X.Γ) :
    0 < pairU z ((γ : SL(2, ℝ)) • w) := by
  rcases (pairU_nonneg z ((γ : SL(2, ℝ)) • w)).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [pairU_eq_cosh] at h
    have h1 : Real.cosh (dist z ((γ : SL(2, ℝ)) • w)) = 1 := by linarith
    have h2 : dist z ((γ : SL(2, ℝ)) • w) = 0 := by
      by_contra hne; have := Real.one_lt_cosh.mpr hne; linarith
    have h3 : (γ : SL(2, ℝ)) • w = z := (dist_eq_zero.mp h2).symm
    exact hw ⟨γ, show (γ : SL(2, ℝ))⁻¹ • z = w by rw [← h3, inv_smul_smul]⟩

section identity

variable {a s : ℝ} (ha : 1 < a) (has : a < s)
include ha has

/-- The difference profile `D_{a,s}`. -/
def diffProfile (a s : ℝ) : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (diffKernel a s u)

theorem measurable_diffProfile : Measurable (diffProfile a s) :=
  ENNReal.measurable_ofReal.comp (continuous_diffKernel (by linarith) has.le).measurable

omit ha in
theorem diffProfile_add (u : ℝ) (hu : 0 < u) (ha' : 1 / 2 < a) :
    diffProfile a s u + resKernel s u = resKernel a u :=
  diffKernel_add_resKernel ha' has.le hu

/-- The mass of `D_{a,s}`. -/
theorem lintegral_diffProfile_mass : ∫⁻ w, diffProfile a s (pairU I w) =
    ENNReal.ofReal (1 / (a * (a - 1)) - 1 / (s * (s - 1))) := by
  have hs : 1 < s := lt_trans ha has
  have hmD : Measurable fun w : ℍ => diffProfile a s (pairU I w) :=
    (measurable_diffProfile ha has).comp
      ((continuous_pairU.comp (continuous_const.prodMk continuous_id)).measurable)
  have hsum : (∫⁻ w, diffProfile a s (pairU I w)) + ∫⁻ w, resKernel s (pairU I w) =
      ∫⁻ w, resKernel a (pairU I w) := by
    rw [← lintegral_add_left hmD]
    refine lintegral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_singleton I)] with w hw
    have hne : I ≠ w := fun h => hw (by rw [h]; rfl)
    have hpos : 0 < pairU I w := by
      rw [pairU_eq_cosh]
      have := Real.one_lt_cosh.mpr (dist_pos.mpr hne).ne'
      linarith
    exact diffProfile_add has _ hpos (by linarith)
  rw [lintegral_resKernel_mass hs, lintegral_resKernel_mass ha] at hsum
  have h := ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hsum
  rw [h, ← ENNReal.ofReal_sub _ (by
    have : 0 < s * (s - 1) := by nlinarith
    positivity)]

theorem lintegral_diffProfile_mass_lt_top : ∫⁻ w, diffProfile a s (pairU I w) < ∞ := by
  rw [lintegral_diffProfile_mass ha has]; exact ENNReal.ofReal_lt_top

/-- The operator `T_a − T_s` of the difference kernel. -/
def diffOp : Lp ℂ 2 X.μ →L[ℂ] Lp ℂ 2 X.μ :=
  (X.profileKernel (measurable_diffProfile ha has) (lintegral_diffProfile_mass_lt_top ha has)).op

/-- `T_a − T_s` is the operator of the difference kernel. -/
theorem resOp_sub : X.resOp ha - X.resOp (lt_trans ha has) = X.diffOp ha has := by
  have hs : 1 < s := lt_trans ha has
  rw [resOp, resOp, diffOp, ← sub_op]
  refine op_eq_of_ae (Eventually.of_forall fun z => ?_)
  filter_upwards [ae_restrict_of_ae (X.ae_not_mem_orbit z)] with w hw
  show ((autK X.Γ (resKernel a) z w).toReal : ℂ) - ((autK X.Γ (resKernel s) z w).toReal : ℂ) =
    ((autK X.Γ (diffProfile a s) z w).toReal : ℂ)
  have hsplit : autK X.Γ (resKernel a) z w =
      autK X.Γ (diffProfile a s) z w + autK X.Γ (resKernel s) z w := by
    rw [autK, autK, autK, ← ENNReal.tsum_add]
    refine tsum_congr fun γ => ?_
    exact (diffProfile_add has _ (X.pairU_pos_of_not_mem_orbit hw γ) (by linarith)).symm
  have hfin_s := X.autK_resKernel_lt_top hs hw
  have hfin_a := X.autK_resKernel_lt_top ha hw
  have hfin_d : autK X.Γ (diffProfile a s) z w < ∞ :=
    lt_of_le_of_lt (by rw [hsplit]; exact le_self_add) hfin_a
  rw [hsplit, ENNReal.toReal_add hfin_d.ne hfin_s.ne]
  push_cast
  ring

/-- The scaled difference profile `D_{a,s}/(s(s−1) − a(a−1))`. -/
def diffProfileScaled (a s : ℝ) : ℝ → ℝ≥0∞ :=
  fun u => ENNReal.ofReal (diffKernel a s u / (s * (s - 1) - a * (a - 1)))

theorem measurable_diffProfileScaled : Measurable (diffProfileScaled a s) :=
  ENNReal.measurable_ofReal.comp
    ((continuous_diffKernel (by linarith) has.le).measurable.div_const _)

theorem diffProfileScaled_eq (u : ℝ) : diffProfileScaled a s u =
    ENNReal.ofReal (1 / (s * (s - 1) - a * (a - 1))) * diffProfile a s u := by
  rw [diffProfileScaled, diffProfile, ← ENNReal.ofReal_mul (one_div_pos.mpr
    (resConst_pos ha has)).le, div_eq_mul_one_div, mul_comm]

theorem lintegral_diffProfileScaled_mass_lt_top :
    ∫⁻ w, diffProfileScaled a s (pairU I w) < ∞ := by
  simp_rw [diffProfileScaled_eq ha has]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_diffProfile_mass_lt_top ha has)

/-- The composed kernel of `T_s T_a` is the scaled difference kernel. -/
theorem comp_resKernel_ae (z : ℍ) : ∀ᵐ w ∂X.μ,
    (comp (X.profileKernel (measurable_resKernel s) (lintegral_resKernel_mass_lt_top (lt_trans ha has)))
      (X.profileKernel (measurable_resKernel a) (lintegral_resKernel_mass_lt_top ha))).toFun z w =
    (X.profileKernel (measurable_diffProfileScaled ha has)
      (lintegral_diffProfileScaled_mass_lt_top ha has)).toFun z w := by
  have hs : 1 < s := lt_trans ha has
  -- the kernel identity at every translate
  have hδ : ∀ δ : X.Γ, ∀ᵐ w : ℍ, convK (resKernel s) (resKernel a) z ((δ : SL(2, ℝ)) • w) =
      diffProfileScaled a s (pairU z ((δ : SL(2, ℝ)) • w)) := by
    intro δ
    have hmp := measurePreserving_smul (((δ : SL(2, ℝ)) : GL (Fin 2) ℝ)) (volume : Measure ℍ)
    exact hmp.quasiMeasurePreserving.ae (convK_resKernel_ae ha has z)
  have hall := ae_all_iff.mpr hδ
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_of_ae (X.ae_not_mem_orbit z)] with w hw hw'
  rw [comp_toFun, profileKernel_toFun]
  -- convert the Bochner integral to a lower integral
  have hfin : ∀ᵐ ξ ∂X.μ, autK X.Γ (resKernel s) z ξ * autK X.Γ (resKernel a) ξ w < ∞ := by
    filter_upwards [ae_restrict_of_ae (X.ae_not_mem_orbit z),
      ae_restrict_of_ae (X.ae_not_mem_orbit w)] with ξ h1 h2
    have h2' : w ∉ Set.range fun γ : X.Γ => (γ : SL(2, ℝ))⁻¹ • ξ := by
      rintro ⟨γ, hγ⟩
      exact h2 ⟨γ⁻¹, by rw [← hγ]; simp⟩
    exact ENNReal.mul_lt_top (X.autK_resKernel_lt_top hs h1) (X.autK_resKernel_lt_top ha h2')
  have hmeas : AEMeasurable (fun ξ => autK X.Γ (resKernel s) z ξ * autK X.Γ (resKernel a) ξ w) X.μ :=
    ((measurable_autK (measurable_resKernel s)).comp (measurable_const.prodMk measurable_id) |>.mul
      (X.measurable_autK_fst (measurable_resKernel a) w)).aemeasurable
  have e1 : ∫ ξ, (X.profileKernel (measurable_resKernel s) (lintegral_resKernel_mass_lt_top hs)).toFun z ξ *
      (X.profileKernel (measurable_resKernel a) (lintegral_resKernel_mass_lt_top ha)).toFun ξ w ∂X.μ =
      (((∫⁻ ξ in X.F, autK X.Γ (resKernel s) z ξ * autK X.Γ (resKernel a) ξ w).toReal : ℝ) : ℂ) := by
    simp only [profileKernel_toFun]
    rw [← integral_toReal hmeas hfin, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [ENNReal.toReal_mul, Complex.ofReal_mul]
  rw [e1, X.setLIntegral_autK_mul (measurable_resKernel s) (measurable_resKernel a)]
  congr 2
  exact tsum_congr fun δ => hw δ

theorem autK_diffProfileScaled (z w : ℍ) : autK X.Γ (diffProfileScaled a s) z w =
    ENNReal.ofReal (1 / (s * (s - 1) - a * (a - 1))) * autK X.Γ (diffProfile a s) z w := by
  rw [autK, autK, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun γ => diffProfileScaled_eq ha has _

/-- The scaled difference kernel defines `c⁻¹ (T_a − T_s)`. -/
theorem op_diffProfileScaled :
    (X.profileKernel (measurable_diffProfileScaled ha has)
      (lintegral_diffProfileScaled_mass_lt_top ha has)).op =
      ((1 / (s * (s - 1) - a * (a - 1)) : ℝ) : ℂ) • X.diffOp ha has := by
  have hc := resConst_pos ha has
  ext1 f
  apply Lp.ext
  filter_upwards [(X.profileKernel (measurable_diffProfileScaled ha has)
      (lintegral_diffProfileScaled_mass_lt_top ha has)).op_coeFn f,
    (X.profileKernel (measurable_diffProfile ha has)
      (lintegral_diffProfile_mass_lt_top ha has)).op_coeFn f,
    Lp.coeFn_smul (((1 / (s * (s - 1) - a * (a - 1)) : ℝ) : ℂ)) (X.diffOp ha has f)] with z h1 h2 h3
  rw [smul_apply, h3, Pi.smul_apply, diffOp, h2, h1, apply, apply, smul_eq_mul,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [profileKernel_toFun]
  rw [X.autK_diffProfileScaled ha has, ENNReal.toReal_mul, ENNReal.toReal_ofReal (one_div_pos.mpr hc).le]
  push_cast
  ring

/-- **The resolvent identity.**  `T_s T_a = c⁻¹ (T_a − T_s)`, `c = s(s − 1) − a(a − 1)`. -/
theorem resOp_comp : X.resOp (lt_trans ha has) ∘L X.resOp ha =
    ((1 / (s * (s - 1) - a * (a - 1)) : ℝ) : ℂ) • (X.resOp ha - X.resOp (lt_trans ha has)) := by
  rw [resOp, resOp, ← comp_op, op_eq_of_ae (Eventually.of_forall fun z => X.comp_resKernel_ae ha has z),
    X.op_diffProfileScaled ha has, ← X.resOp_sub ha has]
  rfl

/-- The resolvent operators commute. -/
theorem resOp_comm : X.resOp ha ∘L X.resOp (lt_trans ha has) =
    X.resOp (lt_trans ha has) ∘L X.resOp ha := by
  have h := X.resOp_comp ha has
  have hA := X.isSelfAdjoint_resOp ha
  have hS := X.isSelfAdjoint_resOp (lt_trans ha has)
  have h2 := congrArg ContinuousLinearMap.adjoint h
  rw [ContinuousLinearMap.adjoint_comp, hA.adjoint_eq, hS.adjoint_eq, map_smulₛₗ, map_sub,
    hA.adjoint_eq, hS.adjoint_eq, Complex.conj_ofReal] at h2
  rw [h2, h]

end identity

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
