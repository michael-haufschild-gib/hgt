import GaloisForLFunctions.RHTower.PositiveInjectiveBoundaryTransfer
import GaloisForLFunctions.HTGeometry.GreedySingularValues
import GaloisForLFunctions.HTGeometry.CfcEigenvectorRankOneAssembly

/-!
# The norm germ of scaled singular boundary transfers

For a positive operator `T` and `c > 0` the singular boundary transfer
`E_ε(cT) = cT(ε + cT)⁻¹` depends on `c` only through a translation of the aperture,
`E_ε(cT) = E_{ε/c}(T)`.  The difference of two scales is the functional calculus of

`h_ε(λ) = cλ/(ε + cλ) - dλ/(ε + dλ)`,

whose supremum over `λ ≥ 0` is the scale contrast `|√c - √d|/(√c + √d)`, attained exactly at
`ε = √(cd) λ`.  If `T` is moreover compact and injective on an infinite-dimensional space, its
positive eigenvalues accumulate at `0`, so the contrast is attained along apertures `ε → 0`:

`limsup_{ε→0+} ‖E_ε(cT) - E_ε(dT)‖ = |√c - √d|/(√c + √d)`.

The boundary-history corona `C_b((0,1], K(H))/C_0((0,1], K(H))` has quotient norm
`‖[F]‖ = limsup_{ε→0+} ‖F(ε)‖`; in it the scale germs `[ε ↦ E_ε(cT)]` lie at exactly this
distance.  The oriented contrast `κ(c,d) = (√c - √d)/(√c + √d)` is reflection-odd, obeys Einstein
addition and has rapidity `artanh κ(c,d) = (log c - log d)/4`.
-/

open Filter Topology Set Metric
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.RHTower

/-! ## The scalar contrast -/

/-- The oriented scale contrast `κ(c,d) = (√c - √d)/(√c + √d)`. -/
def germContrast (c d : ℝ) : ℝ := (Real.sqrt c - Real.sqrt d) / (Real.sqrt c + Real.sqrt d)

/-- The scaled transfer symbol `cλ/(ε + cλ) - dλ/(ε + dλ)`. -/
def scaledTransferSymbol (c d ε x : ℝ) : ℝ := c * x / (ε + c * x) - d * x / (ε + d * x)

theorem scaledTransferSymbol_eq {c d ε x : ℝ} (hc : 0 < c) (hd : 0 < d) (hε : 0 < ε)
    (hx : 0 ≤ x) :
    scaledTransferSymbol c d ε x = (c - d) * ε * x / ((ε + c * x) * (ε + d * x)) := by
  have h1 : ε + c * x ≠ 0 := by positivity
  have h2 : ε + d * x ≠ 0 := by positivity
  rw [scaledTransferSymbol]
  field_simp
  ring

/-- **(INBSG.12).**  `|h_ε(λ)| ≤ |√c - √d|/(√c + √d)` for every `λ ≥ 0`. -/
theorem abs_scaledTransferSymbol_le {c d ε x : ℝ} (hc : 0 < c) (hd : 0 < d) (hε : 0 < ε)
    (hx : 0 ≤ x) : |scaledTransferSymbol c d ε x| ≤ |germContrast c d| := by
  rw [scaledTransferSymbol_eq hc hd hε hx, germContrast]
  set a := Real.sqrt c
  set b := Real.sqrt d
  have ha : 0 < a := Real.sqrt_pos.2 hc
  have hb : 0 < b := Real.sqrt_pos.2 hd
  have hca : c = a * a := (Real.mul_self_sqrt hc.le).symm
  have hdb : d = b * b := (Real.mul_self_sqrt hd.le).symm
  rw [hca, hdb]
  have hden : 0 < (ε + a * a * x) * (ε + b * b * x) := by positivity
  rw [abs_div, abs_div, abs_of_pos hden, abs_of_pos (by positivity : 0 < a + b),
    div_le_div_iff₀ hden (by positivity)]
  have hfac : a * a - b * b = (a - b) * (a + b) := by ring
  rw [hfac, show (a - b) * (a + b) * ε * x = (a - b) * ((a + b) * ε * x) by ring, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (a + b) * ε * x)]
  have hsq : 0 ≤ (ε - a * b * x) ^ 2 := sq_nonneg _
  have key : (a + b) * ε * x * (a + b) ≤ (ε + a * a * x) * (ε + b * b * x) := by
    nlinarith [hsq, hx]
  calc |a - b| * ((a + b) * ε * x) * (a + b) = |a - b| * ((a + b) * ε * x * (a + b)) := by ring
    _ ≤ |a - b| * ((ε + a * a * x) * (ε + b * b * x)) :=
        mul_le_mul_of_nonneg_left key (abs_nonneg _)

/-- **(INBSG.12), equality.**  At the resonant aperture `ε = √(cd) λ` the symbol equals the
oriented contrast. -/
theorem scaledTransferSymbol_resonance {c d x : ℝ} (hc : 0 < c) (hd : 0 < d) (hx : 0 < x) :
    scaledTransferSymbol c d (Real.sqrt (c * d) * x) x = germContrast c d := by
  have hcd : 0 < Real.sqrt (c * d) := Real.sqrt_pos.2 (mul_pos hc hd)
  rw [scaledTransferSymbol_eq hc hd (mul_pos hcd hx) hx.le, germContrast,
    Real.sqrt_mul hc.le]
  set a := Real.sqrt c
  set b := Real.sqrt d
  have ha : 0 < a := Real.sqrt_pos.2 hc
  have hb : 0 < b := Real.sqrt_pos.2 hd
  have hca : c = a * a := (Real.mul_self_sqrt hc.le).symm
  have hdb : d = b * b := (Real.mul_self_sqrt hd.le).symm
  rw [hca, hdb]
  have h1 : a * b * x + a * a * x ≠ 0 := by positivity
  have h2 : a * b * x + b * b * x ≠ 0 := by positivity
  have h3 : a + b ≠ 0 := by positivity
  field_simp
  ring

theorem abs_germContrast_lt_one {c d : ℝ} (hc : 0 < c) (hd : 0 < d) : |germContrast c d| < 1 := by
  rw [germContrast, abs_div, abs_of_pos (by positivity : 0 < Real.sqrt c + Real.sqrt d),
    div_lt_one (by positivity), abs_sub_lt_iff]
  have ha := Real.sqrt_pos.2 hc
  have hb := Real.sqrt_pos.2 hd
  constructor <;> linarith

theorem germContrast_eq_zero_iff {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : 0 < c + d) :
    germContrast c d = 0 ↔ c = d := by
  have hpos : 0 < Real.sqrt c + Real.sqrt d := by
    rcases lt_or_ge 0 c with h | h
    · have := Real.sqrt_pos.2 h
      positivity
    · have hc0 : c = 0 := le_antisymm h hc
      have : 0 < d := by linarith
      have := Real.sqrt_pos.2 this
      positivity
  rw [germContrast, div_eq_zero_iff, or_iff_left hpos.ne', sub_eq_zero]
  constructor
  · intro h
    have := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt hc, Real.sq_sqrt hd] at this
    exact this
  · rintro rfl
    rfl

/-- **(INBSG.13), reflection.**  `κ(c⁻¹, d⁻¹) = -κ(c,d)`. -/
theorem germContrast_inv {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    germContrast c⁻¹ d⁻¹ = -germContrast c d := by
  rw [germContrast, germContrast, Real.sqrt_inv, Real.sqrt_inv]
  have ha := Real.sqrt_pos.2 hc
  have hb := Real.sqrt_pos.2 hd
  field_simp
  ring

/-- **(INBSG.13), Einstein addition.**  `κ(cd,1) = (κ(c,1) + κ(d,1))/(1 + κ(c,1) κ(d,1))`. -/
theorem germContrast_mul_einstein {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    germContrast (c * d) 1 =
      (germContrast c 1 + germContrast d 1) / (1 + germContrast c 1 * germContrast d 1) := by
  rw [germContrast, germContrast, germContrast, Real.sqrt_mul hc.le, Real.sqrt_one]
  have ha := Real.sqrt_pos.2 hc
  have hb := Real.sqrt_pos.2 hd
  generalize Real.sqrt c = a at ha ⊢
  generalize Real.sqrt d = b at hb ⊢
  have h1 : a + 1 ≠ 0 := by positivity
  have h2 : b + 1 ≠ 0 := by positivity
  have h3 : a * b + 1 ≠ 0 := by positivity
  have h4 : (a + 1) * (b + 1) + (a - 1) * (b - 1) ≠ 0 := by nlinarith
  rw [div_add_div _ _ h1 h2, div_mul_div_comm, one_add_div (mul_ne_zero h1 h2),
    div_div_div_cancel_right₀ (mul_ne_zero h1 h2), div_eq_div_iff h3 h4]
  ring

/-- **(INBSG.13), rapidity.**  `artanh κ(c,d) = (log c - log d)/4`. -/
theorem artanh_germContrast {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Real.artanh (germContrast c d) = (Real.log c - Real.log d) / 4 := by
  have hk := abs_germContrast_lt_one hc hd
  rw [Real.artanh_eq_half_log ⟨(abs_lt.1 hk).1.le, (abs_lt.1 hk).2.le⟩]
  have ha := Real.sqrt_pos.2 hc
  have hb := Real.sqrt_pos.2 hd
  have h1 : 1 + germContrast c d = 2 * Real.sqrt c / (Real.sqrt c + Real.sqrt d) := by
    rw [germContrast]
    field_simp
    ring
  have h2 : 1 - germContrast c d = 2 * Real.sqrt d / (Real.sqrt c + Real.sqrt d) := by
    rw [germContrast]
    field_simp
    ring
  rw [h1, h2, show 2 * Real.sqrt c / (Real.sqrt c + Real.sqrt d) /
      (2 * Real.sqrt d / (Real.sqrt c + Real.sqrt d)) = Real.sqrt c / Real.sqrt d by
        field_simp,
    Real.log_div ha.ne' hb.ne', Real.log_sqrt hc.le, Real.log_sqrt hd.le]
  ring

/-! ## Operator bounds -/

section Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spectrum_subset_Icc_of_isPositive {T : H →L[ℂ] H} (hT : T.IsPositive) :
    spectrum ℝ T ⊆ Icc 0 ‖T‖ := by
  intro x hx
  rcases subsingleton_or_nontrivial H with hsub | hnon
  · rw [spectrum.of_subsingleton] at hx
    exact absurd hx (Set.notMem_empty x)
  have h0 : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive T).2 hT
  refine ⟨spectrum_nonneg_of_nonneg h0 hx, ?_⟩
  have := spectrum.subset_closedBall_norm (𝕜 := ℝ) T hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact (le_abs_self x).trans this

theorem continuousOn_transferSymbol {S : Set ℝ} (hS : S ⊆ Ici 0) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun x : ℝ => x / (ε + x)) S := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
  have := hS hx
  simp only [mem_Ici] at this
  linarith

/-- **(INBSG.2).**  Scaling the operator translates the aperture: `E_ε(cT) = E_{ε/c}(T)`. -/
theorem positiveBoundaryTransfer_smul {T : H →L[ℂ] H} (hT : T.IsPositive) {c : ℝ} (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    positiveBoundaryTransfer (c • T) ε = positiveBoundaryTransfer T (ε / c) := by
  have hspec := spectrum_subset_Icc_of_isPositive hT
  rw [positiveBoundaryTransfer, positiveBoundaryTransfer]
  have hcont : ContinuousOn (fun x : ℝ => x / (ε + x)) ((fun x => c • x) '' spectrum ℝ T) := by
    refine continuousOn_transferSymbol ?_ hε
    rintro _ ⟨x, hx, rfl⟩
    simp only [smul_eq_mul, mem_Ici]
    exact mul_nonneg hc.le (hspec hx).1
  rw [← cfc_comp_smul c (fun x : ℝ => x / (ε + x)) T hcont hT.isSelfAdjoint]
  refine cfc_congr fun x hx => ?_
  have hx0 := (hspec hx).1
  simp only [smul_eq_mul]
  have h1 : ε + c * x ≠ 0 := by positivity
  have h2 : ε / c + x ≠ 0 := by positivity
  field_simp

/-- The difference of two scaled transfers is the functional calculus of the scaled symbol. -/
theorem scaledTransfer_sub_eq_cfc {T : H →L[ℂ] H} (hT : T.IsPositive) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    positiveBoundaryTransfer (c • T) ε - positiveBoundaryTransfer (d • T) ε =
      cfc (scaledTransferSymbol c d ε) T := by
  have hspec := spectrum_subset_Icc_of_isPositive hT
  rw [positiveBoundaryTransfer_smul hT hc hε, positiveBoundaryTransfer_smul hT hd hε,
    positiveBoundaryTransfer, positiveBoundaryTransfer,
    ← cfc_sub _ _ T (continuousOn_transferSymbol (fun x hx => (hspec hx).1) (div_pos hε hc))
      (continuousOn_transferSymbol (fun x hx => (hspec hx).1) (div_pos hε hd))]
  refine cfc_congr fun x hx => ?_
  have hx0 := (hspec hx).1
  rw [scaledTransferSymbol]
  have h1 : ε / c + x ≠ 0 := by positivity
  have h2 : ε / d + x ≠ 0 := by positivity
  have h3 : ε + c * x ≠ 0 := by positivity
  have h4 : ε + d * x ≠ 0 := by positivity
  field_simp

theorem continuousOn_scaledTransferSymbol {S : Set ℝ} (hS : S ⊆ Ici 0) {c d ε : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hε : 0 < ε) : ContinuousOn (scaledTransferSymbol c d ε) S := by
  unfold scaledTransferSymbol
  refine ContinuousOn.sub ?_ ?_ <;>
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_ <;>
    · have := hS hx
      simp only [mem_Ici] at this
      positivity

/-- **(INBSG.12), operator form.**  `‖E_ε(cT) - E_ε(dT)‖ ≤ |κ(c,d)|` at every aperture. -/
theorem norm_scaledTransfer_sub_le {T : H →L[ℂ] H} (hT : T.IsPositive) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    ‖positiveBoundaryTransfer (c • T) ε - positiveBoundaryTransfer (d • T) ε‖ ≤
      |germContrast c d| := by
  rcases subsingleton_or_nontrivial H with hsub | hnon
  · rw [Subsingleton.elim (positiveBoundaryTransfer (c • T) ε -
      positiveBoundaryTransfer (d • T) ε) 0, norm_zero]
    exact abs_nonneg _
  have hspec := spectrum_subset_Icc_of_isPositive hT
  rw [scaledTransfer_sub_eq_cfc hT hc hd hε]
  refine norm_cfc_le_of_forall_le _ _
    (continuousOn_scaledTransferSymbol (fun x hx => (hspec hx).1) hc hd hε) hT.isSelfAdjoint
    fun x hx => ?_
  rw [Real.norm_eq_abs]
  exact abs_scaledTransferSymbol_le hc hd hε (hspec hx).1

/-- At a positive spectral point the resonant aperture attains the contrast. -/
theorem le_norm_scaledTransfer_sub_of_mem_spectrum {T : H →L[ℂ] H} (hT : T.IsPositive)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {x : ℝ} (hx : x ∈ spectrum ℝ T) (hx0 : 0 < x) :
    |germContrast c d| ≤
      ‖positiveBoundaryTransfer (c • T) (Real.sqrt (c * d) * x) -
        positiveBoundaryTransfer (d • T) (Real.sqrt (c * d) * x)‖ := by
  have hnon : Nontrivial H := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hx
    exact hx
  have hspec := spectrum_subset_Icc_of_isPositive hT
  have hε : 0 < Real.sqrt (c * d) * x := mul_pos (Real.sqrt_pos.2 (mul_pos hc hd)) hx0
  rw [scaledTransfer_sub_eq_cfc hT hc hd hε]
  have h := norm_apply_le_norm_cfc (scaledTransferSymbol c d (Real.sqrt (c * d) * x)) T hx
    (continuousOn_scaledTransferSymbol (fun y hy => (hspec hy).1) hc hd hε) hT.isSelfAdjoint
  rwa [scaledTransferSymbol_resonance hc hd hx0, Real.norm_eq_abs] at h

/-- A spectral gap at zero makes the scale contrast vanish (INBSG.19). -/
theorem tendsto_norm_scaledTransfer_sub_of_gap {T : H →L[ℂ] H} (hT : T.IsPositive) {c d δ : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hδ : 0 < δ) (hgap : spectrum ℝ T ⊆ {0} ∪ Ici δ) :
    Tendsto (fun ε => ‖positiveBoundaryTransfer (c • T) ε - positiveBoundaryTransfer (d • T) ε‖)
      (𝓝[>] 0) (𝓝 0) := by
  rcases subsingleton_or_nontrivial H with hsub | hnon
  · simp only [Subsingleton.elim (positiveBoundaryTransfer (c • T) _ -
      positiveBoundaryTransfer (d • T) _) 0, norm_zero]
    exact tendsto_const_nhds
  have hspec := spectrum_subset_Icc_of_isPositive hT
  set K : ℝ := |c - d| / (c * d * δ)
  have hbound : ∀ ε > 0, ‖positiveBoundaryTransfer (c • T) ε -
      positiveBoundaryTransfer (d • T) ε‖ ≤ K * ε := by
    intro ε hε
    rw [scaledTransfer_sub_eq_cfc hT hc hd hε]
    refine norm_cfc_le_of_forall_le _ _
      (continuousOn_scaledTransferSymbol (fun x hx => (hspec hx).1) hc hd hε) hT.isSelfAdjoint
      fun x hx => ?_
    rw [Real.norm_eq_abs, scaledTransferSymbol_eq hc hd hε (hspec hx).1]
    rcases hgap hx with h0 | hxδ
    · rw [mem_singleton_iff.1 h0]
      simp only [mul_zero, zero_div, abs_zero]
      positivity
    · have hxδ' : δ ≤ x := hxδ
      have hx0 : 0 < x := hδ.trans_le hxδ'
      rw [abs_div, abs_of_pos (by positivity : 0 < (ε + c * x) * (ε + d * x)), abs_mul, abs_mul,
        abs_of_pos hε, abs_of_pos hx0, div_le_iff₀ (by positivity)]
      have h1 : c * x ≤ ε + c * x := by linarith
      have h2 : d * x ≤ ε + d * x := by linarith
      calc |c - d| * ε * x = K * ε * (c * d * δ * x) := by
            simp only [K]
            field_simp
        _ ≤ K * ε * ((ε + c * x) * (ε + d * x)) := by
            have hprod : c * d * δ * x ≤ (ε + c * x) * (ε + d * x) :=
              calc c * d * δ * x ≤ c * d * x * x := by
                    have := mul_le_mul_of_nonneg_left hxδ' (by positivity : 0 ≤ c * d * x)
                    nlinarith
                _ = (c * x) * (d * x) := by ring
                _ ≤ (ε + c * x) * (ε + d * x) :=
                    mul_le_mul h1 h2 (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hprod (by positivity)
  have hlin : Tendsto (fun ε : ℝ => K * ε) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => K * ε) (𝓝 0) (𝓝 (K * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlin
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

/-! ## Accumulation of the spectrum at zero -/

omit [CompleteSpace H] in
theorem svVal_ne_zero_of_injective {T : H →L[ℂ] H}
    (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) (n : ℕ) :
    ContinuousLinearMap.svVal T n ≠ 0 := by
  intro h0
  set W : Submodule ℂ H := Submodule.span ℂ (ContinuousLinearMap.svVec T '' Iio n)
  haveI : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ ((finite_Iio n).image _)
  have horth : Wᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have hx' : ∀ m < n, ⟪ContinuousLinearMap.svVec T m, x⟫_ℂ = 0 := fun m hm =>
      (Submodule.mem_orthogonal W x).1 hx _ (Submodule.subset_span ⟨m, hm, rfl⟩)
    have hb := ContinuousLinearMap.norm_apply_le_of_orth T n hx'
    rw [h0, zero_mul] at hb
    exact (injective_iff_map_eq_zero T).1 hinj x (norm_le_zero_iff.1 hb)
  have htop : W = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, horth]
  apply hH
  have : FiniteDimensional ℂ (⊤ : Submodule ℂ H) := htop ▸ inferInstance
  exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl)

/-- A positive compact injective operator on an infinite-dimensional space has positive spectral
points accumulating at zero. -/
theorem exists_spectrum_seq_tendsto_zero {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hcpt : IsCompactOperator T) (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) :
    ∃ x : ℕ → ℝ, (∀ n, 0 < x n ∧ x n ∈ spectrum ℝ T) ∧ Tendsto x atTop (𝓝 0) := by
  have hsym : (T : H →ₗ[ℂ] H).IsSymmetric := hT.isSelfAdjoint.isSymmetric
  have hpos : ∀ v : H, 0 ≤ RCLike.re ⟪v, T v⟫_ℂ := fun v => by
    rw [← inner_conj_symm, RCLike.conj_re]
    exact hT.re_inner_nonneg_left v
  refine ⟨ContinuousLinearMap.svVal T, fun n => ⟨?_, ?_⟩,
    ContinuousLinearMap.svVal_tendsto_zero hcpt hsym hpos⟩
  · exact lt_of_le_of_ne (ContinuousLinearMap.svVal_nonneg T n)
      (svVal_ne_zero_of_injective hinj hH n).symm
  · have hne := svVal_ne_zero_of_injective hinj hH n
    have hnorm := ContinuousLinearMap.norm_svVec_of_ne_zero hcpt hsym hpos hne
    exact mem_spectrum_of_eigenvector T (ContinuousLinearMap.apply_svVec T n)
      (fun h => by rw [h, norm_zero] at hnorm; exact zero_ne_one hnorm)

/-- **Theorem INBSG-A, pointwise form.**  The scale contrast is the limit superior of the
difference of the two scaled transfers as the aperture closes. -/
theorem limsup_norm_scaledTransfer_sub {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hcpt : IsCompactOperator T) (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    limsup (fun ε => ‖positiveBoundaryTransfer (c • T) ε - positiveBoundaryTransfer (d • T) ε‖)
      (𝓝[>] 0) = |germContrast c d| := by
  obtain ⟨x, hx, hx0⟩ := exists_spectrum_seq_tendsto_zero hT hcpt hinj hH
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖positiveBoundaryTransfer (c • T) ε -
      positiveBoundaryTransfer (d • T) ε‖ ≤ |germContrast c d| := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact norm_scaledTransfer_sub_le hT hc hd hε
  refine le_antisymm (limsup_le_of_le (isCoboundedUnder_le_of_le _ fun _ => norm_nonneg _) hle)
    (le_limsup_of_frequently_le ?_ (isBoundedUnder_of_eventually_le hle))
  have hε : Tendsto (fun n => Real.sqrt (c * d) * x n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      mul_pos (Real.sqrt_pos.2 (mul_pos hc hd)) (hx n).1⟩
    simpa using hx0.const_mul (Real.sqrt (c * d))
  exact hε.frequently (Frequently.of_forall fun n =>
    le_norm_scaledTransfer_sub_of_mem_spectrum hT hc hd (hx n).2 (hx n).1)

end Operator

end GaloisForLFunctions.HTGeometry
