import GaloisForLFunctions.RHTower.DeckScatteringExtension
import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift

/-!
# Parseval for incomplete Eisenstein series

For `C²` height profiles `ψ, φ` and `v, w ∈ V_∞` put
`T_{ψ,v}(t) = ψ̂(1/2+it) v + ψ̂(1/2-it) Φ̃(1/2-it) v` (`eisTransform`).  Then
`⟨E(·|ψ,v), E(·|φ,w)⟩ = π⁻¹ ∫ ⟨T_{ψ,v}(t), T_{φ,w}(t)⟩ dt + 4 φ̂(1) conj ψ̂(1) ⟨v, R w⟩`
(`inner_incEisL2_eq_eisTransform`), where `R w = Res_{s=1} Φ̃(s) w` (`resVec`).

The line integral on `Re s = 2` (`inner_incEisL2_eq_integral_line`) splits into the entire part
`φ̂(s) ψ̄̂(1-s) ⟨v,w⟩` and the scattering part `φ̂(s) ψ̄̂(s) ⟨v, Φ̃(s) w⟩`; both are shifted to
`Re s = 1/2` (`integral_line_sub_integral_line_eq`), the second picking up the residue at `s = 1`.
On the critical line unitarity and the adjoint relation `Φ̃(1/2-it)* = Φ̃(1/2+it)` turn the sum of the
two shifted integrals into `(2π)⁻¹ ∫ ⟨T_{ψ,v}, T_{φ,w}⟩`, after the reflection `t ↦ -t`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry
open _root_.RHTower (linePt linePt_re linePt_im)

noncomputable section

variable {N : ℕ}

/-! ## The critical line -/

theorem one_sub_linePt (t : ℝ) : 1 - linePt t = linePt (-t) := by
  unfold linePt; push_cast; ring

theorem conj_linePt (t : ℝ) : conj (linePt t) = linePt (-t) := by
  apply Complex.ext <;> simp [linePt]

theorem linePt_ne_half {t : ℝ} (ht : t ≠ 0) : linePt t ≠ 1 / 2 := fun h => ht (by
  have := congrArg Complex.im h; simpa [linePt] using this)

theorem inner_scatVec_linePt_adjoint {t : ℝ} (ht : t ≠ 0) (v w : DeckSpace N) :
    ⟪scatVec (linePt (-t)) v, w⟫_ℂ = ⟪v, scatVec (linePt t) w⟫_ℂ := by
  have h := inner_scatVec_line_adjoint ht v w
  simpa [linePt] using h

theorem inner_scatVec_linePt (hN : 2 ≤ N) {t : ℝ} (ht : t ≠ 0) {v w : DeckSpace N} (hv : IsCuspVec v)
    (hw : IsCuspVec w) : ⟪scatVec (linePt t) v, scatVec (linePt t) w⟫_ℂ = ⟪v, w⟫_ℂ :=
  inner_scatVec_line hN ht hv hw

/-! ## The transform -/

/-- The residue vector `Res_{s=1} Φ̃(s) w = (2L²)⁻¹ ρ₁ (Σ_x w_x) · 𝟙`. -/
def resVec (w : DeckSpace N) : DeckSpace N :=
  ((2 * (N + 1 : ℂ) ^ 2)⁻¹ * scatResidue N * ∑ x : Deck N, w x) • onesVec N

/-- **The Eisenstein transform** of `E(·|ψ, v)`:
`T(t) = ψ̂(1/2 + it) v + ψ̂(1/2 - it) Φ̃(1/2 - it) v`. -/
def eisTransform (ψ : HeightProfile) (v : DeckSpace N) (t : ℝ) : DeckSpace N :=
  hMellin ψ.toFun (linePt t) • v + hMellin ψ.toFun (linePt (-t)) • scatExt v (linePt (-t))

/-- The entire part of the line integrand. -/
def parsevalEntire (ψ φ : HeightProfile) (s : ℂ) : ℂ :=
  hMellin φ.toFun s * hMellin ψ.conjProfile.toFun (1 - s)

/-- The scattering part of the line integrand. -/
def parsevalScatter (ψ φ : HeightProfile) (v w : DeckSpace N) (s : ℂ) : ℂ :=
  hMellin φ.toFun s * hMellin ψ.conjProfile.toFun s * ⟪v, scatExt w s⟫_ℂ

theorem conj_hMellin_linePt (ψ : HeightProfile) (t : ℝ) :
    conj (hMellin ψ.toFun (linePt t)) = hMellin ψ.conjProfile.toFun (linePt (-t)) := by
  rw [HeightProfile.hMellin_conjProfile, conj_linePt, neg_neg]

/-- **Pointwise symmetrization** on the critical line (`t ≠ 0`). -/
theorem inner_eisTransform (hN : 2 ≤ N) (ψ φ : HeightProfile) {v w : DeckSpace N}
    (hv : IsCuspVec v) (hw : IsCuspVec w) {t : ℝ} (ht : t ≠ 0) :
    ⟪eisTransform ψ v t, eisTransform φ w t⟫_ℂ =
      parsevalEntire ψ φ (linePt t) * ⟪v, w⟫_ℂ + parsevalEntire ψ φ (linePt (-t)) * ⟪v, w⟫_ℂ +
        parsevalScatter ψ φ v w (linePt (-t)) + parsevalScatter ψ φ v w (linePt t) := by
  have hnt : -t ≠ 0 := neg_ne_zero.2 ht
  have hX := scatExt_of_ne (linePt_ne_half hnt) v
  have hY := scatExt_of_ne (linePt_ne_half hnt) w
  have hY' := scatExt_of_ne (linePt_ne_half ht) w
  unfold eisTransform parsevalEntire parsevalScatter
  rw [hX, hY, hY', inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_left,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_smul_right, inner_scatVec_linePt hN hnt hv hw, inner_scatVec_linePt_adjoint ht,
    conj_hMellin_linePt, conj_hMellin_linePt, neg_neg, one_sub_linePt, one_sub_linePt, neg_neg]
  ring

/-! ## Bounds on the strip -/

theorem inv_one_add_sq_le_one (x : ℝ) : (1 + x ^ 2)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])

theorem exists_bound_parsevalEntire (ψ φ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun)
    (hφ : ContDiff ℝ 2 φ.toFun) :
    ∃ C, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → ‖parsevalEntire ψ φ s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨Cφ, hCφ0, hCφ⟩ := φ.exists_bound_hMellin hφ (1 / 2) 2
  obtain ⟨Cc, hCc0, hCc⟩ := ψ.conjProfile.exists_bound_hMellin (ψ.contDiff_conjProfile hψ) (-1) (1 / 2)
  refine ⟨Cφ * Cc, fun s h1 h2 => ?_⟩
  have hc := hCc (1 - s) (by simp; linarith) (by simp; linarith)
  have hsq : (1 - s).im ^ 2 = s.im ^ 2 := by simp
  rw [hsq] at hc
  have hi := inv_one_add_sq_le_one s.im
  have hpos : 0 ≤ (1 + s.im ^ 2)⁻¹ := by positivity
  rw [parsevalEntire, norm_mul]
  calc ‖hMellin φ.toFun s‖ * ‖hMellin ψ.conjProfile.toFun (1 - s)‖
      ≤ (Cφ * (1 + s.im ^ 2)⁻¹) * (Cc * 1) :=
        mul_le_mul (hCφ s h1 h2) (hc.trans (mul_le_mul_of_nonneg_left hi hCc0)) (norm_nonneg _)
          (by positivity)
    _ = Cφ * Cc * (1 + s.im ^ 2)⁻¹ := by ring

theorem exists_bound_parsevalScatter (hN : 2 ≤ N) (ψ φ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun)
    (hφ : ContDiff ℝ 2 φ.toFun) (v : DeckSpace N) {w : DeckSpace N} (hw : IsCuspVec w) :
    ∃ C, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖parsevalScatter ψ φ v w s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨Cφ, hCφ0, hCφ⟩ := φ.exists_bound_hMellin hφ (1 / 2) 2
  obtain ⟨Cc, hCc0, hCc⟩ := ψ.conjProfile.exists_bound_hMellin (ψ.contDiff_conjProfile hψ) (1 / 2) 2
  refine ⟨Cφ * Cc * (‖v‖ * (4 * ‖w‖)), fun s h1 h2 ht => ?_⟩
  have hi := inv_one_add_sq_le_one s.im
  have hc := (hCc s h1 h2).trans (mul_le_mul_of_nonneg_left hi hCc0)
  have hS : ‖⟪v, scatExt w s⟫_ℂ‖ ≤ ‖v‖ * (4 * ‖w‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_scatExt_le hN hw h1 h2 ht)
      (norm_nonneg _))
  rw [parsevalScatter, norm_mul, norm_mul]
  calc ‖hMellin φ.toFun s‖ * ‖hMellin ψ.conjProfile.toFun s‖ * ‖⟪v, scatExt w s⟫_ℂ‖
      ≤ (Cφ * (1 + s.im ^ 2)⁻¹) * (Cc * 1) * (‖v‖ * (4 * ‖w‖)) :=
        mul_le_mul (mul_le_mul (hCφ s h1 h2) hc (norm_nonneg _) (by positivity)) hS (norm_nonneg _)
          (by positivity)
    _ = Cφ * Cc * (‖v‖ * (4 * ‖w‖)) * (1 + s.im ^ 2)⁻¹ := by ring

/-! ## Holomorphy and residues -/

theorem differentiable_parsevalEntire (ψ φ : HeightProfile) : Differentiable ℂ (parsevalEntire ψ φ) :=
  φ.differentiable_hMellin.mul (ψ.conjProfile.differentiable_hMellin.comp (differentiable_id.const_sub 1))

theorem differentiableAt_parsevalScatter (hN : 2 ≤ N) (ψ φ : HeightProfile) (v : DeckSpace N)
    {w : DeckSpace N} (hw : IsCuspVec w) {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (parsevalScatter ψ φ v w) s :=
  ((φ.differentiable_hMellin s).mul (ψ.conjProfile.differentiable_hMellin s)).mul
    (differentiableAt_inner_scatExt hN v hw hs hs1)

theorem tendsto_parsevalEntire_residue (ψ φ : HeightProfile) :
    Tendsto (fun s => (s - 1) * parsevalEntire ψ φ s) (𝓝[≠] 1) (𝓝 0) := by
  have h : Tendsto (fun s => (s - 1) * parsevalEntire ψ φ s) (𝓝 1) (𝓝 ((1 - 1) * parsevalEntire ψ φ 1)) :=
    ((continuous_id.sub continuous_const).mul (differentiable_parsevalEntire ψ φ).continuous).tendsto 1
  rw [sub_self, zero_mul] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_parsevalScatter_residue (ψ φ : HeightProfile) (v w : DeckSpace N) :
    Tendsto (fun s => (s - 1) * parsevalScatter ψ φ v w s) (𝓝[≠] 1)
      (𝓝 (hMellin φ.toFun 1 * hMellin ψ.conjProfile.toFun 1 * ⟪v, resVec w⟫_ℂ)) := by
  have hM : Tendsto (fun s => hMellin φ.toFun s * hMellin ψ.conjProfile.toFun s) (𝓝[≠] 1)
      (𝓝 (hMellin φ.toFun 1 * hMellin ψ.conjProfile.toFun 1)) :=
    (((φ.differentiable_hMellin.continuous).mul
      (ψ.conjProfile.differentiable_hMellin.continuous)).tendsto 1).mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun s => ⟪v, (s - 1) • scatVec s w⟫_ℂ) (𝓝[≠] 1) (𝓝 ⟪v, resVec w⟫_ℂ) :=
    tendsto_const_nhds.inner (tendsto_sub_one_smul_scatVec w)
  refine (hM.mul hR).congr' ?_
  have hne : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 1 / 2 :=
    (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 1 / 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne] with s hs
  rw [parsevalScatter, scatExt_of_ne hs, inner_smul_right]
  ring

/-! ## The contour shifts -/

theorem integrable_parsevalEntire_line (ψ φ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun)
    (hφ : ContDiff ℝ 2 φ.toFun) {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 2) :
    Integrable fun t : ℝ => parsevalEntire ψ φ (x + t * Complex.I) := by
  obtain ⟨C, hC⟩ := exists_bound_parsevalEntire ψ φ hψ hφ
  refine integrable_line_of_bound (T₀ := 0) (C := C)
    (fun t => (differentiable_parsevalEntire ψ φ _).continuousAt) (fun t _ => ?_)
  have h := hC ((x : ℂ) + t * Complex.I) (by simpa using h1) (by simpa using h2)
  simpa using h

theorem integrable_parsevalScatter_line (hN : 2 ≤ N) (ψ φ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun)
    (hφ : ContDiff ℝ 2 φ.toFun) (v : DeckSpace N) {w : DeckSpace N} (hw : IsCuspVec w) {x : ℝ}
    (h1 : 1 / 2 ≤ x) (h2 : x ≤ 2) (hx : x ≠ 1) :
    Integrable fun t : ℝ => parsevalScatter ψ φ v w (x + t * Complex.I) := by
  obtain ⟨C, hC⟩ := exists_bound_parsevalScatter hN ψ φ hψ hφ v hw
  refine integrable_line_of_bound (T₀ := 1) (C := C) (fun t => ?_) (fun t ht => ?_)
  · refine (differentiableAt_parsevalScatter hN ψ φ v hw (by simpa using h1) fun h => hx ?_).continuousAt
    have := congrArg Complex.re h
    simpa using this
  · have h := hC ((x : ℂ) + t * Complex.I) (by simpa using h1) (by simpa using h2) (by simpa using ht)
    simpa using h

theorem integral_parsevalEntire_shift (ψ φ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun)
    (hφ : ContDiff ℝ 2 φ.toFun) :
    ∫ t : ℝ, parsevalEntire ψ φ ((2 : ℝ) + t * Complex.I) = ∫ t : ℝ, parsevalEntire ψ φ (linePt t) := by
  obtain ⟨C, hC⟩ := exists_bound_parsevalEntire ψ φ hψ hφ
  have h := integral_line_sub_integral_line_eq (a := 1 / 2) (b := 2) (p := 1) (by norm_num)
    (by norm_num) (fun s _ _ _ => differentiable_parsevalEntire ψ φ s)
    (tendsto_parsevalEntire_residue ψ φ) (T₀ := 0) (C := C) (fun s h1 h2 _ => hC s h1 h2)
  rw [mul_zero, sub_eq_zero] at h
  exact h

theorem integral_parsevalScatter_shift (hN : 2 ≤ N) (ψ φ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun)
    (hφ : ContDiff ℝ 2 φ.toFun) (v : DeckSpace N) {w : DeckSpace N} (hw : IsCuspVec w) :
    ∫ t : ℝ, parsevalScatter ψ φ v w ((2 : ℝ) + t * Complex.I) =
      (∫ t : ℝ, parsevalScatter ψ φ v w (linePt t)) +
        2 * Real.pi * (hMellin φ.toFun 1 * hMellin ψ.conjProfile.toFun 1 * ⟪v, resVec w⟫_ℂ) := by
  obtain ⟨C, hC⟩ := exists_bound_parsevalScatter hN ψ φ hψ hφ v hw
  have h := integral_line_sub_integral_line_eq (a := 1 / 2) (b := 2) (p := 1) (by norm_num)
    (by norm_num) (fun s h1 _ hs1 => differentiableAt_parsevalScatter hN ψ φ v hw h1 hs1)
    (tendsto_parsevalScatter_residue ψ φ v w) (T₀ := 1) (C := C) hC
  rw [sub_eq_iff_eq_add'] at h
  rw [h]
  rfl

/-! ## Parseval for pairs of incomplete Eisenstein series -/

/-- **Parseval for incomplete Eisenstein series**:
`⟨E(·|ψ,v), E(·|φ,w)⟩ = π⁻¹ ∫ ⟨T_{ψ,v}(t), T_{φ,w}(t)⟩ dt + 4 φ̂(1) conj ψ̂(1) ⟨v, R w⟩`. -/
theorem inner_incEisL2_eq_eisTransform (hN : 2 ≤ N) (ψ φ : HeightProfile) (hψ : ContDiff ℝ 2 ψ.toFun)
    (hφ : ContDiff ℝ 2 φ.toFun) {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) :
    ⟪incEisL2 ψ v, incEisL2 φ w⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * (∫ t : ℝ, ⟪eisTransform ψ v t, eisTransform φ w t⟫_ℂ) +
        4 * (hMellin φ.toFun 1 * conj (hMellin ψ.toFun 1)) * ⟪v, resVec w⟫_ℂ := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hc1 : hMellin ψ.conjProfile.toFun 1 = conj (hMellin ψ.toFun 1) := by
    rw [HeightProfile.hMellin_conjProfile, map_one]
  -- the line `Re s = 2`
  have hline := inner_incEisL2_eq_integral_line hN ψ φ hφ hv.1 hw (σ := 2) (by norm_num)
  have hI1 := integrable_parsevalEntire_line ψ φ hψ hφ (x := 2) (by norm_num) le_rfl
  have hI2 := integrable_parsevalScatter_line hN ψ φ hψ hφ v hw (x := 2) (by norm_num) le_rfl
    (by norm_num)
  have hpt : ∀ t : ℝ, hMellin φ.toFun ((2 : ℝ) + t * Complex.I) *
      (2 * (hMellin ψ.conjProfile.toFun (1 - ((2 : ℝ) + t * Complex.I)) * ⟪v, w⟫_ℂ +
        hMellin ψ.conjProfile.toFun ((2 : ℝ) + t * Complex.I) *
          ⟪v, scatVec ((2 : ℝ) + t * Complex.I) w⟫_ℂ)) =
      2 * ⟪v, w⟫_ℂ * parsevalEntire ψ φ ((2 : ℝ) + t * Complex.I) +
        2 * parsevalScatter ψ φ v w ((2 : ℝ) + t * Complex.I) := fun t => by
    have hne : ((2 : ℝ) : ℂ) + t * Complex.I ≠ 1 / 2 := fun h => by
      have := congrArg Complex.re h; norm_num at this
    rw [parsevalEntire, parsevalScatter, scatExt_of_ne hne]
    ring
  simp_rw [hpt] at hline
  rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
    integral_parsevalEntire_shift ψ φ hψ hφ, integral_parsevalScatter_shift hN ψ φ hψ hφ v hw]
    at hline
  -- the critical line
  have hJ1 := integrable_parsevalEntire_line ψ φ hψ hφ (x := 1 / 2) le_rfl (by norm_num)
  have hJ2 := integrable_parsevalScatter_line hN ψ φ hψ hφ v hw (x := 1 / 2) le_rfl (by norm_num)
    (by norm_num)
  have hJ1' : Integrable fun t : ℝ => parsevalEntire ψ φ (linePt t) := by
    simpa [linePt] using hJ1
  have hJ2' : Integrable fun t : ℝ => parsevalScatter ψ φ v w (linePt t) := by
    simpa [linePt] using hJ2
  have hsym : ∫ t : ℝ, ⟪eisTransform ψ v t, eisTransform φ w t⟫_ℂ =
      2 * ⟪v, w⟫_ℂ * (∫ t : ℝ, parsevalEntire ψ φ (linePt t)) +
        2 * ∫ t : ℝ, parsevalScatter ψ φ v w (linePt t) := by
    have hae : (fun t : ℝ => ⟪eisTransform ψ v t, eisTransform φ w t⟫_ℂ) =ᵐ[volume] fun t =>
        (parsevalEntire ψ φ (linePt t) * ⟪v, w⟫_ℂ + parsevalEntire ψ φ (linePt (-t)) * ⟪v, w⟫_ℂ) +
          (parsevalScatter ψ φ v w (linePt (-t)) + parsevalScatter ψ φ v w (linePt t)) := by
      filter_upwards [(countable_singleton (0 : ℝ)).ae_notMem volume] with t ht
      rw [inner_eisTransform hN ψ φ hv hw ht]
      ring
    have hA : Integrable fun t : ℝ => parsevalEntire ψ φ (linePt t) * ⟪v, w⟫_ℂ +
        parsevalEntire ψ φ (linePt (-t)) * ⟪v, w⟫_ℂ :=
      (hJ1'.mul_const _).add (hJ1'.comp_neg.mul_const _)
    have hB : Integrable fun t : ℝ => parsevalScatter ψ φ v w (linePt (-t)) +
        parsevalScatter ψ φ v w (linePt t) := hJ2'.comp_neg.add hJ2'
    rw [integral_congr_ae hae, integral_add hA hB, integral_add (hJ1'.mul_const _) (hJ1'.comp_neg.mul_const _),
      integral_add hJ2'.comp_neg hJ2', integral_mul_const, integral_mul_const,
      integral_neg_eq_self (fun t => parsevalEntire ψ φ (linePt t)),
      integral_neg_eq_self (fun t => parsevalScatter ψ φ v w (linePt t))]
    ring
  rw [hline, hsym, hc1]
  field_simp
  ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
