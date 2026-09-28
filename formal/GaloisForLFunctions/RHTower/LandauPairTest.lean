import GaloisForLFunctions.RHTower.TiltedOffLinePairKernel
import GaloisForLFunctions.RHTower.HodgeOffLineFlatnessLaw

/-!
# The Landau test of an off-line pair

For a super-exponentially decaying kernel `h`, the test
`f = N_{c₁,c₂,s}((h_{≤U}) ⋆ κ₂^{(w,ω)})` is `C²`, supported in `[-(U+w+s), U+w+s]`, polar-free, and
`f̂ = N · (ĥ - (h_{>U})^) · κ̂₂` (`paperFT_pairLandauTest`). Here `κ₂^{(w,ω)}` is the polar-free bump
at frequency `ω`, and `N(z) = c₁ + c₂ e^{isz}`.

For a pair `γ₀`, `γ̄₀` (`Im γ₀ ≠ 0`) and a unit `v`, the coefficients `pairC₁`, `pairC₂` give
`N(γ₀) = 1` and `N(γ̄₀) = v`, with `|pairC₂| ≤ 1/(s|Im γ₀|)` (`nodeSymbol_pairC_γ₀`,
`nodeSymbol_pairC_γ₁`, `norm_pairC₂_le`). The bump transform on the imaginary axis is bounded below:
`|κ̂_w(iy)| ≥ 4w e^{-w|y|} ∫κ` (`norm_paperFT_scaledBump_I_mul_ge`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## Phase alignment at a pair -/

/-- `v = -Q/|Q|` (`1` if `Q = 0`), so that `Q v̄ = -|Q|`. -/
def pairPhase (Q : ℂ) : ℂ := if Q = 0 then 1 else -(Q / (‖Q‖ : ℂ))

theorem norm_pairPhase (Q : ℂ) : ‖pairPhase Q‖ = 1 := by
  unfold pairPhase
  split_ifs with h
  · simp
  · rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.mpr h)]

theorem mul_conj_pairPhase (Q : ℂ) : Q * (starRingEnd ℂ) (pairPhase Q) = -(‖Q‖ : ℂ) := by
  unfold pairPhase
  split_ifs with h
  · simp [h]
  · have hn : (‖Q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [map_neg, map_div₀, Complex.conj_ofReal, mul_neg, mul_div_assoc', Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp

/-- `e^{isγ₀} - e^{isγ̄₀}`. -/
def pairGap (γ₀ : ℂ) (s : ℝ) : ℂ :=
  Complex.exp (I * γ₀ * s) - Complex.exp (I * (starRingEnd ℂ) γ₀ * s)

theorem norm_pairGap_ge (γ₀ : ℂ) {s : ℝ} (hs : 0 < s) : 2 * s * |γ₀.im| ≤ ‖pairGap γ₀ s‖ := by
  unfold pairGap
  refine le_trans ?_ (abs_norm_sub_norm_le _ _)
  rw [norm_cexp_I_mul_eq, norm_cexp_I_mul_eq]
  have hγ₁ : ((starRingEnd ℂ) γ₀).im = -γ₀.im := by simp
  rw [hγ₁]
  set x := γ₀.im * s with hx
  have key : ∀ y : ℝ, 0 ≤ y → 2 * y ≤ |Real.exp (-y) - Real.exp y| := by
    intro y hy
    have h1 : y ≤ Real.sinh y := Real.self_le_sinh_iff.mpr hy
    rw [Real.sinh_eq] at h1
    rw [abs_of_nonpos (by linarith [Real.exp_le_exp.mpr (show -y ≤ y by linarith)])]
    linarith
  have hxabs : |x| = s * |γ₀.im| := by rw [hx, abs_mul, abs_of_pos hs]; ring
  rcases le_or_gt 0 x with h0 | h0
  · have := key x h0
    rw [show -(-γ₀.im * s) = x by rw [hx]; ring, show -(γ₀.im * s) = -x by rw [hx]]
    rw [abs_of_nonneg h0] at hxabs
    linarith
  · have := key (-x) (by linarith)
    rw [show -(-γ₀.im * s) = x by rw [hx]; ring, show -(γ₀.im * s) = -x by rw [hx]]
    rw [neg_neg, abs_sub_comm] at this
    rw [abs_of_neg h0] at hxabs
    linarith

/-- `c₂ = (1 - v)/(e^{isγ₀} - e^{isγ̄₀})`. -/
def pairC₂ (γ₀ : ℂ) (s : ℝ) (v : ℂ) : ℂ := (1 - v) / pairGap γ₀ s

/-- `c₁ = 1 - c₂ e^{isγ₀}`. -/
def pairC₁ (γ₀ : ℂ) (s : ℝ) (v : ℂ) : ℂ := 1 - pairC₂ γ₀ s v * Complex.exp (I * γ₀ * s)

theorem nodeSymbol_pairC_γ₀ (γ₀ : ℂ) (s : ℝ) (v : ℂ) :
    nodeSymbol (pairC₁ γ₀ s v) (pairC₂ γ₀ s v) s γ₀ = 1 := by
  unfold nodeSymbol pairC₁; ring

theorem nodeSymbol_pairC_γ₁ {γ₀ : ℂ} (him : γ₀.im ≠ 0) {s : ℝ} (hs : 0 < s) (v : ℂ) :
    nodeSymbol (pairC₁ γ₀ s v) (pairC₂ γ₀ s v) s ((starRingEnd ℂ) γ₀) = v := by
  have hgap : pairGap γ₀ s ≠ 0 := by
    intro h
    have h1 := norm_pairGap_ge γ₀ hs
    rw [h, norm_zero] at h1
    have : 0 < 2 * s * |γ₀.im| := by have := abs_pos.mpr him; positivity
    linarith
  have key : pairC₂ γ₀ s v * pairGap γ₀ s = 1 - v := div_mul_cancel₀ _ hgap
  unfold nodeSymbol pairC₁
  unfold pairGap at key
  linear_combination (-1 : ℂ) * key

theorem norm_pairC₂_le {γ₀ : ℂ} (him : γ₀.im ≠ 0) {s : ℝ} (hs : 0 < s) {v : ℂ} (hv : ‖v‖ = 1) :
    ‖pairC₂ γ₀ s v‖ ≤ 1 / (s * |γ₀.im|) := by
  unfold pairC₂
  have hg := norm_pairGap_ge γ₀ hs
  have hpos : 0 < 2 * s * |γ₀.im| := by have := abs_pos.mpr him; positivity
  rw [norm_div]
  have hnum : ‖1 - v‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [hv]; norm_num)
  calc ‖1 - v‖ / ‖pairGap γ₀ s‖ ≤ 2 / (2 * s * |γ₀.im|) := by gcongr
    _ = 1 / (s * |γ₀.im|) := by field_simp

theorem norm_pairC₁_le {γ₀ : ℂ} (him : γ₀.im ≠ 0) (him2 : |γ₀.im| ≤ 1 / 2) {s : ℝ} (hs : 0 < s)
    {v : ℂ} (hv : ‖v‖ = 1) :
    ‖pairC₁ γ₀ s v‖ ≤ 1 + Real.exp (s / 2) / (s * |γ₀.im|) := by
  unfold pairC₁
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_mul]
  have h1 := norm_pairC₂_le him hs hv
  have h2 := norm_cexp_I_mul_real_le him2 hs.le
  have : ‖pairC₂ γ₀ s v‖ * ‖Complex.exp (I * γ₀ * s)‖ ≤ 1 / (s * |γ₀.im|) * Real.exp (s / 2) :=
    mul_le_mul h1 h2 (norm_nonneg _) (by have := abs_pos.mpr him; positivity)
  rw [div_mul_eq_mul_div, one_mul] at this
  linarith

/-- On the strip, `|N| ≤ 1 + 3/(s|Im γ₀|)` for `s ≤ 1`. -/
theorem norm_nodeSymbol_pairC_le {γ₀ : ℂ} (him : γ₀.im ≠ 0) (him2 : |γ₀.im| ≤ 1 / 2) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) {v : ℂ} (hv : ‖v‖ = 1) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖nodeSymbol (pairC₁ γ₀ s v) (pairC₂ γ₀ s v) s z‖ ≤ 1 + 4 / (s * |γ₀.im|) := by
  have h := norm_nodeSymbol_le (pairC₁ γ₀ s v) (pairC₂ γ₀ s v) hs.le hz
  have h1 := norm_pairC₁_le him him2 hs hv
  have h2 := norm_pairC₂_le him hs hv
  have he : Real.exp (s / 2) ≤ 2 := by
    have : s / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    calc Real.exp (s / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr this
      _ = 2 := Real.exp_log (by norm_num)
  have hpos : 0 < s * |γ₀.im| := by have := abs_pos.mpr him; positivity
  have h3 : Real.exp (s / 2) / (s * |γ₀.im|) ≤ 2 / (s * |γ₀.im|) :=
    div_le_div_of_nonneg_right he hpos.le
  have h4 : ‖pairC₂ γ₀ s v‖ * Real.exp (s / 2) ≤ 1 / (s * |γ₀.im|) * 2 :=
    mul_le_mul h2 he (Real.exp_pos _).le (by positivity)
  have e : 1 / (s * |γ₀.im|) * 2 = 2 / (s * |γ₀.im|) := by ring
  have e2 : 4 / (s * |γ₀.im|) = 2 / (s * |γ₀.im|) + 2 / (s * |γ₀.im|) := by ring
  linarith

/-! ## The bump on the imaginary axis -/

theorem norm_paperFT_weilBumpC_I_mul_ge (y : ℝ) :
    Real.exp (-(|y| / 4)) * (∫ u, weilBump u) ≤ ‖paperFT weilBumpC ((y : ℂ) * I)‖ := by
  have hint : Integrable (fun u : ℝ => weilBumpC u * Complex.exp (I * ((y : ℂ) * I) * u)) :=
    ((contDiff_weilBumpC.continuous).mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_weilBumpC.mul_right
  have hre : (paperFT weilBumpC ((y : ℂ) * I)).re = ∫ u, weilBump u * Real.exp (-(y * u)) := by
    unfold paperFT
    have h1 := integral_re hint
    simp only [RCLike.re_to_complex] at h1
    rw [← h1]
    congr 1; funext u
    have e : Complex.exp (I * ((y : ℂ) * I) * (u : ℂ)) = ((Real.exp (-(y * u)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1
      have hI : I * I = -1 := Complex.I_mul_I
      push_cast; linear_combination ((y : ℂ) * (u : ℂ)) * hI
    rw [e]
    simp only [weilBumpC, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hbump_int : Integrable (fun u : ℝ => weilBump u) :=
    weilBump.continuous.integrable_of_hasCompactSupport weilBump.hasCompactSupport
  have hge : ∫ u, weilBump u * Real.exp (-(|y| / 4)) ≤ ∫ u, weilBump u * Real.exp (-(y * u)) := by
    refine integral_mono (hbump_int.mul_const _) ?_ fun u => ?_
    · exact (weilBump.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        weilBump.hasCompactSupport.mul_right
    · simp only
      by_cases hu : weilBump u = 0
      · simp [hu]
      · have hu' : |u| < 1 / 4 := by
          by_contra h; push Not at h
          have := weilBumpC_eq_zero h
          simp only [weilBumpC, Complex.ofReal_eq_zero] at this; exact hu this
        have hyu : -(|y| / 4) ≤ -(y * u) := by
          have h1 : y * u ≤ |y * u| := le_abs_self _
          rw [abs_mul] at h1
          have h2 : |y| * |u| ≤ |y| * (1 / 4) :=
            mul_le_mul_of_nonneg_left hu'.le (abs_nonneg y)
          linarith
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hyu) weilBump.nonneg
  rw [integral_mul_const] at hge
  calc Real.exp (-(|y| / 4)) * (∫ u, weilBump u) = (∫ u, weilBump u) * Real.exp (-(|y| / 4)) := by
        ring
    _ ≤ (paperFT weilBumpC ((y : ℂ) * I)).re := by rw [hre]; exact hge
    _ ≤ ‖paperFT weilBumpC ((y : ℂ) * I)‖ := Complex.re_le_norm _

/-- `|κ̂_w(iy)| ≥ 4w e^{-w|y|} ∫κ`. -/
theorem norm_paperFT_scaledBump_I_mul_ge {w : ℝ} (hw : 0 < w) (y : ℝ) :
    4 * w * (Real.exp (-(w * |y|)) * (∫ u, weilBump u)) ≤
      ‖paperFT (scaledBump w) ((y : ℂ) * I)‖ := by
  rw [paperFT_scaledBump hw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 4 * w)]
  have e : (((4 * w : ℝ) : ℂ)) * ((y : ℂ) * I) = (((4 * w * y : ℝ) : ℂ)) * I := by push_cast; ring
  rw [e]
  have h := norm_paperFT_weilBumpC_I_mul_ge (4 * w * y)
  have ha : |4 * w * y| / 4 = w * |y| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * w)]; ring
  rw [ha] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- At a point `x = ω + iy` with `|y| ≤ 1/2`: `|κ̂₂(x)| ≥ ω² · 4w e^{-w/2} ∫κ`. -/
theorem norm_paperFT_scaledBumpPolarFree_node_ge {w : ℝ} (hw : 0 < w) (ω : ℝ) {x : ℂ}
    (hxre : x.re = ω) (hxim : |x.im| ≤ 1 / 2) :
    ω ^ 2 * (4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u))) ≤
      ‖paperFT (scaledBumpPolarFree w ω) x‖ := by
  rw [paperFT_scaledBumpPolarFree hw, norm_mul, norm_neg]
  have hxω : x - (ω : ℂ) = ((x.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hxre]
  rw [hxω]
  have hb := norm_paperFT_scaledBump_I_mul_ge hw x.im
  have hbint : 0 ≤ ∫ u, weilBump u := integral_nonneg fun u => weilBump.nonneg
  have hb' : 4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)) ≤
      4 * w * (Real.exp (-(w * |x.im|)) * (∫ u, weilBump u)) := by
    gcongr
    nlinarith [abs_nonneg x.im]
  have hq : ω ^ 2 ≤ ‖x ^ 2 + 1 / 4‖ := by
    have hre : (x ^ 2 + 1 / 4 : ℂ).re = x.re ^ 2 - x.im ^ 2 + 1 / 4 := by
      simp [sq, Complex.mul_re]
    have h1 := Complex.re_le_norm (x ^ 2 + 1 / 4)
    rw [hre, hxre] at h1
    have h2 : x.im ^ 2 ≤ 1 / 4 := by
      have := abs_le.mp hxim; nlinarith
    linarith
  calc ω ^ 2 * (4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)))
      ≤ ‖x ^ 2 + 1 / 4‖ * ‖paperFT (scaledBump w) (((x.im : ℝ) : ℂ) * I)‖ :=
        mul_le_mul hq (hb'.trans hb) (by positivity) (norm_nonneg _)

/-! ## The test -/

/-- `f = N_{c₁,c₂,s}((h_{≤U}) ⋆ κ₂^{(w,ω)})`. -/
def pairLandauTest (h : ℝ → ℂ) (U w ω : ℝ) (c₁ c₂ : ℂ) (s : ℝ) : ℝ → ℂ :=
  nodeOp c₁ c₂ s (bumpedTest (cutoffCore U h) w ω)

theorem cutoffCore_support (U : ℝ) (h : ℝ → ℂ) : ∀ u, U < |u| → cutoffCore U h u = 0 :=
  fun _ hu => cutoffCore_eq_zero hu

theorem contDiff_pairLandauTest {h : ℝ → ℂ} (hh : Continuous h) (U : ℝ) {w : ℝ} (hw : 0 < w)
    (ω : ℝ) (c₁ c₂ : ℂ) (s : ℝ) : ContDiff ℝ 2 (pairLandauTest h U w ω c₁ c₂ s) := by
  have hg := contDiff_bumpedTest (integrable_cutoffCore (U := U) hh) hw ω
  unfold pairLandauTest nodeOp
  refine (contDiff_const.mul hg).add (contDiff_const.mul ?_)
  exact hg.comp (contDiff_id.sub contDiff_const)

theorem pairLandauTest_eq_zero {h : ℝ → ℂ} {U w : ℝ} (hw : 0 < w) (ω : ℝ) (c₁ c₂ : ℂ) {s : ℝ}
    (hs : 0 ≤ s) {x : ℝ} (hx : U + w + s < |x|) : pairLandauTest h U w ω c₁ c₂ s x = 0 := by
  unfold pairLandauTest nodeOp
  have h1 : U + w < |x| := by linarith
  have h2 : U + w < |x - s| := by
    have := abs_sub_abs_le_abs_sub x s; rw [abs_of_nonneg hs] at this; linarith
  rw [bumpedTest_eq_zero (cutoffCore_support U h) hw ω h1,
    bumpedTest_eq_zero (cutoffCore_support U h) hw ω h2]
  simp

theorem tsupport_pairLandauTest {h : ℝ → ℂ} {U w a : ℝ} (hw : 0 < w) (ω : ℝ) (c₁ c₂ : ℂ) {s : ℝ}
    (hs : 0 ≤ s) (ha : U + w + s ≤ a) : tsupport (pairLandauTest h U w ω c₁ c₂ s) ⊆ Icc (-a) a := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h' : ¬ U + w + s < |x| := fun h' => hx (pairLandauTest_eq_zero hw ω c₁ c₂ hs h')
  push Not at h'
  exact ⟨by linarith [(abs_le.mp h').1], by linarith [(abs_le.mp h').2]⟩

theorem paperFT_pairLandauTest {h : ℝ → ℂ} (hh : SuperExpDecay h) (U : ℝ) {w : ℝ} (hw : 0 < w)
    (ω : ℝ) (c₁ c₂ : ℂ) (s : ℝ) (z : ℂ) :
    paperFT (pairLandauTest h U w ω c₁ c₂ s) z = nodeSymbol c₁ c₂ s z *
      ((paperFT h z - paperFT (cutoffTail U h) z) * paperFT (scaledBumpPolarFree w ω) z) := by
  have hint : Integrable (cutoffCore U h) := integrable_cutoffCore hh.1
  have hg : Integrable (bumpedTest (cutoffCore U h) w ω) := by
    have hc : Continuous (bumpedTest (cutoffCore U h) w ω) :=
      (contDiff_bumpedTest hint hw ω).continuous
    exact hc.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs
      (Λ := U + w) fun u hu => by
        by_contra hc'; push Not at hc'
        exact hu (bumpedTest_eq_zero (cutoffCore_support U h) hw ω hc'))
  have hgz : Integrable (fun u => bumpedTest (cutoffCore U h) w ω u * Complex.exp (I * z * u)) :=
    integrable_mul_cexp_of_support hg (fun u hu => bumpedTest_eq_zero (cutoffCore_support U h)
      hw ω hu) z
  unfold pairLandauTest
  rw [paperFT_nodeOp hgz, paperFT_bumpedTest hint (cutoffCore_support U h) hw ω z,
    paperFT_cutoffCore_eq hh]

theorem paperFT_pairLandauTest_polar {h : ℝ → ℂ} (hh : SuperExpDecay h) (U : ℝ) {w : ℝ}
    (hw : 0 < w) (ω : ℝ) (c₁ c₂ : ℂ) (s : ℝ) :
    paperFT (pairLandauTest h U w ω c₁ c₂ s) (I / 2) = 0 ∧
      paperFT (pairLandauTest h U w ω c₁ c₂ s) (-(I / 2)) = 0 := by
  rw [paperFT_pairLandauTest hh U hw, paperFT_pairLandauTest hh U hw,
    paperFT_scaledBumpPolarFree_half_I hw, paperFT_scaledBumpPolarFree_neg_half_I hw]
  simp

/-! ## One off-line pair against the rest, with window decay -/

/-- **Pair split with window decay.** If `|f̂(γ_ρ)||f̂(γ̄_ρ)| ≤ K'/(1+|t_ρ-ω|)³` at every zero and
`≤ K/(1+|t_ρ-ω|)³` at every zero other than `ρ₀, ρ₁` (`γ_{ρ₁} = γ̄_{ρ₀}`), then
`Re W(f,f) ≤ (m₀+m₁) Re(f̂(γ₀) conj f̂(γ₁)) + 24 K A₀ log(|ω|+3)`. -/
theorem re_W_le_pair_add_window {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {f : ℝ → ℂ} {ρ₀ ρ₁ : ℂ} (h₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (h₁ : ρ₁ ∈ zetaZeroConfig.carrier) (hne : ρ₀ ≠ ρ₁)
    (hconj : gammaOf ρ₁ = (starRingEnd ℂ) (gammaOf ρ₀)) {ω K K' : ℝ} (hK : 0 ≤ K)
    (hall : ∀ ρ ∈ zetaZeroConfig.carrier, ‖paperFT f (gammaOf ρ)‖ *
      ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ K' / (1 + |ρ.im - ω|) ^ 3)
    (hother : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ ρ₁ → ‖paperFT f (gammaOf ρ)‖ *
      ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ K / (1 + |ρ.im - ω|) ^ 3) :
    (zetaZeroConfig.W f f).re ≤
      ((zetaZeroConfig.mult ρ₀ : ℝ) + zetaZeroConfig.mult ρ₁) *
        (paperFT f (gammaOf ρ₀) * (starRingEnd ℂ) (paperFT f (gammaOf ρ₁))).re +
      K * (24 * A₀ * Real.log (|ω| + 3)) := by
  obtain ⟨hsumm, hsumle⟩ := window_tsum_le zetaZeroConfig hA₀ hloc ω
  set ws : zetaZeroConfig.carrier → ℂ := fun ρ => zetaZeroConfig.Wsummand f f ρ with hws
  have hwsn : ∀ ρ : zetaZeroConfig.carrier, ‖ws ρ‖ = (zetaZeroConfig.mult ρ : ℝ) *
      (‖paperFT f (gammaOf ρ)‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖) := by
    intro ρ
    simp only [hws, ZeroConfig.Wsummand]
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]; ring
  have hK'0 : 0 ≤ K' := by
    have := hall ρ₀ h₀
    have hpos : 0 < (1 + |ρ₀.im - ω|) ^ 3 := by positivity
    have : 0 ≤ K' / (1 + |ρ₀.im - ω|) ^ 3 := le_trans (by positivity) this
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
  have hb : ∀ ρ : zetaZeroConfig.carrier, ‖ws ρ‖ ≤
      K' * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ω|) ^ 3) := by
    intro ρ
    rw [hwsn]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) * (‖paperFT f (gammaOf ρ)‖ *
          ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖)
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (K' / (1 + |(ρ : ℂ).im - ω|) ^ 3) :=
          mul_le_mul_of_nonneg_left (hall _ ρ.2) hm
      _ = K' * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ω|) ^ 3) := by ring
  have hsumws : Summable ws := Summable.of_norm_bounded (hsumm.mul_left K') hb
  set p₀ : zetaZeroConfig.carrier := ⟨ρ₀, h₀⟩
  set p₁ : zetaZeroConfig.carrier := ⟨ρ₁, h₁⟩
  have hp : p₀ ≠ p₁ := fun h => hne (congrArg Subtype.val h)
  classical
  set T : Set zetaZeroConfig.carrier :=
    ((↑({p₀, p₁} : Finset zetaZeroConfig.carrier) : Set zetaZeroConfig.carrier)ᶜ) with hT
  have hsplit : ws p₀ + ws p₁ + ∑' x : T, ws x = ∑' ρ, ws ρ := by
    have := hsumws.sum_add_tsum_compl (s := {p₀, p₁})
    rwa [Finset.sum_pair hp] at this
  have hW : zetaZeroConfig.W f f = ws p₀ + ws p₁ + ∑' x : T, ws x := by
    unfold ZeroConfig.W; rw [hsplit]
  have hnode : (ws p₀ + ws p₁).re = ((zetaZeroConfig.mult ρ₀ : ℝ) + zetaZeroConfig.mult ρ₁) *
      (paperFT f (gammaOf ρ₀) * (starRingEnd ℂ) (paperFT f (gammaOf ρ₁))).re := by
    have hc1 : (starRingEnd ℂ) (gammaOf ρ₁) = gammaOf ρ₀ := by rw [hconj]; simp
    simp only [hws, ZeroConfig.Wsummand, p₀, p₁]
    rw [← hconj, hc1]
    set A := paperFT f (gammaOf ρ₀)
    set B := paperFT f (gammaOf ρ₁)
    have hre : (B * (starRingEnd ℂ) A).re = (A * (starRingEnd ℂ) B).re := by
      rw [show B * (starRingEnd ℂ) A = (starRingEnd ℂ) (A * (starRingEnd ℂ) B) by simp [mul_comm],
        Complex.conj_re]
    have e0 : (zetaZeroConfig.mult ρ₀ : ℂ) * A * (starRingEnd ℂ) B =
        ((zetaZeroConfig.mult ρ₀ : ℝ) : ℂ) * (A * (starRingEnd ℂ) B) := by push_cast; ring
    have e1 : (zetaZeroConfig.mult ρ₁ : ℂ) * B * (starRingEnd ℂ) A =
        ((zetaZeroConfig.mult ρ₁ : ℝ) : ℂ) * (B * (starRingEnd ℂ) A) := by push_cast; ring
    rw [e0, e1, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hre]
    ring
  have hrest : (∑' x : T, ws x).re ≤ K * (24 * A₀ * Real.log (|ω| + 3)) := by
    have hbT : ∀ x : T, ‖ws x‖ ≤ K * ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
        (1 + |((x : zetaZeroConfig.carrier) : ℂ).im - ω|) ^ 3) := by
      intro x
      have hx := x.2
      simp only [T, Set.mem_compl_iff, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
      have hx0 : ((x : zetaZeroConfig.carrier) : ℂ) ≠ ρ₀ := fun h => hx.1 (Subtype.ext h)
      have hx1 : ((x : zetaZeroConfig.carrier) : ℂ) ≠ ρ₁ := fun h => hx.2 (Subtype.ext h)
      rw [hwsn]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult (x : zetaZeroConfig.carrier) := Nat.cast_nonneg _
      calc (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) *
            (‖paperFT f (gammaOf (x : zetaZeroConfig.carrier))‖ *
              ‖paperFT f ((starRingEnd ℂ) (gammaOf (x : zetaZeroConfig.carrier)))‖)
          ≤ (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) *
              (K / (1 + |((x : zetaZeroConfig.carrier) : ℂ).im - ω|) ^ 3) :=
            mul_le_mul_of_nonneg_left (hother _ (x : zetaZeroConfig.carrier).2 hx0 hx1) hm
        _ = K * ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
              (1 + |((x : zetaZeroConfig.carrier) : ℂ).im - ω|) ^ 3) := by ring
    have hsT : Summable (fun x : T => K * ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
        (1 + |((x : zetaZeroConfig.carrier) : ℂ).im - ω|) ^ 3)) :=
      (hsumm.subtype T).mul_left _
    have hwsT : Summable (fun x : T => ‖ws x‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbT hsT
    calc (∑' x : T, ws x).re ≤ ‖∑' x : T, ws x‖ := Complex.re_le_norm _
      _ ≤ ∑' x : T, ‖ws x‖ := norm_tsum_le_tsum_norm hwsT
      _ ≤ ∑' x : T, K * ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
            (1 + |((x : zetaZeroConfig.carrier) : ℂ).im - ω|) ^ 3) :=
          Summable.tsum_le_tsum hbT hwsT hsT
      _ = K * ∑' x : T, ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
            (1 + |((x : zetaZeroConfig.carrier) : ℂ).im - ω|) ^ 3) := tsum_mul_left
      _ ≤ K * (24 * A₀ * Real.log (|ω| + 3)) := by
          apply mul_le_mul_of_nonneg_left _ hK
          refine le_trans ?_ hsumle
          exact Summable.tsum_subtype_le (fun ρ : zetaZeroConfig.carrier =>
            (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ω|) ^ 3) T
            (fun _ => by positivity) hsumm
  rw [hW, Complex.add_re, hnode]
  linarith

/-! ## The pair inequality -/

/-- The arithmetic of the node block: if `0 ≤ M(-x₀x₁ + x₀y₁ + y₀x₁ + y₀y₁) + e²R` with
`M ≥ 2`, `0 ≤ y_j ≤ e` and `λ ≤ x_j`, then `λ ≤ e(3 + R/2)`. -/
theorem pair_node_arith {x₀ x₁ y₀ y₁ e lam M R : ℝ} (hM : 2 ≤ M) (hR : 0 ≤ R) (he0 : 0 ≤ e)
    (hy₀ : y₀ ≤ e) (hy₁ : y₁ ≤ e) (hy₁0 : 0 ≤ y₁) (hx₀ : lam ≤ x₀)
    (hx₁ : lam ≤ x₁) (hlam : 0 ≤ lam)
    (hmain : 0 ≤ M * (-(x₀ * x₁) + x₀ * y₁ + y₀ * x₁ + y₀ * y₁) + e ^ 2 * R) :
    lam ≤ e * (3 + R / 2) := by
  have hx₀0 : 0 ≤ x₀ := le_trans hlam hx₀
  have hx₁0 : 0 ≤ x₁ := le_trans hlam hx₁
  have hblock : x₀ * x₁ - x₀ * y₁ - y₀ * x₁ - y₀ * y₁ ≤ e ^ 2 * R / 2 := by
    have h1 : M * (x₀ * x₁ - x₀ * y₁ - y₀ * x₁ - y₀ * y₁) ≤ e ^ 2 * R := by linarith
    by_contra hc
    push Not at hc
    have h2 : 0 ≤ e ^ 2 * R / 2 := by positivity
    have hb0 : 0 ≤ x₀ * x₁ - x₀ * y₁ - y₀ * x₁ - y₀ * y₁ := le_trans h2 hc.le
    have : 2 * (x₀ * x₁ - x₀ * y₁ - y₀ * x₁ - y₀ * y₁) ≤
        M * (x₀ * x₁ - x₀ * y₁ - y₀ * x₁ - y₀ * y₁) := mul_le_mul_of_nonneg_right hM hb0
    linarith
  have hlow : (x₀ - e) * (x₁ - e) - 2 * e ^ 2 ≤ x₀ * x₁ - x₀ * y₁ - y₀ * x₁ - y₀ * y₁ := by
    have t1 : x₀ * y₁ ≤ x₀ * e := mul_le_mul_of_nonneg_left hy₁ hx₀0
    have t2 : y₀ * x₁ ≤ e * x₁ := mul_le_mul_of_nonneg_right hy₀ hx₁0
    have t3 : y₀ * y₁ ≤ e * e := mul_le_mul hy₀ hy₁ hy₁0 he0
    nlinarith
  by_contra hc
  push Not at hc
  have hZ : 1 ≤ 2 + R / 2 := by linarith
  have hd : e * (2 + R / 2) < lam - e := by linarith
  have hd0 : 0 ≤ e * (2 + R / 2) := by positivity
  have hsq : (e * (2 + R / 2)) ^ 2 < (lam - e) ^ 2 := by nlinarith
  have hprod : (lam - e) ^ 2 ≤ (x₀ - e) * (x₁ - e) := by
    have ha : 0 ≤ lam - e := by linarith
    have := mul_le_mul (sub_le_sub_right hx₀ e) (sub_le_sub_right hx₁ e) ha (by linarith)
    nlinarith
  have hbig : e ^ 2 * (2 + R / 2) ≤ (e * (2 + R / 2)) ^ 2 := by
    have : e ^ 2 * (2 + R / 2) * 1 ≤ e ^ 2 * (2 + R / 2) * (2 + R / 2) :=
      mul_le_mul_of_nonneg_left hZ (by positivity)
    nlinarith
  nlinarith

/-- `‖ĥ(z)‖ ≤ ∫ |h| e^{|u|/2}` on the strip. -/
theorem norm_paperFT_le_expTail_half {h : ℝ → ℂ} (hh : SuperExpDecay h) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) : ‖paperFT h z‖ ≤ expTail h (1 / 2) (-1) := by
  have e : cutoffTail (-1) h = h := by
    funext u; unfold cutoffTail
    exact indicator_of_mem (show u ∈ {u : ℝ | -1 < |u|} by
      simp only [mem_setOf_eq]; linarith [abs_nonneg u]) _
  have := norm_paperFT_cutoffTail_le (U := -1) hh hz
  rwa [e] at this

/-- At zeros other than the pair, the divided kernel vanishes. -/
theorem paperFT_divided_eq_zero_of_zero {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ}
    {h : ℝ → ℂ} {m₀ m₁ : ℕ}
    (hprod : ∀ z, (z - gammaOf ρ₀) ^ m₀ * (z - (starRingEnd ℂ) (gammaOf ρ₀)) ^ m₁ *
      paperFT h z = paperFT (tiltedPhi θ) z)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (h0 : ρ ≠ ρ₀) (h1 : ρ ≠ Zeta23.reflect ρ₀) :
    paperFT h (gammaOf ρ) = 0 := by
  have hnt : IsNontrivialZero ρ := hρ
  have hIm : |(gammaOf ρ).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt ⟨hnt.2.1, hnt.2.2⟩).le
  have hΦ : paperFT (tiltedPhi θ) (gammaOf ρ) = 0 := by
    rw [paperFT_tiltedPhi hθ0 hθ hIm, one_half_add_I_mul_gammaOf,
      riemannPhiTransform_eq_zero_of_nontrivial hnt.1 hnt.2.1 hnt.2.2, mul_zero]
  have hp := hprod (gammaOf ρ)
  rw [hΦ] at hp
  have hne0 : gammaOf ρ - gammaOf ρ₀ ≠ 0 :=
    sub_ne_zero.mpr fun h => h0 (gammaOf_injective h)
  have hne1 : gammaOf ρ - (starRingEnd ℂ) (gammaOf ρ₀) ≠ 0 := by
    rw [← gammaOf_reflect']
    exact sub_ne_zero.mpr fun h => h1 (gammaOf_injective h)
  exact (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (pow_ne_zero _ hne0) (pow_ne_zero _ hne1))

/-- **The pair inequality.** Let `h` be divided at the off-line pair of `ρ₀` (`t₀ ≥ 0`), and let the
level-`a` Hodge index hold. For `U + w + s ≤ a`, `0 < w ≤ 1/4`, `0 < s ≤ 1`, if the node values
`X_j = ĥ(γ_j) κ̂₂(γ_j)` satisfy `|X_j| ≥ λ ≥ 0`, then
`λ ≤ ε B_w (1+t₀)² (3 + 12 N² A₀ log(t₀+3))`, with `ε = ∫_{|u|>U} |h| e^{|u|/2}` and
`N = 1 + 4/(s|β₀ - 1/2|)`. -/
theorem pairLandau_inequality {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hoff : ρ₀.re ≠ 1 / 2) (ht₀ : 0 ≤ ρ₀.im) {h : ℝ → ℂ} (hh : SuperExpDecay h)
    (hprod : ∀ z, (z - gammaOf ρ₀) ^ zetaZeroConfig.mult ρ₀ *
      (z - (starRingEnd ℂ) (gammaOf ρ₀)) ^ zetaZeroConfig.mult ρ₀ * paperFT h z =
        paperFT (tiltedPhi θ) z)
    {U w s a : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : U + w + s ≤ a) (hH : HodgeIndexAtLevel zetaZeroConfig a) {lam : ℝ} (hlam : 0 ≤ lam)
    (hX₀ : lam ≤ ‖paperFT h (gammaOf ρ₀)‖ *
      ‖paperFT (scaledBumpPolarFree w ρ₀.im) (gammaOf ρ₀)‖)
    (hX₁ : lam ≤ ‖paperFT h ((starRingEnd ℂ) (gammaOf ρ₀))‖ *
      ‖paperFT (scaledBumpPolarFree w ρ₀.im) ((starRingEnd ℂ) (gammaOf ρ₀))‖) :
    lam ≤ expTail h (1 / 2) U * (scaledBumpConst w * (1 + ρ₀.im) ^ 2) *
      (3 + 12 * (1 + 4 / (s * |ρ₀.re - 1 / 2|)) ^ 2 * A₀ * Real.log (ρ₀.im + 3)) := by
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  set t₀ := ρ₀.im with ht₀def
  set γ₀ := gammaOf ρ₀ with hγ₀def
  set γ₁ := (starRingEnd ℂ) γ₀ with hγ₁def
  set ρ₁ := Zeta23.reflect ρ₀ with hρ₁def
  have h₁ : ρ₁ ∈ zetaZeroConfig.carrier := zetaZeroConfig.reflect_mem ρ₀ hρ₀
  have hγ₁ρ : gammaOf ρ₁ = γ₁ := by rw [hρ₁def, gammaOf_reflect']
  have hne : ρ₀ ≠ ρ₁ := by
    intro h; have := congrArg Complex.re h
    simp [hρ₁def, Zeta23.reflect] at this; exact hoff (by linarith)
  have hγ₀im : γ₀.im = 1 / 2 - ρ₀.re := WeilEF.gammaOf_im ρ₀
  have hγ₀re : γ₀.re = t₀ := WeilEF.gammaOf_re ρ₀
  have him : γ₀.im ≠ 0 := by rw [hγ₀im]; intro h; exact hoff (by linarith)
  have him2 : |γ₀.im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt ⟨hnt.2.1, hnt.2.2⟩).le
  have him2' : |γ₁.im| ≤ 1 / 2 := by rw [hγ₁def, Complex.conj_im, abs_neg]; exact him2
  have hγ₁re : γ₁.re = t₀ := by rw [hγ₁def, Complex.conj_re]; exact hγ₀re
  have habsim : |γ₀.im| = |ρ₀.re - 1 / 2| := by rw [hγ₀im, abs_sub_comm]
  -- node values
  set κ := scaledBumpPolarFree w t₀ with hκ
  set X₀ := paperFT h γ₀ * paperFT κ γ₀ with hX₀def
  set X₁ := paperFT h γ₁ * paperFT κ γ₁ with hX₁def
  set Y₀ := paperFT (cutoffTail U h) γ₀ * paperFT κ γ₀ with hY₀def
  set Y₁ := paperFT (cutoffTail U h) γ₁ * paperFT κ γ₁ with hY₁def
  set Q := X₀ * (starRingEnd ℂ) X₁ with hQdef
  set v := pairPhase Q with hvdef
  have hv : ‖v‖ = 1 := norm_pairPhase Q
  set c₁ := pairC₁ γ₀ s v
  set c₂ := pairC₂ γ₀ s v
  set f := pairLandauTest h U w t₀ c₁ c₂ s with hfdef
  have hf : ∀ z, paperFT f z = nodeSymbol c₁ c₂ s z *
      ((paperFT h z - paperFT (cutoffTail U h) z) * paperFT κ z) :=
    fun z => paperFT_pairLandauTest hh U hw t₀ c₁ c₂ s z
  have hfγ₀ : paperFT f γ₀ = X₀ - Y₀ := by
    rw [hf, nodeSymbol_pairC_γ₀]; ring
  have hfγ₁ : paperFT f γ₁ = v * (X₁ - Y₁) := by
    rw [hf, hγ₁def, nodeSymbol_pairC_γ₁ him hs]; ring
  -- Hodge positivity
  have hpolar := paperFT_pairLandauTest_polar hh U hw t₀ c₁ c₂ s
  have hpos := hH f (contDiff_pairLandauTest hh.1 U hw t₀ c₁ c₂ s)
    (tsupport_pairLandauTest hw t₀ c₁ c₂ hs.le ha) hpolar.1 hpolar.2
  -- bounds on the strip
  set ε := expTail h (1 / 2) U with hε
  set G := expTail h (1 / 2) (-1) with hG
  set Bw := scaledBumpConst w * (1 + t₀) ^ 2 with hBw
  set CN := 1 + 4 / (s * |ρ₀.re - 1 / 2|) with hCN
  have hε0 : 0 ≤ ε := expTail_nonneg _ _ _
  have hG0 : 0 ≤ G := expTail_nonneg _ _ _
  have hBw0 : 0 ≤ Bw := by have := scaledBumpConst_nonneg hw; positivity
  have hCN1 : 1 ≤ CN := by
    have : 0 ≤ 4 / (s * |ρ₀.re - 1 / 2|) := by positivity
    linarith
  have hN : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖nodeSymbol c₁ c₂ s z‖ ≤ CN := by
    intro z hz
    have := norm_nodeSymbol_pairC_le him him2 hs hs1 hv hz
    rwa [habsim] at this
  have hκb : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖paperFT κ z‖ ≤ Bw / (1 + |z.re - t₀|) ^ 2 := by
    intro z hz
    have := norm_paperFT_scaledBumpPolarFree_le hw hw4 t₀ hz
    rw [abs_of_nonneg ht₀] at this
    rw [hBw]; exact this
  have htail : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT (cutoffTail U h) z‖ ≤ ε :=
    fun z hz => norm_paperFT_cutoffTail_le hh hz
  have hhb : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT h z‖ ≤ G :=
    fun z hz => norm_paperFT_le_expTail_half hh hz
  -- the pointwise bound for `f̂`
  have hfb : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ∀ E : ℝ, ‖paperFT h z‖ ≤ E - ε →
      ‖paperFT f z‖ ≤ CN * E * Bw / (1 + |z.re - t₀|) ^ 2 := by
    intro z hz E hE
    rw [hf, norm_mul, norm_mul]
    have h1 := hN z hz
    have h2 : ‖paperFT h z - paperFT (cutoffTail U h) z‖ ≤ E :=
      (norm_sub_le _ _).trans (by linarith [htail z hz])
    have h3 := hκb z hz
    have hE0 : 0 ≤ E := le_trans (norm_nonneg _) h2
    calc ‖nodeSymbol c₁ c₂ s z‖ * (‖paperFT h z - paperFT (cutoffTail U h) z‖ * ‖paperFT κ z‖)
        ≤ CN * (E * (Bw / (1 + |z.re - t₀|) ^ 2)) := by gcongr
      _ = CN * E * Bw / (1 + |z.re - t₀|) ^ 2 := by ring
  have hzero_pts : ∀ ρ ∈ zetaZeroConfig.carrier,
      |(gammaOf ρ).im| ≤ 1 / 2 ∧ |((starRingEnd ℂ) (gammaOf ρ)).im| ≤ 1 / 2 ∧
      (gammaOf ρ).re = ρ.im ∧ ((starRingEnd ℂ) (gammaOf ρ)).re = ρ.im := by
    intro ρ hρ
    have h : IsNontrivialZero ρ := hρ
    have hIm := (WeilEF.abs_gammaOf_im_lt ⟨h.2.1, h.2.2⟩).le
    exact ⟨hIm, by rw [Complex.conj_im, abs_neg]; exact hIm, WeilEF.gammaOf_re ρ,
      by rw [Complex.conj_re, WeilEF.gammaOf_re]⟩
  have hsq4 : ∀ D : ℝ, 1 ≤ D → ∀ A : ℝ, 0 ≤ A → A / D ^ 2 * (A / D ^ 2) ≤ A ^ 2 / D ^ 3 := by
    intro D hD A hA
    rw [div_mul_div_comm, ← sq, ← pow_add]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ hD (by norm_num)
  have hall : ∀ ρ ∈ zetaZeroConfig.carrier, ‖paperFT f (gammaOf ρ)‖ *
      ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        (CN * (G + ε) * Bw) ^ 2 / (1 + |ρ.im - t₀|) ^ 3 := by
    intro ρ hρ
    obtain ⟨hi1, hi2, hr1, hr2⟩ := hzero_pts ρ hρ
    have b1 := hfb _ hi1 (G + ε) (by linarith [hhb _ hi1])
    have b2 := hfb _ hi2 (G + ε) (by linarith [hhb _ hi2])
    rw [hr1] at b1; rw [hr2] at b2
    have hD : 1 ≤ 1 + |ρ.im - t₀| := by linarith [abs_nonneg (ρ.im - t₀)]
    calc ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (CN * (G + ε) * Bw / (1 + |ρ.im - t₀|) ^ 2) *
            (CN * (G + ε) * Bw / (1 + |ρ.im - t₀|) ^ 2) :=
          mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
      _ ≤ (CN * (G + ε) * Bw) ^ 2 / (1 + |ρ.im - t₀|) ^ 3 := hsq4 _ hD _ (by positivity)
  have hother : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ ρ₁ → ‖paperFT f (gammaOf ρ)‖ *
      ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ (CN * ε * Bw) ^ 2 / (1 + |ρ.im - t₀|) ^ 3 := by
    intro ρ hρ h0 h1
    obtain ⟨hi1, hi2, hr1, hr2⟩ := hzero_pts ρ hρ
    have hz1 : paperFT h (gammaOf ρ) = 0 :=
      paperFT_divided_eq_zero_of_zero hθ0 hθ hprod hρ h0 h1
    have hrefl := zetaZeroConfig.reflect_mem ρ hρ
    have hz2 : paperFT h ((starRingEnd ℂ) (gammaOf ρ)) = 0 := by
      rw [← gammaOf_reflect']
      refine paperFT_divided_eq_zero_of_zero hθ0 hθ hprod hrefl ?_ ?_
      · intro h; apply h1; rw [hρ₁def, ← h, reflect_reflect]
      · intro h; apply h0
        have := congrArg Zeta23.reflect h
        rwa [reflect_reflect, reflect_reflect] at this
    have b1 := hfb _ hi1 ε (by rw [hz1, norm_zero]; linarith)
    have b2 := hfb _ hi2 ε (by rw [hz2, norm_zero]; linarith)
    rw [hr1] at b1; rw [hr2] at b2
    have hD : 1 ≤ 1 + |ρ.im - t₀| := by linarith [abs_nonneg (ρ.im - t₀)]
    calc ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (CN * ε * Bw / (1 + |ρ.im - t₀|) ^ 2) * (CN * ε * Bw / (1 + |ρ.im - t₀|) ^ 2) :=
          mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
      _ ≤ (CN * ε * Bw) ^ 2 / (1 + |ρ.im - t₀|) ^ 3 := hsq4 _ hD _ (by positivity)
  have hsplit := re_W_le_pair_add_window hA₀ hloc hρ₀ h₁ hne hγ₁ρ (by positivity) hall hother
  rw [hγ₁ρ, hfγ₀, hfγ₁, abs_of_nonneg ht₀] at hsplit
  -- the node block
  have hQv : X₀ * (starRingEnd ℂ) X₁ * (starRingEnd ℂ) v = -(‖X₀ * (starRingEnd ℂ) X₁‖ : ℂ) :=
    mul_conj_pairPhase Q
  have hblock := OffLinePairData.re_node_block_le (Y₀ := Y₀) (Y₁ := Y₁) hv hQv
  have hY₀ : ‖Y₀‖ ≤ ε * Bw := by
    rw [hY₀def, norm_mul]
    have := hκb γ₀ him2; rw [hγ₀re, sub_self, abs_zero, add_zero, one_pow, div_one] at this
    exact mul_le_mul (htail γ₀ him2) this (norm_nonneg _) hε0
  have hY₁ : ‖Y₁‖ ≤ ε * Bw := by
    rw [hY₁def, norm_mul]
    have := hκb γ₁ him2'; rw [hγ₁re, sub_self, abs_zero, add_zero, one_pow, div_one] at this
    exact mul_le_mul (htail γ₁ him2') this (norm_nonneg _) hε0
  have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ₀ := by
    exact_mod_cast zetaZeroConfig.one_le_mult ρ₀ hρ₀
  have hmr : zetaZeroConfig.mult ρ₁ = zetaZeroConfig.mult ρ₀ := zetaZeroConfig.mult_reflect ρ₀ hρ₀
  rw [hmr] at hsplit
  set M := (zetaZeroConfig.mult ρ₀ : ℝ) + zetaZeroConfig.mult ρ₀ with hMdef
  have hM2 : 2 ≤ M := by rw [hMdef]; linarith
  set R := CN ^ 2 * (24 * A₀ * Real.log (t₀ + 3)) with hR
  have hlog0 : 0 ≤ Real.log (t₀ + 3) := Real.log_nonneg (by linarith)
  have hR0 : 0 ≤ R := by have : 0 ≤ A₀ := by linarith
                         positivity
  have hmain : 0 ≤ M * (-(‖X₀‖ * ‖X₁‖) + ‖X₀‖ * ‖Y₁‖ + ‖Y₀‖ * ‖X₁‖ + ‖Y₀‖ * ‖Y₁‖) +
      (ε * Bw) ^ 2 * R := by
    have h1 := mul_le_mul_of_nonneg_left hblock (by linarith : (0 : ℝ) ≤ M)
    have e : (CN * ε * Bw) ^ 2 * (24 * A₀ * Real.log (t₀ + 3)) = (ε * Bw) ^ 2 * R := by
      rw [hR]; ring
    rw [e] at hsplit
    have hre : ((X₀ - Y₀) * (starRingEnd ℂ) (v * (X₁ - Y₁))).re =
        (paperFT f γ₀ * (starRingEnd ℂ) (paperFT f γ₁)).re := by rw [hfγ₀, hfγ₁]
    linarith
  have hx₀ : lam ≤ ‖X₀‖ := by rw [hX₀def, norm_mul]; exact hX₀
  have hx₁ : lam ≤ ‖X₁‖ := by rw [hX₁def, norm_mul]; exact hX₁
  have harith := pair_node_arith hM2 hR0 (by positivity) hY₀ hY₁ (norm_nonneg _) hx₀ hx₁ hlam hmain
  have e2 : ε * Bw * (3 + R / 2) = ε * Bw * (3 + 12 * CN ^ 2 * A₀ * Real.log (t₀ + 3)) := by
    rw [hR]; ring
  rw [e2] at harith
  exact harith

end

end RHTower
