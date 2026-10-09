import GaloisForLFunctions.HTGeometry.CircleSymbolGroupCStar
import GaloisForLFunctions.HTGeometry.ConeCrossedProductFaithful
import GaloisForLFunctions.HTGeometry.CompactKernelRankOneDensity

/-!
# The Wiener–Hopf extension of the cone crossed product and its connecting map

Crossing the coefficient extension `0 → C₀(ℝ) → C₀((-∞, +∞]) → ℂ → 0` by the translation action of
`ℝ` (which fixes `+∞` and acts freely on the open ideal) gives the **Wiener–Hopf extension**
`0 → C₀(ℝ) ⋊ ℝ → C₀((-∞, +∞]) ⋊ ℝ → C*(ℝ) → 0` of full crossed products
(`wienerHopf_extension_exact`), with ideal `C₀(ℝ) ⋊ ℝ ≅ 𝒦(L²(ℝ))` (SAC.14) and quotient
`C*(ℝ) ≅ C₀(ℝ̂)` (`realGroupCStarEquiv`).

* `isCompactOperator_coneSchrodinger_sub`: in the Schrödinger representation every element is
  `M_χ C_{σ(y)}` modulo compact operators, where `σ` is the symbol at `+∞` and `M_χ` multiplication
  by the cut-off (on the core: `χ(x) G(x - y) + k(x, y)` acts as `M_χ C_G + T_k`).
* Exactness in the middle: zero symbol forces a compact Schrödinger image, which comes from the ideal
  (full = reduced on both sides).  Surjectivity of the symbol: the cut-off lifts `χG` of a convergent
  core sequence are Cauchy, since `‖χG‖ = ‖M_χ C_G‖ ≤ ‖C_G‖`.
* **The connecting map is the analytic Wiener–Hopf index** (`wienerHopf_connecting_index`,
  `wienerHopf_connecting_map`): for a unimodular symbol `u` on the circle every lift `c + y` of
  `C_u` has Fredholm Schrödinger image of index `wind(u)`.  Modulo compact operators
  `c + ρ(y) = (P₊ + c(1 - P₊)) T_u`, using `M_χ - P₊ = (M_χ - P₊) M_b` with a bump `b`, compactness of
  `M_b C_W` for `W` vanishing at `1`, the compact Hankel operator, and the Wiener–Hopf index theorem
  `ind T_u = wind(u)`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped CompactlySupported ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open BandKernel

/-! ## Multiplied convolution kernels -/

namespace BandKernel

theorem isBandKernel_mulConv {a : ℝ → ℂ} (ha : Continuous a) (hb : ∀ x, ‖a x‖ ≤ 1)
    (G : C_c(ℝ, ℂ)) : IsBandKernel fun p : ℝ × ℝ => a p.1 * G (p.1 - p.2) := by
  have h := (conv G).isBandKernel
  refine ⟨(ha.comp continuous_fst).mul h.continuous, ⟨(conv G).sup, fun p => ?_⟩,
    ⟨(conv G).width, fun x y hxy => ?_⟩⟩
  · rw [norm_mul]
    calc ‖a p.1‖ * ‖G (p.1 - p.2)‖ ≤ 1 * (conv G).sup :=
          mul_le_mul (hb _) ((conv G).norm_toFun_le p) (norm_nonneg _) zero_le_one
      _ = (conv G).sup := one_mul _
  · change a x * G (x - y) = 0
    rw [← conv_toFun, (conv G).toFun_eq_zero hxy, mul_zero]

/-- The kernel `a(x) G(x - y)`. -/
def mulConv {a : ℝ → ℂ} (ha : Continuous a) (hb : ∀ x, ‖a x‖ ≤ 1) (G : C_c(ℝ, ℂ)) :
    BandKernel := mk _ (isBandKernel_mulConv ha hb G)

theorem mulConv_toFun {a : ℝ → ℂ} (ha : Continuous a) (hb : ∀ x, ‖a x‖ ≤ 1) (G : C_c(ℝ, ℂ))
    (x y : ℝ) : (mulConv ha hb G).toFun (x, y) = a x * G (x - y) := rfl

end BandKernel

/-- Multiplication by a continuous function bounded by `1` on `L²(ℝ)`. -/
def mulOp {a : ℝ → ℂ} (ha : Continuous a) (hb : ∀ x, ‖a x‖ ≤ 1) : L2Real →L[ℂ] L2Real :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) ha.measurable zero_le_one hb

theorem mulOp_ae {a : ℝ → ℂ} (ha : Continuous a) (hb : ∀ x, ‖a x‖ ≤ 1) (f : L2Real) :
    (mulOp ha hb f : ℝ → ℂ) =ᵐ[volume] fun x => a x * f x :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem norm_mulOp_le {a : ℝ → ℂ} (ha : Continuous a) (hb : ∀ x, ‖a x‖ ≤ 1) :
    ‖mulOp ha hb‖ ≤ 1 :=
  norm_lpBoundedMulCLM_le _ _ _

/-- **`T_{a(x) G(x - y)} = M_a C_G`.** -/
theorem op_mulConv {a : ℝ → ℂ} (ha : Continuous a) (hb : ∀ x, ‖a x‖ ≤ 1) (G : C_c(ℝ, ℂ)) :
    (mulConv ha hb G).op = mulOp ha hb * (conv G).op := by
  ext1 f
  apply Lp.ext
  filter_upwards [(mulConv ha hb G).op_ae f, mulOp_ae ha hb ((conv G).op f), (conv G).op_ae f]
    with x h1 h2 h3
  rw [h1, show (mulOp ha hb * (conv G).op) f = mulOp ha hb ((conv G).op f) from rfl, h2, h3,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [mulConv_toFun, conv_toFun]
  ring

theorem norm_coneCut_le (x : ℝ) : ‖(coneCut x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coneCut_nonneg x)]
  exact coneCut_le_one x

theorem continuous_coneCut_complex : Continuous fun x : ℝ => (coneCut x : ℂ) :=
  Complex.continuous_ofReal.comp continuous_coneCut

/-- Multiplication by the cut-off `χ`. -/
def coneCutMul : L2Real →L[ℂ] L2Real := mulOp continuous_coneCut_complex norm_coneCut_le

theorem op_cutConv (G : C_c(ℝ, ℂ)) : (cutConv G).op = coneCutMul * (conv G).op :=
  op_mulConv continuous_coneCut_complex norm_coneCut_le G

/-! ## The Schrödinger image is `M_χ (symbol)` modulo compact operators -/

/-- **`ρ(y) - M_χ C_{σ(y)}` is compact** for every element of `C₀((-∞, +∞]) ⋊ ℝ`. -/
theorem isCompactOperator_coneSchrodinger_sub (y : ConeCrossedProduct) :
    IsCompactOperator ⇑(coneSchrodinger y - coneCutMul * convRegular (coneSymbolMap y)) := by
  have hc : Continuous fun y : ConeCrossedProduct =>
      coneSchrodinger y - coneCutMul * convRegular (coneSymbolMap y) :=
    continuous_coneSchrodinger.sub (continuous_const.mul
      (continuous_convRegular.comp continuous_coneSymbolMap))
  have hP : IsClosed {y : ConeCrossedProduct |
      IsCompactOperator ⇑(coneSchrodinger y - coneCutMul * convRegular (coneSymbolMap y))} :=
    (isClosed_setOf_isCompactOperator (𝕜₁ := ℂ) (M₁ := L2Real) (M₂ := L2Real)).preimage hc
  refine (toEnvelope_dense coneKernels coneL1Norm).induction_on y hP fun K => ?_
  change IsCompactOperator ⇑((K : BandKernel).op -
    coneCutMul * convRegular (coneSymbolMap (toEnvelope coneKernels coneL1Norm K)))
  rw [coneSymbolMap_toEnvelope, convRegular_toEnvelope, coneSymbolHom_apply, ← op_cutConv]
  have h : (K : BandKernel).op - (cutConv (coneSymbol K)).op = (coneRemainder K).op := by
    rw [coneKernel_decomp K, op_add, op_ofKernelAlg, add_sub_cancel_left]
  rw [h, ← schrodinger_toEnvelope]
  exact isCompactOperator_schrodinger _

/-! ## The Wiener–Hopf extension `0 → C₀(ℝ) ⋊ ℝ → C₀((-∞, +∞]) ⋊ ℝ → C*(ℝ) → 0` -/

/-- The ideal map is injective: it is isometric through the Schrödinger representations. -/
theorem coneIdealMap_injective : Function.Injective coneIdealMap := fun y z h =>
  schrodinger_injective (by rw [← coneSchrodinger_coneIdealMap, h, coneSchrodinger_coneIdealMap])

theorem coneSymbolMap_coneIdealMap (y : RealCrossedProduct) : coneSymbolMap (coneIdealMap y) = 0 := by
  have h := (toEnvelope_dense KernelAlg KernelAlg.l1Norm).equalizer
    (continuous_coneSymbolMap.comp continuous_coneIdealMap) continuous_const
    (funext fun k => by
      change coneSymbolMap (coneIdealMap (toRCP k)) = 0
      rw [coneIdealMap_toRCP, coneSymbolMap_toEnvelope]
      have : coneSymbolHom (coneIdealHom k) = 0 := Subtype.ext (by
        rw [coneSymbolHom_apply, coneSymbol_coneIdealHom, conv_zero]
        rfl)
      rw [this, map_zero])
  exact congrFun h y

/-- **Exactness in the middle**: an element with zero symbol lies in the compact ideal. -/
theorem exists_coneIdealMap_of_coneSymbolMap_eq_zero {y : ConeCrossedProduct}
    (hy : coneSymbolMap y = 0) : ∃ z, coneIdealMap z = y := by
  have hc := isCompactOperator_coneSchrodinger_sub y
  rw [hy, map_zero, mul_zero, sub_zero] at hc
  obtain ⟨z, hz⟩ := compact_mem_range_schrodinger hc
  exact ⟨z, coneSchrodinger_injective (by rw [coneSchrodinger_coneIdealMap, hz])⟩

/-- The cut-off lift `χG` of a convolution kernel. -/
def cutLift (K : convKernels) : coneKernels := cutElem (convProfileOf K)

theorem coneSymbolHom_cutLift (K : convKernels) : coneSymbolHom (cutLift K) = K :=
  Subtype.ext (by rw [coneSymbolHom_apply, cutLift, coneSymbol_cutElem, conv_convProfileOf])

theorem conv_sub (G₁ G₂ : C_c(ℝ, ℂ)) : conv (G₁ - G₂) = conv G₁ - conv G₂ := ext fun _ => rfl

theorem cutElem_sub (G₁ G₂ : C_c(ℝ, ℂ)) : cutElem (G₁ - G₂) = cutElem G₁ - cutElem G₂ :=
  Subtype.ext (ext fun p => by
    change (coneCut p.1 : ℂ) * (G₁ (p.1 - p.2) - G₂ (p.1 - p.2)) =
      (coneCut p.1 : ℂ) * G₁ (p.1 - p.2) - (coneCut p.1 : ℂ) * G₂ (p.1 - p.2)
    rw [mul_sub])

theorem cutLift_sub (K L : convKernels) : cutLift (K - L) = cutLift K - cutLift L := by
  have h : convProfileOf (K - L) = convProfileOf K - convProfileOf L :=
    conv_injective (by
      rw [conv_convProfileOf, conv_sub, conv_convProfileOf, conv_convProfileOf]
      rfl)
  rw [cutLift, h, cutElem_sub]
  rfl

/-- The cut-off lift is a contraction for the C⋆-norms. -/
theorem norm_toEnvelope_cutLift_le (K : convKernels) :
    ‖toEnvelope coneKernels coneL1Norm (cutLift K)‖ ≤ ‖toEnvelope convKernels convL1Norm K‖ := by
  rw [← norm_coneSchrodinger, coneSchrodinger_toEnvelope, ← norm_convRegular,
    convRegular_toEnvelope, cutLift, cutElem_apply, op_cutConv]
  have hK : (K : BandKernel) = conv (convProfileOf K) := (conv_convProfileOf K).symm
  rw [hK]
  calc ‖coneCutMul * (conv (convProfileOf K)).op‖ ≤ ‖coneCutMul‖ * ‖(conv (convProfileOf K)).op‖ :=
        norm_mul_le _ _
    _ ≤ 1 * ‖(conv (convProfileOf K)).op‖ :=
        mul_le_mul_of_nonneg_right (norm_mulOp_le _ _) (norm_nonneg _)
    _ = _ := one_mul _

/-- **The symbol map is onto `C*(ℝ)`**: the cut-off lifts of a convergent core sequence form a
Cauchy sequence. -/
theorem coneSymbolMap_surjective : Function.Surjective coneSymbolMap := by
  intro z
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp ((toEnvelope_dense convKernels convL1Norm) z)
  choose K hK using hu
  set y : ℕ → ConeCrossedProduct := fun n => toEnvelope coneKernels coneL1Norm (cutLift (K n))
  have hdist : ∀ m n, dist (y m) (y n) ≤ dist (u m) (u n) := by
    intro m n
    rw [dist_eq_norm, dist_eq_norm, ← hK m, ← hK n, ← map_sub, ← map_sub, ← cutLift_sub]
    exact norm_toEnvelope_cutLift_le _
  have hcauchy : CauchySeq y := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
    exact ⟨N, fun m hm n hn => lt_of_le_of_lt (hdist m n) (hN m hm n hn)⟩
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨Y, tendsto_nhds_unique ((continuous_coneSymbolMap.tendsto Y).comp hY) ?_⟩
  have hsym : ∀ n, coneSymbolMap (y n) = u n := fun n => by
    change coneSymbolMap (toEnvelope coneKernels coneL1Norm (cutLift (K n))) = u n
    rw [coneSymbolMap_toEnvelope, coneSymbolHom_cutLift, hK n]
  exact (funext hsym ▸ hlim : Tendsto (fun n => coneSymbolMap (y n)) atTop (𝓝 z))

/-- **The Wiener–Hopf extension.**  Crossing the coefficient extension
`0 → C₀(ℝ) → C₀((-∞, +∞]) → ℂ → 0` by the translation action of `ℝ` gives the exact sequence of full
crossed products `0 → C₀(ℝ) ⋊ ℝ → C₀((-∞, +∞]) ⋊ ℝ → C*(ℝ) → 0`, with ideal `C₀(ℝ) ⋊ ℝ ≅ 𝒦(L²(ℝ))`
and quotient `C*(ℝ) ≅ C₀(ℝ̂)`. -/
theorem wienerHopf_extension_exact :
    Function.Injective coneIdealMap ∧
      (∀ y, coneSymbolMap (coneIdealMap y) = 0) ∧
      (∀ y, coneSymbolMap y = 0 → ∃ z, coneIdealMap z = y) ∧
      Function.Surjective coneSymbolMap :=
  ⟨coneIdealMap_injective, coneSymbolMap_coneIdealMap,
    fun _ hy => exists_coneIdealMap_of_coneSymbolMap_eq_zero hy, coneSymbolMap_surjective⟩

/-! ## The cut-off differs from the half-line projection by a local operator -/

theorem norm_tent_le (x : ℝ) : ‖(tentReal 2 x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tentReal_nonneg 2 x)]
  exact tentReal_le_one 2 x

theorem continuous_tent_complex : Continuous fun x : ℝ => (tentReal 2 x : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_tentReal 2)

/-- Multiplication by a bump equal to `1` on `[-1, 1]`. -/
def bumpMul : L2Real →L[ℂ] L2Real := mulOp continuous_tent_complex norm_tent_le

theorem coneCutMul_ae (f : L2Real) :
    (coneCutMul f : ℝ → ℂ) =ᵐ[volume] fun x => (coneCut x : ℂ) * f x :=
  mulOp_ae _ _ f

theorem bumpMul_ae (f : L2Real) :
    (bumpMul f : ℝ → ℂ) =ᵐ[volume] fun x => (tentReal 2 x : ℂ) * f x :=
  mulOp_ae _ _ f

/-- `M_χ - P₊` is multiplication by `χ - 1_{[0,∞)}`, supported in `[0, 1]`: it absorbs the bump. -/
theorem coneCutMul_sub_halfProj_mul_bumpMul :
    (coneCutMul - halfProj) * bumpMul = coneCutMul - halfProj := by
  ext1 f
  apply Lp.ext
  have h1 := Lp.coeFn_sub (coneCutMul (bumpMul f)) (halfProj (bumpMul f))
  have h2 := Lp.coeFn_sub (coneCutMul f) (halfProj f)
  filter_upwards [h1, h2, coneCutMul_ae (bumpMul f), halfProj_ae (bumpMul f), bumpMul_ae f,
    coneCutMul_ae f, halfProj_ae f] with x e1 e2 e3 e4 e5 e6 e7
  change ((coneCutMul - halfProj) (bumpMul f) : ℝ → ℂ) x = ((coneCutMul - halfProj) f : ℝ → ℂ) x
  rw [_root_.sub_apply, _root_.sub_apply, e1, e2, Pi.sub_apply,
    Pi.sub_apply]
  change (coneCutMul (bumpMul f) : ℝ → ℂ) x - (halfProj (bumpMul f) : ℝ → ℂ) x =
    (coneCutMul f : ℝ → ℂ) x - (halfProj f : ℝ → ℂ) x
  rw [e3, e4, e6, e7]
  by_cases hx : |x| ≤ 1
  · rw [e5, tentReal_eq_one (by linarith), Complex.ofReal_one, one_mul]
    by_cases h0 : x ∈ Ici (0 : ℝ)
    · rw [indicator_of_mem h0, indicator_of_mem h0, e5, tentReal_eq_one (by linarith),
        Complex.ofReal_one, one_mul]
    · rw [indicator_of_notMem h0, indicator_of_notMem h0]
  · push Not at hx
    rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; norm_num at hx) with hneg | hpos
    · have hx' : x < -1 := by rw [abs_of_neg hneg] at hx; linarith
      have h0 : x ∉ Ici (0 : ℝ) := by simp; linarith
      rw [indicator_of_notMem h0, indicator_of_notMem h0, coneCut_of_nonpos (by linarith)]
      simp
    · have hx' : 1 < x := by rwa [abs_of_pos hpos] at hx
      have h0 : x ∈ Ici (0 : ℝ) := by simp; linarith
      rw [indicator_of_mem h0, indicator_of_mem h0, coneCut_of_one_le hx'.le, e5]
      simp

/-- **`M_b C_W` is compact** for every circle symbol `W` vanishing at `1`. -/
theorem isCompactOperator_bumpMul_circleMultiplier {W : C(UnitCircle, ℂ)}
    (hW : W ∈ circleVanishing) : IsCompactOperator ⇑(bumpMul * circleMultiplier W) := by
  obtain ⟨z, hz⟩ := exists_convRegular_of_mem_circleVanishing hW
  rw [← hz]
  have hP : IsClosed {z : RealGroupCStar | IsCompactOperator ⇑(bumpMul * convRegular z)} :=
    (isClosed_setOf_isCompactOperator (𝕜₁ := ℂ) (M₁ := L2Real) (M₂ := L2Real)).preimage
      (continuous_const.mul continuous_convRegular)
  refine (toEnvelope_dense convKernels convL1Norm).induction_on z hP fun K => ?_
  obtain ⟨_, ⟨G, rfl⟩⟩ := K
  change IsCompactOperator ⇑(bumpMul * (conv G).op)
  rw [bumpMul, ← op_mulConv]
  have hrows : (mulConv continuous_tent_complex norm_tent_le G).RowsVanish 2 := fun x y hx => by
    rw [mulConv_toFun, tentReal_eq_zero hx.le, Complex.ofReal_zero, zero_mul]
  obtain ⟨k, hk⟩ := mem_range_ofKernelAlg_of_hasCompactSupport (hasCompactSupport_of_rowsVanish hrows)
  rw [← hk, op_ofKernelAlg, ← schrodinger_toEnvelope]
  exact isCompactOperator_schrodinger _

theorem isCompactOperator_cutDiff_circleMultiplier {W : C(UnitCircle, ℂ)}
    (hW : W ∈ circleVanishing) :
    IsCompactOperator ⇑((coneCutMul - halfProj) * circleMultiplier W) := by
  have h : (coneCutMul - halfProj) * circleMultiplier W =
      (coneCutMul - halfProj) * (bumpMul * circleMultiplier W) := by
    rw [← mul_assoc, coneCutMul_sub_halfProj_mul_bumpMul]
  rw [h]
  exact (isCompactOperator_bumpMul_circleMultiplier hW).clm_comp (coneCutMul - halfProj)

/-! ## The connecting map is the analytic Wiener–Hopf index -/

theorem halfProj_mul_one_sub : halfProj * (1 - halfProj) = 0 := by
  rw [mul_sub, mul_one, halfProj_mul_self, sub_self]

theorem one_sub_mul_halfProj : (1 - halfProj) * halfProj = 0 := by
  rw [sub_mul, one_mul, halfProj_mul_self, sub_self]

/-- The twist `P₊ + c (1 - P₊)` of the left half-line. -/
def halfTwist (c : ℂ) : L2Real →L[ℂ] L2Real := halfProj + c • (1 - halfProj)

theorem halfTwist_mul (c d : ℂ) : halfTwist c * halfTwist d = halfTwist (c * d) := by
  simp only [halfTwist, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    halfProj_mul_self, halfProj_mul_one_sub, one_sub_mul_halfProj, one_sub_halfProj_mul_self,
    smul_zero, add_zero, zero_add]
  rw [mul_comm d c]

theorem halfTwist_one : halfTwist 1 = 1 := by
  rw [halfTwist, one_smul, add_sub_cancel]

/-- For `c ≠ 0` the twist is invertible. -/
def halfTwistEquiv (c : ℂ) (hc : c ≠ 0) : L2Real ≃L[ℂ] L2Real :=
  ContinuousLinearEquiv.equivOfInverse (halfTwist c) (halfTwist c⁻¹)
    (fun f => by
      change (halfTwist c⁻¹ * halfTwist c) f = f
      rw [halfTwist_mul, inv_mul_cancel₀ hc, halfTwist_one]
      rfl)
    (fun f => by
      change (halfTwist c * halfTwist c⁻¹) f = f
      rw [halfTwist_mul, mul_inv_cancel₀ hc, halfTwist_one]
      rfl)

theorem halfTwist_mul_wienerHopfLift (c : ℂ) (u : C(UnitCircle, ℂ)) :
    halfTwist c * wienerHopfLift u =
      halfProj * circleMultiplier u * halfProj + c • (1 - halfProj) := by
  have h1 : halfProj * (halfProj * circleMultiplier u * halfProj) =
      halfProj * circleMultiplier u * halfProj := by
    rw [← mul_assoc, ← mul_assoc, halfProj_mul_self]
  have h2 : (1 - halfProj) * (halfProj * circleMultiplier u * halfProj) = 0 := by
    rw [← mul_assoc, ← mul_assoc, one_sub_mul_halfProj, zero_mul, zero_mul]
  simp only [halfTwist, wienerHopfLift, add_mul, mul_add, smul_mul_assoc, h1, h2,
    halfProj_mul_one_sub, one_sub_halfProj_mul_self, smul_zero, add_zero, zero_add]

/-- **The connecting map of the Wiener–Hopf extension is the analytic Wiener–Hopf index.**  Let
`u` be a unimodular symbol on the circle and `(c, y)` a lift of it to the unitization of
`C₀((-∞, +∞]) ⋊ ℝ`: `c + σ(y) = C_u` in `C*(ℝ)⁺`.  Then the Schrödinger image `c + ρ(y)` is Fredholm
and its index is the winding number of `u`.  (Modulo compact operators `c + ρ(y)` is the twisted
Toeplitz lift `(P₊ + c(1 - P₊)) T_u`: the remainders are `ρ(y) - M_χ C_{u-c}`, `(M_χ - P₊) C_{u-c}`
and the Hankel operator `P₊ C_{u-c} (1 - P₊)`.) -/
theorem wienerHopf_connecting_index {u : C(UnitCircle, ℂ)} (hu : star u * u = 1) {c : ℂ}
    {y : ConeCrossedProduct}
    (hlift : c • (1 : L2Real →L[ℂ] L2Real) + convRegular (coneSymbolMap y) = circleMultiplier u) :
    IsFredholmOp (c • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger y) ∧
      fredholmIndex (c • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger y) = circleWinding u := by
  obtain ⟨V, hV, hVz⟩ := exists_circle_of_convRegular (coneSymbolMap y)
  have huV : u = algebraMap ℂ C(UnitCircle, ℂ) c + V := by
    apply circleMultiplier_injective
    rw [circleMultiplier_add, hVz, ← hlift, Algebra.algebraMap_eq_smul_one, circleMultiplier_smul,
      circleMultiplier_one]
  have hc : u circleOne = c := by
    rw [huV, ContinuousMap.add_apply, show V circleOne = 0 from hV, add_zero]
    rfl
  have hcn : ‖c‖ = 1 := by
    rw [← hc]
    exact (star_mul_self_eq_one_iff u).mp hu circleOne
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hcn
  have hCu : circleMultiplier u = c • 1 + circleMultiplier V := by rw [← hlift, hVz]
  have hK1 := isCompactOperator_coneSchrodinger_sub y
  rw [← hVz] at hK1
  have hK2 := isCompactOperator_cutDiff_circleMultiplier hV
  have hK3 := (compactHankel V).1
  have hKc := hK1.add (hK2.add hK3)
  have hX : c • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger y =
      halfTwist c * wienerHopfLift u +
        ((coneSchrodinger y - coneCutMul * circleMultiplier V) +
          ((coneCutMul - halfProj) * circleMultiplier V + hankelPlus V)) := by
    rw [halfTwist_mul_wienerHopfLift, hCu, hankelPlus]
    have e1 : halfProj * (c • 1 + circleMultiplier V) * halfProj =
        c • halfProj + halfProj * circleMultiplier V * halfProj := by
      rw [mul_add, add_mul, mul_smul_comm, mul_one, smul_mul_assoc, halfProj_mul_self]
    rw [e1, sub_mul, mul_sub, mul_one, smul_sub]
    abel
  obtain ⟨hF, hI⟩ := fredholmIndex_wienerHopfLift_eq_circleWinding hu
  have hE : IsFredholmOp (halfTwist c * wienerHopfLift u) ∧
      fredholmIndex (halfTwist c * wienerHopfLift u) = fredholmIndex (wienerHopfLift u) :=
    hF.equiv_comp (halfTwistEquiv c hc0)
  rw [hX]
  exact ⟨hE.1.add_compact hKc, by rw [fredholmIndex_add_compact hE.1 hKc, hE.2, hI]⟩

/-- **Every symbol on the circle lifts** to the unitization of `C₀((-∞, +∞]) ⋊ ℝ`, with scalar part
its value at `1 = c(±∞)`. -/
theorem exists_wienerHopf_lift (u : C(UnitCircle, ℂ)) :
    ∃ y : ConeCrossedProduct, u circleOne • (1 : L2Real →L[ℂ] L2Real) +
      convRegular (coneSymbolMap y) = circleMultiplier u := by
  obtain ⟨z, hz⟩ := circleMultiplier_sub_mem_range u
  obtain ⟨y, rfl⟩ := coneSymbolMap_surjective z
  exact ⟨y, by rw [hz]; abel⟩

/-- **Capstone (SAC.14 and §4).**  For every unimodular symbol `u` on the circle there is a lift to
the unitized full crossed product `C₀((-∞, +∞]) ⋊ ℝ`, and every lift has Fredholm Schrödinger image of
index the winding number of `u`; on the generator `u = z` (the Cayley unitary) the index is `1`. -/
theorem wienerHopf_connecting_map {u : C(UnitCircle, ℂ)} (hu : star u * u = 1) :
    (∃ y : ConeCrossedProduct, u circleOne • (1 : L2Real →L[ℂ] L2Real) +
      convRegular (coneSymbolMap y) = circleMultiplier u) ∧
    ∀ (c : ℂ) (y : ConeCrossedProduct),
      c • (1 : L2Real →L[ℂ] L2Real) + convRegular (coneSymbolMap y) = circleMultiplier u →
        IsFredholmOp (c • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger y) ∧
          fredholmIndex (c • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger y) = circleWinding u :=
  ⟨exists_wienerHopf_lift u, fun _ _ h => wienerHopf_connecting_index hu h⟩

end GaloisForLFunctions.HTGeometry
