import GaloisForLFunctions.HTGeometry.BandKernelOperators
import GaloisForLFunctions.HTGeometry.CStarEnvelope

/-!
# The cone crossed product `C₀((-∞, +∞]) ⋊ ℝ` and its ideal and symbol

Translation `(α_r f)(x) = f(x - r)` acts on `C₀((-∞, +∞])` (continuous functions on `ℝ` vanishing
at `-∞` with a limit at `+∞`), fixing the point `+∞` and acting freely on the open ideal `C₀(ℝ)`.
In the kernel picture `K(x, y) = F(x - y, x)` of the twisted convolution algebra, a dense core is
given by the **cone kernels**
`K(x, y) = χ(x) G(x - y) + k(x, y)`, `G ∈ C_c(ℝ)`, `k ∈ C_c(ℝ × ℝ)`, with `χ` a fixed cut-off equal
to `0` on `x ≤ 0` and `1` on `x ≥ 1`: the fibre `x ↦ K(x, x - s)` vanishes at `-∞` and equals `G(s)`
near `+∞`.

* `coneKernels` is a `*`-subalgebra of the band kernels: `χG₁ · χG₂ = χ(G₁ ⋆ G₂)` and
  `(χG)* = χG*` up to compactly supported kernels, and the compact kernels form a two-sided ideal
  (rows or columns of a product vanish where those of a compact factor do).
* `coneSymbolHom`: the coefficient at `+∞`, `K ↦ G`, is a `*`-homomorphism onto the convolution
  algebra `(C_c(ℝ), ⋆)` (realised as the translation-invariant kernels `convKernels`); the symbol is
  determined by the kernel (`cutConv_add_ofKernelAlg_inj`).
* `coneL1Norm` is the `L¹(ℝ, C₀((-∞, +∞]))` norm `∫ sup_x |K(x, x - s)| ds`; it dominates the
  operator norm of the Schrödinger representation (Schur's test in the twisted picture), restricts to
  the `L¹(ℝ, C₀(ℝ))` norm on the ideal, and dominates the `L¹` norm of the symbol.
* `ConeCrossedProduct` (the full crossed product, an enveloping C⋆-algebra), `RealGroupCStar` (the
  full group C⋆-algebra `C*(ℝ) = ℂ ⋊ ℝ`), the ideal map `C₀(ℝ) ⋊ ℝ → C₀((-∞, +∞]) ⋊ ℝ`, the symbol
  map `C₀((-∞, +∞]) ⋊ ℝ → C*(ℝ)` (functoriality of envelopes, `CStarEnvelope.map`), and the
  Schrödinger and regular representations on `L²(ℝ)`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped CompactlySupported ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace BandKernel

/-! ## Kernels with bounded rows or columns are compactly supported -/

/-- The rows of `K` vanish for `|x| > R`. -/
def RowsVanish (K : BandKernel) (R : ℝ) : Prop := ∀ x y, R < |x| → K.toFun (x, y) = 0

/-- The columns of `K` vanish for `|y| > R`. -/
def ColsVanish (K : BandKernel) (R : ℝ) : Prop := ∀ x y, R < |y| → K.toFun (x, y) = 0

theorem RowsVanish.mul {K : BandKernel} {R : ℝ} (hK : K.RowsVanish R) (L : BandKernel) :
    (K * L).RowsVanish R := fun x z hx => by
  rw [mul_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  change K.toFun (x, y) * L.toFun (y, z) = 0
  rw [hK x y hx, zero_mul]

theorem ColsVanish.mul {L : BandKernel} {R : ℝ} (hL : L.ColsVanish R) (K : BandKernel) :
    (K * L).ColsVanish R := fun x z hz => by
  rw [mul_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  change K.toFun (x, y) * L.toFun (y, z) = 0
  rw [hL y z hz, mul_zero]

theorem hasCompactSupport_of_rowsVanish {K : BandKernel} {R : ℝ} (hK : K.RowsVanish R) :
    HasCompactSupport K.toFun := by
  refine HasCompactSupport.intro ((isCompact_Icc (a := -R) (b := R)).prod
    (isCompact_Icc (a := -R - K.width) (b := R + K.width))) fun p hp => ?_
  obtain ⟨x, y⟩ := p
  by_cases hx : R < |x|
  · exact hK x y hx
  · refine K.toFun_eq_zero ?_
    by_contra hxy
    push Not at hx hxy
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    obtain ⟨hy1, hy2⟩ := abs_le.mp hxy
    exact hp ⟨⟨hx1, hx2⟩, ⟨by linarith, by linarith⟩⟩

theorem hasCompactSupport_of_colsVanish {K : BandKernel} {R : ℝ} (hK : K.ColsVanish R) :
    HasCompactSupport K.toFun := by
  refine HasCompactSupport.intro ((isCompact_Icc (a := -R - K.width) (b := R + K.width)).prod
    (isCompact_Icc (a := -R) (b := R))) fun p hp => ?_
  obtain ⟨x, y⟩ := p
  by_cases hy : R < |y|
  · exact hK x y hy
  · refine K.toFun_eq_zero ?_
    by_contra hxy
    push Not at hy hxy
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    obtain ⟨hx1, hx2⟩ := abs_le.mp hxy
    exact hp ⟨⟨by linarith, by linarith⟩, ⟨hy1, hy2⟩⟩

theorem mem_range_ofKernelAlg_of_hasCompactSupport {K : BandKernel}
    (hK : HasCompactSupport K.toFun) : K ∈ Set.range ofKernelAlg :=
  ⟨KernelAlg.ofCc ⟨⟨K.toFun, K.continuous_toFun⟩, hK⟩, rfl⟩

theorem exists_rowsVanish_ofKernelAlg (k : KernelAlg) : ∃ R, (ofKernelAlg k).RowsVanish R := by
  obtain ⟨R, hR⟩ := k.hasCompactSupport_toFun.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun x y hx => ?_⟩
  by_contra hne
  have hmem := hR (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs] at hmem
  linarith [hmem.1]

theorem exists_colsVanish_ofKernelAlg (k : KernelAlg) : ∃ R, (ofKernelAlg k).ColsVanish R := by
  obtain ⟨R, hR⟩ := k.hasCompactSupport_toFun.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun x y hy => ?_⟩
  by_contra hne
  have hmem := hR (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    at hmem
  linarith [hmem.2]

theorem ofKernelAlg_add (k₁ k₂ : KernelAlg) :
    ofKernelAlg (k₁ + k₂) = ofKernelAlg k₁ + ofKernelAlg k₂ := rfl

theorem ofKernelAlg_smul (c : ℂ) (k : KernelAlg) : ofKernelAlg (c • k) = c • ofKernelAlg k := rfl

theorem ofKernelAlg_mul (k₁ k₂ : KernelAlg) :
    ofKernelAlg (k₁ * k₂) = ofKernelAlg k₁ * ofKernelAlg k₂ := rfl

theorem ofKernelAlg_star (k : KernelAlg) : ofKernelAlg (star k) = star (ofKernelAlg k) := rfl

theorem ofKernelAlg_zero : ofKernelAlg 0 = 0 := rfl

/-- **The compact kernels are a two-sided ideal of the band kernels.** -/
theorem ofKernelAlg_mul_mem (k : KernelAlg) (K : BandKernel) :
    ofKernelAlg k * K ∈ Set.range ofKernelAlg := by
  obtain ⟨R, hR⟩ := exists_rowsVanish_ofKernelAlg k
  exact mem_range_ofKernelAlg_of_hasCompactSupport (hasCompactSupport_of_rowsVanish (hR.mul K))

theorem mul_ofKernelAlg_mem (K : BandKernel) (k : KernelAlg) :
    K * ofKernelAlg k ∈ Set.range ofKernelAlg := by
  obtain ⟨R, hR⟩ := exists_colsVanish_ofKernelAlg k
  exact mem_range_ofKernelAlg_of_hasCompactSupport (hasCompactSupport_of_colsVanish (hR.mul K))

theorem add_mem_range_ofKernelAlg {K L : BandKernel} (hK : K ∈ Set.range ofKernelAlg)
    (hL : L ∈ Set.range ofKernelAlg) : K + L ∈ Set.range ofKernelAlg := by
  obtain ⟨k, rfl⟩ := hK
  obtain ⟨l, rfl⟩ := hL
  exact ⟨k + l, ofKernelAlg_add k l⟩

/-! ## The convolution algebra -/

theorem conv_add (G₁ G₂ : C_c(ℝ, ℂ)) : conv (G₁ + G₂) = conv G₁ + conv G₂ := ext fun _ => rfl

theorem conv_smul (c : ℂ) (G : C_c(ℝ, ℂ)) : conv (c • G) = c • conv G := ext fun _ => rfl

theorem conv_zero : conv 0 = 0 := ext fun _ => rfl

theorem conv_injective : Function.Injective conv := fun G₁ G₂ h => by
  ext s
  have := congrFun (congrArg toFun h) (s, 0)
  simpa [conv_toFun] using this

/-- The convolution `(G₁ ⋆ G₂)(s) = ∫ G₁(s - y) G₂(y) dy` of compactly supported profiles. -/
def convProfile (G₁ G₂ : C_c(ℝ, ℂ)) : C_c(ℝ, ℂ) where
  toFun s := (conv G₁ * conv G₂).toFun (s, 0)
  continuous_toFun := (conv G₁ * conv G₂).continuous_toFun.comp (continuous_id.prodMk continuous_const)
  hasCompactSupport' := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(conv G₁ * conv G₂).width)
      (b := (conv G₁ * conv G₂).width)) fun s hs => (conv G₁ * conv G₂).toFun_eq_zero ?_
    rw [sub_zero]
    by_contra h
    push Not at h
    exact hs (abs_le.mp h)

theorem conv_mul_conv (G₁ G₂ : C_c(ℝ, ℂ)) : conv G₁ * conv G₂ = conv (convProfile G₁ G₂) := by
  refine ext fun p => ?_
  obtain ⟨x, z⟩ := p
  rw [conv_toFun]
  change (conv G₁ * conv G₂).toFun (x, z) = (conv G₁ * conv G₂).toFun (x - z, 0)
  rw [mul_apply, mul_apply, ← integral_add_right_eq_self _ z]
  congr 1
  funext y
  rw [conv_toFun, conv_toFun, conv_toFun, conv_toFun]
  congr 2 <;> ring

/-- The involution `G*(s) = conj G(-s)`. -/
def starProfile (G : C_c(ℝ, ℂ)) : C_c(ℝ, ℂ) where
  toFun s := star (G (-s))
  continuous_toFun := continuous_star.comp (G.continuous.comp continuous_neg)
  hasCompactSupport' :=
    (G.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (star_zero ℂ)

theorem star_conv (G : C_c(ℝ, ℂ)) : star (conv G) = conv (starProfile G) := by
  refine ext fun p => ?_
  obtain ⟨x, y⟩ := p
  rw [star_apply, conv_toFun, conv_toFun]
  change star (G (y - x)) = star (G (-(x - y)))
  rw [neg_sub]

/-- **The convolution algebra** `C_c(ℝ)` as the translation-invariant band kernels. -/
def convKernels : NonUnitalStarSubalgebra ℂ BandKernel where
  carrier := Set.range conv
  add_mem' := by
    rintro _ _ ⟨G₁, rfl⟩ ⟨G₂, rfl⟩
    exact ⟨G₁ + G₂, conv_add G₁ G₂⟩
  zero_mem' := ⟨0, conv_zero⟩
  mul_mem' := by
    rintro _ _ ⟨G₁, rfl⟩ ⟨G₂, rfl⟩
    exact ⟨convProfile G₁ G₂, (conv_mul_conv G₁ G₂).symm⟩
  smul_mem' := by
    rintro c _ ⟨G, rfl⟩
    exact ⟨c • G, conv_smul c G⟩
  star_mem' := by
    rintro _ ⟨G, rfl⟩
    exact ⟨starProfile G, (star_conv G).symm⟩

/-! ## The cut-off convolution kernels -/

/-- The cut-off `χ(x) = max 0 (min 1 x)`: `0` on `x ≤ 0`, `1` on `x ≥ 1`. -/
def coneCut (x : ℝ) : ℝ := max 0 (min 1 x)

theorem continuous_coneCut : Continuous coneCut :=
  continuous_const.max (continuous_const.min continuous_id)

theorem coneCut_nonneg (x : ℝ) : 0 ≤ coneCut x := le_max_left _ _

theorem coneCut_le_one (x : ℝ) : coneCut x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem coneCut_of_nonpos {x : ℝ} (hx : x ≤ 0) : coneCut x = 0 :=
  max_eq_left (min_le_of_right_le hx)

theorem coneCut_of_one_le {x : ℝ} (hx : 1 ≤ x) : coneCut x = 1 := by
  rw [coneCut, min_eq_left hx, max_eq_right zero_le_one]

theorem isBandKernel_cutConv (G : C_c(ℝ, ℂ)) :
    IsBandKernel fun p : ℝ × ℝ => (coneCut p.1 : ℂ) * G (p.1 - p.2) := by
  have h := (conv G).isBandKernel
  refine ⟨(Complex.continuous_ofReal.comp (continuous_coneCut.comp continuous_fst)).mul
    h.continuous, ⟨(conv G).sup, fun p => ?_⟩, ⟨(conv G).width, fun x y hxy => ?_⟩⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coneCut_nonneg _)]
    calc coneCut p.1 * ‖G (p.1 - p.2)‖ ≤ 1 * (conv G).sup :=
          mul_le_mul (coneCut_le_one _) ((conv G).norm_toFun_le p) (norm_nonneg _) zero_le_one
      _ = (conv G).sup := one_mul _
  · change (coneCut x : ℂ) * G (x - y) = 0
    rw [← conv_toFun, (conv G).toFun_eq_zero hxy, mul_zero]

/-- The cut-off convolution kernel `χ(x) G(x - y)`. -/
def cutConv (G : C_c(ℝ, ℂ)) : BandKernel := mk _ (isBandKernel_cutConv G)

theorem cutConv_toFun (G : C_c(ℝ, ℂ)) (x y : ℝ) :
    (cutConv G).toFun (x, y) = (coneCut x : ℂ) * G (x - y) := rfl

theorem cutConv_add (G₁ G₂ : C_c(ℝ, ℂ)) : cutConv (G₁ + G₂) = cutConv G₁ + cutConv G₂ :=
  ext fun p => by
    change (coneCut p.1 : ℂ) * (G₁ (p.1 - p.2) + G₂ (p.1 - p.2)) = _
    rw [mul_add]
    rfl

theorem cutConv_smul (c : ℂ) (G : C_c(ℝ, ℂ)) : cutConv (c • G) = c • cutConv G :=
  ext fun p => by
    change (coneCut p.1 : ℂ) * (c * G (p.1 - p.2)) = c * ((coneCut p.1 : ℂ) * G (p.1 - p.2))
    ring

theorem cutConv_zero : cutConv 0 = 0 := ext fun p => by
  change (coneCut p.1 : ℂ) * 0 = 0
  rw [mul_zero]

/-- **Products of cut-off kernels**: `χG₁ · χG₂ = χ(G₁ ⋆ G₂)` up to a compact kernel; the rows of
the difference vanish off `[0, 1 + S]`. -/
theorem cutConv_mul_cutConv_sub_mem (G₁ G₂ : C_c(ℝ, ℂ)) :
    cutConv G₁ * cutConv G₂ - cutConv (convProfile G₁ G₂) ∈ Set.range ofKernelAlg := by
  refine mem_range_ofKernelAlg_of_hasCompactSupport
    (hasCompactSupport_of_rowsVanish (R := 1 + (conv G₁).width) fun x z hx => ?_)
  rw [sub_apply]
  rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at hx; linarith [(conv G₁).width_nonneg])
    with hneg | hpos
  · have hc : coneCut x = 0 := coneCut_of_nonpos hneg.le
    rw [mul_apply, cutConv_toFun, hc]
    simp only [cutConv_toFun, hc, Complex.ofReal_zero, zero_mul, integral_zero, sub_zero]
  · have hx' : 1 + (conv G₁).width < x := by rwa [abs_of_pos hpos] at hx
    have hc : coneCut x = 1 := coneCut_of_one_le (by linarith [(conv G₁).width_nonneg])
    have h1 : (cutConv G₁ * cutConv G₂).toFun (x, z) = (conv G₁ * conv G₂).toFun (x, z) := by
      rw [mul_apply, mul_apply]
      congr 1
      funext y
      rw [cutConv_toFun, cutConv_toFun, hc, Complex.ofReal_one, one_mul, conv_toFun, conv_toFun]
      by_cases hy : (conv G₁).width < |x - y|
      · rw [← conv_toFun G₁, (conv G₁).toFun_eq_zero hy, zero_mul, zero_mul]
      · push Not at hy
        rw [coneCut_of_one_le (by linarith [(abs_le.mp hy).2]), Complex.ofReal_one, one_mul]
    rw [h1, conv_mul_conv, cutConv_toFun, hc, Complex.ofReal_one, one_mul, conv_toFun, sub_self]

/-- `(χG)* = χG*` up to a compact kernel. -/
theorem star_cutConv_sub_mem (G : C_c(ℝ, ℂ)) :
    star (cutConv G) - cutConv (starProfile G) ∈ Set.range ofKernelAlg := by
  refine mem_range_ofKernelAlg_of_hasCompactSupport
    (hasCompactSupport_of_rowsVanish (R := 1 + (conv G).width) fun x y hx => ?_)
  rw [sub_apply, star_apply, cutConv_toFun, cutConv_toFun]
  change star ((coneCut y : ℂ) * G (y - x)) - (coneCut x : ℂ) * star (G (-(x - y))) = 0
  rw [neg_sub, _root_.star_mul', Complex.star_def, Complex.conj_ofReal]
  by_cases hxy : (conv G).width < |y - x|
  · rw [← conv_toFun G, (conv G).toFun_eq_zero hxy]
    simp
  · push Not at hxy
    obtain ⟨h1, h2⟩ := abs_le.mp hxy
    have hw := (conv G).width_nonneg
    rcases lt_or_gt_of_ne (show x ≠ 0 by rintro rfl; simp at hx; linarith) with hneg | hpos
    · rw [abs_of_neg hneg] at hx
      rw [coneCut_of_nonpos (by linarith), coneCut_of_nonpos (by linarith)]
      ring
    · rw [abs_of_pos hpos] at hx
      rw [coneCut_of_one_le (by linarith), coneCut_of_one_le (by linarith)]
      ring

/-! ## The cone kernel algebra -/

/-- **The cone kernel algebra**: `χ(x) G(x - y) + k(x, y)` with `G ∈ C_c(ℝ)` and `k` compactly
supported.  In the twisted picture `F(s, x) = K(x, x - s)` these are the `C_c(ℝ, ·)` sections with
values in `C₀((-∞, +∞])` that are constant `G(s)` near `+∞`: the dense core of `C₀((-∞, +∞]) ⋊ ℝ`. -/
def coneKernels : NonUnitalStarSubalgebra ℂ BandKernel where
  carrier := {K | ∃ (G : C_c(ℝ, ℂ)) (k : KernelAlg), K = cutConv G + ofKernelAlg k}
  add_mem' := by
    rintro _ _ ⟨G₁, k₁, rfl⟩ ⟨G₂, k₂, rfl⟩
    refine ⟨G₁ + G₂, k₁ + k₂, ?_⟩
    rw [cutConv_add, ofKernelAlg_add k₁ k₂]
    abel
  zero_mem' := ⟨0, 0, by rw [cutConv_zero, ofKernelAlg_zero, add_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨G₁, k₁, rfl⟩ ⟨G₂, k₂, rfl⟩
    have hr : (cutConv G₁ + ofKernelAlg k₁) * (cutConv G₂ + ofKernelAlg k₂) -
        cutConv (convProfile G₁ G₂) ∈ Set.range ofKernelAlg := by
      have h : (cutConv G₁ + ofKernelAlg k₁) * (cutConv G₂ + ofKernelAlg k₂) -
          cutConv (convProfile G₁ G₂) =
          (cutConv G₁ * cutConv G₂ - cutConv (convProfile G₁ G₂)) +
            (cutConv G₁ * ofKernelAlg k₂ + (ofKernelAlg k₁ * cutConv G₂ +
              ofKernelAlg k₁ * ofKernelAlg k₂)) := by
        rw [add_mul, mul_add, mul_add]
        abel
      rw [h]
      exact add_mem_range_ofKernelAlg (cutConv_mul_cutConv_sub_mem G₁ G₂)
        (add_mem_range_ofKernelAlg (mul_ofKernelAlg_mem _ _)
          (add_mem_range_ofKernelAlg (ofKernelAlg_mul_mem _ _) (ofKernelAlg_mul_mem _ _)))
    obtain ⟨k, hk⟩ := hr
    exact ⟨convProfile G₁ G₂, k, by rw [hk]; abel⟩
  smul_mem' := by
    rintro c _ ⟨G, k, rfl⟩
    exact ⟨c • G, c • k, by rw [smul_add, cutConv_smul, ofKernelAlg_smul c k]⟩
  star_mem' := by
    rintro _ ⟨G, k, rfl⟩
    obtain ⟨l, hl⟩ := star_cutConv_sub_mem G
    refine ⟨starProfile G, l + star k, ?_⟩
    rw [star_add, ofKernelAlg_add l (star k), hl, ofKernelAlg_star k]
    change star (cutConv G) + star (ofKernelAlg k) =
      cutConv (starProfile G) + (star (cutConv G) - cutConv (starProfile G) + star (ofKernelAlg k))
    abel

end BandKernel

namespace BandKernel

/-! ## Decompositions and the symbol at `+∞` -/

theorem cone_add_decomp (G₁ G₂ : C_c(ℝ, ℂ)) (k₁ k₂ : KernelAlg) :
    (cutConv G₁ + ofKernelAlg k₁) + (cutConv G₂ + ofKernelAlg k₂) =
      cutConv (G₁ + G₂) + ofKernelAlg (k₁ + k₂) := by
  rw [cutConv_add, ofKernelAlg_add]
  abel

theorem cone_mul_decomp (G₁ G₂ : C_c(ℝ, ℂ)) (k₁ k₂ : KernelAlg) :
    ∃ k : KernelAlg, (cutConv G₁ + ofKernelAlg k₁) * (cutConv G₂ + ofKernelAlg k₂) =
      cutConv (convProfile G₁ G₂) + ofKernelAlg k := by
  have h : (cutConv G₁ + ofKernelAlg k₁) * (cutConv G₂ + ofKernelAlg k₂) -
      cutConv (convProfile G₁ G₂) =
      (cutConv G₁ * cutConv G₂ - cutConv (convProfile G₁ G₂)) +
        (cutConv G₁ * ofKernelAlg k₂ + (ofKernelAlg k₁ * cutConv G₂ +
          ofKernelAlg k₁ * ofKernelAlg k₂)) := by
    rw [add_mul, mul_add, mul_add]
    abel
  have hr : (cutConv G₁ + ofKernelAlg k₁) * (cutConv G₂ + ofKernelAlg k₂) -
      cutConv (convProfile G₁ G₂) ∈ Set.range ofKernelAlg := by
    rw [h]
    exact add_mem_range_ofKernelAlg (cutConv_mul_cutConv_sub_mem G₁ G₂)
      (add_mem_range_ofKernelAlg (mul_ofKernelAlg_mem _ _)
        (add_mem_range_ofKernelAlg (ofKernelAlg_mul_mem _ _) (ofKernelAlg_mul_mem _ _)))
  obtain ⟨k, hk⟩ := hr
  exact ⟨k, by rw [hk]; abel⟩

theorem cone_star_decomp (G : C_c(ℝ, ℂ)) (k : KernelAlg) :
    ∃ l : KernelAlg, star (cutConv G + ofKernelAlg k) = cutConv (starProfile G) + ofKernelAlg l := by
  obtain ⟨l, hl⟩ := star_cutConv_sub_mem G
  refine ⟨l + star k, ?_⟩
  rw [star_add, ofKernelAlg_add, hl, ofKernelAlg_star]
  abel

/-- **The symbol is determined by the kernel**: at `x → +∞` the kernel is `G(x - y)`. -/
theorem cutConv_add_ofKernelAlg_inj {G G' : C_c(ℝ, ℂ)} {k k' : KernelAlg}
    (h : cutConv G + ofKernelAlg k = cutConv G' + ofKernelAlg k') : G = G' ∧ k = k' := by
  obtain ⟨R, hR⟩ := exists_rowsVanish_ofKernelAlg k
  obtain ⟨R', hR'⟩ := exists_rowsVanish_ofKernelAlg k'
  have hG : G = G' := by
    ext s
    set x := |R| + |R'| + 2
    have hx : 0 < x := by positivity
    have hxR : R < |x| := by rw [abs_of_pos hx]; linarith [le_abs_self R, abs_nonneg R']
    have hxR' : R' < |x| := by rw [abs_of_pos hx]; linarith [le_abs_self R', abs_nonneg R]
    have h1 : coneCut x = 1 := coneCut_of_one_le (by linarith [abs_nonneg R, abs_nonneg R'])
    have := congrFun (congrArg toFun h) (x, x - s)
    rw [add_apply, add_apply, cutConv_toFun, cutConv_toFun, hR x _ hxR, hR' x _ hxR', h1,
      sub_sub_cancel] at this
    simpa using this
  subst hG
  exact ⟨rfl, ofKernelAlg_injective (add_left_cancel h)⟩

end BandKernel

open BandKernel

/-- The symbol `G` of a cone kernel `χ(x) G(x - y) + k(x, y)`. -/
def coneSymbol (K : coneKernels) : C_c(ℝ, ℂ) := Classical.choose K.2

/-- The compact remainder `k` of a cone kernel. -/
def coneRemainder (K : coneKernels) : KernelAlg := Classical.choose (Classical.choose_spec K.2)

theorem coneKernel_decomp (K : coneKernels) :
    (K : BandKernel) = cutConv (coneSymbol K) + ofKernelAlg (coneRemainder K) :=
  Classical.choose_spec (Classical.choose_spec K.2)

theorem coneSymbol_eq {K : coneKernels} {G : C_c(ℝ, ℂ)} {k : KernelAlg}
    (h : (K : BandKernel) = cutConv G + ofKernelAlg k) : coneSymbol K = G :=
  (cutConv_add_ofKernelAlg_inj ((coneKernel_decomp K).symm.trans h)).1

theorem coneSymbol_add (K L : coneKernels) :
    coneSymbol (K + L) = coneSymbol K + coneSymbol L := by
  refine coneSymbol_eq (k := coneRemainder K + coneRemainder L) ?_
  change (K : BandKernel) + L = _
  rw [coneKernel_decomp K, coneKernel_decomp L, cone_add_decomp]

theorem coneSymbol_smul (c : ℂ) (K : coneKernels) : coneSymbol (c • K) = c • coneSymbol K := by
  refine coneSymbol_eq (k := c • coneRemainder K) ?_
  change c • (K : BandKernel) = _
  rw [coneKernel_decomp K, smul_add, cutConv_smul, ofKernelAlg_smul]

theorem coneSymbol_mul (K L : coneKernels) :
    coneSymbol (K * L) = convProfile (coneSymbol K) (coneSymbol L) := by
  obtain ⟨k, hk⟩ := cone_mul_decomp (coneSymbol K) (coneSymbol L) (coneRemainder K)
    (coneRemainder L)
  refine coneSymbol_eq (k := k) ?_
  change (K : BandKernel) * L = _
  rw [coneKernel_decomp K, coneKernel_decomp L, hk]

theorem coneSymbol_star (K : coneKernels) : coneSymbol (star K) = starProfile (coneSymbol K) := by
  obtain ⟨l, hl⟩ := cone_star_decomp (coneSymbol K) (coneRemainder K)
  refine coneSymbol_eq (k := l) ?_
  change star (K : BandKernel) = _
  rw [coneKernel_decomp K, hl]

/-- **The symbol homomorphism** `C₀((-∞, +∞]) ⋊ ℝ → C*(ℝ)` on the cores: evaluation of the
coefficient at `+∞`. -/
def coneSymbolHom : coneKernels →⋆ₙₐ[ℂ] convKernels where
  toFun K := ⟨conv (coneSymbol K), ⟨_, rfl⟩⟩
  map_smul' c K := Subtype.ext (by
    change conv (coneSymbol (c • K)) = c • conv (coneSymbol K)
    rw [coneSymbol_smul, conv_smul])
  map_zero' := Subtype.ext (by
    change conv (coneSymbol 0) = 0
    rw [coneSymbol_eq (k := 0) (by rw [cutConv_zero, ofKernelAlg_zero, add_zero]; rfl), conv_zero])
  map_add' K L := Subtype.ext (by
    change conv (coneSymbol (K + L)) = conv (coneSymbol K) + conv (coneSymbol L)
    rw [coneSymbol_add, conv_add])
  map_mul' K L := Subtype.ext (by
    change conv (coneSymbol (K * L)) = conv (coneSymbol K) * conv (coneSymbol L)
    rw [coneSymbol_mul, conv_mul_conv])
  map_star' K := Subtype.ext (by
    change conv (coneSymbol (star K)) = star (conv (coneSymbol K))
    rw [coneSymbol_star, star_conv])

theorem coneSymbolHom_apply (K : coneKernels) :
    (coneSymbolHom K : BandKernel) = conv (coneSymbol K) := rfl

/-- **The compact ideal** `C₀(ℝ) ⋊ ℝ` of the cone core. -/
def coneIdealHom : KernelAlg →⋆ₙₐ[ℂ] coneKernels where
  toFun k := ⟨ofKernelAlg k, ⟨0, k, by rw [cutConv_zero, zero_add]⟩⟩
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

theorem coneIdealHom_apply (k : KernelAlg) : (coneIdealHom k : BandKernel) = ofKernelAlg k := rfl

theorem coneSymbol_coneIdealHom (k : KernelAlg) : coneSymbol (coneIdealHom k) = 0 :=
  coneSymbol_eq (k := k) (by rw [cutConv_zero, zero_add]; rfl)

/-- The cut-off convolution kernel `χ(x) G(x - y)` as a cone kernel. -/
def cutElem (G : C_c(ℝ, ℂ)) : coneKernels := ⟨cutConv G, ⟨G, 0, by rw [ofKernelAlg_zero, add_zero]⟩⟩

theorem cutElem_apply (G : C_c(ℝ, ℂ)) : (cutElem G : BandKernel) = cutConv G := rfl

theorem coneSymbol_cutElem (G : C_c(ℝ, ℂ)) : coneSymbol (cutElem G) = G :=
  coneSymbol_eq (k := 0) (by rw [ofKernelAlg_zero, add_zero]; rfl)

/-- Every cone kernel is `χG + k`. -/
theorem coneKernel_eq_cutElem_add (K : coneKernels) :
    K = cutElem (coneSymbol K) + coneIdealHom (coneRemainder K) :=
  Subtype.ext (coneKernel_decomp K)

/-! ## The `L¹(ℝ, C₀((-∞, +∞]))` norm -/

namespace BandKernel

/-- The fibre `x ↦ K(x, x - s)` at translation `s`: the coefficient of `K` in the twisted picture. -/
def fibre (K : BandKernel) (s : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => K.toFun (x, x - s))
    (K.continuous_toFun.comp (continuous_id.prodMk (continuous_id.sub continuous_const))) K.sup
    fun _ => K.norm_toFun_le _

theorem fibre_apply (K : BandKernel) (s x : ℝ) : K.fibre s x = K.toFun (x, x - s) := rfl

/-- The sup norm of the fibre. -/
def fibreSup (K : BandKernel) (s : ℝ) : ℝ := ‖K.fibre s‖

theorem norm_toFun_le_fibreSup (K : BandKernel) (s x : ℝ) : ‖K.toFun (x, x - s)‖ ≤ K.fibreSup s :=
  (K.fibre s).norm_coe_le_norm x

theorem fibreSup_nonneg (K : BandKernel) (s : ℝ) : 0 ≤ K.fibreSup s := norm_nonneg _

theorem fibre_add (K L : BandKernel) (s : ℝ) : (K + L).fibre s = K.fibre s + L.fibre s :=
  BoundedContinuousFunction.ext fun _ => rfl

theorem fibre_eq_zero (K : BandKernel) {s : ℝ} (hs : K.width < |s|) : K.fibre s = 0 :=
  BoundedContinuousFunction.ext fun x => by
    rw [fibre_apply, K.toFun_eq_zero (by rwa [sub_sub_cancel])]
    rfl

theorem continuous_fibre_of_uniformContinuous (K : BandKernel) (hK : UniformContinuous K.toFun) :
    Continuous K.fibre := by
  rw [Metric.continuous_iff]
  intro s ε hε
  obtain ⟨δ, hδ, hδK⟩ := Metric.uniformContinuous_iff.mp hK (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun s' hs' => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).mpr fun x => ?_)
    (half_lt_self hε)
  refine (hδK ?_).le
  rw [Prod.dist_eq, dist_self, Real.dist_eq, show x - s' - (x - s) = s - s' by ring, ← Real.dist_eq,
    dist_comm]
  exact max_lt hδ hs'

theorem continuous_fibre_ofKernelAlg (k : KernelAlg) : Continuous (ofKernelAlg k).fibre :=
  continuous_fibre_of_uniformContinuous (ofKernelAlg k)
    (k.hasCompactSupport_toFun.uniformContinuous_of_continuous k.continuous_toFun)

theorem continuous_fibre_cutConv (G : C_c(ℝ, ℂ)) : Continuous (cutConv G).fibre := by
  rw [Metric.continuous_iff]
  intro s ε hε
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuous_iff.mp G.continuous s (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun s' hs' => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).mpr fun x => ?_)
    (half_lt_self hε)
  rw [fibre_apply, fibre_apply, cutConv_toFun, cutConv_toFun, sub_sub_cancel, sub_sub_cancel,
    dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coneCut_nonneg x), ← dist_eq_norm]
  calc coneCut x * dist (G s') (G s) ≤ 1 * dist (G s') (G s) :=
        mul_le_mul_of_nonneg_right (coneCut_le_one x) dist_nonneg
    _ ≤ ε / 2 := by rw [one_mul]; exact (hδG s' hs').le

theorem continuous_fibreSup_cone (K : coneKernels) : Continuous (K : BandKernel).fibreSup := by
  have h : (K : BandKernel).fibre = fun s =>
      (cutConv (coneSymbol K)).fibre s + (ofKernelAlg (coneRemainder K)).fibre s := by
    funext s
    rw [coneKernel_decomp K, fibre_add]
  have hc : Continuous (K : BandKernel).fibre := by
    rw [h]
    exact (continuous_fibre_cutConv _).add (continuous_fibre_ofKernelAlg _)
  exact continuous_norm.comp hc

theorem hasCompactSupport_fibreSup (K : BandKernel) : HasCompactSupport K.fibreSup := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -K.width) (b := K.width)) fun s hs => ?_
  rw [fibreSup, K.fibre_eq_zero, norm_zero]
  by_contra h
  push Not at h
  exact hs (abs_le.mp h)

theorem integrable_fibreSup_cone (K : coneKernels) : Integrable (K : BandKernel).fibreSup :=
  (continuous_fibreSup_cone K).integrable_of_hasCompactSupport (hasCompactSupport_fibreSup _)

/-- **Schur's test in the twisted picture**: rows and columns are bounded by `∫ ‖K(·, · - s)‖_∞ ds`. -/
theorem norm_op_le_integral_fibreSup (K : BandKernel) (hK : Integrable K.fibreSup) :
    ‖K.op‖ ≤ ∫ s, K.fibreSup s := by
  have hN : 0 ≤ ∫ s, K.fibreSup s := integral_nonneg K.fibreSup_nonneg
  have hlin : ∫⁻ s, ENNReal.ofReal (K.fibreSup s) = ENNReal.ofReal (∫ s, K.fibreSup s) :=
    (ofReal_integral_eq_lintegral_ofReal hK (Eventually.of_forall K.fibreSup_nonneg)).symm
  have h := K.norm_op_le_of_row_col (Real.toNNReal (∫ s, K.fibreSup s)) (fun y => ?_) (fun z => ?_)
  · rwa [Real.coe_toNNReal _ hN] at h
  · rw [← lintegral_sub_left_eq_self (fun z => ‖K.toFun (y, z)‖ₑ) y]
    refine (lintegral_mono fun s => ?_).trans hlin.le
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (K.norm_toFun_le_fibreSup s y)
  · rw [← lintegral_add_right_eq_self (fun y => ‖K.toFun (y, z)‖ₑ) z]
    refine (lintegral_mono fun s => ?_).trans hlin.le
    rw [← ofReal_norm]
    have := K.norm_toFun_le_fibreSup s (s + z)
    rw [add_sub_cancel_left] at this
    exact ENNReal.ofReal_le_ofReal this

end BandKernel

/-- **The `L¹(ℝ, C₀((-∞, +∞]))` norm** `∫ sup_x |K(x, x - s)| ds` of a cone kernel. -/
def coneL1Norm (K : coneKernels) : ℝ := ∫ s, (K : BandKernel).fibreSup s

theorem coneL1Norm_nonneg (K : coneKernels) : 0 ≤ coneL1Norm K :=
  integral_nonneg (K : BandKernel).fibreSup_nonneg

theorem norm_op_le_coneL1Norm (K : coneKernels) : ‖(K : BandKernel).op‖ ≤ coneL1Norm K :=
  BandKernel.norm_op_le_integral_fibreSup _ (BandKernel.integrable_fibreSup_cone K)

theorem fibreSup_ofKernelAlg (k : KernelAlg) (s : ℝ) :
    (ofKernelAlg k).fibreSup s = k.fibreNorm s := by
  rw [BandKernel.fibreSup, KernelAlg.fibreNorm]
  congr 1

/-- On the compact ideal the cone norm is the `L¹(ℝ, C₀(ℝ))` norm. -/
theorem coneL1Norm_coneIdealHom (k : KernelAlg) : coneL1Norm (coneIdealHom k) = k.l1Norm := by
  rw [coneL1Norm, KernelAlg.l1Norm]
  exact integral_congr_ae (Eventually.of_forall fun s => fibreSup_ofKernelAlg k s)

theorem fibreSup_cutConv (G : C_c(ℝ, ℂ)) (s : ℝ) : (cutConv G).fibreSup s = ‖G s‖ := by
  refine le_antisymm ?_ ?_
  · refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr fun x => ?_
    rw [BandKernel.fibre_apply, cutConv_toFun, sub_sub_cancel, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (coneCut_nonneg x)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (coneCut_le_one x))
  · have := (cutConv G).norm_toFun_le_fibreSup s 1
    rwa [cutConv_toFun, sub_sub_cancel, coneCut_of_one_le le_rfl, Complex.ofReal_one, one_mul]
      at this

/-- The cut-off kernel `χ G` has cone norm `‖G‖₁`. -/
theorem coneL1Norm_cutElem (G : C_c(ℝ, ℂ)) : coneL1Norm (cutElem G) = ∫ s, ‖G s‖ := by
  rw [coneL1Norm]
  congr 1
  funext s
  exact fibreSup_cutConv G s

/-- **The `L¹(ℝ)` norm** `∫ |G|` of a convolution kernel. -/
def convL1Norm (K : convKernels) : ℝ := ∫ s, ‖(K : BandKernel).toFun (s, 0)‖

theorem convL1Norm_conv (G : C_c(ℝ, ℂ)) :
    convL1Norm ⟨conv G, ⟨G, rfl⟩⟩ = ∫ s, ‖G s‖ := by
  rw [convL1Norm]
  congr 1
  funext s
  rw [conv_toFun, sub_zero]

theorem convL1Norm_nonneg (K : convKernels) : 0 ≤ convL1Norm K :=
  integral_nonneg fun _ => norm_nonneg _

theorem norm_op_conv_le (G : C_c(ℝ, ℂ)) : ‖(conv G).op‖ ≤ ∫ s, ‖G s‖ := by
  rw [op_conv]
  exact norm_fourierMulCLM_le _ _ _

theorem norm_op_le_convL1Norm (K : convKernels) : ‖(K : BandKernel).op‖ ≤ convL1Norm K := by
  obtain ⟨_, ⟨G, rfl⟩⟩ := K
  rw [convL1Norm_conv]
  exact norm_op_conv_le G

/-- The symbol does not increase the `L¹` norm: `‖G‖₁ ≤ ‖K‖_{L¹(ℝ, C₀((-∞,+∞]))}`. -/
theorem convL1Norm_coneSymbolHom_le (K : coneKernels) :
    convL1Norm (coneSymbolHom K) ≤ coneL1Norm K := by
  change convL1Norm ⟨conv (coneSymbol K), ⟨_, rfl⟩⟩ ≤ _
  rw [convL1Norm_conv]
  refine integral_mono (integrable_cc (coneSymbol K)).norm (BandKernel.integrable_fibreSup_cone K)
    fun s => ?_
  obtain ⟨R, hR⟩ := BandKernel.exists_rowsVanish_ofKernelAlg (coneRemainder K)
  set x := |R| + 1
  have hx : R < |x| := by rw [abs_of_pos (by positivity)]; linarith [le_abs_self R]
  have hval : (K : BandKernel).toFun (x, x - s) = coneSymbol K s := by
    rw [coneKernel_decomp K, BandKernel.add_apply, cutConv_toFun, hR _ _ hx, add_zero,
      sub_sub_cancel, coneCut_of_one_le (by linarith [abs_nonneg R]), Complex.ofReal_one, one_mul]
  have h := (K : BandKernel).norm_toFun_le_fibreSup s x
  rwa [hval] at h

/-! ## Functoriality of enveloping C⋆-algebras -/

section EnvelopeMap

universe u

variable {B B' : Type u} [NonUnitalRing B] [StarRing B] [Module ℂ B]
  [NonUnitalRing B'] [StarRing B'] [Module ℂ B'] {N : B → ℝ} {N' : B' → ℝ}

/-- The pull-back of a bounded representation along a norm-decreasing `*`-homomorphism. -/
def BoundedRep.pullback (ρ : BoundedRep B' N') (φ : B →⋆ₙₐ[ℂ] B') (hφ : ∀ b, N' (φ b) ≤ N b) :
    BoundedRep B N where
  H := ρ.H
  π := ρ.π.comp φ
  bound b := (ρ.bound (φ b)).trans (hφ b)

variable (φ : B →⋆ₙₐ[ℂ] B') (hφ : ∀ b, N' (φ b) ≤ N b)

/-- The induced map of bounded families, `(y_ρ)_ρ ↦ (y_{ρ' ∘ φ})_{ρ'}`. -/
def envFamilyMap : EnvFamily B N →⋆ₙₐ[ℂ] EnvFamily B' N' where
  toFun y := EnvFamily.ofBounded (fun ρ => y.apply (ρ.pullback φ hφ)) ‖y‖
    fun _ => y.norm_apply_le _
  map_smul' _ _ := EnvFamily.ext fun _ => rfl
  map_zero' := EnvFamily.ext fun _ => rfl
  map_add' _ _ := EnvFamily.ext fun _ => rfl
  map_mul' _ _ := EnvFamily.ext fun _ => rfl
  map_star' _ := EnvFamily.ext fun _ => rfl

theorem norm_envFamilyMap_le (y : EnvFamily B N) : ‖envFamilyMap φ hφ y‖ ≤ ‖y‖ :=
  EnvFamily.norm_le_of_forall_le (norm_nonneg y) fun ρ => y.norm_apply_le (ρ.pullback φ hφ)

theorem continuous_envFamilyMap : Continuous (envFamilyMap φ hφ) :=
  AddMonoidHomClass.continuous_of_bound (envFamilyMap φ hφ) 1 fun y => by
    rw [one_mul]
    exact norm_envFamilyMap_le φ hφ y

theorem envFamilyMap_envUniversal (b : B) :
    envFamilyMap φ hφ (envUniversal B N b) = envUniversal B' N' (φ b) :=
  EnvFamily.ext fun _ => rfl

theorem envFamilyMap_mem {y : EnvFamily B N} (hy : y ∈ envSub B N) :
    envFamilyMap φ hφ y ∈ envSub B' N' := by
  rw [mem_envSub_iff] at hy ⊢
  refine map_mem_closure (continuous_envFamilyMap φ hφ) hy ?_
  rintro _ ⟨b, rfl⟩
  exact ⟨φ b, (envFamilyMap_envUniversal φ hφ b).symm⟩

/-- **Functoriality**: a norm-decreasing `*`-homomorphism of cores induces a `*`-homomorphism of
enveloping C⋆-algebras. -/
def CStarEnvelope.map : CStarEnvelope B N →⋆ₙₐ[ℂ] CStarEnvelope B' N' where
  toFun y := CStarEnvelope.mk (envFamilyMap φ hφ y.val) (envFamilyMap_mem φ hφ y.val_mem)
  map_smul' c y := CStarEnvelope.ext (map_smul (envFamilyMap φ hφ) c y.val)
  map_zero' := CStarEnvelope.ext (map_zero (envFamilyMap φ hφ))
  map_add' y z := CStarEnvelope.ext (map_add (envFamilyMap φ hφ) y.val z.val)
  map_mul' y z := CStarEnvelope.ext (map_mul (envFamilyMap φ hφ) y.val z.val)
  map_star' y := CStarEnvelope.ext (map_star (envFamilyMap φ hφ) y.val)

theorem CStarEnvelope.map_toEnvelope (b : B) :
    CStarEnvelope.map φ hφ (toEnvelope B N b) = toEnvelope B' N' (φ b) :=
  CStarEnvelope.ext (envFamilyMap_envUniversal φ hφ b)

theorem BoundedRep.extend_map (ρ : BoundedRep B' N') (y : CStarEnvelope B N) :
    ρ.extend (CStarEnvelope.map φ hφ y) = (ρ.pullback φ hφ).extend y := rfl

end EnvelopeMap

/-! ## The crossed products and their Schrödinger representations -/

/-- **The full crossed product** `C₀((-∞, +∞]) ⋊ ℝ`: the enveloping C⋆-algebra of the cone core for
its `L¹(ℝ, C₀((-∞, +∞]))` norm. -/
abbrev ConeCrossedProduct : Type 1 := CStarEnvelope coneKernels coneL1Norm

/-- **The full group C⋆-algebra** `C*(ℝ) = ℂ ⋊ ℝ`: the enveloping C⋆-algebra of `(C_c(ℝ), ⋆)` for
the `L¹` norm. -/
abbrev RealGroupCStar : Type 1 := CStarEnvelope convKernels convL1Norm

/-- The Schrödinger representation of the cone core on `L²(ℝ)`. -/
def coneSchrodingerRep : BoundedRep coneKernels coneL1Norm where
  H := L2Real
  π := BandKernel.opHom.comp (NonUnitalStarSubalgebraClass.subtype coneKernels)
  bound K := norm_op_le_coneL1Norm K

/-- **The Schrödinger representation** of `C₀((-∞, +∞]) ⋊ ℝ` on `L²(ℝ)`. -/
def coneSchrodinger : ConeCrossedProduct →⋆ₙₐ[ℂ] (L2Real →L[ℂ] L2Real) := coneSchrodingerRep.extend

theorem coneSchrodinger_toEnvelope (K : coneKernels) :
    coneSchrodinger (toEnvelope coneKernels coneL1Norm K) = (K : BandKernel).op := rfl

/-- The regular representation of the convolution core on `L²(ℝ)`. -/
def convRegularRep : BoundedRep convKernels convL1Norm where
  H := L2Real
  π := BandKernel.opHom.comp (NonUnitalStarSubalgebraClass.subtype convKernels)
  bound K := norm_op_le_convL1Norm K

/-- **The regular representation** of `C*(ℝ)` on `L²(ℝ)`: convolution operators. -/
def convRegular : RealGroupCStar →⋆ₙₐ[ℂ] (L2Real →L[ℂ] L2Real) := convRegularRep.extend

theorem convRegular_toEnvelope (K : convKernels) :
    convRegular (toEnvelope convKernels convL1Norm K) = (K : BandKernel).op := rfl

/-- **The ideal** `C₀(ℝ) ⋊ ℝ → C₀((-∞, +∞]) ⋊ ℝ`. -/
def coneIdealMap : RealCrossedProduct →⋆ₙₐ[ℂ] ConeCrossedProduct :=
  CStarEnvelope.map coneIdealHom fun k => (coneL1Norm_coneIdealHom k).le

/-- **The symbol** `C₀((-∞, +∞]) ⋊ ℝ → C*(ℝ)`, evaluation of coefficients at `+∞`. -/
def coneSymbolMap : ConeCrossedProduct →⋆ₙₐ[ℂ] RealGroupCStar :=
  CStarEnvelope.map coneSymbolHom convL1Norm_coneSymbolHom_le

theorem coneIdealMap_toRCP (k : KernelAlg) :
    coneIdealMap (toRCP k) = toEnvelope coneKernels coneL1Norm (coneIdealHom k) :=
  CStarEnvelope.map_toEnvelope _ _ k

theorem coneSymbolMap_toEnvelope (K : coneKernels) :
    coneSymbolMap (toEnvelope coneKernels coneL1Norm K) =
      toEnvelope convKernels convL1Norm (coneSymbolHom K) :=
  CStarEnvelope.map_toEnvelope _ _ K

/-- The Schrödinger representation restricts on the ideal to the Schrödinger representation of
`C₀(ℝ) ⋊ ℝ`. -/
theorem continuous_coneSchrodinger : Continuous coneSchrodinger :=
  (NonUnitalStarAlgHom.instContinuousLinearMapClassComplex (F := ConeCrossedProduct →⋆ₙₐ[ℂ]
    (L2Real →L[ℂ] L2Real))).map_continuous coneSchrodinger

theorem continuous_coneIdealMap : Continuous coneIdealMap :=
  (NonUnitalStarAlgHom.instContinuousLinearMapClassComplex (F := RealCrossedProduct →⋆ₙₐ[ℂ]
    ConeCrossedProduct)).map_continuous coneIdealMap

theorem continuous_coneSymbolMap : Continuous coneSymbolMap :=
  (NonUnitalStarAlgHom.instContinuousLinearMapClassComplex (F := ConeCrossedProduct →⋆ₙₐ[ℂ]
    RealGroupCStar)).map_continuous coneSymbolMap

theorem continuous_convRegular : Continuous convRegular :=
  (NonUnitalStarAlgHom.instContinuousLinearMapClassComplex (F := RealGroupCStar →⋆ₙₐ[ℂ]
    (L2Real →L[ℂ] L2Real))).map_continuous convRegular

theorem coneSchrodinger_coneIdealMap (y : RealCrossedProduct) :
    coneSchrodinger (coneIdealMap y) = schrodinger y := by
  have h := (toEnvelope_dense KernelAlg KernelAlg.l1Norm).equalizer
    (continuous_coneSchrodinger.comp continuous_coneIdealMap) continuous_schrodinger
    (funext fun k => by
      change coneSchrodinger (coneIdealMap (toRCP k)) = schrodinger (toRCP k)
      rw [coneIdealMap_toRCP, coneSchrodinger_toEnvelope, coneIdealHom_apply,
        BandKernel.op_ofKernelAlg, schrodinger_toEnvelope])
  exact congrFun h y

end GaloisForLFunctions.HTGeometry
