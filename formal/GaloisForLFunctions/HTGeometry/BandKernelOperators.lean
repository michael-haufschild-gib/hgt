import GaloisForLFunctions.HTGeometry.RealTranslationCrossedProduct
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier

/-!
# Band kernels on `ℝ × ℝ` and their integral operators

A kernel `K : ℝ × ℝ → ℂ` is a **band kernel** when it is continuous, bounded, and vanishes off a
band `|x - y| ≤ S` around the diagonal.  Rows and columns are then supported in intervals of length
`2S`, so

* the composition `(K L)(x, z) = ∫ K(x, y) L(y, z) dy` is again a band kernel (the integral runs
  over the compact window `|y - x| ≤ S`, parametric continuity), and the adjoint
  `K*(x, y) = conj K(y, x)` is a band kernel: a non-unital `*`-algebra (associativity is Fubini for
  the compactly supported integrand `K(x, y) L(y, w) M(w, z)`);
* `(T_K f)(x) = ∫ K(x, y) f(y) dy` is bounded on `L²(ℝ)` by Schur's test, with norm at most any
  common bound `A` of the row and column integrals (`norm_op_le_of_row_col`), and `K ↦ T_K` is a
  `*`-homomorphism (`opHom`; multiplicativity is Fubini on the band against `f ∈ L²_loc`).

The compactly supported kernels (`ofKernelAlgHom`, the kernel algebra of `C₀(ℝ) ⋊ ℝ`) and the
convolution kernels `G(x - y)`, whose operators are the Fourier multipliers of `𝓕 G` (`op_conv`), are
band kernels.  Band kernels are the common home of the coefficient-cone crossed product, its compact
ideal and its convolution quotient.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped CompactlySupported ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Band kernels -/

/-- A kernel on `ℝ × ℝ` that is continuous, bounded, and supported in a band `|x - y| ≤ S`. -/
structure IsBandKernel (K : ℝ × ℝ → ℂ) : Prop where
  continuous : Continuous K
  bounded : ∃ C, ∀ p, ‖K p‖ ≤ C
  band : ∃ S, ∀ x y, S < |x - y| → K (x, y) = 0

/-- The band kernels as a complex vector space of functions. -/
def bandKernels : Submodule ℂ (ℝ × ℝ → ℂ) where
  carrier := {K | IsBandKernel K}
  add_mem' {K L} hK hL := by
    obtain ⟨C, hC⟩ := hK.bounded
    obtain ⟨D, hD⟩ := hL.bounded
    obtain ⟨S, hS⟩ := hK.band
    obtain ⟨T, hT⟩ := hL.band
    refine ⟨hK.continuous.add hL.continuous, ⟨C + D, fun p => ?_⟩, ⟨max S T, fun x y h => ?_⟩⟩
    · exact (norm_add_le _ _).trans (add_le_add (hC p) (hD p))
    · change K (x, y) + L (x, y) = 0
      rw [hS x y (lt_of_le_of_lt (le_max_left _ _) h), hT x y (lt_of_le_of_lt (le_max_right _ _) h),
        add_zero]
  zero_mem' := ⟨continuous_const, ⟨0, fun _ => by simp⟩, ⟨0, fun _ _ _ => rfl⟩⟩
  smul_mem' c {K} hK := by
    obtain ⟨C, hC⟩ := hK.bounded
    obtain ⟨S, hS⟩ := hK.band
    refine ⟨continuous_const.mul hK.continuous, ⟨‖c‖ * C, fun p => ?_⟩, ⟨S, fun x y h => ?_⟩⟩
    · change ‖c * K p‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC p) (norm_nonneg c)
    · change c * K (x, y) = 0
      rw [hS x y h, mul_zero]

/-- **The band kernel algebra** (composition and adjoint below). -/
def BandKernel : Type := bandKernels

instance : AddCommGroup BandKernel := inferInstanceAs (AddCommGroup bandKernels)
instance : Module ℂ BandKernel := inferInstanceAs (Module ℂ bandKernels)

namespace BandKernel

/-- The kernel function. -/
def toFun (K : BandKernel) : ℝ × ℝ → ℂ := (show bandKernels from K).1

/-- A band kernel from a kernel function. -/
def mk (K : ℝ × ℝ → ℂ) (hK : IsBandKernel K) : BandKernel := show bandKernels from ⟨K, hK⟩

@[simp] theorem mk_toFun (K : ℝ × ℝ → ℂ) (hK : IsBandKernel K) : (mk K hK).toFun = K := rfl

theorem isBandKernel (K : BandKernel) : IsBandKernel K.toFun := (show bandKernels from K).2

theorem ext {K L : BandKernel} (h : ∀ p, K.toFun p = L.toFun p) : K = L :=
  Subtype.ext (funext h)

theorem add_apply (K L : BandKernel) (p : ℝ × ℝ) : (K + L).toFun p = K.toFun p + L.toFun p := rfl

theorem smul_apply (c : ℂ) (K : BandKernel) (p : ℝ × ℝ) : (c • K).toFun p = c * K.toFun p := rfl

theorem zero_apply (p : ℝ × ℝ) : (0 : BandKernel).toFun p = 0 := rfl

theorem neg_apply (K : BandKernel) (p : ℝ × ℝ) : (-K).toFun p = -K.toFun p := rfl

theorem sub_apply (K L : BandKernel) (p : ℝ × ℝ) : (K - L).toFun p = K.toFun p - L.toFun p := rfl

theorem continuous_toFun (K : BandKernel) : Continuous K.toFun := K.isBandKernel.continuous

/-- A width of the band. -/
def width (K : BandKernel) : ℝ := max (Classical.choose K.isBandKernel.band) 0

theorem width_nonneg (K : BandKernel) : 0 ≤ K.width := le_max_right _ _

theorem toFun_eq_zero (K : BandKernel) {x y : ℝ} (h : K.width < |x - y|) : K.toFun (x, y) = 0 :=
  Classical.choose_spec K.isBandKernel.band x y (lt_of_le_of_lt (le_max_left _ _) h)

/-- A bound of the kernel. -/
def sup (K : BandKernel) : ℝ := max (Classical.choose K.isBandKernel.bounded) 0

theorem sup_nonneg (K : BandKernel) : 0 ≤ K.sup := le_max_right _ _

theorem norm_toFun_le (K : BandKernel) (p : ℝ × ℝ) : ‖K.toFun p‖ ≤ K.sup :=
  (Classical.choose_spec K.isBandKernel.bounded p).trans (le_max_left _ _)

theorem toFun_eq_zero_of_notMem_row (K : BandKernel) {x y : ℝ}
    (h : y ∉ Icc (x - K.width) (x + K.width)) : K.toFun (x, y) = 0 := by
  refine K.toFun_eq_zero ?_
  have := K.width_nonneg
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_pos (by linarith)]
    linarith
  · rw [abs_of_neg (by linarith)]
    linarith

theorem toFun_eq_zero_of_notMem_col (K : BandKernel) {x y : ℝ}
    (h : x ∉ Icc (y - K.width) (y + K.width)) : K.toFun (x, y) = 0 := by
  refine K.toFun_eq_zero ?_
  have := K.width_nonneg
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

/-- A row against a continuous function is integrable. -/
theorem integrable_row_mul (K : BandKernel) (x : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable fun y => K.toFun (x, y) * g y := by
  refine Continuous.integrable_of_hasCompactSupport
    ((K.continuous_toFun.comp (continuous_const.prodMk continuous_id)).mul hg) ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := x - K.width) (b := x + K.width)) fun y hy => ?_
  rw [K.toFun_eq_zero_of_notMem_row hy, zero_mul]

/-- A column against a continuous function is integrable. -/
theorem integrable_mul_col (K : BandKernel) (z : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable fun y => g y * K.toFun (y, z) := by
  refine Continuous.integrable_of_hasCompactSupport
    (hg.mul (K.continuous_toFun.comp (continuous_id.prodMk continuous_const))) ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := z - K.width) (b := z + K.width)) fun y hy => ?_
  rw [K.toFun_eq_zero_of_notMem_col hy, mul_zero]

/-! ### Composition -/

/-- The composed kernel `∫ K(x, y) L(y, z) dy`. -/
def compFun (K L : BandKernel) (p : ℝ × ℝ) : ℂ := ∫ y, K.toFun (p.1, y) * L.toFun (y, p.2)

theorem compFun_eq_intervalIntegral (K L : BandKernel) (x z : ℝ) :
    compFun K L (x, z) = ∫ r in (-K.width)..K.width, K.toFun (x, x + r) * L.toFun (x + r, z) := by
  have hvan : ∀ y ∉ Icc (x - K.width) (x + K.width), K.toFun (x, y) * L.toFun (y, z) = 0 :=
    fun y hy => by rw [K.toFun_eq_zero_of_notMem_row hy, zero_mul]
  change ∫ y, K.toFun (x, y) * L.toFun (y, z) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [K.width_nonneg]),
    intervalIntegral.integral_comp_add_left (fun y => K.toFun (x, y) * L.toFun (y, z)) x]
  congr 1

theorem continuous_compFun (K L : BandKernel) : Continuous (compFun K L) := by
  have h : compFun K L = fun p : ℝ × ℝ =>
      ∫ r in (-K.width)..K.width, K.toFun (p.1, p.1 + r) * L.toFun (p.1 + r, p.2) :=
    funext fun p => compFun_eq_intervalIntegral K L p.1 p.2
  rw [h]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  exact (K.continuous_toFun.comp (continuous_fst.fst.prodMk (continuous_fst.fst.add continuous_snd))).mul
    (L.continuous_toFun.comp ((continuous_fst.fst.add continuous_snd).prodMk continuous_fst.snd))

theorem norm_compFun_le (K L : BandKernel) (p : ℝ × ℝ) :
    ‖compFun K L p‖ ≤ K.sup * L.sup * (2 * K.width) := by
  rw [compFun_eq_intervalIntegral]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K.sup * L.sup)
    fun r _ => ?_).trans (le_of_eq ?_)
  · rw [norm_mul]
    exact mul_le_mul (K.norm_toFun_le _) (L.norm_toFun_le _) (norm_nonneg _) K.sup_nonneg
  · rw [abs_of_nonneg (by linarith [K.width_nonneg])]
    ring

theorem compFun_eq_zero (K L : BandKernel) {x z : ℝ} (h : K.width + L.width < |x - z|) :
    compFun K L (x, z) = 0 := by
  rw [compFun]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  change K.toFun (x, y) * L.toFun (y, z) = 0
  by_cases hy : K.width < |x - y|
  · rw [K.toFun_eq_zero hy, zero_mul]
  · have : L.width < |y - z| := by
      have := abs_sub_le x y z
      push Not at hy
      linarith
    rw [L.toFun_eq_zero this, mul_zero]

theorem isBandKernel_compFun (K L : BandKernel) : IsBandKernel (compFun K L) :=
  ⟨continuous_compFun K L, ⟨_, norm_compFun_le K L⟩,
    ⟨K.width + L.width, fun _ _ h => compFun_eq_zero K L h⟩⟩

instance : Mul BandKernel := ⟨fun K L => mk (compFun K L) (isBandKernel_compFun K L)⟩

theorem mul_apply (K L : BandKernel) (x z : ℝ) :
    (K * L).toFun (x, z) = ∫ y, K.toFun (x, y) * L.toFun (y, z) := rfl

/-! ### Adjoint -/

theorem isBandKernel_adj (K : BandKernel) :
    IsBandKernel fun p : ℝ × ℝ => star (K.toFun (p.2, p.1)) := by
  refine ⟨continuous_star.comp (K.continuous_toFun.comp continuous_swap), ⟨K.sup, fun p => ?_⟩,
    ⟨K.width, fun x y h => ?_⟩⟩
  · rw [norm_star]
    exact K.norm_toFun_le _
  · change star (K.toFun (y, x)) = 0
    rw [K.toFun_eq_zero (by rwa [abs_sub_comm]), star_zero]

instance : Star BandKernel := ⟨fun K => mk _ K.isBandKernel_adj⟩

theorem star_apply (K : BandKernel) (x y : ℝ) : (star K).toFun (x, y) = star (K.toFun (y, x)) :=
  rfl

/-! ### The algebra laws -/

theorem integrable_triple (K L M : BandKernel) (x z : ℝ) :
    Integrable (Function.uncurry fun y w => K.toFun (x, y) * L.toFun (y, w) * M.toFun (w, z))
      (volume.prod volume) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact ((K.continuous_toFun.comp (continuous_const.prodMk continuous_fst)).mul
      L.continuous_toFun).mul (M.continuous_toFun.comp (continuous_snd.prodMk continuous_const))
  · refine HasCompactSupport.intro ((isCompact_Icc (a := x - K.width) (b := x + K.width)).prod
      (isCompact_Icc (a := z - M.width) (b := z + M.width))) fun q hq => ?_
    rw [Set.mem_prod, not_and_or] at hq
    change K.toFun (x, q.1) * L.toFun (q.1, q.2) * M.toFun (q.2, z) = 0
    rcases hq with h | h
    · rw [K.toFun_eq_zero_of_notMem_row h, zero_mul, zero_mul]
    · rw [M.toFun_eq_zero_of_notMem_col h, mul_zero]

theorem mul_assoc' (K L M : BandKernel) : K * L * M = K * (L * M) := by
  refine ext fun p => ?_
  obtain ⟨x, z⟩ := p
  rw [mul_apply, mul_apply]
  have h1 : ∀ w, (K * L).toFun (x, w) * M.toFun (w, z) =
      ∫ y, K.toFun (x, y) * L.toFun (y, w) * M.toFun (w, z) := fun w => by
    rw [mul_apply, ← integral_mul_const]
  have h2 : ∀ y, K.toFun (x, y) * (L * M).toFun (y, z) =
      ∫ w, K.toFun (x, y) * L.toFun (y, w) * M.toFun (w, z) := fun y => by
    rw [mul_apply, ← integral_const_mul]
    congr 1
    funext w
    ring
  simp_rw [h1, h2]
  exact (integral_integral_swap (integrable_triple K L M x z)).symm

theorem mul_add' (K L M : BandKernel) : K * (L + M) = K * L + K * M := by
  refine ext fun p => ?_
  obtain ⟨x, z⟩ := p
  rw [add_apply, mul_apply, mul_apply, mul_apply, ← integral_add]
  · congr 1
    funext y
    rw [add_apply, mul_add]
  · exact (K.integrable_row_mul x (L.continuous_toFun.comp (continuous_id.prodMk continuous_const)))
  · exact (K.integrable_row_mul x (M.continuous_toFun.comp (continuous_id.prodMk continuous_const)))

theorem add_mul' (K L M : BandKernel) : (K + L) * M = K * M + L * M := by
  refine ext fun p => ?_
  obtain ⟨x, z⟩ := p
  rw [add_apply, mul_apply, mul_apply, mul_apply, ← integral_add]
  · congr 1
    funext y
    rw [add_apply, add_mul]
  · exact (M.integrable_mul_col z (K.continuous_toFun.comp (continuous_const.prodMk continuous_id)))
  · exact (M.integrable_mul_col z (L.continuous_toFun.comp (continuous_const.prodMk continuous_id)))

theorem smul_mul' (c : ℂ) (K L : BandKernel) : (c • K) * L = c • (K * L) := by
  refine ext fun p => ?_
  obtain ⟨x, z⟩ := p
  rw [smul_apply, mul_apply, mul_apply, ← integral_const_mul]
  congr 1
  funext y
  rw [smul_apply]
  ring

theorem mul_smul' (c : ℂ) (K L : BandKernel) : K * (c • L) = c • (K * L) := by
  refine ext fun p => ?_
  obtain ⟨x, z⟩ := p
  rw [smul_apply, mul_apply, mul_apply, ← integral_const_mul]
  congr 1
  funext y
  rw [smul_apply]
  ring

theorem star_mul' (K L : BandKernel) : star (K * L) = star L * star K := by
  refine ext fun p => ?_
  obtain ⟨x, z⟩ := p
  rw [star_apply, mul_apply, mul_apply]
  change (starRingEnd ℂ) (∫ y, _) = _
  rw [← integral_conj]
  congr 1
  funext y
  rw [star_apply, star_apply, map_mul, mul_comm]
  rfl

end BandKernel

instance : NonUnitalRing BandKernel where
  left_distrib := BandKernel.mul_add'
  right_distrib := BandKernel.add_mul'
  zero_mul K := by
    have := BandKernel.smul_mul' 0 0 K
    simp only [zero_smul] at this
    exact this
  mul_zero K := by
    have := BandKernel.mul_smul' 0 K 0
    simp only [zero_smul] at this
    exact this
  mul_assoc := BandKernel.mul_assoc'

instance : StarRing BandKernel where
  star_involutive K := BandKernel.ext fun p => by
    obtain ⟨x, y⟩ := p
    rw [BandKernel.star_apply, BandKernel.star_apply, star_star]
  star_mul := BandKernel.star_mul'
  star_add K L := BandKernel.ext fun p => by
    obtain ⟨x, y⟩ := p
    rw [BandKernel.star_apply, BandKernel.add_apply, BandKernel.add_apply, star_add]
    rfl

instance : IsScalarTower ℂ BandKernel BandKernel := ⟨fun c K L => BandKernel.smul_mul' c K L⟩

instance : SMulCommClass ℂ BandKernel BandKernel := ⟨fun c K L => (BandKernel.mul_smul' c K L).symm⟩

instance : StarModule ℂ BandKernel := ⟨fun c K => BandKernel.ext fun p => by
  obtain ⟨x, y⟩ := p
  rw [BandKernel.star_apply, BandKernel.smul_apply, BandKernel.smul_apply, star_mul']
  rfl⟩

/-! ## The integral representation on `L²(ℝ)` -/

namespace SchurKernel

/-- Two Schur kernels with the same kernel function define the same operator. -/
theorem op_congr {k₁ k₂ : SchurKernel (volume : Measure ℝ)} (h : ∀ y z, k₁.toFun y z = k₂.toFun y z) :
    k₁.op = k₂.op := by
  ext1 f
  apply Lp.ext
  filter_upwards [k₁.op_coeFn f, k₂.op_coeFn f] with y h1 h2
  rw [h1, h2]
  simp only [SchurKernel.apply, h]

end SchurKernel

namespace BandKernel

theorem lintegral_row_le (K : BandKernel) (y : ℝ) :
    ∫⁻ z, ‖K.toFun (y, z)‖ₑ ≤ ENNReal.ofReal (2 * K.width * K.sup) := by
  calc ∫⁻ z, ‖K.toFun (y, z)‖ₑ
      ≤ ∫⁻ z, (Icc (y - K.width) (y + K.width)).indicator (fun _ => ENNReal.ofReal K.sup) z := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ Icc (y - K.width) (y + K.width)
        · rw [indicator_of_mem hz, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (K.norm_toFun_le _)
        · rw [K.toFun_eq_zero_of_notMem_row hz, enorm_zero]
          positivity
    _ = ENNReal.ofReal K.sup * volume (Icc (y - K.width) (y + K.width)) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (2 * K.width * K.sup) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul K.sup_nonneg]
        congr 1
        ring

theorem lintegral_col_le (K : BandKernel) (z : ℝ) :
    ∫⁻ y, ‖K.toFun (y, z)‖ₑ ≤ ENNReal.ofReal (2 * K.width * K.sup) := by
  calc ∫⁻ y, ‖K.toFun (y, z)‖ₑ
      ≤ ∫⁻ y, (Icc (z - K.width) (z + K.width)).indicator (fun _ => ENNReal.ofReal K.sup) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ Icc (z - K.width) (z + K.width)
        · rw [indicator_of_mem hy, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (K.norm_toFun_le _)
        · rw [K.toFun_eq_zero_of_notMem_col hy, enorm_zero]
          positivity
    _ = ENNReal.ofReal K.sup * volume (Icc (z - K.width) (z + K.width)) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (2 * K.width * K.sup) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul K.sup_nonneg]
        congr 1
        ring

/-- The Schur kernel of a band kernel. -/
def schur (K : BandKernel) : SchurKernel (volume : Measure ℝ) where
  toFun y z := K.toFun (y, z)
  measurable := K.continuous_toFun.measurable
  bound := Real.toNNReal (2 * K.width * K.sup)
  row y := K.lintegral_row_le y
  col z := K.lintegral_col_le z

/-- **The integral operator** `(T_K f)(x) = ∫ K(x, y) f(y) dy` of a band kernel. -/
def op (K : BandKernel) : L2Real →L[ℂ] L2Real := K.schur.op

theorem op_ae (K : BandKernel) (f : L2Real) :
    (K.op f : ℝ → ℂ) =ᵐ[volume] fun x => ∫ y, K.toFun (x, y) * f y :=
  K.schur.op_coeFn f

/-- **Schur's test.**  Row and column integrals at most `A` bound the operator norm by `A`. -/
theorem norm_op_le_of_row_col (K : BandKernel) (A : ℝ≥0)
    (hrow : ∀ y, ∫⁻ z, ‖K.toFun (y, z)‖ₑ ≤ A) (hcol : ∀ z, ∫⁻ y, ‖K.toFun (y, z)‖ₑ ≤ A) :
    ‖K.op‖ ≤ A := by
  let k : SchurKernel (volume : Measure ℝ) :=
    { toFun := fun y z => K.toFun (y, z)
      measurable := K.continuous_toFun.measurable
      bound := A
      row := hrow
      col := hcol }
  have h : K.op = k.op := SchurKernel.op_congr fun _ _ => rfl
  rw [h]
  exact k.norm_op_le

theorem op_add (K L : BandKernel) : (K + L).op = K.op + L.op := by
  rw [op, op, op, ← SchurKernel.add_op]
  exact SchurKernel.op_congr fun _ _ => rfl

theorem op_smul (c : ℂ) (K : BandKernel) : (c • K).op = c • K.op := by
  ext1 f
  apply Lp.ext
  filter_upwards [(c • K).op_ae f, K.op_ae f, Lp.coeFn_smul c (K.op f)] with x h1 h2 h3
  rw [_root_.smul_apply, h3, Pi.smul_apply, h1, h2, smul_eq_mul,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [smul_apply]
  ring

theorem op_zero : (0 : BandKernel).op = 0 := by
  have h := op_smul 0 0
  rwa [zero_smul, zero_smul] at h

theorem op_star (K : BandKernel) : (star K).op = ContinuousLinearMap.adjoint K.op := by
  rw [op, op, SchurKernel.adjoint_op]
  exact SchurKernel.op_congr fun _ _ => rfl

/-- The local integrability of an `L²` function on a compact interval. -/
theorem integrable_indicator_norm (f : L2Real) (a b : ℝ) :
    Integrable ((Icc a b).indicator fun z => ‖(f : ℝ → ℂ) z‖) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have h : Integrable (f : ℝ → ℂ) (volume.restrict (Icc a b)) :=
    ((Lp.memLp f).restrict (Icc a b)).integrable one_le_two
  exact (integrable_indicator_iff measurableSet_Icc).mpr h.norm

theorem integrable_comp_triple (K L : BandKernel) (x : ℝ) (f : L2Real) :
    Integrable (Function.uncurry fun y z => K.toFun (x, y) * L.toFun (y, z) * (f : ℝ → ℂ) z)
      (volume.prod volume) := by
  set I := Icc (x - K.width) (x + K.width)
  set J := Icc (x - K.width - L.width) (x + K.width + L.width)
  have hg : Integrable (I.indicator fun _ => K.sup * L.sup) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  have hh := integrable_indicator_norm f (x - K.width - L.width) (x + K.width + L.width)
  refine (hg.mul_prod hh).mono' ?_ (Eventually.of_forall fun q => ?_)
  · exact (((K.continuous_toFun.comp (continuous_const.prodMk continuous_fst)).mul
      L.continuous_toFun).aestronglyMeasurable).mul (Lp.aestronglyMeasurable f).comp_snd
  · obtain ⟨y, z⟩ := q
    simp only [Function.uncurry_apply_pair]
    by_cases hy : y ∈ I
    · by_cases hz : z ∈ J
      · rw [indicator_of_mem hy, indicator_of_mem hz, norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (K.norm_toFun_le _) (L.norm_toFun_le _) (norm_nonneg _)
          K.sup_nonneg) le_rfl (norm_nonneg _) (mul_nonneg K.sup_nonneg L.sup_nonneg)
      · have hL : L.toFun (y, z) = 0 := by
          refine L.toFun_eq_zero_of_notMem_row fun hz' => hz ?_
          rw [mem_Icc] at hy hz' ⊢
          constructor <;> linarith [hy.1, hy.2, hz'.1, hz'.2]
        rw [hL, mul_zero, zero_mul, norm_zero]
        exact mul_nonneg (by rw [indicator_of_mem hy]; exact mul_nonneg K.sup_nonneg L.sup_nonneg)
          (indicator_nonneg (fun _ _ => norm_nonneg _) _)
    · rw [K.toFun_eq_zero_of_notMem_row hy, zero_mul, zero_mul, norm_zero, indicator_of_notMem hy,
        zero_mul]

/-- **The integral representation is multiplicative** (Fubini on the band). -/
theorem op_mul (K L : BandKernel) : (K * L).op = K.op * L.op := by
  ext1 f
  apply Lp.ext
  filter_upwards [(K * L).op_ae f, K.op_ae (L.op f)] with x h1 h2
  rw [show (K.op * L.op) f = K.op (L.op f) from rfl, h1, h2]
  have h3 : ∫ y, K.toFun (x, y) * (L.op f : ℝ → ℂ) y =
      ∫ y, K.toFun (x, y) * ∫ z, L.toFun (y, z) * (f : ℝ → ℂ) z := by
    refine integral_congr_ae ?_
    filter_upwards [L.op_ae f] with y hy
    rw [hy]
  rw [h3]
  simp_rw [← integral_const_mul, ← mul_assoc]
  rw [integral_integral_swap (integrable_comp_triple K L x f)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  change (K * L).toFun (x, z) * (f : ℝ → ℂ) z = _
  rw [mul_apply, ← integral_mul_const]

end BandKernel

namespace BandKernel

/-- **The integral representation** of the band kernel algebra on `L²(ℝ)`. -/
def opHom : BandKernel →⋆ₙₐ[ℂ] (L2Real →L[ℂ] L2Real) where
  toFun := op
  map_smul' := op_smul
  map_zero' := op_zero
  map_add' := op_add
  map_mul' := op_mul
  map_star' := op_star

theorem opHom_apply (K : BandKernel) : opHom K = K.op := rfl

/-! ### Compactly supported kernels -/

theorem exists_band_of_hasCompactSupport {k : ℝ × ℝ → ℂ} (hk : HasCompactSupport k) :
    ∃ S, ∀ x y, S < |x - y| → k (x, y) = 0 := by
  obtain ⟨R, hR⟩ := hk.isCompact.isBounded.subset_closedBall 0
  refine ⟨2 * R, fun x y h => ?_⟩
  by_contra hne
  have hmem : (x, y) ∈ Metric.closedBall (0 : ℝ × ℝ) R := hR (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs] at hmem
  have := abs_sub x y
  linarith [hmem.1, hmem.2]

theorem isBandKernel_of_cc (k : C_c(ℝ × ℝ, ℂ)) : IsBandKernel k :=
  ⟨k.continuous, k.continuous.bounded_above_of_compact_support k.hasCompactSupport,
    exists_band_of_hasCompactSupport k.hasCompactSupport⟩

/-- A compactly supported kernel as a band kernel. -/
def ofKernelAlg (k : KernelAlg) : BandKernel := mk k.toFun (isBandKernel_of_cc k.toCc)

theorem ofKernelAlg_toFun (k : KernelAlg) : (ofKernelAlg k).toFun = k.toFun := rfl

/-- **The compact kernels form a `*`-subalgebra**: composition and adjoint agree. -/
def ofKernelAlgHom : KernelAlg →⋆ₙₐ[ℂ] BandKernel where
  toFun := ofKernelAlg
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

theorem ofKernelAlg_injective : Function.Injective ofKernelAlg := fun _ _ h =>
  KernelAlg.ext fun p => congrFun (congrArg toFun h) p

theorem op_ofKernelAlg (k : KernelAlg) : (ofKernelAlg k).op = k.op := by
  ext1 f
  apply Lp.ext
  filter_upwards [(ofKernelAlg k).op_ae f, k.op_ae f] with x h1 h2
  rw [h1, h2]
  rfl

/-! ### Convolution kernels -/

theorem isBandKernel_conv (G : C_c(ℝ, ℂ)) : IsBandKernel fun p : ℝ × ℝ => G (p.1 - p.2) := by
  obtain ⟨C, hC⟩ := G.continuous.bounded_above_of_compact_support G.hasCompactSupport
  obtain ⟨R, hR⟩ := G.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  refine ⟨G.continuous.comp (continuous_fst.sub continuous_snd), ⟨C, fun p => hC _⟩,
    ⟨R, fun x y h => ?_⟩⟩
  by_contra hne
  have hmem := hR (subset_tsupport _ hne)
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at hmem
  linarith

/-- The convolution kernel `G(x - y)` of a compactly supported profile. -/
def conv (G : C_c(ℝ, ℂ)) : BandKernel := mk _ (isBandKernel_conv G)

theorem conv_toFun (G : C_c(ℝ, ℂ)) (x y : ℝ) : (conv G).toFun (x, y) = G (x - y) := rfl

theorem integrable_cc (G : C_c(ℝ, ℂ)) : Integrable G :=
  G.continuous.integrable_of_hasCompactSupport G.hasCompactSupport

/-- **A convolution kernel acts as the Fourier multiplier of `𝓕 G`.** -/
theorem op_conv (G : C_c(ℝ, ℂ)) :
    (conv G).op = fourierMulCLM (continuous_fourier_of_integrable' (integrable_cc G)).measurable
        (integral_nonneg fun x => norm_nonneg (G x)) (norm_fourier_apply_le_integral_norm G) := by
  rw [← convolutionKernel_op_eq_fourierMulCLM G G.continuous.measurable (integrable_cc G), op]
  exact SchurKernel.op_congr fun _ _ => rfl

end BandKernel

end GaloisForLFunctions.HTGeometry
