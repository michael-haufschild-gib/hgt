import GaloisForLFunctions.RHTower.ChiCubicNearConeReduction
import GaloisForLFunctions.RHTower.WindowTransformSamplingParseval

/-!
# Exact integer-height energy of the entire retained cone tube

The literal cone cutoff puts every normal slice inside an interval of length
one once its width is at most one quarter. Sampling Parseval therefore gives
an exact isometry on every shifted integer-height grid. Both contraction
translations preserve the identity through their exact mixed normal shift.
The complete logarithmically normalized critical height weights are bounded
by one, so their entire weighted square trace is controlled by the same energy.

The original shrinking width enters this range on the full natural scale.
No normal derivative budget is needed. These are normal-slice statements;
cancellation of the full signed tangential arithmetic action remains separate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology
namespace RHTower.BAGTrace

/-- Widths for which the normal support fits one sampling period. -/
abbrev BAGCubicTraceWidth := {ε : ℝ // ε ∈ Ioc (0 : ℝ) (1/4)}

/-- Entire retained Fourier test in exact signed normal coordinates. -/
def bagCubicNearNormalSlice (ε : ℝ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (x y D : ℝ) : ℂ :=
  (𝓕 (bagCubicNearConePhysical ε f)) (WithLp.toLp 2 ![x,y,D-x*y])

theorem bagCubicNearNormalSlice_continuous (ε : ℝ)
    (f : SchwartzMap BAGPhysicalSpace ℂ) (x y : ℝ) :
    Continuous (bagCubicNearNormalSlice ε f x y) := by
  unfold bagCubicNearNormalSlice
  have hc : Continuous (fun D : ℝ =>
      (WithLp.toLp 2 ![x,y,D-x*y] : BAGPhysicalSpace)) := by fun_prop
  exact (𝓕 (bagCubicNearConePhysical ε f)).continuous.comp hc

theorem bagCubicNearNormalSlice_off (ε : BAGCubicTraceWidth)
    (f : SchwartzMap BAGPhysicalSpace ℂ) (x y D : ℝ) (hD : 1/2 ≤ |D|) :
    bagCubicNearNormalSlice ε.1 f x y D = 0 := by
  rw [bagCubicNearNormalSlice,bagCubicNearConePhysical_fourier]
  have he : bagCubicSignedDefect (WithLp.toLp 2 ![x,y,D-x*y]) = D := by
    change D-x*y+x*y=D
    ring
  rw [he]
  have hb : bagCubicConeCutoff (D/ε.1)=0 := by
    apply bagCubicConeCutoff.zero_of_le_dist
    change 2 ≤ dist (D/ε.1) 0
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos ε.2.1]
    apply (le_div_iff₀ ε.2.1).mpr
    linarith [ε.2.2]
  rw [hb,zero_smul]

/-- Every integer height is retained, with an arbitrary real grid shift. -/
theorem bagCubicNearNormalSlice_height_isometry (ε : BAGCubicTraceWidth)
    (f : SchwartzMap BAGPhysicalSpace ℂ) (x y τ : ℝ) :
    HasSum (fun r : ℤ => ‖(𝓕 (bagCubicNearNormalSlice ε.1 f x y)) (τ+r)‖^2)
      (∫ D : ℝ, ‖bagCubicNearNormalSlice ε.1 f x y D‖^2) := by
  let ψ := bagCubicNearNormalSlice ε.1 f x y
  have hs : ∀ D : ℝ, (1 : ℝ)/2 ≤ |D| → ψ D=0 :=
    bagCubicNearNormalSlice_off ε f x y
  have hp := RHTower.hasSum_norm_sq_paperFT_grid (L:=1) zero_lt_one
    (bagCubicNearNormalSlice_continuous ε.1 f x y) hs (-2*Real.pi*τ) 0
  have hi : (∫ D in (-(1/2 : ℝ))..(1/2), ‖ψ D‖^2) = ∫ D : ℝ, ‖ψ D‖^2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro D hD
    have hb : (1 : ℝ)/2 ≤ |D| := by
      rw [mem_Ioc,not_and_or,not_lt,not_le] at hD
      rcases hD with hl | hr
      · exact le_trans (by linarith : (1 : ℝ)/2 ≤ -D) (neg_le_abs D)
      · exact le_trans (by linarith : (1 : ℝ)/2 ≤ D) (le_abs_self D)
    rw [hs D hb,norm_zero,zero_pow (by decide)]
  simp only [div_one,zero_add,one_mul] at hp
  rw [hi] at hp
  refine hp.congr_fun (fun r => ?_)
  rw [Zeta23.fourier_eq_paperFT]
  congr 3
  push_cast
  ring

private theorem fourier_translate_norm (ψ : ℝ → ℂ) (c r : ℝ) :
    ‖(𝓕 (fun D : ℝ => ψ (D+c))) r‖ = ‖(𝓕 ψ) r‖ := by
  change ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (ψ ∘ (fun D : ℝ => D+c)) r‖ = _
  rw [VectorFourier.fourierIntegral_comp_add_right]
  exact Circle.norm_smul _ _

/-- Both literal contraction translations, including their intersection. -/
def bagCubicNearTranslatedNormalSlice (ε : ℝ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (x y u v D : ℝ) : ℂ :=
  (𝓕 (bagCubicNearConePhysical ε f)) (WithLp.toLp 2 ![x+u,y+v,D-x*y-u-v])

/-- The mixed translation contributes the exact `u*v` normal shift. -/
theorem bagCubicNearTranslatedNormalSlice_eq (ε : ℝ)
    (f : SchwartzMap BAGPhysicalSpace ℂ) (x y u v D : ℝ) :
    bagCubicNearTranslatedNormalSlice ε f x y u v D =
      bagCubicNearNormalSlice ε f (x+u) (y+v) (D+u*(y-1)+v*(x-1)+u*v) := by
  unfold bagCubicNearTranslatedNormalSlice bagCubicNearNormalSlice
  congr 1
  have he : D-x*y-u-v = D+u*(y-1)+v*(x-1)+u*v-(x+u)*(y+v) := by ring
  rw [he]

/-- Each term of both contraction averages has the same exact height isometry. -/
theorem bagCubicNearTranslatedNormalSlice_height_isometry (ε : BAGCubicTraceWidth)
    (f : SchwartzMap BAGPhysicalSpace ℂ) (x y u v τ : ℝ) :
    HasSum (fun r : ℤ =>
      ‖(𝓕 (bagCubicNearTranslatedNormalSlice ε.1 f x y u v)) (τ+r)‖^2)
      (∫ D : ℝ, ‖bagCubicNearNormalSlice ε.1 f (x+u) (y+v) D‖^2) := by
  have he : bagCubicNearTranslatedNormalSlice ε.1 f x y u v =
      fun D : ℝ => bagCubicNearNormalSlice ε.1 f (x+u) (y+v)
        (D+(u*(y-1)+v*(x-1)+u*v)) := by
    funext D
    rw [bagCubicNearTranslatedNormalSlice_eq]
    congr 1
    ring
  rw [he]
  have hs := bagCubicNearNormalSlice_height_isometry ε f (x+u) (y+v) τ
  simpa only [fourier_translate_norm] using hs

/-- Complete critical height multiplier divided by its logarithmic envelope. -/
def bagCriticalHeightWeight (P : Finset ℕ) (r : ℤ) : ℝ :=
  ramanujanDistinguishedPrimeMultiplier P r.natAbs / Real.log ((r.natAbs : ℝ)+1)

theorem bagCriticalHeightWeight_bounds (P : Finset ℕ) (r : ℤ) :
    0 ≤ bagCriticalHeightWeight P r ∧ bagCriticalHeightWeight P r ≤ 1 := by
  obtain ⟨h0,hb⟩ := ramanujanDistinguishedPrimeMultiplier_uniform_bound P r.natAbs
  have hl : 0 ≤ Real.log ((r.natAbs : ℝ)+1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg r.natAbs : (0 : ℝ)≤r.natAbs)])
  refine ⟨div_nonneg h0 hl,?_⟩
  change _ / _ ≤ 1
  rcases hl.eq_or_lt with hz | hp
  · rw [← hz,div_zero]
    exact zero_le_one
  · exact (div_le_one hp).mpr hb

theorem bagCubicNearNormalSlice_critical_height_bound (ε : BAGCubicTraceWidth)
    (P : Finset ℕ) (S : Finset ℤ) (f : SchwartzMap BAGPhysicalSpace ℂ) (x y τ : ℝ) :
    (∑ r ∈ S, bagCriticalHeightWeight P r *
      ‖(𝓕 (bagCubicNearNormalSlice ε.1 f x y)) (τ+r)‖^2) ≤
      ∫ D : ℝ, ‖bagCubicNearNormalSlice ε.1 f x y D‖^2 := by
  calc
    _ ≤ ∑ r ∈ S, ‖(𝓕 (bagCubicNearNormalSlice ε.1 f x y)) (τ+r)‖^2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_of_le_one_left (sq_nonneg _) (bagCriticalHeightWeight_bounds P r).2
    _ ≤ _ := by
      have hs := bagCubicNearNormalSlice_height_isometry ε f x y τ
      exact sum_le_hasSum S
        (fun r _ => sq_nonneg (‖(𝓕 (bagCubicNearNormalSlice ε.1 f x y)) (τ+r)‖)) hs

/-- The actual shrinking tube has this isometry on every sufficiently large
original natural scale, for every physical Schwartz input. -/
theorem bagCubicShrinkingNearNormalSlice_height_isometry :
    ∀ᶠ N : ℕ in atTop, ∀ f : SchwartzMap BAGPhysicalSpace ℂ, ∀ x y τ : ℝ,
      HasSum (fun r : ℤ =>
        ‖(𝓕 (bagCubicNearNormalSlice ((N : ℝ)^(-(1 : ℝ)/8)) f x y)) (τ+r)‖^2)
        (∫ D : ℝ, ‖bagCubicNearNormalSlice ((N : ℝ)^(-(1 : ℝ)/8)) f x y D‖^2) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(-(1 : ℝ)/8)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/8)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
    simpa only [Function.comp_def,neg_div] using h
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/4))] with N hN he
  have hp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  exact bagCubicNearNormalSlice_height_isometry
    ⟨_,Real.rpow_pos_of_pos hp _,he.le⟩

/-- The complete normalized critical height trace is summable and controlled
without a prime-cutoff constant or derivative penalty. -/
theorem bagCubicNearNormalSlice_critical_height_summable (ε : BAGCubicTraceWidth)
    (P : Finset ℕ) (f : SchwartzMap BAGPhysicalSpace ℂ) (x y τ : ℝ) :
    Summable (fun r : ℤ => bagCriticalHeightWeight P r *
      ‖(𝓕 (bagCubicNearNormalSlice ε.1 f x y)) (τ+r)‖^2) ∧
    (∑' r : ℤ, bagCriticalHeightWeight P r *
      ‖(𝓕 (bagCubicNearNormalSlice ε.1 f x y)) (τ+r)‖^2) ≤
      ∫ D : ℝ, ‖bagCubicNearNormalSlice ε.1 f x y D‖^2 := by
  let a : ℤ → ℝ := fun r => ‖(𝓕 (bagCubicNearNormalSlice ε.1 f x y)) (τ+r)‖^2
  have ha : ∀ r, 0 ≤ a r := fun r => sq_nonneg _
  have hs : HasSum a (∫ D : ℝ, ‖bagCubicNearNormalSlice ε.1 f x y D‖^2) :=
    bagCubicNearNormalSlice_height_isometry ε f x y τ
  have hn (r : ℤ) : 0 ≤ bagCriticalHeightWeight P r * a r :=
    mul_nonneg (bagCriticalHeightWeight_bounds P r).1 (ha r)
  have hb (r : ℤ) : bagCriticalHeightWeight P r * a r ≤ a r :=
    mul_le_of_le_one_left (ha r) (bagCriticalHeightWeight_bounds P r).2
  have hw := Summable.of_nonneg_of_le hn hb hs.summable
  exact ⟨hw,(hw.tsum_le_tsum hb hs.summable).trans_eq hs.tsum_eq⟩

/-- Uniform critical height control for every pair of projector translations. -/
theorem bagCubicNearTranslatedNormalSlice_critical_height_bound (ε : BAGCubicTraceWidth)
    (P : Finset ℕ) (S : Finset ℤ) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (x y u v τ : ℝ) :
    (∑ r ∈ S, bagCriticalHeightWeight P r *
      ‖(𝓕 (bagCubicNearTranslatedNormalSlice ε.1 f x y u v)) (τ+r)‖^2) ≤
      ∫ D : ℝ, ‖bagCubicNearNormalSlice ε.1 f (x+u) (y+v) D‖^2 := by
  let a : ℤ → ℝ := fun r =>
    ‖(𝓕 (bagCubicNearTranslatedNormalSlice ε.1 f x y u v)) (τ+r)‖^2
  have hs : HasSum a (∫ D : ℝ, ‖bagCubicNearNormalSlice ε.1 f (x+u) (y+v) D‖^2) :=
    bagCubicNearTranslatedNormalSlice_height_isometry ε f x y u v τ
  calc
    _ ≤ ∑ r ∈ S, a r := Finset.sum_le_sum (fun r _ =>
      mul_le_of_le_one_left (sq_nonneg _) (bagCriticalHeightWeight_bounds P r).2)
    _ ≤ _ := sum_le_hasSum S (fun r _ => sq_nonneg
      (‖(𝓕 (bagCubicNearTranslatedNormalSlice ε.1 f x y u v)) (τ+r)‖)) hs

end RHTower.BAGTrace
