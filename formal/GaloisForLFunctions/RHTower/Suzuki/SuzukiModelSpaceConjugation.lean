import GaloisForLFunctions.RHTower.L2FourierConjugation
import GaloisForLFunctions.RHTower.Suzuki.SuzukiModelSpaceOrthogonal

noncomputable section

/-!
# Suzuki Lemma 5.1: the model space is the Fourier image of `V(0)`

Section 5 of Suzuki's paper works with the conjugate-linear involution `K = F^{-1} M_Θ J F` of
equation (5.1) and the spaces `V(t) = L²(t,∞) ∩ K L²(t,∞)` of equation (5.2).  Although `K` is
only conjugate-linear, `K S` is a complex subspace whenever `S` is, because `c • K f = K (conj c • f)`.

Lemma 5.1 says `K(Θ) = F(V(0))`.  Transporting by `F` turns it into

```text
H² ∩ Θ · conj(H²) = H² ∩ Θ · (H²)^⊥ = H² ∩ (Θ H²)^⊥,
```

so the whole content is `conj(H²) = (H²)^⊥` together with unitarity of multiplication by `Θ`.
The first is `map_star_hardyL2`, proved from the conjugation law for the Fourier transform and the
fact that reflection exchanges the two datum rays; the second is `thetaUnitary`.
-/

open MeasureTheory FourierTransform

namespace RHTower

abbrev L2R := Lp ℂ 2 (volume : Measure ℝ)

theorem lpStar_add (f g : L2R) : star (f + g) = star f + star g := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star (f + g), MeasureTheory.Lp.coeFn_add f g,
    MeasureTheory.Lp.coeFn_add (star f) (star g), MeasureTheory.Lp.coeFn_star f,
    MeasureTheory.Lp.coeFn_star g] with x h1 h2 h3 h4 h5
  simp only [h1, h3, Pi.add_apply, Pi.star_apply, h2, h4, h5]
  exact star_add _ _

theorem lpStar_smul (c : ℂ) (f : L2R) :
    star (c • f) = (starRingEnd ℂ) c • star f := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star (c • f), MeasureTheory.Lp.coeFn_smul c f,
    MeasureTheory.Lp.coeFn_smul ((starRingEnd ℂ) c) (star f),
    MeasureTheory.Lp.coeFn_star f] with x h1 h2 h3 h4
  simp only [h1, h3, Pi.smul_apply, Pi.star_apply, h2, h4, smul_eq_mul]
  exact star_mul' c _

/-- Complex conjugation on `L²(ℝ)` as a conjugate-linear map. -/
def lpStarₛₗ : L2R →ₛₗ[starRingEnd ℂ] L2R where
  toFun := star
  map_add' := lpStar_add
  map_smul' := lpStar_smul

@[simp] theorem lpStarₛₗ_apply (f : L2R) : lpStarₛₗ f = star f := rfl

theorem star_star_lp (f : L2R) : star (star f) = f := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star (star f), MeasureTheory.Lp.coeFn_star f]
    with x h1 h2
  simp only [h1, Pi.star_apply, h2]
  exact star_star _

theorem map_star_lowerHalfLineL2 :
    Submodule.map lpStarₛₗ lowerHalfLineL2 = lowerHalfLineL2 := by
  refine le_antisymm ?_ ?_
  · rintro f ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_lowerHalfLineL2_iff] at hg
    rw [mem_lowerHalfLineL2_iff]
    filter_upwards [hg, MeasureTheory.Lp.coeFn_star g] with x hx h1 hpos
    rw [lpStarₛₗ_apply, h1, Pi.star_apply, hx hpos, star_zero]
  · intro f hf
    refine ⟨star f, ?_, by rw [lpStarₛₗ_apply, star_star_lp]⟩
    rw [SetLike.mem_coe, mem_lowerHalfLineL2_iff]
    rw [mem_lowerHalfLineL2_iff] at hf
    filter_upwards [hf, MeasureTheory.Lp.coeFn_star f] with x hx h1 hpos
    rw [h1, Pi.star_apply, hx hpos, star_zero]

theorem l2Reflection_coeFn (f : L2R) :
    ((l2Reflection f : L2R) : ℝ → ℂ) =ᵐ[volume] fun x => (f : ℝ → ℂ) (-x) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem map_l2Reflection_lowerHalfLineL2 :
    Submodule.map (l2Reflection : L2R →L[ℂ] L2R).toLinearMap lowerHalfLineL2 = halfLineL2 := by
  refine le_antisymm ?_ ?_
  · rintro f ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_lowerHalfLineL2_iff] at hg
    rw [mem_halfLineL2_iff]
    have hg' : ∀ᵐ x : ℝ, 0 < (-x) → (g : ℝ → ℂ) (-x) = 0 :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hg
    filter_upwards [hg', l2Reflection_coeFn g] with x hx h1 hneg
    show ((l2Reflection g : L2R) : ℝ → ℂ) x = 0
    rw [h1]
    exact hx (by linarith)
  · intro f hf
    rw [mem_halfLineL2_iff] at hf
    refine ⟨l2Reflection f, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_lowerHalfLineL2_iff]
      have hf' : ∀ᵐ x : ℝ, (-x) < 0 → (f : ℝ → ℂ) (-x) = 0 :=
        (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hf
      filter_upwards [hf', l2Reflection_coeFn f] with x hx h1 hpos
      rw [h1]
      exact hx (by linarith)
    · show l2Reflection (l2Reflection f) = f
      refine MeasureTheory.Lp.ext ?_
      have hrefl : ∀ᵐ x : ℝ, ((l2Reflection f : L2R) : ℝ → ℂ) (-x) = (f : ℝ → ℂ) (-(-x)) :=
        (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
          (l2Reflection_coeFn f)
      filter_upwards [l2Reflection_coeFn (l2Reflection f), hrefl] with x h1 h2
      rw [h1, h2, neg_neg]

theorem map_star_hardyL2 : Submodule.map lpStarₛₗ hardyL2 = hardyL2ᗮ := by
  have key : ∀ g : L2R, g ∈ lowerHalfLineL2 →
      star ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) g)
        = (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (l2Reflection (star g)) := by
    intro g _
    have h := star_fourier_star (star g)
    rw [star_star_lp] at h
    rw [h, l2_fourier_reflection]
  rw [hardyL2_orthogonal]
  refine le_antisymm ?_ ?_
  · rintro f ⟨h, hh, rfl⟩
    rw [SetLike.mem_coe, hardyL2] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    refine ⟨l2Reflection (star g), ?_, ?_⟩
    · rw [SetLike.mem_coe, ← map_l2Reflection_lowerHalfLineL2]
      exact ⟨star g, (map_star_lowerHalfLineL2 ▸ ⟨g, hg, rfl⟩ : star g ∈ lowerHalfLineL2), rfl⟩
    · exact (key g hg).symm
  · rintro f ⟨h, hh, rfl⟩
    rw [SetLike.mem_coe, ← map_l2Reflection_lowerHalfLineL2] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    refine ⟨(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (star g), ⟨star g, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, ← map_star_lowerHalfLineL2]
      exact ⟨g, hg, rfl⟩
    · rw [lpStarₛₗ_apply, key (star g) (map_star_lowerHalfLineL2 ▸ ⟨g, hg, rfl⟩), star_star_lp]
      rfl


/-! ## Suzuki's involution `K` and the space `V(0)` -/

/-- **Suzuki equation (5.1).**  The conjugate-linear involution `K = F^{-1} M_Θ J F`. -/
def suzukiKFun (f : L2R) : L2R :=
  (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm
    (thetaMul (star ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f)))

theorem suzukiKFun_add (f g : L2R) : suzukiKFun (f + g) = suzukiKFun f + suzukiKFun g := by
  simp only [suzukiKFun, map_add, lpStar_add]

theorem suzukiKFun_smul (c : ℂ) (f : L2R) :
    suzukiKFun (c • f) = (starRingEnd ℂ) c • suzukiKFun f := by
  simp only [suzukiKFun, map_smul, lpStar_smul]

/-- `K` as a conjugate-linear map. -/
def suzukiKₛₗ : L2R →ₛₗ[starRingEnd ℂ] L2R where
  toFun := suzukiKFun
  map_add' := suzukiKFun_add
  map_smul' := suzukiKFun_smul

@[simp] theorem suzukiKₛₗ_apply (f : L2R) : suzukiKₛₗ f = suzukiKFun f := rfl

theorem fourier_suzukiKFun (f : L2R) :
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (suzukiKFun f)
      = thetaMul (star ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) f)) := by
  rw [suzukiKFun, LinearIsometryEquiv.apply_symm_apply]

/-- **Suzuki equation (5.2) at `t = 0`.** -/
def suzukiV0 : Submodule ℂ L2R :=
  lowerHalfLineL2 ⊓ Submodule.map suzukiKₛₗ lowerHalfLineL2

theorem map_fourier_map_suzukiK :
    Submodule.map ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap)
        (Submodule.map suzukiKₛₗ lowerHalfLineL2)
      = Submodule.map (thetaUnitary.toLinearEquiv.toLinearMap) hardyL2ᗮ := by
  rw [← map_star_hardyL2]
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨star ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) g), ⟨_, ⟨g, hg, rfl⟩, rfl⟩, ?_⟩
    exact (fourier_suzukiKFun g).symm ▸ rfl
  · rintro y ⟨z, ⟨w, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
    refine ⟨suzukiKFun g, ⟨g, hg, rfl⟩, ?_⟩
    exact fourier_suzukiKFun g

theorem thetaMul_star_thetaMul_star (h : L2R) :
    thetaMul (star (thetaMul (star h))) = h := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [thetaMul_coeFn (star (thetaMul (star h))),
    MeasureTheory.Lp.coeFn_star (thetaMul (star h)), thetaMul_coeFn (star h),
    MeasureTheory.Lp.coeFn_star h] with x h1 h2 h3 h4
  rw [h1, h2, Pi.star_apply, h3, h4, Pi.star_apply]
  have hu : suzukiThetaSymbol x * (starRingEnd ℂ) (suzukiThetaSymbol x) = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, norm_suzukiThetaSymbol]
    norm_num
  rw [star_mul', star_star, ← mul_assoc]
  show suzukiThetaSymbol x * (starRingEnd ℂ) (suzukiThetaSymbol x) * (h : ℝ → ℂ) x = _
  rw [hu, one_mul]

/-- **`K` is an involution** (Suzuki, section 5). -/
theorem suzukiKFun_suzukiKFun (f : L2R) : suzukiKFun (suzukiKFun f) = f := by
  rw [suzukiKFun, fourier_suzukiKFun, thetaMul_star_thetaMul_star,
    LinearIsometryEquiv.symm_apply_apply]


/-- **Suzuki Lemma 5.1.**  The model space is the Fourier image of `V(0)`. -/
theorem map_fourier_suzukiV0 :
    Submodule.map ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap) suzukiV0
      = suzukiModelSpace := by
  rw [suzukiV0, Submodule.map_inf _ (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).injective,
    map_fourier_map_suzukiK, suzukiModelSpace_eq_inf_map]
  rfl


end RHTower
