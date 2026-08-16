import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# A holomorphic function with nonnegative real part is either strictly positive or purely imaginary

For a holomorphic `f` the function `exp(-f)` has modulus `exp(-Re f)`, so a zero of the real part
is a maximum of that modulus.  The maximum modulus principle then forces `exp(-f)` — hence the real
part of `f` — to be constant on a connected domain.  Consequently a nonnegative real part that is
positive at one point is positive everywhere, which is the minimum principle in the form a Herglotz
limit needs: passing to a limit only gives `Re ≥ 0`, and a single positive value upgrades it.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The modulus of `exp(-f)` is the exponential of minus the real part of `f`. -/
theorem norm_exp_neg (w : ℂ) : ‖Complex.exp (-w)‖ = Real.exp (-w.re) := by
  rw [Complex.norm_exp, Complex.neg_re]

/-- **The minimum principle for a nonnegative real part.**  On a connected domain, a holomorphic
function whose real part is nonnegative and positive somewhere has a strictly positive real part
everywhere. -/
theorem re_pos_of_re_nonneg_of_exists_pos {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (hnn : ∀ z ∈ U, 0 ≤ (f z).re) {z₁ : ℂ} (hz₁ : z₁ ∈ U) (hpos : 0 < (f z₁).re) :
    ∀ z ∈ U, 0 < (f z).re := by
  intro z hz
  rcases lt_or_ge 0 (f z).re with h | h
  · exact h
  exfalso
  have hzero : (f z).re = 0 := le_antisymm h (hnn z hz)
  have hgd : DifferentiableOn ℂ (fun w => Complex.exp (-(f w))) U := (hf.neg).cexp
  have hmax : IsMaxOn (norm ∘ fun w => Complex.exp (-(f w))) U z := by
    intro w hw
    simp only [Function.comp_apply, norm_exp_neg]
    rw [hzero]
    simp only [neg_zero, Real.exp_zero]
    exact Real.exp_le_one_iff.mpr (by linarith [hnn w hw])
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hU hgd hz hmax
  have h1 : Complex.exp (-(f z₁)) = Complex.exp (-(f z)) := heq hz₁
  have h2 : Real.exp (-(f z₁).re) = Real.exp (-(f z).re) := by
    rw [← norm_exp_neg, ← norm_exp_neg, h1]
  have h3 : -(f z₁).re = -(f z).re := Real.exp_injective h2
  rw [hzero] at h3
  linarith

/-- The real-part sign passes to a locally uniform limit, weakly. -/
theorem re_nonneg_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {G : ℂ → ℂ} {U : Set ℂ}
    (hlim : TendstoLocallyUniformlyOn F G l U)
    (hpos : ∀ᶠ i in l, ∀ z ∈ U, 0 ≤ (F i z).re) :
    ∀ z ∈ U, 0 ≤ (G z).re := by
  intro z hz
  have hpt : Tendsto (fun i => F i z) l (𝓝 (G z)) := hlim.tendsto_at hz
  have hre : Tendsto (fun i => (F i z).re) l (𝓝 (G z).re) :=
    (Complex.continuous_re.tendsto (G z)).comp hpt
  exact ge_of_tendsto hre (hpos.mono fun i hi => hi z hz)

/-- **Herglotz rigidity of a locally uniform limit.**  A locally uniform limit of functions with
positive real part has strictly positive real part as soon as it is positive at one point. -/
theorem re_pos_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hlim : TendstoLocallyUniformlyOn F G l U)
    (hpos : ∀ᶠ i in l, ∀ z ∈ U, 0 ≤ (F i z).re)
    {z₁ : ℂ} (hz₁ : z₁ ∈ U) (hz₁pos : 0 < (G z₁).re) :
    ∀ z ∈ U, 0 < (G z).re :=
  re_pos_of_re_nonneg_of_exists_pos hU hUc (hlim.differentiableOn hF hU)
    (re_nonneg_of_tendstoLocallyUniformlyOn hlim hpos) hz₁ hz₁pos

end GaloisForLFunctions.HTGeometry
