import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireDegreeControl
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireExpandingTaylor

/-! # Uniform small-value bounds from one calibrated local field -/
open MeasureTheory Set Polynomial RiemannGaussian
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- Taylor truncation on a comparison circle larger than the sampled
interval by a factor of `2*q` absorbs the exponential loss in extrapolation. -/
private theorem taylor_bound {b q M : ℝ} (hb : 0<b) (hq : 1≤q) (hM : 0≤M)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hr : ∀ x : ℝ, (f x).im=0)
    (hbound : ∀ z : ℂ, ‖z‖=2*q*b → ‖f z‖≤M) (k : ℕ) {x : ℝ} (hx : |x|≤b) :
    |(entireRealTaylorPolynomial f k).eval x - (f x).re| ≤ (2*M/2^k)/q^k := by
  let R := 2*q*b
  have hq' : 0<q := zero_lt_one.trans_le hq
  have hR : 0<R := by dsimp [R]; positivity
  have hn : ‖(x:ℂ)‖≤b := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx
  have hbr : b<R := by dsimp only [R]; nlinarith only [hb,hq,mul_le_mul_of_nonneg_right hq hb.le]
  have hrat : ‖(x:ℂ)‖/R ≤ 1/(2*q) := by
    apply (div_le_div_iff₀ hR (by positivity)).mpr
    dsimp only [R]
    linarith only [mul_le_mul_of_nonneg_right hn (by positivity : 0≤2*q)]
  have hden : 1/2 ≤ 1-‖(x:ℂ)‖/R := by
    have hhalf : (1:ℝ)/(2*q) ≤ 1/2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith only [hq]
    linarith only [hrat.trans hhalf]
  have he : Complex.ofReal ((entireRealTaylorPolynomial f k).eval x) =
      (cauchyPowerSeries f 0 1).partialSum k (x:ℂ) := by
    rw [←entireRealTaylorPolynomial_map_eval hf hr,Polynomial.eval_map]
    exact (Polynomial.eval₂_at_apply Complex.ofRealHom x).symm
  have ht := entire_cauchyPowerSeries_partialSum_remainder_le_of_sphere_bound hf hR hbound (hn.trans_lt hbr) k
  have hreal := Complex.abs_re_le_norm (Complex.ofReal ((entireRealTaylorPolynomial f k).eval x)-f x)
  simp only [Complex.sub_re,Complex.ofReal_re] at hreal
  rw [he] at hreal
  calc
    _ ≤ M * (‖(x:ℂ)‖/R)^k / (1-‖(x:ℂ)‖/R) := hreal.trans ht
    _ ≤ M * (‖(x:ℂ)‖/R)^k / (1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ ≤ M * (1/(2*q))^k / (1/2) := by gcongr
    _ = _ := by rw [div_pow,one_pow,mul_pow]; ring

/-- A family of real entire responses with a common growth envelope and a
nonzero calibration has a common signal threshold outside a prescribed
Lebesgue measure of field values. The calibration can vary across the family. -/
theorem anchored_sublevel {b h δ : ℝ} (hb : 0<b) (hh : 0<h) (hδ : 0<δ)
    (M : ℝ → ℝ) (hM : ∀ R, 0≤M R) :
    ∃ ε : ℝ, 0<ε ∧ ∀ (f : ℂ → ℂ), Differentiable ℂ f → (∀ x : ℝ, (f x).im=0) →
      (∀ z : ℂ, ‖f z‖≤M ‖z‖) → ∀ u : ℝ, |u|≤b → h≤|(f u).re| →
      volume.real {x ∈ Ioo (-b) b | |(f (x:ℂ)).re|≤ε} ≤ δ := by
  let q := 1+8*Real.exp 1*b/δ
  have hq : 1≤q := by exact le_add_of_nonneg_right (by positivity)
  have hq' : 0<q := zero_lt_one.trans_le hq
  let B := M (2*q*b)
  obtain ⟨k,hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually (Filter.eventually_gt_atTop (8*B/h))).exists
  let ε := h/(4*q^k)
  have hε : 0<ε := by dsimp only [ε]; positivity
  have hk' := (div_lt_iff₀ hh).mp hk
  have hres : (2*B/2^k)/q^k ≤ ε := by
    calc
      _ ≤ (h/4)/q^k := div_le_div_of_nonneg_right
        ((div_le_iff₀ (by positivity)).mpr (by nlinarith only [hk'])) (pow_pos hq' _).le
      _ = ε := by dsimp only [ε]; ring
  have hsmall : ε≤h/4 := by
    apply div_le_div_of_nonneg_left hh.le (by norm_num)
    linarith only [one_le_pow₀ hq (n := k)]
  refine ⟨ε,hε,?_⟩
  intro f hf hr hbound u hu hcal
  let P := entireRealTaylorPolynomial f k
  have hnear (x : ℝ) (hx : |x|≤b) : |P.eval x-(f x).re|≤ε :=
    (taylor_bound hb hq (hM _) hf hr (fun z hz => by simpa only [hz] using hbound z) k hx).trans hres
  have ha : (2*ε)*q^k < |P.eval u| := by
    have hdiff := abs_sub_abs_le_abs_sub ((f u).re) (P.eval u)
    rw [abs_sub_comm ((f u).re)] at hdiff
    have hv : (2*ε)*q^k=h/2 := by dsimp only [ε]; field_simp; norm_num
    rw [hv]
    linarith only [hdiff,hnear u hu,hcal,hsmall,hh]
  have hfar (x : ℝ) (hx : x∈Ioo (-b) b) : |u-x| ≤ 2*b := by
    rw [abs_le] at hu ⊢
    constructor <;> linarith only [hu.1,hu.2,hx.1,hx.2]
  have hpoly := volume_sublevel_comp_le P (entireRealTaylorPolynomial_natDegree_le f k)
    (g := id) (lam := 1) zero_lt_one (by positivity : 0<2*b) hq'
    (by intros; simp only [one_mul,id_eq]; exact le_rfl) hfar ha
  let S := {x ∈ Ioo (-b) b | |P.eval x|≤2*ε}
  have hfin : volume S ≠ ⊤ := ne_top_of_le_ne_top (by simp : volume (Ioo (-b) b) ≠ ⊤)
    (measure_mono (fun _ hx => hx.1 : S ⊆ Ioo (-b) b))
  refine (ENNReal.toReal_mono hfin (measure_mono (t := S) ?_)).trans (hpoly.trans ?_)
  · intro x hx
    have ht := abs_sub_abs_le_abs_sub (P.eval x) (f x).re
    have he := hnear x (abs_le.mpr ⟨hx.1.1.le,hx.1.2.le⟩)
    exact ⟨hx.1,by linarith only [ht,he,hx.2]⟩
  · rw [one_mul,div_le_iff₀ hq']
    dsimp only [q]
    rw [mul_add,mul_one,show δ*(8*Real.exp 1*b/δ)=8*Real.exp 1*b by field_simp]
    linarith only [hδ]

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
