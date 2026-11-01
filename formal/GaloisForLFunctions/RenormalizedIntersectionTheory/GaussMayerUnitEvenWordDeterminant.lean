import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEvenWordDeterminant
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerWordProbability
import GaloisForLFunctions.HTGeometry.HolomorphicRealTaylor

/-! The exact even-word trace exponential reaches the unit spectral parameter
on the half-plane `Re w>2`, by the source denominator probability bound. -/

open Complex Filter Metric Set Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerFredholm MayerWords MayerOrbitDeterminant MayerWordProbability
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerUnitOrbitDeterminant

private theorem radius_beyond_one {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ R : ℝ, 1 < R ∧ R^2*q < 1 := by
  have hd : 0 < 1+q := by linarith only [hq]
  refine ⟨2/(1+q), (lt_div_iff₀ hd).mpr (by linarith only [hq1]), ?_⟩
  rw [div_pow, div_mul_eq_mul_div]
  apply (div_lt_iff₀ (sq_pos_of_pos hd)).mpr
  have hs : 0 < (1-q)^2 := sq_pos_of_pos (sub_pos.mpr hq1)
  nlinarith only [hs]

private theorem norm_trace_sum_le {w : ℂ} (hw : 2 < w.re) (n : ℕ) :
    ‖∑' a : Word (2*n+2), wordTrace w (2*n+1) a‖ ≤
      (8/3 : ℝ)*decayRate w^(n+1) :=
  (norm_tsum_le_tsum_norm (summable_wordTrace
    (show 1 < w.re by linarith only [hw]) (2*n+1)).norm).trans
    (tsum_norm_even_wordTrace_le hw n)

/-- The source decay gives a holomorphic even-word logarithm on every spectral
disk whose squared radius times the geometric decay rate is less than one. -/
theorem differentiableOn_evenWordExponent {w : ℂ} (hw : 2 < w.re)
    {R : ℝ} (hR : 0 < R) (hRq : R^2*decayRate w < 1) :
    DifferentiableOn ℂ (evenWordExponent w) (ball 0 R) := by
  let u : ℕ → ℝ := fun n => (8/3 : ℝ)*(R^2*decayRate w)^(n+1)
  have hq0 : 0 ≤ R^2*decayRate w := mul_nonneg (sq_nonneg R) (decayRate_bounds hw).1.le
  have hu : Summable u := by
    have h := ((summable_geometric_of_lt_one hq0 hRq).mul_right
      (R^2*decayRate w)).mul_left (8/3 : ℝ)
    simpa only [u,pow_succ] using h
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      ‖z^(2*n+2) / ((n+1 : ℕ) : ℂ) *
        ∑' a : Word (2*n+2), wordTrace w (2*n+1) a‖ ≤ u n := by
    have hzR : ‖z‖ ≤ R := (mem_ball_zero_iff.mp hz).le
    have hden : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hquot : ‖z^(2*n+2) / ((n+1 : ℕ) : ℂ)‖ ≤ R^(2*n+2) := by
      rw [norm_div,norm_pow,Complex.norm_natCast]
      exact (div_le_self (pow_nonneg (norm_nonneg z) _) hden).trans
        (pow_le_pow_left₀ (norm_nonneg z) hzR _)
    rw [norm_mul]
    calc
      _ ≤ R^(2*n+2)*((8/3 : ℝ)*decayRate w^(n+1)) :=
        mul_le_mul hquot (norm_trace_sum_le hw n) (norm_nonneg _)
          (pow_nonneg hR.le _)
      _ = u n := by
        dsimp [u]
        rw [show 2*n+2 = 2*(n+1) by omega, pow_mul, mul_pow]
        ring
  have h := hasSum_iteratedDeriv_of_summable_bound isOpen_ball
    (fun n => (((differentiable_id.pow (2*n+2)).div_const ((n+1 : ℕ) : ℂ)).mul_const
      (∑' a : Word (2*n+2), wordTrace w (2*n+1) a)).differentiableOn) hu hb
  exact h.1

/-- Absolute convergence of the full countable even-word logarithm holds
throughout the closed unit spectral disk when `Re w>2`. -/
theorem summable_norm_evenWordSeries_on_closed_unit {w z : ℂ} (hw : 2 < w.re)
    (hz : ‖z‖ ≤ 1) :
    Summable (fun p : (Σ n : ℕ, Word (2*n+2)) =>
      ‖z^(2*p.1+2) / ((p.1+1 : ℕ) : ℂ) * wordTrace w (2*p.1+1) p.2‖) := by
  have hgeom : Summable (fun n : ℕ => (8/3 : ℝ)*decayRate w^(n+1)) := by
    have h := ((summable_geometric_of_lt_one (decayRate_bounds hw).1.le
      (decayRate_bounds hw).2).mul_right (decayRate w)).mul_left (8/3 : ℝ)
    simpa only [pow_succ] using h
  have hf (n : ℕ) : Summable (fun a : Word (2*n+2) =>
      ‖z^(2*n+2) / ((n+1 : ℕ) : ℂ) * wordTrace w (2*n+1) a‖) := by
    simp only [norm_mul]
    exact (summable_wordTrace (show 1 < w.re by linarith only [hw]) (2*n+1)).norm.mul_left _
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨hf, hgeom.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _) ?_⟩
  intro n
  have hden : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hcoef : ‖z^(2*n+2) / ((n+1 : ℕ) : ℂ)‖ ≤ 1 := by
    rw [norm_div,norm_pow,Complex.norm_natCast]
    exact (div_le_self (pow_nonneg (norm_nonneg z) _) hden).trans
      (pow_le_one₀ (norm_nonneg z) hz)
  simp only [norm_mul,tsum_mul_left]
  exact (mul_le_of_le_one_left (tsum_nonneg fun _ => norm_nonneg _) hcoef).trans
    (tsum_norm_even_wordTrace_le hw n)

/-- The actual global signed determinant product equals the even-word trace
exponential on the closed unit spectral disk throughout `Re w>2`. -/
theorem signed_determinant_eq_evenWordExponent_on_closed_unit {w z : ℂ}
    (hw : 2 < w.re) (hz : ‖z‖ ≤ 1) :
    determinant w (show 0 < w.re by linarith only [hw]) z *
      determinant w (show 0 < w.re by linarith only [hw]) (-z) =
      exp (-evenWordExponent w z) := by
  have hw0 : 0 < w.re := by linarith only [hw]
  have hw1 : 1 < w.re := by linarith only [hw]
  obtain ⟨R,hR,hRq⟩ := radius_beyond_one (decayRate_bounds hw).1 (decayRate_bounds hw).2
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hF : AnalyticOnNhd ℂ (fun z : ℂ => determinant w hw0 z * determinant w hw0 (-z))
      (ball 0 R) :=
    ((differentiable_determinant hw0).mul
      ((differentiable_determinant hw0).comp differentiable_id.neg)).differentiableOn.analyticOnNhd
      isOpen_ball
  have hG : AnalyticOnNhd ℂ (fun z : ℂ => exp (-evenWordExponent w z)) (ball 0 R) :=
    ((differentiableOn_evenWordExponent hw hR0 hRq).neg.cexp).analyticOnNhd isOpen_ball
  obtain ⟨r,hr,he⟩ := exists_signed_determinant_eq_evenWordExponent hw1
  have hev : (fun z : ℂ => determinant w hw0 z * determinant w hw0 (-z)) =ᶠ[𝓝 0]
      (fun z : ℂ => exp (-evenWordExponent w z)) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact he z (mem_ball_zero_iff.mp hz)
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_ball (0 : ℂ) R).isPreconnected
    (mem_ball_self hR0) hev (mem_ball_zero_iff.mpr (hz.trans_lt hR))

/-- The signed determinant identity at unit spectral parameter. -/
theorem signed_determinant_one_eq_evenWordExponent {w : ℂ} (hw : 2 < w.re) :
    determinant w (show 0 < w.re by linarith only [hw]) 1 *
      determinant w (show 0 < w.re by linarith only [hw]) (-1) =
      exp (-evenWordExponent w 1) :=
  signed_determinant_eq_evenWordExponent_on_closed_unit hw (by simp)

/-- The actual Mayer determinant has no spectral zero in the closed unit disk
when `Re w>2`. -/
theorem determinant_ne_zero_on_closed_unit {w z : ℂ} (hw : 2 < w.re) (hz : ‖z‖ ≤ 1) :
    determinant w (show 0 < w.re by linarith only [hw]) z ≠ 0 := by
  intro he
  have hid := signed_determinant_eq_evenWordExponent_on_closed_unit hw hz
  rw [he,zero_mul] at hid
  exact exp_ne_zero _ hid.symm

#print axioms differentiableOn_evenWordExponent
#print axioms summable_norm_evenWordSeries_on_closed_unit
#print axioms signed_determinant_eq_evenWordExponent_on_closed_unit
#print axioms signed_determinant_one_eq_evenWordExponent
#print axioms determinant_ne_zero_on_closed_unit
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerUnitOrbitDeterminant
