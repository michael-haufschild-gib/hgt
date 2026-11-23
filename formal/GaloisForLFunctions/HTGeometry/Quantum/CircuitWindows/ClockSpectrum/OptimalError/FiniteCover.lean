import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.CircularArcRange
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.NearbySpectrum

/-! # Sharp circle-covering obstruction for a finite circuit spectrum -/
open Real Set
namespace GaloisForLFunctions.HTGeometry.ClockSpectrum
noncomputable section

/-- The chord from the midpoint of a regular M-gon's complementary gap
to either end of that gap. -/
def clockRadius (M : ℕ) : ℝ := 2*sin (π/(2*M))

/-- A list of at most M unimodular numbers misses an open chordal ball
of radius 2 sin(π/(2M)). The antipode of an enclosing-arc center is an
explicit choice of the missing ball's center. -/
theorem finite_clock_hole {I : Type*} [Fintype I] [Nonempty I] {M : ℕ}
    (hm : Fintype.card I ≤ M) (f : I → ℂ) (hf : ∀ i, ‖f i‖=1) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∀ i, clockRadius M≤‖f i-z‖ := by
  let D := Fintype.card I
  have hD : (1:ℝ)≤D := by exact_mod_cast Fintype.card_pos (α:=I)
  have hM : (1:ℝ)≤M := hD.trans (Nat.cast_le.mpr hm)
  have hDp := zero_lt_one.trans_le hD
  have hMp := zero_lt_one.trans_le hM
  let θ (i : I) := (f i).arg
  obtain ⟨c,hc⟩ := exists_spectralEnclosingArc_center θ
  let w := Complex.exp ((c:ℂ)*Complex.I)
  have hw : ‖w‖=1 := Complex.norm_exp_ofReal_mul_I c
  refine ⟨-w,(norm_neg _).trans hw,fun i => ?_⟩
  let x := π/(2*M)
  have hx : 0≤x := div_nonneg pi_pos.le (by positivity)
  have hxhi : x≤π/2 := div_le_div_of_nonneg_left pi_pos.le (by norm_num)
    (by linarith only [hM])
  have he : Complex.exp (((θ i):ℂ)*Complex.I)=f i := by
    simpa only [θ,hf i,Complex.ofReal_one,one_mul] using Complex.norm_mul_exp_arg_mul_I (f i)
  have hdist : circDist (θ i) c/2 ≤ π/2-x := by
    have ht := spectralEnclosingArcLength_le_finitePhaseArcCeiling θ
    change spectralEnclosingArcLength θ ≤ 2*π*(1-(D:ℝ)⁻¹) at ht
    have him : (M:ℝ)⁻¹≤(D:ℝ)⁻¹ := inv_anti₀ hDp (Nat.cast_le.mpr hm)
    have hh := mul_le_mul_of_nonneg_left him pi_pos.le
    dsimp only [x]
    rw [show π/(2*(M:ℝ))=π*(M:ℝ)⁻¹/2 by ring]
    linarith only [hc i,ht,hh]
  have hs := Real.strictMonoOn_sin.monotoneOn
    (show circDist (θ i) c/2∈Icc (-(π/2)) (π/2) from ⟨by linarith only [circDist_nonneg (θ i) c,pi_pos],
      by linarith only [circDist_le_pi (θ i) c]⟩)
    (show π/2-x∈Icc (-(π/2)) (π/2) from ⟨by linarith only [hxhi,pi_pos],sub_le_self _ hx⟩) hdist
  rw [Real.sin_pi_div_two_sub] at hs
  have he' : ‖f i-w‖ ≤ 2*cos x := by
    rw [←he,norm_expI_sub_eq_sin_circDist]
    exact mul_le_mul_of_nonneg_left hs zero_le_two
  have hpar := parallelogram_law_with_norm_mul (𝕜:=ℂ) (f i) w
  rw [hf i,hw] at hpar
  have hsq := pow_le_pow_left₀ (norm_nonneg _) he' 2
  have hsin := sin_nonneg_of_nonneg_of_le_pi hx (by linarith only [hxhi,pi_pos])
  change 2*sin x≤‖f i-(-w)‖
  rw [sub_neg_eq_add]
  apply (sq_le_sq₀ (mul_nonneg zero_le_two hsin) (norm_nonneg _)).mp
  nlinarith only [hpar,hsq,sin_sq_add_cos_sq x]

/-- A normal approximant with no spectrum near z has to pay the width
of the hole, less the distance from z to the nearest target eigenphase. -/
theorem error_of_spectral_hole {A : Type*} [CStarAlgebra A] {U V : A} [IsStarNormal V]
    {z u : ℂ} (hu : u∈spectrum ℂ U) {r δ : ℝ} (hδ : ‖z-u‖≤δ)
    (hh : ∀ v∈spectrum ℂ V, r≤‖z-v‖) : r≤δ+‖U-V‖ := by
  by_contra! ht
  have hgap : ‖U-V‖<r-δ := by linarith only [ht]
  obtain ⟨v,hv,hd⟩ := SpectralApproximation.nearby_spectral_point hu hgap
  have h := hh v hv
  have htri := norm_sub_le_norm_sub_add_norm_sub z u v
  linarith only [h,htri,hδ,hd]

#print axioms finite_clock_hole
#print axioms error_of_spectral_hole
end
end GaloisForLFunctions.HTGeometry.ClockSpectrum
