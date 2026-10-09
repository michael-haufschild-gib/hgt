import GaloisForLFunctions.HTGeometry.OneFiberDiskGrowth
import GaloisForLFunctions.Bottcher.W4LinWinding
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic

open Filter Topology Set Metric
namespace GaloisForLFunctions.HTGeometry

/-- A normalized local biholomorphism on a disk omits some value within twice the radius. -/
theorem exists_nearby_omitted_value_normalized_disk {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hi : InjOn f (ball 0 R))
    (hd : ∀ z ∈ ball 0 R, deriv f z ≠ 0) (hf0 : f 0 = 0)
    (hd0 : deriv f 0 = 1) :
    ∃ a : ℂ, ‖a‖ < 2 * R ∧ ∀ z ∈ ball 0 R, f z ≠ a := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hn : ¬ ball (0 : ℂ) (2 * R) ⊆ f '' ball 0 R := by
    intro hsub
    let g := Bottcher.imageInv f (ball 0 R)
    have hg : AnalyticOnNhd ℂ g (ball 0 (2 * R)) :=
      (Bottcher.imageInv_analytic isOpen_ball (hf.analyticOnNhd isOpen_ball) hi hd).mono hsub
    have hg0 : g 0 = 0 := by
      have hx : (0 : ℂ) ∈ f '' ball 0 R := ⟨0, h0, hf0⟩
      apply hi (Bottcher.imageInv_mem hx) h0
      exact (Bottcher.imageInv_right hx).trans hf0.symm
    have h00 : (0 : ℂ) ∈ ball 0 (2 * R) := mem_ball_self (by positivity)
    have hgf : (fun z => f (g z)) =ᶠ[𝓝 (0 : ℂ)] id := by
      filter_upwards [isOpen_ball.mem_nhds h00] with z hz
      exact Bottcher.imageInv_right (hsub hz)
    have hdf : HasDerivAt f 1 (g 0) := by
      rw [hg0, ← hd0]
      exact (hf.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    have hdg : HasDerivAt g (deriv g 0) 0 := (hg 0 h00).differentiableAt.hasDerivAt
    have hder : deriv g 0 = 1 := by
      have hh := (hdf.comp 0 hdg).congr_of_eventuallyEq hgf.symm
      simpa using hh.unique (hasDerivAt_id (0 : ℂ))
    have hmaps : MapsTo g (ball 0 (2 * R)) (closedBall (g 0) R) := by
      intro z hz
      rw [hg0]
      exact ball_subset_closedBall (Bottcher.imageInv_mem (hsub hz))
    have hb := Complex.norm_deriv_le_div_of_mapsTo_ball hg.differentiableOn hmaps
      (by positivity : 0 < 2 * R)
    have hh : R / (2 * R) = (1 : ℝ) / 2 := by field_simp [hR.ne']
    norm_num [hder, hh] at hb
  obtain ⟨a, ha, hna⟩ := Set.not_subset.mp hn
  refine ⟨a, by simpa using ha, ?_⟩
  intro z hz heq
  exact hna ⟨z, hz, heq⟩

/-- Universal half-disk control for normalized analytic embeddings with analytic local inverses. -/
theorem exists_normalized_embedding_disk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (R : ℝ), 0 < R →
      DifferentiableOn ℂ f (ball 0 R) → InjOn f (ball 0 R) →
      (∀ z ∈ ball 0 R, deriv f z ≠ 0) → f 0 = 0 → deriv f 0 = 1 →
      ∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖f z‖ ≤ C * R := by
  obtain ⟨B, hB, hb⟩ := exists_one_fiber_omitted_value_disk_bound
  refine ⟨2 * (B + 1), by linarith, ?_⟩
  intro f R hR hf hi hd hf0 hd0 z hz
  obtain ⟨a, ha, homit⟩ := exists_nearby_omitted_value_normalized_disk hR hf hi hd hf0 hd0
  have hg := hb f 0 a R hR hf
    (fun w hw heq => hi hw (mem_ball_self hR) heq) homit z (by simpa using hz)
  rw [hf0, zero_sub, norm_neg] at hg
  have ht : ‖f z‖ ≤ ‖f z - a‖ + ‖a‖ := by simpa using norm_add_le (f z - a) a
  calc
    ‖f z‖ ≤ (B + 1) * ‖a‖ := by nlinarith
    _ ≤ (B + 1) * (2 * R) := mul_le_mul_of_nonneg_left ha.le (by linarith)
    _ = 2 * (B + 1) * R := by ring

end GaloisForLFunctions.HTGeometry
