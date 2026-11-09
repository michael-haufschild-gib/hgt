import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialElapsedDepthActionIsContinuous
import GaloisForLFunctions.ArithmeticElectrostatics.TheLogarithmicDepthProfilesDissipate

/-!
# Continuity of polynomial logarithmic depth action

A jointly continuous nonnegative root weight varies continuously along
polynomial heat. A local bound on total root norm confines every multiplicity
copy, so uniform continuity on a compact set controls the moving weight.
Subtracting the real-axis baseline gives logarithmic action continuous
through collisions and down to the initial divisor.
-/

open Polynomial Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

private theorem abs_root_sum_difference_le (S : Multiset ℂ) (F G : ℂ → ℝ) {η : ℝ}
    (h : ∀ z ∈ S, |F z - G z| ≤ η) :
    |(S.map F).sum - (S.map G).sum| ≤ (S.card : ℝ) * η := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    have hz := h z (Multiset.mem_cons_self z S)
    have hS := ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
      Nat.cast_add, Nat.cast_one]
    calc
      |F z + (S.map F).sum - (G z + (S.map G).sum)| =
          |(F z - G z) + ((S.map F).sum - (S.map G).sum)| := by congr 1; ring
      _ ≤ |F z - G z| + |(S.map F).sum - (S.map G).sum| := abs_add_le _ _
      _ ≤ η + (S.card : ℝ) * η := add_le_add hz hS
      _ = ((S.card : ℝ) + 1) * η := by ring

/-- Joint continuity of time and weight survives every polynomial heat collision. -/
theorem continuous_polynomial_heat_moving_root_sum {p : ℂ[X]} (hp : p ≠ 0)
    {Ψ : ℝ → ℂ → ℝ} (hΨ : Continuous (Function.uncurry Ψ))
    (hΨ0 : ∀ t z, 0 ≤ Ψ t z) :
    Continuous (fun t : ℝ => ((heatFlow (t : ℂ) p).roots.map (Ψ t)).sum) := by
  have hnorm : Continuous (fun t : ℝ => ((heatFlow (t : ℂ) p).roots.map norm).sum) :=
    (continuous_polynomial_heat_root_sum hp continuous_norm norm_nonneg).comp continuous_ofReal
  apply continuous_iff_continuousAt.mpr
  intro t
  let R := ((heatFlow (t : ℂ) p).roots.map norm).sum + 1
  have hRnear : ∀ᶠ s : ℝ in 𝓝 t, ∀ z ∈ (heatFlow (s : ℂ) p).roots, ‖z‖ ≤ R := by
    filter_upwards [(hnorm.tendsto t).eventually
      (Iio_mem_nhds (show ((heatFlow (t : ℂ) p).roots.map norm).sum < R by
        dsimp only [R]; linarith))] with s hs z hz
    have hsingle : ‖z‖ ≤ ((heatFlow (s : ℂ) p).roots.map norm).sum :=
      Multiset.single_le_sum (fun x hx => by
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hx
        exact norm_nonneg w) ‖z‖ (Multiset.mem_map.mpr ⟨z, hz, rfl⟩)
    exact hsingle.trans hs.le
  let K := closedBall (0 : ℂ) R
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) R)
  let F : ℝ → K → ℝ := fun s z => Ψ s (z : ℂ)
  have hF : Continuous (Function.uncurry F) :=
    hΨ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hu := Continuous.tendstoUniformly F hF t
  have hfixedWeight : Continuous (Ψ t) :=
    hΨ.comp (continuous_const.prodMk continuous_id)
  have hfixed : Continuous (fun s : ℝ => ((heatFlow (s : ℂ) p).roots.map (Ψ t)).sum) :=
    (continuous_polynomial_heat_root_sum hp hfixedWeight (hΨ0 t)).comp continuous_ofReal
  rw [Metric.continuousAt_iff]
  intro ε hε
  let η := ε / (2 * ((p.natDegree : ℝ) + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηN : (p.natDegree : ℝ) * η < ε / 2 := by
    dsimp only [η]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith only [hε]
  have he := (Metric.tendstoUniformly_iff.mp hu) η hη
  have hf := (hfixed.tendsto t).eventually (Metric.ball_mem_nhds _ (half_pos hε))
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp (hRnear.and (he.and hf))
  refine ⟨δ, hδ, fun s hs => ?_⟩
  obtain ⟨hR, hweight, hclose⟩ := hδnear hs
  have hw (z : ℂ) (hz : z ∈ (heatFlow (s : ℂ) p).roots) : |Ψ s z - Ψ t z| ≤ η := by
    have hzK : z ∈ K := by simpa only [K, mem_closedBall, dist_zero_right] using hR z hz
    have h := hweight ⟨z, hzK⟩
    simpa only [F, Real.dist_eq, abs_sub_comm] using h.le
  have hdiff := abs_root_sum_difference_le (heatFlow (s : ℂ) p).roots (Ψ s) (Ψ t) hw
  rw [IsAlgClosed.card_roots_eq_natDegree, (heatFlow_degree_ne_zero hp (s : ℂ)).1] at hdiff
  have hfirst : dist (((heatFlow (s : ℂ) p).roots.map (Ψ s)).sum)
      (((heatFlow (s : ℂ) p).roots.map (Ψ t)).sum) ≤ (p.natDegree : ℝ) * η := by
    simpa only [Real.dist_eq] using hdiff
  calc
    _ ≤ dist (((heatFlow (s : ℂ) p).roots.map (Ψ s)).sum)
          (((heatFlow (s : ℂ) p).roots.map (Ψ t)).sum) +
        dist (((heatFlow (s : ℂ) p).roots.map (Ψ t)).sum)
          (((heatFlow (t : ℂ) p).roots.map (Ψ t)).sum) := dist_triangle _ _ _
    _ ≤ (p.natDegree : ℝ) * η + dist (((heatFlow (s : ℂ) p).roots.map (Ψ t)).sum)
          (((heatFlow (t : ℂ) p).roots.map (Ψ t)).sum) := add_le_add hfirst le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hηN hclose
    _ = ε := by ring

/-- The logarithmic moment with its real-axis baseline removed at every root. -/
def polynomialElapsedLogDepthAction (p : ℂ[X]) (r A t : ℝ) : ℝ :=
  ((heatFlow (t : ℂ) p).roots.map (fun z =>
    elapsedLogDepthProfile r A (z.im ^ 2 + 2 * t) - elapsedLogDepthProfile r A (2 * t))).sum

/-- Corrected logarithmic action remains continuous at collisions and at zero time. -/
theorem continuousOn_polynomialElapsedLogDepthAction {p : ℂ[X]} (hp : p ≠ 0)
    {r A : ℝ} (hr : 0 ≤ r) (hA : 0 < A) :
    ContinuousOn (polynomialElapsedLogDepthAction p r A) (Ici 0) := by
  have hbase : Continuous (fun v : ℝ × ℂ => v.2.im ^ 2 + 2 * max v.1 0) := by fun_prop
  have hweight : Continuous (fun v : ℝ × ℂ =>
      elapsedLogDepthProfile r A (v.2.im ^ 2 + 2 * max v.1 0)) := by
    have h := (continuous_elapsedLogDepthProfile_clamped hr hA).comp hbase
    apply h.congr
    intro v
    exact congrArg (elapsedLogDepthProfile r A) (max_eq_left (by positivity))
  have hc := continuous_polynomial_heat_moving_root_sum hp
    (Ψ := fun t z => elapsedLogDepthProfile r A (z.im ^ 2 + 2 * max t 0)) hweight
    (fun t z => elapsedLogDepthProfile_nonneg hA (by positivity) r)
  have hbaseline : Continuous (fun t : ℝ => elapsedLogDepthProfile r A (2 * max t 0)) := by
    have hclock : Continuous (fun t : ℝ => 2 * max t 0) := by fun_prop
    have h := (continuous_elapsedLogDepthProfile_clamped hr hA).comp hclock
    apply h.congr
    intro t
    exact congrArg (elapsedLogDepthProfile r A) (max_eq_left (by positivity))
  have h := hc.sub (hbaseline.mul_const (p.natDegree : ℝ))
  apply h.continuousOn.congr
  intro t ht
  simp only [Pi.sub_apply, max_eq_left (show 0 ≤ t from ht)]
  unfold polynomialElapsedLogDepthAction
  rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
    IsAlgClosed.card_roots_eq_natDegree, (heatFlow_degree_ne_zero hp (t : ℂ)).1]
  ring

/-- A positive exponent removes the initial baseline exactly. -/
theorem polynomialElapsedLogDepthAction_zero (p : ℂ[X]) {r : ℝ} (hr : 0 < r) (A : ℝ) :
    polynomialElapsedLogDepthAction p r A 0 =
      (p.roots.map (fun z => elapsedLogDepthProfile r A (z.im ^ 2))).sum := by
  simp only [polynomialElapsedLogDepthAction, Complex.ofReal_zero, heatFlow_zero_time,
    mul_zero, add_zero, elapsedLogDepthProfile_zero hr, sub_zero]

#print axioms continuous_polynomial_heat_moving_root_sum
#print axioms continuousOn_polynomialElapsedLogDepthAction
#print axioms polynomialElapsedLogDepthAction_zero

end
end GaloisForLFunctions.ArithmeticElectrostatics
