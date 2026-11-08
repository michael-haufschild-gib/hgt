import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialHeatCollisionsAreFinite
import GaloisForLFunctions.HTGeometry.PolynomialRoots.WeightedSumContinuity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Continuity of polynomial elapsed-depth action

Heat preserves the degree of a nonzero polynomial. Locally uniform convergence
therefore preserves every continuous nonnegative root sum, including through
multiple roots. A local bound on the sum of root norms confines the roots and
permits a moving depth weight. The corrected action is continuous down to zero
time, where every positive exponent recovers the initial depth moment.
-/

open Polynomial Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- Polynomial heat varies locally uniformly in complex time. -/
theorem tendstoLocallyUniformly_heatFlow_nhds (p : ℂ[X]) (t : ℂ) :
    TendstoLocallyUniformly (fun s z => (heatFlow s p).eval z)
      (heatFlow t p).eval (𝓝 t) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℂ → K → ℂ := fun s z => (heatFlow s p).eval z
  have hF : Continuous (Function.uncurry F) := by
    have hmap : Continuous (fun z : ℂ × K => (z.1, (z.2 : ℂ))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have h := (continuous_biEval (polynomialHeatFamily p)).comp hmap
    apply h.congr
    intro z
    exact (biEval_eq_eval_biFibre _ _).trans (by rw [biFibre_polynomialHeatFamily]; rfl)
  have hu := Continuous.tendstoUniformly F hF t
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp hu) ε hε] with s hs z hz
  exact hs ⟨z, hz⟩

/-- A continuous nonnegative root weight has a continuous multiplicity-counted
sum along polynomial heat, even at collisions. -/
theorem continuous_polynomial_heat_root_sum {p : ℂ[X]} (hp : p ≠ 0)
    {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ) (hΨ0 : ∀ z, 0 ≤ Ψ z) :
    Continuous (fun t : ℂ => ((heatFlow t p).roots.map Ψ).sum) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hut
  have hconv : TendstoLocallyUniformly (fun n z => (heatFlow (u n) p).eval z)
      (heatFlow t p).eval atTop := by
    intro U hU z
    obtain ⟨V, hV, he⟩ := tendstoLocallyUniformly_heatFlow_nhds p t U hU z
    exact ⟨V, hV, hut.eventually he⟩
  apply tendsto_sum_roots_of_fixed_card (heatFlow_degree_ne_zero hp t).2 hconv _ hΨ hΨ0
  exact Filter.Eventually.of_forall fun n => by
    rw [IsAlgClosed.card_roots_eq_natDegree, IsAlgClosed.card_roots_eq_natDegree,
      (heatFlow_degree_ne_zero hp (u n)).1, (heatFlow_degree_ne_zero hp t).1]

private theorem abs_sum_map_sub_le (S : Multiset ℂ) (F G : ℂ → ℝ) {η : ℝ}
    (h : ∀ z ∈ S, |F z - G z| ≤ η) :
    |(S.map F).sum - (S.map G).sum| ≤ (S.card : ℝ) * η := by
  induction S using Multiset.induction_on with
  | empty => simp only [Multiset.map_zero, Multiset.sum_zero, sub_self, abs_zero,
      Multiset.card_zero, Nat.cast_zero, zero_mul, le_refl]
  | cons z S ih =>
    have hz := h z (Multiset.mem_cons_self z S)
    have hS := ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one]
    calc
      |F z + (S.map F).sum - (G z + (S.map G).sum)| =
          |(F z - G z) + ((S.map F).sum - (S.map G).sum)| := by congr 1; ring
      _ ≤ |F z - G z| + |(S.map F).sum - (S.map G).sum| := abs_add_le _ _
      _ ≤ η + (S.card : ℝ) * η := add_le_add hz hS
      _ = ((S.card : ℝ) + 1) * η := by ring

private theorem continuous_polynomial_elapsedMoment_clamped {p : ℂ[X]}
    (hp : p ≠ 0) {q : ℝ} (hq : 0 ≤ q) :
    Continuous (fun t : ℝ =>
      ((heatFlow (t : ℂ) p).roots.map (fun z => (z.im ^ 2 + 2 * max t 0) ^ q)).sum) := by
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
  let F : ℝ → K → ℝ := fun s z => ((z : ℂ).im ^ 2 + 2 * max s 0) ^ q
  have hF : Continuous (Function.uncurry F) := by
    have hbase : Continuous (fun v : ℝ × K => (v.2 : ℂ).im ^ 2 + 2 * max v.1 0) := by
      fun_prop
    exact hbase.rpow_const (fun _ => Or.inr hq)
  have hu := Continuous.tendstoUniformly F hF t
  let Ψ : ℂ → ℝ := fun z => (z.im ^ 2 + 2 * max t 0) ^ q
  have hΨ : Continuous Ψ := ((continuous_im.pow 2).add continuous_const).rpow_const
    (fun _ => Or.inr hq)
  have hΨ0 (z : ℂ) : 0 ≤ Ψ z := Real.rpow_nonneg
    (add_nonneg (sq_nonneg _) (mul_nonneg zero_le_two (le_max_right _ _))) _
  have hfixed : Continuous (fun s : ℝ => ((heatFlow (s : ℂ) p).roots.map Ψ).sum) :=
    (continuous_polynomial_heat_root_sum hp hΨ hΨ0).comp continuous_ofReal
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
  have hw (z : ℂ) (hz : z ∈ (heatFlow (s : ℂ) p).roots) :
      |(z.im ^ 2 + 2 * max s 0) ^ q - Ψ z| ≤ η := by
    have hzK : z ∈ K := by simpa only [K, mem_closedBall, dist_zero_right] using hR z hz
    have h := hweight ⟨z, hzK⟩
    simpa only [F, Ψ, Real.dist_eq, abs_sub_comm] using h.le
  have hdiff := abs_sum_map_sub_le (heatFlow (s : ℂ) p).roots
    (fun z => (z.im ^ 2 + 2 * max s 0) ^ q) Ψ hw
  rw [IsAlgClosed.card_roots_eq_natDegree, (heatFlow_degree_ne_zero hp (s : ℂ)).1] at hdiff
  have hfirst : dist
      (((heatFlow (s : ℂ) p).roots.map (fun z => (z.im ^ 2 + 2 * max s 0) ^ q)).sum)
      (((heatFlow (s : ℂ) p).roots.map Ψ).sum) ≤ (p.natDegree : ℝ) * η := by
    simpa only [Real.dist_eq] using hdiff
  calc
    _ ≤ dist (((heatFlow (s : ℂ) p).roots.map (fun z => (z.im ^ 2 + 2 * max s 0) ^ q)).sum)
          (((heatFlow (s : ℂ) p).roots.map Ψ).sum) +
        dist (((heatFlow (s : ℂ) p).roots.map Ψ).sum)
          (((heatFlow (t : ℂ) p).roots.map Ψ).sum) := dist_triangle _ _ _
    _ ≤ (p.natDegree : ℝ) * η + dist (((heatFlow (s : ℂ) p).roots.map Ψ).sum)
          (((heatFlow (t : ℂ) p).roots.map Ψ).sum) := add_le_add hfirst le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hηN hclose
    _ = ε := by ring

/-- The elapsed-depth moment with its real-axis baseline subtracted at every root. -/
def polynomialElapsedDepthAction (p : ℂ[X]) (q t : ℝ) : ℝ :=
  ((heatFlow (t : ℂ) p).roots.map
    (fun z => (z.im ^ 2 + 2 * t) ^ q - (2 * t) ^ q)).sum

/-- The corrected polynomial action remains continuous at collisions and at zero time. -/
theorem continuousOn_polynomialElapsedDepthAction {p : ℂ[X]} (hp : p ≠ 0)
    {q : ℝ} (hq : 0 ≤ q) :
    ContinuousOn (polynomialElapsedDepthAction p q) (Ici 0) := by
  have hbase : Continuous (fun t : ℝ => (2 * max t 0) ^ q * (p.natDegree : ℝ)) :=
    (((continuous_const.mul (continuous_id.max continuous_const)).rpow_const
      (fun _ => Or.inr hq)).mul continuous_const)
  have hc := (continuous_polynomial_elapsedMoment_clamped hp hq).sub hbase
  apply hc.continuousOn.congr
  intro t ht
  simp only [Pi.sub_apply, max_eq_left (show 0 ≤ t from ht)]
  unfold polynomialElapsedDepthAction
  rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
    IsAlgClosed.card_roots_eq_natDegree, (heatFlow_degree_ne_zero hp (t : ℂ)).1]
  ring

/-- Positive exponents remove the baseline at zero, leaving the initial depth moment. -/
theorem polynomialElapsedDepthAction_zero (p : ℂ[X]) {q : ℝ} (hq : 0 < q) :
    polynomialElapsedDepthAction p q 0 = (p.roots.map (fun z => (z.im ^ 2) ^ q)).sum := by
  simp only [polynomialElapsedDepthAction, Complex.ofReal_zero, heatFlow_zero_time,
    mul_zero, add_zero, Real.zero_rpow hq.ne', sub_zero]

#print axioms tendstoLocallyUniformly_heatFlow_nhds
#print axioms continuous_polynomial_heat_root_sum
#print axioms continuousOn_polynomialElapsedDepthAction
#print axioms polynomialElapsedDepthAction_zero

end
end GaloisForLFunctions.ArithmeticElectrostatics
