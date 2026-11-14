import GaloisForLFunctions.HilbertMetric.NonoverlappingCoverObstructions
import GaloisForLFunctions.HilbertMetric.SeparatedConfigurations
import GaloisForLFunctions.Bottcher.DiskAlgebraicContinuation

/-!
# A finite planar obstruction without a configuration search

If separated unit disks covered the plane, approaching every boundary
point of one disk from outside would force a tangent disk in that direction.
Its centre is uniquely determined by the parallelogram identity. This
would put an infinite circle of centres in a bounded separated set.

Compactness then yields a finite noncoverable configuration. Together with
stable finite obstructions, this supplies the existence input for the
small-spacing transfer of Proposition 9.3 of Kittipassorn--Phetmak--Sriamorn.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric

open Metric Set Filter Topology

/-- Equality in the two unit-radius constraints forces antipodal tangency. -/
private theorem tangency_eq {u w : ℂ} (hu : ‖u‖ = 1)
    (hnear : ‖w - u‖ ≤ 1) (hfar : 2 ≤ ‖w‖) : w = u + u := by
  have hn : Complex.normSq (w - u) ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have h := mul_le_mul hnear hnear (norm_nonneg _) zero_le_one
    nlinarith only [h]
  have hf : 4 ≤ Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]
    have h := mul_le_mul hfar hfar (by positivity : (0 : ℝ) ≤ 2) (norm_nonneg w)
    nlinarith only [h]
  have hu' : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu]
    ring
  have hid : Complex.normSq (w - (u + u)) =
      2 * Complex.normSq (w - u) + 2 * Complex.normSq u - Complex.normSq w := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im]
    ring
  have hz : Complex.normSq (w - (u + u)) = 0 := by
    apply le_antisymm
    · linarith only [hid, hn, hf, hu']
    · rw [Complex.normSq_eq_norm_sq]
      exact sq_nonneg _
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)

/-- Covering the plane forces a tangent disk at every boundary direction of each disk. -/
private theorem tangent_centre_mem {C : Set ℂ} (hC : IsClosed C)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 ≤ dist x y)
    (hcover : ∀ z : ℂ, ∃ c ∈ C, dist z c ≤ 1)
    {c₀ : ℂ} (hc₀ : c₀ ∈ C) {u : ℂ} (hu : ‖u‖ = 1) : c₀ + (u + u) ∈ C := by
  let t : ℕ → ℝ := fun n => 1 + 1 / (n + 1 : ℝ)
  let p : ℕ → ℂ := fun n => c₀ + (t n : ℂ) * u
  have htpos (n : ℕ) : 1 < t n := by
    have h : 0 < 1 / (n + 1 : ℝ) := by positivity
    dsimp [t]
    linarith only [h]
  have htbound (n : ℕ) : t n ≤ 2 := by
    have hd : 1 / (n + 1 : ℝ) ≤ 1 :=
      (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr (by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith only [hn])
    dsimp [t]
    linarith only [hd]
  have hpdist (n : ℕ) : dist (p n) c₀ = t n := by
    simp only [p, dist_eq_norm, add_sub_cancel_left, norm_mul, hu, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zero_lt_one.trans (htpos n)).le]
  choose c hmem hcov using fun n => hcover (p n)
  have hfar (n : ℕ) : 2 ≤ dist (c n) c₀ := by
    apply hsep _ (hmem n) _ hc₀
    intro heq
    have hn := hcov n
    rw [heq, hpdist] at hn
    exact (not_le_of_gt (htpos n)) hn
  have hbounded (n : ℕ) : c n ∈ closedBall c₀ 3 := by
    have ht := dist_triangle (c n) (p n) c₀
    rw [dist_comm (c n) (p n), hpdist] at ht
    change dist (c n) c₀ ≤ 3
    linarith only [ht, hcov n, htbound n]
  obtain ⟨v, _, φ, hφ, hv⟩ := (isCompact_closedBall c₀ 3).tendsto_subseq hbounded
  have hvC : v ∈ C := hC.mem_of_tendsto hv (Eventually.of_forall fun n => hmem (φ n))
  have htlim : Tendsto t atTop (𝓝 (1 : ℝ)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [add_zero] using h
  have hplim : Tendsto p atTop (𝓝 (c₀ + u)) := by
    have h := (((Complex.continuous_ofReal.tendsto 1).comp htlim).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u))).const_add c₀
    simpa only [p, Function.comp_apply, Complex.ofReal_one, one_mul] using h
  have hvnear : dist (c₀ + u) v ≤ 1 :=
    le_of_tendsto ((hplim.comp hφ.tendsto_atTop).dist hv)
      (Eventually.of_forall fun n => hcov (φ n))
  have hvfar : 2 ≤ dist v c₀ :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).mem_of_tendsto hv
      (Eventually.of_forall fun n => hfar (φ n))
  have hnorm : ‖(v - c₀) - u‖ ≤ 1 := by
    rw [sub_sub, ← dist_eq_norm, dist_comm]
    exact hvnear
  have heq := tangency_eq hu hnorm (by simpa only [dist_eq_norm] using hvfar)
  have hv_eq : v = c₀ + (u + u) := by
    linear_combination heq
  rwa [hv_eq] at hvC

/-- The complex plane cannot be covered by nonoverlapping closed unit disks. -/
theorem not_ballCoverable_complex_plane : ¬ BallCoverable 1 (fun z : ℂ => z) := by
  intro h
  obtain ⟨C, hsep, hcover⟩ := (ballCoverable_iff_centres 1 (fun z : ℂ => z)).mp h
  have hsep' : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 ≤ dist x y := by
    simpa only [NNReal.coe_one, mul_one] using hsep
  have hcover' : ∀ z : ℂ, ∃ c ∈ C, dist z c ≤ 1 := by
    simpa only [NNReal.coe_one] using hcover
  obtain ⟨c₀, hc₀, _⟩ := hcover' 0
  have hC := isClosed_of_dist_separated (by positivity : (0 : ℝ) < 2) hsep'
  let S : Set ℂ := C ∩ closedBall c₀ 2
  have hS : S.Finite := finite_of_dist_separated_of_subset_compact
    (by positivity : (0 : ℝ) < 2)
    (fun x hx y hy hxy => hsep' x hx.1 y hy.1 hxy)
    (isCompact_closedBall c₀ 2) (fun _ hx => hx.2)
  let f : ℂ → ℂ := fun u => c₀ + (u + u)
  have hf : Function.Injective f := by
    intro u v huv
    dsimp [f] at huv
    linear_combination (1 / 2 : ℂ) * huv
  have hsphere : sphere (0 : ℂ) 1 ⊆ f ⁻¹' S := by
    intro u hu
    have hunorm : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu
    refine ⟨tangent_centre_mem hC hsep' hcover' hc₀ hunorm, ?_⟩
    change dist (c₀ + (u + u)) c₀ ≤ 2
    rw [dist_eq_norm, add_sub_cancel_left]
    calc
      ‖u + u‖ ≤ ‖u‖ + ‖u‖ := norm_add_le _ _
      _ = 2 := by rw [hunorm]; ring
  exact Bottcher.infinite_sphere_one ((hS.preimage hf.injOn).subset hsphere)

/-- A finite planar obstruction exists without enumerating configurations. -/
theorem exists_noncoverable_finset_complex :
    ∃ s : Finset ℂ, ¬ BallCoverable 1 (fun z : s => (z : ℂ)) :=
  (not_ballCoverable_iff_finset 1 (fun z : ℂ => z)).mp not_ballCoverable_complex_plane

end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.not_ballCoverable_complex_plane
#print axioms GaloisForLFunctions.HilbertMetric.exists_noncoverable_finset_complex
