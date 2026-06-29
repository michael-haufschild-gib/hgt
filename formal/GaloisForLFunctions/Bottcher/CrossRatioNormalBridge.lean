/-
# Cross-ratio algebra bridge for the Montel lane

The three-value Montel route normalizes an iterate family by cross-ratios.  The
lemmas here package the algebraic pushback: once a cross-ratio family is known
to be the genuine cross-ratio of the quadratic iterates on a patch, the inverse
Möbius transform recovers the original iterate family pointwise on that patch.
-/
import GaloisForLFunctions.Bottcher.PeriodicPoints
import GaloisForLFunctions.Bottcher.MontelIterates

open Complex Metric Set Filter Topology

namespace Bottcher

noncomputable section

/-- Inverse Möbius transform solving the cross-ratio for the target value. -/
def crossRatioInverse (α β z R : ℂ) : ℂ :=
  (R * β * (z - α) - α * (z - β)) / (R * (z - α) - (z - β))

/-- The finite affine chart of the Riemann sphere, inverse to stereographic projection away from the
north pole. -/
def stereoFiniteChart (v : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (((v.ofLp (0 : Fin 3) : ℝ) : ℂ) + ((v.ofLp (1 : Fin 3) : ℝ) : ℂ) * Complex.I) /
    (((1 : ℝ) - v.ofLp (2 : Fin 3) : ℝ) : ℂ)

/-- The inverse affine chart near the north pole. On `stereo z`, it returns `z⁻¹`, so it turns
spherical convergence to the point at infinity into finite convergence in the inverse coordinate. -/
def stereoInvChart (v : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (((v.ofLp (0 : Fin 3) : ℝ) : ℂ) - ((v.ofLp (1 : Fin 3) : ℝ) : ℂ) * Complex.I) /
    (((1 : ℝ) + v.ofLp (2 : Fin 3) : ℝ) : ℂ)

/-- The finite chart recovers a complex number from its stereographic image. -/
theorem stereoFiniteChart_stereo (z : ℂ) :
    stereoFiniteChart (stereo z) = z := by
  let A : ℝ := 2 / (1 + ‖z‖ ^ 2)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hAne : (A : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hApos)
  have hx : (stereo z).ofLp (0 : Fin 3) = A * z.re := by
    dsimp [A]
    simp [stereo]
    ring
  have hy : (stereo z).ofLp (1 : Fin 3) = A * z.im := by
    dsimp [A]
    simp [stereo]
    ring
  have hdenR : (1 : ℝ) - (stereo z).ofLp (2 : Fin 3) = A := by
    dsimp [A]
    simp [stereo]
    field_simp [show (1 : ℝ) + ‖z‖ ^ 2 ≠ 0 by positivity]
    ring
  have hden : (((1 : ℝ) - (stereo z).ofLp (2 : Fin 3) : ℝ) : ℂ) = (A : ℂ) := by
    exact_mod_cast hdenR
  have hnum : (((stereo z).ofLp (0 : Fin 3) : ℝ) : ℂ) +
      ((stereo z).ofLp (1 : Fin 3) : ℝ) * Complex.I = (A : ℂ) * z := by
    rw [hx, hy]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  unfold stereoFiniteChart
  rw [hden, hnum]
  exact mul_div_cancel_left₀ z hAne

/-- The inverse chart recovers `z⁻¹` from the stereographic image of a nonzero complex number. -/
theorem stereoInvChart_stereo {z : ℂ} (hz : z ≠ 0) :
    stereoInvChart (stereo z) = z⁻¹ := by
  let A : ℝ := 2 / (1 + ‖z‖ ^ 2)
  let B : ℝ := A * ‖z‖ ^ 2
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hAne : (A : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hApos)
  have hBpos : 0 < B := by
    dsimp [B, A]
    have hzpos : 0 < ‖z‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hz)
    positivity
  have hx : (stereo z).ofLp (0 : Fin 3) = A * z.re := by
    dsimp [A]
    simp [stereo]
    ring
  have hy : (stereo z).ofLp (1 : Fin 3) = A * z.im := by
    dsimp [A]
    simp [stereo]
    ring
  have hdenR : (1 : ℝ) + (stereo z).ofLp (2 : Fin 3) = B := by
    dsimp [B, A]
    simp [stereo]
    field_simp [show (1 : ℝ) + ‖z‖ ^ 2 ≠ 0 by positivity]
    ring
  have hden : (((1 : ℝ) + (stereo z).ofLp (2 : Fin 3) : ℝ) : ℂ) = (B : ℂ) := by
    exact_mod_cast hdenR
  have hnum : (((stereo z).ofLp (0 : Fin 3) : ℝ) : ℂ) -
      ((stereo z).ofLp (1 : Fin 3) : ℝ) * Complex.I = (A : ℂ) * star z := by
    rw [hx, hy]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hB : (B : ℂ) = (A : ℂ) * (z * star z) := by
    dsimp [B]
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq]
  unfold stereoInvChart
  rw [hden, hnum, hB]
  field_simp [hAne, hz, (star_ne_zero.mpr hz)]

/-- The third stereographic coordinate is always at most the north-pole coordinate. -/
theorem stereo_third_le_one (z : ℂ) : (stereo z).ofLp (2 : Fin 3) ≤ 1 := by
  simp [stereo]
  have hdenpos : 0 < (1 : ℝ) + ‖z‖ ^ 2 := by positivity
  rw [div_le_iff₀ hdenpos]
  ring_nf
  nlinarith [sq_nonneg ‖z‖]

/-- The third stereographic coordinate is always at least the south-pole coordinate. -/
theorem neg_one_le_stereo_third (z : ℂ) : -1 ≤ (stereo z).ofLp (2 : Fin 3) := by
  simp [stereo]
  have hdenpos : 0 < (1 : ℝ) + ‖z‖ ^ 2 := by positivity
  rw [le_div_iff₀ hdenpos]
  ring_nf
  nlinarith [sq_nonneg ‖z‖]

/-- The finite stereographic chart is continuous away from the north pole. -/
theorem stereoFiniteChart_continuousAt {v : EuclideanSpace ℝ (Fin 3)}
    (h : v.ofLp (2 : Fin 3) ≠ 1) : ContinuousAt stereoFiniteChart v := by
  have h0 : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp (0 : Fin 3)) v :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).continuousAt
  have h1 : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp (1 : Fin 3)) v :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)).continuousAt
  have h2 : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp (2 : Fin 3)) v :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).continuousAt
  have h0c : ContinuousAt
      (fun v : EuclideanSpace ℝ (Fin 3) => ((v.ofLp (0 : Fin 3) : ℝ) : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp h0
  have h1c : ContinuousAt
      (fun v : EuclideanSpace ℝ (Fin 3) => ((v.ofLp (1 : Fin 3) : ℝ) : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp h1
  have hn : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) =>
      (((v.ofLp (0 : Fin 3) : ℝ) : ℂ) + ((v.ofLp (1 : Fin 3) : ℝ) : ℂ) * Complex.I)) v :=
    h0c.add (h1c.mul continuousAt_const)
  have hd : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) =>
      (((1 : ℝ) - v.ofLp (2 : Fin 3) : ℝ) : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.sub h2)
  have hdne : (((1 : ℝ) - v.ofLp (2 : Fin 3) : ℝ) : ℂ) ≠ 0 := by
    have hreal : (1 : ℝ) - v.ofLp (2 : Fin 3) ≠ 0 := by
      intro hzero
      apply h
      linarith
    exact_mod_cast hreal
  unfold stereoFiniteChart
  exact hn.div hd hdne

/-- The inverse stereographic chart is continuous away from the south pole. -/
theorem stereoInvChart_continuousAt {v : EuclideanSpace ℝ (Fin 3)}
    (h : v.ofLp (2 : Fin 3) ≠ -1) : ContinuousAt stereoInvChart v := by
  have h0 : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp (0 : Fin 3)) v :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)).continuousAt
  have h1 : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp (1 : Fin 3)) v :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)).continuousAt
  have h2 : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp (2 : Fin 3)) v :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).continuousAt
  have h0c : ContinuousAt
      (fun v : EuclideanSpace ℝ (Fin 3) => ((v.ofLp (0 : Fin 3) : ℝ) : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp h0
  have h1c : ContinuousAt
      (fun v : EuclideanSpace ℝ (Fin 3) => ((v.ofLp (1 : Fin 3) : ℝ) : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp h1
  have hn : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) =>
      (((v.ofLp (0 : Fin 3) : ℝ) : ℂ) - ((v.ofLp (1 : Fin 3) : ℝ) : ℂ) * Complex.I)) v :=
    h0c.sub (h1c.mul continuousAt_const)
  have hd : ContinuousAt (fun v : EuclideanSpace ℝ (Fin 3) =>
      (((1 : ℝ) + v.ofLp (2 : Fin 3) : ℝ) : ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.add h2)
  have hdne : (((1 : ℝ) + v.ofLp (2 : Fin 3) : ℝ) : ℂ) ≠ 0 := by
    have hreal : (1 : ℝ) + v.ofLp (2 : Fin 3) ≠ 0 := by
      intro hzero
      apply h
      linarith
    exact_mod_cast hreal
  unfold stereoInvChart
  exact hn.div hd hdne

/-- Set-level continuity of the finite stereographic chart away from the north pole. -/
theorem stereoFiniteChart_continuousOn {S : Set (EuclideanSpace ℝ (Fin 3))}
    (h : ∀ v ∈ S, v.ofLp (2 : Fin 3) ≠ 1) :
    ContinuousOn stereoFiniteChart S := by
  intro v hv
  exact (stereoFiniteChart_continuousAt (h v hv)).continuousWithinAt

/-- Set-level continuity of the inverse stereographic chart away from the south pole. -/
theorem stereoInvChart_continuousOn {S : Set (EuclideanSpace ℝ (Fin 3))}
    (h : ∀ v ∈ S, v.ofLp (2 : Fin 3) ≠ -1) :
    ContinuousOn stereoInvChart S := by
  intro v hv
  exact (stereoInvChart_continuousAt (h v hv)).continuousWithinAt

/-- A coordinate difference is bounded by Euclidean distance. -/
theorem stereo_coord_abs_sub_le_dist (x y : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    |x.ofLp i - y.ofLp i| ≤ dist x y := by
  rw [dist_eq_norm]
  have h := PiLp.norm_apply_le (x - y) i
  simpa using h

/-- If a spherical limit stays uniformly away from the north pole, spherical uniform convergence of
`stereo (R n z)` upgrades to ordinary uniform convergence of `R n z` in the finite chart. -/
theorem tendstoUniformlyOn_of_stereo_tendstoUniformlyOn_finiteChart
    {K : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {G : ℂ → EuclideanSpace ℝ (Fin 3)} {B : ℝ}
    (hGthird : ∀ z ∈ K, (G z).ofLp (2 : Fin 3) ≤ B)
    (hB : B < 1)
    (hconv : TendstoUniformlyOn (fun n z => stereo (Rseq n z)) G atTop K) :
    TendstoUniformlyOn Rseq (fun z => stereoFiniteChart (G z)) atTop K := by
  let C : ℝ := (B + 1) / 2
  have hBC : B < C := by
    dsimp [C]
    linarith
  have hC1 : C < 1 := by
    dsimp [C]
    linarith
  let S : Set (EuclideanSpace ℝ (Fin 3)) :=
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 ∩ {v | v.ofLp (2 : Fin 3) ≤ C}
  have hclosedCoord : IsClosed ({v : EuclideanSpace ℝ (Fin 3) | v.ofLp (2 : Fin 3) ≤ C}) :=
    isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)) continuous_const
  have hScompact : IsCompact S :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2).inter_right hclosedCoord
  have hScont : ContinuousOn stereoFiniteChart S := by
    refine stereoFiniteChart_continuousOn ?_
    intro v hv hEq
    have hvle : v.ofLp (2 : Fin 3) ≤ C := hv.2
    linarith
  have hUC : UniformContinuousOn stereoFiniteChart S :=
    hScompact.uniformContinuousOn_of_continuous hScont
  have hlim_norm : ∀ z ∈ K, ‖G z‖ ≤ 1 := by
    intro z hz
    have hpt : Tendsto (fun n => stereo (Rseq n z)) atTop (𝓝 (G z)) := hconv.tendsto_at hz
    have hnorm : Tendsto (fun n => ‖stereo (Rseq n z)‖) atTop (𝓝 ‖G z‖) := hpt.norm
    exact le_of_tendsto' hnorm (fun n => by rw [norm_stereo_eq_one])
  have hlim_mem : ∀ z ∈ K, G z ∈ S := by
    intro z hz
    refine ⟨?_, (hGthird z hz).trans (le_of_lt hBC)⟩
    rw [mem_closedBall, dist_zero_right]
    linarith [hlim_norm z hz]
  have hseq_mem : ∀ᶠ n in atTop, ∀ z ∈ K, stereo (Rseq n z) ∈ S := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv
    filter_upwards [hconv (C - B) (by linarith)] with n hn
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_stereo_eq_one]
      norm_num
    · have hdist : dist (stereo (Rseq n z)) (G z) < C - B := by
        simpa [dist_comm] using hn z hz
      have hcoord := stereo_coord_abs_sub_le_dist (stereo (Rseq n z)) (G z) (2 : Fin 3)
      have hdiff : (stereo (Rseq n z)).ofLp (2 : Fin 3) - (G z).ofLp (2 : Fin 3) <
          C - B := by
        have habs_nonneg : (stereo (Rseq n z)).ofLp (2 : Fin 3) - (G z).ofLp (2 : Fin 3) ≤
            |(stereo (Rseq n z)).ofLp (2 : Fin 3) - (G z).ofLp (2 : Fin 3)| :=
          le_abs_self _
        linarith
      have hle1 : (stereo (Rseq n z)).ofLp (2 : Fin 3) ≤
          (G z).ofLp (2 : Fin 3) + (C - B) := by
        linarith [hdiff]
      have hle2 : (G z).ofLp (2 : Fin 3) + (C - B) ≤ C := by
        linarith [hGthird z hz]
      exact hle1.trans hle2
  have hcomp : TendstoUniformlyOn
      (fun n z => stereoFiniteChart (stereo (Rseq n z)))
      (fun z => stereoFiniteChart (G z)) atTop K :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually hseq_mem hlim_mem hUC hconv
  exact hcomp.congr (by
    filter_upwards with n z _hz
    exact stereoFiniteChart_stereo (Rseq n z))

/-- If a spherical limit stays uniformly away from the south pole, spherical uniform convergence of
`stereo (R n z)` upgrades to uniform convergence of the inverse values `(R n z)⁻¹`. -/
theorem tendstoUniformlyOn_inv_of_stereo_tendstoUniformlyOn_invChart
    {K : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {G : ℂ → EuclideanSpace ℝ (Fin 3)} {A : ℝ}
    (hGthird : ∀ z ∈ K, A ≤ (G z).ofLp (2 : Fin 3))
    (hA : -1 < A)
    (hRne : ∀ n z, z ∈ K → Rseq n z ≠ 0)
    (hconv : TendstoUniformlyOn (fun n z => stereo (Rseq n z)) G atTop K) :
    TendstoUniformlyOn (fun n z => (Rseq n z)⁻¹) (fun z => stereoInvChart (G z)) atTop K := by
  let C : ℝ := (A - 1) / 2
  have hneg1C : -1 < C := by
    dsimp [C]
    linarith
  have hCA : C < A := by
    dsimp [C]
    linarith
  let S : Set (EuclideanSpace ℝ (Fin 3)) :=
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 ∩ {v | C ≤ v.ofLp (2 : Fin 3)}
  have hclosedCoord : IsClosed ({v : EuclideanSpace ℝ (Fin 3) | C ≤ v.ofLp (2 : Fin 3)}) :=
    isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3))
  have hScompact : IsCompact S :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2).inter_right hclosedCoord
  have hScont : ContinuousOn stereoInvChart S := by
    refine stereoInvChart_continuousOn ?_
    intro v hv hEq
    have hvge : C ≤ v.ofLp (2 : Fin 3) := hv.2
    linarith
  have hUC : UniformContinuousOn stereoInvChart S :=
    hScompact.uniformContinuousOn_of_continuous hScont
  have hlim_norm : ∀ z ∈ K, ‖G z‖ ≤ 1 := by
    intro z hz
    have hpt : Tendsto (fun n => stereo (Rseq n z)) atTop (𝓝 (G z)) := hconv.tendsto_at hz
    have hnorm : Tendsto (fun n => ‖stereo (Rseq n z)‖) atTop (𝓝 ‖G z‖) := hpt.norm
    exact le_of_tendsto' hnorm (fun n => by rw [norm_stereo_eq_one])
  have hlim_mem : ∀ z ∈ K, G z ∈ S := by
    intro z hz
    refine ⟨?_, (le_of_lt hCA).trans (hGthird z hz)⟩
    rw [mem_closedBall, dist_zero_right]
    linarith [hlim_norm z hz]
  have hseq_mem : ∀ᶠ n in atTop, ∀ z ∈ K, stereo (Rseq n z) ∈ S := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv
    filter_upwards [hconv (A - C) (by linarith)] with n hn
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_stereo_eq_one]
      norm_num
    · have hdist : dist (stereo (Rseq n z)) (G z) < A - C := by
        simpa [dist_comm] using hn z hz
      have hcoord := stereo_coord_abs_sub_le_dist (stereo (Rseq n z)) (G z) (2 : Fin 3)
      have hdiff : (G z).ofLp (2 : Fin 3) - (stereo (Rseq n z)).ofLp (2 : Fin 3) <
          A - C := by
        have habs_nonneg : (G z).ofLp (2 : Fin 3) - (stereo (Rseq n z)).ofLp (2 : Fin 3) ≤
            |(stereo (Rseq n z)).ofLp (2 : Fin 3) - (G z).ofLp (2 : Fin 3)| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        linarith
      have hle1 : (G z).ofLp (2 : Fin 3) - (A - C) ≤
          (stereo (Rseq n z)).ofLp (2 : Fin 3) := by
        linarith [hdiff]
      have hle2 : C ≤ (G z).ofLp (2 : Fin 3) - (A - C) := by
        linarith [hGthird z hz]
      exact hle2.trans hle1
  have hcomp : TendstoUniformlyOn
      (fun n z => stereoInvChart (stereo (Rseq n z)))
      (fun z => stereoInvChart (G z)) atTop K :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually hseq_mem hlim_mem hUC hconv
  exact hcomp.congr (by
    filter_upwards with n z hz
    exact stereoInvChart_stereo (hRne n z hz))

/-- Continuity of the finite-chart pullback of a spherical limit that avoids the north pole. -/
theorem continuousOn_stereoFiniteChart_comp {K : Set ℂ} {G : ℂ → EuclideanSpace ℝ (Fin 3)}
    (hGcont : ContinuousOn G K)
    (hGnorth : ∀ z ∈ K, (G z).ofLp (2 : Fin 3) ≠ 1) :
    ContinuousOn (fun z => stereoFiniteChart (G z)) K := by
  intro z hz
  exact (stereoFiniteChart_continuousAt (hGnorth z hz)).comp_continuousWithinAt (hGcont z hz)

/-- Continuity of the inverse-chart pullback of a spherical limit that avoids the south pole. -/
theorem continuousOn_stereoInvChart_comp {K : Set ℂ} {G : ℂ → EuclideanSpace ℝ (Fin 3)}
    (hGcont : ContinuousOn G K)
    (hGsouth : ∀ z ∈ K, (G z).ofLp (2 : Fin 3) ≠ -1) :
    ContinuousOn (fun z => stereoInvChart (G z)) K := by
  intro z hz
  exact (stereoInvChart_continuousAt (hGsouth z hz)).comp_continuousWithinAt (hGcont z hz)

/-- If a continuous spherical limit has third coordinate below `B` at the center, then on some
smaller closed ball the third coordinate is bounded by `B`. -/
theorem exists_closedBall_upper_bound_of_continuousOn {z₀ : ℂ} {ρ B : ℝ}
    {G : ℂ → EuclideanSpace ℝ (Fin 3)}
    (hρ : 0 < ρ)
    (hGcont : ContinuousOn G (closedBall z₀ ρ))
    (hB : (G z₀).ofLp (2 : Fin 3) < B) :
    ∃ r : ℝ, 0 < r ∧ closedBall z₀ r ⊆ closedBall z₀ ρ ∧
      ∀ z ∈ closedBall z₀ r, (G z).ofLp (2 : Fin 3) ≤ B := by
  have hzmem : z₀ ∈ closedBall z₀ ρ := by
    rw [mem_closedBall, dist_self]
    exact le_of_lt hρ
  have hcoord_cont : ContinuousWithinAt (fun z => (G z).ofLp (2 : Fin 3))
      (closedBall z₀ ρ) z₀ := by
    exact ContinuousAt.comp_continuousWithinAt
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).continuousAt)
      (hGcont z₀ hzmem)
  rw [Metric.continuousWithinAt_iff] at hcoord_cont
  have hε : 0 < B - (G z₀).ofLp (2 : Fin 3) := by
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := hcoord_cont (B - (G z₀).ofLp (2 : Fin 3)) hε
  let r : ℝ := min ρ δ / 2
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  refine ⟨r, hrpos, ?_, ?_⟩
  · intro z hz
    rw [mem_closedBall] at hz ⊢
    have hrleρ : r ≤ ρ := by
      dsimp [r]
      have hmin : min ρ δ ≤ ρ := min_le_left _ _
      linarith
    exact hz.trans hrleρ
  · intro z hz
    have hzK : z ∈ closedBall z₀ ρ := by
      rw [mem_closedBall] at hz ⊢
      have hrleρ : r ≤ ρ := by
        dsimp [r]
        have hmin : min ρ δ ≤ ρ := min_le_left _ _
        linarith
      exact hz.trans hrleρ
    have hdistδ : dist z z₀ < δ := by
      rw [mem_closedBall] at hz
      have hrltδ : r < δ := by
        dsimp [r]
        have hmin : min ρ δ ≤ δ := min_le_right _ _
        linarith
      exact lt_of_le_of_lt hz hrltδ
    have hdist : dist ((G z).ofLp (2 : Fin 3)) ((G z₀).ofLp (2 : Fin 3)) <
        B - (G z₀).ofLp (2 : Fin 3) :=
      hδ (x := z) hzK hdistδ
    rw [Real.dist_eq] at hdist
    have hle : (G z).ofLp (2 : Fin 3) - (G z₀).ofLp (2 : Fin 3) ≤
        |(G z).ofLp (2 : Fin 3) - (G z₀).ofLp (2 : Fin 3)| :=
      le_abs_self _
    linarith

/-- If a continuous spherical limit has third coordinate above `A` at the center, then on some
smaller closed ball the third coordinate is bounded below by `A`. -/
theorem exists_closedBall_lower_bound_of_continuousOn {z₀ : ℂ} {ρ A : ℝ}
    {G : ℂ → EuclideanSpace ℝ (Fin 3)}
    (hρ : 0 < ρ)
    (hGcont : ContinuousOn G (closedBall z₀ ρ))
    (hA : A < (G z₀).ofLp (2 : Fin 3)) :
    ∃ r : ℝ, 0 < r ∧ closedBall z₀ r ⊆ closedBall z₀ ρ ∧
      ∀ z ∈ closedBall z₀ r, A ≤ (G z).ofLp (2 : Fin 3) := by
  have hzmem : z₀ ∈ closedBall z₀ ρ := by
    rw [mem_closedBall, dist_self]
    exact le_of_lt hρ
  have hcoord_cont : ContinuousWithinAt (fun z => (G z).ofLp (2 : Fin 3))
      (closedBall z₀ ρ) z₀ := by
    exact ContinuousAt.comp_continuousWithinAt
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).continuousAt)
      (hGcont z₀ hzmem)
  rw [Metric.continuousWithinAt_iff] at hcoord_cont
  have hε : 0 < (G z₀).ofLp (2 : Fin 3) - A := by
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := hcoord_cont ((G z₀).ofLp (2 : Fin 3) - A) hε
  let r : ℝ := min ρ δ / 2
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  refine ⟨r, hrpos, ?_, ?_⟩
  · intro z hz
    rw [mem_closedBall] at hz ⊢
    have hrleρ : r ≤ ρ := by
      dsimp [r]
      have hmin : min ρ δ ≤ ρ := min_le_left _ _
      linarith
    exact hz.trans hrleρ
  · intro z hz
    have hzK : z ∈ closedBall z₀ ρ := by
      rw [mem_closedBall] at hz ⊢
      have hrleρ : r ≤ ρ := by
        dsimp [r]
        have hmin : min ρ δ ≤ ρ := min_le_left _ _
        linarith
      exact hz.trans hrleρ
    have hdistδ : dist z z₀ < δ := by
      rw [mem_closedBall] at hz
      have hrltδ : r < δ := by
        dsimp [r]
        have hmin : min ρ δ ≤ δ := min_le_right _ _
        linarith
      exact lt_of_le_of_lt hz hrltδ
    have hdist : dist ((G z).ofLp (2 : Fin 3)) ((G z₀).ofLp (2 : Fin 3)) <
        (G z₀).ofLp (2 : Fin 3) - A :=
      hδ (x := z) hzK hdistδ
    rw [Real.dist_eq] at hdist
    have hle : (G z₀).ofLp (2 : Fin 3) - (G z).ofLp (2 : Fin 3) ≤
        |(G z).ofLp (2 : Fin 3) - (G z₀).ofLp (2 : Fin 3)| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith

/-- Homogeneous stereographic image of a quotient `N / D`.

Unlike `stereo (N / D)` as a `ℂ`-valued quotient, this formula stays meaningful at `D = 0`: it is the
continuous projective-sphere value of the ratio, provided `(N, D) ≠ (0, 0)`. -/
def homogeneousRatioStereo (N D : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  let S : ℝ := Complex.normSq N + Complex.normSq D
  !₂[2 * (N * star D).re / S, 2 * (N * star D).im / S,
    (Complex.normSq N - Complex.normSq D) / S]

/-- The homogeneous quotient agrees with ordinary stereographic projection away from the pole. -/
theorem homogeneousRatioStereo_eq_stereo_div {N D : ℂ} (hD : D ≠ 0) :
    homogeneousRatioStereo N D = stereo (N / D) := by
  ext i
  fin_cases i
  · simp [homogeneousRatioStereo, stereo]
    rw [Complex.div_re]
    simp_rw [Complex.normSq_eq_norm_sq]
    field_simp [hD]
    ring_nf
  · simp [homogeneousRatioStereo, stereo]
    rw [Complex.div_im]
    simp_rw [Complex.normSq_eq_norm_sq]
    field_simp [hD]
    ring_nf
  · simp [homogeneousRatioStereo, stereo]
    simp_rw [Complex.normSq_eq_norm_sq]
    field_simp [hD]
    ring_nf

/-- The homogeneous quotient map is continuous at every nonzero homogeneous coordinate pair. -/
theorem homogeneousRatioStereo_continuousAt {N D : ℂ} (hND : N ≠ 0 ∨ D ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => homogeneousRatioStereo p.1 p.2) (N, D) := by
  have hS : Complex.normSq N + Complex.normSq D ≠ 0 := by
    intro hS0
    have hN0 : Complex.normSq N = 0 := by
      have hnnonneg := Complex.normSq_nonneg N
      have hdnonneg := Complex.normSq_nonneg D
      nlinarith
    have hD0 : Complex.normSq D = 0 := by
      have hnnonneg := Complex.normSq_nonneg N
      have hdnonneg := Complex.normSq_nonneg D
      nlinarith
    rcases hND with hN | hD
    · exact hN (Complex.normSq_eq_zero.mp hN0)
    · exact hD (Complex.normSq_eq_zero.mp hD0)
  unfold homogeneousRatioStereo
  fun_prop

/-- Homogeneous quotient coordinates are invariant under a nonzero common scalar. -/
theorem homogeneousRatioStereo_smul {a N D : ℂ} (ha : a ≠ 0) :
    homogeneousRatioStereo (a * N) (a * D) = homogeneousRatioStereo N D := by
  by_cases hS : Complex.normSq N + Complex.normSq D = 0
  · have hN0 : Complex.normSq N = 0 := by
      have hn := Complex.normSq_nonneg N
      have hd := Complex.normSq_nonneg D
      nlinarith
    have hD0 : Complex.normSq D = 0 := by
      have hn := Complex.normSq_nonneg N
      have hd := Complex.normSq_nonneg D
      nlinarith
    have hzN : N = 0 := Complex.normSq_eq_zero.mp hN0
    have hzD : D = 0 := Complex.normSq_eq_zero.mp hD0
    simp [hzN, hzD]
  have haS : Complex.normSq a ≠ 0 := mt Complex.normSq_eq_zero.mp ha
  ext i
  fin_cases i
  · simp [homogeneousRatioStereo, Complex.normSq_mul]
    field_simp [haS, hS]
    rw [Complex.normSq_apply]
    ring
  · simp [homogeneousRatioStereo, Complex.normSq_mul]
    field_simp [haS, hS]
    rw [Complex.normSq_apply]
    ring
  · simp [homogeneousRatioStereo, Complex.normSq_mul]
    field_simp [haS, hS]

/-- Homogeneous spherical inverse of the cross-ratio transform. This is the correct target for
spherical normality: it remains continuous through the inverse-Möbius pole. -/
def crossRatioInverseSphere (α β z R : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  homogeneousRatioStereo (R * β * (z - α) - α * (z - β)) (R * (z - α) - (z - β))

/-- Homogeneous spherical inverse written in the coordinate `T = R⁻¹`; this is the chart used when
cross-ratio values tend to infinity. -/
def crossRatioInverseSphereInv (α β z T : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  homogeneousRatioStereo (β * (z - α) - T * α * (z - β)) ((z - α) - T * (z - β))

/-- Away from the inverse-Möbius pole, the homogeneous spherical inverse is just
`stereo (crossRatioInverse ...)`. -/
theorem crossRatioInverseSphere_eq_stereo {α β z R : ℂ}
    (hden : R * (z - α) - (z - β) ≠ 0) :
    crossRatioInverseSphere α β z R = stereo (crossRatioInverse α β z R) := by
  exact homogeneousRatioStereo_eq_stereo_div hden

/-- The homogeneous inverse-cross-ratio coordinates are never simultaneously zero when the anchors are
distinct and the source point is not `β`. This is the projective nondegeneracy behind the spherical
inverse bridge. -/
theorem crossRatioInverseSphere_num_den_not_both_zero {α β z R : ℂ}
    (hαβ : α ≠ β) (hzβ : z ≠ β) :
    R * β * (z - α) - α * (z - β) ≠ 0 ∨ R * (z - α) - (z - β) ≠ 0 := by
  by_contra h
  have hN : R * β * (z - α) - α * (z - β) = 0 := by
    by_contra hN
    exact h (Or.inl hN)
  have hD : R * (z - α) - (z - β) = 0 := by
    by_contra hD
    exact h (Or.inr hD)
  have hDmul : R * (z - α) = z - β := sub_eq_zero.mp hD
  have hNmul : R * β * (z - α) = α * (z - β) := sub_eq_zero.mp hN
  have hzero : (β - α) * (z - β) = 0 := by
    calc
      (β - α) * (z - β) = R * β * (z - α) - α * (z - β) := by
        rw [← hDmul]
        ring
      _ = 0 := by rw [hNmul]; ring
  rcases mul_eq_zero.mp hzero with hba | hzb
  · exact hαβ (eq_comm.mp (sub_eq_zero.mp hba))
  · exact hzβ (sub_eq_zero.mp hzb)

/-- The pole-safe inverse-cross-ratio sphere map is continuous at every source point away from `β`. -/
theorem crossRatioInverseSphere_continuousAt {α β z R : ℂ} (hαβ : α ≠ β) (hzβ : z ≠ β) :
    ContinuousAt (fun p : ℂ × ℂ => crossRatioInverseSphere α β p.1 p.2) (z, R) := by
  have hND := crossRatioInverseSphere_num_den_not_both_zero (R := R) hαβ hzβ
  let F : ℂ × ℂ → ℂ × ℂ := fun p =>
    (p.2 * β * (p.1 - α) - α * (p.1 - β), p.2 * (p.1 - α) - (p.1 - β))
  change ContinuousAt ((fun q : ℂ × ℂ => homogeneousRatioStereo q.1 q.2) ∘ F) (z, R)
  exact ContinuousAt.comp_of_eq (homogeneousRatioStereo_continuousAt hND)
    (by fun_prop : ContinuousAt F (z, R)) rfl

/-- Set-level continuity of the pole-safe inverse-cross-ratio sphere map. -/
theorem crossRatioInverseSphere_continuousOn {α β : ℂ} {U : Set ℂ} {R : ℂ → ℂ}
    (hαβ : α ≠ β) (hzβ : ∀ z ∈ U, z ≠ β) (hRcont : ContinuousOn R U) :
    ContinuousOn (fun z => crossRatioInverseSphere α β z (R z)) U := by
  intro z hz
  exact ContinuousAt.comp₂_continuousWithinAt_of_eq
    (crossRatioInverseSphere_continuousAt hαβ (hzβ z hz))
    continuousWithinAt_id (hRcont z hz) rfl

/-- In the inverse coordinate `T = R⁻¹`, the homogeneous inverse-cross-ratio coordinates are never
simultaneously zero when `α ≠ β` and the source point is not `α`. -/
theorem crossRatioInverseSphereInv_num_den_not_both_zero {α β z T : ℂ}
    (hαβ : α ≠ β) (hzα : z ≠ α) :
    β * (z - α) - T * α * (z - β) ≠ 0 ∨ (z - α) - T * (z - β) ≠ 0 := by
  by_contra h
  have hN : β * (z - α) - T * α * (z - β) = 0 := by
    by_contra hN
    exact h (Or.inl hN)
  have hD : (z - α) - T * (z - β) = 0 := by
    by_contra hD
    exact h (Or.inr hD)
  have hDmul : z - α = T * (z - β) := sub_eq_zero.mp hD
  have hNmul : β * (z - α) = T * α * (z - β) := sub_eq_zero.mp hN
  have hzero : (β - α) * (z - α) = 0 := by
    calc
      (β - α) * (z - α) = β * (z - α) - T * α * (z - β) := by
        rw [hDmul]
        ring
      _ = 0 := by rw [hNmul]; ring
  rcases mul_eq_zero.mp hzero with hba | hza
  · exact hαβ (eq_comm.mp (sub_eq_zero.mp hba))
  · exact hzα (sub_eq_zero.mp hza)

/-- Continuity of the inverse-coordinate homogeneous sphere map. -/
theorem crossRatioInverseSphereInv_continuousAt {α β z T : ℂ}
    (hαβ : α ≠ β) (hzα : z ≠ α) :
    ContinuousAt (fun p : ℂ × ℂ => crossRatioInverseSphereInv α β p.1 p.2) (z, T) := by
  have hND := crossRatioInverseSphereInv_num_den_not_both_zero (T := T) hαβ hzα
  let F : ℂ × ℂ → ℂ × ℂ := fun p =>
    (β * (p.1 - α) - p.2 * α * (p.1 - β), (p.1 - α) - p.2 * (p.1 - β))
  change ContinuousAt ((fun q : ℂ × ℂ => homogeneousRatioStereo q.1 q.2) ∘ F) (z, T)
  exact ContinuousAt.comp_of_eq (homogeneousRatioStereo_continuousAt hND)
    (by fun_prop : ContinuousAt F (z, T)) rfl

/-- Set-level continuity of the inverse-coordinate homogeneous sphere map. -/
theorem crossRatioInverseSphereInv_continuousOn {α β : ℂ} {U : Set ℂ} {T : ℂ → ℂ}
    (hαβ : α ≠ β) (hα : ∀ z ∈ U, z ≠ α) (hTcont : ContinuousOn T U) :
    ContinuousOn (fun z => crossRatioInverseSphereInv α β z (T z)) U := by
  intro z hz
  exact ContinuousAt.comp₂_continuousWithinAt_of_eq
    (crossRatioInverseSphereInv_continuousAt hαβ (hα z hz))
    continuousWithinAt_id (hTcont z hz) rfl

/-- At `T = 0`, i.e. `R = ∞`, the inverse-cross-ratio sphere value is the finite point `β`. -/
theorem crossRatioInverseSphereInv_zero_eq {α β z : ℂ} (hzα : z ≠ α) :
    crossRatioInverseSphereInv α β z 0 = stereo β := by
  rw [crossRatioInverseSphereInv]
  simp only [zero_mul, sub_zero]
  have hden : z - α ≠ 0 := sub_ne_zero.mpr hzα
  rw [homogeneousRatioStereo_eq_stereo_div hden]
  congr
  field_simp [hden]

/-- The finite `R` chart and the inverse `T = R⁻¹` chart define the same homogeneous sphere point. -/
theorem crossRatioInverseSphere_eq_inv {α β z R : ℂ} (hR : R ≠ 0) :
    crossRatioInverseSphere α β z R = crossRatioInverseSphereInv α β z R⁻¹ := by
  rw [crossRatioInverseSphere, crossRatioInverseSphereInv]
  have hscale := homogeneousRatioStereo_smul (a := R⁻¹)
    (N := R * β * (z - α) - α * (z - β))
    (D := R * (z - α) - (z - β)) (inv_ne_zero hR)
  rw [← hscale]
  congr 1
  · field_simp [hR]
  · field_simp [hR]

/-- Uniform convergence of cross-ratio values gives uniform convergence of the pole-safe homogeneous
inverse-sphere values on compact patches avoiding `β`.

This is the analytic bridge that removes the inverse-Möbius pole from the Montel source: after a
cross-ratio subsequence converges uniformly to `Rlim`, the corresponding homogeneous spherical
inverse-cross-ratio subsequence converges uniformly to the homogeneous inverse of `Rlim`. -/
theorem tendstoUniformlyOn_crossRatioInverseSphere_of_tendstoUniformlyOn
    {α β : ℂ} {K : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {Rlim : ℂ → ℂ}
    (hK : IsCompact K)
    (hαβ : α ≠ β)
    (hzβ : ∀ z ∈ K, z ≠ β)
    (hRcont : ContinuousOn Rlim K)
    (hconv : TendstoUniformlyOn Rseq Rlim atTop K) :
    TendstoUniformlyOn
      (fun n z => crossRatioInverseSphere α β z (Rseq n z))
      (fun z => crossRatioInverseSphere α β z (Rlim z)) atTop K := by
  have hRimgCompact : IsCompact (Rlim '' K) := hK.image_of_continuousOn hRcont
  obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hRimgCompact.isBounded
  let C : ℝ := B + 1
  let S : Set (ℂ × ℂ) := K ×ˢ closedBall (0 : ℂ) C
  have hScompact : IsCompact S := hK.prod (isCompact_closedBall (0 : ℂ) C)
  have hFcont : ContinuousOn (fun p : ℂ × ℂ => crossRatioInverseSphere α β p.1 p.2) S := by
    intro p hp
    exact (crossRatioInverseSphere_continuousAt hαβ (hzβ p.1 hp.1)).continuousWithinAt
  have hUC : UniformContinuousOn (fun p : ℂ × ℂ => crossRatioInverseSphere α β p.1 p.2) S :=
    hScompact.uniformContinuousOn_of_continuous hFcont
  have hlim_mem : ∀ z ∈ K, (z, Rlim z) ∈ S := by
    intro z hz
    refine ⟨hz, ?_⟩
    have himg : Rlim z ∈ Rlim '' K := ⟨z, hz, rfl⟩
    have hclosed := hB himg
    rw [mem_closedBall, dist_zero_right] at hclosed ⊢
    dsimp [C]
    linarith
  have hseq_mem : ∀ᶠ n in atTop, ∀ z ∈ K, (z, Rseq n z) ∈ S := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv
    filter_upwards [hconv 1 (by norm_num)] with n hn
    intro z hz
    refine ⟨hz, ?_⟩
    have hlim_closed : Rlim z ∈ closedBall (0 : ℂ) B := hB ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hlim_closed ⊢
    have hdist : dist (Rlim z) (Rseq n z) < 1 := hn z hz
    have hnorm : ‖Rseq n z‖ ≤ ‖Rlim z‖ + dist (Rlim z) (Rseq n z) := by
      calc
        ‖Rseq n z‖ = dist (0 : ℂ) (Rseq n z) := by rw [dist_zero_left]
        _ ≤ dist (0 : ℂ) (Rlim z) + dist (Rlim z) (Rseq n z) := dist_triangle _ _ _
        _ = ‖Rlim z‖ + dist (Rlim z) (Rseq n z) := by rw [dist_zero_left]
    dsimp [C]
    linarith
  have hpair : TendstoUniformlyOn (fun n z => (z, Rseq n z)) (fun z => (z, Rlim z)) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    filter_upwards [hconv ε hε] with n hn
    intro z hz
    simpa using hn z hz
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hseq_mem hlim_mem hUC hpair

/-- Uniform convergence in the inverse coordinate `T = R⁻¹` gives uniform convergence of the
inverse-coordinate homogeneous sphere values on compact patches avoiding `α`. -/
theorem tendstoUniformlyOn_crossRatioInverseSphereInv_of_tendstoUniformlyOn
    {α β : ℂ} {K : Set ℂ} {Tseq : ℕ → ℂ → ℂ} {Tlim : ℂ → ℂ}
    (hK : IsCompact K)
    (hαβ : α ≠ β)
    (hα : ∀ z ∈ K, z ≠ α)
    (hTcont : ContinuousOn Tlim K)
    (hconv : TendstoUniformlyOn Tseq Tlim atTop K) :
    TendstoUniformlyOn
      (fun n z => crossRatioInverseSphereInv α β z (Tseq n z))
      (fun z => crossRatioInverseSphereInv α β z (Tlim z)) atTop K := by
  have hTimgCompact : IsCompact (Tlim '' K) := hK.image_of_continuousOn hTcont
  obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hTimgCompact.isBounded
  let C : ℝ := B + 1
  let S : Set (ℂ × ℂ) := K ×ˢ closedBall (0 : ℂ) C
  have hScompact : IsCompact S := hK.prod (isCompact_closedBall (0 : ℂ) C)
  have hFcont : ContinuousOn (fun p : ℂ × ℂ => crossRatioInverseSphereInv α β p.1 p.2) S := by
    intro p hp
    exact (crossRatioInverseSphereInv_continuousAt hαβ (hα p.1 hp.1)).continuousWithinAt
  have hUC : UniformContinuousOn (fun p : ℂ × ℂ => crossRatioInverseSphereInv α β p.1 p.2) S :=
    hScompact.uniformContinuousOn_of_continuous hFcont
  have hlim_mem : ∀ z ∈ K, (z, Tlim z) ∈ S := by
    intro z hz
    refine ⟨hz, ?_⟩
    have himg : Tlim z ∈ Tlim '' K := ⟨z, hz, rfl⟩
    have hclosed := hB himg
    rw [mem_closedBall, dist_zero_right] at hclosed ⊢
    dsimp [C]
    linarith
  have hseq_mem : ∀ᶠ n in atTop, ∀ z ∈ K, (z, Tseq n z) ∈ S := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv
    filter_upwards [hconv 1 (by norm_num)] with n hn
    intro z hz
    refine ⟨hz, ?_⟩
    have hlim_closed : Tlim z ∈ closedBall (0 : ℂ) B := hB ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hlim_closed ⊢
    have hdist : dist (Tlim z) (Tseq n z) < 1 := hn z hz
    have hnorm : ‖Tseq n z‖ ≤ ‖Tlim z‖ + dist (Tlim z) (Tseq n z) := by
      calc
        ‖Tseq n z‖ = dist (0 : ℂ) (Tseq n z) := by rw [dist_zero_left]
        _ ≤ dist (0 : ℂ) (Tlim z) + dist (Tlim z) (Tseq n z) := dist_triangle _ _ _
        _ = ‖Tlim z‖ + dist (Tlim z) (Tseq n z) := by rw [dist_zero_left]
    dsimp [C]
    linarith
  have hpair : TendstoUniformlyOn (fun n z => (z, Tseq n z)) (fun z => (z, Tlim z)) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    filter_upwards [hconv ε hε] with n hn
    intro z hz
    simpa using hn z hz
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hseq_mem hlim_mem hUC hpair

/-- The inverse-coordinate convergence theorem in the original finite `R` chart. -/
theorem tendstoUniformlyOn_crossRatioInverseSphere_of_inv_tendstoUniformlyOn
    {α β : ℂ} {K : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {Tlim : ℂ → ℂ}
    (hK : IsCompact K)
    (hαβ : α ≠ β)
    (hα : ∀ z ∈ K, z ≠ α)
    (hRne : ∀ n z, z ∈ K → Rseq n z ≠ 0)
    (hTcont : ContinuousOn Tlim K)
    (hconv : TendstoUniformlyOn (fun n z => (Rseq n z)⁻¹) Tlim atTop K) :
    TendstoUniformlyOn
      (fun n z => crossRatioInverseSphere α β z (Rseq n z))
      (fun z => crossRatioInverseSphereInv α β z (Tlim z)) atTop K := by
  have hInv := tendstoUniformlyOn_crossRatioInverseSphereInv_of_tendstoUniformlyOn
    hK hαβ hα hTcont hconv
  refine hInv.congr ?_
  filter_upwards with n z hz
  exact (crossRatioInverseSphere_eq_inv (hRne n z hz)).symm

/-- If cross-ratio values tend uniformly to `∞` in the inverse coordinate (`R⁻¹ → 0`), then the
homogeneous inverse-cross-ratio sphere values tend uniformly to the finite point `β`.

This is the infinity-chart companion to
`tendstoUniformlyOn_crossRatioInverseSphere_of_tendstoUniformlyOn`. -/
theorem tendstoUniformlyOn_crossRatioInverseSphereInv_of_tendstoUniformlyOn_zero
    {α β : ℂ} {K : Set ℂ} {Tseq : ℕ → ℂ → ℂ}
    (hK : IsCompact K)
    (hαβ : α ≠ β)
    (hα : ∀ z ∈ K, z ≠ α)
    (hconv : TendstoUniformlyOn Tseq (fun _ : ℂ => 0) atTop K) :
    TendstoUniformlyOn
      (fun n z => crossRatioInverseSphereInv α β z (Tseq n z))
      (fun _z => stereo β) atTop K := by
  let S : Set (ℂ × ℂ) := K ×ˢ closedBall (0 : ℂ) 1
  have hScompact : IsCompact S := hK.prod (isCompact_closedBall (0 : ℂ) 1)
  have hFcont : ContinuousOn (fun p : ℂ × ℂ => crossRatioInverseSphereInv α β p.1 p.2) S := by
    intro p hp
    exact (crossRatioInverseSphereInv_continuousAt hαβ (hα p.1 hp.1)).continuousWithinAt
  have hUC : UniformContinuousOn (fun p : ℂ × ℂ => crossRatioInverseSphereInv α β p.1 p.2) S :=
    hScompact.uniformContinuousOn_of_continuous hFcont
  have hlim_mem : ∀ z ∈ K, (z, (0 : ℂ)) ∈ S := by
    intro z hz
    exact ⟨hz, mem_closedBall_self zero_le_one⟩
  have hseq_mem : ∀ᶠ n in atTop, ∀ z ∈ K, (z, Tseq n z) ∈ S := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv
    filter_upwards [hconv 1 (by norm_num)] with n hn
    intro z hz
    refine ⟨hz, ?_⟩
    have hdist : dist (0 : ℂ) (Tseq n z) < 1 := hn z hz
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖Tseq n z‖ = dist (Tseq n z) (0 : ℂ) := by rw [dist_zero_right]
      _ = dist (0 : ℂ) (Tseq n z) := dist_comm _ _
      _ ≤ 1 := le_of_lt hdist
  have hpair : TendstoUniformlyOn (fun n z => (z, Tseq n z)) (fun z => (z, (0 : ℂ))) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    filter_upwards [hconv ε hε] with n hn
    intro z hz
    simpa using hn z hz
  have hcomp : TendstoUniformlyOn
      (fun n z => crossRatioInverseSphereInv α β z (Tseq n z))
      (fun z => crossRatioInverseSphereInv α β z 0) atTop K :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually hseq_mem hlim_mem hUC hpair
  exact hcomp.congr_right (fun z hz => crossRatioInverseSphereInv_zero_eq (hα z hz))

/-- The previous theorem in the original finite `R` chart. If `R n z` is never zero and `R n z⁻¹`
tends uniformly to `0`, then the pole-safe inverse-cross-ratio sphere values tend to `β`. -/
theorem tendstoUniformlyOn_crossRatioInverseSphere_of_inv_tendstoUniformlyOn_zero
    {α β : ℂ} {K : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    (hK : IsCompact K)
    (hαβ : α ≠ β)
    (hα : ∀ z ∈ K, z ≠ α)
    (hRne : ∀ n z, z ∈ K → Rseq n z ≠ 0)
    (hconv : TendstoUniformlyOn (fun n z => (Rseq n z)⁻¹) (fun _ : ℂ => 0) atTop K) :
    TendstoUniformlyOn
      (fun n z => crossRatioInverseSphere α β z (Rseq n z))
      (fun _z => stereo β) atTop K := by
  have hInv := tendstoUniformlyOn_crossRatioInverseSphereInv_of_tendstoUniformlyOn_zero
    hK hαβ hα hconv
  refine hInv.congr ?_
  filter_upwards with n z hz
  exact (crossRatioInverseSphere_eq_inv (hRne n z hz)).symm

/-- On a patch where `R` is the genuine iterate cross-ratio, the inverse Möbius transform recovers
the quadratic iterate pointwise. -/
theorem eqOn_iterate_eq_crossRatioInverse {c α β : ℂ} {n : ℕ} {U : Set ℂ}
    {R : ℂ → ℂ}
    (hαβ : α ≠ β)
    (hβ : ∀ z ∈ U, (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : Set.EqOn R
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    Set.EqOn (fun z => crossRatioInverse α β z (R z))
      (fun z => (quadratic c)^[n] z) U := by
  intro z hz
  exact crossRatio_iterate_solve hαβ (hβ z hz) (hα z hz) (hzβ z hz) (hR hz)

/-- On the same patch, the inverse-Möbius denominator is nonzero pointwise. -/
theorem eqOn_crossRatioInverse_den_ne_zero {c α β : ℂ} {n : ℕ} {U : Set ℂ}
    {R : ℂ → ℂ}
    (hαβ : α ≠ β)
    (hβ : ∀ z ∈ U, (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : Set.EqOn R
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ∀ z ∈ U, R z * (z - α) - (z - β) ≠ 0 := by
  intro z hz
  exact crossRatio_iterate_solve_den_ne_zero hαβ (hβ z hz) (hα z hz) (hzβ z hz) (hR hz)

/-- Family form of `eqOn_iterate_eq_crossRatioInverse`, for the Montel sequence of iterates. -/
theorem forall_eqOn_iterate_eq_crossRatioInverse {c α β : ℂ} {U : Set ℂ}
    {R : ℕ → ℂ → ℂ}
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ∀ n, Set.EqOn (fun z => crossRatioInverse α β z (R n z))
      (fun z => (quadratic c)^[n] z) U := by
  intro n
  exact eqOn_iterate_eq_crossRatioInverse hαβ (hβ n) hα hzβ (hR n)

/-- Family form of `eqOn_crossRatioInverse_den_ne_zero`, for the Montel sequence of iterates. -/
theorem forall_crossRatioInverse_den_ne_zero {c α β : ℂ} {U : Set ℂ}
    {R : ℕ → ℂ → ℂ}
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ∀ n z, z ∈ U → R n z * (z - α) - (z - β) ≠ 0 := by
  intro n z hz
  exact eqOn_crossRatioInverse_den_ne_zero hαβ (hβ n) hα hzβ (hR n) z hz

/-- A genuine iterate cross-ratio is nonzero on a patch avoiding the numerator fibres. -/
theorem eqOn_crossRatio_ne_zero {c α β : ℂ} {n : ℕ} {U : Set ℂ}
    {R : ℂ → ℂ}
    (hβ : ∀ z ∈ U, (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ z ∈ U, (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : Set.EqOn R
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ∀ z ∈ U, R z ≠ 0 := by
  intro z hz
  rw [hR hz]
  exact crossRatio_iterate_ne_zero_of_avoids (hβ z hz) (hα z hz) (hpreα z hz) (hzβ z hz)

/-- Family form of `eqOn_crossRatio_ne_zero`. -/
theorem forall_crossRatio_ne_zero {c α β : ℂ} {U : Set ℂ}
    {R : ℕ → ℂ → ℂ}
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ∀ n z, z ∈ U → R n z ≠ 0 := by
  intro n z hz
  exact eqOn_crossRatio_ne_zero (hβ n) hα (hpreα n) hzβ (hR n) z hz

/-- On a frontier ball, the inverse-cross-ratio family cannot have a finite locally uniform
subsequential limit.

The family equality supplied by `forall_eqOn_iterate_eq_crossRatioInverse` pushes such a limit to the
quadratic iterate family, contradicting `no_normal_limit_of_frontier`. -/
theorem no_normal_crossRatioInverse_limit_of_frontier {c α β z₀ : ℂ} {ρ : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : ball z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ¬ ∃ (φ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono φ ∧
        TendstoUniformlyOn (fun k z => crossRatioInverse α β z (R (φ k) z)) G atTop
          (ball z₀ ρ) := by
  intro hlim
  obtain ⟨φ, G, hφ, hconv⟩ := hlim
  have hEq := forall_eqOn_iterate_eq_crossRatioInverse hαβ hβ hα hzβ hR
  have hiter : TendstoUniformlyOn (fun k => (quadratic c)^[φ k]) G atTop (ball z₀ ρ) := by
    refine hconv.congr ?_
    filter_upwards with k z hz
    exact hEq (φ k) (hU hz)
  exact no_normal_limit_of_frontier hzfront hρ ⟨φ, G, hφ, hiter⟩

/-- Spherical version of `no_normal_crossRatioInverse_limit_of_frontier`.

This is the bridge needed after replacing finite normality by Marty/spherical normality: even if the
inverse Möbius transform tends to the point at infinity, a spherical locally uniform limit would still
push to a forbidden spherical iterate limit at the frontier. -/
theorem no_spherical_crossRatioInverse_limit_of_frontier {c α β z₀ : ℂ} {ρ : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ¬ ∃ (φ : ℕ → ℕ) (G : ℂ → EuclideanSpace ℝ (Fin 3)), StrictMono φ ∧
        ContinuousOn G (closedBall z₀ ρ) ∧
        TendstoUniformlyOn
          (fun k z => stereo (crossRatioInverse α β z (R (φ k) z))) G atTop
          (closedBall z₀ ρ) := by
  intro hlim
  obtain ⟨φ, G, hφ, hGcont, hconv⟩ := hlim
  have hEq := forall_eqOn_iterate_eq_crossRatioInverse hαβ hβ hα hzβ hR
  have hiter : TendstoUniformlyOn (fun k z => stereo ((quadratic c)^[φ k] z)) G atTop
      (closedBall z₀ ρ) := by
    refine hconv.congr ?_
    filter_upwards with k z hz
    exact congrArg stereo (hEq (φ k) (hU hz))
  exact no_spherical_normal_limit_of_frontier hzfront hρ ⟨φ, G, hφ, hGcont, hiter⟩

/-- Spherical obstruction for the homogeneous inverse-cross-ratio family.

This is the pole-safe version of `no_spherical_crossRatioInverse_limit_of_frontier`: the homogeneous
projective formula agrees with `stereo (crossRatioInverse ...)` on every genuine cross-ratio value,
but it also has the right target when the limiting inverse-Möbius denominator vanishes. -/
theorem no_spherical_crossRatioInverseSphere_limit_of_frontier {c α β z₀ : ℂ} {ρ : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ¬ ∃ (φ : ℕ → ℕ) (G : ℂ → EuclideanSpace ℝ (Fin 3)), StrictMono φ ∧
        ContinuousOn G (closedBall z₀ ρ) ∧
        TendstoUniformlyOn
          (fun k z => crossRatioInverseSphere α β z (R (φ k) z)) G atTop
          (closedBall z₀ ρ) := by
  intro hlim
  obtain ⟨φ, G, hφ, hGcont, hconv⟩ := hlim
  have hEq := forall_eqOn_iterate_eq_crossRatioInverse hαβ hβ hα hzβ hR
  have hDen := forall_crossRatioInverse_den_ne_zero hαβ hβ hα hzβ hR
  have hiter : TendstoUniformlyOn (fun k z => stereo ((quadratic c)^[φ k] z)) G atTop
      (closedBall z₀ ρ) := by
    refine hconv.congr ?_
    filter_upwards with k z hz
    change crossRatioInverseSphere α β z (R (φ k) z) = stereo ((quadratic c)^[φ k] z)
    rw [crossRatioInverseSphere_eq_stereo (hDen (φ k) z (hU hz))]
    exact congrArg stereo (hEq (φ k) (hU hz))
  exact no_spherical_normal_limit_of_frontier hzfront hρ ⟨φ, G, hφ, hGcont, hiter⟩

/-- A genuine cross-ratio family has no finite locally uniform subsequential limit on a frontier
closed ball.

Given such a cross-ratio limit `H`, the compact-uniform homogeneous inverse-sphere bridge turns it into
a spherical locally uniform limit of the pole-safe inverse-cross-ratio family. The preceding theorem
pushes that back to forbidden spherical normality of the quadratic iterates at the frontier. -/
theorem no_crossRatio_uniform_limit_of_frontier {c α β z₀ : ℂ} {ρ : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hRcont : ∀ n, ContinuousOn (R n) (closedBall z₀ ρ))
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ¬ ∃ (φ : ℕ → ℕ) (H : ℂ → ℂ), StrictMono φ ∧
        TendstoUniformlyOn (fun k z => R (φ k) z) H atTop (closedBall z₀ ρ) := by
  intro hlim
  obtain ⟨φ, H, hφ, hconv⟩ := hlim
  have hHcont : ContinuousOn H (closedBall z₀ ρ) := by
    exact hconv.continuousOn (Frequently.of_forall fun k => hRcont (φ k))
  have hSphereConv :
      TendstoUniformlyOn
        (fun k z => crossRatioInverseSphere α β z (R (φ k) z))
        (fun z => crossRatioInverseSphere α β z (H z)) atTop (closedBall z₀ ρ) :=
    tendstoUniformlyOn_crossRatioInverseSphere_of_tendstoUniformlyOn
      (isCompact_closedBall z₀ ρ) hαβ (fun z hz => hzβ z (hU hz)) hHcont hconv
  have hSphereCont : ContinuousOn (fun z => crossRatioInverseSphere α β z (H z))
      (closedBall z₀ ρ) :=
    crossRatioInverseSphere_continuousOn hαβ (fun z hz => hzβ z (hU hz)) hHcont
  exact no_spherical_crossRatioInverseSphere_limit_of_frontier hzfront hρ hU hαβ hβ hα hzβ hR
    ⟨φ, fun z => crossRatioInverseSphere α β z (H z), hφ, hSphereCont, hSphereConv⟩

/-- A genuine cross-ratio family also cannot escape uniformly to infinity on a frontier closed ball.

In inverse coordinates this says `(R n z)⁻¹ → 0` uniformly. The infinity-chart bridge then makes the
homogeneous inverse-cross-ratio sphere converge uniformly to the finite point `β`, again contradicting
the spherical non-normality of the quadratic iterates at the frontier. -/
theorem no_crossRatio_inv_tendsto_zero_of_frontier {c α β z₀ : ℂ} {ρ : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hRne : ∀ n z, z ∈ closedBall z₀ ρ → R n z ≠ 0)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ¬ ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        TendstoUniformlyOn (fun k z => (R (φ k) z)⁻¹) (fun _ : ℂ => 0) atTop
          (closedBall z₀ ρ) := by
  intro hlim
  obtain ⟨φ, hφ, hinv⟩ := hlim
  have hSphereConv :
      TendstoUniformlyOn
        (fun k z => crossRatioInverseSphere α β z (R (φ k) z))
        (fun _z => stereo β) atTop (closedBall z₀ ρ) :=
    tendstoUniformlyOn_crossRatioInverseSphere_of_inv_tendstoUniformlyOn_zero
      (isCompact_closedBall z₀ ρ) hαβ (fun z hz => hα z (hU hz))
      (fun k z hz => hRne (φ k) z hz) hinv
  have hSphereCont : ContinuousOn (fun _z : ℂ => stereo β) (closedBall z₀ ρ) :=
    continuous_const.continuousOn
  exact no_spherical_crossRatioInverseSphere_limit_of_frontier hzfront hρ hU hαβ hβ hα hzβ hR
    ⟨φ, fun _z => stereo β, hφ, hSphereCont, hSphereConv⟩

/-- A genuine cross-ratio family has no locally uniform subsequential limit in the inverse
coordinate on a frontier closed ball.

This is the full infinity-chart obstruction: the limit of `(R n z)⁻¹` may be any continuous finite
function, not only `0`. Composing with the inverse-coordinate homogeneous sphere map again produces
a forbidden spherical normal limit of the inverse-cross-ratio family. -/
theorem no_crossRatio_inv_uniform_limit_of_frontier {c α β z₀ : ℂ} {ρ : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hRne : ∀ n z, z ∈ closedBall z₀ ρ → R n z ≠ 0)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ¬ ∃ (φ : ℕ → ℕ) (T : ℂ → ℂ), StrictMono φ ∧
        ContinuousOn T (closedBall z₀ ρ) ∧
        TendstoUniformlyOn (fun k z => (R (φ k) z)⁻¹) T atTop
          (closedBall z₀ ρ) := by
  intro hlim
  obtain ⟨φ, T, hφ, hTcont, hinv⟩ := hlim
  have hSphereConv :
      TendstoUniformlyOn
        (fun k z => crossRatioInverseSphere α β z (R (φ k) z))
        (fun z => crossRatioInverseSphereInv α β z (T z)) atTop (closedBall z₀ ρ) :=
    tendstoUniformlyOn_crossRatioInverseSphere_of_inv_tendstoUniformlyOn
      (isCompact_closedBall z₀ ρ) hαβ (fun z hz => hα z (hU hz))
      (fun k z hz => hRne (φ k) z hz) hTcont hinv
  have hSphereCont : ContinuousOn (fun z => crossRatioInverseSphereInv α β z (T z))
      (closedBall z₀ ρ) :=
    crossRatioInverseSphereInv_continuousOn hαβ (fun z hz => hα z (hU hz)) hTcont
  exact no_spherical_crossRatioInverseSphere_limit_of_frontier hzfront hρ hU hαβ hβ hα hzβ hR
    ⟨φ, fun z => crossRatioInverseSphereInv α β z (T z), hφ, hSphereCont, hSphereConv⟩

/-- Finite-chart branch of the spherical cross-ratio obstruction. If the spherical limit stays
uniformly away from the north pole, charting it gives a forbidden finite cross-ratio limit. -/
theorem no_spherical_crossRatio_uniform_limit_of_frontier_finiteChart {c α β z₀ : ℂ} {ρ B : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hRcont : ∀ n, ContinuousOn (R n) (closedBall z₀ ρ))
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hB : B < 1) :
    ¬ ∃ (φ : ℕ → ℕ) (G : ℂ → EuclideanSpace ℝ (Fin 3)), StrictMono φ ∧
        ContinuousOn G (closedBall z₀ ρ) ∧
        (∀ z ∈ closedBall z₀ ρ, (G z).ofLp (2 : Fin 3) ≤ B) ∧
        TendstoUniformlyOn (fun k z => stereo (R (φ k) z)) G atTop
          (closedBall z₀ ρ) := by
  intro hlim
  obtain ⟨φ, G, hφ, _hGcont, hGthird, hconv⟩ := hlim
  have hchart :
      TendstoUniformlyOn (fun k z => R (φ k) z) (fun z => stereoFiniteChart (G z)) atTop
        (closedBall z₀ ρ) :=
    tendstoUniformlyOn_of_stereo_tendstoUniformlyOn_finiteChart hGthird hB hconv
  exact no_crossRatio_uniform_limit_of_frontier hzfront hρ hU hαβ hβ hα hzβ hRcont hR
    ⟨φ, fun z => stereoFiniteChart (G z), hφ, hchart⟩

/-- Inverse-chart branch of the spherical cross-ratio obstruction. If the spherical limit stays
uniformly away from the south pole, charting near infinity gives a forbidden inverse-coordinate
cross-ratio limit. -/
theorem no_spherical_crossRatio_uniform_limit_of_frontier_invChart {c α β z₀ : ℂ} {ρ A : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hA : -1 < A) :
    ¬ ∃ (φ : ℕ → ℕ) (G : ℂ → EuclideanSpace ℝ (Fin 3)), StrictMono φ ∧
        ContinuousOn G (closedBall z₀ ρ) ∧
        (∀ z ∈ closedBall z₀ ρ, A ≤ (G z).ofLp (2 : Fin 3)) ∧
        TendstoUniformlyOn (fun k z => stereo (R (φ k) z)) G atTop
          (closedBall z₀ ρ) := by
  intro hlim
  obtain ⟨φ, G, hφ, hGcont, hGthird, hconv⟩ := hlim
  have hRneAll := forall_crossRatio_ne_zero hβ hα hpreα hzβ hR
  have hRne : ∀ n z, z ∈ closedBall z₀ ρ → R n z ≠ 0 := by
    intro n z hz
    exact hRneAll n z (hU hz)
  have hchart :
      TendstoUniformlyOn (fun k z => (R (φ k) z)⁻¹) (fun z => stereoInvChart (G z)) atTop
        (closedBall z₀ ρ) :=
    tendstoUniformlyOn_inv_of_stereo_tendstoUniformlyOn_invChart hGthird hA
      (fun k z hz => hRne (φ k) z hz) hconv
  have hTcont : ContinuousOn (fun z => stereoInvChart (G z)) (closedBall z₀ ρ) := by
    refine continuousOn_stereoInvChart_comp hGcont ?_
    intro z hz hEq
    have hlower := hGthird z hz
    linarith
  exact no_crossRatio_inv_uniform_limit_of_frontier hzfront hρ hU hαβ hβ hα hzβ hRne hR
    ⟨φ, fun z => stereoInvChart (G z), hφ, hTcont, hchart⟩

/-- Full spherical cross-ratio obstruction on a frontier closed ball.

Any spherical locally uniform subsequential limit of the genuine cross-ratio family has a center value
whose third stereographic coordinate is at most `1`. If it is below `1`, continuity puts a smaller
closed ball in the finite chart and the finite cross-ratio obstruction applies. If it is exactly `1`,
continuity puts a smaller closed ball in the inverse chart and the inverse-coordinate obstruction
applies. -/
theorem no_spherical_crossRatio_uniform_limit_of_frontier {c α β z₀ : ℂ} {ρ : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hRcont : ∀ n, ContinuousOn (R n) (closedBall z₀ ρ))
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U) :
    ¬ ∃ (φ : ℕ → ℕ) (G : ℂ → EuclideanSpace ℝ (Fin 3)), StrictMono φ ∧
        ContinuousOn G (closedBall z₀ ρ) ∧
        TendstoUniformlyOn (fun k z => stereo (R (φ k) z)) G atTop
          (closedBall z₀ ρ) := by
  intro hlim
  obtain ⟨φ, G, hφ, hGcont, hconv⟩ := hlim
  have hzmem : z₀ ∈ closedBall z₀ ρ := by
    rw [mem_closedBall, dist_self]
    exact le_of_lt hρ
  have hpt : Tendsto (fun k => stereo (R (φ k) z₀)) atTop (𝓝 (G z₀)) :=
    hconv.tendsto_at hzmem
  have hcoord : Tendsto (fun k => (stereo (R (φ k) z₀)).ofLp (2 : Fin 3)) atTop
      (𝓝 ((G z₀).ofLp (2 : Fin 3))) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).tendsto (G z₀)).comp hpt
  have hcenter_le : (G z₀).ofLp (2 : Fin 3) ≤ 1 :=
    le_of_tendsto' hcoord (fun k => stereo_third_le_one (R (φ k) z₀))
  rcases lt_or_eq_of_le hcenter_le with hcenter_lt | hcenter_eq
  · let B : ℝ := ((G z₀).ofLp (2 : Fin 3) + 1) / 2
    have hcenter_B : (G z₀).ofLp (2 : Fin 3) < B := by
      dsimp [B]
      linarith
    have hB : B < 1 := by
      dsimp [B]
      linarith
    obtain ⟨r, hrpos, hsub, hGthird⟩ :=
      exists_closedBall_upper_bound_of_continuousOn hρ hGcont hcenter_B
    have hUsub : closedBall z₀ r ⊆ U := fun z hz => hU (hsub hz)
    have hconv_r : TendstoUniformlyOn (fun k z => stereo (R (φ k) z)) G atTop
        (closedBall z₀ r) :=
      hconv.mono hsub
    have hGcont_r : ContinuousOn G (closedBall z₀ r) := hGcont.mono hsub
    have hRcont_r : ∀ n, ContinuousOn (R n) (closedBall z₀ r) :=
      fun n => (hRcont n).mono hsub
    exact no_spherical_crossRatio_uniform_limit_of_frontier_finiteChart
      hzfront hrpos hUsub hαβ hβ hα hzβ hRcont_r hR hB
      ⟨φ, G, hφ, hGcont_r, hGthird, hconv_r⟩
  · have hcenter_pos : (0 : ℝ) < (G z₀).ofLp (2 : Fin 3) := by
      rw [hcenter_eq]
      norm_num
    obtain ⟨r, hrpos, hsub, hGthird⟩ :=
      exists_closedBall_lower_bound_of_continuousOn (A := (0 : ℝ)) hρ hGcont hcenter_pos
    have hUsub : closedBall z₀ r ⊆ U := fun z hz => hU (hsub hz)
    have hconv_r : TendstoUniformlyOn (fun k z => stereo (R (φ k) z)) G atTop
        (closedBall z₀ r) :=
      hconv.mono hsub
    have hGcont_r : ContinuousOn G (closedBall z₀ r) := hGcont.mono hsub
    exact no_spherical_crossRatio_uniform_limit_of_frontier_invChart
      hzfront hrpos hUsub hαβ hβ hα hpreα hzβ hR (by norm_num : (-1 : ℝ) < 0)
      ⟨φ, G, hφ, hGcont_r, hGthird, hconv_r⟩

/-- Marty-form obstruction for the inverse-cross-ratio family itself.

On a frontier neighborhood where the inverse cross-ratio is the genuine quadratic iterate family, its
spherical derivatives cannot be uniformly bounded. A bound would make Marty produce a spherical
locally uniform subsequential limit for the inverse-cross-ratio family, contradicting
`no_spherical_crossRatioInverse_limit_of_frontier`. -/
theorem not_sphericalDeriv_bounded_crossRatioInverse_on_frontier_ball {c α β z₀ : ℂ}
    {Rball ρ M : ℝ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ ball z₀ Rball → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ ball z₀ Rball, z ≠ α)
    (hzβ : ∀ z ∈ ball z₀ Rball, z ≠ β)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) (ball z₀ Rball)) :
    ¬ ∀ n z, z ∈ ball z₀ Rball →
      sphericalDeriv (fun y => crossRatioInverse α β y (R n y)) z ≤ M := by
  intro hM
  have hEq := forall_eqOn_iterate_eq_crossRatioInverse hαβ hβ hα hzβ hR
  have hdiff : ∀ n, ∀ z ∈ ball z₀ Rball,
      DifferentiableAt ℂ (fun y => crossRatioInverse α β y (R n y)) z := by
    intro n z hz
    have hevent : (fun y => crossRatioInverse α β y (R n y)) =ᶠ[𝓝 z]
        (fun y => (quadratic c)^[n] y) :=
      eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) (fun y hy => hEq n hy)
    exact ((differentiable_quadratic_iterate c n) z).congr_of_eventuallyEq hevent
  obtain ⟨φ, G, hφ, hconv⟩ :=
    marty_normal_subseq (f := fun n y => crossRatioInverse α β y (R n y)) (c := z₀)
      (R := Rball) (r := ρ) (M := M) hρ0 hρR hdiff hM
  have hGcont : ContinuousOn G (closedBall z₀ ρ) := by
    refine hconv.continuousOn (Frequently.of_forall ?_)
    intro k
    have hcontInv : ContinuousOn (fun y => crossRatioInverse α β y (R (φ k) y))
        (closedBall z₀ ρ) := by
      intro z hz
      exact ((hdiff (φ k) z (closedBall_subset_ball hρR hz)).continuousAt).continuousWithinAt
    exact continuous_stereo.comp_continuousOn hcontInv
  exact no_spherical_crossRatioInverse_limit_of_frontier hzfront hρ0 (closedBall_subset_ball hρR)
    hαβ hβ hα hzβ hR ⟨φ, G, hφ, hGcont, hconv⟩

/-- Pointed form of the Marty obstruction for inverse cross-ratios.

For every proposed uniform spherical-derivative bound on the local inverse-cross-ratio family, some
member of the family exceeds that bound somewhere in the frontier neighborhood. -/
theorem exists_sphericalDeriv_gt_crossRatioInverse_on_frontier_ball {c α β z₀ : ℂ}
    {Rball ρ M : ℝ} {R : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ ball z₀ Rball → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ ball z₀ Rball, z ≠ α)
    (hzβ : ∀ z ∈ ball z₀ Rball, z ≠ β)
    (hR : ∀ n, Set.EqOn (R n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) (ball z₀ Rball)) :
    ∃ n z, z ∈ ball z₀ Rball ∧
      M < sphericalDeriv (fun y => crossRatioInverse α β y (R n y)) z := by
  by_contra h
  have hle : ∀ n z, z ∈ ball z₀ Rball →
      sphericalDeriv (fun y => crossRatioInverse α β y (R n y)) z ≤ M := by
    intro n z hz
    by_contra hnot
    exact h ⟨n, z, hz, lt_of_not_ge hnot⟩
  exact not_sphericalDeriv_bounded_crossRatioInverse_on_frontier_ball
    hzfront hρ0 hρR hαβ hβ hα hzβ hR hle

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Subsequence-depth form of the spherical frontier cross-ratio obstruction.  The family index may be
`k` while the genuine iterate depth is a strictly increasing sequence `nseq k`.  The proof reduces to
the existing full-depth obstruction by comparing with the raw cross-ratio family and composing strict
monotone subsequences. -/
theorem no_spherical_crossRatio_uniform_limit_of_frontier_subseq {c α β z₀ : ℂ} {ρ : ℝ}
    {U : Set ℂ} {R : ℕ → ℂ → ℂ} {nseq : ℕ → ℕ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hnseq : StrictMono nseq)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ k, Set.EqOn (R k)
      (fun z => ((quadratic c)^[nseq k] z - α) * (z - β) /
        (((quadratic c)^[nseq k] z - β) * (z - α))) U) :
    ¬ ∃ (φ : ℕ → ℕ) (G : ℂ → EuclideanSpace ℝ (Fin 3)), StrictMono φ ∧
        ContinuousOn G (closedBall z₀ ρ) ∧
        TendstoUniformlyOn (fun k z => stereo (R (φ k) z)) G atTop
          (closedBall z₀ ρ) := by
  let Rfull : ℕ → ℂ → ℂ := fun n z => ((quadratic c)^[n] z - α) * (z - β) /
    (((quadratic c)^[n] z - β) * (z - α))
  have hRfullcont : ∀ n, ContinuousOn (Rfull n) (closedBall z₀ ρ) := by
    intro n
    exact ((differentiableOn_crossRatio_iterate (U := U) (hβ n) hα).continuousOn).mono hU
  have hRfull : ∀ n, Set.EqOn (Rfull n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U := by
    intro n z hz
    rfl
  intro hlim
  obtain ⟨φ, G, hφ, hGcont, hconv⟩ := hlim
  have hdepth : StrictMono (fun k => nseq (φ k)) := hnseq.comp hφ
  have hconv_full : TendstoUniformlyOn
      (fun k z => stereo (Rfull (nseq (φ k)) z)) G atTop (closedBall z₀ ρ) := by
    refine hconv.congr ?_
    filter_upwards with k z hz
    have hEq := hR (φ k) (hU hz)
    exact congrArg stereo hEq
  exact no_spherical_crossRatio_uniform_limit_of_frontier
    (R := Rfull) hzfront hρ hU hαβ hβ hα hpreα hzβ hRfullcont hRfull
    ⟨fun k => nseq (φ k), G, hdepth, hGcont, hconv_full⟩

end

end Bottcher
