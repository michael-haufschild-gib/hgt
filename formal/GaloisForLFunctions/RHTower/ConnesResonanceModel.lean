import Mathlib

/-!
# Connes' resonance model: non-critical zeros through the Poisson kernel

Formalization of the model computation inside the proof of Lemma 3 of §VIII of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Lemma VIII.3 identifies the limit of the distributions `Δ_Λ` and shows that *all* zeros of the
`L`-functions contribute, the critical ones per se and the non-critical ones **as resonances,
through their harmonic potential with respect to the critical line**.  Connes reduces the whole
statement to the following model on `ℓ²(ℤ)`: with `V` the shift, `S_N` the truncation to
`[-N, N]`, `E_N ⊆ S_N` the subspace cut out by the conditions `∑ ξ(n) z^n = 0`, `z ∈ F`, one has

  `Lim_{N→∞} ⟨V(f) η_z , η_z⟩ = ∫_{|u|=1} P_z(u) f̂(u) du`,       (29)

`P_z` the Poisson kernel, `η_z` the explicit unit vectors of the statement.

Two hypothesis-free theorems carry this:

* `connes_shiftRatio_tendsto` — the pairing `⟨V^k η_z , η_z⟩` equals `conj z ^ (-k)` times an
  explicit ratio of geometric sums, and that ratio tends to `1`: this is Connes' *"the unit vectors
  `η_z` are asymptotically orthogonal and span `S_N - E_N`"*.
* `connes_poisson_reproducing` — the Poisson kernel of the unit disc reproduces the monomials,
  `∫_{|u|=1} P_w(u) u^k du/2π = w^k`, i.e. the right-hand side of (29) evaluated on the Fourier
  modes.  Combining, the limit of `⟨V^k η_z, η_z⟩` is exactly the Poisson integral at `w = 1/conj z`,
  which is the harmonic potential of the non-critical zero with respect to the unit circle.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open Filter Topology Finset

/-- The ratio of truncated geometric sums appearing in `⟨V^k η_z , η_z⟩`, with `q = |z|²`. -/
def connesShiftRatio (q : ℝ) (k N : ℕ) : ℝ :=
  q ^ k * ((q ^ (2 * N + 1 - k) - 1) / (q ^ (2 * N + 1) - 1))

theorem connesShiftRatio_eq_geomSum {q : ℝ} (hq : 1 < q) (k N : ℕ) :
    connesShiftRatio q k N
      = q ^ k * ((∑ j ∈ range (2 * N + 1 - k), q ^ j) / (∑ j ∈ range (2 * N + 1), q ^ j)) := by
  have hne : q - 1 ≠ 0 := by linarith
  have hB : q ^ (2 * N + 1) - 1 ≠ 0 := by
    have h1 : (1:ℝ) < q ^ (2 * N + 1) := one_lt_pow₀ hq (by omega)
    linarith
  rw [connesShiftRatio, geom_sum_eq (by linarith), geom_sum_eq (by linarith)]
  field_simp

/-- **§VIII Lemma 3, model computation.**  The normalization ratio tends to one, so
`⟨V^k η_z , η_z⟩ → conj z ^ (-k)`. -/
theorem connes_shiftRatio_tendsto {q : ℝ} (hq : 1 < q) (k : ℕ) :
    Tendsto (fun N : ℕ => connesShiftRatio q k N) atTop (𝓝 1) := by
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq
  have hpow : Tendsto (fun N : ℕ => q ^ (2 * N + 1)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => q ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hq
    have h2 : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
      refine Filter.tendsto_atTop_mono (fun N => ?_) tendsto_id
      simp only [id_eq]
      omega
    exact h1.comp h2
  have hg : Tendsto (fun t : ℝ => (t - q ^ k) / (t - 1)) atTop (𝓝 1) := by
    have hz : Tendsto (fun t : ℝ => (1 - q ^ k) / (t - 1)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right _ (-1) tendsto_id)
    have heq : ∀ᶠ t : ℝ in atTop, 1 + (1 - q ^ k) / (t - 1) = (t - q ^ k) / (t - 1) := by
      filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
      have htne : t - 1 ≠ 0 := by intro h; linarith [h]
      field_simp
      ring
    have hsum : Tendsto (fun t : ℝ => (1:ℝ) + (1 - q ^ k) / (t - 1)) atTop (𝓝 ((1:ℝ) + 0)) :=
      (tendsto_const_nhds (x := (1:ℝ))).add hz
    rw [add_zero] at hsum
    exact hsum.congr' heq
  have hcomp : Tendsto (fun N : ℕ => (q ^ (2 * N + 1) - q ^ k) / (q ^ (2 * N + 1) - 1))
      atTop (𝓝 1) := hg.comp hpow
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  have hkle : k ≤ 2 * N + 1 := by omega
  have hsplit : q ^ k * q ^ (2 * N + 1 - k) = q ^ (2 * N + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [connesShiftRatio, ← mul_div_assoc, mul_sub, mul_one, hsplit]

/-- **§VIII Lemma 3, spectral side.**  The Poisson kernel of the unit disc reproduces the monomials:
`∫_{|u| = 1} P_w(u) u^k du/2π = w^k`.  This is the harmonic potential of the point `w` with respect
to the boundary circle, evaluated on the Fourier mode `u^k`. -/
theorem connes_poisson_reproducing {w : ℂ} (hw : ‖w‖ < 1) (k : ℕ) :
    Real.circleAverage (fun ζ : ℂ => poissonKernel 0 w ζ • ζ ^ k) 0 1 = w ^ k := by
  have hball : w ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
    exact hw
  have hdc : DiffContOnCl ℂ (fun ζ : ℂ => ζ ^ k) (Metric.ball (0:ℂ) 1) :=
    ⟨(differentiable_pow k).differentiableOn, (continuous_pow k).continuousOn⟩
  exact DiffContOnCl.circleAverage_poissonKernel_smul (R := (1:ℝ)) hdc hball

end

end GaloisForLFunctions.RHTower
