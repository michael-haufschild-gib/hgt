import GaloisForLFunctions.RHTower.IsingHarmonicMagnetizationNoGo
import GaloisForLFunctions.RHTower.SuzukiCoalescingXiCayleyTarget

/-!
# Slow-field Griffiths–Simon producers of `Ξ` are carried by their couplings

Let `X_n = Σ_k c_{n,k} σ_k` be zero-field ferromagnetic Ising magnetizations (`J ≥ 0`, `c ≥ 0`)
whose centred characteristic functions converge locally uniformly on `ℂ` to `Ξ(z)/Ξ(0)`, and
suppose the fields are slow: `max_k c_{n,k} → 0`.

**Theorem** (`tendsto_freeVariance_zero`). The free variance `Σ_k c_{n,k}²` tends to `0`.

**Proof.** For `c w ≤ 1`, `tanh(cw) ≥ cw − (cw)³/3 ≥ (2/3)cw`, so the free magnetization in the
field `w` is at least `(2/3) w Σ_k c_k²` once the masses are below `1/w`. By the dominance law it is
at most `(ξ'/ξ)(½ + w) + 1`, and the Gamma cap gives `(ξ'/ξ)(½ + w) ≤ 3 + ½ log w` for `w ≥ 1`.
Hence `Σ_k c_k² ≤ (3/(2w))(4 + ½ log w)` eventually, for every `w ≥ 1`.

**Corollary** (`tendsto_isingMag_sub_freeMag`). In every field `w > 0` the free magnetization
`Σ_k c_k tanh(c_k w)` tends to `0`, while `⟨X_n⟩_w → (ξ'/ξ)(½ + w) > 0`. The whole Riemann
magnetization is therefore produced by the couplings: slow-field producers are asymptotically
critical.
-/

open Filter Topology

namespace RHTower.GriffithsSimon

noncomputable section

/-- For `0 ≤ y ≤ 1`, `tanh y ≥ (2/3) y`. -/
theorem two_thirds_mul_le_tanh {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) : 2 / 3 * y ≤ Real.tanh y := by
  have h := sub_cube_le_tanh hy
  have : y ^ 3 ≤ y := by
    calc y ^ 3 = y * y ^ 2 := by ring
      _ ≤ y * 1 := mul_le_mul_of_nonneg_left (by nlinarith) hy
      _ = y := mul_one y
  linarith

/-- A Gamma cap of logarithmic size: `(ξ'/ξ)(½ + w) ≤ 3 + ½ log w` for `w ≥ 1`. -/
theorem xiRealLogDeriv_le_log {w : ℝ} (hw : 1 ≤ w) :
    xiRealLogDeriv w ≤ 3 + Real.log w / 2 := by
  have h := xiRealLogDeriv_le (w := w) (by linarith)
  have h1 : 1 / (1 / 2 + w) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have h2 : 1 / (w - 1 / 2) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h3 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h4 : Real.log ((1 / 2 + w) / 2) ≤ Real.log w :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

/-- `(3/(2w))(4 + ½ log w) → 0` as `w → ∞`. -/
theorem tendsto_criticality_bound :
    Tendsto (fun w : ℝ => 3 / (2 * w) * (4 + Real.log w / 2)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun w : ℝ => Real.log w / w) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Tendsto (fun w : ℝ => w⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := (hinv.const_mul 6).add (hlog.const_mul (3 / 4))
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  field_simp
  ring

/-- **Slow-field producers have vanishing free variance.** -/
theorem tendsto_freeVariance_zero {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hslow : ∀ δ > 0, ∀ᶠ n in atTop, ∀ k, c n k ≤ δ)
    (hconv : TendstoLocallyUniformly (fun n => isingChar (J n) (E n) (c n))
      (fun z => XiC z / XiC 0) atTop) :
    Tendsto (fun n => ∑ k, c n k ^ 2) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨w, hw1, hwε⟩ : ∃ w : ℝ, 1 ≤ w ∧ 3 / (2 * w) * (4 + Real.log w / 2) < ε := by
    have := (tendsto_criticality_bound.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 1)
    obtain ⟨w, hw, hw1⟩ := this.exists
    exact ⟨w, hw1, hw⟩
  have hw0 : 0 < w := by linarith
  have hev := (eventually_freeMag_le_xiRealLogDeriv J E hJ c hc hconv hw0.le one_pos).and
    (hslow (1 / w) (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hdom, hsmall⟩ := hN n hn
  have hlow : 2 / 3 * w * ∑ k, c n k ^ 2 ≤ ∑ k, c n k * Real.tanh (c n k * w) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hy0 : 0 ≤ c n k * w := mul_nonneg (hc n k) hw0.le
    have hy1 : c n k * w ≤ 1 := by
      have := hsmall k
      rw [le_div_iff₀ hw0] at this
      linarith
    have := mul_le_mul_of_nonneg_left (two_thirds_mul_le_tanh hy0 hy1) (hc n k)
    nlinarith
  have hcap := xiRealLogDeriv_le_log hw1
  have hsq : 0 ≤ ∑ k, c n k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsq]
  have hbound : ∑ k, c n k ^ 2 ≤ 3 / (2 * w) * (4 + Real.log w / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **The couplings carry the whole Riemann magnetization.** Along a slow-field producer, in every
field `w > 0` the free magnetization tends to `0` and the interaction part
`⟨X_n⟩_w − Σ_k c_{n,k} tanh(c_{n,k} w)` tends to `(ξ'/ξ)(½ + w) > 0`. -/
theorem tendsto_isingMag_sub_freeMag {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (J : ∀ n, ι n → ι n → ℝ) (E : ∀ n, Finset (ι n × ι n))
    (hJ : ∀ n, ∀ p ∈ E n, 0 ≤ J n p.1 p.2) (c : ∀ n, ι n → ℝ) (hc : ∀ n k, 0 ≤ c n k)
    (hslow : ∀ δ > 0, ∀ᶠ n in atTop, ∀ k, c n k ≤ δ)
    (hconv : TendstoLocallyUniformly (fun n => isingChar (J n) (E n) (c n))
      (fun z => XiC z / XiC 0) atTop) {w : ℝ} (hw : 0 < w) :
    Tendsto (fun n => ∑ k, c n k * Real.tanh (c n k * w)) atTop (𝓝 0) ∧
      Tendsto (fun n => isingMag (J n) (E n) (c n) w - ∑ k, c n k * Real.tanh (c n k * w))
        atTop (𝓝 (xiRealLogDeriv w)) ∧ 0 < xiRealLogDeriv w := by
  have hvar := tendsto_freeVariance_zero J E hJ c hc hslow hconv
  have hfree : Tendsto (fun n => ∑ k, c n k * Real.tanh (c n k * w)) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => w * ∑ k, c n k ^ 2) atTop (𝓝 0) := by
      simpa using hvar.const_mul w
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_)
      (fun n => ?_)
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (hc n k)
        (tanh_nonneg_of_nonneg (mul_nonneg (hc n k) hw.le))
    · rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h := GaloisForLFunctions.HTGeometry.tanh_le_self (mul_nonneg (hc n k) hw.le)
      have := mul_le_mul_of_nonneg_left h (hc n k)
      nlinarith
  refine ⟨hfree, ?_, xiRealLogDeriv_pos hw⟩
  simpa using (tendsto_isingMag_xiRealLogDeriv J E c hconv w).sub hfree

end

end RHTower.GriffithsSimon
