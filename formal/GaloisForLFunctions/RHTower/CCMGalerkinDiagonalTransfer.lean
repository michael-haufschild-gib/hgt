import GaloisForLFunctions.RHTower.CCMRayleighExcessAngle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Galerkin convergence and the cofinal diagonal transfer

The Rayleigh–Ritz ground data of a nested Galerkin family converges to the continuous ground data
whenever the continuous bottom eigenvalue is isolated, and the convergence upgrades to locally
uniform convergence of the associated entire transforms.  A diagonal choice of Galerkin dimensions
then transports any continuous limit to a cofinal family of finite objects.

* `tendsto_of_antitone_of_approx` — the Ritz values decrease to the continuous bottom: an antitone
  sequence bounded below by `L` and coming arbitrarily close to `L` converges to `L`.
* `gap_le_rayleighExcess_of_inner_eq_zero` — the parity/simplicity step: a trial vector orthogonal to
  the ground vector has Rayleigh value at least `eps_0 + Gap`.  Contrapositively, a Ritz value below
  the second eigenvalue forces nonzero overlap, which is what excludes an odd Ritz ground vector.
* `norm_sub_sq_eq_of_inner_real_nonneg` — with the phase convention `⟪ξ_M, ξ⟫ ≥ 0` the distance to the
  ground vector is exactly `2 (1 - ⟪ξ_M, ξ⟫)`, so no infimum over phases is needed.
* `tendstoUniformlyOn_inner_of_tendsto` — Cauchy–Schwarz against a family bounded on a compact set
  turns norm convergence of the vectors into uniform convergence of the transforms.
* `exists_diagonal_lt` and `tendsto_of_dist_lt_inv` — the diagonal selection and its conclusion.

The spectral inequality itself is reused from `CCMRayleighExcessAngle`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-! ## Ritz values decrease to the continuous bottom -/

/-- **An antitone sequence bounded below and approximating its bound converges to it.**  This is the
Rayleigh–Ritz half: the Ritz values decrease, are bounded below by the continuous bottom, and the
form core supplies trial vectors realizing it. -/
theorem tendsto_of_antitone_of_approx {f : ℕ → ℝ} {L : ℝ} (hanti : Antitone f)
    (hlb : ∀ n, L ≤ f n) (happrox : ∀ ε > 0, ∃ n, f n < L + ε) :
    Tendsto f atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := happrox ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h1 : f n ≤ f N := hanti hn
  have h2 : L ≤ f n := hlb n
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

/-! ## The orthogonality obstruction -/

/-- **A trial vector orthogonal to the ground vector has Rayleigh value at least `eps_0 + Gap`.**
This is the step that excludes an odd Ritz ground vector: an odd vector is orthogonal to the even
continuous ground vector, so its Rayleigh value cannot be below the second eigenvalue. -/
theorem gap_le_rayleighExcess_of_weight_eq_zero {ι : Type*} [DecidableEq ι] {w eps : ι → ℝ}
    {i₀ : ι} {r Gap : ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : HasSum w 1)
    (hr : HasSum (fun j => eps j * w j) r)
    (hgap : ∀ j, j ≠ i₀ → eps i₀ + Gap ≤ eps j) (hzero : w i₀ = 0) :
    eps i₀ + Gap ≤ r := by
  have h := gap_mul_one_sub_le_rayleighExcess hw hsum hr hgap
  rw [hzero, sub_zero, mul_one] at h
  linarith

/-- The contrapositive: a Rayleigh value strictly below `eps_0 + Gap` forces nonzero ground weight. -/
theorem weight_ne_zero_of_lt {ι : Type*} [DecidableEq ι] {w eps : ι → ℝ}
    {i₀ : ι} {r Gap : ℝ} (hw : ∀ j, 0 ≤ w j) (hsum : HasSum w 1)
    (hr : HasSum (fun j => eps j * w j) r)
    (hgap : ∀ j, j ≠ i₀ → eps i₀ + Gap ≤ eps j) (hlt : r < eps i₀ + Gap) :
    w i₀ ≠ 0 := by
  intro hzero
  have := gap_le_rayleighExcess_of_weight_eq_zero hw hsum hr hgap hzero
  linarith

/-! ## The normalized phase -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **With the phase convention the distance is exactly `2 (1 - ⟪ξ_M, ξ⟫)`.**  If the overlap is real
and nonnegative then the identity phase already attains the projective distance, so no infimum over
phases appears. -/
theorem norm_sub_sq_eq_of_inner_real_nonneg (g xi : E) (hg : ‖g‖ = 1) (hxi : ‖xi‖ = 1)
    (hreal : inner ℂ g xi = ((RCLike.re (inner ℂ g xi) : ℝ) : ℂ))
    (hnn : 0 ≤ RCLike.re (inner ℂ g xi)) :
    ‖g - xi‖ ^ 2 = 2 - 2 * ‖(inner ℂ g xi : ℂ)‖ := by
  have h1 : ‖g - (1 : ℂ) • xi‖ ^ 2 = 2 - 2 * RCLike.re ((1 : ℂ) * inner ℂ g xi) :=
    norm_sub_smul_sq_eq g xi hg hxi (by norm_num)
  have hnorm : ‖(inner ℂ g xi : ℂ)‖ = RCLike.re (inner ℂ g xi) := by
    conv_lhs => rw [hreal]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [one_smul] at h1
  rw [h1, one_mul, hnorm]

/-- The phase-normalized angle bound: the distance to the ground vector is controlled by the
Rayleigh excess. -/
theorem norm_sub_sq_le_of_inner_real_nonneg (g xi : E) (hg : ‖g‖ = 1) (hxi : ‖xi‖ = 1)
    (hreal : inner ℂ g xi = ((RCLike.re (inner ℂ g xi) : ℝ) : ℂ))
    (hnn : 0 ≤ RCLike.re (inner ℂ g xi))
    {Gap delta : ℝ} (hGap : 0 < Gap)
    (hexcess : Gap * (1 - ‖(inner ℂ g xi : ℂ)‖ ^ 2) ≤ delta) :
    ‖g - xi‖ ^ 2 ≤ 2 * delta / Gap := by
  rw [norm_sub_sq_eq_of_inner_real_nonneg g xi hg hxi hreal hnn]
  have ht0 : 0 ≤ ‖(inner ℂ g xi : ℂ)‖ := norm_nonneg _
  have ht1 : ‖(inner ℂ g xi : ℂ)‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) g xi
    rw [hg, hxi, one_mul] at this
    exact this
  have hstep : Gap * (1 - ‖(inner ℂ g xi : ℂ)‖) ≤ Gap * (1 - ‖(inner ℂ g xi : ℂ)‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hGap.le
  rw [le_div_iff₀ hGap]
  nlinarith [hstep, hexcess]

/-! ## Uniform convergence of the transforms -/

/-- **Cauchy–Schwarz turns norm convergence into uniform convergence.**  If the evaluation family is
bounded on a set then norm convergence of the vectors gives uniform convergence of their pairings
there.  This is the fixed-aperture determinant convergence. -/
theorem tendstoUniformlyOn_inner_of_tendsto {ι : Type*} {l : Filter ι} {v : ι → E} {vlim : E}
    {K : Set ℂ} {e : ℂ → E} {C : ℝ} (hC : 0 < C) (he : ∀ z ∈ K, ‖e z‖ ≤ C)
    (hlim : Tendsto (fun n => ‖v n - vlim‖) l (nhds 0)) :
    TendstoUniformlyOn (fun n z => inner ℂ (v n) (e z)) (fun z => inner ℂ vlim (e z)) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC0 : C ≠ 0 := ne_of_gt hC
  have hpos : 0 < ε / (2 * C) := by positivity
  have hev : ∀ᶠ n in l, ‖v n - vlim‖ < ε / (2 * C) := by
    refine (hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hpos)) |>.mono ?_
    intro n hn
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hn
  filter_upwards [hev] with n hn z hz
  have hcs : ‖inner ℂ (v n - vlim) (e z)‖ ≤ ‖v n - vlim‖ * ‖e z‖ :=
    norm_inner_le_norm (𝕜 := ℂ) _ _
  have hdist : dist (inner ℂ vlim (e z) : ℂ) (inner ℂ (v n) (e z))
      = ‖inner ℂ (v n - vlim) (e z)‖ := by
    rw [dist_eq_norm, inner_sub_left]
    rw [show (inner ℂ vlim (e z) : ℂ) - inner ℂ (v n) (e z)
        = -((inner ℂ (v n) (e z) : ℂ) - inner ℂ vlim (e z)) from by ring, norm_neg]
  rw [hdist]
  have hfin : ‖v n - vlim‖ * ‖e z‖ ≤ (ε / (2 * C)) * C :=
    mul_le_mul hn.le (he z hz) (norm_nonneg _) hpos.le
  have hval : (ε / (2 * C)) * C = ε / 2 := by field_simp
  linarith [hcs, hfin, hval]

/-! ## The diagonal selection -/

/-- **Diagonal selection.**  If every level can be approximated to arbitrary accuracy by a later
index, a diagonal sequence exists with error below `1/(j+1)`. -/
theorem exists_diagonal_lt {F : ℕ → ℕ → ℝ}
    (h : ∀ j : ℕ, ∀ ε > 0, ∃ M, j < M ∧ F j M < ε) :
    ∃ Mseq : ℕ → ℕ, (∀ j, j < Mseq j) ∧ ∀ j, F j (Mseq j) < 1 / (j + 1 : ℝ) := by
  choose M hM hF using fun j => h j (1 / (j + 1 : ℝ)) (by positivity)
  exact ⟨M, hM, hF⟩

/-- **The diagonal converges to the same limit.** -/
theorem tendsto_of_dist_lt_inv {X : Type*} [PseudoMetricSpace X] {G Gd : ℕ → X} {L : X}
    (hG : Tendsto G atTop (nhds L)) (hd : ∀ j, dist (Gd j) (G j) < 1 / (j + 1 : ℝ)) :
    Tendsto Gd atTop (nhds L) := by
  have hzero : Tendsto (fun j : ℕ => dist (Gd j) (G j)) atTop (nhds 0) := by
    refine squeeze_zero (fun j => dist_nonneg) (fun j => (hd j).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_atTop] at hG ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hG (ε / 2) (by linarith)
  have hev := hzero.eventually (Metric.ball_mem_nhds (0 : ℝ) (show 0 < ε / 2 by linarith))
  obtain ⟨N₂, hN₂⟩ := (Filter.eventually_atTop.mp hev)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 : dist (G n) L < ε / 2 := hN₁ n (le_trans (le_max_left _ _) hn)
  have h2 : dist (Gd n) (G n) < ε / 2 := by
    have := hN₂ n (le_trans (le_max_right _ _) hn)
    simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using this
  calc dist (Gd n) L ≤ dist (Gd n) (G n) + dist (G n) L := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end GaloisForLFunctions.RHTower

end
