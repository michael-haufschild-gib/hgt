import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.EveryFrequencyActsAsAFrobeniusAngle

/-!
# The horizon layer is graded by frequency

A window twisted by a trigonometric polynomial `χ(n) = Σ_k a_k cos(2πnα_k)` whose frequencies are
pairwise distinct modulo `ℤ` and sign (`2α_k ∉ ℤ`, `α_k ± α_l ∉ ℤ` for `k ≠ l`) carries the sum of
the second-order terms of its frequencies:

`c⁻¹⟨Wx, x⟩/∫g² → (βA_φ/(K∫φ²)) Σ_k a_k² · ½(ζ(β+1, u_k) + ζ(β+1, 1 − u_k)) ∫ e^{−(β+1)y} H²`,

`u_k = {α_k}` (`trigTwist_layer_criticalCurve`). Distinct frequencies are orthogonal at second
order, as distinct conductors are: the products `cos(2πnα_k) cos(2π(n+δ)α_l)`, `k ≠ l`, oscillate at
the frequencies `α_k ± α_l`, whose partial sums are bounded, and only the diagonal autocorrelation
`Σ_k a_k² ½cos(2πδα_k)` survives (`trigEnergy_le`). The grading by frequency is the continuous
counterpart of the grading by conductor, and each graded piece carries the Hurwitz form of a
Frobenius angle.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ} {ι : Type*} (s : Finset ι) (a α : ι → ℝ)

/-- The trigonometric twist `n ↦ Σ_k a_k cos(2πnα_k)`. -/
def trigTwist (n : ℕ) : ℝ := ∑ k ∈ s, a k * freqTwist (α k) n

/-- The trigonometric twist on the integers. -/
def trigTwistZ (z : ℤ) : ℝ := ∑ k ∈ s, a k * freqTwistZ (α k) z

theorem trigTwistZ_natCast (n : ℕ) : trigTwistZ s a α n = trigTwist s a α n := by
  unfold trigTwistZ trigTwist
  exact sum_congr rfl fun k _ => by rw [freqTwistZ_natCast]

theorem abs_trigTwist_le (n : ℕ) : |trigTwist s a α n| ≤ ∑ k ∈ s, |a k| := by
  unfold trigTwist
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_freqTwist_le _ _)

theorem abs_trigTwistZ_le (z : ℤ) : |trigTwistZ s a α z| ≤ ∑ k ∈ s, |a k| := by
  unfold trigTwistZ
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- **Bounded partial sums**: `|Σ_{j<n} χ(j)| ≤ Σ_k |a_k|/|sin πα_k|`. -/
theorem abs_sum_range_trigTwist_le (hα : ∀ k ∈ s, Real.sin (Real.pi * α k) ≠ 0) (n : ℕ) :
    |∑ j ∈ range n, trigTwist s a α j| ≤ ∑ k ∈ s, |a k| / |Real.sin (Real.pi * α k)| := by
  unfold trigTwist
  rw [Finset.sum_comm]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  rw [← Finset.mul_sum, abs_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (abs_sum_range_freqTwist_le (hα k hk) n) (abs_nonneg _)

/-- **Kuzmin–Landau for a trigonometric twist**: each frequency is a rotation. -/
theorem norm_partial_trigTwist_cpow_le {δ : ℝ} (hδ0 : 0 < δ)
    (hu0 : ∀ k ∈ s, 0 < Int.fract (α k))
    (hδ : ∀ k ∈ s, δ ≤ min (Int.fract (α k)) (1 - Int.fract (α k)) / 2) {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : ∀ k ∈ s, τ ≤ Real.pi * n₀ * min (Int.fract (α k)) (1 - Int.fract (α k))) (j : ℕ) :
    ‖∑ i ∈ range (j + 1), (trigTwist s a α (n₀ + i) : ℂ) *
        Complex.exp (((τ * Real.log ((n₀ + i : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (∑ k ∈ s, |a k|) * (3 / (2 * δ) + 1) := by
  have e : ∑ i ∈ range (j + 1), (trigTwist s a α (n₀ + i) : ℂ) *
      Complex.exp (((τ * Real.log ((n₀ + i : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      ∑ k ∈ s, (a k : ℂ) * ∑ i ∈ range (j + 1), (freqTwist (α k) (n₀ + i) : ℂ) *
        Complex.exp (((τ * Real.log ((n₀ + i : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
    simp_rw [trigTwist, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    rw [Finset.sum_mul]
    exact sum_congr rfl fun k _ => by ring
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (norm_partial_freqTwist_cpow_le (hu0 k hk) hδ0 (hδ k hk) hn₀ hτ0 (hτ k hk) j) (abs_nonneg _)

/-- **A trigonometric block below its resonances**: for `|τ| ≤ π N e^{−A} m₀`, `m₀ ≤ min(u_k, 1 − u_k)`,
`|D_x(τ)| ≤ (Σ|a_k|)(3/m₀ + 1)(L e^{3A/2} + B e^{A/2})/√N`. -/
theorem norm_dirichletPoly_trigTwist_le {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|)
    (hu0 : ∀ k ∈ s, 0 < Int.fract (α k)) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hm : ∀ k ∈ s, m₀ ≤ min (Int.fract (α k)) (1 - Int.fract (α k))) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hτ : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) * m₀) :
    ‖dirichletPoly N (twistedWeights h (trigTwist s a α) N) τ‖ ≤
      (∑ k ∈ s, |a k|) * (3 / (2 * (m₀ / 2)) + 1) *
        ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) * m₀ →
      ‖dirichletPoly N (twistedWeights h (trigTwist s a α) N) t‖ ≤
        (∑ k ∈ s, |a k|) * (3 / (2 * (m₀ / 2)) + 1) *
          ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
    intro t ht htN
    set n₀ := windowStart A N with hn₀
    have h1 := one_le_windowStart hN A
    have htn : ∀ k ∈ s, t ≤ Real.pi * n₀ * min (Int.fract (α k)) (1 - Int.fract (α k)) := by
      intro k hk
      refine htN.trans ?_
      have hw := le_windowStart A N
      rw [← hn₀] at hw
      have hπ := Real.pi_pos
      have h0 : 0 ≤ (N : ℝ) * Real.exp (-A) := by positivity
      calc Real.pi * ((N : ℝ) * Real.exp (-A)) * m₀ ≤ Real.pi * n₀ * m₀ := by
            have := mul_le_mul_of_nonneg_left hw hπ.le
            nlinarith
        _ ≤ Real.pi * n₀ * min (Int.fract (α k)) (1 - Int.fract (α k)) :=
            mul_le_mul_of_nonneg_left (hm k hk) (by positivity)
    rw [dirichletPoly_twisted_eq_range hsupp hA _ hN]
    refine (norm_sum_mul_le_of_partial (fun j => horizonWeights h N (n₀ + j))
      (fun j => (trigTwist s a α (n₀ + j) : ℂ) * Complex.exp (((t * Real.log (n₀ + j) : ℝ) : ℂ) *
        Complex.I)) (N - n₀) (B := (∑ k ∈ s, |a k|) * (3 / (2 * (m₀ / 2)) + 1))
          fun j _ => ?_).trans ?_
    · have := norm_partial_trigTwist_cpow_le s a α (δ := m₀ / 2) (by positivity) hu0
        (fun k hk => by linarith [hm k hk]) h1 ht htn j
      push_cast at this ⊢
      exact this
    · exact mul_le_mul_of_nonneg_left (variation_horizonWeights_le hsupp hA hB hL hN)
        (by positivity)
  rcases le_or_gt 0 τ with hpos | hneg
  · rw [abs_of_nonneg hpos] at hτ
    exact key τ hpos hτ
  · have := key (-τ) (by linarith) (by rw [abs_of_neg hneg] at hτ; exact hτ)
    rwa [norm_dirichletPoly_neg] at this

/-- **The quiet region of a trigonometric twist**: with `A' = A − log m₀`, `m₀ ≤ min(u_k, 1 − u_k)`,
the energy of the block on `|τ| ≤ N e^{−A'}` is `O(N^{−1/2})`. -/
theorem exists_trigLow_energy_le {Cφ q : ℝ} (hq : 0 ≤ q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hu0 : ∀ k ∈ s, 0 < Int.fract (α k)) {m₀ : ℝ} (hm₀0 : 0 < m₀) (hm₀1 : m₀ ≤ 1)
    (hm : ∀ k ∈ s, m₀ ≤ min (Int.fract (α k)) (1 - Int.fract (α k))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
      ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-(A - Real.log m₀))))
          ((N : ℝ) * Real.exp (-(A - Real.log m₀))),
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (trigTwist s a α) N) τ‖ ^ 2 / N) ≤
            C / Real.sqrt N := by
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hL0 : 0 ≤ L := by
    have := hL 1 0; norm_num at this; linarith [abs_nonneg (h 1 - h 0)]
  set K := (∑ k ∈ s, |a k|) * (3 / (2 * (m₀ / 2)) + 1) with hK
  set V := L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) with hV
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∑ k ∈ s, |a k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  have hV0 : 0 ≤ V := by positivity
  refine ⟨2 * (Cφ * (K * V) ^ 2), by positivity, fun N hN c hc => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsN1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hexp : Real.exp (-(A - Real.log m₀)) = Real.exp (-A) * m₀ := by
    rw [show -(A - Real.log m₀) = -A + Real.log m₀ by ring, Real.exp_add, Real.exp_log hm₀0]
  set T₀ := (N : ℝ) * Real.exp (-(A - Real.log m₀)) with hT₀
  have hT₀0 : 0 ≤ T₀ := by positivity
  have hT₀N : T₀ ≤ N := by
    rw [hT₀, hexp]
    have : Real.exp (-A) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have : Real.exp (-A) * m₀ ≤ 1 := by nlinarith [Real.exp_pos (-A)]
    nlinarith
  have hφb : ∀ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 ≤ Cφ := fun τ => by
    have := hdecay (c / N * τ)
    rw [show ((c / N * τ : ℝ) : ℂ) = ((c / N : ℝ) : ℂ) * (τ : ℂ) by push_cast; ring] at this
    refine this.trans ?_
    have : (1 + |(c / N * τ)|) ^ (-q) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (c / N * τ)]) (by linarith)
    nlinarith
  have hpt : ∀ τ ∈ Set.Icc (-T₀) T₀, ‖‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (twistedWeights h (trigTwist s a α) N) τ‖ ^ 2 / N)‖ ≤
        Cφ * ((K * V) ^ 2 / (N : ℝ) ^ 2) := by
    intro τ hτ
    have hτ' : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) * m₀ := by
      refine (abs_le.mpr hτ).trans ?_
      rw [hT₀, hexp]
      have := Real.pi_gt_three
      have : 0 ≤ (N : ℝ) * (Real.exp (-A) * m₀) := by positivity
      nlinarith
    have hD := norm_dirichletPoly_trigTwist_le s a α hsupp hA hB hL hu0 hm₀0 hm hN hτ'
    rw [← hK, ← hV] at hD
    have hD2 : ‖dirichletPoly N (twistedWeights h (trigTwist s a α) N) τ‖ ^ 2 / N ≤
        (K * V) ^ 2 / (N : ℝ) ^ 2 := by
      have h2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
      rw [div_le_div_iff₀ hN0 (by positivity)]
      calc ‖dirichletPoly N (twistedWeights h (trigTwist s a α) N) τ‖ ^ 2 * (N : ℝ) ^ 2
          ≤ (K * (V / Real.sqrt N)) ^ 2 * (N : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = (K * V) ^ 2 * N := by
            rw [mul_pow, div_pow, Real.sq_sqrt hN0.le]; field_simp
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (hφb τ) hD2 (by positivity) hCφ
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (-T₀) T₀)
    measure_Icc_lt_top hpt
  rw [Real.volume_real_Icc_of_le (by linarith)] at hI
  refine (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hI.trans ?_))
  have h1 : Cφ * ((K * V) ^ 2 / (N : ℝ) ^ 2) * (T₀ - -T₀) ≤ 2 * (Cφ * (K * V) ^ 2) / N := by
    have : Cφ * ((K * V) ^ 2 / (N : ℝ) ^ 2) * (T₀ - -T₀) =
        2 * (Cφ * (K * V) ^ 2) * (T₀ / (N : ℝ) ^ 2) := by ring
    rw [this, div_eq_mul_inv (2 * (Cφ * (K * V) ^ 2))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    calc T₀ ≤ N := hT₀N
      _ = (N : ℝ)⁻¹ * (N : ℝ) ^ 2 := by field_simp
  refine h1.trans (div_le_div_of_nonneg_left (by positivity) hsN ?_)
  calc Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := le_mul_of_one_le_left hsN.le hsN1
    _ = N := Real.mul_self_sqrt hN0.le

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
