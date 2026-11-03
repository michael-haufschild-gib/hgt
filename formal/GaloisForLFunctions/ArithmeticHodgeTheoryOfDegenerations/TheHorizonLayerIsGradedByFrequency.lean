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

/-- The oscillation constant `Σ_{k,l} |a_k||a_l|/2 (1/|sin π(α_k + α_l)| + [k ≠ l]/|sin π(α_k − α_l)|)`
of a trigonometric twist: the partial sums of its off-diagonal products are bounded by it. -/
def trigOsc [DecidableEq ι] : ℝ :=
  ∑ k ∈ s, ∑ l ∈ s, |a k| * |a l| / 2 * (1 / |Real.sin (Real.pi * (α k + α l))| +
    if k = l then 0 else 1 / |Real.sin (Real.pi * (α k - α l))|)

theorem trigOsc_nonneg [DecidableEq ι] : 0 ≤ trigOsc s a α :=
  Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => by
    have h1 : 0 ≤ 1 / |Real.sin (Real.pi * (α k + α l))| := by positivity
    have h2 : 0 ≤ (if k = l then (0 : ℝ) else 1 / |Real.sin (Real.pi * (α k - α l))|) := by
      split_ifs <;> positivity
    positivity

/-- **The offsets of a trigonometric twist equidistribute**: the products of two frequencies
oscillate at `α_k ± α_l` and only the diagonal autocorrelation `Σ_k a_k² ½cos(2πδα_k)` survives. -/
theorem abs_offsetSum_trig_sub_le [DecidableEq ι] {G : ℝ → ℝ} {BG LG : ℝ} (hG : ∀ t, |G t| ≤ BG)
    (hGL : ∀ s t, |G s - G t| ≤ LG * |s - t|) (hBG : 0 ≤ BG) {Bu Lu : ℝ}
    (hBu : ∀ x, |invWindow h x| ≤ Bu) (hLu : ∀ x y, |invWindow h x - invWindow h y| ≤ Lu * |x - y|)
    (hu0 : ∀ x, x < Real.exp (-A) → invWindow h x = 0) (hu1 : invWindow h 1 = 0)
    (hsum : ∀ k ∈ s, ∀ l ∈ s, Real.sin (Real.pi * (α k + α l)) ≠ 0)
    (hdiff : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Real.sin (Real.pi * (α k - α l)) ≠ 0) {c : ℝ} (hc : 1 ≤ c)
    {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, trigTwist s a α n * horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        trigTwistZ s a α (n + δ) * G (δ * (c * n / N)⁻¹) -
      ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        (∑ k ∈ s, a k ^ 2 * Real.cos (2 * Real.pi * δ * α k) / 2) * G (δ * (c * n / N)⁻¹)| ≤
      5 * c * ((Lu * BG + Bu * (2 * LG * Real.exp A ^ 2)) * trigOsc s a α) / N := by
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hLu0 : 0 ≤ Lu := by
    have := hLu 1 0; norm_num at this; linarith [abs_nonneg (invWindow h 1 - invWindow h 0)]
  have hLG0 : 0 ≤ LG := by
    have := hGL 1 0; norm_num at this; linarith [abs_nonneg (G 1 - G 0)]
  obtain ⟨D, hD⟩ : ∃ D, D = ⌈c⌉₊ := ⟨_, rfl⟩
  rw [← hD]
  have hDc : (D : ℝ) ≤ 2 * c := by
    rw [hD]; linarith [Nat.ceil_lt_add_one hc0.le]
  obtain ⟨Lf, hLf⟩ : ∃ Lf, Lf = Lu * BG + Bu * (2 * LG * Real.exp A ^ 2) := ⟨_, rfl⟩
  rw [← hLf]
  have hLf0 : 0 ≤ Lf := by rw [hLf]; positivity
  set f : ℤ → ℝ → ℝ := fun δ x => invWindow h x * G (δ * (c * x)⁻¹) with hf
  set ψ : ℤ → ℕ → ℝ := fun δ n => trigTwist s a α n * trigTwistZ s a α (n + δ) with hψ
  set C : ℤ → ℝ := fun δ => ∑ k ∈ s, a k ^ 2 * Real.cos (2 * Real.pi * δ * α k) / 2 with hCdef
  set Osc := trigOsc s a α with hOsc
  have hOsc0 : 0 ≤ Osc := trigOsc_nonneg s a α
  have hrw1 : ∀ n ∈ Icc 1 N, trigTwist s a α n * horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(D : ℤ)) D,
      trigTwistZ s a α (n + δ) * G (δ * (c * n / N)⁻¹) =
      ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, (N : ℝ)⁻¹ * (ψ δ n * f δ (n / N)) := fun n hn => by
    rw [horizonWeights_sq_eq h hN (Finset.mem_Icc.mp hn).1, mul_sum]
    refine sum_congr rfl fun δ _ => ?_
    simp only [hψ, hf]
    rw [show c * n / N = c * (n / N) by ring]
    ring
  have hrw2 : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(D : ℤ)) D,
      (∑ k ∈ s, a k ^ 2 * Real.cos (2 * Real.pi * δ * α k) / 2) * G (δ * (c * n / N)⁻¹) =
      ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, (N : ℝ)⁻¹ * (C δ * f δ (n / N)) := fun n hn => by
    rw [horizonWeights_sq_eq h hN (Finset.mem_Icc.mp hn).1, mul_sum]
    refine sum_congr rfl fun δ _ => ?_
    simp only [hf, hCdef]
    rw [show c * n / N = c * (n / N) by ring]
    ring
  rw [sum_congr rfl hrw1, sum_congr rfl hrw2, Finset.sum_comm, Finset.sum_comm (s := Icc 1 N),
    ← sum_sub_distrib]
  have hδ : ∀ δ ∈ Finset.Icc (-(D : ℤ)) D,
      |∑ n ∈ Icc 1 N, (N : ℝ)⁻¹ * (ψ δ n * f δ (n / N)) -
        ∑ n ∈ Icc 1 N, (N : ℝ)⁻¹ * (C δ * f δ (n / N))| ≤
      (N : ℝ)⁻¹ * (Lf * Osc) := fun δ hδ => by
    have hδ' : |(δ : ℝ)| ≤ 2 * c := by
      have h1 := Finset.mem_Icc.mp hδ
      have : |(δ : ℝ)| ≤ D := by
        rw [abs_le]; constructor
        · have : ((-(D : ℤ) : ℤ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h1.1
          push_cast at this; linarith
        · exact_mod_cast h1.2
      linarith
    have hfL : ∀ x y, |f δ x - f δ y| ≤ Lf * |x - y| := fun x y => by
      rw [hLf]; exact abs_offsetProfile_sub_le hG hGL hBG hBu hLu hu0 hc0 hδ' x y
    have hf1 : f δ 1 = 0 := by simp only [hf]; rw [hu1, zero_mul]
    -- the product of two trigonometric twists: the diagonal autocorrelation plus oscillations
    have hpt : ∀ n : ℕ, ψ δ n - C δ = ∑ k ∈ s, ∑ l ∈ s, a k * a l / 2 *
        (Real.cos (2 * Real.pi * n * (α k + α l) + 2 * Real.pi * δ * α l) +
          if k = l then 0 else Real.cos (2 * Real.pi * n * (α k - α l) + -(2 * Real.pi * δ * α l))) := by
      intro n
      simp only [hψ, hCdef, trigTwist, trigTwistZ, freqTwist, freqTwistZ]
      rw [Finset.sum_mul_sum]
      have hC : ∑ k ∈ s, a k ^ 2 * Real.cos (2 * Real.pi * δ * α k) / 2 =
          ∑ k ∈ s, ∑ l ∈ s, if k = l then a k * a l * Real.cos (2 * Real.pi * δ * α l) / 2
            else 0 := by
        refine sum_congr rfl fun k hk => ?_
        rw [Finset.sum_ite_eq s k (fun l => a k * a l * Real.cos (2 * Real.pi * δ * α l) / 2),
          if_pos hk]
        ring
      rw [hC, ← Finset.sum_sub_distrib]
      refine sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine sum_congr rfl fun l _ => ?_
      push_cast
      have hc1 := Real.cos_add (2 * Real.pi * n * α k) (2 * Real.pi * (n + δ) * α l)
      have hc2 := Real.cos_sub (2 * Real.pi * n * α k) (2 * Real.pi * (n + δ) * α l)
      have e1 : 2 * Real.pi * n * (α k + α l) + 2 * Real.pi * δ * α l =
          2 * Real.pi * n * α k + 2 * Real.pi * (n + δ) * α l := by ring
      have e2 : 2 * Real.pi * n * (α k - α l) + -(2 * Real.pi * δ * α l) =
          2 * Real.pi * n * α k - 2 * Real.pi * (n + δ) * α l := by ring
      rw [e1, e2]
      split_ifs with hkl
      · subst hkl
        have e3 : 2 * Real.pi * n * α k - 2 * Real.pi * (n + δ) * α k = -(2 * Real.pi * δ * α k) := by
          ring
        rw [e3, Real.cos_neg] at hc2
        linear_combination (-(a k * a k / 2)) * hc1 - (a k * a k / 2) * hc2
      · linear_combination (-(a k * a l / 2)) * hc1 - (a k * a l / 2) * hc2
    have hsplit : ∑ n ∈ Icc 1 N, (N : ℝ)⁻¹ * (ψ δ n * f δ (n / N)) -
        ∑ n ∈ Icc 1 N, (N : ℝ)⁻¹ * (C δ * f δ (n / N)) =
        (N : ℝ)⁻¹ * ∑ k ∈ s, ∑ l ∈ s, a k * a l / 2 *
          ((∑ n ∈ Icc 1 N, Real.cos (2 * Real.pi * n * (α k + α l) + 2 * Real.pi * δ * α l) *
              f δ (n / N)) +
            if k = l then 0 else ∑ n ∈ Icc 1 N,
              Real.cos (2 * Real.pi * n * (α k - α l) + -(2 * Real.pi * δ * α l)) * f δ (n / N)) := by
      rw [← mul_sum, ← mul_sum, ← mul_sub, ← sum_sub_distrib]
      congr 1
      have : ∀ n ∈ Icc 1 N, ψ δ n * f δ (n / N) - C δ * f δ (n / N) =
          ∑ k ∈ s, ∑ l ∈ s, a k * a l / 2 *
            (Real.cos (2 * Real.pi * n * (α k + α l) + 2 * Real.pi * δ * α l) * f δ (n / N) +
              if k = l then 0 else
                Real.cos (2 * Real.pi * n * (α k - α l) + -(2 * Real.pi * δ * α l)) * f δ (n / N)) :=
        fun n _ => by
          rw [← sub_mul, hpt n, Finset.sum_mul]
          refine sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine sum_congr rfl fun l _ => ?_
          split_ifs <;> ring
      rw [sum_congr rfl this, Finset.sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine sum_congr rfl fun l _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      split_ifs
      · simp
      · rw [Finset.sum_add_distrib]
    rw [hsplit, abs_mul, abs_of_pos (inv_pos.mpr hN0)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hN0).le
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hOsc, trigOsc, Finset.mul_sum]
    refine sum_le_sum fun k hk => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine sum_le_sum fun l hl => ?_
    have hp := abs_sum_cos_mul_le (hsum k hk l hl) (2 * Real.pi * δ * α l) hfL hN
    rw [hf1, abs_zero, zero_add] at hp
    rw [abs_mul, abs_div, abs_mul, abs_two]
    have hab : 0 ≤ |a k| * |a l| / 2 := by positivity
    split_ifs with hkl
    · rw [add_zero, add_zero]
      calc |a k| * |a l| / 2 * |∑ n ∈ Icc 1 N, Real.cos (2 * Real.pi * n * (α k + α l) +
            2 * Real.pi * δ * α l) * f δ (n / N)|
          ≤ |a k| * |a l| / 2 * (Lf / |Real.sin (Real.pi * (α k + α l))|) :=
            mul_le_mul_of_nonneg_left hp hab
        _ = Lf * (|a k| * |a l| / 2 * (1 / |Real.sin (Real.pi * (α k + α l))|)) := by ring
    · have hm := abs_sum_cos_mul_le (hdiff k hk l hl hkl) (-(2 * Real.pi * δ * α l)) hfL hN
      rw [hf1, abs_zero, zero_add] at hm
      calc |a k| * |a l| / 2 * |∑ n ∈ Icc 1 N, Real.cos (2 * Real.pi * n * (α k + α l) +
            2 * Real.pi * δ * α l) * f δ (n / N) + ∑ n ∈ Icc 1 N,
              Real.cos (2 * Real.pi * n * (α k - α l) + -(2 * Real.pi * δ * α l)) * f δ (n / N)|
          ≤ |a k| * |a l| / 2 * (Lf / |Real.sin (Real.pi * (α k + α l))| +
              Lf / |Real.sin (Real.pi * (α k - α l))|) :=
            mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hp hm)) hab
        _ = Lf * (|a k| * |a l| / 2 * (1 / |Real.sin (Real.pi * (α k + α l))| +
              1 / |Real.sin (Real.pi * (α k - α l))|)) := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hδ).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc (-(D : ℤ)) D).card : ℝ) ≤ 5 * c := by
    rw [Int.card_Icc]
    have : ((D : ℤ) + 1 - -(D : ℤ)).toNat = 2 * D + 1 := by omega
    rw [this]
    push_cast
    linarith [Nat.ceil_lt_add_one hc0.le, hD ▸ (Nat.ceil_lt_add_one hc0.le)]
  calc ((Finset.Icc (-(D : ℤ)) D).card : ℝ) * ((N : ℝ)⁻¹ * (Lf * Osc))
      ≤ 5 * c * ((N : ℝ)⁻¹ * (Lf * Osc)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 5 * c * (Lf * Osc) / N := by ring

/-- **The energy of a trigonometric twist**: with distinct frequency classes,
`E_N = (2π/c) Σ_n y_n² Σ_{|δ| ≤ ⌈c⌉} (Σ_k a_k² ½cos(2πδα_k)) G(δ/a_n) + O(c/N)`. -/
theorem trigEnergy_le [DecidableEq ι] (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hsum : ∀ k ∈ s, ∀ l ∈ s, Real.sin (Real.pi * (α k + α l)) ≠ 0)
    (hdiff : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Real.sin (Real.pi * (α k - α l)) ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (trigTwist s a α) N) τ‖ ^ 2 / N)) -
        2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
          ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
            (∑ k ∈ s, a k ^ 2 * Real.cos (2 * Real.pi * δ * α k) / 2) *
              shellAutocorr φ (δ * (c * n / N)⁻¹)| ≤ K * c / N := by
  obtain ⟨Bk, Lk, hk, hkL⟩ := exists_bound_lipschitz (contDiff_taperedProfile hh)
    (A := A) fun y hy => taperedProfile_eq_zero hsupp hy
  have hG2 := contDiff_shellAutocorr hφ hφsupp
  have hG1 : ∀ t, 1 ≤ |t| → shellAutocorr φ t = 0 := fun t ht =>
    shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ht
  have hGc : HasCompactSupport (shellAutocorr φ) :=
    HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun t ht => by
      refine hG1 t ?_
      by_contra hlt
      exact ht (abs_le.mp (not_le.mp hlt).le)
  obtain ⟨BG, hBG⟩ := hGc.exists_bound_of_continuous hG2.continuous
  obtain ⟨LG, hLG⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGc hG2 (by norm_num)
  have hGb : ∀ t, |shellAutocorr φ t| ≤ |BG| := fun t =>
    (by simpa [Real.norm_eq_abs] using hBG t : |shellAutocorr φ t| ≤ BG).trans (le_abs_self _)
  have hGL : ∀ s t, |shellAutocorr φ s - shellAutocorr φ t| ≤ (LG : ℝ) * |s - t| := fun s t => by
    simpa [Real.dist_eq] using hLG.dist_le_mul s t
  have hkb : ∀ y, |taperedProfile h y| ≤ |Bk| := fun y => (hk y).trans (le_abs_self _)
  have hkL' : ∀ u v, |taperedProfile h u - taperedProfile h v| ≤ |Lk| * |u - v| := fun u v =>
    (hkL u v).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _))
  have hk0 : ∀ y, 0 < y → taperedProfile h y = 0 := fun y hy =>
    taperedProfile_eq_zero hsupp fun hm => by linarith [hm.2]
  obtain ⟨Bu, Lu, hBu0, hLu0, hBu, hLu, hu0⟩ := exists_invWindow_bounds hh hA hsupp
  have hu1 : invWindow h 1 = 0 := by
    obtain ⟨-, Lh0, -, hLh0⟩ := exists_bound_lipschitz hh hsupp
    rw [invWindow, sqWindow, if_pos one_pos, Real.log_one, horizon_zero_at_zero hsupp hLh0]
    simp
  obtain ⟨Mχ, hMχ⟩ : ∃ Mχ : ℝ, Mχ = ∑ k ∈ s, |a k| := ⟨_, rfl⟩
  have hMχ0 : 0 ≤ Mχ := by rw [hMχ]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hχb : ∀ n, |trigTwist s a α n| ≤ Mχ := fun n => hMχ ▸ abs_trigTwist_le s a α n
  have hχZb : ∀ z, |trigTwistZ s a α z| ≤ Mχ := fun z => hMχ ▸ abs_trigTwistZ_le s a α z
  obtain ⟨X, hX⟩ : ∃ X, X = 5 * (|Lk| * |BG| + 8 * |Bk| * (LG : ℝ)) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 5 * ((Lu * |BG| + Bu * (2 * (LG : ℝ) * Real.exp A ^ 2)) *
      trigOsc s a α) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    have := trigOsc_nonneg s a α
    positivity
  refine ⟨2 * Real.pi * (Mχ ^ 2 * |Bk| * X) + 2 * Real.pi * Q, by positivity,
    fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hxw : ∀ m, 1 ≤ m → horizonWeights h N m =
      taperedProfile h (Real.log m - Real.log N) / Real.sqrt N := fun m hm =>
    horizonWeights_eq_tapered h hN hm
  rw [atomEnergy_eq hφ hφsupp _ hc0 hN]
  set G := shellAutocorr φ with hGdef
  set tw := twistedWeights h (trigTwist s a α) N with htw
  set R : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 N, tw m * G (N * (Real.log m - Real.log n) / c) with hR
  set L : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 (2 * N), trigTwistZ s a α m *
    G (((m : ℝ) - n) * (c * n / N)⁻¹) with hL
  have hswap : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, tw m * tw n *
      G (N * (Real.log m - Real.log n) / c) = ∑ n ∈ Icc 1 N, tw n * R n := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun n _ => ?_
    simp only [hR]
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  rw [hswap]
  -- the rows
  set ε := X * c ^ 2 / (N * Real.sqrt N) with hε
  have hrows : |∑ n ∈ Icc 1 N, tw n * R n - ∑ n ∈ Icc 1 N, tw n * (horizonWeights h N n * L n)| ≤
      N * (Mχ * |Bk| / Real.sqrt N * (Mχ * ε)) :=
    abs_sum_mul_sub_sum_le fun n hn => by
      have hn1 := (Finset.mem_Icc.mp hn).1
      have hnN := (Finset.mem_Icc.mp hn).2
      have hr := abs_twistRow_sub_le hkb hkL' hGb hGL hG1 hk0 (abs_nonneg _) (abs_nonneg _)
        (NNReal.coe_nonneg _) (abs_nonneg _) hχZb hc hcN hn1 hnN
      have hRn : R n = ∑ m ∈ Icc 1 N, trigTwistZ s a α m *
          (taperedProfile h (Real.log m - Real.log N) / Real.sqrt N) *
            G (N * (Real.log m - Real.log n) / c) := by
        simp only [hR, htw]
        refine sum_congr rfl fun m hm => ?_
        rw [twistedWeights, hxw m (Finset.mem_Icc.mp hm).1, trigTwistZ_natCast]
        ring
      rw [← mul_sub, abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
      · simp only [htw]
        rw [twistedWeights, abs_mul, hxw n hn1, abs_div, abs_of_pos hsN, mul_comm, mul_div_assoc]
        exact mul_le_mul (hχb n) (div_le_div_of_nonneg_right (hkb _) hsN.le)
          (by positivity) hMχ0
      · rw [hRn, hxw n hn1]
        refine hr.trans (le_of_eq ?_)
        rw [hε, hX]
  -- the offsets
  have hoff : ∑ n ∈ Icc 1 N, tw n * (horizonWeights h N n * L n) =
      ∑ n ∈ Icc 1 N, trigTwist s a α n * horizonWeights h N n ^ 2 *
        ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, trigTwistZ s a α (n + δ) * G (δ * (c * n / N)⁻¹) := by
    refine sum_congr rfl fun n hn => ?_
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have ha0 : 0 < c * n / N := by positivity
    have hac : c * n / N ≤ c := by
      rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN hc0.le
    have han : 4 * (c * n / N) ≤ n := by
      rw [show 4 * (c * n / N) = 4 * c / N * n by ring]
      exact mul_le_of_le_one_left hn0.le ((div_le_one hN0).mpr hcN)
    have hDN : n + ⌈c⌉₊ ≤ 2 * N := by
      have : ⌈c⌉₊ ≤ N := Nat.ceil_le.mpr (by linarith)
      have : n ≤ N := (Finset.mem_Icc.mp hn).2
      omega
    have hL' : L n = ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        trigTwistZ s a α (n + δ) * G (δ * (c * n / N)⁻¹) :=
      sum_offset_eq hG1 (trigTwistZ s a α) ha0 han (hac.trans (Nat.le_ceil c)) hDN
    rw [hL']
    simp only [htw]
    rw [twistedWeights]
    ring
  have hoffeq := abs_offsetSum_trig_sub_le s a α hGb hGL (abs_nonneg _) hBu hLu hu0 hu1 hsum hdiff
    hc hN (G := G)
  rw [← hoff] at hoffeq
  have htot : |2 * Real.pi / c * ∑ n ∈ Icc 1 N, tw n * R n -
      2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
        ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, (∑ k ∈ s, a k ^ 2 * Real.cos (2 * Real.pi * δ * α k) / 2) *
          G (δ * (c * n / N)⁻¹)| ≤
      2 * Real.pi / c * (N * (Mχ * |Bk| / Real.sqrt N * (Mχ * ε)) +
        5 * c * ((Lu * |BG| + Bu * (2 * (LG : ℝ) * Real.exp A ^ 2)) *
          trigOsc s a α) / N) := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / c)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := abs_sub_le (∑ n ∈ Icc 1 N, tw n * R n)
      (∑ n ∈ Icc 1 N, tw n * (horizonWeights h N n * L n))
      (∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
        ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, (∑ k ∈ s, a k ^ 2 * Real.cos (2 * Real.pi * δ * α k) / 2) *
          G (δ * (c * n / N)⁻¹))
    linarith
  refine htot.trans ?_
  rw [hε]
  have e1 : 2 * Real.pi / c * (N * (Mχ * |Bk| / Real.sqrt N * (Mχ * (X * c ^ 2 /
      (N * Real.sqrt N))))) = 2 * Real.pi * (Mχ ^ 2 * |Bk| * X) * c / N := by
    field_simp
    rw [Real.sq_sqrt hN0.le]
    ring
  have e2 : 2 * Real.pi / c * (5 * c * ((Lu * |BG| + Bu * (2 * (LG : ℝ) * Real.exp A ^ 2)) *
      trigOsc s a α) / N) = 2 * Real.pi * Q / N := by
    rw [hQ]; field_simp
  rw [mul_add, e1, e2]
  have hQc : 2 * Real.pi * Q / N ≤ 2 * Real.pi * Q * c / N := by
    rw [div_le_div_iff_of_pos_right hN0]
    exact le_mul_of_one_le_right (by positivity) hc
  have : (2 * Real.pi * (Mχ ^ 2 * |Bk| * X) + 2 * Real.pi * Q) * c / N =
      2 * Real.pi * (Mχ ^ 2 * |Bk| * X) * c / N + 2 * Real.pi * Q * c / N := by ring
  linarith

/-- The spectral aliasing of a trigonometric twist, `Σ_k a_k² · ½(𝒜^{(u_k)} + 𝒜^{(1−u_k)})`. -/
def trigAlias (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ := ∑ k ∈ s, a k ^ 2 * freqAlias φ h (α k) c N

/-- **The energy of a trigonometric twist is the sum of its frequencies**. -/
theorem abs_trigEnergy_sub_le [DecidableEq ι] (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hsum : ∀ k ∈ s, ∀ l ∈ s, Real.sin (Real.pi * (α k + α l)) ≠ 0)
    (hdiff : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Real.sin (Real.pi * (α k - α l)) ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (trigTwist s a α) N) τ‖ ^ 2 / N)) -
        2 * Real.pi * trigAlias s a α φ h c N| ≤ K * c / N := by
  obtain ⟨K, hK0, hK⟩ := trigEnergy_le s a α hφ hφsupp hh hA hsupp hsum hdiff
  refine ⟨K, hK0, fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have e : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, (∑ k ∈ s, a k ^ 2 *
        Real.cos (2 * Real.pi * δ * α k) / 2) * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      ∑ k ∈ s, a k ^ 2 * (c / N * (h (Real.log n - Real.log N) ^ 2 *
        (twistDensity φ (Int.fract (α k)) (c * n / N) +
          twistDensity φ (1 - Int.fract (α k)) (c * n / N))) / 2) := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have ha0 : 0 < c * n / N := by positivity
    have haD : c * n / N ≤ ⌈c⌉₊ := by
      refine le_trans ?_ (Nat.le_ceil c)
      rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN hc0.le
    have hswap : ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, (∑ k ∈ s, a k ^ 2 *
        Real.cos (2 * Real.pi * δ * α k) / 2) * shellAutocorr φ (δ * (c * n / N)⁻¹) =
        ∑ k ∈ s, a k ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
          Real.cos (2 * Real.pi * δ * α k) / 2 * shellAutocorr φ (δ * (c * n / N)⁻¹) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun δ _ => by ring
    rw [hswap, Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_offset_freq_eq hφ hφsupp (α k) ha0 haD, horizonWeights, div_pow, Real.sq_sqrt hn0.le]
    field_simp
  have hmain : 2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, (∑ k ∈ s, a k ^ 2 *
        Real.cos (2 * Real.pi * δ * α k) / 2) * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      2 * Real.pi * trigAlias s a α φ h c N := by
    rw [sum_congr rfl e, Finset.sum_comm]
    unfold trigAlias freqAlias densityAlias
    rw [Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun n _ => ?_
    field_simp
  rw [← hmain]
  exact hK c hc N hcN

/-- **The horizon layer is graded by frequency.** For a trigonometric twist with distinct
frequency classes (`α_k + α_l ∉ ℤ`, and `α_k − α_l ∉ ℤ` for `k ≠ l`), along `c^{β+1}/log N → K`,
`c⁻¹⟨Wx, x⟩/∫g² → (βA_φ/(K∫φ²)) Σ_k a_k² · ½(ζ(β+1, u_k) + ζ(β+1, 1 − u_k)) ∫ e^{−(β+1)y} H²`,
`u_k = {α_k}`. -/
theorem trigTwist_layer_criticalCurve [DecidableEq ι] (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    (hsum : ∀ k ∈ s, ∀ l ∈ s, Real.sin (Real.pi * (α k + α l)) ≠ 0)
    (hdiff : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Real.sin (Real.pi * (α k - α l)) ≠ 0) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (trigTwist s a α) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (β * Aφ / (K * ∫ u, φ u ^ 2) *
        (∑ k ∈ s, a k ^ 2 * ((hurwitzSum (β + 1) (Int.fract (α k)) +
          hurwitzSum (β + 1) (1 - Int.fract (α k))) / 2)) *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog, -⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  have hsin : ∀ k ∈ s, Real.sin (Real.pi * α k) ≠ 0 := fun k hk =>
    sin_pi_ne_zero_of_two (by rw [show 2 * α k = α k + α k by ring]; exact hsum k hk k hk)
  have hu0 : ∀ k ∈ s, 0 < Int.fract (α k) := fun k hk => fract_pos_of_sin (hsin k hk)
  -- a common lower bound for the distances of the frequencies to the integers
  obtain ⟨m₀, hm₀0, hm₀1, hm⟩ : ∃ m₀ : ℝ, 0 < m₀ ∧ m₀ ≤ 1 ∧
      ∀ k ∈ s, m₀ ≤ min (Int.fract (α k)) (1 - Int.fract (α k)) := by
    rcases s.eq_empty_or_nonempty with hs | hs
    · exact ⟨1, one_pos, le_rfl, fun k hk => by simp [hs] at hk⟩
    · obtain ⟨k₀, hk₀, hmin⟩ := s.exists_min_image
        (fun k => min (Int.fract (α k)) (1 - Int.fract (α k))) hs
      refine ⟨min (Int.fract (α k₀)) (1 - Int.fract (α k₀)),
        lt_min (hu0 k₀ hk₀) (by linarith [Int.fract_lt_one (α k₀)]),
        (min_le_right _ _).trans (by linarith [Int.fract_nonneg (α k₀)]), fun k hk => hmin k hk⟩
  have hAA' : A ≤ A - Real.log m₀ := by
    have := Real.log_nonpos hm₀0.le hm₀1
    linarith
  have hsharp := twisted_layer_sharp_of_energy_of_bounded hφ hφsupp hφ2 hq hCφ hdecay hh hA hsupp
    hc1 hcinf hclog (abs_trigTwist_le s a α) (abs_sum_range_trigTwist_le s a α hsin) hAA'
    (trigAlias s a α φ h) (abs_trigEnergy_sub_le s a α hφ hφsupp hh hA hsupp hsum hdiff)
    (exists_trigLow_energy_le s a α (by linarith : 0 ≤ q) hCφ hdecay hh hA hsupp hu0 hm₀0 hm₀1 hm)
  set I := ∫ y, Real.exp (-(β * y)) * h y ^ 2 with hI
  set M₀ := ∫ u, φ u ^ 2 with hM₀
  have hlim : ∀ v, 0 < v → v ≤ 1 → Tendsto (fun N : ℕ =>
      Real.log N * densityAlias (twistDensity φ v) h (c N) N) atTop
      (𝓝 (K⁻¹ * (Aφ * hurwitzSum (β + 1) v * (β * I)))) := fun v hv0 hv1 =>
    tendsto_log_mul_twistDensityAlias hφ hφsupp hq hCφ hdecay hβ hT hh hA hsupp hc1 hK hcrit hv0 hv1
  have hterm : Tendsto (fun N : ℕ => Real.log N / M₀ * trigAlias s a α φ h (c N) N) atTop
      (𝓝 (∑ k ∈ s, a k ^ 2 * (M₀⁻¹ * ((K⁻¹ * (Aφ * hurwitzSum (β + 1) (Int.fract (α k)) *
        (β * I)) + K⁻¹ * (Aφ * hurwitzSum (β + 1) (1 - Int.fract (α k)) * (β * I))) / 2)))) := by
    have := tendsto_finsetSum s fun k hk =>
      ((((hlim (Int.fract (α k)) (hu0 k hk) (Int.fract_lt_one _).le).add
        (hlim (1 - Int.fract (α k)) (by linarith [Int.fract_lt_one (α k)])
          (by linarith [hu0 k hk]))).div_const
          2).const_mul M₀⁻¹).const_mul (a k ^ 2)
    refine this.congr fun N => ?_
    unfold trigAlias freqAlias
    rw [Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  have := hsharp.add hterm
  rw [zero_add] at this
  have hH : ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2 = I := by
    rw [hI]; congr 1; funext y
    rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
      show Real.exp (-((β + 1) * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
        (Real.exp (-((β + 1) * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring,
      ← Real.exp_add]
    congr 2; push_cast; ring
  rw [hH]
  have hval : ∑ k ∈ s, a k ^ 2 * (M₀⁻¹ * ((K⁻¹ * (Aφ * hurwitzSum (β + 1) (Int.fract (α k)) *
      (β * I)) + K⁻¹ * (Aφ * hurwitzSum (β + 1) (1 - Int.fract (α k)) * (β * I))) / 2)) =
      β * Aφ / (K * M₀) * (∑ k ∈ s, a k ^ 2 * ((hurwitzSum (β + 1) (Int.fract (α k)) +
        hurwitzSum (β + 1) (1 - Int.fract (α k))) / 2)) * I := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun k _ => ?_
    field_simp
  rw [hval] at this
  refine this.congr fun N => ?_
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
