import GaloisForLFunctions.SurfaceOfSpecZ.TheOtherSideAtThePrimes

/-!
# The zero-free strip improves itself

Fix `k ≥ 1`. **Theorem** (`riemannHypothesis_iff_bddBelow_kthPrimePowers`): RH holds iff
`2 Re S(k log p) ≥ −K` at every prime `p`, a one-sided bound at the degrees `pᵏ` only (`S` the lag
structure of the cubic spline). For `k = 2` these are Bombieri's even extensions at the primes.

**The bootstrap** (`re_le_of_bddBelow_kthPrimePowers_step`). Let every zero have `Re ρ ≤ ½ + b`,
`0 ≤ b < ½`. The nonnegative series `Σ_p log p (2 Re S(k log p) + K + 1) p^{−s}` is
`−Σ_z e_z ζ'/ζ(s − kz) − (K + 1)ζ'/ζ(s)` minus a series holomorphic right of `½ + kb`
(`gdSeries_kCoeff_eq`). It continues to `Re s > ½ + (k + 1)b` off the poles `1 + kz`, since the
arguments `s − kz` stay right of the zeros (`differentiableAt_scaledLogDerivOf`); Landau's theorem puts
the abscissa at `max(1, ½ + (k + 1)b)`, and a zero of depth `b'` is a pole of real part `1 + kb'`. So
every zero has depth `≤ max(0, b − (½ − b)/k)` (up to any `η > 0`): the distance to `½` grows by the
factor `1 + 1/k`, and finitely many steps reach the line.

**The first strip.** The degrees `pᵏ` have gaps `x^{1 − 1/(3k)}` (`powGaps_kthPrimePowers`, from
Huxley's prime gaps), and the gap method from one side gives `Re ρ ≤ 1 − 1/(3k)`.

So the gap method only has to supply some zero-free strip; the multiplicative structure of the
degrees improves it to the line. In `TheStepanovCountAtThePrimeDegrees` one step sufficed because the
first strip was already `Re ρ ≤ 5/8 < ¾`.
-/

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open GaloisForLFunctions.HTGeometry ArithmeticFunction

/-! ### `ζ'/ζ` right of a zero-free strip, without an upper limit -/

/-- `|ζ'/ζ(w)| ≤ Σ Λ(n) n^{−2}` for `Re w ≥ 2`. -/
theorem norm_logDeriv_zeta_le_of_two_le {w : ℂ} (hw : 2 ≤ w.re) :
    ‖logDeriv riemannZeta w‖ ≤ ∑' j : ℕ, Λ (j + 1) * ((j : ℝ) + 1) ^ (-2 : ℝ) := by
  obtain ⟨hs, he⟩ := summable_tsum_vonMangoldt (w := w) (by linarith)
  have h2 : Summable fun j : ℕ => Λ (j + 1) * ((j : ℝ) + 1) ^ (-2 : ℝ) := by
    have h := (summable_tsum_vonMangoldt (w := (2 : ℂ)) (by norm_num)).1.norm
    refine h.congr fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    norm_num
  have hle : ∀ j : ℕ, ‖(Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-w)‖ ≤
      Λ (j + 1) * ((j : ℝ) + 1) ^ (-2 : ℝ) := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) j]) ?_) vonMangoldt_nonneg
    simp only [Complex.neg_re]; linarith
  calc ‖logDeriv riemannZeta w‖ = ‖∑' j : ℕ, (Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-w)‖ := by
        rw [he, norm_neg]
    _ ≤ ∑' j : ℕ, ‖(Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-w)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ _ := Summable.tsum_le_tsum hle hs.norm h2

/-- If every zero has `Re ρ ≤ β₀`, then `|ζ'/ζ(w)| ≤ C |Im w|` for `Re w ≥ β₀ + δ`, `|Im w| ≥ 4`. -/
theorem exists_norm_logDeriv_zeta_le_of_re_le'' {β₀ δ : ℝ} (hβ : 1 / 2 ≤ β₀ + δ) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ β₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, β₀ + δ ≤ w.re → 4 ≤ |w.im| →
      ‖logDeriv riemannZeta w‖ ≤ C * |w.im| := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_logDeriv_zeta_le_of_re_le' hβ hδ0 hδ1 hzf
  set C₂ := ∑' j : ℕ, Λ (j + 1) * ((j : ℝ) + 1) ^ (-2 : ℝ) with hC₂def
  have hC₂ : 0 ≤ C₂ := tsum_nonneg fun j => mul_nonneg vonMangoldt_nonneg (by positivity)
  refine ⟨C₁ + C₂, by positivity, fun w hw h4 => ?_⟩
  have him : 0 ≤ |w.im| := abs_nonneg _
  rcases le_total w.re 2 with h2 | h2
  · have := h₁ w hw h2 h4
    nlinarith [mul_nonneg hC₂ him]
  · have h3 := norm_logDeriv_zeta_le_of_two_le h2
    have h5 : C₂ ≤ C₂ * |w.im| := le_mul_of_one_le_right hC₂ (by linarith)
    nlinarith [mul_nonneg hC₁ him]

/-! ### The scaled trace log-derivative -/

/-- `Σ_z c_z ζ'/ζ(s − kz)`. -/
def scaledLogDerivOf (k : ℕ) (c : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑' z : ℂ, c z * logDeriv riemannZeta (s - k * z)

/-- **Continuation of `Σ_z c_z ζ'/ζ(s − kz)`** to `Re s > ½ + (k + 1)b` off the poles `1 + kz`, when
every zero has `Re ρ ≤ ½ + b`. -/
theorem differentiableAt_scaledLogDerivOf {k : ℕ} (hk : 1 ≤ k) {b : ℝ} (hb0 : 0 ≤ b)
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b)
    {c : ℂ → ℂ} (hc : ∀ z, ‖c z‖ ≤ ‖traceCoeff 3 z‖)
    {s₀ : ℂ} (hs1 : 1 / 2 + (k + 1) * b < s₀.re)
    (hpole : ∀ z, c z ≠ 0 → s₀ ≠ 1 + k * z) :
    DifferentiableAt ℂ (scaledLogDerivOf k c) s₀ := by
  classical
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set m := s₀.re - (1 / 2 + (k + 1) * b) with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  set δ₀ := min (m / 2) 1 with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by linarith) one_pos
  have hδ₀1 : δ₀ ≤ 1 := min_le_right _ _
  have hδ₀m : δ₀ ≤ m / 2 := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_zeta_le_of_re_le'' (β₀ := 1 / 2 + b)
    (by linarith) hδ₀0 hδ₀1 hzf
  have hsupp : ∀ z, c z ≠ 0 → traceCoeff 3 z ≠ 0 := fun z hz h =>
    hz (norm_eq_zero.mp (le_antisymm ((hc z).trans (by rw [h, norm_zero])) (norm_nonneg _)))
  have hre : ∀ z, c z ≠ 0 → |z.re| ≤ b := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf (hsupp z hz)
  -- the poles near the horizontal line of `s₀`
  set F : Set ℂ := {z | c z ≠ 0 ∧ |(k : ℝ) * z.im - s₀.im| ≤ 5} with hFdef
  have hF : F.Finite := by
    refine (finite_traceCoeff_height 3 (|s₀.im| + 5)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hsupp z hz0, ?_⟩
    have hkz : |(k : ℝ) * z.im| ≤ |s₀.im| + 5 := by
      have := abs_le.mp hzim
      rw [abs_le]; constructor <;> linarith [neg_abs_le s₀.im, le_abs_self s₀.im]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)] at hkz
    calc |z.im| ≤ k * |z.im| := le_mul_of_one_le_left (abs_nonneg _) hk'
      _ ≤ _ := hkz
  obtain ⟨δ, hδ0, hδ1, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ F, δ ≤ ‖s₀ - (1 + k * z)‖ := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · exact ⟨1, one_pos, le_rfl, by simp [hFe]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hF.toFinset.exists_min_image (fun z => ‖s₀ - (1 + k * z)‖)
        (by simpa using hFne)
      have hz₁' := hF.mem_toFinset.mp hz₁
      refine ⟨min 1 ‖s₀ - (1 + k * z₁)‖,
        lt_min one_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hpole z₁ hz₁'.1))),
        min_le_left _ _, fun z hz => (min_le_right _ _).trans (hmin z (hF.mem_toFinset.mpr hz))⟩
  set ε := min (δ / 2) (m / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by linarith)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεm : ε ≤ m / 2 := min_le_right _ _
  -- on the closed ball every argument `s − kz` lies right of the zeros and off `1`
  have hstrip : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε, 1 / 2 + b + δ₀ ≤ (s - k * z).re := by
    intro z hz s hs
    have hs' : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs
    have hre' : |s.re - s₀.re| ≤ ε := (Complex.abs_re_le_norm (s - s₀)).trans (by simpa using hs')
    have h1 := abs_le.mp hre'
    have h2 := abs_le.mp (hre z hz)
    have hkz : (k : ℝ) * z.re ≤ k * b := mul_le_mul_of_nonneg_left h2.2 (by positivity)
    simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
      sub_zero]
    nlinarith
  have hfar : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε, s - k * z ≠ 1 := by
    intro z hz s hs h
    have hs' : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs
    by_cases hzF : z ∈ F
    · have h1 := hδF z hzF
      have h2 : s₀ - (1 + k * z) = s₀ - s := by rw [← h]; ring
      rw [h2, norm_sub_rev] at h1
      linarith
    · have him : s.im = k * z.im := by
        have := congrArg Complex.im h
        simp at this; linarith
      have h3 : |s.im - s₀.im| ≤ ε := (Complex.abs_im_le_norm (s - s₀)).trans (by simpa using hs')
      apply hzF
      refine ⟨hz, ?_⟩
      rw [← him]
      linarith
  have hζne : ∀ z, c z ≠ 0 → ∀ s ∈ Metric.closedBall s₀ ε, riemannZeta (s - k * z) ≠ 0 :=
    fun z hz s hs => riemannZeta_ne_zero_of_re_gt (by linarith) hzf
      (by linarith [hstrip z hz s hs])
  -- bounds for the finitely many nearby terms
  have hM : ∀ z ∈ F, ∃ M : ℝ, ∀ s ∈ Metric.closedBall s₀ ε,
      ‖logDeriv riemannZeta (s - k * z)‖ ≤ M := by
    intro z hz
    have hcont : ContinuousOn (fun s => logDeriv riemannZeta (s - k * z))
        (Metric.closedBall s₀ ε) := by
      intro s hs
      have hd : DifferentiableAt ℂ (fun s => logDeriv riemannZeta (s - k * z)) s :=
        (differentiableAt_logDeriv_riemannZeta (hfar z hz.1 s hs) (hζne z hz.1 s hs)).comp s
          (differentiableAt_id.sub_const _)
      exact hd.continuousAt.continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_closedBall s₀ ε).exists_bound_of_continuousOn hcont
    exact ⟨M, hM⟩
  choose! M hMb using hM
  set K₀ : ℝ := |s₀.im| + 1 + k with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  set u : ℂ → ℝ := fun z => ‖c z‖ * (C * K₀ * (1 + |z.im|)) +
    (if z ∈ F then ‖c z‖ * |M z| else 0) with hu
  have hus : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
        ((summable_traceCoeff_mul_pow (N := 1) (le_refl 3) (by norm_num)).mul_left (C * K₀))
      calc ‖c z‖ * (C * K₀ * (1 + |z.im|))
          ≤ ‖traceCoeff 3 z‖ * (C * K₀ * (1 + |z.im|)) :=
            mul_le_mul_of_nonneg_right (hc z) (by positivity)
        _ = C * K₀ * (‖traceCoeff 3 z‖ * (1 + |z.im|) ^ 1) := by ring
    · exact summable_of_ne_finset_zero (s := hF.toFinset) fun z hz => by
        rw [Set.Finite.mem_toFinset] at hz; simp [hz]
  have hdiff : DifferentiableOn ℂ (scaledLogDerivOf k c) (Metric.ball s₀ ε) := by
    unfold scaledLogDerivOf
    refine differentiableOn_tsum_of_summable_norm hus (fun z => ?_) Metric.isOpen_ball
      (fun z s hs => ?_)
    · by_cases hz : c z = 0
      · simp only [hz, zero_mul]; exact differentiableOn_const _
      · intro s hs
        have hs' := Metric.ball_subset_closedBall hs
        exact ((differentiableAt_logDeriv_riemannZeta (hfar z hz s hs') (hζne z hz s hs')).comp s
          (differentiableAt_id.sub (differentiableAt_const _))).const_mul _
          |>.differentiableWithinAt
    · have hs' := Metric.ball_subset_closedBall hs
      have hsn : ‖s - s₀‖ ≤ ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at hs'
      by_cases hz : c z = 0
      · simp only [hz, zero_mul, norm_zero]
        exact add_nonneg (by positivity) (by split_ifs <;> positivity)
      by_cases hzF : z ∈ F
      · have h1 := hMb z hzF s hs'
        simp only [hu, if_pos hzF, norm_mul]
        have : ‖c z‖ * ‖logDeriv riemannZeta (s - k * z)‖ ≤ ‖c z‖ * |M z| :=
          mul_le_mul_of_nonneg_left (h1.trans (le_abs_self _)) (norm_nonneg _)
        have h0 : 0 ≤ ‖c z‖ * (C * K₀ * (1 + |z.im|)) := by positivity
        linarith
      · have hzF' : 5 < |(k : ℝ) * z.im - s₀.im| := by
          by_contra h; exact hzF ⟨hz, not_lt.mp h⟩
        have hst := hstrip z hz s hs'
        set w := s - k * z with hw
        have hwim : w.im = s.im - k * z.im := by simp [hw]
        have him : |s.im - s₀.im| ≤ ε :=
          (Complex.abs_im_le_norm (s - s₀)).trans (by simpa using hsn)
        have hε1 : ε ≤ 1 / 2 := by linarith
        have ht : 4 ≤ |w.im| := by
          rw [hwim]
          have := abs_le.mp him
          rcases le_or_gt 0 ((k : ℝ) * z.im - s₀.im) with h | h
          · rw [abs_of_nonneg h] at hzF'
            rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_neg h] at hzF'
            rw [abs_of_pos (by linarith)]; linarith
        have hbound := hC w hst ht
        have hwle : |w.im| ≤ K₀ * (1 + |z.im|) := by
          rw [hwim]
          have h2 : |(k : ℝ) * z.im| = k * |z.im| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
          have hs_im : |s.im| ≤ |s₀.im| + ε := by
            calc |s.im| = |(s.im - s₀.im) + s₀.im| := by ring_nf
              _ ≤ |s.im - s₀.im| + |s₀.im| := abs_add_le _ _
              _ ≤ |s₀.im| + ε := by linarith
          calc |s.im - k * z.im| ≤ |s.im| + |(k : ℝ) * z.im| := abs_sub _ _
            _ ≤ (|s₀.im| + 1) + k * |z.im| := by rw [h2]; linarith
            _ ≤ K₀ * (1 + |z.im|) := by
                rw [hK₀]; nlinarith [abs_nonneg z.im, abs_nonneg s₀.im]
        simp only [hu, if_neg hzF, add_zero, norm_mul]
        calc ‖c z‖ * ‖logDeriv riemannZeta w‖ ≤ ‖c z‖ * (C * |w.im|) :=
              mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
          _ ≤ ‖c z‖ * (C * (K₀ * (1 + |z.im|))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle hC0) (norm_nonneg _)
          _ = ‖c z‖ * (C * K₀ * (1 + |z.im|)) := by ring
  exact hdiff.differentiableAt (Metric.ball_mem_nhds _ hε0)

/-- **Pointwise convergence** of `Σ_z c_z ζ'/ζ(s − kz)` for `Re s > ½ + (k + 1)b`. -/
theorem summable_scaledLogDerivOf_terms {k : ℕ} (hk : 1 ≤ k) {b : ℝ} (hb0 : 0 ≤ b)
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b)
    {c : ℂ → ℂ} (hc : ∀ z, ‖c z‖ ≤ ‖traceCoeff 3 z‖)
    {s : ℂ} (hs1 : 1 / 2 + (k + 1) * b < s.re) :
    Summable fun z => c z * logDeriv riemannZeta (s - k * z) := by
  classical
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set m := s.re - (1 / 2 + (k + 1) * b) with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  set δ₀ := min m 1 with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min hm0 one_pos
  have hδ₀m : δ₀ ≤ m := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_zeta_le_of_re_le'' (β₀ := 1 / 2 + b)
    (by linarith) hδ₀0 (min_le_right _ _) hzf
  have hsupp : ∀ z, c z ≠ 0 → traceCoeff 3 z ≠ 0 := fun z hz h =>
    hz (norm_eq_zero.mp (le_antisymm ((hc z).trans (by rw [h, norm_zero])) (norm_nonneg _)))
  set F : Set ℂ := {z | c z ≠ 0 ∧ |(k : ℝ) * z.im - s.im| < 4} with hFdef
  have hF : F.Finite := by
    refine (finite_traceCoeff_height 3 (|s.im| + 4)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hsupp z hz0, ?_⟩
    have hkz : |(k : ℝ) * z.im| ≤ |s.im| + 4 := by
      have := abs_le.mp hzim.le
      rw [abs_le]; constructor <;> linarith [neg_abs_le s.im, le_abs_self s.im]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)] at hkz
    calc |z.im| ≤ k * |z.im| := le_mul_of_one_le_left (abs_nonneg _) hk'
      _ ≤ _ := hkz
  set K₀ : ℝ := |s.im| + k with hK₀
  set u : ℂ → ℝ := fun z => ‖c z‖ * (C * K₀ * (1 + |z.im|)) +
    (if z ∈ F then ‖c z * logDeriv riemannZeta (s - k * z)‖ else 0) with hu
  have hus : Summable u := by
    refine Summable.add ?_ ?_
    · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
        ((summable_traceCoeff_mul_pow (N := 1) (le_refl 3) (by norm_num)).mul_left (C * K₀))
      calc ‖c z‖ * (C * K₀ * (1 + |z.im|))
          ≤ ‖traceCoeff 3 z‖ * (C * K₀ * (1 + |z.im|)) :=
            mul_le_mul_of_nonneg_right (hc z) (by positivity)
        _ = C * K₀ * (‖traceCoeff 3 z‖ * (1 + |z.im|) ^ 1) := by ring
    · exact summable_of_ne_finset_zero (s := hF.toFinset) fun z hz => by
        rw [Set.Finite.mem_toFinset] at hz; simp [hz]
  refine Summable.of_norm_bounded hus fun z => ?_
  by_cases hz : c z = 0
  · simp only [hz, zero_mul, norm_zero]
    exact add_nonneg (by positivity) (by split_ifs <;> positivity)
  by_cases hzF : z ∈ F
  · simp only [hu, if_pos hzF]
    have h0 : 0 ≤ ‖c z‖ * (C * K₀ * (1 + |z.im|)) := by positivity
    linarith
  have hzF' : 4 ≤ |(k : ℝ) * z.im - s.im| := by
    by_contra h; exact hzF ⟨hz, not_le.mp h⟩
  have hre := abs_le.mp (abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf (hsupp z hz))
  set w := s - k * z with hw
  have hwim : w.im = s.im - k * z.im := by simp [hw]
  have hwre : w.re = s.re - k * z.re := by simp [hw]
  have ht : 4 ≤ |w.im| := by rw [hwim, abs_sub_comm]; exact hzF'
  have hkz : (k : ℝ) * z.re ≤ k * b := mul_le_mul_of_nonneg_left hre.2 (by positivity)
  have hbound := hC w (by rw [hwre]; nlinarith) ht
  have hwle : |w.im| ≤ K₀ * (1 + |z.im|) := by
    rw [hwim]
    have h2 : |(k : ℝ) * z.im| = k * |z.im| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
    calc |s.im - k * z.im| ≤ |s.im| + |(k : ℝ) * z.im| := abs_sub _ _
      _ = |s.im| + k * |z.im| := by rw [h2]
      _ ≤ K₀ * (1 + |z.im|) := by rw [hK₀]; nlinarith [abs_nonneg z.im, abs_nonneg s.im]
  simp only [hu, if_neg hzF, add_zero, norm_mul]
  calc ‖c z‖ * ‖logDeriv riemannZeta w‖ ≤ ‖c z‖ * (C * |w.im|) :=
        mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ ≤ ‖c z‖ * (C * (K₀ * (1 + |z.im|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle hC0) (norm_nonneg _)
    _ = ‖c z‖ * (C * K₀ * (1 + |z.im|)) := by ring

/-! ### The series at the degrees `pᵏ` -/

/-- The coefficients `Λ(n)(2 Re S(k log n) + K + 1)` at `n = j + 1`. -/
def kCoeff (k : ℕ) (K : ℝ) (j : ℕ) : ℝ :=
  Λ (j + 1) * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log (j + 1))).re + K + 1)

/-- The same coefficients at the primes. -/
def kPrimeCoeff (k : ℕ) (K : ℝ) (j : ℕ) : ℝ :=
  primeWeight j *
    (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log (j + 1))).re + K + 1)

/-- The same coefficients at the higher prime powers. -/
def kHigherCoeff (k : ℕ) (K : ℝ) (j : ℕ) : ℝ :=
  higherWeight j *
    (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log (j + 1))).re + K + 1)

theorem kPrimeCoeff_add_kHigherCoeff (k : ℕ) (K : ℝ) (j : ℕ) :
    kPrimeCoeff k K j + kHigherCoeff k K j = kCoeff k K j := by
  unfold kPrimeCoeff kHigherCoeff kCoeff
  rw [← primeWeight_add_higherWeight]; ring

/-- The candidate continuation `−Σ_z e_z ζ'/ζ(s − kz) − (K + 1) ζ'/ζ(s)`. -/
def kZeta (k : ℕ) (K : ℝ) (s : ℂ) : ℂ :=
  -scaledLogDerivOf k (traceCoeff 3) s - ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s

/-- `|2 Re S(k log n) + K + 1| ≤ (E + |K| + 1) n^{kb}` once every exponent has `|Re z| ≤ b`. -/
theorem abs_kTrace_add_le (k : ℕ) {b : ℝ} (hb0 : 0 ≤ b)
    (hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b) (K : ℝ) (j : ℕ) :
    |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log (j + 1))).re + K + 1| ≤
      ((∑' z : ℂ, ‖traceCoeff 3 z‖) + |K| + 1) * ((j : ℝ) + 1) ^ (k * b) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hv : 0 ≤ (k : ℝ) * Real.log ((j : ℝ) + 1) := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hj1)
  have habs := abs_two_re_lagStructure_le_of_width hw hv
  have hexp : Real.exp (b * ((k : ℝ) * Real.log ((j : ℝ) + 1))) = ((j : ℝ) + 1) ^ (k * b) := by
    rw [Real.rpow_def_of_pos hj0]; ring_nf
  rw [hexp] at habs
  have hp1 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ (k * b) := Real.one_le_rpow hj1 (by positivity)
  have h2 := mul_le_mul_of_nonneg_left hp1 (by linarith [abs_nonneg K] : (0 : ℝ) ≤ |K| + 1)
  have h3 := abs_add_le (2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
    ((k : ℝ) * Real.log ((j : ℝ) + 1))).re + K) 1
  have h4 := abs_add_le (2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
    ((k : ℝ) * Real.log ((j : ℝ) + 1))).re) K
  rw [abs_one] at h3
  nlinarith

/-- **The traces at the degrees `nᵏ`, weighted by `Λ(n)`, have the Dirichlet series
`−Σ_z e_z ζ'/ζ(s − kz) − (K + 1)ζ'/ζ(s)`.** -/
theorem gdSeries_kCoeff_eq {k : ℕ} {b : ℝ} (hb0 : 0 ≤ b)
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b) (K : ℝ) {s : ℂ}
    (hs : 1 + k * b < s.re) :
    gdSeries (kCoeff k K) powerFreq s = kZeta k K s := by
  have hb := contDiff_boxSpline_two (le_refl 3)
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  set e := traceCoeff 3 with he
  have hE : Summable fun z => ‖e z‖ := by
    have h0 := (two_re_lagStructure_eq zetaZeroConfig hZ hb hbs 0).1.norm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0
  have hw : ∀ z, e z ≠ 0 → |z.re| ≤ b := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
  set σ' := s.re - k * b with hσ'
  have hσ'1 : 1 < σ' := by rw [hσ']; linarith
  have hΛ : Summable fun j : ℕ => Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ') := by
    have h := (summable_tsum_vonMangoldt (w := (σ' : ℂ)) (by simpa using hσ'1)).1.norm
    refine h.congr fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    simp
  set f : ℕ → ℂ → ℂ := fun j z =>
    (Λ (j + 1) : ℂ) * (e z * ((j : ℂ) + 1) ^ (-(s - k * z))) with hf
  have hfn : ∀ j z, ‖f j z‖ ≤ Λ (j + 1) * ((j : ℝ) + 1) ^ (-σ') * ‖e z‖ := by
    intro j z
    by_cases hz : e z = 0
    · simp [hf, hz]
    have hre := (abs_le.mp (hw z hz)).2
    have hkz : (k : ℝ) * z.re ≤ k * b := mul_le_mul_of_nonneg_left hre (by positivity)
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    have hexp : ((j : ℝ) + 1) ^ (-(s - k * z)).re ≤ ((j : ℝ) + 1) ^ (-σ') := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j])
      simp only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, zero_mul, sub_zero]
      rw [hσ']; linarith
    have hΛ0 := vonMangoldt_nonneg (n := j + 1)
    calc Λ (j + 1) * (‖e z‖ * ((j : ℝ) + 1) ^ (-(s - k * z)).re)
        ≤ Λ (j + 1) * (‖e z‖ * ((j : ℝ) + 1) ^ (-σ')) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) hΛ0
      _ = _ := by ring
  have hprod : Summable fun p : ℕ × ℂ => Λ (p.1 + 1) * ((p.1 : ℝ) + 1) ^ (-σ') * ‖e p.2‖ :=
    hΛ.mul_of_nonneg hE (fun j => mul_nonneg vonMangoldt_nonneg (by positivity))
      (fun _ => norm_nonneg _)
  have hF : Summable (Function.uncurry f) := Summable.of_norm_bounded hprod fun p => hfn p.1 p.2
  have hFp : Summable fun j => ∑' z, f j z := hF.prod
  -- the fibres over `j`
  have hj : ∀ j : ℕ, ∑' z, f j z = (Λ (j + 1) : ℂ) *
      (((2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log (j + 1))).re : ℝ) : ℂ) *
        ((j : ℂ) + 1) ^ (-s)) := by
    intro j
    simp only [hf]
    rw [tsum_mul_left]
    congr 1
    rw [(two_re_lagStructure_eq zetaZeroConfig hZ hb hbs (k * Real.log (j + 1))).2,
      ← tsum_mul_right]
    refine tsum_congr fun z => ?_
    rw [natCast_add_one_cpow_eq, natCast_add_one_cpow_eq, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  -- the fibres over `z`
  have hz : ∀ z : ℂ, ∑' j, f j z = e z * (-logDeriv riemannZeta (s - k * z)) := by
    intro z
    by_cases hz0 : e z = 0
    · simp [hf, hz0]
    have hre := (abs_le.mp (hw z hz0)).2
    have hkz : (k : ℝ) * z.re ≤ k * b := mul_le_mul_of_nonneg_left hre (by positivity)
    have hres : 1 < (s - k * z).re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
        sub_zero]
      linarith
    obtain ⟨-, hsum⟩ := summable_tsum_vonMangoldt hres
    rw [← hsum, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hf]; ring
  have hkb : 0 ≤ (k : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb0
  obtain ⟨hKs, hKe⟩ := summable_tsum_vonMangoldt (w := s) (by linarith)
  have hterm : ∀ j : ℕ, ((kCoeff k K j : ℝ) : ℂ) * Complex.exp (-(s * (powerFreq j : ℂ))) =
      ∑' z, f j z + ((K + 1 : ℝ) : ℂ) * ((Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-s)) := by
    intro j
    rw [hj, cexp_neg_mul_powerFreq, kCoeff]
    push_cast
    ring
  unfold gdSeries kZeta scaledLogDerivOf
  calc ∑' j : ℕ, ((kCoeff k K j : ℝ) : ℂ) * Complex.exp (-(s * (powerFreq j : ℂ)))
      = ∑' j : ℕ, (∑' z, f j z + ((K + 1 : ℝ) : ℂ) * ((Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-s))) :=
        tsum_congr hterm
    _ = ∑' j : ℕ, ∑' z, f j z +
          ((K + 1 : ℝ) : ℂ) * ∑' j : ℕ, (Λ (j + 1) : ℂ) * ((j : ℂ) + 1) ^ (-s) := by
        rw [hFp.tsum_add (hKs.mul_left _), tsum_mul_left]
    _ = ∑' z, ∑' j, f j z + ((K + 1 : ℝ) : ℂ) * (-logDeriv riemannZeta s) := by
        rw [← hF.tsum_comm, hKe]
    _ = ∑' z, e z * (-logDeriv riemannZeta (s - k * z)) +
          ((K + 1 : ℝ) : ℂ) * (-logDeriv riemannZeta s) := by
        rw [tsum_congr hz]
    _ = -∑' z, e z * logDeriv riemannZeta (s - k * z) -
          ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s := by
        simp only [mul_neg, tsum_neg]; ring

/-- The candidate continuation is holomorphic on a ball around every non-pole `s₀` with
`Re s₀ > max(1, ½ + (k + 1)b)`. -/
theorem exists_ball_differentiableOn_kZeta {k : ℕ} (hk : 1 ≤ k) {b : ℝ} (hb0 : 0 ≤ b)
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b) (K : ℝ)
    {s₀ : ℂ} (hs1 : 1 < s₀.re) (hs2 : 1 / 2 + (k + 1) * b < s₀.re)
    (hpole : ∀ z, traceCoeff 3 z ≠ 0 → s₀ ≠ 1 + k * z) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (kZeta k K) (ball s₀ ρ) := by
  classical
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set P : Set ℂ := {z | traceCoeff 3 z ≠ 0 ∧ |(k : ℝ) * z.im - s₀.im| ≤ 1} with hPdef
  have hP : P.Finite := by
    refine (finite_traceCoeff_height 3 (|s₀.im| + 1)).subset fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := hz
    refine ⟨hz0, ?_⟩
    have hkz : |(k : ℝ) * z.im| ≤ |s₀.im| + 1 := by
      have := abs_le.mp hzim
      rw [abs_le]; constructor <;> linarith [neg_abs_le s₀.im, le_abs_self s₀.im]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)] at hkz
    calc |z.im| ≤ k * |z.im| := le_mul_of_one_le_left (abs_nonneg _) hk'
      _ ≤ _ := hkz
  obtain ⟨δ, hδ0, hδ1, hδP⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z ∈ P, δ ≤ ‖s₀ - (1 + k * z)‖ := by
    rcases P.eq_empty_or_nonempty with hPe | hPne
    · exact ⟨1, one_pos, le_rfl, by simp [hPe]⟩
    · obtain ⟨z₁, hz₁, hmin⟩ := hP.toFinset.exists_min_image (fun z => ‖s₀ - (1 + k * z)‖)
        (by simpa using hPne)
      have hz₁' := hP.mem_toFinset.mp hz₁
      refine ⟨min 1 ‖s₀ - (1 + k * z₁)‖,
        lt_min one_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hpole z₁ hz₁'.1))),
        min_le_left _ _, fun z hz => (min_le_right _ _).trans (hmin z (hP.mem_toFinset.mpr hz))⟩
  set ρ := min δ (min (s₀.re - 1) (s₀.re - (1 / 2 + (k + 1) * b))) / 2 with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]; exact half_pos (lt_min hδ0 (lt_min (by linarith) (by linarith)))
  have hρδ : ρ < δ := by
    rw [hρdef]; have := min_le_left δ (min (s₀.re - 1) (s₀.re - (1 / 2 + (k + 1) * b))); linarith
  have hρ1 : ρ < s₀.re - 1 := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (s₀.re - (1 / 2 + (k + 1) * b)))).trans
      (min_le_left _ _)
    linarith
  have hρ2 : ρ < s₀.re - (1 / 2 + (k + 1) * b) := by
    rw [hρdef]
    have := (min_le_right δ (min (s₀.re - 1) (s₀.re - (1 / 2 + (k + 1) * b)))).trans
      (min_le_right _ _)
    linarith
  refine ⟨ρ, hρ0, fun s hs => ?_⟩
  rw [mem_ball, dist_eq_norm] at hs
  have hre : |s.re - s₀.re| < ρ :=
    lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀)) hs
  have him : |s.im - s₀.im| < ρ :=
    lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (s - s₀)) hs
  have hs1' : 1 < s.re := by linarith [(abs_lt.mp hre).1]
  have hs2' : 1 / 2 + (k + 1) * b < s.re := by linarith [(abs_lt.mp hre).1]
  have hnp : ∀ z, traceCoeff 3 z ≠ 0 → s ≠ 1 + k * z := by
    intro z hz h
    have hzim : s.im = k * z.im := by have := congrArg Complex.im h; simp at this; linarith
    have hzP : z ∈ P := ⟨hz, by rw [← hzim]; linarith [abs_lt.mp him, hδ1, hρδ]⟩
    have h1 := hδP z hzP
    rw [← h, norm_sub_rev] at h1
    linarith
  have h1 := differentiableAt_scaledLogDerivOf hk hb0 hzf (c := traceCoeff 3) (fun _ => le_rfl)
    hs2' hnp
  have hs1ne : s ≠ 1 := fun h => by rw [h] at hs1'; simp at hs1'
  have h2 := differentiableAt_logDeriv_riemannZeta hs1ne
    (riemannZeta_ne_zero_of_one_le_re hs1'.le)
  exact (h1.neg.sub (h2.const_mul _)).differentiableWithinAt

/-- **The correction over the higher prime powers is holomorphic** right of `½ + kb + η`. -/
theorem differentiableOn_gdSeries_kHigherCoeff {k : ℕ} {b : ℝ} (hb0 : 0 ≤ b)
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b) (K : ℝ) {η : ℝ} (hη : 0 < η) :
    DifferentiableOn ℂ (gdSeries (kHigherCoeff k K) powerFreq)
      {s | 1 / 2 + k * b + η < s.re} := by
  have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
  set E := ∑' z : ℂ, ‖traceCoeff 3 z‖ with hE
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  have hsum := (summable_higherWeight (σ := 1 / 2 + η) (by linarith)).mul_left (E + |K| + 1)
  unfold gdSeries
  refine differentiableOn_tsum_of_summable_norm hsum (fun j => ?_)
    (isOpen_lt continuous_const Complex.continuous_re) (fun j s hs => ?_)
  · exact ((differentiable_id.mul_const _).neg.cexp.const_mul _).differentiableOn
  · have hs' : 1 / 2 + k * b + η < s.re := hs
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, cexp_neg_mul_powerFreq,
      norm_natCast_add_one_cpow]
    have hre : (-s).re = -s.re := by simp
    rw [hre]
    have h1 : |kHigherCoeff k K j| ≤
        higherWeight j * ((E + |K| + 1) * ((j : ℝ) + 1) ^ (k * b)) := by
      unfold kHigherCoeff
      rw [abs_mul, abs_of_nonneg (higherWeight_nonneg j)]
      exact mul_le_mul_of_nonneg_left (abs_kTrace_add_le k hb0 hw K j) (higherWeight_nonneg j)
    have h2 : ((j : ℝ) + 1) ^ (-s.re) ≤ ((j : ℝ) + 1) ^ (-(1 / 2 + k * b + η)) :=
      Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
    have hc0 : 0 ≤ higherWeight j * ((E + |K| + 1) * ((j : ℝ) + 1) ^ (k * b)) :=
      mul_nonneg (higherWeight_nonneg j) (mul_nonneg (by linarith [abs_nonneg K]) (by positivity))
    calc |kHigherCoeff k K j| * ((j : ℝ) + 1) ^ (-s.re)
        ≤ higherWeight j * ((E + |K| + 1) * ((j : ℝ) + 1) ^ (k * b)) *
            ((j : ℝ) + 1) ^ (-(1 / 2 + k * b + η)) :=
          mul_le_mul h1 h2 (by positivity) hc0
      _ = (E + |K| + 1) * (higherWeight j *
            (((j : ℝ) + 1) ^ (k * b) * ((j : ℝ) + 1) ^ (-(1 / 2 + k * b + η)))) := by ring
      _ = (E + |K| + 1) * (higherWeight j * ((j : ℝ) + 1) ^ (-(1 / 2 + η))) := by
          rw [← Real.rpow_add hj0]; congr 3; ring

/-! ### One step of the bootstrap -/

/-- **One step of the bootstrap.** If every zero has `Re ρ ≤ ½ + b`, `0 ≤ b < ½`, and
`2 Re S(k log p) ≥ −K` at every prime, then every zero has
`Re ρ ≤ ½ + max(0, ((k + 1)b − ½ + η)/k)` for every `η > 0`. -/
theorem re_le_of_bddBelow_kthPrimePowers_step {k : ℕ} (hk : 1 ≤ k) {b : ℝ} (hb0 : 0 ≤ b)
    (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log p)).re)
    {η : ℝ} (hη : 0 < η) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + max 0 (((k + 1) * b - 1 / 2 + η) / k) := by
  classical
  intro ρ₁ hρ₁
  by_contra hρ₁re
  push Not at hρ₁re
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ b := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le hzf hz
  set L₁ : ℝ := 1 / 2 + (k + 1) * b + η with hL₁
  set A₀ : ℝ := 1 + k * b with hA₀
  have hkb : 0 ≤ (k : ℝ) * b := mul_nonneg hk0.le hb0
  set E := ∑' z : ℂ, ‖traceCoeff 3 z‖ with hE
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  -- the coefficients at the primes
  have hinner : ∀ j : ℕ, (j + 1).Prime → 1 ≤
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log ((j : ℝ) + 1))).re + K + 1 := by
    intro j hj
    have := hK (j + 1) hj
    push_cast at this
    linarith
  set B := kPrimeCoeff k K with hBdef
  have hge : ∀ j, primeWeight j ≤ B j := by
    intro j
    simp only [hBdef, kPrimeCoeff]
    by_cases hj : (j + 1).Prime
    · have h0 : 0 ≤ primeWeight j := primeWeight_nonneg j
      have := mul_le_mul_of_nonneg_left (hinner j hj) h0
      linarith
    · simp [primeWeight, hj]
  have hB : ∀ j, 0 ≤ B j := fun j => (primeWeight_nonneg j).trans (hge j)
  have hbound : ∀ (w : ℕ → ℝ), (∀ j, 0 ≤ w j) → (∀ j, w j ≤ Λ (j + 1)) → ∀ j,
      |w j * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log (j + 1))).re + K + 1)|
        ≤ (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (k * b)) := by
    intro w hw0 hwΛ j
    rw [abs_mul, abs_of_nonneg (hw0 j)]
    have h1 := abs_kTrace_add_le k hb0 hw K j
    calc w j * |2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
          ((k : ℝ) * Real.log ((j : ℝ) + 1))).re + K + 1|
        ≤ Λ (j + 1) * ((E + |K| + 1) * ((j : ℝ) + 1) ^ (k * b)) :=
          mul_le_mul (hwΛ j) h1 (abs_nonneg _) vonMangoldt_nonneg
      _ = _ := by ring
  have hbP : ∀ j, |kPrimeCoeff k K j| ≤ (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (k * b)) :=
    hbound primeWeight primeWeight_nonneg primeWeight_le
  have hbH : ∀ j, |kHigherCoeff k K j| ≤ (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (k * b)) :=
    hbound higherWeight higherWeight_nonneg higherWeight_le
  have hbA : ∀ j, |kCoeff k K j| ≤ (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (k * b)) :=
    hbound (fun j => Λ (j + 1)) (fun _ => vonMangoldt_nonneg) (fun _ => le_rfl)
  have hlam : ∀ j, 0 ≤ powerFreq j := powerFreq_nonneg
  have htw : ∀ σ j, gdTwistTerm B powerFreq σ 0 j = B j * ((j : ℝ) + 1) ^ (-σ) := by
    intro σ j; rw [gdTwistTerm, pow_zero, mul_one, real_exp_neg_mul_powerFreq]
  have hsumHigh : ∀ σ : ℝ, A₀ < σ → Summable (gdTwistTerm B powerFreq σ 0) := by
    intro σ hσ
    have h := summable_gdTerm_of_abs_le' hbP (s := (σ : ℂ)) (by simpa using hσ)
    refine (h.norm.congr fun j => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hB j),
      cexp_neg_mul_powerFreq, norm_natCast_add_one_cpow, htw]
    simp
  have hdivLow : ∀ σ : ℝ, σ ≤ 1 → ¬ Summable (gdTwistTerm B powerFreq σ 0) := by
    intro σ hσ hs
    apply not_summable_primeWeight_div
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (primeWeight_nonneg j) (by positivity))
      (fun j => ?_) hs
    rw [htw]
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    exact mul_le_mul (hge j) (Real.rpow_le_rpow_of_exponent_le hj1 (by linarith))
      (by positivity) (hB j)
  -- the abscissa
  set S : Set ℝ := {σ | Summable (gdTwistTerm B powerFreq σ 0)} with hSdef
  set S2 : ℝ := A₀ + 1 with hS2def
  have hS2 : S2 ∈ S := hsumHigh _ (by rw [hS2def]; linarith)
  have hSne : S.Nonempty := ⟨_, hS2⟩
  have hSbdd : BddBelow S := ⟨1, fun σ hσ => by
    by_contra h; exact hdivLow σ (le_of_lt (not_le.mp h)) hσ⟩
  set σc := sInf S with hσcdef
  have hsum : ∀ σ, σc < σ → Summable (gdTwistTerm B powerFreq σ 0) := by
    intro σ hσ
    obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hSne hσ
    exact summable_gdTwistTerm_of_le hB hlam hσ'S hlt.le
  have hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm B powerFreq σ 0) := fun σ hσ hs =>
    absurd (csInf_le hSbdd hs) (not_le.mpr hσ)
  have hσc2 : σc ≤ S2 := csInf_le hSbdd hS2
  -- analyticity
  have hgdAn : ∀ s : ℂ, σc < s.re → AnalyticAt ℂ (gdSeries B powerFreq) s := by
    intro s hs
    have hopen : IsOpen {w : ℂ | σc < w.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticAt (s := {w : ℂ | σc < w.re}) (fun w hw => ?_)
      (hopen.mem_nhds hs)
    have hw' : σc < w.re := hw
    exact (RHTower.differentiableAt_gdSeries hB hlam (hsum ((σc + w.re) / 2) (by linarith))
      (by linarith)).differentiableWithinAt
  set N : ℂ → ℂ := gdSeries (kHigherCoeff k K) powerFreq with hNdef
  have hN := differentiableOn_gdSeries_kHigherCoeff (k := k) hb0 hzf K (η := η / 2) (by linarith)
  have hNAn : ∀ s : ℂ, 1 / 2 + k * b + η / 2 < s.re → AnalyticAt ℂ N s := fun s hs =>
    hN.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  set G : ℂ → ℂ := fun s => kZeta k K s - N s with hGdef
  have hGball : ∀ s₀ : ℂ, 1 < s₀.re → L₁ < s₀.re →
      (∀ z, traceCoeff 3 z ≠ 0 → s₀ ≠ 1 + k * z) →
        ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ G (ball s₀ ρ) := by
    intro s₀ h1 h2 hp
    obtain ⟨ρ, hρ, hd⟩ := exists_ball_differentiableOn_kZeta hk hb0 hzf K h1 (by linarith) hp
    refine ⟨min ρ (s₀.re - L₁), lt_min hρ (by linarith), ?_⟩
    refine (hd.mono (ball_subset_ball (min_le_left _ _))).sub (hN.mono fun s hs => ?_)
    rw [mem_ball, dist_eq_norm] at hs
    have hre : |s.re - s₀.re| < s₀.re - L₁ :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀))
        (hs.trans_le (min_le_right _ _))
    show 1 / 2 + k * b + η / 2 < s.re
    have := (abs_lt.mp hre).1
    nlinarith
  have hGAn : ∀ s : ℂ, 1 < s.re → L₁ < s.re →
      (∀ z, traceCoeff 3 z ≠ 0 → s ≠ 1 + k * z) → AnalyticAt ℂ G s := by
    intro s h1 h2 hp
    obtain ⟨ρ, hρ, hd⟩ := hGball s h1 h2 hp
    exact hd.analyticAt (ball_mem_nhds s hρ)
  have hrealNoPole : ∀ t : ℝ, ∀ z, traceCoeff 3 z ≠ 0 → (t : ℂ) ≠ 1 + k * z := by
    intro t z hz h
    have him := congrArg Complex.im h
    rw [Complex.ofReal_im, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero, zero_add] at him
    have : z.im = 0 := by
      rcases mul_eq_zero.mp him.symm with h0 | h0
      · exact absurd h0 hk0.ne'
      · exact h0
    exact traceCoeff_im_ne_zero hz this
  have hagreeHigh : ∀ s : ℂ, A₀ < s.re → gdSeries B powerFreq s = G s := by
    intro s hs
    have hA := summable_gdTerm_of_abs_le' hbA hs
    have hH := summable_gdTerm_of_abs_le' hbH hs
    simp only [hGdef, hNdef]
    rw [← gdSeries_kCoeff_eq hb0 hzf K hs]
    unfold gdSeries
    rw [← hA.tsum_sub hH]
    refine tsum_congr fun j => ?_
    simp only [hBdef]
    rw [← kPrimeCoeff_add_kHigherCoeff k K j]
    push_cast
    ring
  -- Landau: the abscissa is at most `max(1, L₁)`
  have hσc : σc ≤ max 1 L₁ := by
    by_contra hgt
    push Not at hgt
    have hgt1 : 1 < σc := (le_max_left _ _).trans_lt hgt
    have hgt2 : L₁ < σc := (le_max_right _ _).trans_lt hgt
    obtain ⟨ρ, hρ, hG⟩ := hGball (σc : ℂ) (by simpa using hgt1) (by simpa using hgt2)
      (fun z hz => hrealNoPole σc z hz)
    have hreal : ∀ t ∈ Ioo σc (S2 + 1),
        gdSeries B powerFreq ((0 : ℂ) + t) = G ((0 : ℂ) + t) := by
      refine eqOn_ray_of_eventually (a := σc) (c := S2 + 1 / 2) (b := S2 + 1)
        (by linarith) (by linarith) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
      · rw [zero_add]; exact hgdAn _ (by simpa using ht.1)
      · rw [zero_add]
        exact hGAn _ (by simpa using hgt1.trans ht.1) (by simpa using hgt2.trans ht.1)
          (fun z hz => hrealNoPole t z hz)
      · rw [zero_add]; exact hagreeHigh _ (by simp; linarith [ht.1])
    have hhalf := eqOn_halfBall (f := G) (g := gdSeries B powerFreq) hρ
      (fun s hs _ => hG.analyticAt (isOpen_ball.mem_nhds hs))
      (fun s _ hs => hgdAn s hs)
      (fun t ht1 _ => by
        rcases lt_or_ge t (S2 + 1) with htb | htb
        · have := hreal t ⟨ht1, htb⟩; rw [zero_add] at this; exact this.symm
        · exact (hagreeHigh _ (by simp; linarith)).symm)
    exact RHTower.gdSeries_no_continuation_at_abscissa hB hlam hsum hdiv hρ hG
      (fun s hs hre => hhalf s hs hre)
  -- the deep zero, rightmost on its line
  set z₁ := ρ₁ - 1 / 2 with hz₁def
  have hz₁re : z₁.re = ρ₁.re - 1 / 2 := by simp [hz₁def]
  have hbig : max 0 (((k + 1) * b - 1 / 2 + η) / k) < z₁.re := by rw [hz₁re]; linarith
  have hz₁pos : 0 < z₁.re := (le_max_left _ _).trans_lt hbig
  have hz₁ : traceCoeff 3 z₁ ≠ 0 := traceCoeff_sees (le_refl 3) hρ₁ (by rw [hz₁re] at hz₁pos; linarith)
  set Lset := (finite_evenCoeff_line zetaZeroConfig (boxSpline 1 3) z₁.im).toFinset with hLset
  obtain ⟨z₀, hz₀L, hmax⟩ := Lset.exists_max_image Complex.re
    ⟨z₁, (Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩⟩
  obtain ⟨hz₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hz₀L
  have hre₀ : z₁.re ≤ z₀.re := hmax z₁ ((Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩)
  set s₀ : ℂ := 1 + k * z₀ with hs₀def
  have hs₀re : s₀.re = 1 + k * z₀.re := by simp [hs₀def]
  have hs₀1 : 1 < s₀.re := by rw [hs₀re]; nlinarith
  have hs₀2 : L₁ < s₀.re := by
    have h1 : ((k + 1) * b - 1 / 2 + η) / k < z₀.re := (le_max_right _ _).trans_lt (hbig.trans_le hre₀)
    rw [div_lt_iff₀ hk0] at h1
    rw [hs₀re, hL₁]; nlinarith
  have hs₀σ : σc < s₀.re := hσc.trans_lt (max_lt hs₀1 hs₀2)
  set T : ℝ := max (A₀ - s₀.re) 0 + 2 with hTdef
  have hT : 0 < T := by rw [hTdef]; positivity
  have hqre : ∀ t : ℝ, (s₀ + t).re = s₀.re + t := fun t => by simp
  have hray : ∀ t : ℝ, 0 < t → ∀ z, traceCoeff 3 z ≠ 0 → s₀ + t ≠ 1 + k * z := by
    intro t ht z hz h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [hs₀def] at him hre
    have hzim : z.im = z₀.im := by
      rcases him with h0 | h0
      · exact h0.symm
      · exact absurd h0 (by omega)
    have hle := hmax z ((Set.Finite.mem_toFinset _).mpr ⟨hz, hzim.trans him₀⟩)
    nlinarith
  have hGray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ G (s₀ + t) := fun t ht =>
    hGAn _ (by rw [hqre]; linarith [ht.1]) (by rw [hqre]; linarith [ht.1]) (hray t ht.1)
  have hgdray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ (gdSeries B powerFreq) (s₀ + t) := fun t ht =>
    hgdAn _ (by rw [hqre]; linarith [ht.1])
  have hagreeRay : ∀ t ∈ Ioo 0 T, gdSeries B powerFreq (s₀ + t) = G (s₀ + t) :=
    eqOn_ray_of_eventually (c := max (A₀ - s₀.re) 0 + 1) (by positivity) (by rw [hTdef]; linarith)
      hgdray hGray (fun t ht => hagreeHigh _ (by
        rw [hqre]; have := le_max_left (A₀ - s₀.re) 0; linarith [ht.1]))
  -- split off the pole
  set c' : ℂ → ℂ := fun z => if z = z₀ then 0 else traceCoeff 3 z with hc'def
  have hc' : ∀ z, ‖c' z‖ ≤ ‖traceCoeff 3 z‖ := fun z => by
    simp only [hc'def]; split_ifs <;> simp
  set R : ℂ → ℂ := fun s => -scaledLogDerivOf k c' s -
    ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s - N s with hRdef
  have hsplit : ∀ t ∈ Ioo 0 T,
      G (s₀ + t) = -(traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) + R (s₀ + t) := by
    intro t ht
    have hsm := summable_scaledLogDerivOf_terms hk hb0 hzf (c := traceCoeff 3)
      (fun _ => le_rfl) (s := s₀ + t) (by rw [hqre]; linarith [ht.1])
    simp only [hGdef, hRdef]
    unfold kZeta scaledLogDerivOf
    rw [hsm.tsum_eq_add_tsum_ite z₀]
    have h1 : (s₀ + t) - k * z₀ = 1 + t := by rw [hs₀def]; ring
    have h2 : ∑' z, (if z = z₀ then 0 else
          traceCoeff 3 z * logDeriv riemannZeta (s₀ + t - k * z)) =
        ∑' z, c' z * logDeriv riemannZeta (s₀ + t - k * z) :=
      tsum_congr fun z => by simp only [hc'def]; split_ifs <;> simp
    rw [h1, h2]
    ring
  have hs₀ne : s₀ ≠ 1 := fun h => by rw [h] at hs₀1; simp at hs₀1
  have hRcont : ContinuousAt R s₀ := by
    have hp : ∀ z, c' z ≠ 0 → s₀ ≠ 1 + k * z := by
      intro z hz h
      have hzz : z ≠ z₀ := fun e => hz (by simp [hc'def, e])
      have hk0' : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have : (k : ℂ) * z₀ = k * z := by rw [hs₀def] at h; linear_combination h
      exact hzz (mul_left_cancel₀ hk0' this).symm
    have h1 := differentiableAt_scaledLogDerivOf hk hb0 hzf hc' (by linarith) hp
    have h2 := differentiableAt_logDeriv_riemannZeta hs₀ne
      (riemannZeta_ne_zero_of_one_le_re hs₀1.le)
    exact ((h1.neg.sub (h2.const_mul _)).continuousAt).sub
      (hNAn s₀ (by nlinarith)).continuousAt
  have hgdcont : ContinuousAt (gdSeries B powerFreq) s₀ := (hgdAn s₀ hs₀σ).continuousAt
  set H : ℂ → ℂ := fun s => gdSeries B powerFreq s - R s with hHdef
  have hHcont : ContinuousAt H s₀ := hgdcont.sub hRcont
  have hHray : ∀ t ∈ Ioo 0 T, H (s₀ + t) = -(traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) := by
    intro t ht
    simp only [hHdef]
    rw [hagreeRay t ht, hsplit t ht]
    ring
  -- the pole of `ζ'/ζ` at `1` against continuity
  obtain ⟨δ₁, hδ₁, hδ₁H⟩ := Metric.continuousAt_iff.mp hHcont 1 one_pos
  set A := ‖traceCoeff 3 z₀‖ with hAdef
  have hA : 0 < A := norm_pos_iff.mpr hz₀
  obtain ⟨t, ht0, htδ, htB⟩ := exists_norm_logDeriv_zeta_one_add_gt ((‖H s₀‖ + 1) / A)
    (lt_min hδ₁ hT)
  have htδ₁ : t < δ₁ := htδ.trans_le (min_le_left _ _)
  have htT : t < T := htδ.trans_le (min_le_right _ _)
  have h1 := hHray t ⟨ht0, htT⟩
  have h2 : dist (H (s₀ + t)) (H s₀) < 1 := hδ₁H (by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact htδ₁)
  have h4 : ‖H s₀‖ + 1 < ‖H (s₀ + t)‖ := by
    rw [h1, norm_neg, norm_mul]
    rw [div_lt_iff₀ hA] at htB
    linarith
  have h5 : ‖H (s₀ + t)‖ < ‖H s₀‖ + 1 := by
    have := norm_sub_norm_le (H (s₀ + t)) (H s₀)
    rw [dist_eq_norm] at h2
    linarith
  linarith

/-! ### The first strip -/

/-- `yᵏ − pᵏ ≤ k y^{k−1}(y − p)` for `0 ≤ p ≤ y`. -/
theorem pow_sub_pow_le_mul {y p : ℝ} (hp : 0 ≤ p) (hpy : p ≤ y) (k : ℕ) :
    y ^ k - p ^ k ≤ k * y ^ (k - 1) * (y - p) := by
  rw [← geom_sum₂_mul]
  have hy : 0 ≤ y := hp.trans hpy
  have hsum : ∑ i ∈ Finset.range k, y ^ i * p ^ (k - 1 - i) ≤ k * y ^ (k - 1) := by
    have h := Finset.sum_le_card_nsmul (Finset.range k) (fun i => y ^ i * p ^ (k - 1 - i))
      (y ^ (k - 1)) (fun i hi => by
        have hik : i ≤ k - 1 := by have := Finset.mem_range.mp hi; omega
        calc y ^ i * p ^ (k - 1 - i) ≤ y ^ i * y ^ (k - 1 - i) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpy _) (pow_nonneg hy _)
          _ = y ^ (k - 1) := by rw [← pow_add]; congr 1; omega)
    simpa using h
  exact mul_le_mul_of_nonneg_right hsum (by linarith)

/-- **The degrees `pᵏ` have gaps `x^{1 − 1/(3k)}`.** -/
theorem powGaps_kthPrimePowers {k : ℕ} (hk : 1 ≤ k) :
    PowGaps (1 - 1 / (3 * k)) {d : ℕ | ∃ p : ℕ, p.Prime ∧ d = p ^ k} := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  refine ⟨fun d ⟨p, hp, hd⟩ => hd ▸ pow_pos hp.pos k, ?_⟩
  obtain ⟨-, M, X, hM0, hgap⟩ := powGaps_primes (α := 2 / 3) (by norm_num) (by norm_num)
  refine ⟨k * M, max (|X| ^ k) 1, by positivity, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  set y := x ^ ((1 : ℝ) / k) with hydef
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hyk : y ^ k = x := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    rw [show (1 : ℝ) / k * k = 1 by field_simp, Real.rpow_one]
  have hyX : X ≤ y := by
    have h1 : |X| ^ k ≤ x := (le_max_left _ _).trans hx
    have h2 : |X| ≤ y := by
      by_contra hlt
      push Not at hlt
      have := pow_lt_pow_left₀ hlt hy0.le (by omega : k ≠ 0)
      rw [hyk] at this
      linarith
    exact (le_abs_self X).trans h2
  obtain ⟨p, hp, hpy, hgp⟩ := hgap y hyX
  refine ⟨p ^ k, ⟨p, hp, rfl⟩, ?_, ?_⟩
  · have := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) p) hpy k
    push_cast
    linarith
  · have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have h1 := pow_sub_pow_le_mul hp0 hpy k
    have hyk1 : y ^ (k - 1) * y ^ ((2 : ℝ) / 3) = x ^ (1 - 1 / (3 * (k : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hy0, hydef, ← Real.rpow_mul hx0.le]
      congr 1
      rw [Nat.cast_sub hk]
      field_simp
      ring
    push_cast
    rw [hyk] at h1
    calc x - (p : ℝ) ^ k ≤ k * y ^ (k - 1) * (y - p) := h1
      _ ≤ k * y ^ (k - 1) * (M * y ^ ((2 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left hgp (by positivity)
      _ = k * M * (y ^ (k - 1) * y ^ ((2 : ℝ) / 3)) := by ring
      _ = k * M * x ^ (1 - 1 / (3 * (k : ℝ))) := by rw [hyk1]

/-! ### The theorem -/

/-- **The bootstrap at the prime powers.** For every `k ≥ 1`, RH holds iff the traces
`2 Re S(k log p)` of the smoothed Frobenius graphs of degree `pᵏ`, `p` prime, are bounded below. -/
theorem riemannHypothesis_iff_bddBelow_kthPrimePowers {k : ℕ} (hk : 1 ≤ k) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (k * Real.log p)).re := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hb := contDiff_boxSpline_two (le_refl 3)
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  constructor
  · intro hRH
    have hon := riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH
    set L₀ := ∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z‖ with hL₀
    refine ⟨2 * L₀, fun p _ => ?_⟩
    set v : ℝ := k * Real.log p
    obtain ⟨hs, he⟩ := lagStructure_eq_tsum_lagCoeff zetaZeroConfig hZ hb hbs v
    have hterm : ∀ z, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z * cexp (z * v)‖ =
        ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z‖ := by
      intro z
      by_cases hz : lagCoeff zetaZeroConfig (boxSpline 1 3) z = 0
      · simp [hz]
      have hmem : (1 / 2 + z) ∈ zetaZeroConfig.carrier := by
        by_contra h; exact hz (by rw [lagCoeff, Set.indicator_of_notMem h])
      have hre : z.re = 0 := by have := hon _ hmem; simp at this; linarith
      rw [norm_mul, Complex.norm_exp]
      simp [hre]
    have hle : ‖lagStructure zetaZeroConfig (boxSpline 1 3) v‖ ≤ L₀ := by
      rw [he]
      calc ‖∑' z, lagCoeff zetaZeroConfig (boxSpline 1 3) z * cexp (z * v)‖
          ≤ ∑' z, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z * cexp (z * v)‖ :=
            norm_tsum_le_tsum_norm hs.norm
        _ = L₀ := tsum_congr hterm
    have h1 := (Complex.abs_re_le_norm (lagStructure zetaZeroConfig (boxSpline 1 3) v)).trans hle
    linarith [(abs_le.mp h1).1]
  · rintro ⟨K, hK⟩
    -- the first strip, from the gaps of the degrees `pᵏ`
    set b₀ : ℝ := 1 / 2 - 1 / (3 * k) with hb₀
    have hpos3 : 0 < 1 / (3 * (k : ℝ)) := by positivity
    have h3k : 1 / (3 * (k : ℝ)) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hb₀0 : 0 ≤ b₀ := by rw [hb₀]; linarith
    have hb₀1 : b₀ < 1 / 2 := by rw [hb₀]; linarith
    have hzf₀ : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b₀ := by
      have h := re_le_of_bddBelow_of_powGaps (θ := 1 - 1 / (3 * k)) (by linarith) (by linarith)
        (powGaps_kthPrimePowers hk) (K := K / 2) (fun d ⟨p, hp, hd⟩ => by
          have := hK p hp
          rw [hd, Nat.cast_pow, Real.log_pow, orbitCorr_eq_re_lagStructure_spline]
          linarith)
      intro ρ hρ
      have := h ρ hρ
      rw [hb₀]; linarith
    -- the bootstrap
    set d₀ : ℝ := (1 / 2 - b₀) / (2 * k) with hd₀
    have hd₀0 : 0 < d₀ := by rw [hd₀]; apply div_pos <;> linarith
    have hstep : ∀ n : ℕ, ∀ ρ ∈ zetaZeroConfig.carrier,
        ρ.re ≤ 1 / 2 + max 0 (b₀ - n * d₀) := by
      intro n
      induction n with
      | zero =>
        intro ρ hρ
        have := hzf₀ ρ hρ
        simp only [Nat.cast_zero, zero_mul, sub_zero]
        linarith [le_max_right 0 b₀]
      | succ n ih =>
        set bn := max 0 (b₀ - n * d₀) with hbn
        have hbn0 : 0 ≤ bn := le_max_left _ _
        have hbnb : bn ≤ b₀ := max_le hb₀0 (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
        have h := re_le_of_bddBelow_kthPrimePowers_step hk hbn0 ih hK
          (η := (1 / 2 - b₀) / 2) (by linarith)
        intro ρ hρ
        have hρ' := h ρ hρ
        have hkey : ((k + 1) * bn - 1 / 2 + (1 / 2 - b₀) / 2) / k ≤ bn - d₀ := by
          rw [div_le_iff₀ hk0, hd₀]
          have : (1 / 2 - b₀) / (2 * k) * k = (1 / 2 - b₀) / 2 := by field_simp
          nlinarith
        have hmono : max 0 (((k + 1) * bn - 1 / 2 + (1 / 2 - b₀) / 2) / k) ≤
            max 0 (b₀ - ((n + 1 : ℕ) : ℝ) * d₀) := by
          apply max_le (le_max_left _ _)
          refine hkey.trans ?_
          push_cast
          rcases le_total 0 (b₀ - n * d₀) with h0 | h0
          · rw [hbn, max_eq_right h0]; exact le_max_of_le_right (by ring_nf; linarith)
          · rw [hbn, max_eq_left h0]; exact le_max_of_le_left (by linarith)
        linarith
    -- finitely many steps reach the line
    obtain ⟨n, hn⟩ := exists_nat_gt (b₀ / d₀)
    have hnd : b₀ - n * d₀ ≤ 0 := by
      have := (div_lt_iff₀ hd₀0).mp hn
      linarith
    apply riemannHypothesis_of_forall_re_le
    intro ρ hρ
    have := hstep n ρ hρ
    rw [max_eq_left hnd] at this
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
