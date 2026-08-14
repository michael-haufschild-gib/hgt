import GaloisForLFunctions.HTGeometry.CompactTestTransform

/-!
# The entire test transform decays faster than every power

For a compactly supported smooth `ψ` the entire Fourier extension

`Ψ(z) = ∫ ψ(L) e^{izL} dL`

satisfies `Ψ(z)(iz)^k = (-1)^k Ψ_k(z)` where `Ψ_k` is the transform of the `k`-th derivative.  Since
every derivative is again compactly supported and smooth, its transform is bounded on each
horizontal strip, and therefore

`‖Ψ(z)‖ ≤ C_k (1+‖z‖)^{-k}`

uniformly on each horizontal strip, for every order `k`.  This is what lets the pairing argument
absorb polynomial growth of the other factor, not merely boundedness.
-/

open Complex MeasureTheory Set Filter

open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Every iterated derivative of a smooth function is smooth. -/
theorem contDiff_iterate_deriv {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (k : ℕ) :
    ContDiff ℝ ∞ (deriv^[k] ψ) := by
  induction k with
  | zero => simpa using hψ
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (contDiff_infty_iff_deriv.mp ih).2

/-- Every iterated derivative of a compactly supported function has compact support. -/
theorem hasCompactSupport_iterate_deriv {ψ : ℝ → ℂ} (hs : HasCompactSupport ψ) (k : ℕ) :
    HasCompactSupport (deriv^[k] ψ) := by
  induction k with
  | zero => simpa using hs
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

/-- **Iterated integration by parts.**  Multiplying the transform by `(iz)^k` is the transform of
the `k`-th derivative, up to sign. -/
theorem testTransform_ibp_iter {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    (k : ℕ) (z : ℂ) :
    testTransform ψ z * (Complex.I * z) ^ k = (-1) ^ k * testTransform (deriv^[k] ψ) z := by
  have hle : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  induction k with
  | zero => simp
  | succ n ih =>
      have hdn : ContDiff ℝ 1 (deriv^[n] ψ) := (contDiff_iterate_deriv hψ n).of_le hle
      have hsn : HasCompactSupport (deriv^[n] ψ) := hasCompactSupport_iterate_deriv hs n
      have hstep := testTransform_ibp hdn hsn z
      calc testTransform ψ z * (Complex.I * z) ^ (n + 1)
          = testTransform ψ z * (Complex.I * z) ^ n * (Complex.I * z) := by ring
        _ = (-1) ^ n * testTransform (deriv^[n] ψ) z * (Complex.I * z) := by rw [ih]
        _ = (-1) ^ n * (testTransform (deriv^[n] ψ) z * (Complex.I * z)) := by ring
        _ = (-1) ^ n * -testTransform (deriv (deriv^[n] ψ)) z := by rw [hstep]
        _ = (-1) ^ (n + 1) * testTransform (deriv^[n + 1] ψ) z := by
            rw [Function.iterate_succ_apply']
            ring

/-- The transform of a compactly supported smooth function is bounded on each horizontal strip. -/
theorem exists_bound_testTransform_strip {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (a b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, z.im ∈ uIcc a b → ‖testTransform ψ z‖ ≤ B := by
  classical
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hs.isCompact.isBounded
  set M : ℝ := |r| with hMdef
  have hM0 : (0 : ℝ) ≤ M := abs_nonneg r
  have hMsupp : ∀ x : ℝ, M < |x| → ψ x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
    have hx' : x ∈ Metric.closedBall (0 : ℝ) r := hr hmem
    have hxr : |x| ≤ r := by simpa [Real.dist_eq] using hx'
    exact absurd (lt_of_lt_of_le hx (le_trans hxr (le_abs_self r))) (lt_irrefl _)
  set K : ℝ := |a| + |b| with hKdef
  have hKmem : ∀ y : ℝ, y ∈ uIcc a b → |y| ≤ K := by
    intro y hy
    have h1 : min a b ≤ y := (Set.mem_uIcc.mp hy).elim (fun h => le_trans (min_le_left a b) h.1)
      (fun h => le_trans (min_le_right a b) h.1)
    have h2 : y ≤ max a b := (Set.mem_uIcc.mp hy).elim (fun h => le_trans h.2 (le_max_right a b))
      (fun h => le_trans h.2 (le_max_left a b))
    have hmax : max a b ≤ K := by
      rw [hKdef]
      rcases max_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        [linarith [le_abs_self a, abs_nonneg b]; linarith [le_abs_self b, abs_nonneg a]]
    have hmin : -K ≤ min a b := by
      rw [hKdef]
      rcases min_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        [linarith [neg_abs_le a, abs_nonneg b]; linarith [neg_abs_le b, abs_nonneg a]]
    exact abs_le.mpr ⟨le_trans hmin h1, le_trans h2 hmax⟩
  refine ⟨Real.exp (M * K) * ∫ L : ℝ, ‖ψ L‖, ?_, fun z hz => ?_⟩
  · have : (0 : ℝ) ≤ ∫ L : ℝ, ‖ψ L‖ := integral_nonneg fun L => norm_nonneg _
    positivity
  · exact norm_testTransform_le_exp hψ.continuous hs hM0 hMsupp z (hKmem z.im hz)

/-- **Decay of every order.**  On each horizontal strip the entire test transform is bounded by
`C (1+‖z‖)^{-k}` for every `k`. -/
theorem exists_testTransform_decay_order {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (a b : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.im ∈ uIcc a b →
      ‖testTransform ψ z‖ ≤ C / (1 + ‖z‖) ^ k := by
  obtain ⟨B₀, hB₀0, hB₀⟩ := exists_bound_testTransform_strip hψ hs a b
  obtain ⟨Bk, hBk0, hBk⟩ := exists_bound_testTransform_strip
    (contDiff_iterate_deriv hψ k) (hasCompactSupport_iterate_deriv hs k) a b
  refine ⟨2 ^ k * max B₀ Bk, by positivity, fun z hz => ?_⟩
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hpos : (0 : ℝ) < (1 + ‖z‖) ^ k := by positivity
  rw [le_div_iff₀ hpos]
  have hsplit : ‖testTransform ψ z‖ * max 1 (‖z‖) ^ k ≤ max B₀ Bk := by
    rcases le_or_gt ‖z‖ 1 with hle | hgt
    · rw [max_eq_left hle, one_pow, mul_one]
      exact le_trans (hB₀ z hz) (le_max_left _ _)
    · rw [max_eq_right hgt.le]
      have hiter : ‖testTransform ψ z‖ * ‖z‖ ^ k = ‖testTransform (deriv^[k] ψ) z‖ := by
        have h := testTransform_ibp_iter hψ hs k z
        have hnorm := congrArg norm h
        rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul,
          norm_pow, norm_neg, norm_one, one_pow, one_mul] at hnorm
        exact hnorm
      rw [hiter]
      exact le_trans (hBk z hz) (le_max_right _ _)
  have hcmp : (1 + ‖z‖) ^ k ≤ 2 ^ k * max 1 (‖z‖) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    rcases le_or_gt ‖z‖ 1 with hle | hgt
    · rw [max_eq_left hle]
      linarith
    · rw [max_eq_right hgt.le]
      linarith
  calc ‖testTransform ψ z‖ * (1 + ‖z‖) ^ k
      ≤ ‖testTransform ψ z‖ * (2 ^ k * max 1 (‖z‖) ^ k) :=
        mul_le_mul_of_nonneg_left hcmp (norm_nonneg _)
    _ = 2 ^ k * (‖testTransform ψ z‖ * max 1 (‖z‖) ^ k) := by ring
    _ ≤ 2 ^ k * max B₀ Bk := by
        refine mul_le_mul_of_nonneg_left hsplit (by positivity)

/-- The decay of every order survives the `2π` rescaling. -/
theorem exists_testTransformTwoPi_decay_order {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (a b : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.im ∈ uIcc a b →
      ‖testTransformTwoPi ψ z‖ ≤ C / (1 + ‖z‖) ^ k := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_testTransform_decay_order hψ hs (2 * Real.pi * a) (2 * Real.pi * b) k
  refine ⟨C, hC0, fun z hz => ?_⟩
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hzim : (((2 * Real.pi : ℝ) : ℂ) * z).im = 2 * Real.pi * z.im := by simp
  have hmem : (((2 * Real.pi : ℝ) : ℂ) * z).im ∈ uIcc (2 * Real.pi * a) (2 * Real.pi * b) := by
    rw [hzim]
    rcases Set.mem_uIcc.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Set.mem_uIcc.mpr (Or.inl ⟨by nlinarith, by nlinarith⟩)
    · exact Set.mem_uIcc.mpr (Or.inr ⟨by nlinarith, by nlinarith⟩)
  have hnorm : ‖z‖ ≤ ‖((2 * Real.pi : ℝ) : ℂ) * z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    nlinarith [norm_nonneg z, Real.two_le_pi]
  refine le_trans (hC _ hmem) ?_
  refine div_le_div_of_nonneg_left hC0 (by positivity) ?_
  exact pow_le_pow_left₀ (by positivity) (by linarith) k

end GaloisForLFunctions.HTGeometry
