import GaloisForLFunctions.HTGeometry.PoissonKernelBound
import GaloisForLFunctions.HTGeometry.AnalyticRootFactor

/-!
# The proximity cost of extracting zeros

Dividing an analytic function by the monic polynomial carrying its zeros in a closed ball changes
the boundary proximity average by at most `log 2` per zero.  The mechanism is the exact circle
average `⨍ log ‖· - a‖ = log R` for a point `a` of the ball, together with the crude bound
`log⁺ ‖z - a‖ ≤ log (2R)` on the boundary circle.

Combined with the Poisson bound for the zero-free cofactor this converts a maximum modulus at an
interior radius into a proximity average on the boundary, with the zero count as the only other
term.
-/

open Complex Metric Real Finset Topology

namespace GaloisForLFunctions.HTGeometry

/-! ## The positive part -/

/-- The positive part is subadditive. -/
theorem posPart_add_le (x y : ℝ) : max 0 (x + y) ≤ max 0 x + max 0 y := by
  have h1 : (0 : ℝ) ≤ max 0 x := le_max_left _ _
  have h2 : (0 : ℝ) ≤ max 0 y := le_max_left _ _
  have h3 : x ≤ max 0 x := le_max_right _ _
  have h4 : y ≤ max 0 y := le_max_right _ _
  exact max_le (by linarith) (by linarith)

/-- The positive part is homogeneous under nonnegative scaling. -/
theorem posPart_smul {c : ℝ} (t : ℝ) (hc : 0 ≤ c) : max 0 (c * t) = c * max 0 t := by
  rcases le_total 0 t with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonneg hc h)]
  · rw [max_eq_left h, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc h), mul_zero]

/-- The positive part of a nonnegative combination is at most the combination of positive parts. -/
theorem posPart_sum_le {ι : Type*} (s : Finset ι) (c t : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    max 0 (∑ i ∈ s, c i * t i) ≤ ∑ i ∈ s, c i * max 0 (t i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j u hj ih =>
      have hcj : 0 ≤ c j := hc j (Finset.mem_insert_self j u)
      have hcu : ∀ i ∈ u, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      calc max 0 (c j * t j + ∑ i ∈ u, c i * t i)
          ≤ max 0 (c j * t j) + max 0 (∑ i ∈ u, c i * t i) := posPart_add_le _ _
        _ ≤ c j * max 0 (t j) + ∑ i ∈ u, c i * max 0 (t i) := by
            rw [posPart_smul _ hcj]
            linarith [ih hcu]

/-- The negative part expressed through the positive part. -/
theorem posPart_neg (t : ℝ) : max 0 (-t) = max 0 t - t := by
  rcases le_total 0 t with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : -t ≤ (0 : ℝ))]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith : (0 : ℝ) ≤ -t)]
    ring

/-! ## The cost of one zero -/

/-- On a circle of radius `R ≥ 1` about `c`, the negative part of `log ‖· - a‖` has circle average at
most `log 2` for every `a` in the closed ball.  The exact average of `log ‖· - a‖` is `log R`, and
the positive part is bounded by `log (2R)` since every boundary point is within `2R` of `a`. -/
theorem circleAverage_negPart_log_norm_sub_le {c a : ℂ} {R : ℝ} (hR : 1 ≤ R)
    (ha : a ∈ closedBall c R) :
    Real.circleAverage (fun z => max 0 (-Real.log ‖z - a‖)) c R ≤ Real.log 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have habs : |R| = R := abs_of_pos hR0
  have hac : ‖a - c‖ ≤ R := mem_closedBall_iff_norm.mp ha
  have hmero : MeromorphicOn (fun z : ℂ => z - a) (sphere c |R|) :=
    (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
  have hint₁ : CircleIntegrable (fun z => Real.posLog ‖z - a‖) c R :=
    hmero.circleIntegrable_posLog_norm
  have hint₂ : CircleIntegrable (fun z => Real.log ‖z - a‖) c R :=
    hmero.circleIntegrable_log_norm
  have hfun : (fun z : ℂ => max 0 (-Real.log ‖z - a‖))
      = (fun z : ℂ => Real.posLog ‖z - a‖) - fun z : ℂ => Real.log ‖z - a‖ := by
    funext z
    rw [Pi.sub_apply, Real.posLog, posPart_neg]
  rw [hfun, Real.circleAverage_sub hint₁ hint₂]
  -- the exact average of the log
  have hlogavg : Real.circleAverage (fun z => Real.log ‖z - a‖) c R = Real.log R := by
    exact circleAverage_log_norm_sub_const_of_mem_closedBall (by rw [habs]; exact ha)
  -- the crude bound on the positive part
  have hlog2R : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hposavg : Real.circleAverage (fun z => Real.posLog ‖z - a‖) c R ≤ Real.log (2 * R) := by
    refine Real.circleAverage_mono_on_of_le_circle hint₁ ?_
    intro z hz
    rw [habs] at hz
    have hzc : ‖z - c‖ = R := by simpa [mem_sphere_iff_norm] using hz
    have hdist : ‖z - a‖ ≤ 2 * R := by
      calc ‖z - a‖ = ‖(z - c) - (a - c)‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖a - c‖ := norm_sub_le _ _
        _ ≤ 2 * R := by linarith
    have hlogle : Real.log ‖z - a‖ ≤ Real.log (2 * R) := by
      rcases eq_or_lt_of_le (norm_nonneg (z - a)) with h | h
      · rw [← h, Real.log_zero]
        exact hlog2R
      · exact Real.log_le_log h hdist
    rw [Real.posLog]
    exact max_le hlog2R hlogle
  have hsplit : Real.log (2 * R) = Real.log 2 + Real.log R :=
    Real.log_mul two_ne_zero (ne_of_gt hR0)
  rw [hlogavg]
  linarith [hposavg, hsplit]

/-! ## The proximity comparison -/

/-- **Extracting zeros costs `log 2` per zero in proximity.**  If `f = ∏ (· - a)^{m a} · g` on a
closed ball of radius `R ≥ 1`, with all `a` in the ball and `f` nonvanishing on the boundary circle,
then the boundary proximity average of the cofactor `g` exceeds that of `f` by at most
`(∑ m a) · log 2`. -/
theorem circleAverage_posLog_cofactor_le
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} {T : Finset ℂ} {m : ℂ → ℕ}
    (hR : 1 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hTmem : ∀ a ∈ T, a ∈ closedBall c R)
    (hfac : ∀ z ∈ closedBall c R, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    (hsph : ∀ z ∈ sphere c R, f z ≠ 0) :
    Real.circleAverage (fun z => Real.posLog ‖g z‖) c R
      ≤ Real.circleAverage (fun z => Real.posLog ‖f z‖) c R
        + (∑ a ∈ T, (m a : ℝ)) * Real.log 2 := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have habs : |R| = R := abs_of_pos hR0
  have hsubball : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  -- integrability of the three ingredients
  have hmerof : MeromorphicOn f (sphere c |R|) := by
    rw [habs]
    exact (hf.mono hsubball).meromorphicOn
  have hmerog : MeromorphicOn g (sphere c |R|) := by
    rw [habs]
    exact (hg.mono hsubball).meromorphicOn
  have hintg : CircleIntegrable (fun z => Real.posLog ‖g z‖) c R :=
    hmerog.circleIntegrable_posLog_norm
  have hintf : CircleIntegrable (fun z => Real.posLog ‖f z‖) c R :=
    hmerof.circleIntegrable_posLog_norm
  have hinta : ∀ a ∈ T,
      CircleIntegrable (fun z => (m a : ℝ) * max 0 (-Real.log ‖z - a‖)) c R := by
    intro a _
    have hmero : MeromorphicOn (fun z : ℂ => z - a) (sphere c |R|) :=
      (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
    have hfun : (fun z : ℂ => max 0 (-Real.log ‖z - a‖))
        = (fun z : ℂ => Real.posLog ‖z - a‖) - fun z : ℂ => Real.log ‖z - a‖ := by
      funext z
      rw [Pi.sub_apply, Real.posLog, posPart_neg]
    have : CircleIntegrable (fun z : ℂ => max 0 (-Real.log ‖z - a‖)) c R := by
      rw [hfun]
      exact hmero.circleIntegrable_posLog_norm.sub hmero.circleIntegrable_log_norm
    exact this.const_mul _
  have hintsum : CircleIntegrable
      (fun z => ∑ a ∈ T, (m a : ℝ) * max 0 (-Real.log ‖z - a‖)) c R :=
    CircleIntegrable.fun_sum T hinta
  -- the pointwise comparison on the boundary circle
  have hpt : ∀ z ∈ sphere c |R|,
      Real.posLog ‖g z‖
        ≤ Real.posLog ‖f z‖ + ∑ a ∈ T, (m a : ℝ) * max 0 (-Real.log ‖z - a‖) := by
    intro z hz
    rw [habs] at hz
    have hzball : z ∈ closedBall c R := hsubball hz
    have hfz : f z ≠ 0 := hsph z hz
    have hnorm : ‖f z‖ = (∏ a ∈ T, ‖z - a‖ ^ (m a)) * ‖g z‖ := by
      rw [hfac z hzball, norm_mul, norm_prod]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro a _
      rw [norm_pow]
    have hgz : ‖g z‖ ≠ 0 := by
      intro hcon
      apply hfz
      have : ‖f z‖ = 0 := by rw [hnorm, hcon, mul_zero]
      exact norm_eq_zero.mp this
    have hprodne : (∏ a ∈ T, ‖z - a‖ ^ (m a)) ≠ 0 := by
      intro hcon
      apply hfz
      have : ‖f z‖ = 0 := by rw [hnorm, hcon, zero_mul]
      exact norm_eq_zero.mp this
    have hlogg : Real.log ‖g z‖
        = Real.log ‖f z‖ + ∑ a ∈ T, (m a : ℝ) * (-Real.log ‖z - a‖) := by
      have hsplit : Real.log ‖f z‖
          = ∑ a ∈ T, (m a : ℝ) * Real.log ‖z - a‖ + Real.log ‖g z‖ := by
        rw [hnorm, Real.log_mul hprodne hgz]
        congr 1
        rw [Real.log_prod (fun a ha => Finset.prod_ne_zero_iff.mp hprodne a ha)]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Real.log_pow]
      have hneg : ∑ a ∈ T, (m a : ℝ) * (-Real.log ‖z - a‖)
          = -∑ a ∈ T, (m a : ℝ) * Real.log ‖z - a‖ := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl ?_
        intro a _
        ring
      rw [hneg]
      linarith [hsplit]
    rw [Real.posLog, hlogg]
    calc max 0 (Real.log ‖f z‖ + ∑ a ∈ T, (m a : ℝ) * (-Real.log ‖z - a‖))
        ≤ max 0 (Real.log ‖f z‖) + max 0 (∑ a ∈ T, (m a : ℝ) * (-Real.log ‖z - a‖)) :=
          posPart_add_le _ _
      _ ≤ Real.posLog ‖f z‖ + ∑ a ∈ T, (m a : ℝ) * max 0 (-Real.log ‖z - a‖) := by
          rw [Real.posLog]
          linarith [posPart_sum_le T (fun a => (m a : ℝ)) (fun a => -Real.log ‖z - a‖)
            (fun a _ => Nat.cast_nonneg (m a))]
  -- integrate
  have hmono := Real.circleAverage_mono hintg (hintf.add hintsum) hpt
  have hadd : Real.circleAverage
      ((fun z => Real.posLog ‖f z‖) + fun z => ∑ a ∈ T, (m a : ℝ) * max 0 (-Real.log ‖z - a‖))
        c R
      = Real.circleAverage (fun z => Real.posLog ‖f z‖) c R
        + Real.circleAverage (fun z => ∑ a ∈ T, (m a : ℝ) * max 0 (-Real.log ‖z - a‖)) c R :=
    Real.circleAverage_add hintf hintsum
  have hsumavg : Real.circleAverage
      (fun z => ∑ a ∈ T, (m a : ℝ) * max 0 (-Real.log ‖z - a‖)) c R
      = ∑ a ∈ T, (m a : ℝ)
          * Real.circleAverage (fun z => max 0 (-Real.log ‖z - a‖)) c R := by
    rw [Real.circleAverage_fun_sum hinta]
    refine Finset.sum_congr rfl ?_
    intro a _
    have := Real.circleAverage_fun_smul (a := (m a : ℝ))
      (f := fun z : ℂ => max 0 (-Real.log ‖z - a‖)) (c := c) (R := R)
    simpa [smul_eq_mul] using this
  have hterm : ∑ a ∈ T, (m a : ℝ)
      * Real.circleAverage (fun z => max 0 (-Real.log ‖z - a‖)) c R
      ≤ ∑ a ∈ T, (m a : ℝ) * Real.log 2 := by
    refine Finset.sum_le_sum ?_
    intro a ha
    exact mul_le_mul_of_nonneg_left
      (circleAverage_negPart_log_norm_sub_le hR (hTmem a ha)) (Nat.cast_nonneg _)
  have hfinal : ∑ a ∈ T, (m a : ℝ) * Real.log 2 = (∑ a ∈ T, (m a : ℝ)) * Real.log 2 := by
    rw [Finset.sum_mul]
  rw [hadd, hsumavg] at hmono
  linarith [hmono, hterm, hfinal.symm.le, hfinal.le]

/-! ## The maximum-modulus bound by proximity -/

/-- **Maximum modulus bounded by boundary proximity, across a factorization.**  Combining the
Poisson bound for the zero-free cofactor with the `log 2` per-zero proximity cost. -/
theorem log_norm_le_proximity_of_factor
    {f g : ℂ → ℂ} {c w : ℂ} {R r : ℝ} {T : Finset ℂ} {m : ℂ → ℕ}
    (hR : 1 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hgfree : ∀ z ∈ closedBall c R, g z ≠ 0)
    (hTmem : ∀ a ∈ T, a ∈ closedBall c R)
    (hfac : ∀ z ∈ closedBall c R, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    (hsph : ∀ z ∈ sphere c R, f z ≠ 0)
    (hw : w ∈ ball c R) (hwr : ‖w - c‖ ≤ r) (hrR : r < R) :
    Real.log ‖f w‖
      ≤ (∑ a ∈ T, (m a : ℝ)) * (Real.log (2 * R) + (R + r) / (R - r) * Real.log 2)
        + (R + r) / (R - r) * Real.circleAverage (fun z => Real.posLog ‖f z‖) c R := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hwr
  have hK0 : 0 ≤ (R + r) / (R - r) := by
    have : 0 < R - r := by linarith
    positivity
  have h1 := log_norm_le_of_factor hR hg hgfree hTmem hfac hw hwr hrR
  have h2 := circleAverage_posLog_cofactor_le hR hf hg hTmem hfac hsph
  have h3 : (R + r) / (R - r) * Real.circleAverage (fun z => Real.posLog ‖g z‖) c R
      ≤ (R + r) / (R - r)
        * (Real.circleAverage (fun z => Real.posLog ‖f z‖) c R
            + (∑ a ∈ T, (m a : ℝ)) * Real.log 2) :=
    mul_le_mul_of_nonneg_left h2 hK0
  have h4 : (R + r) / (R - r)
      * (Real.circleAverage (fun z => Real.posLog ‖f z‖) c R
          + (∑ a ∈ T, (m a : ℝ)) * Real.log 2)
      = (R + r) / (R - r) * Real.circleAverage (fun z => Real.posLog ‖f z‖) c R
        + (∑ a ∈ T, (m a : ℝ)) * ((R + r) / (R - r) * Real.log 2) := by ring
  have h5 : (∑ a ∈ T, (m a : ℝ)) * (Real.log (2 * R) + (R + r) / (R - r) * Real.log 2)
      = (∑ a ∈ T, (m a : ℝ)) * Real.log (2 * R)
        + (∑ a ∈ T, (m a : ℝ)) * ((R + r) / (R - r) * Real.log 2) := by ring
  rw [h5]
  rw [h4] at h3
  linarith [h1, h3]

/-- **Maximum modulus bounded by boundary proximity, for an entire function.**  For an entire
function with no zero on the boundary circle, the log-modulus at an interior point is bounded by the
Poisson-weighted proximity average plus a multiple of the number of zeros in the ball. -/
theorem log_norm_le_proximity_of_entire {f : ℂ → ℂ} {c w : ℂ} {R r : ℝ}
    (hR : 1 ≤ R) (hf : AnalyticOnNhd ℂ f Set.univ)
    (hnz : ∀ a : ℂ, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hsph : ∀ z ∈ sphere c R, f z ≠ 0)
    (hw : w ∈ ball c R) (hwr : ‖w - c‖ ≤ r) (hrR : r < R) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ), (∀ a ∈ T, a ∈ closedBall c R) ∧
      Real.log ‖f w‖
        ≤ (∑ a ∈ T, (m a : ℝ)) * (Real.log (2 * R) + (R + r) / (R - r) * Real.log 2)
          + (R + r) / (R - r) * Real.circleAverage (fun z => Real.posLog ‖f z‖) c R := by
  obtain ⟨T, m, g, hg, hgfree, hTmem, hfac⟩ :=
    exists_zero_free_factor_closedBall isOpen_univ (Set.subset_univ _) hf
      (fun a _ => hnz a)
  refine ⟨T, m, hTmem, ?_⟩
  exact log_norm_le_proximity_of_factor hR (hf.mono (Set.subset_univ _))
    (hg.mono (Set.subset_univ _)) hgfree hTmem (fun z _ => hfac z (Set.mem_univ z)) hsph hw hwr hrR

/-! ## Radii free of boundary zeros -/

/-- **Good radii are cofinal.**  A nonzero entire function has only finitely many zeros in any
closed ball, so in every unit interval of radii there is one whose circle carries no zero. -/
theorem exists_radius_no_boundary_zero {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hnz : ∀ a : ℂ, ¬ ∀ᶠ z in 𝓝 a, f z = 0) (R₀ : ℝ) :
    ∃ R, R₀ ≤ R ∧ R ≤ R₀ + 1 ∧ ∀ z ∈ sphere c R, f z ≠ 0 := by
  classical
  have hfin : {z ∈ closedBall c (R₀ + 1) | f z = 0}.Finite :=
    finite_zeros_closedBall (hf.mono (Set.subset_univ _)) (fun z _ => hnz z)
  have hbad : ((fun z : ℂ => ‖z - c‖) '' {z ∈ closedBall c (R₀ + 1) | f z = 0}).Finite :=
    hfin.image _
  have hinf : (Set.Icc R₀ (R₀ + 1)).Infinite := Set.Icc_infinite (by linarith)
  obtain ⟨R, hR⟩ := (hinf.sdiff hbad).nonempty
  obtain ⟨hRmem, hRbad⟩ := hR
  obtain ⟨hR₀, hR₁⟩ := Set.mem_Icc.mp hRmem
  refine ⟨R, hR₀, hR₁, ?_⟩
  intro z hz hfz
  apply hRbad
  have hzc : ‖z - c‖ = R := by simpa [mem_sphere_iff_norm] using hz
  refine ⟨z, ⟨?_, hfz⟩, hzc⟩
  rw [mem_closedBall_iff_norm, hzc]
  exact hR₁

/-! ## Jensen's formula across a factorization -/

/-- **Jensen's formula in factorized form.**  If `f = ∏ (· - a)^{m a} · g` on a closed ball with `g`
zero-free there and `f` nonvanishing on the boundary circle, the boundary average of `log ‖f‖` is
`(∑ m a) log R + log ‖g c‖`.  Each zero contributes exactly `log R`. -/
theorem circleAverage_log_norm_of_factor {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} {T : Finset ℂ} {m : ℂ → ℕ}
    (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hgfree : ∀ z ∈ closedBall c R, g z ≠ 0)
    (hTmem : ∀ a ∈ T, a ∈ closedBall c R)
    (hfac : ∀ z ∈ closedBall c R, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    (hsph : ∀ z ∈ sphere c R, f z ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖f z‖) c R
      = (∑ a ∈ T, (m a : ℝ)) * Real.log R + Real.log ‖g c‖ := by
  classical
  have habs : |R| = R := abs_of_pos hR
  have hsubball : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  have hinta : ∀ a ∈ T, CircleIntegrable (fun z => (m a : ℝ) * Real.log ‖z - a‖) c R := by
    intro a _
    have hmero : MeromorphicOn (fun z : ℂ => z - a) (sphere c |R|) :=
      (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
    exact hmero.circleIntegrable_log_norm.const_mul _
  have hintsum : CircleIntegrable
      (fun z => ∑ a ∈ T, (m a : ℝ) * Real.log ‖z - a‖) c R :=
    CircleIntegrable.fun_sum T hinta
  have hintg : CircleIntegrable (fun z => Real.log ‖g z‖) c R := by
    have hmerog : MeromorphicOn g (sphere c |R|) := by
      rw [habs]
      exact (hg.mono hsubball).meromorphicOn
    exact hmerog.circleIntegrable_log_norm
  have heq : Set.EqOn (fun z => Real.log ‖f z‖)
      ((fun z : ℂ => ∑ a ∈ T, (m a : ℝ) * Real.log ‖z - a‖) + fun z : ℂ => Real.log ‖g z‖)
      (sphere c |R|) := by
    intro z hz
    rw [habs] at hz
    have hzball : z ∈ closedBall c R := hsubball hz
    have hfz : f z ≠ 0 := hsph z hz
    have hnorm : ‖f z‖ = (∏ a ∈ T, ‖z - a‖ ^ (m a)) * ‖g z‖ := by
      rw [hfac z hzball, norm_mul, norm_prod]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro a _
      rw [norm_pow]
    have hgz : ‖g z‖ ≠ 0 := norm_ne_zero_iff.mpr (hgfree z hzball)
    have hprodne : (∏ a ∈ T, ‖z - a‖ ^ (m a)) ≠ 0 := by
      intro hcon
      apply hfz
      have : ‖f z‖ = 0 := by rw [hnorm, hcon, zero_mul]
      exact norm_eq_zero.mp this
    simp only [Pi.add_apply]
    rw [hnorm, Real.log_mul hprodne hgz,
      Real.log_prod (fun a ha => Finset.prod_ne_zero_iff.mp hprodne a ha)]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Real.log_pow]
  have hsumavg : Real.circleAverage
      (fun z => ∑ a ∈ T, (m a : ℝ) * Real.log ‖z - a‖) c R
      = (∑ a ∈ T, (m a : ℝ)) * Real.log R := by
    rw [Real.circleAverage_fun_sum hinta, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro a ha
    have hsm := Real.circleAverage_fun_smul (a := (m a : ℝ))
      (f := fun z : ℂ => Real.log ‖z - a‖) (c := c) (R := R)
    have hlog : Real.circleAverage (fun z : ℂ => Real.log ‖z - a‖) c R = Real.log R :=
      circleAverage_log_norm_sub_const_of_mem_closedBall (by rw [habs]; exact hTmem a ha)
    rw [show (fun z : ℂ => (m a : ℝ) * Real.log ‖z - a‖)
        = fun z : ℂ => (m a : ℝ) • Real.log ‖z - a‖ from rfl, hsm, hlog, smul_eq_mul]
  have hgavg : Real.circleAverage (fun z => Real.log ‖g z‖) c R = Real.log ‖g c‖ := by
    refine AnalyticOnNhd.circleAverage_log_norm_of_ne_zero ?_ ?_
    · rw [habs]; exact hg
    · rw [habs]; exact hgfree
  rw [Real.circleAverage_congr_sphere heq, Real.circleAverage_add hintsum hintg, hsumavg, hgavg]

/-- **Jensen's count bound.**  If `f` is bounded by `M` on the boundary circle of radius `R`, does
not vanish there or at the centre, then its zeros in the concentric ball of radius `R₁ < R` number at
most `(log M - log ‖f c‖) / log (R / R₁)`.  Each such zero contributes at least `log (R / R₁)` to
Jensen's formula, and all contributions are nonnegative. -/
theorem sum_multiplicity_le_of_factor {f g : ℂ → ℂ} {c : ℂ} {R R₁ M : ℝ} {T : Finset ℂ} {m : ℂ → ℕ}
    (hR : 0 < R) (hR₁ : 0 < R₁)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hgfree : ∀ z ∈ closedBall c R, g z ≠ 0)
    (hTmem : ∀ a ∈ T, a ∈ closedBall c R)
    (hfac : ∀ z ∈ closedBall c R, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z)
    (hsph : ∀ z ∈ sphere c R, f z ≠ 0) (hfc : f c ≠ 0)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    (∑ a ∈ T.filter (fun a => ‖a - c‖ ≤ R₁), (m a : ℝ)) * Real.log (R / R₁)
      ≤ Real.log M - Real.log ‖f c‖ := by
  classical
  have habs : |R| = R := abs_of_pos hR
  have hcball : c ∈ closedBall c R := Metric.mem_closedBall_self (le_of_lt hR)
  have hsubball : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  -- the centre value splits
  have hnormc : ‖f c‖ = (∏ a ∈ T, ‖c - a‖ ^ (m a)) * ‖g c‖ := by
    rw [hfac c hcball, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro a _
    rw [norm_pow]
  have hgc : ‖g c‖ ≠ 0 := norm_ne_zero_iff.mpr (hgfree c hcball)
  have hprodne : (∏ a ∈ T, ‖c - a‖ ^ (m a)) ≠ 0 := by
    intro hcon
    apply hfc
    have : ‖f c‖ = 0 := by rw [hnormc, hcon, zero_mul]
    exact norm_eq_zero.mp this
  have hlogc : Real.log ‖f c‖
      = ∑ a ∈ T, (m a : ℝ) * Real.log ‖c - a‖ + Real.log ‖g c‖ := by
    rw [hnormc, Real.log_mul hprodne hgc,
      Real.log_prod (fun a ha => Finset.prod_ne_zero_iff.mp hprodne a ha)]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Real.log_pow]
  -- Jensen's formula
  have hjensen := circleAverage_log_norm_of_factor hR hg hgfree hTmem hfac hsph
  -- the boundary bound
  have hintf : CircleIntegrable (fun z => Real.log ‖f z‖) c R := by
    have hmerof : MeromorphicOn f (sphere c |R|) := by
      rw [habs]
      exact (hf.mono hsubball).meromorphicOn
    exact hmerof.circleIntegrable_log_norm
  have hbound : Real.circleAverage (fun z => Real.log ‖f z‖) c R ≤ Real.log M := by
    refine Real.circleAverage_mono_on_of_le_circle hintf ?_
    intro z hz
    rw [habs] at hz
    exact Real.log_le_log (norm_pos_iff.mpr (hsph z hz)) (hM z hz)
  -- each zero contributes nonnegatively
  have hterm : ∀ a ∈ T, 0 ≤ (m a : ℝ) * (Real.log R - Real.log ‖c - a‖) := by
    intro a ha
    rcases Nat.eq_zero_or_pos (m a) with h | h
    · rw [h]
      simp
    · have hne : ‖c - a‖ ^ (m a) ≠ 0 := Finset.prod_ne_zero_iff.mp hprodne a ha
      have hpos : 0 < ‖c - a‖ := by
        rcases eq_or_lt_of_le (norm_nonneg (c - a)) with h' | h'
        · exact absurd (by rw [← h']; exact zero_pow (by omega)) hne
        · exact h'
      have hle : ‖c - a‖ ≤ R := by
        rw [norm_sub_rev]
        exact mem_closedBall_iff_norm.mp (hTmem a ha)
      have := Real.log_le_log hpos hle
      have hm0 : (0 : ℝ) ≤ (m a : ℝ) := Nat.cast_nonneg _
      nlinarith
  -- the filtered zeros contribute at least log (R / R₁) each
  have hfilter : ∀ a ∈ T.filter (fun a => ‖a - c‖ ≤ R₁),
      (m a : ℝ) * Real.log (R / R₁) ≤ (m a : ℝ) * (Real.log R - Real.log ‖c - a‖) := by
    intro a ha
    obtain ⟨haT, haR₁⟩ := Finset.mem_filter.mp ha
    rcases Nat.eq_zero_or_pos (m a) with h | h
    · rw [h]
      simp
    · have hne : ‖c - a‖ ^ (m a) ≠ 0 := Finset.prod_ne_zero_iff.mp hprodne a haT
      have hpos : 0 < ‖c - a‖ := by
        rcases eq_or_lt_of_le (norm_nonneg (c - a)) with h' | h'
        · exact absurd (by rw [← h']; exact zero_pow (by omega)) hne
        · exact h'
      have hle : ‖c - a‖ ≤ R₁ := by
        rw [norm_sub_rev]
        exact haR₁
      have hlog : Real.log ‖c - a‖ ≤ Real.log R₁ := Real.log_le_log hpos hle
      have hdiv : Real.log (R / R₁) = Real.log R - Real.log R₁ :=
        Real.log_div (ne_of_gt hR) (ne_of_gt hR₁)
      have hm0 : (0 : ℝ) ≤ (m a : ℝ) := Nat.cast_nonneg _
      rw [hdiv]
      nlinarith
  have hsubset : T.filter (fun a => ‖a - c‖ ≤ R₁) ⊆ T := Finset.filter_subset _ _
  have hstep : (∑ a ∈ T.filter (fun a => ‖a - c‖ ≤ R₁), (m a : ℝ)) * Real.log (R / R₁)
      ≤ ∑ a ∈ T, (m a : ℝ) * (Real.log R - Real.log ‖c - a‖) := by
    rw [Finset.sum_mul]
    calc ∑ a ∈ T.filter (fun a => ‖a - c‖ ≤ R₁), (m a : ℝ) * Real.log (R / R₁)
        ≤ ∑ a ∈ T.filter (fun a => ‖a - c‖ ≤ R₁),
            (m a : ℝ) * (Real.log R - Real.log ‖c - a‖) := Finset.sum_le_sum hfilter
      _ ≤ ∑ a ∈ T, (m a : ℝ) * (Real.log R - Real.log ‖c - a‖) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun a ha _ => hterm a ha)
  have hexpand : ∑ a ∈ T, (m a : ℝ) * (Real.log R - Real.log ‖c - a‖)
      = (∑ a ∈ T, (m a : ℝ)) * Real.log R - ∑ a ∈ T, (m a : ℝ) * Real.log ‖c - a‖ := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    ring
  rw [hexpand] at hstep
  rw [hjensen] at hbound
  linarith [hstep, hbound, hlogc]

/-! ## The maximum modulus bounded by the Nevanlinna data -/

/-- **`log M(r) ≲ T(R)`.**  For an entire function with no zero at the centre and none on the two
circles of radii `R` and `2R`, bounded by `M` on the outer circle, the log-modulus at any point with
`‖w - c‖ ≤ r < R` is bounded by the boundary proximity average and the Jensen zero count.  The zeros
inside the small ball are separated off and counted by Jensen's inequality; those between the two
radii are absorbed into the zero-free cofactor. -/
theorem log_norm_le_proximity_and_count_of_entire {f : ℂ → ℂ} {c w : ℂ} {R r M : ℝ}
    (hR : 1 ≤ R) (hwr : ‖w - c‖ ≤ r) (hrR : r < R) (hw : w ∈ ball c R)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hnz : ∀ a : ℂ, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hfc : f c ≠ 0)
    (hsph : ∀ z ∈ sphere c R, f z ≠ 0)
    (hsph2 : ∀ z ∈ sphere c (2 * R), f z ≠ 0)
    (hM : ∀ z ∈ sphere c (2 * R), ‖f z‖ ≤ M) :
    Real.log ‖f w‖
      ≤ ((Real.log M - Real.log ‖f c‖) / Real.log 2)
          * (Real.log (2 * R) + (R + r) / (R - r) * Real.log 2)
        + (R + r) / (R - r) * Real.circleAverage (fun z => Real.posLog ‖f z‖) c R := by
  classical
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hR2 : 0 < 2 * R := by linarith
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hwr
  have hK0 : 0 ≤ (R + r) / (R - r) := by
    have : 0 < R - r := by linarith
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2R : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  -- factor out all zeros in the large ball
  obtain ⟨T, m, g, hg, hgfree, hTmem, hfac⟩ :=
    exists_zero_free_factor_closedBall (R := 2 * R) isOpen_univ (Set.subset_univ _) hf
      (fun a _ => hnz a)
  set S : Finset ℂ := T.filter (fun a => ‖a - c‖ ≤ R) with hS
  set S' : Finset ℂ := T.filter (fun a => ¬ ‖a - c‖ ≤ R) with hS'
  set h : ℂ → ℂ := fun z => (∏ a ∈ S', (z - a) ^ (m a)) * g z with hh
  have hsmallsub : closedBall c R ⊆ closedBall c (2 * R) :=
    Metric.closedBall_subset_closedBall (by linarith)
  -- the enlarged cofactor is analytic and zero free on the small ball
  have hhan : AnalyticOnNhd ℂ h (closedBall c R) := by
    refine AnalyticOnNhd.mul ?_ (hg.mono (Set.subset_univ _))
    refine Finset.analyticOnNhd_fun_prod _ ?_
    intro a _ z _
    exact ((analyticAt_id).sub analyticAt_const).pow (m a)
  have hfar : ∀ a ∈ S', ∀ z ∈ closedBall c R, z - a ≠ 0 := by
    intro a ha z hz hcon
    have haR : ¬ ‖a - c‖ ≤ R := (Finset.mem_filter.mp ha).2
    have hzc : ‖z - c‖ ≤ R := mem_closedBall_iff_norm.mp hz
    have : a = z := by
      have := sub_eq_zero.mp hcon
      exact this.symm
    rw [this] at haR
    exact haR hzc
  have hhfree : ∀ z ∈ closedBall c R, h z ≠ 0 := by
    intro z hz
    rw [hh]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_) (hgfree z (hsmallsub hz))
    intro a ha
    exact pow_ne_zero _ (hfar a ha z hz)
  have hSmem : ∀ a ∈ S, a ∈ closedBall c R := by
    intro a ha
    rw [mem_closedBall_iff_norm]
    exact (Finset.mem_filter.mp ha).2
  have hfacS : ∀ z ∈ closedBall c R, f z = (∏ a ∈ S, (z - a) ^ (m a)) * h z := by
    intro z hz
    rw [hh, hfac z (Set.mem_univ z), ← mul_assoc]
    congr 1
    rw [hS, hS']
    exact (Finset.prod_filter_mul_prod_filter_not T (fun a => ‖a - c‖ ≤ R) _).symm
  -- the proximity bound at radius `R`
  have hprox := log_norm_le_proximity_of_factor hR (hf.mono (Set.subset_univ _)) hhan hhfree
    hSmem hfacS hsph hw hwr hrR
  -- the Jensen count at radius `2R`
  have hcount := sum_multiplicity_le_of_factor (R := 2 * R) (R₁ := R) (M := M) hR2 hR0
    (hf.mono (Set.subset_univ _)) (hg.mono (Set.subset_univ _)) hgfree hTmem
    (fun z _ => hfac z (Set.mem_univ z)) hsph2 hfc hM
  have hratio : Real.log (2 * R / R) = Real.log 2 := by
    rw [mul_div_assoc, div_self (ne_of_gt hR0), mul_one]
  rw [hratio] at hcount
  have hN : (∑ a ∈ S, (m a : ℝ)) ≤ (Real.log M - Real.log ‖f c‖) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact hcount
  have hpos : 0 ≤ Real.log (2 * R) + (R + r) / (R - r) * Real.log 2 := by
    have : 0 ≤ (R + r) / (R - r) * Real.log 2 := mul_nonneg hK0 (le_of_lt hlog2)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hN hpos
  linarith [hprox, hmul]

end GaloisForLFunctions.HTGeometry
