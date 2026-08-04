import GaloisForLFunctions.HTGeometry.RootProximity
import GaloisForLFunctions.HTGeometry.AnalyticRootFactor

/-!
# A minimum-modulus bound for polynomials

A monic polynomial is large wherever it is far from all of its roots: if every root is at distance at
least `H`, the modulus is at least `H` to the degree.  Consequently the radii on which the modulus is
small along a whole circle are confined to finitely many short intervals, one around the modulus of
each root, so any sufficiently long range of radii contains a circle on which the polynomial is
uniformly large.

This is the polynomial case of the minimum-modulus input that a composition-growth argument needs:
the image of a curve meets every circle in a range, and on a good circle the outer function cannot be
small.
-/

open MeasureTheory Polynomial Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Far from the roots means large.**  If every root of a monic complex polynomial is at distance
at least `H` from `z`, then `‖p z‖ ≥ H ^ deg p`. -/
theorem norm_eval_ge_of_roots_far {p : Polynomial ℂ} (hmonic : p.Monic) {z : ℂ} {H : ℝ}
    (hH : 0 ≤ H) (hfar : ∀ a ∈ p.roots, H ≤ ‖z - a‖) :
    H ^ p.natDegree ≤ ‖p.eval z‖ := by
  classical
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = p.natDegree :=
    (Polynomial.splits_iff_card_roots).mp hsplits
  have hfac : p = C p.leadingCoeff * (p.roots.map fun a => X - C a).prod :=
    Polynomial.Splits.eq_prod_roots hsplits
  have hlead : p.leadingCoeff = 1 := hmonic
  have heval : p.eval z = (p.roots.map fun a => z - a).prod := by
    conv_lhs => rw [hfac]
    rw [hlead, map_one, one_mul, Polynomial.eval_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod ?_
    refine Multiset.map_congr rfl ?_
    intro x _
    simp
  have hbase := pow_card_le_norm_prod (T := z) (c := H) hH hfar
  rw [hcard] at hbase
  rw [heval]
  exact hbase

/-- **A good circle exists.**  If the range of radii is longer than `2 H` times the degree, some
radius in it keeps every point of the circle at distance at least `H` from every root, hence keeps
the polynomial at least `H ^ deg`. -/
theorem exists_radius_norm_eval_ge {p : Polynomial ℂ} (hmonic : p.Monic) {H A B : ℝ}
    (hH : 0 < H) (hAB : 2 * (p.natDegree : ℝ) * H < B - A) :
    ∃ s ∈ Set.Icc A B, ∀ z : ℂ, ‖z‖ = s → H ^ p.natDegree ≤ ‖p.eval z‖ := by
  classical
  -- the bad radii lie near the moduli of the roots
  set bad : Set ℝ := ⋃ a ∈ p.roots.toFinset, Set.Ioo (‖a‖ - H) (‖a‖ + H) with hbad
  have hmeas : volume bad ≤ ∑ a ∈ p.roots.toFinset, volume (Set.Ioo (‖a‖ - H) (‖a‖ + H)) :=
    measure_biUnion_finset_le _ _
  have hval : ∀ a : ℂ, volume (Set.Ioo (‖a‖ - H) (‖a‖ + H)) = ENNReal.ofReal (2 * H) := by
    intro a
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hcard : (p.roots.toFinset.card : ℝ) ≤ (p.natDegree : ℝ) := by
    have h1 : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    have h2 : Multiset.card p.roots = p.natDegree :=
      (Polynomial.splits_iff_card_roots).mp (IsAlgClosed.splits p)
    rw [← h2]
    exact_mod_cast h1
  have hsum : volume bad ≤ ENNReal.ofReal (2 * (p.natDegree : ℝ) * H) := by
    refine le_trans hmeas ?_
    rw [Finset.sum_congr rfl (fun a _ => hval a), Finset.sum_const, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hcard, hH]
  -- the range is longer than the bad set
  have hAB' : A ≤ B := by linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
    (Nat.cast_nonneg p.natDegree)) (le_of_lt hH)]
  have hIcc : volume (Set.Icc A B) = ENNReal.ofReal (B - A) := Real.volume_Icc
  have hlt : volume bad < volume (Set.Icc A B) := by
    rw [hIcc]
    refine lt_of_le_of_lt hsum ?_
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr hAB
  have hne : ¬ (Set.Icc A B ⊆ bad) := by
    intro hsub
    exact absurd (measure_mono hsub) (not_le.mpr hlt)
  obtain ⟨s, hsmem, hsbad⟩ := Set.not_subset.mp hne
  refine ⟨s, hsmem, ?_⟩
  intro z hz
  refine norm_eval_ge_of_roots_far hmonic (le_of_lt hH) ?_
  intro a ha
  have hnot : s ∉ Set.Ioo (‖a‖ - H) (‖a‖ + H) := by
    intro hmem
    exact hsbad (Set.mem_biUnion (Multiset.mem_toFinset.mpr ha) hmem)
  have hdist : H ≤ |s - ‖a‖| := by
    rcases le_or_gt s (‖a‖ - H) with h | h
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · have h2 : ‖a‖ + H ≤ s := by
        by_contra hcon
        exact hnot ⟨h, not_le.mp hcon⟩
      rw [abs_of_nonneg (by linarith)]
      linarith
  have habs : |‖z‖ - ‖a‖| ≤ ‖z - a‖ := abs_norm_sub_norm_le z a
  rw [hz] at habs
  linarith

/-! ## Combining with a zero-free factor -/

/-- **A good circle for a function with extracted zeros.**  If `f` factors on a disc as a monic
polynomial times a factor bounded below, then some circle in a long enough range carries a lower
bound for `f` itself: the polynomial contributes `H ^ deg` and the other factor its own bound.

The zero-free lower bound is taken as a hypothesis rather than derived here; the corpus already
proves it for a zero-free analytic function from one anchor value and one supremum
(`norm_lower_bound_of_anchor`), which lives in the RH area and must not be imported into this
one. -/
theorem exists_radius_norm_ge_of_factorization {f g : ℂ → ℂ} {P : Polynomial ℂ}
    {H A B L : ℝ} (hmonic : P.Monic) (hH : 0 < H) (hL : 0 ≤ L)
    (hAB : 2 * (P.natDegree : ℝ) * H < B - A)
    (hfac : ∀ z : ℂ, ‖z‖ ≤ B → f z = P.eval z * g z)
    (hglow : ∀ z : ℂ, ‖z‖ ≤ B → L ≤ ‖g z‖) :
    ∃ s ∈ Set.Icc A B, ∀ z : ℂ, ‖z‖ = s → H ^ P.natDegree * L ≤ ‖f z‖ := by
  obtain ⟨s, hs, hbig⟩ := exists_radius_norm_eval_ge hmonic hH hAB
  refine ⟨s, hs, ?_⟩
  intro z hz
  have hzB : ‖z‖ ≤ B := by
    rw [hz]
    exact hs.2
  have hP := hbig z hz
  have hg := hglow z hzB
  have hHpow : (0 : ℝ) ≤ H ^ P.natDegree := by positivity
  have hPnn : (0 : ℝ) ≤ ‖P.eval z‖ := norm_nonneg _
  calc H ^ P.natDegree * L ≤ ‖P.eval z‖ * ‖g z‖ := by
        exact mul_le_mul hP hg hL hPnn
    _ = ‖f z‖ := by rw [hfac z hzB, norm_mul]

/-! ## Bounding the zero-free factor above -/

/-- **The zero-free factor is bounded on a circle.**  If all roots of the monic polynomial lie at
distance at least `H` inside the circle of radius `R`, then on that circle the polynomial is at least
`H ^ deg`, so the other factor is at most the bound for `f` divided by that. -/
theorem norm_zero_free_factor_le {f g : ℂ → ℂ} {P : Polynomial ℂ} {R Mf H : ℝ}
    (hP : P.Monic) (hH : 0 < H) (hroots : ∀ a ∈ P.roots, ‖a‖ ≤ R - H)
    (hfac : ∀ z : ℂ, ‖z‖ = R → f z = P.eval z * g z)
    (hMf : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ Mf) :
    ∀ z : ℂ, ‖z‖ = R → ‖g z‖ ≤ Mf / H ^ P.natDegree := by
  intro z hz
  have hfar : ∀ a ∈ P.roots, H ≤ ‖z - a‖ := by
    intro a ha
    have h1 : ‖z‖ - ‖a‖ ≤ ‖z - a‖ := norm_sub_norm_le z a
    have h2 : ‖a‖ ≤ R - H := hroots a ha
    rw [hz] at h1
    linarith
  have hPz : H ^ P.natDegree ≤ ‖P.eval z‖ :=
    norm_eval_ge_of_roots_far hP (le_of_lt hH) hfar
  have hHpow : (0 : ℝ) < H ^ P.natDegree := by positivity
  have hnorm : ‖f z‖ = ‖P.eval z‖ * ‖g z‖ := by
    rw [hfac z hz, norm_mul]
  have hle : H ^ P.natDegree * ‖g z‖ ≤ Mf := by
    have h1 : H ^ P.natDegree * ‖g z‖ ≤ ‖P.eval z‖ * ‖g z‖ :=
      mul_le_mul_of_nonneg_right hPz (norm_nonneg _)
    have h2 : ‖f z‖ ≤ Mf := hMf z hz
    rw [hnorm] at h2
    linarith
  rw [le_div_iff₀ hHpow]
  linarith

/-- **Maximum modulus on a ball, in circle form.**  A bound on the circle bounds the whole closed
ball. -/
theorem norm_le_of_sphere_bound {g : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 R))
    (hM : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ ≤ M) :
    ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ M := by
  intro z hz
  have hRne : R ≠ 0 := ne_of_gt hR
  have hballsub : Metric.ball (0 : ℂ) R ⊆ Metric.closedBall (0 : ℂ) R := Metric.ball_subset_closedBall
  have hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) :=
    (hg.differentiableOn).mono hballsub
  have hclos : closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R :=
    closure_ball (0 : ℂ) hRne
  have hcont : ContinuousOn g (closure (Metric.ball (0 : ℂ) R)) := by
    rw [hclos]
    exact hg.continuousOn
  have hdc : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) := ⟨hdiff, hcont⟩
  have hfront : ∀ w ∈ frontier (Metric.ball (0 : ℂ) R), ‖g w‖ ≤ M := by
    intro w hw
    rw [frontier_ball (0 : ℂ) hRne] at hw
    have : ‖w‖ = R := by
      simpa [mem_sphere_iff_norm] using hw
    exact hM w this
  have hzmem : z ∈ closure (Metric.ball (0 : ℂ) R) := by
    rw [hclos]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc hfront hzmem

/-- **The extracted product is large on a larger circle.**  If every extracted point lies within
radius `R`, then on the circle of radius `R' ≥ R` the product of the linear factors is at least
`(R' - R)` to the total multiplicity.  This is the form the factorisation produces, avoiding a detour
through the polynomial's root multiset. -/
theorem prod_norm_ge_of_roots_inside {T : Finset ℂ} {m : ℂ → ℕ} {R R' : ℝ}
    (hT : ∀ a ∈ T, ‖a‖ ≤ R) (hRR' : R ≤ R') {z : ℂ} (hz : ‖z‖ = R') :
    (R' - R) ^ (∑ a ∈ T, m a) ≤ ∏ a ∈ T, ‖z - a‖ ^ (m a) := by
  classical
  have hstep : ∀ a ∈ T, (R' - R) ^ (m a) ≤ ‖z - a‖ ^ (m a) := by
    intro a ha
    have hdist : R' - R ≤ ‖z - a‖ := by
      have h1 : ‖z‖ - ‖a‖ ≤ ‖z - a‖ := norm_sub_norm_le z a
      have h2 : ‖a‖ ≤ R := hT a ha
      rw [hz] at h1
      linarith
    exact pow_le_pow_left₀ (by linarith) hdist _
  have hsum : (R' - R) ^ (∑ a ∈ T, m a) = ∏ a ∈ T, (R' - R) ^ (m a) :=
    (Finset.prod_pow_eq_pow_sum T m (R' - R)).symm
  rw [hsum]
  refine Finset.prod_le_prod ?_ hstep
  intro a _
  positivity

/-! ## The zero-free cofactor with both bounds -/

/-- **The cofactor is zero-free inside and bounded outside.**  Extracting the zeros of the inner ball
and estimating on a larger circle gives, in one statement, everything the Borel--Carathéodory
minimum-modulus theorem asks of the cofactor: it is analytic, zero-free on the inner ball, and
bounded on the larger ball by the bound for `f` divided by the gap to the power of the total
multiplicity. -/
theorem exists_zero_free_cofactor_bounds {f : ℂ → ℂ} {U : Set ℂ} {R R' Mf : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (hRR' : R < R')
    (hball : Metric.closedBall (0 : ℂ) R' ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hMf : ∀ z : ℂ, ‖z‖ = R' → ‖f z‖ ≤ Mf) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g U ∧ (∀ a ∈ T, ‖a‖ ≤ R) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0) ∧
      (∀ z : ℂ, ‖z‖ ≤ R' → ‖g z‖ ≤ Mf / (R' - R) ^ (∑ a ∈ T, m a)) ∧
      (∀ z ∈ U, f z = (∏ a ∈ T, (z - a) ^ (m a)) * g z) := by
  classical
  have hballR : Metric.closedBall (0 : ℂ) R ⊆ U :=
    subset_trans (Metric.closedBall_subset_closedBall (le_of_lt hRR')) hball
  obtain ⟨T, m, g, hg, hgfree, hTmem, hfac⟩ :=
    exists_zero_free_factor_closedBall hU hballR hf hnz
  have hTnorm : ∀ a ∈ T, ‖a‖ ≤ R := by
    intro a ha
    simpa [Metric.mem_closedBall, dist_eq_norm] using hTmem a ha
  have hgap : (0 : ℝ) < (R' - R) ^ (∑ a ∈ T, m a) := by
    have : (0 : ℝ) < R' - R := by linarith
    positivity
  have hcirc : ∀ z : ℂ, ‖z‖ = R' → ‖g z‖ ≤ Mf / (R' - R) ^ (∑ a ∈ T, m a) := by
    intro z hz
    have hzU : z ∈ U := by
      refine hball ?_
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_eq hz
    have hnorm : ‖f z‖ = (∏ a ∈ T, ‖z - a‖ ^ (m a)) * ‖g z‖ := by
      rw [hfac z hzU, norm_mul, norm_prod]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro a _
      rw [norm_pow]
    have hprod : (R' - R) ^ (∑ a ∈ T, m a) ≤ ∏ a ∈ T, ‖z - a‖ ^ (m a) :=
      prod_norm_ge_of_roots_inside hTnorm (le_of_lt hRR') hz
    have hstep : (R' - R) ^ (∑ a ∈ T, m a) * ‖g z‖ ≤ ‖f z‖ := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    have hfle : ‖f z‖ ≤ Mf := hMf z hz
    rw [le_div_iff₀ hgap]
    linarith
  have hballR' : ∀ z : ℂ, ‖z‖ ≤ R' → ‖g z‖ ≤ Mf / (R' - R) ^ (∑ a ∈ T, m a) := by
    refine norm_le_of_sphere_bound (by linarith) ?_ hcirc
    exact hg.mono hball
  exact ⟨T, m, g, hg, hTnorm, hgfree, hballR', hfac⟩

/-! ## A self-contained zero-count bound -/

/-- **The total multiplicity is bounded by the growth ratio.**  From the factorisation alone — no
Jensen formula — the zeros of the inner ball, counted with multiplicity, satisfy
`(∑ m) log((R' − R)/R) ≤ log(Mf/‖f 0‖)`.  Each extracted point contributes a factor at most `R` at
the centre while costing a factor at least `R' − R` in the cofactor's bound. -/
theorem sum_multiplicity_mul_log_le {f g : ℂ → ℂ} {T : Finset ℂ} {m : ℂ → ℕ} {R R' Mf : ℝ}
    (hR : 0 < R) (hRR' : 2 * R < R') (hMf0 : 0 < Mf)
    (hTnorm : ∀ a ∈ T, ‖a‖ ≤ R)
    (hgbound : ‖g 0‖ ≤ Mf / (R' - R) ^ (∑ a ∈ T, m a))
    (hfac0 : f 0 = (∏ a ∈ T, ((0 : ℂ) - a) ^ (m a)) * g 0)
    (hf0 : f 0 ≠ 0) :
    ((∑ a ∈ T, m a : ℕ) : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (Mf / ‖f 0‖) := by
  classical
  have hgap : 0 < R' - R := by linarith
  have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hnorm0 : ‖f 0‖ = (∏ a ∈ T, ‖a‖ ^ (m a)) * ‖g 0‖ := by
    rw [hfac0, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro a _
    rw [norm_pow, zero_sub, norm_neg]
  have hprod : ∏ a ∈ T, ‖a‖ ^ (m a) ≤ R ^ (∑ a ∈ T, m a) := by
    have hstep : ∀ a ∈ T, ‖a‖ ^ (m a) ≤ R ^ (m a) := by
      intro a ha
      exact pow_le_pow_left₀ (norm_nonneg _) (hTnorm a ha) _
    have hsum : R ^ (∑ a ∈ T, m a) = ∏ a ∈ T, R ^ (m a) :=
      (Finset.prod_pow_eq_pow_sum T m R).symm
    rw [hsum]
    refine Finset.prod_le_prod ?_ hstep
    intro a _
    positivity
  have hgapPow : (0 : ℝ) < (R' - R) ^ (∑ a ∈ T, m a) := by positivity
  have hchain : ‖f 0‖ ≤ R ^ (∑ a ∈ T, m a) * (Mf / (R' - R) ^ (∑ a ∈ T, m a)) := by
    rw [hnorm0]
    exact mul_le_mul hprod hgbound (norm_nonneg _) (by positivity)
  have hlog := Real.log_le_log hf0pos hchain
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_div (ne_of_gt hMf0) (ne_of_gt hgapPow), Real.log_pow, Real.log_pow] at hlog
  rw [Real.log_div (ne_of_gt hgap) (ne_of_gt hR), Real.log_div (ne_of_gt hMf0) (ne_of_gt hf0pos)]
  push_cast at hlog ⊢
  linarith

/-! ## The loss from the zeros, bounded -/

/-- **The zero loss is controlled by the count bound.**  If the total multiplicity `N` satisfies
`N D ≤ C` with `D > 0`, then the factor `H ^ N` costs at most `(C/D)·(−log H)`:

  `log L + (C/D) log H ≤ log (H ^ N · L)`.

Combined with `sum_multiplicity_mul_log_le` this turns the minimum-modulus conclusion into an
explicit floor that does not mention the number of zeros. -/
theorem log_pow_mul_ge_of_count {H L C D : ℝ} {N : ℕ} (hH : 0 < H) (hH1 : H ≤ 1) (hL : 0 < L)
    (hD : 0 < D) (hcount : (N : ℝ) * D ≤ C) :
    Real.log L + (C / D) * Real.log H ≤ Real.log (H ^ N * L) := by
  have hlogH : Real.log H ≤ 0 := Real.log_nonpos (le_of_lt hH) hH1
  have hNC : (N : ℝ) ≤ C / D := by
    rw [le_div_iff₀ hD]
    exact hcount
  have hmul : (C / D) * Real.log H ≤ (N : ℝ) * Real.log H :=
    mul_le_mul_of_nonpos_right hNC hlogH
  have hsplit : Real.log (H ^ N * L) = (N : ℝ) * Real.log H + Real.log L := by
    rw [Real.log_mul (by positivity) (ne_of_gt hL), Real.log_pow]
  rw [hsplit]
  linarith

end GaloisForLFunctions.HTGeometry
