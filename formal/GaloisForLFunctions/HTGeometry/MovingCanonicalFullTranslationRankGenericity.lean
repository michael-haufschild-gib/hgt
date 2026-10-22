import GaloisForLFunctions.HTGeometry.MovingCanonicalFiniteJetSubmersion
import GaloisForLFunctions.HTGeometry.CompactCauchyRowPacketAtlas
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierRelationFree
import GaloisForLFunctions.HTGeometry.InjectiveShiftConfigurationTopology
import GaloisForLFunctions.HTGeometry.NevanlinnaNoncriticalProjectiveCompactPatch

/-!
# Generic full rank of moving canonical jet evaluation matrices

For a bounded real sequence `θ`, `L_θ(z) = Σ_n ((a_n(θ) - z)⁻¹ - a_n(θ)⁻¹)` is the moving canonical
log-derivative with zeros `a_n(θ) = n + 1 + δ(θ n)`. On the upper half-plane its derivatives are
`L_θ^{(k)}(z) = k! J_k(θ, z)` with `J_k = Σ_n (a_n - z)^{-(k+1)}` for `k ≥ 1`, and the jets are
jointly continuous in `(θ, z)`. Perturbing finitely many coordinates of `θ` gives smooth
finite-dimensional jet families whose derivative in the perturbation is surjective at injective
upper-half-plane nodes. A transversality argument on compact patches then shows that the expanded
evaluation matrix of a finite differential pattern (rows: evaluation points; columns: monomials in
`z` and jets) has full column rank for a dense open set of `θ`. Covering compact sets of shift
configurations by finitely many row packets and applying the Baire category theorem over the
countably many finite patterns yields a dense residual set of `θ` for which every finite pattern
and every injective shift configuration have a full-rank witness, hence have only the zero
pattern relation.

## Main results

- `iteratedDeriv_movingCanonicalLogDerivative_eq_factorial_mul_normalizedJet`:
  `L_θ^{(k)}(z) = k! · movingCanonicalNormalizedJet θ k z` for `Im z > 0`.
- `continuousAt_iteratedDeriv_movingCanonicalLogDerivative_joint`: joint continuity of
  `(θ, z) ↦ L_θ^{(k)}(z)` on bounded sequences times the upper half-plane.
- `fderiv_movingCanonicalExpandedJetFamily_probe_surjective`: surjectivity of the probe derivative.
- `compact_movingCanonicalExpandedActualEvaluation_avoidance_dense`: density of `θ` avoiding the
  rank-defect locus over a compact patch.
- `movingCanonicalExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness`: a full-rank
  witness forces every pattern relation to have zero coefficients.
- `allFinitePatterns_movingCanonicalExpandedFullRankWitness_dense_residual` and
  `allFinitePatterns_movingCanonicalExpandedRelationFree_dense_residual`: full-rank witnesses and
  relation-freeness hold simultaneously for all finite patterns and all injective shifts on a dense
  residual set of `θ`.

## Hypotheses

The final dense-residual theorems over all finite patterns are unconditional. Intermediate results
take explicit dimension-counting hypotheses (`hrows`: `#columns + degree < #rows`; `hdim`: the
real dimension of the node-parameter space is below `2 (#rows - #columns - degree + 1)`),
injectivity of the exponent map,
smoothness of the node map, and injective upper-half-plane nodes; for canonical finite patterns
these are discharged by the `carrierPattern_*` lemmas. `movingCanonicalExpandedFullRankWitness`
and `movingCanonicalExpandedPatternRelationHolds` are Prop-valued definitions describing rank and
relation conditions, not assumed inputs of the final theorems.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-- Uniform zero majorant: `1 / a_n(θ)² ≤ 4 / (n + 1)²` for every bounded `θ`. -/
theorem movingCanonicalZero_inv_sq_le_nat_majorant
    (θ : BoundedRealSequence) (a : ℕ) :
    1 / ‖(movingCanonicalZero θ a : ℂ)‖ ^ (2 : ℕ) ≤
      4 / ((a : ℝ) + 1) ^ (2 : ℕ) := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (movingCanonicalZero_pos θ a)]
  have hl : ((a : ℝ) + 1) / 2 ≤ movingCanonicalZero θ a := by
    have h := movingCanonicalZero_lower θ a
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have hap : 0 < (a : ℝ) + 1 := by positivity
  have hzp := movingCanonicalZero_pos θ a
  have hsq : (((a : ℝ) + 1) / 2) ^ (2 : ℕ) ≤
      (movingCanonicalZero θ a) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hl 2
  rw [div_le_iff₀ (sq_pos_of_pos hzp)]
  field_simp
  nlinarith [hsq]

theorem summable_movingCanonicalNatMajorant :
    Summable (fun a : ℕ => 4 / ((a : ℝ) + 1) ^ (2 : ℕ)) := by
  have hbase : Summable (fun a : ℕ => (1 : ℝ) / (a : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff
    (f := fun a : ℕ => (1 : ℝ) / (a : ℝ) ^ (2 : ℕ)) 1).mpr hbase
  have hone : Summable (fun a : ℕ =>
      (1 : ℝ) / ((a : ℝ) + 1) ^ (2 : ℕ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  simpa [div_eq_mul_inv] using hone.mul_left 4

/-- A summable majorant, uniform in `θ`, for the `a`-th normalized jet term of order `k` on the ball
of radius `Im z / 2` around `z`. -/
def movingCanonicalLocalJetMajorant (k : ℕ) (z : ℂ) (a : ℕ) : ℝ :=
  let y := z.im / 2
  let R := ‖z‖ + y
  let C := 1 + R / y
  (if k = 0 then R * C else C ^ (2 : ℕ) * y⁻¹ ^ (k - 1)) *
    (4 / ((a : ℝ) + 1) ^ (2 : ℕ))

theorem summable_movingCanonicalLocalJetMajorant
    (k : ℕ) {z : ℂ} (_hz : 0 < z.im) :
    Summable (movingCanonicalLocalJetMajorant k z) := by
  unfold movingCanonicalLocalJetMajorant
  exact summable_movingCanonicalNatMajorant.mul_left
    (if k = 0 then (‖z‖ + z.im / 2) *
      (1 + (‖z‖ + z.im / 2) / (z.im / 2))
    else (1 + (‖z‖ + z.im / 2) / (z.im / 2)) ^ (2 : ℕ) *
      (z.im / 2)⁻¹ ^ (k - 1))

/-- For `Im z₀ > 0` and `z` in the ball of radius `Im z₀ / 2` around `z₀`, the normalized jet term
is bounded by the local majorant, uniformly in `θ`. -/
theorem movingCanonicalNormalizedJetTerm_norm_le_localMajorant
    (k a : ℕ) (θ : BoundedRealSequence) {z₀ z : ℂ}
    (hz₀ : 0 < z₀.im) (hz : z ∈ Metric.ball z₀ (z₀.im / 2)) :
    ‖movingCanonicalNormalizedJetTerm θ k a z‖ ≤
      movingCanonicalLocalJetMajorant k z₀ a := by
  let y : ℝ := z₀.im / 2
  let R : ℝ := ‖z₀‖ + y
  let C : ℝ := 1 + R / y
  let A : ℝ := ‖(movingCanonicalZero θ a : ℂ)‖
  let d : ℝ := ‖(movingCanonicalZero θ a : ℂ) - z‖
  have hy : 0 < y := half_pos hz₀
  have hdist : ‖z - z₀‖ < y := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have himnorm : |(z - z₀).im| ≤ ‖z - z₀‖ :=
    Complex.abs_im_le_norm _
  have hzim : y < z.im := by
    have habs : |z.im - z₀.im| < y := by
      exact lt_of_le_of_lt (by simpa [Complex.sub_im] using himnorm) hdist
    rw [abs_lt] at habs
    dsimp only [y] at habs ⊢
    linarith
  have hzpos : 0 < z.im := hy.trans hzim
  have hApos : 0 < A := norm_pos_iff.mpr
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (movingCanonicalZero_pos θ a)))
  have hdpos : 0 < d := by
    rw [norm_pos_iff]
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hzpos) him
  have hyd : y ≤ d := by
    have hi : z.im ≤ d := by
      have hi' := Complex.abs_im_le_norm
        ((movingCanonicalZero θ a : ℂ) - z)
      have him :
          ((movingCanonicalZero θ a : ℂ) - z).im = -z.im := by simp
      rw [him, abs_neg, abs_of_pos hzpos] at hi'
      exact hi'
    exact hzim.le.trans hi
  have hnormz : ‖z‖ ≤ R := by
    have htri : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
      calc
        ‖z‖ = ‖(z - z₀) + z₀‖ := by
          congr 2
          abel
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
    dsimp only [R]
    linarith
  have hAz : A ≤ d + ‖z‖ := by
    calc
      A = ‖(movingCanonicalZero θ a : ℂ)‖ := rfl
      _ = ‖((movingCanonicalZero θ a : ℂ) - z) + z‖ := by
        congr 2
        abel
      _ ≤ d + ‖z‖ := norm_add_le _ _
  have hRscale : R ≤ (R / y) * d := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hy]
    exact mul_le_mul_of_nonneg_left hyd (by
      dsimp only [R]
      positivity)
  have hACd : A ≤ C * d := by
    dsimp only [C]
    nlinarith
  have hinvAC : d⁻¹ ≤ C * A⁻¹ := by
    have hdiv : 1 / d ≤ C / A := by
      rw [div_le_div_iff₀ hdpos hApos]
      simpa [mul_comm] using hACd
    simpa [div_eq_mul_inv] using hdiv
  have hinvY : d⁻¹ ≤ y⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hy hyd
  have hAmajor : 1 / A ^ (2 : ℕ) ≤ 4 / ((a : ℝ) + 1) ^ (2 : ℕ) := by
    exact movingCanonicalZero_inv_sq_le_nat_majorant θ a
  by_cases hk : k = 0
  · subst k
    have hzeroNe : (movingCanonicalZero θ a : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ a))
    have hsep : (movingCanonicalZero θ a : ℂ) - z ≠ 0 := by
      exact norm_ne_zero_iff.mp (ne_of_gt hdpos)
    have heq :
        ((movingCanonicalZero θ a : ℂ) - z)⁻¹ -
            (movingCanonicalZero θ a : ℂ)⁻¹ =
          z / ((movingCanonicalZero θ a : ℂ) *
            ((movingCanonicalZero θ a : ℂ) - z)) := by
      field_simp [hzeroNe, hsep]
      ring
    rw [movingCanonicalNormalizedJetTerm, if_pos rfl,
      movingCanonicalRegularizedTerm, heq, norm_div, norm_mul]
    change ‖z‖ / (A * d) ≤ _
    have hbound : ‖z‖ / (A * d) ≤
        (R * C) * (1 / A ^ (2 : ℕ)) := by
      rw [div_eq_mul_inv, mul_inv]
      calc
        ‖z‖ * (A⁻¹ * d⁻¹) ≤ R * (A⁻¹ * (C * A⁻¹)) := by
          gcongr
        _ = (R * C) * (1 / A ^ (2 : ℕ)) := by
          field_simp
    exact hbound.trans (mul_le_mul_of_nonneg_left hAmajor (by positivity))
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [movingCanonicalNormalizedJetTerm, if_neg (Nat.succ_ne_zero m),
      norm_pow, norm_inv]
    change d⁻¹ ^ (m + 2) ≤ _
    have hbound :
        d⁻¹ ^ (m + 2) ≤
          (C ^ (2 : ℕ) * y⁻¹ ^ m) * (1 / A ^ (2 : ℕ)) := by
      rw [pow_add]
      calc
        d⁻¹ ^ m * d⁻¹ ^ (2 : ℕ) ≤
            y⁻¹ ^ m * (C * A⁻¹) ^ (2 : ℕ) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hinvY m)
            (pow_le_pow_left₀ (by positivity) hinvAC 2)
            (by positivity) (by positivity)
        _ = (C ^ (2 : ℕ) * y⁻¹ ^ m) * (1 / A ^ (2 : ℕ)) := by
          field_simp
    have hconst : 0 ≤ C ^ (2 : ℕ) * y⁻¹ ^ m := by positivity
    exact hbound.trans (mul_le_mul_of_nonneg_left hAmajor hconst)

/-- The normalized jet `(θ, z) ↦ J_k(θ, z)` is jointly continuous at every `(θ, z)` with
`Im z > 0`. -/
theorem continuousAt_movingCanonicalNormalizedJet
    (k : ℕ) (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt
      (fun p : BoundedRealSequence × ℂ =>
        movingCanonicalNormalizedJet p.1 k p.2) (θ, z) := by
  let S : Set (BoundedRealSequence × ℂ) :=
    Set.univ ×ˢ Metric.ball z (z.im / 2)
  have hballUpper : Metric.ball z (z.im / 2) ⊆ upperHalfPlane := by
    intro w hw
    have hdist : ‖w - z‖ < z.im / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have himnorm : |(w - z).im| ≤ ‖w - z‖ :=
      Complex.abs_im_le_norm _
    have habs : |w.im - z.im| < z.im / 2 := by
      exact lt_of_le_of_lt (by simpa [Complex.sub_im] using himnorm) hdist
    rw [abs_lt] at habs
    change 0 < w.im
    linarith
  have hterm : ∀ a, ContinuousOn
      (fun p : BoundedRealSequence × ℂ =>
        movingCanonicalNormalizedJetTerm p.1 k a p.2) S := by
    intro a
    exact (continuousOn_movingCanonicalNormalizedJetTerm k a).mono
      (fun p hp => ⟨Set.mem_univ _, hballUpper hp.2⟩)
  have hcontOn : ContinuousOn
      (fun p : BoundedRealSequence × ℂ =>
        ∑' a, movingCanonicalNormalizedJetTerm p.1 k a p.2) S :=
    continuousOn_tsum hterm
      (summable_movingCanonicalLocalJetMajorant k hz)
      (fun a p hp =>
        movingCanonicalNormalizedJetTerm_norm_le_localMajorant
          k a p.1 hz hp.2)
  have hSn : S ∈ 𝓝 (θ, z) := by
    apply (isOpen_univ.prod Metric.isOpen_ball).mem_nhds
    exact ⟨Set.mem_univ _, Metric.mem_ball_self (half_pos hz)⟩
  exact hcontOn.continuousAt hSn

/-- `HasDerivAt` for maps `ℂ → ℂ` with the module instance path fixed explicitly. -/
abbrev HasCoherentComplexDerivAt
    (f : ℂ → ℂ) (f' x : ℂ) : Prop :=
  @HasDerivAt ℂ inferInstance ℂ
    instCommCStarAlgebraComplex.toCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℂ).toModule
    inferInstance inferInstance f f' x

/-- Termwise derivative: for `Im z > 0` the `a`-th jet term of order `k` has derivative
`(k + 1)` times the term of order `k + 1`. -/
theorem movingCanonicalNormalizedJetTerm_hasDerivAt
    (θ : BoundedRealSequence) (k a : ℕ) {z : ℂ} (hz : 0 < z.im) :
    HasCoherentComplexDerivAt
      (movingCanonicalNormalizedJetTerm θ k a)
      ((k + 1 : ℕ) •
        movingCanonicalNormalizedJetTerm θ (k + 1) a z) z := by
  have hsep : (movingCanonicalZero θ a : ℂ) - z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hbase : HasCoherentComplexDerivAt
      (fun w : ℂ => ((movingCanonicalZero θ a : ℂ) - w)⁻¹)
      ((((movingCanonicalZero θ a : ℂ) - z)⁻¹) ^ (2 : ℕ)) z := by
    have h :=
      ((hasDerivAt_const (x := z)
        (movingCanonicalZero θ a : ℂ)).sub (hasDerivAt_id z)).inv hsep
    convert h using 1
    · funext w
      rfl
    · simp
  by_cases hk : k = 0
  · subst k
    simp only [movingCanonicalNormalizedJetTerm, if_neg one_ne_zero,
      movingCanonicalRegularizedTerm, zero_add, one_nsmul]
    convert hbase.sub (hasDerivAt_const (x := z)
      (movingCanonicalZero θ a : ℂ)⁻¹) using 1
    · funext w
      rfl
    · simp
  · have hfun : movingCanonicalNormalizedJetTerm θ k a =
        fun w : ℂ =>
          (((movingCanonicalZero θ a : ℂ) - w)⁻¹) ^ (k + 1) := by
      funext w
      simp [movingCanonicalNormalizedJetTerm, hk]
    have hnext :
        movingCanonicalNormalizedJetTerm θ (k + 1) a z =
          (((movingCanonicalZero θ a : ℂ) - z)⁻¹) ^ (k + 2) := by
      simp [movingCanonicalNormalizedJetTerm]
    rw [hfun, hnext]
    have hpow := hbase.pow (k + 1)
    convert hpow using 1
    · funext w
      rfl
    · simp only [nsmul_eq_mul, Nat.add_sub_cancel]
      rw [pow_add]
      ring

/-- For `Im z > 0`, `J_k(θ, ·)` has derivative `(k + 1) J_{k+1}(θ, z)`, by locally uniform
summation of the termwise derivatives. -/
theorem movingCanonicalNormalizedJet_hasDerivAt
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    HasCoherentComplexDerivAt
      (movingCanonicalNormalizedJet θ k)
      ((k + 1 : ℕ) • movingCanonicalNormalizedJet θ (k + 1) z) z := by
  let r : ℝ := z.im / 2
  let u : ℕ → ℝ := fun a =>
    (k + 1 : ℝ) * movingCanonicalLocalJetMajorant (k + 1) z a
  have hr : 0 < r := half_pos hz
  have hu : Summable u := by
    exact (summable_movingCanonicalLocalJetMajorant
      (k + 1) hz).mul_left (k + 1 : ℝ)
  have hupper : Metric.ball z r ⊆ upperHalfPlane := by
    intro w hw
    have hdist : ‖w - z‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have himnorm : |(w - z).im| ≤ ‖w - z‖ :=
      Complex.abs_im_le_norm _
    have habs : |w.im - z.im| < r := by
      exact lt_of_le_of_lt (by simpa [Complex.sub_im] using himnorm) hdist
    rw [abs_lt] at habs
    change 0 < w.im
    dsimp only [r] at habs
    linarith
  have hterm : ∀ a w, w ∈ Metric.ball z r →
      HasCoherentComplexDerivAt
        (movingCanonicalNormalizedJetTerm θ k a)
        ((k + 1 : ℕ) •
          movingCanonicalNormalizedJetTerm θ (k + 1) a w) w := by
    intro a w hw
    exact movingCanonicalNormalizedJetTerm_hasDerivAt
      θ k a (hupper hw)
  have hbound : ∀ a w, w ∈ Metric.ball z r →
      ‖(k + 1 : ℕ) •
        movingCanonicalNormalizedJetTerm θ (k + 1) a w‖ ≤ u a := by
    intro a w hw
    rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul]
    simpa only [u, Nat.cast_add, Nat.cast_one] using
      mul_le_mul_of_nonneg_left
        (movingCanonicalNormalizedJetTerm_norm_le_localMajorant
          (k + 1) a θ hz (by simpa only [r] using hw))
        (Nat.cast_nonneg (k + 1))
  have hmain := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball z r).isPreconnected hterm hbound
    (Metric.mem_ball_self hr)
    (summable_movingCanonicalNormalizedJetTerm θ k hz)
    (Metric.mem_ball_self hr)
  convert hmain using 1
  · rfl
  · simp only [movingCanonicalNormalizedJet, nsmul_eq_mul]
    rw [tsum_mul_left]

/-- For `Im z > 0`, the `k`-th derivative of `L_θ` is `k! · J_k(θ, z)`, where
`J_k = Σ_n (a_n - z)^{-(k+1)}` for `k ≥ 1`. -/
theorem iteratedDeriv_movingCanonicalLogDerivative_eq_factorial_mul_normalizedJet
    (θ : BoundedRealSequence) (k : ℕ) {z : ℂ} (hz : 0 < z.im) :
    iteratedDeriv k (movingCanonicalLogDerivative θ) z =
      (k.factorial : ℂ) * movingCanonicalNormalizedJet θ k z := by
  induction k generalizing z with
  | zero =>
      simp [iteratedDeriv_zero, movingCanonicalNormalizedJet_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv k (movingCanonicalLogDerivative θ) =ᶠ[𝓝 z]
          fun w => (k.factorial : ℂ) *
            movingCanonicalNormalizedJet θ k w := by
        filter_upwards [isOpen_upperHalfPlane.mem_nhds hz] with w hw
        exact ih hw
      rw [heq.deriv_eq]
      have hderiv :=
        (movingCanonicalNormalizedJet_hasDerivAt θ k hz).const_mul
          (k.factorial : ℂ)
      rw [hderiv.deriv]
      rw [Nat.factorial_succ]
      push_cast
      simp only [nsmul_eq_mul]
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- `(θ, z) ↦ L_θ^{(k)}(z)` is jointly continuous at every `(θ, z)` with `Im z > 0`. -/
theorem continuousAt_iteratedDeriv_movingCanonicalLogDerivative_joint
    (k : ℕ) (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt
      (fun p : BoundedRealSequence × ℂ =>
        iteratedDeriv k (movingCanonicalLogDerivative p.1) p.2)
      (θ, z) := by
  have hcont : ContinuousAt
      (fun p : BoundedRealSequence × ℂ =>
        (k.factorial : ℂ) *
          movingCanonicalNormalizedJet p.1 k p.2) (θ, z) :=
    continuousAt_const.mul
      (continuousAt_movingCanonicalNormalizedJet k θ hz)
  have hupperN :
      {p : BoundedRealSequence × ℂ | p.2 ∈ upperHalfPlane} ∈
        𝓝 (θ, z) :=
    (isOpen_upperHalfPlane.preimage continuous_snd).mem_nhds hz
  apply hcont.congr_of_eventuallyEq
  filter_upwards [hupperN] with p hp
  exact iteratedDeriv_movingCanonicalLogDerivative_eq_factorial_mul_normalizedJet
    p.1 k hp

/-- The jet family `(θ, h) ↦ (L_θ^{(k)}(nodes h i))_{i, k < n i}` at parametrized nodes. -/
def movingCanonicalActualJetFamily
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ)
    (p : BoundedRealSequence × H) :
    (Σ i, Fin (n i)) → ℂ :=
  fun s => iteratedDeriv s.2.1
    (movingCanonicalLogDerivative p.1) (nodes p.2 s.1)

/-- For continuous nodes lying in the upper half-plane over `U`, the jet family is continuous on
`(bounded sequences) × U`. -/
theorem continuousOn_movingCanonicalActualJetFamily
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (hnodes : Continuous nodes)
    (n : ι → ℕ) (U : Set H)
    (hupper : ∀ h ∈ U, ∀ i, 0 < (nodes h i).im) :
    ContinuousOn
      (movingCanonicalActualJetFamily nodes n)
      (Set.univ ×ˢ U) := by
  apply continuousOn_pi'
  intro s p hp
  have hinner : ContinuousAt
      (fun q : BoundedRealSequence × H =>
        (q.1, nodes q.2 s.1)) p :=
    continuousAt_fst.prodMk
      ((continuous_apply s.1).comp
        (hnodes.comp continuous_snd)).continuousAt
  exact (continuousAt_iteratedDeriv_movingCanonicalLogDerivative_joint
    s.2.1 p.1 (hupper p.2 hp.2 s.1)).comp
      (f := fun q : BoundedRealSequence × H =>
        (q.1, nodes q.2 s.1)) hinner |>.continuousWithinAt

/-- The jet family at row-by-shift nodes, reshaped into rows of jet coordinates. -/
def movingCanonicalExpandedActualJetFamily
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (p : BoundedRealSequence × H) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (movingCanonicalActualJetFamily nodes
      (fun x : row × ι => orders x.2) p)

theorem continuousOn_movingCanonicalExpandedActualJetFamily
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (hnodes : Continuous nodes) (U : Set H)
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im) :
    ContinuousOn
      (movingCanonicalExpandedActualJetFamily orders nodes)
      (Set.univ ×ˢ U) :=
  (reshapeCombinedJetsFinCLM row ι orders).continuous.comp_continuousOn
    (continuousOn_movingCanonicalActualJetFamily
      nodes hnodes (fun x : row × ι => orders x.2) U hupper)

/-- Jet family in the finite chart `p ↦ θ + (finitely supported perturbation p)`, jointly in `p`
and the node parameter. -/
def movingCanonicalFiniteJointJetFamily
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H) :
    (Σ i, Fin (n i)) → ℂ :=
  movingCanonicalFiniteActualJetFamily (nodes p.2) n θ p.1

/-- Smooth model of the finite-chart jet family: the base jet plus the finitely many perturbed
zero terms minus the unperturbed ones. -/
def movingCanonicalFiniteJointJetSmoothModel
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H) :
    (Σ i, Fin (n i)) → ℂ :=
  fun s =>
    iteratedDeriv s.2.1 (movingCanonicalLogDerivative θ) (nodes p.2 s.1) +
      ∑ a : Fin (movingCanonicalLocationProbeCard n),
        (movingCanonicalDifferentialJetTerm
            (movingCanonicalFiniteChart
              (movingCanonicalLocationProbeCard n) θ p.1)
            s.2.1 a.1 (nodes p.2 s.1) -
          movingCanonicalDifferentialJetTerm
            θ s.2.1 a.1 (nodes p.2 s.1))

/-- At upper-half-plane nodes, the finite-chart jet family equals its smooth model. -/
theorem movingCanonicalFiniteJointJetFamily_eq_smoothModel
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (n : ι → ℕ) (θ : BoundedRealSequence)
    (p : (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H)
    (hupper : ∀ i, 0 < (nodes p.2 i).im) :
    movingCanonicalFiniteJointJetFamily nodes n θ p =
      movingCanonicalFiniteJointJetSmoothModel nodes n θ p := by
  funext s
  exact iteratedDeriv_movingCanonicalLogDerivative_finiteChart
    (movingCanonicalLocationProbeCard n) θ p.1 s.2.1 (hupper s.1)

/-- For smooth nodes lying in the upper half-plane over `U`, the smooth model is `C^∞` on
`(chart parameters) × U`. -/
theorem contDiffOn_movingCanonicalFiniteJointJetSmoothModel
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (U : Set H) (hupper : ∀ h ∈ U, ∀ i, 0 < (nodes h i).im) :
    ContDiffOn ℝ ⊤
      (movingCanonicalFiniteJointJetSmoothModel nodes n θ)
      (Set.univ ×ˢ U) := by
  apply contDiffOn_pi'
  intro s p hp
  have hpU : p.2 ∈ U := hp.2
  have hnode : ContDiff ℝ ⊤
      (fun q :
        (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
        nodes q.2 s.1) :=
    (contDiff_apply ℝ ℂ s.1).comp (hnodes.comp contDiff_snd)
  have hbase : ContDiffAt ℝ ⊤
      (fun q :
        (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
        iteratedDeriv s.2.1 (movingCanonicalLogDerivative θ)
          (nodes q.2 s.1)) p := by
    exact ((analyticAt_iteratedDeriv_movingCanonicalLogDerivative
      θ s.2.1 (hupper p.2 hpU s.1)).restrictScalars.contDiffAt).comp
        p hnode.contDiffAt
  have hterm : ∀ a : Fin (movingCanonicalLocationProbeCard n),
      ContDiffAt ℝ ⊤
        (fun q :
          (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
          movingCanonicalDifferentialJetTerm
              (movingCanonicalFiniteChart
                (movingCanonicalLocationProbeCard n) θ q.1)
              s.2.1 a.1 (nodes q.2 s.1) -
            movingCanonicalDifferentialJetTerm
              θ s.2.1 a.1 (nodes q.2 s.1)) p := by
    intro a
    have hzero : ContDiff ℝ ⊤
        (fun q :
          (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
          (movingCanonicalZero
            (movingCanonicalFiniteChart
              (movingCanonicalLocationProbeCard n) θ q.1) a.1 : ℂ)) :=
      (contDiff_movingCanonicalZero_finiteChart_ofReal
        (movingCanonicalLocationProbeCard n) θ a).comp contDiff_fst
    have hsepNew :
        (movingCanonicalZero
          (movingCanonicalFiniteChart
            (movingCanonicalLocationProbeCard n) θ p.1) a.1 : ℂ) -
            nodes p.2 s.1 ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact (ne_of_gt (hupper p.2 hpU s.1)) him
    have hzeroNew :
        (movingCanonicalZero
          (movingCanonicalFiniteChart
            (movingCanonicalLocationProbeCard n) θ p.1) a.1 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos
          (movingCanonicalFiniteChart
            (movingCanonicalLocationProbeCard n) θ p.1) a.1))
    have hsepOld :
        (movingCanonicalZero θ a.1 : ℂ) - nodes p.2 s.1 ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact (ne_of_gt (hupper p.2 hpU s.1)) him
    have hzeroOld : (movingCanonicalZero θ a.1 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ a.1))
    unfold movingCanonicalDifferentialJetTerm
    by_cases hk : s.2.1 = 0
    · simp only [if_pos hk, movingCanonicalRegularizedTerm]
      have hnewReg :=
        ((hzero.contDiffAt.sub hnode.contDiffAt).inv hsepNew).sub
          (hzero.contDiffAt.inv hzeroNew)
      have holdZero : ContDiffAt ℝ ⊤
          (fun _ :
            (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
            (movingCanonicalZero θ a.1 : ℂ)) p :=
        contDiffAt_const
      have holdReg :=
        ((holdZero.sub hnode.contDiffAt).inv hsepOld).sub
          (holdZero.inv hzeroOld)
      exact hnewReg.sub holdReg
    · simp only [if_neg hk]
      have hnewPow :=
        ((hzero.contDiffAt.sub hnode.contDiffAt).inv hsepNew).pow
          (s.2.1 + 1)
      have holdZero : ContDiffAt ℝ ⊤
          (fun _ :
            (Fin (movingCanonicalLocationProbeCard n) → ℝ) × H =>
            (movingCanonicalZero θ a.1 : ℂ)) p :=
        contDiffAt_const
      have holdPow :=
        ((holdZero.sub hnode.contDiffAt).inv hsepOld).pow
          (s.2.1 + 1)
      exact (contDiffAt_const.mul hnewPow).sub
        (contDiffAt_const.mul holdPow)
  exact (hbase.add
    (ContDiffAt.sum (s := Finset.univ) (fun a _ => hterm a))).contDiffWithinAt

/-- For smooth upper-half-plane nodes over `U`, the finite-chart jet family is `C^∞` on
`(chart parameters) × U`. -/
theorem contDiffOn_movingCanonicalFiniteJointJetFamily
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype ι]
    (nodes : H → ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (n : ι → ℕ) (θ : BoundedRealSequence)
    (U : Set H) (hupper : ∀ h ∈ U, ∀ i, 0 < (nodes h i).im) :
    ContDiffOn ℝ ⊤
      (movingCanonicalFiniteJointJetFamily nodes n θ)
      (Set.univ ×ˢ U) := by
  apply (contDiffOn_movingCanonicalFiniteJointJetSmoothModel
    nodes hnodes n θ U hupper).congr
  intro p hp
  exact movingCanonicalFiniteJointJetFamily_eq_smoothModel
    nodes n θ p (hupper p.2 hp.2)

/-- The finite-chart jet family at row-by-shift nodes, reshaped into rows of jet coordinates. -/
def movingCanonicalExpandedJetFamily
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (θ : BoundedRealSequence)
    (p :
      (Fin (movingCanonicalLocationProbeCard
        (fun x : row × ι => orders x.2)) → ℝ) × H) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (movingCanonicalFiniteJointJetFamily nodes
      (fun x : row × ι => orders x.2) θ p)

/-- The reshaped finite-chart jet family is `C^∞` on `(chart parameters) × U`. -/
theorem contDiffOn_movingCanonicalExpandedJetFamily
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (hnodes : ContDiff ℝ ⊤ nodes)
    (θ : BoundedRealSequence) (U : Set H)
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im) :
    ContDiffOn ℝ ⊤
      (movingCanonicalExpandedJetFamily orders nodes θ)
      (Set.univ ×ˢ U) := by
  exact (reshapeCombinedJetsFinCLM row ι orders).contDiff.comp_contDiffOn
    (contDiffOn_movingCanonicalFiniteJointJetFamily
      nodes hnodes (fun x : row × ι => orders x.2) θ U hupper)

/-- At injective upper-half-plane nodes, the derivative of the reshaped jet family with respect to
the finite chart parameters is surjective. -/
theorem fderiv_movingCanonicalExpandedJetFamily_probe_surjective
    {H row ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype row] [Fintype ι]
    [DecidableEq row] [DecidableEq ι]
    (orders : ι → ℕ) (nodes : H → row × ι → ℂ)
    (θ : BoundedRealSequence)
    (p : Fin (movingCanonicalLocationProbeCard
      (fun x : row × ι => orders x.2)) → ℝ)
    (h : H) (hinj : Function.Injective (nodes h))
    (hupper : ∀ x, 0 < (nodes h x).im) :
    Function.Surjective
      (fderiv ℝ
        (fun v => movingCanonicalExpandedJetFamily
          orders nodes θ (v, h)) p) := by
  let nodeOrders : row × ι → ℕ := fun x => orders x.2
  have hactual :=
    movingCanonicalFiniteActualJetFamily_hasFDerivAt
      (nodes h) hupper nodeOrders θ p
  have hreshape : HasNormedFDerivAt
      (reshapeCombinedJetsFinCLM row ι orders)
      (reshapeCombinedJetsFinCLM row ι orders)
      (movingCanonicalFiniteActualJetFamily (nodes h) nodeOrders θ p) :=
    (reshapeCombinedJetsFinCLM row ι orders).hasFDerivAt
  have hcomp := hreshape.comp p hactual
  have hfun :
      (fun v => movingCanonicalExpandedJetFamily
        orders nodes θ (v, h)) =
        (reshapeCombinedJetsFinCLM row ι orders) ∘
          movingCanonicalFiniteActualJetFamily (nodes h) nodeOrders θ := by
    funext v
    rfl
  have hderiv :
      fderiv ℝ
        (fun v => movingCanonicalExpandedJetFamily
          orders nodes θ (v, h)) p =
        (reshapeCombinedJetsFinCLM row ι orders).comp
          (movingCanonicalFiniteParameterJetCLM (nodes h) nodeOrders
            (movingCanonicalFiniteChart
              (movingCanonicalLocationProbeCard nodeOrders) θ p)) := by
    rw [hfun]
    exact hcomp.fderiv
  rw [hderiv]
  exact (reshapeCombinedJetsFinCLM_surjective row ι orders).comp
    (movingCanonicalFiniteParameterJetCLM_surjective
      (nodes h) hinj hupper nodeOrders
        (movingCanonicalFiniteChart
          (movingCanonicalLocationProbeCard nodeOrders) θ p))

/-- Under `hrows` and `hdim`, for smooth injective upper-half-plane nodes on an open `U ⊇ K`, the
chart parameters whose jet family avoids the rank-defect locus over the whole patch `K` are
dense. -/
theorem compact_movingCanonicalExpandedEvaluation_avoidance_dense
    {H row κ ι : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hinj : ∀ h ∈ U, Function.Injective (nodes h))
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im)
    (θ : BoundedRealSequence)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense
      (compactConfigurationAvoidance
        (movingCanonicalExpandedJetFamily orders nodes θ)
        (expandedDifferentialEvaluationRankDefect degree
          (Fintype.card (Σ i, Fin (orders i))) z exponent)
        K) := by
  apply expandedEvaluation_compactPatchAvoidance_dense
    degree (Fintype.card (Σ i, Fin (orders i)))
      z hz exponent hexponent hrows
      (movingCanonicalExpandedJetFamily orders nodes θ)
      U K hU hKU
  · exact contDiffOn_movingCanonicalExpandedJetFamily
      orders nodes hnodes θ U hupper
  · intro p h hh
    exact fderiv_movingCanonicalExpandedJetFamily_probe_surjective
      orders nodes θ p h (hinj h hh) (hupper h hh)
  · exact hdim

@[simp]
theorem movingCanonicalFiniteChart_zero
    (D : ℕ) (θ : BoundedRealSequence) :
    movingCanonicalFiniteChart D θ 0 = θ := by
  ext a
  simp [movingCanonicalFiniteChart]

/-- Under the same hypotheses, the bounded sequences `θ` for which the expanded evaluation matrix
has full column rank at every parameter of the compact patch `K` form a dense set. -/
theorem compact_movingCanonicalExpandedActualEvaluation_avoidance_dense
    {H row κ ι : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (z : row → ℂ) (hz : Function.Injective z)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (nodes : H → row × ι → ℂ) (hnodes : ContDiff ℝ ⊤ nodes)
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hinj : ∀ h ∈ U, Function.Injective (nodes h))
    (hupper : ∀ h ∈ U, ∀ x, 0 < (nodes h x).im)
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    Dense
      (compactConfigurationAvoidance
        (movingCanonicalExpandedActualJetFamily orders nodes)
        (expandedDifferentialEvaluationRankDefect degree
          (Fintype.card (Σ i, Fin (orders i))) z exponent)
        K) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro θ
  rw [mem_closure_iff]
  intro V hVopen hθV
  let D := movingCanonicalLocationProbeCard
    (fun x : row × ι => orders x.2)
  let chart : (Fin D → ℝ) → BoundedRealSequence :=
    movingCanonicalFiniteChart D θ
  have hchart : Continuous chart := by
    exact (contDiff_movingCanonicalFiniteChart D θ).continuous
  have hchartZero : chart 0 = θ := by
    exact movingCanonicalFiniteChart_zero D θ
  have hpreOpen : IsOpen (chart ⁻¹' V) :=
    hVopen.preimage hchart
  have hpreNonempty : (chart ⁻¹' V).Nonempty := by
    exact ⟨0, by simpa [hchartZero] using hθV⟩
  have hdenseFinite :=
    compact_movingCanonicalExpandedEvaluation_avoidance_dense
      degree orders z hz exponent hexponent hrows nodes hnodes
      U K hU hKU hinj hupper θ hdim
  obtain ⟨p, hpgood, hpV⟩ :=
    hdenseFinite.exists_mem_open hpreOpen hpreNonempty
  refine ⟨chart p, hpV, ?_⟩
  intro h hh
  exact hpgood h hh

/-- Jet values of `L_θ` at the row-by-shift nodes `packet r + shift i`, reshaped into rows. -/
def movingCanonicalExpandedPacketValue
    {row ι : Type} [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    (orders : ι → ℕ) (packet : InjectiveProjectiveRowPacket row)
    (θ : BoundedRealSequence) (shift : InjectiveShiftConfiguration ι) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  reshapeCombinedJetsFinCLM row ι orders
    (movingCanonicalActualJetFamily
      (fun _ : Unit =>
        combinedProjectiveRowShiftPacket packet shift)
      (fun x : row × ι => orders x.2) (θ, ()))

/-- A row packet whose row-by-shift nodes are distinct and in the upper half-plane and whose
expanded evaluation matrix for `θ` is injective (full column rank). -/
def movingCanonicalExpandedFullRankWitness
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∃ packet : InjectiveProjectiveRowPacket row,
    Function.Injective (combinedProjectiveRowShiftPacket packet shift) ∧
      (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (movingCanonicalExpandedPacketValue orders packet θ shift)).mulVec

/-- The coefficient vector `coeff` is a pattern relation for `θ` and `shift`: for every admissible
row packet, every row of the expanded evaluation matrix is annihilated by `coeff`. -/
def movingCanonicalExpandedPatternRelationHolds
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row,
    Function.Injective (combinedProjectiveRowShiftPacket packet shift) →
    (∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (movingCanonicalExpandedPacketValue orders packet θ shift) r col = 0

/-- Given a full-rank witness, every pattern relation for `θ` and `shift` has zero coefficients. -/
theorem movingCanonicalExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence)
    (shift : InjectiveShiftConfiguration ι)
    (hwitness : movingCanonicalExpandedFullRankWitness
      (row := row) (κ := κ) degree orders exponent θ shift)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : movingCanonicalExpandedPatternRelationHolds
      (row := row) degree orders exponent θ shift coeff) :
    ∀ col, coeff col = 0 := by
  obtain ⟨packet, hinjNodes, hupper, hinjective⟩ := hwitness
  let A := expandedDifferentialEvaluationMatrix degree
    (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
    (movingCanonicalExpandedPacketValue orders packet θ shift)
  have hmul : A.mulVec coeff = 0 := by
    funext r
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using
      hrelation packet hinjNodes hupper r
  have hcoeff : coeff = 0 := hinjective (by simpa [A] using hmul)
  intro col
  exact congrFun hcoeff col

/-- Under `hexponent`, `hrows`, `hdim`, every compact set of injective shift configurations is
covered by finitely many compact pieces with row packets such that a dense open set of `θ` has a
full-rank witness for every shift in the compact set. -/
theorem compact_injectiveShiftPatch_has_dense_completeAtlas_movingCanonical
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (Kshift : Set (InjectiveShiftConfiguration ι))
    (hKshift : IsCompact Kshift)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        Kshift ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        (∀ j, pieces j ⊆
          cauchyUpperGoodCombinedRowPacketSet (packets j)) ∧
        let ambientPiece := fun j =>
          ambientImageOfInjectiveShiftPiece (pieces j)
        let family := fun j =>
          movingCanonicalExpandedActualJetFamily orders
            (fun h x => (packets j).1 x.1 + h x.2)
        let good := fun j => compactConfigurationAvoidance (family j)
          (expandedDifferentialEvaluationRankDefect degree
            (Fintype.card (Σ i, Fin (orders i)))
            (packets j).1 exponent)
          (ambientPiece j)
        Dense (⋂ j, good j) ∧ IsOpen (⋂ j, good j) ∧
          ∀ θ ∈ ⋂ j, good j, ∀ shift ∈ Kshift,
            movingCanonicalExpandedFullRankWitness
              (row := row) (κ := κ)
              degree orders exponent θ shift := by
  classical
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart⟩ :=
    compact_injectiveShiftPatch_finite_cauchyUpperGoodCombinedRowPacket_refinement
      (row := row) hKshift
  let ambientPiece : Fin n → Set (ι → ℂ) := fun j =>
    ambientImageOfInjectiveShiftPiece (pieces j)
  let nodes : Fin n → (ι → ℂ) → (row × ι → ℂ) := fun j h x =>
    (packets j).1 x.1 + h x.2
  let family := fun j =>
    movingCanonicalExpandedActualJetFamily orders (nodes j)
  let good := fun j => compactConfigurationAvoidance (family j)
    (expandedDifferentialEvaluationRankDefect degree
      (Fintype.card (Σ i, Fin (orders i))) (packets j).1 exponent)
    (ambientPiece j)
  have hgood : ∀ j, Dense (good j) ∧ IsOpen (good j) := by
    intro j
    let Uj : Set (ι → ℂ) :=
      cauchyUpperGoodCombinedRowPacketAmbientSet (packets j)
    have hUj : IsOpen Uj :=
      cauchyUpperGoodCombinedRowPacketAmbientSet_isOpen (packets j)
    have hKj : IsCompact (ambientPiece j) :=
      (hpiecesCompact j).image continuous_subtype_val
    have hKjUj : ambientPiece j ⊆ Uj := by
      rintro shift ⟨shiftCfg, hpiece, rfl⟩
      exact hpiecesChart j hpiece
    have hnodes : ContDiff ℝ ⊤ (nodes j) := by
      rw [contDiff_pi]
      intro x
      exact contDiff_const.add (contDiff_apply ℝ ℂ x.2)
    have hdenseRaw :=
      compact_movingCanonicalExpandedActualEvaluation_avoidance_dense
        degree orders (packets j).1 (packets j).2
        exponent hexponent hrows
        (nodes j) hnodes Uj (ambientPiece j)
        hUj hKjUj
        (fun h hh => hh.1)
        (fun h hh x => hh.2 x)
        hdim
    have hdense : Dense (good j) := by
      simpa only [good, family] using hdenseRaw
    have hfamilyOn : ContinuousOn (family j) (Set.univ ×ˢ Uj) := by
      exact continuousOn_movingCanonicalExpandedActualJetFamily
        orders (nodes j) hnodes.continuous Uj
          (fun h hh x => hh.2 x)
    have hopenRaw :=
      compactConfigurationAvoidance_isOpen_of_continuousOn_open
        (family j)
        (expandedDifferentialEvaluationRankDefect degree
          (Fintype.card (Σ i, Fin (orders i)))
          (packets j).1 exponent)
        (expandedDifferentialEvaluationRankDefect_isClosed degree
          (Fintype.card (Σ i, Fin (orders i)))
          (packets j).1 exponent)
        Uj hUj hfamilyOn (ambientPiece j) hKj hKjUj
    have hopen : IsOpen (good j) := by
      simpa only [good] using hopenRaw
    exact ⟨hdense, hopen⟩
  refine ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart,
    ?_, ?_, ?_⟩
  · exact dense_iInter_of_finite_isOpen good
      (fun j => (hgood j).2) (fun j => (hgood j).1)
  · exact isOpen_iInter_of_finite (fun j => (hgood j).2)
  · intro θ hθ shift hshift
    obtain ⟨j, hjpiece⟩ := Set.mem_iUnion.mp (hcover hshift)
    have hjchart := hpiecesChart j hjpiece
    refine ⟨packets j, hjchart.1, hjchart.2, ?_⟩
    have hjgood := Set.mem_iInter.mp hθ j
    have hambient : shift.1 ∈ ambientPiece j :=
      ⟨shift, hjpiece, rfl⟩
    have havoid := hjgood shift.1 hambient
    have hinjective : Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i)))
          (packets j).1 exponent
          (family j (θ, shift.1))).mulVec := by
      simpa only [mem_expandedDifferentialEvaluationRankDefect_iff,
        not_not] using havoid
    change Function.Injective
      (expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i)))
        (packets j).1 exponent
        (family j (θ, shift.1))).mulVec
    exact hinjective

/-- Under `hexponent`, `hrows`, `hdim`, the `θ` having a full-rank witness for every injective
shift configuration form a dense residual set (σ-compactness of shifts and Baire category). -/
theorem global_injectiveShifts_movingCanonicalExpandedFullRankWitness_dense_residual
    {row κ ι : Type}
    [Fintype row] [DecidableEq row]
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent :
      κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (degree + 1)) + degree <
      Fintype.card row)
    (hdim : Module.finrank ℝ (ι → ℂ) <
      2 * (Fintype.card row -
        Fintype.card (κ × Fin (degree + 1)) - degree + 1)) :
    let good : Set BoundedRealSequence := {θ |
      ∀ shift : InjectiveShiftConfiguration ι,
        movingCanonicalExpandedFullRankWitness
          (row := row) (κ := κ)
          degree orders exponent θ shift}
    Dense good ∧ good ∈ residual BoundedRealSequence := by
  dsimp only
  letI : BaireSpace BoundedRealSequence := by infer_instance
  apply globalWitness_dense_residual_of_sigmaCompact
    (fun θ (shift : InjectiveShiftConfiguration ι) =>
      movingCanonicalExpandedFullRankWitness
        (row := row) (κ := κ)
        degree orders exponent θ shift)
  intro Kshift hKshift
  obtain ⟨n, packets, pieces, hcover, hpiecesCompact, hpiecesChart,
      hDense, hOpen, hWitness⟩ :=
    compact_injectiveShiftPatch_has_dense_completeAtlas_movingCanonical
      degree orders exponent hexponent hrows Kshift hKshift hdim
  exact ⟨_, hOpen, hDense, hWitness⟩

/-- For a countable label type `Γ`, the `θ` having full-rank witnesses for every finite
differential pattern over `Γ` and every injective shift configuration form a dense residual set. -/
theorem allFinitePatterns_movingCanonicalExpandedFullRankWitness_dense_residual
    {Γ : Type} [Countable Γ] :
    let fullRank : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        movingCanonicalExpandedFullRankWitness
          (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift}
    Dense fullRank ∧ fullRank ∈ residual BoundedRealSequence := by
  dsimp only
  letI : BaireSpace BoundedRealSequence := by infer_instance
  let goodPattern :
      FiniteDifferentialPattern Γ → Set BoundedRealSequence := fun p =>
    {θ | ∀ shift : InjectiveShiftConfiguration (CarrierPatternShift p),
      movingCanonicalExpandedFullRankWitness
        (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift}
  have hgoodPattern : ∀ p : FiniteDifferentialPattern Γ,
      Dense (goodPattern p) ∧
        goodPattern p ∈ residual BoundedRealSequence := by
    intro p
    have hsource :=
      global_injectiveShifts_movingCanonicalExpandedFullRankWitness_dense_residual
        (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p)
        (ι := CarrierPatternShift p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p)
        (carrierPatternExponent_injective p)
        (carrierPattern_rows_strictly_dominate_columns p)
        (carrierPattern_shift_dimension_below_codimension p)
    change Dense (goodPattern p) ∧
      goodPattern p ∈ residual BoundedRealSequence at hsource
    exact hsource
  have hresidual : (⋂ p, goodPattern p) ∈
      residual BoundedRealSequence :=
    countable_iInter_mem.mpr fun p => (hgoodPattern p).2
  have heq : (⋂ p, goodPattern p) =
      {θ | ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
        movingCanonicalExpandedFullRankWitness
          (row := CarrierPatternRow p)
          (κ := CarrierPatternMonomial p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift} := by
    ext θ
    simp only [Set.mem_iInter, goodPattern, Set.mem_setOf_eq]
  rw [heq] at hresidual
  exact ⟨dense_of_mem_residual hresidual, hresidual⟩

/-- The `θ` for which every finite pattern relation, for every injective shift configuration, has
zero coefficients form a dense residual set of bounded real sequences. -/
theorem allFinitePatterns_movingCanonicalExpandedRelationFree_dense_residual
    {Γ : Type} [Countable Γ] :
    let relationFree : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern Γ)
        (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff :
          CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
        movingCanonicalExpandedPatternRelationHolds
          (row := CarrierPatternRow p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift coeff →
        ∀ col, coeff col = 0}
    Dense relationFree ∧
      relationFree ∈ residual BoundedRealSequence := by
  dsimp only
  let fullRank : Set BoundedRealSequence := {θ |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p)),
      movingCanonicalExpandedFullRankWitness
        (row := CarrierPatternRow p)
        (κ := CarrierPatternMonomial p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift}
  let relationFree : Set BoundedRealSequence := {θ |
    ∀ (p : FiniteDifferentialPattern Γ)
      (shift : InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ),
      movingCanonicalExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0}
  have hfull : Dense fullRank ∧
      fullRank ∈ residual BoundedRealSequence := by
    simpa only [fullRank] using
      (allFinitePatterns_movingCanonicalExpandedFullRankWitness_dense_residual
        (Γ := Γ))
  have hsubset : fullRank ⊆ relationFree := by
    intro θ hθ p shift coeff hrelation
    exact
      movingCanonicalExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift
        (hθ p shift) coeff hrelation
  exact ⟨hfull.1.mono hsubset,
    Filter.mem_of_superset hfull.2 hsubset⟩

end

end GaloisForLFunctions.HTGeometry
