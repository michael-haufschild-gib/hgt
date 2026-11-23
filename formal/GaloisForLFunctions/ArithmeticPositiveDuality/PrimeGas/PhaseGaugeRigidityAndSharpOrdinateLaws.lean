import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FiniteEigenvalueCertificatesAndExceptionDensity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.Window
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.ZetaLocalWindowTailUpper
import GaloisForLFunctions.RHTower.SpeiserShadowExponentialDensity
import GaloisForLFunctions.RHTower.SpeiserLittlewoodStrip

/-!
# Phase-gauge rigidity of rank-one spectra, sharp two-sided `|t|^{1 - σ}` ordinate laws, and uniform single-wave certificates on Speiser-shadowed ordinates

We resolve the phase-twisted rank-one witness question on `{3001 / 24000 ≤ Re s < 1 / 2 ∧ 169 / 2 < |Im s|}`
and establish the exact high-ordinate scaling laws of `SpectralBand 1` together with uniform
single-wave horizontal witness certificates across Speiser-shadowed ordinates:

1. **Exact $U(1)^{\mathbb{N}^+}$ phase-gauge blindness and arithmetic twist erasure
   (`modulusMissingWave`, `missingWaveSpectrum_eq_of_coord_norm_eq`,
   `boundedTwist_missingWaveSpectrum_eq_abs`, `unitTwist_missingWaveSpectrum_eq`)**:
   Every diagonal unitary on `Gas = ℓ²(ℕ+)` commutes with `criticalOperator` and conjugates
   `(projected (omitLine v))^2` to `(projected (omitLine (U v)))^2`. Whenever `v, w : MissingWave`
   have equal coordinate moduli `∀ n : ℕ+, ‖v.val n‖ = ‖w.val n‖`, their rank-one surviving spectra
   `missingWaveSpectrum v = missingWaveSpectrum w`, fourth-trace losses `lineLoss`, UV-regularity
   predicates `uvRegularRankOne`, finite-prefix readings `finiteTriadReading`, and full partitions
   `jointSurvivingPartition` agree identically. Every `v : MissingWave` admits a canonical real
   nonnegative twin `modulusMissingWave v`; unit-modulus multiplicative twists (Liouville, `n^{-iτ}`)
   alter `missingWaveSpectrum` by zero, while bounded twists (Möbius `μ(n)`, Dirichlet characters
   `χ(n)`) collapse identically to their nonnegative modulus indicators `|μ(n)|`, `|χ(n)|`.

2. **Sharp two-sided `Θ_σ(|t|^{1 - σ})` ordinate envelope and collapse of the
   `|t|^{-4σ/(1+σ)}` / `K ≍ |t|^{1/(1+σ)}` regime
   (`norm_relativePartition_le_rpow_one_sub_re_uniform`,
   `norm_jointSurvivingPartition_le_rpow_one_sub_re_uniform`,
   `norm_finiteTriadReading_le_rpow_one_sub_re_uniform`,
   `capped_witness_lineLoss_lt_rpow_neg_four_re`,
   `no_witness_at_sublinear_loss_scale`,
   `uncapped_witness_lineLoss_lt_inv_sq`,
   `uncapped_witness_operator_sq_dist_le_inv_im`,
   `norm_finiteTriadReading_le_triadTailBound_of_le_linear`,
   `no_finite_witness_at_sublinear_prefix_scale`,
   `exists_uvRegularRankOne_jointSurvivingPartition_ge_rpow_one_sub_re`)**:
   Splitting `relativePartition` and `etaTerm` at `N = ⌊|s.im|⌋₊` proves that uniformly across all
   `b : SpectralBand 1` and `K : ℕ` (`0 < σ = s.re < 1`, `1 ≤ |s.im|`), `‖relativePartition b s‖`,
   `‖jointSurvivingPartition b s‖`, and `‖finiteTriadReading b K s‖` are `O_σ(|s.im|^{1 - σ})`,
   strictly below `|s.im|^{1/(1+σ)}` by `|s.im|^{-σ^2/(1+σ)}`. Conversely, on `0 < σ < 1 / 2`,
   hybridizing the coherent half-turn window at `N = ⌊|s.im| / (4π)⌋₊` with a ground-mode UV-slack
   shift `δ₀ = (32 / Λ)(N + 1)^{-4σ}` and the convexity bound `‖ζ(s)‖ = O_σ(|s.im|^{3(1-σ)/4})`
   produces physical `uvRegularRankOne` missing waves achieving `‖jointSurvivingPartition b_v s‖ ≥ c_σ |s.im|^{1 - σ}`
   at every large ordinate (zero or not). Consequently:
   - every capped witness obeys `lineLoss v.val < M_sharp(σ)^4 Λ⁻¹ |s.im|^{-4σ}`, defeating any
     profile family scaled at `lineLoss v.val ≥ c |s.im|^{-4σ/(1+σ)}`;
   - every uncapped witness obeys `lineLoss v.val < M_sharp(σ)^{2/σ} |s.im|^{-2}` and
     `‖D^2 - G_v^2‖ ≤ M_sharp(σ)^{1/σ} |s.im|^{-1}`;
   - every finite-prefix witness `(v, K)` obeys `K > ((1 - σ) / (3^σ σ)) |s.im|`, defeating
     `K ≤ C |s.im|^{1/(1+σ)}`.

3. **Uniform single-wave horizontal certificates on Speiser-shadowed ordinates and 75% clean windows
   (`norm_riemannZeta_ge_exp_of_not_mem_speiserDisk_segment`,
   `exists_uniform_single_witness_of_not_mem_speiserDisk_segment`,
   `eventually_volume_clean_zero_exception_heights_window_ge_three_quarters`,
   `exists_speiserShadow_exponential_density_uniform_witnesses`,
   `exists_all_ordinates_littlewood_strip_uniform_witness`)**:
   Outside all Speiser disks on `[a, b] + iγ` (`0 < a ≤ b < 1 / 2`, `γ ≥ 100`), `‖ζ(σ ± iγ)‖` grows
   leftward at least as `‖ζ(b + iγ)‖ exp(((log(γ / 2π)) / 2 - 1 / 10)(b - σ))`, and **one single
   pair `(v : MissingWave, K : ℕ)`** simultaneously certifies all `σ ∈ [a, b]` on both lines `σ ± iγ`
   in both the capped and uncapped finite-eigenvalue tests. Clean `(0, 1 / 2)` lines occupy measure
   `≥ (3 / 4) H - 3` (`75%`) of every `[T + 3 / 2, T + H - 3 / 2]` (`T^{24 / 25} ≤ H ≤ T`), while
   across Speiser-shadowed ordinates on `[T₁ + 1 / 2, T₂ - 1 / 2]`, outside an exponentially small
   height set of measure `≤ A'(T₂ - T₁) exp(-κ / 2400) + K'(log U)^2`, every ordinate admits one
   simultaneous witness `(v, K)` across `[a, 1 / 2 - κ / log U] ± iγ` (and across
   `[a, b] ⊂ (0, c log log γ / log γ)` at 100% of ordinates `γ ≥ T₀`).
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Complex ContinuousLinearMap Filter MeasureTheory Set Topology
open scoped ComplexConjugate InnerProductSpace
open AntipodalSpectrum AntipodalSpectrum.ComplementaryHalves
open InverseSpectrum.ShellMixing

/-! ### Part 1: Exact $U(1)^{\mathbb{N}^+}$ phase-gauge blindness and arithmetic twist erasure -/

/-- Bounded diagonal unitary operator on `Gas = ℓ²(ℕ+)` multiplying coordinate `n` by `u n` (`‖u n‖ = 1`). -/
def unitPhaseDiag (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) : GasOp :=
  HTGeometry.LpDiagonal.lpDiag u 1 zero_le_one (fun n => (hu n).le)

@[simp] theorem unitPhaseDiag_apply (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (x : Gas) (n : ℕ+) :
    unitPhaseDiag u hu x n = u n * x n := rfl

private def starPhase (u : ℕ+ → ℂ) : ℕ+ → ℂ := fun n => star (u n)

private theorem norm_starPhase (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) :
    ∀ n, ‖starPhase u n‖ = 1 := fun n => by
  simp only [starPhase, norm_star, hu n]

private theorem norm_unitPhaseDiag_le (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) :
    ‖unitPhaseDiag u hu‖ ≤ 1 :=
  HTGeometry.LpDiagonal.norm_lpDiag_le u 1 zero_le_one (fun n => (hu n).le)

private theorem mul_star_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    z * star z = 1 ∧ star z * z = 1 := by
  have h1 : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, one_pow, Complex.ofReal_one]
  exact ⟨h1, by rw [mul_comm, h1]⟩

private theorem unitPhaseDiag_apply_star (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (x : Gas) :
    unitPhaseDiag u hu (unitPhaseDiag (starPhase u) (norm_starPhase u hu) x) = x := by
  apply lp.ext
  funext n
  simp only [unitPhaseDiag_apply, starPhase, ← mul_assoc, (mul_star_eq_one_of_norm_eq_one (hu n)).1,
    one_mul]

private theorem unitPhaseDiag_star_apply (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (x : Gas) :
    unitPhaseDiag (starPhase u) (norm_starPhase u hu) (unitPhaseDiag u hu x) = x := by
  apply lp.ext
  funext n
  simp only [unitPhaseDiag_apply, starPhase, ← mul_assoc, (mul_star_eq_one_of_norm_eq_one (hu n)).2,
    one_mul]

private theorem norm_unitPhaseDiag_eq (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (x : Gas) :
    ‖unitPhaseDiag u hu x‖ = ‖x‖ := by
  apply le_antisymm
  · exact ((unitPhaseDiag u hu).le_opNorm x).trans
      (mul_le_of_le_one_left (norm_nonneg x) (norm_unitPhaseDiag_le u hu))
  · calc ‖x‖ = ‖unitPhaseDiag (starPhase u) (norm_starPhase u hu) (unitPhaseDiag u hu x)‖ := by
          rw [unitPhaseDiag_star_apply]
      _ ≤ ‖unitPhaseDiag (starPhase u) (norm_starPhase u hu)‖ * ‖unitPhaseDiag u hu x‖ :=
          (unitPhaseDiag (starPhase u) (norm_starPhase u hu)).le_opNorm _
      _ ≤ 1 * ‖unitPhaseDiag u hu x‖ :=
          mul_le_mul_of_nonneg_right (norm_unitPhaseDiag_le _ _) (norm_nonneg _)
      _ = ‖unitPhaseDiag u hu x‖ := one_mul _

private theorem inner_unitPhaseDiag_left (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (x y : Gas) :
    inner ℂ (unitPhaseDiag u hu x) y =
      inner ℂ x (unitPhaseDiag (starPhase u) (norm_starPhase u hu) y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [unitPhaseDiag_apply, starPhase, RCLike.inner_apply, map_mul, Complex.star_def]
  ring

private theorem unitPhaseDiag_comm_criticalOperator (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (x : Gas) :
    criticalOperator (unitPhaseDiag u hu x) = unitPhaseDiag u hu (criticalOperator x) := by
  apply lp.ext
  funext n
  change (attenuation n : ℂ) * (u n * x n) = u n * ((attenuation n : ℂ) * x n)
  ring

private theorem unitPhaseDiag_comm_squareHeat (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (x : Gas) :
    squareHeat.val (unitPhaseDiag u hu x) = unitPhaseDiag u hu (squareHeat.val x) := by
  change criticalOperator (criticalOperator (unitPhaseDiag u hu x)) =
    unitPhaseDiag u hu (criticalOperator (criticalOperator x))
  rw [unitPhaseDiag_comm_criticalOperator, unitPhaseDiag_comm_criticalOperator]

private theorem projected_omitLine_sq_unitPhaseDiag (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (v : Gas) :
    (projected (omitLine (unitPhaseDiag u hu v))) ^ 2 =
      (unitPhaseDiag u hu).comp
        (((projected (omitLine v)) ^ 2).comp (unitPhaseDiag (starPhase u) (norm_starPhase u hu))) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [line_square, comp_apply, sub_apply, smul_apply, map_sub, map_smul,
    norm_unitPhaseDiag_eq]
  change squareHeat.val x - ((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ •
      (inner ℂ (criticalOperator (unitPhaseDiag u hu v)) x •
        criticalOperator (unitPhaseDiag u hu v)) =
    unitPhaseDiag u hu (squareHeat.val (unitPhaseDiag (starPhase u) (norm_starPhase u hu) x)) -
      ((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ •
        (inner ℂ (criticalOperator v) (unitPhaseDiag (starPhase u) (norm_starPhase u hu) x) •
          unitPhaseDiag u hu (criticalOperator v))
  rw [← unitPhaseDiag_comm_squareHeat, unitPhaseDiag_apply_star,
    unitPhaseDiag_comm_criticalOperator, inner_unitPhaseDiag_left]

private theorem approxNumber_unitPhaseDiag_conj (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (A : GasOp)
    (k : ℕ) :
    _root_.RHTower.approxNumber
      ((unitPhaseDiag u hu).comp (A.comp (unitPhaseDiag (starPhase u) (norm_starPhase u hu)))) k =
      _root_.RHTower.approxNumber A k := by
  let U := unitPhaseDiag u hu
  let U' := unitPhaseDiag (starPhase u) (norm_starPhase u hu)
  have hU : ‖U‖ ≤ 1 := norm_unitPhaseDiag_le u hu
  have hU' : ‖U'‖ ≤ 1 := norm_unitPhaseDiag_le _ _
  change _root_.RHTower.rectApproxNumber (U.comp (A.comp U')) k =
    _root_.RHTower.rectApproxNumber A k
  apply le_antisymm
  · have h1 := _root_.RHTower.rectApproxNumber_comp_le_left U (A.comp U') k
    have h2 := _root_.RHTower.rectApproxNumber_comp_le_right A U' k
    exact (h1.trans (mul_le_of_le_one_left (_root_.RHTower.rectApproxNumber_nonneg _ _) hU)).trans
      (h2.trans (mul_le_of_le_one_right (_root_.RHTower.rectApproxNumber_nonneg _ _) hU'))
  · have hA_eq : A = U'.comp ((U.comp (A.comp U')).comp U) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [U, U', comp_apply, unitPhaseDiag_star_apply]
    conv_lhs => rw [hA_eq]
    have h1 := _root_.RHTower.rectApproxNumber_comp_le_left U' ((U.comp (A.comp U')).comp U) k
    have h2 := _root_.RHTower.rectApproxNumber_comp_le_right (U.comp (A.comp U')) U k
    exact (h1.trans (mul_le_of_le_one_left (_root_.RHTower.rectApproxNumber_nonneg _ _) hU')).trans
      (h2.trans (mul_le_of_le_one_right (_root_.RHTower.rectApproxNumber_nonneg _ _) hU))

private def phaseRatio (v w : Gas) (n : ℕ+) : ℂ :=
  if v n = 0 then 1 else w n / v n

private theorem norm_phaseRatio (v w : Gas) (h : ∀ n : ℕ+, ‖v n‖ = ‖w n‖) :
    ∀ n : ℕ+, ‖phaseRatio v w n‖ = 1 := by
  intro n
  unfold phaseRatio
  split_ifs with hvn
  · exact norm_one
  · rw [norm_div, ← h n, div_self (norm_ne_zero_iff.mpr hvn)]

private theorem unitPhaseDiag_phaseRatio_apply (v w : Gas) (h : ∀ n : ℕ+, ‖v n‖ = ‖w n‖) :
    unitPhaseDiag (phaseRatio v w) (norm_phaseRatio v w h) v = w := by
  apply lp.ext
  funext n
  rw [unitPhaseDiag_apply]
  unfold phaseRatio
  split_ifs with hvn
  · have hwn : w n = 0 := norm_eq_zero.mp (by rw [← h n, hvn, norm_zero])
    rw [hvn, hwn, mul_zero]
  · exact div_mul_cancel₀ (w n) hvn

/-- **Coordinate-modulus invariance of `criticalOperator` range membership:** two `Gas` waves with
equal coordinate norms lie in `range criticalOperator` simultaneously. -/
theorem mem_range_criticalOperator_iff_of_coord_norm_eq {v w : Gas}
    (h : ∀ n : ℕ+, ‖v n‖ = ‖w n‖) :
    v ∈ LinearMap.range criticalOperator.toLinearMap ↔
      w ∈ LinearMap.range criticalOperator.toLinearMap := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨unitPhaseDiag (phaseRatio v w) (norm_phaseRatio v w h) f, ?_⟩
    change criticalOperator (unitPhaseDiag (phaseRatio v w) (norm_phaseRatio v w h) f) = w
    change criticalOperator f = v at hf
    rw [unitPhaseDiag_comm_criticalOperator, hf, unitPhaseDiag_phaseRatio_apply v w h]
  · rintro ⟨f, hf⟩
    have hsymm : ∀ n : ℕ+, ‖w n‖ = ‖v n‖ := fun n => (h n).symm
    refine ⟨unitPhaseDiag (phaseRatio w v) (norm_phaseRatio w v hsymm) f, ?_⟩
    change criticalOperator (unitPhaseDiag (phaseRatio w v) (norm_phaseRatio w v hsymm) f) = v
    change criticalOperator f = w at hf
    rw [unitPhaseDiag_comm_criticalOperator, hf, unitPhaseDiag_phaseRatio_apply w v hsymm]

private def toModulusPhase (v : Gas) (n : ℕ+) : ℂ :=
  if v n = 0 then 1 else ((‖v n‖ : ℝ) : ℂ) / v n

private theorem norm_toModulusPhase (v : Gas) : ∀ n : ℕ+, ‖toModulusPhase v n‖ = 1 := by
  intro n
  unfold toModulusPhase
  split_ifs with hvn
  · exact norm_one
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hvn)]

/-- Canonical zero-phase nonnegative modulus wave `n ↦ (‖v n‖ : ℂ)` in `Gas`. -/
def modulusGas (v : Gas) : Gas :=
  unitPhaseDiag (toModulusPhase v) (norm_toModulusPhase v) v

@[simp] theorem modulusGas_apply (v : Gas) (n : ℕ+) :
    modulusGas v n = ((‖v n‖ : ℝ) : ℂ) := by
  rw [modulusGas, unitPhaseDiag_apply]
  unfold toModulusPhase
  split_ifs with hvn
  · simp [hvn]
  · exact div_mul_cancel₀ _ hvn

/-- Canonical real nonnegative zero-phase twin of any conserving rank-one missing wave `v`. -/
def modulusMissingWave (v : MissingWave) : MissingWave :=
  ⟨modulusGas v.val, fun hmem => v.property
    ((mem_range_criticalOperator_iff_of_coord_norm_eq (fun n => by
      rw [modulusGas_apply, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)])).mpr hmem)⟩

theorem modulusMissingWave_re_nonneg_and_im_zero (v : MissingWave) (n : ℕ+) :
    0 ≤ ((modulusMissingWave v).val n).re ∧ ((modulusMissingWave v).val n).im = 0 := by
  change 0 ≤ (modulusGas v.val n).re ∧ (modulusGas v.val n).im = 0
  rw [modulusGas_apply, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨norm_nonneg _, rfl⟩

/-- **Exact $U(1)^{\mathbb{N}^+}$ phase-gauge blindness of `missingWaveSpectrum`:**
whenever `v, w : MissingWave` have equal coordinate moduli `∀ n : ℕ+, ‖v.val n‖ = ‖w.val n‖`,
their surviving spectra `missingWaveSpectrum`, fourth-trace losses `lineLoss`, UV-regularity
predicates `uvRegularRankOne`, finite-prefix readings `finiteTriadReading`, and full partitions
`jointSurvivingPartition` are **identically equal**. -/
theorem missingWaveSpectrum_eq_of_coord_norm_eq {v w : MissingWave}
    (h : ∀ n : ℕ+, ‖v.val n‖ = ‖w.val n‖) :
    missingWaveSpectrum v = missingWaveSpectrum w ∧
    lineLoss v.val = lineLoss w.val ∧
    (∀ (s : ℂ) (hs0 : 0 < s.re) (Λ : ℝ),
      uvRegularRankOne s hs0 Λ v ↔ uvRegularRankOne s hs0 Λ w) ∧
    (∀ (K : ℕ) (s : ℂ),
      finiteTriadReading (missingWaveSpectrum v) K s =
        finiteTriadReading (missingWaveSpectrum w) K s) ∧
    (∀ s : ℂ,
      jointSurvivingPartition (missingWaveSpectrum v) s =
        jointSurvivingPartition (missingWaveSpectrum w) s) := by
  have hspec : missingWaveSpectrum v = missingWaveSpectrum w := by
    funext k
    apply Subtype.ext
    change _root_.RHTower.approxNumber ((projected (omitLine v.val)) ^ 2) k =
      _root_.RHTower.approxNumber ((projected (omitLine w.val)) ^ 2) k
    have hw : w.val = unitPhaseDiag (phaseRatio v.val w.val) (norm_phaseRatio v.val w.val h) v.val :=
      (unitPhaseDiag_phaseRatio_apply v.val w.val h).symm
    rw [hw, projected_omitLine_sq_unitPhaseDiag, approxNumber_unitPhaseDiag_conj]
  have hloss : lineLoss v.val = lineLoss w.val := by
    rw [← relativeReading_quadratic_missingWaveSpectrum v,
      ← relativeReading_quadratic_missingWaveSpectrum w, hspec]
  refine ⟨hspec, hloss, ?_, ?_, ?_⟩
  · intro s hs0 Λ
    simp only [uvRegularRankOne, hspec, hloss]
  · intro K s
    rw [hspec]
  · intro s
    rw [hspec]

/-- Every missing wave `v` shares its exact surviving spectrum and all witness readings with its
real nonnegative twin `modulusMissingWave v`. -/
theorem missingWaveSpectrum_modulusMissingWave (v : MissingWave) :
    missingWaveSpectrum (modulusMissingWave v) = missingWaveSpectrum v ∧
    lineLoss (modulusMissingWave v).val = lineLoss v.val := by
  have h := missingWaveSpectrum_eq_of_coord_norm_eq (v := modulusMissingWave v) (w := v) (fun n => by
    change ‖modulusGas v.val n‖ = ‖v.val n‖
    rw [modulusGas_apply, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)])
  exact ⟨h.1, h.2.1⟩

/-- Bounded coordinatewise twist `(f · v)(n) = f(n) v(n)` on `Gas` (covering Möbius `μ(n)`,
Dirichlet characters `χ(n)`, Liouville `λ(n)`, and imaginary-time twists `n^{-iτ}`). -/
def boundedGasTwist (f : ℕ+ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ n, ‖f n‖ ≤ M) (v : Gas) : Gas :=
  HTGeometry.LpDiagonal.lpDiag f M hM hf v

/-- Nonnegative zero-phase twin `(|f| · |v|)(n) = (‖f(n)‖ · ‖v(n)‖ : ℂ)` of `boundedGasTwist`. -/
def absBoundedGasTwist (f : ℕ+ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ n, ‖f n‖ ≤ M) (v : Gas) :
    Gas :=
  HTGeometry.LpDiagonal.lpDiag (fun n => ((‖f n‖ : ℝ) : ℂ)) M hM
    (fun n => by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact hf n)
    (modulusGas v)

/-- **Arithmetic sign and character erasure:** for any bounded twist `f : ℕ+ → ℂ` (such as Möbius
`μ(n)` or a Dirichlet character `χ(n)`) and any `v : Gas` with `f · v ∉ range criticalOperator`,
`absBoundedGasTwist` is also a `MissingWave` and has **identically the same** `missingWaveSpectrum`,
`lineLoss`, `uvRegularRankOne`, `finiteTriadReading`, and `jointSurvivingPartition` as `f · v`. -/
theorem boundedTwist_missingWaveSpectrum_eq_abs (f : ℕ+ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ n, ‖f n‖ ≤ M) (v : Gas)
    (hmem : boundedGasTwist f hM hf v ∉ LinearMap.range criticalOperator.toLinearMap) :
    ∃ hmem_abs : absBoundedGasTwist f hM hf v ∉ LinearMap.range criticalOperator.toLinearMap,
      let wTwist : MissingWave := ⟨boundedGasTwist f hM hf v, hmem⟩
      let wAbs : MissingWave := ⟨absBoundedGasTwist f hM hf v, hmem_abs⟩
      missingWaveSpectrum wTwist = missingWaveSpectrum wAbs ∧
      lineLoss wTwist.val = lineLoss wAbs.val ∧
      (∀ (K : ℕ) (s : ℂ),
        finiteTriadReading (missingWaveSpectrum wTwist) K s =
          finiteTriadReading (missingWaveSpectrum wAbs) K s) := by
  have hnorm : ∀ n : ℕ+, ‖boundedGasTwist f hM hf v n‖ = ‖absBoundedGasTwist f hM hf v n‖ := by
    intro n
    change ‖f n * v n‖ = ‖((‖f n‖ : ℝ) : ℂ) * modulusGas v n‖
    rw [modulusGas_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (norm_nonneg _)]
  have hmem_abs : absBoundedGasTwist f hM hf v ∉ LinearMap.range criticalOperator.toLinearMap :=
    fun ha => hmem ((mem_range_criticalOperator_iff_of_coord_norm_eq hnorm).mpr ha)
  refine ⟨hmem_abs, ?_⟩
  have heq := missingWaveSpectrum_eq_of_coord_norm_eq
    (v := ⟨boundedGasTwist f hM hf v, hmem⟩) (w := ⟨absBoundedGasTwist f hM hf v, hmem_abs⟩) hnorm
  exact ⟨heq.1, heq.2.1, heq.2.2.2.1⟩

/-- **Exact invariance under unit-modulus twists:** twisting any `v : MissingWave` by `u : ℕ+ → ℂ`
with `∀ n, ‖u n‖ = 1` (e.g., Liouville `(-1)^{Ω(n)}` or `n^{-iτ}`) leaves `missingWaveSpectrum` and
all finite-prefix readings strictly unchanged. -/
theorem unitTwist_missingWaveSpectrum_eq (u : ℕ+ → ℂ) (hu : ∀ n, ‖u n‖ = 1) (v : MissingWave) :
    ∃ hmem : unitPhaseDiag u hu v.val ∉ LinearMap.range criticalOperator.toLinearMap,
      missingWaveSpectrum ⟨unitPhaseDiag u hu v.val, hmem⟩ = missingWaveSpectrum v := by
  have hnorm : ∀ n : ℕ+, ‖unitPhaseDiag u hu v.val n‖ = ‖v.val n‖ := fun n => by
    rw [unitPhaseDiag_apply, norm_mul, hu n, one_mul]
  have hmem : unitPhaseDiag u hu v.val ∉ LinearMap.range criticalOperator.toLinearMap :=
    fun ha => v.property ((mem_range_criticalOperator_iff_of_coord_norm_eq hnorm).mp ha)
  exact ⟨hmem, (missingWaveSpectrum_eq_of_coord_norm_eq
    (v := ⟨unitPhaseDiag u hu v.val, hmem⟩) (w := v) hnorm).1⟩

/-! ### Part 2: Sharp two-sided `Θ_σ(|t|^{1 - σ})` ordinate laws and collapse of the sublinear loss/prefix scales -/

private theorem inv_rpow_step_le_sub {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (n : ℕ) :
    (1 - σ) * occupationWeight n ^ σ ≤
      ((n : ℝ) + 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ) := by
  have h1mσ : 0 < 1 - σ := sub_pos.mpr hσ1
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [occupationWeight_zero, Real.one_rpow, mul_one, Nat.cast_zero, zero_add,
      Real.zero_rpow h1mσ.ne', sub_zero]
    linarith
  · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    set y : ℝ := (n : ℝ) / ((n : ℝ) + 1)
    have hy_pos : 0 < y := div_pos hn_pos hn1_pos
    have hy_le1 : y ≤ 1 := div_le_one_of_le₀ (by linarith) hn1_pos.le
    have hch := norm_thermal_chord (x := 1) (y := y) (δ := 1 - σ) (z := 1)
      hy_pos hy_le1 le_rfl h1mσ (by rw [Complex.one_re]; linarith)
    simp only [Complex.ofReal_one, Complex.one_cpow, norm_one, Real.one_rpow] at hch
    have h1my : ‖(1 : ℂ) - ((y : ℝ) : ℂ) ^ (1 : ℂ)‖ = 1 / ((n : ℝ) + 1) := by
      rw [Complex.cpow_one, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr hy_le1)]
      dsimp only [y]
      field_simp [hn1_pos.ne']
      ring
    rw [h1my] at hch
    have hmul := mul_le_mul_of_nonneg_left hch (mul_nonneg h1mσ.le
      (Real.rpow_nonneg hn1_pos.le (1 - σ)))
    have hlhs : (1 - σ) * ((n : ℝ) + 1) ^ (1 - σ) * (1 / ((n : ℝ) + 1)) =
        (1 - σ) * occupationWeight n ^ σ := by
      rw [occupationWeight_eq, Real.inv_rpow hn1_pos.le]
      have hpow : ((n : ℝ) + 1) ^ (1 - σ) / ((n : ℝ) + 1) = (((n : ℝ) + 1) ^ σ)⁻¹ := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one ((n : ℝ) + 1), ← Real.rpow_add hn1_pos,
          show 1 - σ + -1 = -σ by ring, Real.rpow_neg hn1_pos.le]
      calc (1 - σ) * ((n : ℝ) + 1) ^ (1 - σ) * (1 / ((n : ℝ) + 1))
          = (1 - σ) * (((n : ℝ) + 1) ^ (1 - σ) / ((n : ℝ) + 1)) := by ring
        _ = (1 - σ) * (((n : ℝ) + 1) ^ σ)⁻¹ := by rw [hpow]
    have hrhs : (1 - σ) * ((n : ℝ) + 1) ^ (1 - σ) * ((1 / (1 - σ)) * (1 - y ^ (1 - σ))) =
        ((n : ℝ) + 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ) := by
      have hy_pow : ((n : ℝ) + 1) ^ (1 - σ) * y ^ (1 - σ) = (n : ℝ) ^ (1 - σ) := by
        dsimp only [y]
        rw [Real.div_rpow hn_pos.le hn1_pos.le,
          mul_div_cancel₀ _ (Real.rpow_pos_of_pos hn1_pos _).ne']
      calc (1 - σ) * ((n : ℝ) + 1) ^ (1 - σ) * ((1 / (1 - σ)) * (1 - y ^ (1 - σ)))
          = ((n : ℝ) + 1) ^ (1 - σ) * (1 - y ^ (1 - σ)) := by field_simp [h1mσ.ne']
        _ = ((n : ℝ) + 1) ^ (1 - σ) - ((n : ℝ) + 1) ^ (1 - σ) * y ^ (1 - σ) := by ring
        _ = ((n : ℝ) + 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ) := by rw [hy_pow]
    rwa [hlhs, hrhs] at hmul

/-- Elementary telescoping power-sum bound `∑_{n < N} (n + 1)^{-σ} ≤ N^{1 - σ} / (1 - σ)`
for `0 < σ < 1`. -/
theorem sum_range_occupationWeight_rpow_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, occupationWeight n ^ σ) ≤ (N : ℝ) ^ (1 - σ) / (1 - σ) := by
  have h1mσ : 0 < 1 - σ := sub_pos.mpr hσ1
  have hsum : (∑ n ∈ Finset.range N, (1 - σ) * occupationWeight n ^ σ) ≤
      ∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ)) :=
    Finset.sum_le_sum fun n _ => inv_rpow_step_le_sub hσ0 hσ1 n
  rw [← Finset.mul_sum] at hsum
  have htel : (∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ))) =
      (N : ℝ) ^ (1 - σ) := by
    have h := Finset.sum_range_sub (fun n : ℕ => (n : ℝ) ^ (1 - σ)) N
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Real.zero_rpow h1mσ.ne', sub_zero] at h
    exact h
  rw [htel] at hsum
  exact (le_div_iff₀' h1mσ).mpr hsum

private theorem norm_complexDrop_le_two_mul_occ (b : SpectralBand 1) (n : ℕ) {s : ℂ}
    (hs0 : 0 < s.re) :
    ‖complexDrop b n s‖ ≤ 2 * occupationWeight n ^ s.re := by
  unfold complexDrop
  have hocc_pos := occupationWeight_pos n
  have hb_pos := band_pos b n
  have hb_le : (b n).val ^ s.re ≤ occupationWeight n ^ s.re :=
    Real.rpow_le_rpow hb_pos.le (b n).property.2 hs0.le
  calc ‖(occupationWeight n : ℂ) ^ s - ((b n).val : ℂ) ^ s‖
      ≤ ‖(occupationWeight n : ℂ) ^ s‖ + ‖((b n).val : ℂ) ^ s‖ := norm_sub_le _ _
    _ = occupationWeight n ^ s.re + (b n).val ^ s.re := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hocc_pos,
          Complex.norm_cpow_eq_rpow_re_of_pos hb_pos]
    _ ≤ 2 * occupationWeight n ^ s.re := by linarith

private theorem sum_range_norm_complexDrop_le (b : SpectralBand 1) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|) (M : ℕ) :
    (∑ n ∈ Finset.range M, ‖complexDrop b n s‖) ≤
      (2 / (1 - s.re) + (s.re + 1) / s.re) * |s.im| ^ (1 - s.re) := by
  set σ : ℝ := s.re
  set t : ℝ := |s.im|
  have ht_pos : 0 < t := zero_lt_one.trans_le him
  have h1mσ : 0 < 1 - σ := sub_pos.mpr hs1
  set N : ℕ := ⌊t⌋₊
  have hN_le : (N : ℝ) ≤ t := Nat.floor_le ht_pos.le
  have hN_gt : t < (N : ℝ) + 1 := Nat.lt_floor_add_one t
  have hN_pow : (N : ℝ) ^ (1 - σ) ≤ t ^ (1 - σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) hN_le h1mσ.le
  have hs_norm : ‖s‖ ≤ (σ + 1) * t := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at h
    nlinarith
  have hocc_N : occupationWeight N ^ σ ≤ t ^ (-σ) := by
    have hinv : occupationWeight N ≤ t⁻¹ := by
      rw [occupationWeight_eq]
      exact inv_anti₀ ht_pos hN_gt.le
    calc occupationWeight N ^ σ ≤ (t⁻¹) ^ σ :=
          Real.rpow_le_rpow (occupationWeight_pos N).le hinv hs0.le
      _ = t ^ (-σ) := by rw [Real.inv_rpow ht_pos.le, Real.rpow_neg ht_pos.le]
  have hprod_t : t * t ^ (-σ) = t ^ (1 - σ) := by
    calc t * t ^ (-σ) = t ^ (1 : ℝ) * t ^ (-σ) := by rw [Real.rpow_one]
      _ = t ^ (1 - σ) := by rw [← Real.rpow_add ht_pos, sub_eq_add_neg]
  rcases le_or_gt M N with hMN | hNM
  · calc (∑ n ∈ Finset.range M, ‖complexDrop b n s‖)
        ≤ ∑ n ∈ Finset.range N, ‖complexDrop b n s‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN) (fun _ _ _ => norm_nonneg _)
      _ ≤ ∑ n ∈ Finset.range N, 2 * occupationWeight n ^ σ :=
          Finset.sum_le_sum fun n _ => norm_complexDrop_le_two_mul_occ b n hs0
      _ = 2 * ∑ n ∈ Finset.range N, occupationWeight n ^ σ := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ((N : ℝ) ^ (1 - σ) / (1 - σ)) :=
          mul_le_mul_of_nonneg_left (sum_range_occupationWeight_rpow_le hs0 hs1 N) zero_le_two
      _ ≤ 2 * (t ^ (1 - σ) / (1 - σ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hN_pow h1mσ.le) zero_le_two
      _ = (2 / (1 - σ)) * t ^ (1 - σ) := by ring
      _ ≤ (2 / (1 - σ) + (σ + 1) / σ) * t ^ (1 - σ) := by
          have hadd_nn : 0 ≤ ((σ + 1) / σ) * t ^ (1 - σ) := by positivity
          linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hNM.le
    rw [Finset.sum_range_add]
    have hhead : (∑ n ∈ Finset.range N, ‖complexDrop b n s‖) ≤ (2 / (1 - σ)) * t ^ (1 - σ) := by
      calc (∑ n ∈ Finset.range N, ‖complexDrop b n s‖)
          ≤ 2 * ∑ n ∈ Finset.range N, occupationWeight n ^ σ := by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun n _ => norm_complexDrop_le_two_mul_occ b n hs0
        _ ≤ 2 * ((N : ℝ) ^ (1 - σ) / (1 - σ)) :=
            mul_le_mul_of_nonneg_left (sum_range_occupationWeight_rpow_le hs0 hs1 N) zero_le_two
        _ ≤ 2 * (t ^ (1 - σ) / (1 - σ)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hN_pow h1mσ.le) zero_le_two
        _ = (2 / (1 - σ)) * t ^ (1 - σ) := by ring
    let β : GibbsExponent := ⟨σ, hs0⟩
    have htail : (∑ j ∈ Finset.range m, ‖complexDrop b (N + j) s‖) ≤
        ((σ + 1) / σ) * t ^ (1 - σ) := by
      have h1 : (∑ j ∈ Finset.range m, ‖complexDrop b (N + j) s‖) ≤
          (‖s‖ / σ) * ∑ j ∈ Finset.range m,
            (occupationWeight (N + j) ^ σ - occupationWeight (N + j + 1) ^ σ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        have hcb := complexDrop_bound b (N + j) β le_rfl
        have hde := drop_le_edge (powerResponse β) b (N + j)
        exact hcb.trans (mul_le_mul_of_nonneg_left hde (div_nonneg (norm_nonneg s) hs0.le))
      have htel : (∑ j ∈ Finset.range m,
          (occupationWeight (N + j) ^ σ - occupationWeight (N + j + 1) ^ σ)) ≤
          occupationWeight N ^ σ := by
        have ht := Finset.sum_range_sub' (fun j : ℕ => occupationWeight (N + j) ^ σ) m
        simp only [Nat.add_zero, ← Nat.add_assoc] at ht
        rw [ht]
        linarith [Real.rpow_nonneg (occupationWeight_pos (N + m)).le σ]
      calc (∑ j ∈ Finset.range m, ‖complexDrop b (N + j) s‖)
          ≤ (‖s‖ / σ) * occupationWeight N ^ σ :=
            h1.trans (mul_le_mul_of_nonneg_left htel (div_nonneg (norm_nonneg s) hs0.le))
        _ ≤ (((σ + 1) * t) / σ) * t ^ (-σ) :=
            mul_le_mul (div_le_div_of_nonneg_right hs_norm hs0.le) hocc_N
              (Real.rpow_nonneg (occupationWeight_pos N).le σ) (by positivity)
        _ = ((σ + 1) / σ) * (t * t ^ (-σ)) := by ring
        _ = ((σ + 1) / σ) * t ^ (1 - σ) := by rw [hprod_t]
    linarith

/-- **Sharp `O_σ(|Im s|^{1 - Re s})` uniform upper bound on `relativePartition` across `SpectralBand 1`:**
for every `b : SpectralBand 1` and `0 < Re s < 1`, `1 ≤ |Im s|`, `‖relativePartition b s‖` grows at
most as `|Im s|^{1 - Re s}` (strictly smaller than `|Im s|^{1 / (1 + Re s)}`). -/
theorem norm_relativePartition_le_rpow_one_sub_re_uniform (b : SpectralBand 1)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|) :
    ‖relativePartition b s‖ ≤
      (2 / (1 - s.re) + (s.re + 1) / s.re) * |s.im| ^ (1 - s.re) := by
  have hsum : Summable (fun n : ℕ => ‖complexDrop b n s‖) := (summable_complexDrop b hs0).norm
  calc ‖relativePartition b s‖
      ≤ ∑' n : ℕ, ‖complexDrop b n s‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ (2 / (1 - s.re) + (s.re + 1) / s.re) * |s.im| ^ (1 - s.re) :=
        le_of_tendsto hsum.hasSum.tendsto_sum_nat
          (Eventually.of_forall (sum_range_norm_complexDrop_le b hs0 hs1 him))

private theorem norm_etaTerm_le_two_mul_occ (k : ℕ) {s : ℂ} (hs0 : 0 < s.re) :
    ‖_root_.RHTower.etaTerm s k‖ ≤ 2 * occupationWeight k ^ s.re := by
  unfold _root_.RHTower.etaTerm
  have hpos1 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  have hpos2 : (0 : ℝ) < 2 * (k : ℝ) + 2 := by positivity
  have h1 : ‖((2 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ occupationWeight k ^ s.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos1, Complex.neg_re, Real.rpow_neg hpos1.le,
      ← Real.inv_rpow hpos1.le, occupationWeight_eq]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hpos1.le)
      (inv_anti₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1) (by linarith)) hs0.le
  have h2 : ‖((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)‖ ≤ occupationWeight k ^ s.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos2, Complex.neg_re, Real.rpow_neg hpos2.le,
      ← Real.inv_rpow hpos2.le, occupationWeight_eq]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hpos2.le)
      (inv_anti₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1) (by linarith)) hs0.le
  calc ‖((2 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - ((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)‖
      ≤ ‖((2 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖ + ‖((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)‖ :=
        norm_sub_le _ _
    _ ≤ 2 * occupationWeight k ^ s.re := by linarith

private theorem norm_etaTerm_le_chord (k : ℕ) {s : ℂ} (hs0 : 0 < s.re) :
    ‖_root_.RHTower.etaTerm s k‖ ≤
      (‖s‖ / s.re) * (occupationWeight (2 * k) ^ s.re - occupationWeight (2 * (k + 1)) ^ s.re) := by
  have heven : (occupationWeight (2 * k) : ℂ) ^ s = ((2 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
    have hpos : (0 : ℝ) < (2 * k : ℕ) + 1 := by positivity
    have harg : (((2 * k : ℕ) + 1 : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne
    rw [occupationWeight_eq, Complex.ofReal_inv, Complex.inv_cpow _ s harg, Complex.cpow_neg]
    push_cast; ring_nf
  have hodd : (occupationWeight (2 * k + 1) : ℂ) ^ s = ((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
    have hpos : (0 : ℝ) < (2 * k + 1 : ℕ) + 1 := by positivity
    have harg : (((2 * k + 1 : ℕ) + 1 : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne
    rw [occupationWeight_eq, Complex.ofReal_inv, Complex.inv_cpow _ s harg, Complex.cpow_neg]
    push_cast; ring_nf
  unfold _root_.RHTower.etaTerm
  rw [← heven, ← hodd]
  have hch := norm_thermal_chord (occupationWeight_pos (2 * k + 1))
    (occupationWeight_antitone (Nat.le_succ (2 * k))) (occupation_in_unit (2 * k)).2 hs0 le_rfl
  have hmono : occupationWeight (2 * (k + 1)) ^ s.re ≤ occupationWeight (2 * k + 1) ^ s.re :=
    Real.rpow_le_rpow (occupationWeight_pos _).le
      (occupationWeight_antitone (by omega : 2 * k + 1 ≤ 2 * (k + 1))) hs0.le
  exact hch.trans (mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (norm_nonneg s) hs0.le))

private theorem sum_range_norm_etaTerm_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (him : 1 ≤ |s.im|) (M : ℕ) :
    (∑ k ∈ Finset.range M, ‖_root_.RHTower.etaTerm s k‖) ≤
      (2 / (1 - s.re) + (s.re + 1) / s.re) * |s.im| ^ (1 - s.re) := by
  set σ : ℝ := s.re
  set t : ℝ := |s.im|
  have ht_pos : 0 < t := zero_lt_one.trans_le him
  have h1mσ : 0 < 1 - σ := sub_pos.mpr hs1
  set N : ℕ := ⌊t⌋₊
  have hN_le : (N : ℝ) ≤ t := Nat.floor_le ht_pos.le
  have hN_gt : t < (N : ℝ) + 1 := Nat.lt_floor_add_one t
  have hN_pow : (N : ℝ) ^ (1 - σ) ≤ t ^ (1 - σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) hN_le h1mσ.le
  have hs_norm : ‖s‖ ≤ (σ + 1) * t := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at h
    nlinarith
  have hocc_2N : occupationWeight (2 * N) ^ σ ≤ t ^ (-σ) := by
    have hinv : occupationWeight (2 * N) ≤ t⁻¹ := by
      rw [occupationWeight_eq]
      push_cast
      exact inv_anti₀ ht_pos (by linarith)
    calc occupationWeight (2 * N) ^ σ ≤ (t⁻¹) ^ σ :=
          Real.rpow_le_rpow (occupationWeight_pos _).le hinv hs0.le
      _ = t ^ (-σ) := by rw [Real.inv_rpow ht_pos.le, Real.rpow_neg ht_pos.le]
  have hprod_t : t * t ^ (-σ) = t ^ (1 - σ) := by
    calc t * t ^ (-σ) = t ^ (1 : ℝ) * t ^ (-σ) := by rw [Real.rpow_one]
      _ = t ^ (1 - σ) := by rw [← Real.rpow_add ht_pos, sub_eq_add_neg]
  rcases le_or_gt M N with hMN | hNM
  · calc (∑ k ∈ Finset.range M, ‖_root_.RHTower.etaTerm s k‖)
        ≤ ∑ k ∈ Finset.range N, ‖_root_.RHTower.etaTerm s k‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN) (fun _ _ _ => norm_nonneg _)
      _ ≤ 2 * ∑ k ∈ Finset.range N, occupationWeight k ^ σ := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun k _ => norm_etaTerm_le_two_mul_occ k hs0
      _ ≤ 2 * ((N : ℝ) ^ (1 - σ) / (1 - σ)) :=
          mul_le_mul_of_nonneg_left (sum_range_occupationWeight_rpow_le hs0 hs1 N) zero_le_two
      _ ≤ 2 * (t ^ (1 - σ) / (1 - σ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hN_pow h1mσ.le) zero_le_two
      _ = (2 / (1 - σ)) * t ^ (1 - σ) := by ring
      _ ≤ (2 / (1 - σ) + (σ + 1) / σ) * t ^ (1 - σ) := by
          have hadd_nn : 0 ≤ ((σ + 1) / σ) * t ^ (1 - σ) := by positivity
          linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hNM.le
    rw [Finset.sum_range_add]
    have hhead : (∑ k ∈ Finset.range N, ‖_root_.RHTower.etaTerm s k‖) ≤
        (2 / (1 - σ)) * t ^ (1 - σ) := by
      calc (∑ k ∈ Finset.range N, ‖_root_.RHTower.etaTerm s k‖)
          ≤ 2 * ∑ k ∈ Finset.range N, occupationWeight k ^ σ := by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun k _ => norm_etaTerm_le_two_mul_occ k hs0
        _ ≤ 2 * ((N : ℝ) ^ (1 - σ) / (1 - σ)) :=
            mul_le_mul_of_nonneg_left (sum_range_occupationWeight_rpow_le hs0 hs1 N) zero_le_two
        _ ≤ 2 * (t ^ (1 - σ) / (1 - σ)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hN_pow h1mσ.le) zero_le_two
        _ = (2 / (1 - σ)) * t ^ (1 - σ) := by ring
    have htail : (∑ j ∈ Finset.range m, ‖_root_.RHTower.etaTerm s (N + j)‖) ≤
        ((σ + 1) / σ) * t ^ (1 - σ) := by
      have h1 : (∑ j ∈ Finset.range m, ‖_root_.RHTower.etaTerm s (N + j)‖) ≤
          (‖s‖ / σ) * ∑ j ∈ Finset.range m,
            (occupationWeight (2 * (N + j)) ^ σ - occupationWeight (2 * (N + j + 1)) ^ σ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => norm_etaTerm_le_chord (N + j) hs0
      have htel : (∑ j ∈ Finset.range m,
          (occupationWeight (2 * (N + j)) ^ σ - occupationWeight (2 * (N + j + 1)) ^ σ)) ≤
          occupationWeight (2 * N) ^ σ := by
        have ht := Finset.sum_range_sub' (fun j : ℕ => occupationWeight (2 * (N + j)) ^ σ) m
        simp only [Nat.add_zero, ← Nat.add_assoc] at ht
        rw [ht]
        linarith [Real.rpow_nonneg (occupationWeight_pos (2 * (N + m))).le σ]
      calc (∑ j ∈ Finset.range m, ‖_root_.RHTower.etaTerm s (N + j)‖)
          ≤ (‖s‖ / σ) * occupationWeight (2 * N) ^ σ :=
            h1.trans (mul_le_mul_of_nonneg_left htel (div_nonneg (norm_nonneg s) hs0.le))
        _ ≤ (((σ + 1) * t) / σ) * t ^ (-σ) :=
            mul_le_mul (div_le_div_of_nonneg_right hs_norm hs0.le) hocc_2N
              (Real.rpow_nonneg (occupationWeight_pos _).le σ) (by positivity)
        _ = ((σ + 1) / σ) * (t * t ^ (-σ)) := by ring
        _ = ((σ + 1) / σ) * t ^ (1 - σ) := by rw [hprod_t]
    linarith

/-- Explicit constant governing the sharp `|Im s|^{1 - Re s}` ceiling on `jointSurvivingPartition`
and `finiteTriadReading` across `SpectralBand 1`. -/
def sharpOrdinateCeilingConstant (σ : ℝ) : ℝ :=
  (((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) *
    (4 * (2 / (1 - σ) + (σ + 1) / σ))

theorem sharpOrdinateCeilingConstant_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    0 < sharpOrdinateCeilingConstant σ := by
  have h2 : 0 < (2 : ℝ) ^ (1 - σ) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow one_lt_two (sub_pos.mpr hσ1))
  have h1mσ : 0 < 1 - σ := sub_pos.mpr hσ1
  unfold sharpOrdinateCeilingConstant
  positivity

private theorem factor_ratio_le {s : ℂ} (_hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖ ≤
      ((2 : ℝ) ^ s.re + 1) / ((2 : ℝ) ^ (1 - s.re) - 1) := by
  have h2s : ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ s.re := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
  have h2_1s : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
      Complex.sub_re, Complex.one_re]
  have hpos2 : 0 < (2 : ℝ) ^ (1 - s.re) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow one_lt_two (sub_pos.mpr hs1))
  have hhi1 : ‖(2 : ℂ) ^ s - 1‖ ≤ (2 : ℝ) ^ s.re + 1 := by
    have h := norm_sub_le ((2 : ℂ) ^ s) 1
    rwa [h2s, norm_one] at h
  have hlo2 : (2 : ℝ) ^ (1 - s.re) - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
    rw [norm_sub_rev]
    have h := norm_sub_norm_le ((2 : ℂ) ^ (1 - s)) 1
    rwa [h2_1s, norm_one] at h
  calc ‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖
      ≤ ((2 : ℝ) ^ s.re + 1) / ‖1 - (2 : ℂ) ^ (1 - s)‖ :=
        div_le_div_of_nonneg_right hhi1 (norm_nonneg _)
    _ ≤ ((2 : ℝ) ^ s.re + 1) / ((2 : ℝ) ^ (1 - s.re) - 1) :=
        div_le_div_of_nonneg_left (by positivity) hpos2 hlo2

/-- **Uniform `O_σ(|Im s|^{1 - Re s})` upper bound on `finiteTriadReading` across all `b : SpectralBand 1`
and all prefix lengths `K : ℕ`:** strictly improves `|Im s|^{1 / (1 + Re s)}` by `|Im s|^{-σ^2 / (1 + σ)}`. -/
theorem norm_finiteTriadReading_le_rpow_one_sub_re_uniform (b : SpectralBand 1) (K : ℕ)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|) :
    ‖finiteTriadReading b K s‖ ≤ sharpOrdinateCeilingConstant s.re * |s.im| ^ (1 - s.re) := by
  set σ : ℝ := s.re
  set t : ℝ := |s.im|
  set B : ℝ := (2 / (1 - σ) + (σ + 1) / σ) * t ^ (1 - σ)
  have hB_nn : 0 ≤ B := by
    dsimp only [B]
    have h1 : 0 < 1 - σ := sub_pos.mpr hs1
    positivity
  have htriad_split : (∑ k ∈ Finset.range K, dyadicSpectralTriad b s k) =
      (∑ k ∈ Finset.range K, _root_.RHTower.etaTerm s k) -
        ((∑ n ∈ Finset.range (2 * K), complexDrop b n s) -
          (2 : ℂ) ^ (1 - s) * ∑ k ∈ Finset.range K, complexDrop b k s) := by
    have hcongr : (∑ k ∈ Finset.range K, dyadicSpectralTriad b s k) =
        ∑ k ∈ Finset.range K, (_root_.RHTower.etaTerm s k -
          (complexDrop b (2 * k) s + complexDrop b (2 * k + 1) s -
            (2 : ℂ) ^ (1 - s) * complexDrop b k s)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have heven : (occupationWeight (2 * k) : ℂ) ^ s = ((2 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
        have hpos : (0 : ℝ) < (2 * k : ℕ) + 1 := by positivity
        have harg : (((2 * k : ℕ) + 1 : ℝ) : ℂ).arg ≠ Real.pi := by
          rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne
        rw [occupationWeight_eq, Complex.ofReal_inv, Complex.inv_cpow _ s harg, Complex.cpow_neg]
        push_cast; ring_nf
      have hodd : (occupationWeight (2 * k + 1) : ℂ) ^ s = ((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
        have hpos : (0 : ℝ) < (2 * k + 1 : ℕ) + 1 := by positivity
        have harg : (((2 * k + 1 : ℕ) + 1 : ℝ) : ℂ).arg ≠ Real.pi := by
          rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne
        rw [occupationWeight_eq, Complex.ofReal_inv, Complex.inv_cpow _ s harg, Complex.cpow_neg]
        push_cast; ring_nf
      have h2pow : (2 : ℂ) ^ (1 - s) * (occupationWeight k : ℂ) ^ s =
          2 * ((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
        have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have harg : (((k : ℝ) + 1 : ℝ) : ℂ).arg ≠ Real.pi := by
          rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne
        have hsplit : (2 : ℂ) ^ (1 - s) = (2 : ℂ) * (2 : ℂ) ^ (-s) := by
          rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
        have hmul : (2 : ℂ) ^ (-s) * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
            ((2 * (k : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
          have h := (Complex.mul_cpow_ofReal_nonneg zero_le_two hpos.le (-s)).symm
          rw [Complex.ofReal_ofNat] at h
          refine h.trans ?_
          congr 1; push_cast; ring
        have hocc_k : (occupationWeight k : ℂ) ^ s = (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
          rw [occupationWeight_eq, Complex.ofReal_inv, Complex.inv_cpow _ s harg, Complex.cpow_neg]
        rw [hocc_k, hsplit, mul_assoc, hmul]
      unfold dyadicSpectralTriad _root_.RHTower.etaTerm complexDrop
      linear_combination heven + hodd - h2pow
    have hpair_sum : ∀ m : ℕ,
        (∑ k ∈ Finset.range m, (complexDrop b (2 * k) s + complexDrop b (2 * k + 1) s)) =
          ∑ n ∈ Finset.range (2 * m), complexDrop b n s := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih, show 2 * (m + 1) = 2 * m + 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    rw [hcongr, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hpair_sum K, Finset.mul_sum]
  have heta_le : ‖∑ k ∈ Finset.range K, _root_.RHTower.etaTerm s k‖ ≤ B :=
    (norm_sum_le _ _).trans (sum_range_norm_etaTerm_le hs0 hs1 him K)
  have hcd2K_le : ‖∑ n ∈ Finset.range (2 * K), complexDrop b n s‖ ≤ B :=
    (norm_sum_le _ _).trans (sum_range_norm_complexDrop_le b hs0 hs1 him (2 * K))
  have hcdK_le : ‖(2 : ℂ) ^ (1 - s) * ∑ k ∈ Finset.range K, complexDrop b k s‖ ≤ 2 * B := by
    have h2_norm : ‖(2 : ℂ) ^ (1 - s)‖ ≤ 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
        Complex.sub_re, Complex.one_re]
      calc (2 : ℝ) ^ (1 - σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
        _ = 2 := Real.rpow_one 2
    have hsumK : ‖∑ k ∈ Finset.range K, complexDrop b k s‖ ≤ B :=
      (norm_sum_le _ _).trans (sum_range_norm_complexDrop_le b hs0 hs1 him K)
    rw [norm_mul]
    exact mul_le_mul h2_norm hsumK (norm_nonneg _) zero_le_two
  have hsum_norm : ‖∑ k ∈ Finset.range K, dyadicSpectralTriad b s k‖ ≤ 4 * B := by
    rw [htriad_split]
    have h1 := norm_sub_le (∑ k ∈ Finset.range K, _root_.RHTower.etaTerm s k)
      ((∑ n ∈ Finset.range (2 * K), complexDrop b n s) -
        (2 : ℂ) ^ (1 - s) * ∑ k ∈ Finset.range K, complexDrop b k s)
    have h2 := norm_sub_le (∑ n ∈ Finset.range (2 * K), complexDrop b n s)
      ((2 : ℂ) ^ (1 - s) * ∑ k ∈ Finset.range K, complexDrop b k s)
    linarith
  unfold finiteTriadReading
  rw [norm_mul, norm_div]
  calc (‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖) *
          ‖∑ k ∈ Finset.range K, dyadicSpectralTriad b s k‖
      ≤ (((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)) * (4 * B) :=
        mul_le_mul (factor_ratio_le hs0 hs1) hsum_norm (norm_nonneg _) (by
          have hpos2 : 0 < (2 : ℝ) ^ (1 - σ) - 1 :=
            sub_pos.mpr (Real.one_lt_rpow one_lt_two (sub_pos.mpr hs1))
          positivity)
    _ = sharpOrdinateCeilingConstant σ * t ^ (1 - σ) := by
        dsimp only [B, sharpOrdinateCeilingConstant]; ring

/-- **Sharp `O_σ(|Im s|^{1 - Re s})` uniform upper bound on `jointSurvivingPartition` across all
`b : SpectralBand 1`:** improves `norm_jointSurvivingPartition_le_rpow_im_uniform` from exponent
`1 / (1 + Re s)` to `1 - Re s`. -/
theorem norm_jointSurvivingPartition_le_rpow_one_sub_re_uniform (b : SpectralBand 1)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|) :
    ‖jointSurvivingPartition b s‖ ≤ sharpOrdinateCeilingConstant s.re * |s.im| ^ (1 - s.re) := by
  by_contra! hgt
  set gap : ℝ := ‖jointSurvivingPartition b s‖ -
      sharpOrdinateCeilingConstant s.re * |s.im| ^ (1 - s.re)
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  obtain ⟨K, hK⟩ := ((tendsto_triadTailBound_zero hs0).eventually (gt_mem_nhds hgap)).exists
  have htail := norm_jointSurviving_sub_finiteTriadReading_le b K hs0 hs1.ne
  have htri : ‖jointSurvivingPartition b s‖ ≤
      ‖finiteTriadReading b K s‖ + ‖jointSurvivingPartition b s - finiteTriadReading b K s‖ := by
    have h := norm_add_le (finiteTriadReading b K s)
      (jointSurvivingPartition b s - finiteTriadReading b K s)
    simpa only [add_sub_cancel] using h
  have hftr := norm_finiteTriadReading_le_rpow_one_sub_re_uniform b K hs0 hs1 him
  dsimp only [gap] at hK
  linarith

/-- Explicit constant governing sharp high-ordinate witness loss decay. -/
def sharpWitnessLossConstant (σ : ℝ) : ℝ :=
  sharpOrdinateCeilingConstant σ * σ / ((2 : ℝ) ^ σ - 1)

theorem sharpWitnessLossConstant_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    0 < sharpWitnessLossConstant σ := by
  have h1 : 0 < sharpOrdinateCeilingConstant σ := sharpOrdinateCeilingConstant_pos hσ0 hσ1
  have h2 : 0 < (2 : ℝ) ^ σ - 1 := sub_pos.mpr (Real.one_lt_rpow one_lt_two hσ0)
  unfold sharpWitnessLossConstant
  positivity

/-- **Sharp `|Im s|^{-4 Re s}` fourth-trace loss collapse for capped witnesses:**
every conserving rank-one omission `v : MissingWave` beating `uvZeroThresholdFactor s Λ * lineLoss v.val`
at `0 < Re s < 1`, `1 ≤ |Im s|` satisfies
`lineLoss v.val < sharpWitnessLossConstant(s.re)^4 * Λ⁻¹ * |Im s|^{-4 s.re}` (strictly smaller than
`|Im s|^{-4 s.re / (1 + s.re)}` by `|Im s|^{-4 s.re^2 / (1 + s.re)}`). -/
theorem capped_witness_lineLoss_lt_rpow_neg_four_re
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|) {Λ : ℝ} (hΛ : 0 < Λ)
    (v : MissingWave)
    (hgt : uvZeroThresholdFactor s Λ * lineLoss v.val <
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4) :
    lineLoss v.val < sharpWitnessLossConstant s.re ^ 4 * Λ⁻¹ * |s.im| ^ (-4 * s.re) := by
  set σ : ℝ := s.re
  set t : ℝ := |s.im|
  have ht_pos : 0 < t := zero_lt_one.trans_le him
  have h2_pos : 0 < (2 : ℝ) ^ σ - 1 := sub_pos.mpr (Real.one_lt_rpow one_lt_two hs0)
  have h2_lo : (2 : ℝ) ^ σ - 1 ≤ ‖(2 : ℂ) ^ s - 1‖ := by
    have h2s : ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ σ := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
    have h := norm_sub_norm_le ((2 : ℂ) ^ s) 1
    rwa [h2s, norm_one] at h
  have hL_pos : 0 < Λ * lineLoss v.val := mul_pos hΛ (line_loss_bounds v).1
  set r4 : ℝ := (Λ * lineLoss v.val) ^ (1 / 4 : ℝ)
  have hr4_pos : 0 < r4 := Real.rpow_pos_of_pos hL_pos _
  have hr4_pow : r4 ^ 4 = Λ * lineLoss v.val := by
    dsimp only [r4]
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hL_pos.le,
      show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
  have hbase_lt : ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) * r4 <
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ := by
    by_contra! hle
    have hp := pow_le_pow_left₀ (norm_nonneg _) hle 4
    have heq : (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) * r4) ^ 4 =
        uvZeroThresholdFactor s Λ * lineLoss v.val := by
      dsimp only [σ]
      rw [mul_pow, mul_pow, hr4_pow, uvZeroThresholdFactor]; ring
    rw [heq] at hp
    exact hgt.not_ge hp
  have hub := norm_jointSurvivingPartition_le_rpow_one_sub_re_uniform
    (missingWaveSpectrum v) hs0 hs1 him
  have ht_le_s : t / σ ≤ ‖s‖ / σ :=
    div_le_div_of_nonneg_right (Complex.abs_im_le_norm s) hs0.le
  have hchain : ((2 : ℝ) ^ σ - 1) * (t / σ) * r4 <
      sharpOrdinateCeilingConstant σ * t ^ (1 - σ) := by
    have hle1 : ((2 : ℝ) ^ σ - 1) * (t / σ) ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) :=
      mul_le_mul h2_lo ht_le_s (by positivity) (norm_nonneg _)
    exact (mul_le_mul_of_nonneg_right hle1 hr4_pos.le).trans_lt (hbase_lt.trans_le hub)
  have hr4_lt : r4 < sharpWitnessLossConstant σ * t ^ (-σ) := by
    have hpos_lhs : 0 < ((2 : ℝ) ^ σ - 1) * (t / σ) := by positivity
    have hdiv := (lt_div_iff₀' hpos_lhs).mpr hchain
    have hrew : (sharpOrdinateCeilingConstant σ * t ^ (1 - σ)) / (((2 : ℝ) ^ σ - 1) * (t / σ)) =
        sharpWitnessLossConstant σ * t ^ (-σ) := by
      have ht_pow : t ^ (1 - σ) / t = t ^ (-σ) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one t, ← Real.rpow_add ht_pos,
          show 1 - σ + -1 = -σ by ring]
      unfold sharpWitnessLossConstant
      calc (sharpOrdinateCeilingConstant σ * t ^ (1 - σ)) / (((2 : ℝ) ^ σ - 1) * (t / σ))
          = (sharpOrdinateCeilingConstant σ * σ / ((2 : ℝ) ^ σ - 1)) * (t ^ (1 - σ) / t) := by
            field_simp [h2_pos.ne', hs0.ne', ht_pos.ne']
        _ = (sharpOrdinateCeilingConstant σ * σ / ((2 : ℝ) ^ σ - 1)) * t ^ (-σ) := by
            rw [ht_pow]
    rwa [hrew] at hdiv
  have hp4 := pow_lt_pow_left₀ hr4_lt hr4_pos.le (by norm_num : 4 ≠ 0)
  rw [hr4_pow, mul_pow, ← Real.rpow_natCast (t ^ (-σ)) 4, ← Real.rpow_mul ht_pos.le,
    show (-σ) * (4 : ℕ) = -4 * σ by push_cast; ring] at hp4
  have hdiv := (lt_div_iff₀' hΛ).mpr hp4
  exact hdiv.trans_eq (by ring)

/-- **Explicit no-go for the `|Im s|^{-4σ / (1 + σ)}` loss scale:**
for every `0 < σ < 1`, `Λ > 0`, and `c > 0`, at all sufficiently large ordinates `|Im s| ≥ T₀`
along `Re s = σ`, **no** missing wave `v` with `c * |Im s|^{-4σ / (1 + σ)} ≤ lineLoss v.val` can
beat `uvZeroThresholdFactor s Λ * lineLoss v.val` (even on clean lines and even under RH). -/
theorem no_witness_at_sublinear_loss_scale
    {σ Λ c : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hΛ : 0 < Λ) (hc : 0 < c) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ s : ℂ, s.re = σ → T₀ ≤ |s.im| → ∀ v : MissingWave,
      c * |s.im| ^ (-4 * σ / (1 + σ)) ≤ lineLoss v.val →
        ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 ≤
          uvZeroThresholdFactor s Λ * lineLoss v.val := by
  have hexp_pos : 0 < 4 * σ ^ 2 / (1 + σ) := by positivity
  set A : ℝ := sharpWitnessLossConstant σ ^ 4 * Λ⁻¹ / c
  have hA_pos : 0 < A := by
    have hM := sharpWitnessLossConstant_pos hσ0 hσ1
    dsimp only [A]; positivity
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hexp_pos).eventually_gt_atTop A)
  refine ⟨max 1 T₁, le_max_left 1 T₁, fun s hs_re hT v hloss => ?_⟩
  by_contra! hgt
  have hs0 : 0 < s.re := hs_re ▸ hσ0
  have hs1' : s.re < 1 := hs_re ▸ hσ1
  have him1 : 1 ≤ |s.im| := (le_max_left 1 T₁).trans hT
  have himT₁ : T₁ ≤ |s.im| := (le_max_right 1 T₁).trans hT
  have ht_pos : 0 < |s.im| := zero_lt_one.trans_le him1
  have hlt := capped_witness_lineLoss_lt_rpow_neg_four_re hs0 hs1' him1 hΛ v hgt
  rw [hs_re] at hlt
  have hcomb : c * |s.im| ^ (-4 * σ / (1 + σ)) <
      sharpWitnessLossConstant σ ^ 4 * Λ⁻¹ * |s.im| ^ (-4 * σ) := hloss.trans_lt hlt
  have hpow_gt : A < |s.im| ^ (4 * σ ^ 2 / (1 + σ)) := hT₁ |s.im| himT₁
  have hmul := mul_lt_mul_of_pos_right hpow_gt
    (mul_pos hc (Real.rpow_pos_of_pos ht_pos (-4 * σ)))
  have hlhs : A * (c * |s.im| ^ (-4 * σ)) =
      sharpWitnessLossConstant σ ^ 4 * Λ⁻¹ * |s.im| ^ (-4 * σ) := by
    dsimp only [A]
    field_simp [hc.ne']
  have hrhs : |s.im| ^ (4 * σ ^ 2 / (1 + σ)) * (c * |s.im| ^ (-4 * σ)) =
      c * |s.im| ^ (-4 * σ / (1 + σ)) := by
    rw [mul_left_comm, ← Real.rpow_add ht_pos]
    congr 2
    have h1σ : 1 + σ ≠ 0 := by linarith
    field_simp [h1σ]
    ring
  rw [hlhs, hrhs] at hmul
  exact hcomb.not_ge hmul.le

/-- **Sharp `|Im s|^{-2}` fourth-trace loss collapse for uncapped witnesses:**
every conserving rank-one omission `v : MissingWave` beating `chordZeroThresholdFactor s * lineLoss v.val`
at `0 < Re s < 1`, `1 ≤ |Im s|` satisfies
`lineLoss v.val < sharpWitnessLossConstant(s.re)^{2 / s.re} * |Im s|^{-2}` (exponent `-2`
independent of `Re s`, improving `-2 / (1 + Re s)`). -/
theorem uncapped_witness_lineLoss_lt_inv_sq
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|)
    (v : MissingWave)
    (hgt : chordZeroThresholdFactor s * lineLoss v.val <
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ (2 / s.re)) :
    lineLoss v.val < sharpWitnessLossConstant s.re ^ (2 / s.re) * |s.im| ^ (-2 : ℝ) := by
  set σ : ℝ := s.re
  set t : ℝ := |s.im|
  have ht_pos : 0 < t := zero_lt_one.trans_le him
  have h2_pos : 0 < (2 : ℝ) ^ σ - 1 := sub_pos.mpr (Real.one_lt_rpow one_lt_two hs0)
  have h2_lo : (2 : ℝ) ^ σ - 1 ≤ ‖(2 : ℂ) ^ s - 1‖ := by
    have h2s : ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ σ := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
    have h := norm_sub_norm_le ((2 : ℂ) ^ s) 1
    rwa [h2s, norm_one] at h
  have hll_pos : 0 < lineLoss v.val := (line_loss_bounds v).1
  have hexp_pos : 0 < 2 / σ := div_pos two_pos hs0
  set A : ℝ := chordZeroThresholdFactor s * lineLoss v.val
  have hA_pos : 0 < A := by
    dsimp only [A, chordZeroThresholdFactor, σ]
    have hs_ne : s ≠ 0 := fun h => hs0.ne' (by dsimp only [σ]; rw [h, Complex.zero_re])
    have hnorm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs_ne
    have hf_pos : 0 < ‖(2 : ℂ) ^ s - 1‖ := h2_pos.trans_le h2_lo
    positivity
  have hpow_cancel : (A ^ (σ / 2)) ^ (2 / σ) = A := by
    rw [← Real.rpow_mul hA_pos.le, show (σ / 2) * (2 / σ) = 1 by field_simp [hs0.ne'],
      Real.rpow_one]
  have hbase_lt : A ^ (σ / 2) < ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ := by
    by_contra! hle
    have hp := Real.rpow_le_rpow (norm_nonneg _) hle hexp_pos.le
    rw [hpow_cancel] at hp
    exact hgt.not_ge hp
  have hA_root : A ^ (σ / 2) = ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) * lineLoss v.val ^ (σ / 2) := by
    dsimp only [A, chordZeroThresholdFactor]
    have hbase_nn : 0 ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) := by positivity
    rw [Real.mul_rpow (Real.rpow_nonneg hbase_nn _) hll_pos.le, ← Real.rpow_mul hbase_nn,
      show (2 / σ) * (σ / 2) = 1 by field_simp [hs0.ne'], Real.rpow_one]
  rw [hA_root] at hbase_lt
  have hub := norm_jointSurvivingPartition_le_rpow_one_sub_re_uniform
    (missingWaveSpectrum v) hs0 hs1 him
  have ht_le_s : t / σ ≤ ‖s‖ / σ :=
    div_le_div_of_nonneg_right (Complex.abs_im_le_norm s) hs0.le
  have hchain : ((2 : ℝ) ^ σ - 1) * (t / σ) * lineLoss v.val ^ (σ / 2) <
      sharpOrdinateCeilingConstant σ * t ^ (1 - σ) := by
    have hle1 : ((2 : ℝ) ^ σ - 1) * (t / σ) ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) :=
      mul_le_mul h2_lo ht_le_s (by positivity) (norm_nonneg _)
    exact (mul_le_mul_of_nonneg_right hle1 (Real.rpow_nonneg hll_pos.le _)).trans_lt
      (hbase_lt.trans_le hub)
  have hroot_lt : lineLoss v.val ^ (σ / 2) < sharpWitnessLossConstant σ * t ^ (-σ) := by
    have hpos_lhs : 0 < ((2 : ℝ) ^ σ - 1) * (t / σ) := by positivity
    have hdiv := (lt_div_iff₀' hpos_lhs).mpr hchain
    have hrew : (sharpOrdinateCeilingConstant σ * t ^ (1 - σ)) / (((2 : ℝ) ^ σ - 1) * (t / σ)) =
        sharpWitnessLossConstant σ * t ^ (-σ) := by
      have ht_pow : t ^ (1 - σ) / t = t ^ (-σ) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one t, ← Real.rpow_add ht_pos,
          show 1 - σ + -1 = -σ by ring]
      unfold sharpWitnessLossConstant
      calc (sharpOrdinateCeilingConstant σ * t ^ (1 - σ)) / (((2 : ℝ) ^ σ - 1) * (t / σ))
          = (sharpOrdinateCeilingConstant σ * σ / ((2 : ℝ) ^ σ - 1)) * (t ^ (1 - σ) / t) := by
            field_simp [h2_pos.ne', hs0.ne', ht_pos.ne']
        _ = (sharpOrdinateCeilingConstant σ * σ / ((2 : ℝ) ^ σ - 1)) * t ^ (-σ) := by
            rw [ht_pow]
    rwa [hrew] at hdiv
  have hp := Real.rpow_lt_rpow (Real.rpow_nonneg hll_pos.le _) hroot_lt hexp_pos
  have hM_nn : 0 ≤ sharpWitnessLossConstant σ := (sharpWitnessLossConstant_pos hs0 hs1).le
  rw [← Real.rpow_mul hll_pos.le, show (σ / 2) * (2 / σ) = 1 by field_simp [hs0.ne'],
    Real.rpow_one, Real.mul_rpow hM_nn (Real.rpow_nonneg ht_pos.le _),
    ← Real.rpow_mul ht_pos.le, show (-σ) * (2 / σ) = -2 by field_simp [hs0.ne']] at hp
  exact hp

/-- **Sharp `O_σ(|Im s|^{-1})` operator-norm collapse of uncapped witness propagators:**
every uncapped witness `v` at `0 < Re s < 1`, `1 ≤ |Im s|` satisfies
`‖criticalOperator^2 - (projected (omitLine v.val))^2‖ ≤ sharpWitnessLossConstant(s.re)^{1 / s.re} * |Im s|^{-1}`. -/
theorem uncapped_witness_operator_sq_dist_le_inv_im
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (him : 1 ≤ |s.im|)
    (v : MissingWave)
    (hgt : chordZeroThresholdFactor s * lineLoss v.val <
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ (2 / s.re)) :
    ‖criticalOperator ^ 2 - (projected (omitLine v.val)) ^ 2‖ ≤
      sharpWitnessLossConstant s.re ^ (1 / s.re) * |s.im| ^ (-1 : ℝ) := by
  have hcons := ((nonzero_line_conserves_iff v.val).mpr v.property).2
  obtain ⟨hop_le, hhs_le, _⟩ := norm_critical_sq_sub_sq_le_sqrt_fourth_trace_defect hcons
  change _ ≤ Real.sqrt (traceLoss (projected (omitLine v.val))) at hhs_le
  rw [traceLoss_omitLine] at hhs_le
  have hloss := uncapped_witness_lineLoss_lt_inv_sq hs0 hs1 him v hgt
  have ht_pos : 0 < |s.im| := zero_lt_one.trans_le him
  have hM_nn : 0 ≤ sharpWitnessLossConstant s.re := (sharpWitnessLossConstant_pos hs0 hs1).le
  have hsqrt_le := Real.sqrt_le_sqrt hloss.le
  have hrhs_eq : Real.sqrt (sharpWitnessLossConstant s.re ^ (2 / s.re) * |s.im| ^ (-2 : ℝ)) =
      sharpWitnessLossConstant s.re ^ (1 / s.re) * |s.im| ^ (-1 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg hM_nn _) (Real.rpow_nonneg ht_pos.le _),
      ← Real.rpow_mul hM_nn, ← Real.rpow_mul ht_pos.le,
      show (2 / s.re) * (1 / 2) = 1 / s.re by ring, show (-2 : ℝ) * (1 / 2) = -1 by ring]
  rw [hrhs_eq] at hsqrt_le
  exact (hop_le.trans hhs_le).trans hsqrt_le

private theorem norm_dyadicSpectralTriad_le_four_mul_occ (b : SpectralBand 1) (k : ℕ)
    {s : ℂ} (hs0 : 0 < s.re) (_hs1 : s.re < 1) :
    ‖dyadicSpectralTriad b s k‖ ≤ 4 * occupationWeight k ^ s.re := by
  unfold dyadicSpectralTriad
  have hb2k_pos := band_pos b (2 * k)
  have hb2k1_pos := band_pos b (2 * k + 1)
  have hbk_pos := band_pos b k
  have h1 : ‖((b (2 * k)).val : ℂ) ^ s‖ ≤ occupationWeight (2 * k) ^ s.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb2k_pos]
    exact Real.rpow_le_rpow hb2k_pos.le (b (2 * k)).property.2 hs0.le
  have h2 : ‖((b (2 * k + 1)).val : ℂ) ^ s‖ ≤ occupationWeight (2 * k + 1) ^ s.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb2k1_pos]
    exact Real.rpow_le_rpow hb2k1_pos.le (b (2 * k + 1)).property.2 hs0.le
  have h3 : ‖(2 : ℂ) ^ (1 - s) * ((b k).val : ℂ) ^ s‖ ≤ 2 * occupationWeight k ^ s.re := by
    rw [norm_mul, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.sub_re, Complex.one_re,
      Complex.norm_cpow_eq_rpow_re_of_pos hbk_pos]
    have h2_le : (2 : ℝ) ^ (1 - s.re) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - s.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul h2_le (Real.rpow_le_rpow hbk_pos.le (b k).property.2 hs0.le)
      (Real.rpow_nonneg hbk_pos.le _) zero_le_two
  have hm1 : occupationWeight (2 * k) ^ s.re ≤ occupationWeight k ^ s.re :=
    Real.rpow_le_rpow (occupationWeight_pos _).le
      (occupationWeight_antitone (by omega : k ≤ 2 * k)) hs0.le
  have hm2 : occupationWeight (2 * k + 1) ^ s.re ≤ occupationWeight k ^ s.re :=
    Real.rpow_le_rpow (occupationWeight_pos _).le
      (occupationWeight_antitone (by omega : k ≤ 2 * k + 1)) hs0.le
  have ht1 := norm_sub_le (((b (2 * k)).val : ℂ) ^ s + ((b (2 * k + 1)).val : ℂ) ^ s)
    ((2 : ℂ) ^ (1 - s) * ((b k).val : ℂ) ^ s)
  have ht2 := norm_add_le (((b (2 * k)).val : ℂ) ^ s) (((b (2 * k + 1)).val : ℂ) ^ s)
  linarith

/-- **Linear prefix horizon for `finiteTriadReading`:** whenever `(K : ℝ) ≤ ((1 - Re s) / (3^{Re s} * Re s)) * |Im s|`,
`‖finiteTriadReading b K s‖ ≤ triadTailBound K s` holds for **every** `b : SpectralBand 1`, so no
finite-prefix witness `(v, K)` can exist below this linear prefix scale. -/
theorem norm_finiteTriadReading_le_triadTailBound_of_le_linear (b : SpectralBand 1) (K : ℕ)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hK : (K : ℝ) ≤ ((1 - s.re) / ((3 : ℝ) ^ s.re * s.re)) * |s.im|) :
    ‖finiteTriadReading b K s‖ ≤ triadTailBound K s := by
  rcases eq_or_ne K 0 with rfl | hK0
  · simp only [finiteTriadReading, Finset.range_zero, Finset.sum_empty, mul_zero, norm_zero,
      triadTailBound]
    have hocc : 0 ≤ occupationWeight (2 * 0) ^ s.re :=
      Real.rpow_nonneg (occupationWeight_pos 0).le s.re
    exact mul_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (norm_nonneg s)) hs0.le) hocc)
  · set σ : ℝ := s.re
    have h1mσ : 0 < 1 - σ := sub_pos.mpr hs1
    have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hK0)
    have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hK0)
    have hsum_le : ‖∑ k ∈ Finset.range K, dyadicSpectralTriad b s k‖ ≤
        (4 / (1 - σ)) * (K : ℝ) ^ (1 - σ) := by
      calc ‖∑ k ∈ Finset.range K, dyadicSpectralTriad b s k‖
          ≤ ∑ k ∈ Finset.range K, ‖dyadicSpectralTriad b s k‖ := norm_sum_le _ _
        _ ≤ 4 * ∑ k ∈ Finset.range K, occupationWeight k ^ σ := by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun k _ => norm_dyadicSpectralTriad_le_four_mul_occ b k hs0 hs1
        _ ≤ 4 * ((K : ℝ) ^ (1 - σ) / (1 - σ)) :=
            mul_le_mul_of_nonneg_left (sum_range_occupationWeight_rpow_le hs0 hs1 K) (by norm_num)
        _ = (4 / (1 - σ)) * (K : ℝ) ^ (1 - σ) := by ring
    have hocc_ge : ((3 * (K : ℝ)) ^ σ)⁻¹ ≤ occupationWeight (2 * K) ^ σ := by
      rw [← Real.inv_rpow (by positivity : 0 ≤ 3 * (K : ℝ)), occupationWeight_eq]
      push_cast
      exact Real.rpow_le_rpow (by positivity)
        (inv_anti₀ (by positivity : (0 : ℝ) < 2 * (K : ℝ) + 1) (by linarith)) hs0.le
    have hcore : (4 / (1 - σ)) * (K : ℝ) ^ (1 - σ) ≤
        (4 * ‖s‖ / σ) * occupationWeight (2 * K) ^ σ := by
      have h3K_pow : ((3 * (K : ℝ)) ^ σ)⁻¹ = ((3 : ℝ) ^ σ)⁻¹ * (K : ℝ) ^ (-σ) := by
        rw [Real.mul_rpow (by norm_num) hK_pos.le, mul_inv, Real.rpow_neg hK_pos.le]
      have hK_split : (K : ℝ) ^ (1 - σ) = (K : ℝ) * (K : ℝ) ^ (-σ) := by
        conv_lhs => rw [sub_eq_add_neg, Real.rpow_add hK_pos, Real.rpow_one]
      have h3_pos : 0 < (3 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) σ
      have him_le : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      have hK_le' : (K : ℝ) / (1 - σ) ≤ (‖s‖ / σ) * ((3 : ℝ) ^ σ)⁻¹ := by
        have h1 : (K : ℝ) ≤ ((1 - σ) / ((3 : ℝ) ^ σ * σ)) * ‖s‖ :=
          hK.trans (mul_le_mul_of_nonneg_left him_le (by positivity))
        have h2 := (div_le_iff₀ h1mσ).mpr (show (K : ℝ) ≤ (‖s‖ / σ) * ((3 : ℝ) ^ σ)⁻¹ * (1 - σ) by
          calc (K : ℝ) ≤ ((1 - σ) / ((3 : ℝ) ^ σ * σ)) * ‖s‖ := h1
            _ = (‖s‖ / σ) * ((3 : ℝ) ^ σ)⁻¹ * (1 - σ) := by
                field_simp [h3_pos.ne', hs0.ne'])
        exact h2
      calc (4 / (1 - σ)) * (K : ℝ) ^ (1 - σ)
          = 4 * ((K : ℝ) / (1 - σ)) * (K : ℝ) ^ (-σ) := by rw [hK_split]; ring
        _ ≤ 4 * ((‖s‖ / σ) * ((3 : ℝ) ^ σ)⁻¹) * (K : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK_le' (by norm_num))
              (Real.rpow_nonneg hK_pos.le _)
        _ = (4 * ‖s‖ / σ) * (((3 * (K : ℝ)) ^ σ)⁻¹) := by rw [h3K_pow]; ring
        _ ≤ (4 * ‖s‖ / σ) * occupationWeight (2 * K) ^ σ :=
            mul_le_mul_of_nonneg_left hocc_ge (by positivity)
    unfold finiteTriadReading triadTailBound
    rw [norm_mul, norm_div]
    exact mul_le_mul_of_nonneg_left (hsum_le.trans hcore) (by positivity)

/-- **Explicit no-go for the `K ≍ |Im s|^{1 / (1 + σ)}` prefix scale:**
for every `0 < σ < 1` and `C > 0`, at all sufficiently large `|Im s| ≥ T₀` along `Re s = σ`,
**every** `b : SpectralBand 1` and `K : ℕ` with `(K : ℝ) ≤ C * |Im s|^{1 / (1 + σ)}` satisfies
`‖finiteTriadReading b K s‖ ≤ triadTailBound K s`, so neither capped nor uncapped finite-prefix
witnesses can exist at prefix scale `O(|Im s|^{1 / (1 + σ)})`. -/
theorem no_finite_witness_at_sublinear_prefix_scale
    {σ C : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hC : 0 < C) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ s : ℂ, s.re = σ → T₀ ≤ |s.im| →
      ∀ (b : SpectralBand 1) (K : ℕ), (K : ℝ) ≤ C * |s.im| ^ (1 / (1 + σ)) →
        ‖finiteTriadReading b K s‖ ≤ triadTailBound K s := by
  have hexp_pos : 0 < σ / (1 + σ) := by positivity
  have h1mσ : 0 < 1 - σ := sub_pos.mpr hσ1
  have h3_pos : 0 < (3 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) σ
  set B : ℝ := C * ((3 : ℝ) ^ σ * σ) / (1 - σ)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hexp_pos).eventually_ge_atTop B)
  refine ⟨max 1 T₁, le_max_left 1 T₁, fun s hs_re hT b K hK => ?_⟩
  have hs0 : 0 < s.re := hs_re ▸ hσ0
  have hs1' : s.re < 1 := hs_re ▸ hσ1
  have him1 : 1 ≤ |s.im| := (le_max_left 1 T₁).trans hT
  have himT₁ : T₁ ≤ |s.im| := (le_max_right 1 T₁).trans hT
  have ht_pos : 0 < |s.im| := zero_lt_one.trans_le him1
  refine norm_finiteTriadReading_le_triadTailBound_of_le_linear b K hs0 hs1' ?_
  rw [hs_re]
  have hpow_ge : B ≤ |s.im| ^ (σ / (1 + σ)) := hT₁ |s.im| himT₁
  have hmul := mul_le_mul_of_nonneg_right hpow_ge
    (mul_nonneg ((div_pos h1mσ (mul_pos h3_pos hσ0)).le)
      (Real.rpow_nonneg ht_pos.le (1 / (1 + σ))))
  have hlhs : B * (((1 - σ) / ((3 : ℝ) ^ σ * σ)) * |s.im| ^ (1 / (1 + σ))) =
      C * |s.im| ^ (1 / (1 + σ)) := by
    dsimp only [B]
    field_simp [h1mσ.ne', h3_pos.ne', hσ0.ne']
  have hrhs : |s.im| ^ (σ / (1 + σ)) * (((1 - σ) / ((3 : ℝ) ^ σ * σ)) * |s.im| ^ (1 / (1 + σ))) =
      ((1 - σ) / ((3 : ℝ) ^ σ * σ)) * |s.im| := by
    rw [mul_left_comm, ← Real.rpow_add ht_pos,
      show σ / (1 + σ) + 1 / (1 + σ) = 1 by field_simp [show 1 + σ ≠ 0 by linarith]; ring,
      Real.rpow_one]
  rw [hlhs, hrhs] at hmul
  exact hK.trans hmul

private theorem ofReal_cpow_conj {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (r : ℂ) ^ (conj s) = conj ((r : ℂ) ^ s) := by
  have harg : (r : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne
  have h := Complex.cpow_conj (r : ℂ) s harg
  rwa [Complex.conj_ofReal] at h

private theorem dyadicSpectralTriad_conj (b : SpectralBand 1) (s : ℂ) (k : ℕ) :
    dyadicSpectralTriad b (conj s) k = conj (dyadicSpectralTriad b s k) := by
  unfold dyadicSpectralTriad
  have h1 := ofReal_cpow_conj (band_pos b (2 * k)) s
  have h2 := ofReal_cpow_conj (band_pos b (2 * k + 1)) s
  have h3 := ofReal_cpow_conj (band_pos b k) s
  have h4 : (2 : ℂ) ^ (1 - conj s) = conj ((2 : ℂ) ^ (1 - s)) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      show 1 - conj s = conj (1 - s) by simp]
    exact ofReal_cpow_conj two_pos (1 - s)
  rw [h1, h2, h3, h4, map_sub, map_add, map_mul]

private theorem norm_jointSurvivingPartition_conj (b : SpectralBand 1) {s : ℂ}
    (hs0 : 0 < s.re) (hs_re : s.re ≠ 1) :
    ‖jointSurvivingPartition b (conj s)‖ = ‖jointSurvivingPartition b s‖ := by
  have hcs0 : 0 < (conj s).re := by simpa using hs0
  have hcs_re : (conj s).re ≠ 1 := by simpa using hs_re
  rw [jointSurvivingPartition_eq_tsum_dyadicSpectralTriad b hcs0 hcs_re,
    jointSurvivingPartition_eq_tsum_dyadicSpectralTriad b hs0 hs_re]
  have htsum : (∑' k : ℕ, dyadicSpectralTriad b (conj s) k) =
      conj (∑' k : ℕ, dyadicSpectralTriad b s k) := by
    simp_rw [dyadicSpectralTriad_conj]
    exact (Complex.conjCLE.map_tsum (f := fun k : ℕ => dyadicSpectralTriad b s k)).symm
  have hf1 : (2 : ℂ) ^ (conj s) - 1 = conj ((2 : ℂ) ^ s - 1) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ofReal_cpow_conj two_pos s, map_sub, map_one]
  have hf2 : 1 - (2 : ℂ) ^ (1 - conj s) = conj (1 - (2 : ℂ) ^ (1 - s)) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, show 1 - conj s = conj (1 - s) by simp,
      ofReal_cpow_conj two_pos (1 - s), map_sub, map_one]
  rw [htsum, hf1, hf2, ← map_div₀, ← map_mul, Complex.norm_conj]

private theorem four_pow_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 4 ≤ 16 * a ^ 4 + 16 * b ^ 4 := by
  rcases le_total a b with hab | hba
  · have h1 : (a + b) ^ 4 ≤ (2 * b) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h2 : 0 ≤ 16 * a ^ 4 := by positivity
    nlinarith [show (2 * b) ^ 4 = 16 * b ^ 4 by ring]
  · have h1 : (a + b) ^ 4 ≤ (2 * a) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h2 : 0 ≤ 16 * b ^ 4 := by positivity
    nlinarith [show (2 * a) ^ 4 = 16 * a ^ 4 by ring]

/-- **Matching `Ω_σ(|Im s|^{1 - σ})` lower bound inside `uvRegularRankOne` on `0 < σ < 1 / 2`:**
the `O_σ(|Im s|^{1 - σ})` ceiling is **sharp** across `uvRegularRankOne`: for every `0 < σ < 1 / 2`
and `Λ > 0`, there exist `c > 0` and `T₀ ≥ 1` such that at **every** `s` with `s.re = σ` and
`|s.im| ≥ T₀` (including every Speiser-shadowed ordinate and any hypothetical zero of `ζ`), some
conserving `v : MissingWave` in `uvRegularRankOne s hs0 Λ` achieves
`c * |s.im|^{1 - σ} ≤ ‖jointSurvivingPartition (missingWaveSpectrum v) s‖`. -/
theorem exists_uvRegularRankOne_jointSurvivingPartition_ge_rpow_one_sub_re
    {σ Λ : ℝ} (hσ0 : 0 < σ) (hσ_half : σ < 1 / 2) (hΛ : 0 < Λ) :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ s : ℂ, ∀ hs0 : 0 < s.re, s.re = σ → T₀ ≤ |s.im| →
        ∃ v : MissingWave, uvRegularRankOne s hs0 Λ v ∧
          c * |s.im| ^ (1 - σ) ≤ ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ := by
  have hσ1 : σ < 1 := by linarith
  have h1mσ : 0 < 1 - σ := sub_pos.mpr hσ1
  set η : ℝ := (1 - σ) / 2
  have hη0 : 0 < η := by dsimp only [η]; positivity
  have hη_half : η ≤ 1 / 2 := by dsimp only [η]; linarith
  obtain ⟨Cζ, hCζ, hconv⟩ := _root_.RHTower.exists_norm_riemannZeta_le_convexity hη0 hη_half
  have h2_pos : 0 < (2 : ℝ) ^ σ - 1 := sub_pos.mpr (Real.one_lt_rpow one_lt_two hσ0)
  set c_win : ℝ := (1 / (32 * Real.pi)) * (Real.pi) ^ σ
  have hc_win_pos : 0 < c_win := by dsimp only [c_win]; positivity
  set c_out : ℝ := ((2 : ℝ) ^ σ - 1) * (c_win / 4)
  have hc_out_pos : 0 < c_out := by dsimp only [c_out]; positivity
  -- Thresholds ensuring `N = ⌊t / (4π)⌋₊ ≥ 1`, `δ₀ ≤ 3/4`, `16 δ₀^3 < Λ / 2`, and `Cζ t^{3(1-σ)/4} + 2 ≤ (c_win / 2) t^{1-σ}`.
  have hexp_4σ : 0 < 4 * σ := by positivity
  set M_uv : ℝ := max ((128 / (3 * Λ)) ^ (1 / (4 * σ)))
      ((32 ^ 4 / Λ ^ 4) ^ (1 / (12 * σ)))
  have hexp_gap : 0 < (1 - σ) / 4 := by positivity
  obtain ⟨T_gap, hT_gap⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hexp_gap).eventually_ge_atTop ((4 * (Cζ + 2)) / c_win))
  set T₀ : ℝ := max (max 8 (8 * Real.pi * (M_uv + 2))) T_gap
  have hT₀_ge1 : 1 ≤ T₀ := le_trans (by norm_num : (1 : ℝ) ≤ 8)
    ((le_max_left 8 _).trans (le_max_left _ T_gap))
  refine ⟨c_out, hc_out_pos, T₀, hT₀_ge1, fun s hs0 hs_re hT => ?_⟩
  set t : ℝ := |s.im|
  have ht8 : 8 ≤ t := ((le_max_left 8 _).trans (le_max_left _ T_gap)).trans hT
  have ht_M : 8 * Real.pi * (M_uv + 2) ≤ t :=
    ((le_max_right 8 _).trans (le_max_left _ T_gap)).trans hT
  have ht_gap : T_gap ≤ t := (le_max_right _ T_gap).trans hT
  have ht_pos : 0 < t := by linarith
  -- Work at positive ordinate `z = σ + i t` (`z = s` if `0 ≤ s.im`, `z = conj s` if `s.im < 0`).
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hz_re : z.re = σ := by simp [z]
  have hz_im : z.im = t := by simp [z]
  have hz0 : 0 < z.re := hz_re ▸ hσ0
  have hzt : 0 < z.im := hz_im ▸ ht_pos
  set N : ℕ := ⌊t / (4 * Real.pi)⌋₊
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have ht_div_ge2 : 2 * (M_uv + 2) ≤ t / (4 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * Real.pi)]
    linarith
  have hM_uv_nn : 0 ≤ M_uv := le_max_of_le_left (Real.rpow_nonneg (by positivity) _)
  have hN_ge2 : 2 ≤ N := by
    exact Nat.le_floor (by linarith : (2 : ℝ) ≤ t / (4 * Real.pi))
  have hN_pos : 0 < N := by omega
  have hN_le : (N : ℝ) ≤ t / (4 * Real.pi) := Nat.floor_le (by positivity)
  have hN_gt : t / (4 * Real.pi) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hN_ge_half : t / (8 * Real.pi) ≤ (N : ℝ) := by
    have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge2
    have hmul := (div_lt_iff₀ (by positivity : 0 < 4 * Real.pi)).mp hN_gt
    rw [div_le_iff₀ (by positivity : 0 < 8 * Real.pi)]
    nlinarith [Real.pi_pos]
  have hN1_gt_M : M_uv < (N : ℝ) + 1 := by linarith
  have hsize : (2 * (N : ℝ) + 1) * Real.pi ≤ z.im := by
    rw [hz_im]
    have hmul := (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mp hN_le
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos
    nlinarith [Real.pi_pos]
  -- Construct the hybrid window + ground-slack profile `b_hyb : SpectralBand 1`.
  let u := halfTurnFraction hzt.ne'
  let v_vec (j : ℕ) : ℂ :=
    (occupationWeight (N + j) : ℂ) ^ z - ((occupationWeight (N + j) * u.val : ℝ) : ℂ) ^ z
  have hx_win : ∀ j ∈ Finset.range N,
      occupationWeight (N + j) * u.val ∈
        Icc (occupationWeight (N + j + 1)) (occupationWeight (N + j)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have ha : Real.pi / z.im ≤ occupationWeight (2 * N) := by
      rw [occupationWeight_eq, ← one_div, Nat.cast_mul, Nat.cast_ofNat]
      apply (div_le_div_iff₀ hzt (by positivity : 0 < 2 * (N : ℝ) + 1)).mpr
      simpa only [one_mul, mul_comm Real.pi] using hsize
    have hcost := ((halfTurn_fraction_loss hzt).trans ha).trans
      (occupationWeight_antitone (show N + j + 1 ≤ 2 * N by omega))
    have hret : 1 - occupationWeight (N + j + 1) ≤ u.val := by
      change 1 - u.val ≤ _ at hcost; linarith only [hcost]
    have hrec : occupationWeight (N + j) * (1 - occupationWeight (N + j + 1)) =
        occupationWeight (N + j + 1) := by
      simp only [occupationWeight_eq, Nat.cast_add, Nat.cast_one]; field_simp; ring
    exact ⟨hrec.symm.trans_le (mul_le_mul_of_nonneg_left hret (occupationWeight_pos _).le),
      mul_le_of_le_one_right (occupationWeight_pos _).le u.property.2.le⟩
  have hlen : ∀ j ∈ Finset.range N, occupationWeight (2 * N) ^ z.re ≤ ‖v_vec j‖ := by
    intro j hj
    dsimp only [v_vec]
    rw [norm_scaled_occupation_chord z (occupationWeight_pos _) u.property.1]
    have hj' := Finset.mem_range.mp hj
    exact (Real.rpow_le_rpow (occupationWeight_pos _).le
      (occupationWeight_antitone (show N + j ≤ 2 * N by omega)) hz0.le).trans
      (le_mul_of_one_le_right (Real.rpow_nonneg (occupationWeight_pos _).le _)
        (halfTurn_chord_one_le hzt))
  obtain ⟨S, hS, hsel⟩ := exists_complex_subset (Finset.range N) v_vec
  set δ₀ : ℝ := (32 / Λ) * occupationWeight N ^ (4 * σ)
  have hδ₀_pos : 0 < δ₀ := by dsimp only [δ₀]; positivity
  have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hoccN_pow : occupationWeight N ^ (4 * σ) = (((N : ℝ) + 1) ^ (4 * σ))⁻¹ := by
    rw [occupationWeight_eq, Real.inv_rpow hN1_pos.le]
  have hδ₀_le : δ₀ ≤ 3 / 4 := by
    have hM1 : (128 / (3 * Λ)) ^ (1 / (4 * σ)) < (N : ℝ) + 1 :=
      (le_max_left _ _).trans_lt hN1_gt_M
    have hp := Real.rpow_lt_rpow (Real.rpow_nonneg (by positivity) _) hM1 hexp_4σ
    rw [← Real.rpow_mul (by positivity),
      show (1 / (4 * σ)) * (4 * σ) = 1 by field_simp [hσ0.ne'], Real.rpow_one] at hp
    dsimp only [δ₀]
    rw [hoccN_pow]
    have hdiv := (div_lt_iff₀ (Real.rpow_pos_of_pos hN1_pos (4 * σ))).mpr
      (show 32 / Λ < (3 / 4) * ((N : ℝ) + 1) ^ (4 * σ) by
        have hrew : 128 / (3 * Λ) = (32 / Λ) / (3 / 4) := by ring
        rw [hrew, div_lt_iff₀ (by norm_num : (0 : ℝ) < 3 / 4)] at hp
        linarith)
    linarith [show (32 / Λ) * (((N : ℝ) + 1) ^ (4 * σ))⁻¹ =
      (32 / Λ) / ((N : ℝ) + 1) ^ (4 * σ) by ring]
  have h16δ₀3_lt : 16 * δ₀ ^ 3 < Λ / 2 := by
    have hM2 : (32 ^ 4 / Λ ^ 4) ^ (1 / (12 * σ)) < (N : ℝ) + 1 :=
      (le_max_right _ _).trans_lt hN1_gt_M
    have hp := Real.rpow_lt_rpow (Real.rpow_nonneg (by positivity) _) hM2 (by positivity : 0 < 12 * σ)
    rw [← Real.rpow_mul (by positivity),
      show (1 / (12 * σ)) * (12 * σ) = 1 by field_simp [hσ0.ne'], Real.rpow_one] at hp
    have hδ3 : δ₀ ^ 3 = (32 ^ 3 / Λ ^ 3) / ((N : ℝ) + 1) ^ (12 * σ) := by
      dsimp only [δ₀]
      rw [hoccN_pow, mul_pow, div_pow, inv_pow, ← Real.rpow_natCast (((N : ℝ) + 1) ^ (4 * σ)) 3,
        ← Real.rpow_mul hN1_pos.le, show (4 * σ) * (3 : ℕ) = 12 * σ by push_cast; ring]
      ring
    rw [hδ3]
    have hden_pos : 0 < ((N : ℝ) + 1) ^ (12 * σ) := Real.rpow_pos_of_pos hN1_pos _
    rw [show 16 * ((32 ^ 3 / Λ ^ 3) / ((N : ℝ) + 1) ^ (12 * σ)) =
      (16 * 32 ^ 3 / Λ ^ 3) / ((N : ℝ) + 1) ^ (12 * σ) by ring, div_lt_iff₀ hden_pos]
    have hmul := mul_lt_mul_of_pos_left hp (by positivity : 0 < Λ / 2)
    have hlhs : (Λ / 2) * (32 ^ 4 / Λ ^ 4) = 16 * 32 ^ 3 / Λ ^ 3 := by
      field_simp [hΛ.ne']; ring
    rwa [hlhs] at hmul
  set τ₀ : ℝ := Real.sqrt (1 - δ₀)
  have h1mδ₀_ge : 1 / 4 ≤ 1 - δ₀ := by linarith
  have hτ₀_ge : 1 / 2 ≤ τ₀ := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by norm_num]
    exact Real.sqrt_le_sqrt h1mδ₀_ge
  have hτ₀_pos : 0 < τ₀ := by linarith
  have hτ₀_le1 : τ₀ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hτ₀_sq : τ₀ ^ 2 = 1 - δ₀ := Real.sq_sqrt (by linarith)
  let S_img : Finset ℕ := S.image (fun j => N + j)
  have h0_not_mem : 0 ∉ S_img := by
    intro hmem
    obtain ⟨j, _, hj0⟩ := Finset.mem_image.mp hmem
    omega
  let F : Finset ℕ := insert 0 S_img
  let x_hyb : ℕ → ℝ := fun k => if k = 0 then τ₀ else occupationWeight k * u.val
  have hmem_hyb : ∀ k ∈ F, x_hyb k ∈ Icc (occupationWeight (k + 1)) (occupationWeight k) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hkS
    · simp only [x_hyb, ↓reduceIte, zero_add, occupationWeight_zero]
      have hocc1 : occupationWeight 1 = 1 / 2 := by rw [occupationWeight_eq]; norm_num
      rw [hocc1]
      exact ⟨hτ₀_ge, hτ₀_le1⟩
    · obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hkS
      have hne0 : N + j ≠ 0 := by omega
      simp only [x_hyb, if_neg hne0]
      exact hx_win j (hS hjS)
  let b_hyb : SpectralBand 1 := finiteProfile F x_hyb hmem_hyb
  have hinj : Function.Injective (fun j : ℕ => N + j) := fun _ _ he => Nat.add_left_cancel he
  -- 1. Quadratic reading `≥ δ₀`.
  have hL_ge : δ₀ ≤ relativeReading quadraticResponse b_hyb := by
    rw [show relativeReading quadraticResponse b_hyb =
        ∑ k ∈ F, (occupationWeight k ^ 2 - x_hyb k ^ 2) from finiteProfile_quadratic F x_hyb hmem_hyb]
    rw [Finset.sum_insert h0_not_mem]
    have h0_term : occupationWeight 0 ^ 2 - x_hyb 0 ^ 2 = δ₀ := by
      simp only [x_hyb, ↓reduceIte, occupationWeight_zero, one_pow, hτ₀_sq]; ring
    have hrest_nn : 0 ≤ ∑ k ∈ S_img, (occupationWeight k ^ 2 - x_hyb k ^ 2) :=
      Finset.sum_nonneg fun k hk => sub_nonneg.mpr (pow_le_pow_left₀
        ((occupationWeight_pos (k + 1)).le.trans (hmem_hyb k (Finset.mem_insert_of_mem hk)).1)
        (hmem_hyb k (Finset.mem_insert_of_mem hk)).2 2)
    linarith
  -- 2. Power-`σ` reading `≤ δ₀ + occupationWeight N ^ σ`.
  let β : GibbsExponent := ⟨σ, hσ0⟩
  have hR_le : relativeReading (powerResponse β) b_hyb ≤ δ₀ + occupationWeight N ^ σ := by
    unfold relativeReading
    rw [tsum_eq_sum (s := F) (fun k hk => by
      simp only [spectralDrop, b_hyb, finiteProfile, dif_neg hk, hotEdge, sub_self])]
    have hcongr : (∑ k ∈ F, spectralDrop (powerResponse β) b_hyb k) =
        ∑ k ∈ F, (occupationWeight k ^ σ - x_hyb k ^ σ) :=
      Finset.sum_congr rfl fun k hk => by
        simp only [spectralDrop, b_hyb, finiteProfile, dif_pos hk, powerResponse]
    rw [hcongr, Finset.sum_insert h0_not_mem]
    have h0_le : occupationWeight 0 ^ σ - x_hyb 0 ^ σ ≤ δ₀ := by
      simp only [x_hyb, ↓reduceIte, occupationWeight_zero, Real.one_rpow]
      have hle : τ₀ ^ (2 : ℝ) ≤ τ₀ ^ σ :=
        Real.rpow_le_rpow_of_exponent_ge hτ₀_pos hτ₀_le1 (by linarith)
      rw [Real.rpow_two, hτ₀_sq] at hle
      linarith
    have hrest_le : (∑ k ∈ S_img, (occupationWeight k ^ σ - x_hyb k ^ σ)) ≤
        occupationWeight N ^ σ := by
      rw [Finset.sum_image hinj.injOn]
      have hsub1 : (∑ j ∈ S, (occupationWeight (N + j) ^ σ - x_hyb (N + j) ^ σ)) ≤
          ∑ j ∈ S, (occupationWeight (N + j) ^ σ - occupationWeight (N + j + 1) ^ σ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hlo := (hmem_hyb (N + j)
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))).1
        exact sub_le_sub_left (Real.rpow_le_rpow (occupationWeight_pos _).le hlo hσ0.le) _
      have hsub2 : (∑ j ∈ S, (occupationWeight (N + j) ^ σ - occupationWeight (N + j + 1) ^ σ)) ≤
          ∑ j ∈ Finset.range N, (occupationWeight (N + j) ^ σ - occupationWeight (N + j + 1) ^ σ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun j _ _ => sub_nonneg.mpr
          (Real.rpow_le_rpow (occupationWeight_pos _).le
            (occupationWeight_antitone (Nat.le_succ _)) hσ0.le)
      have htel := Finset.sum_range_sub' (fun j : ℕ => occupationWeight (N + j) ^ σ) N
      simp only [Nat.add_zero, ← Nat.add_assoc] at htel
      rw [htel] at hsub2
      linarith [hsub1, hsub2, Real.rpow_nonneg (occupationWeight_pos (N + N)).le σ]
    linarith
  -- 3. Strict UV cap `R_σ(b_hyb)^4 < Λ * L(b_hyb)`.
  have huv_strict : relativeReading (powerResponse β) b_hyb ^ 4 <
      Λ * relativeReading quadraticResponse b_hyb := by
    have hp4 : relativeReading (powerResponse β) b_hyb ^ 4 ≤
        (δ₀ + occupationWeight N ^ σ) ^ 4 :=
      pow_le_pow_left₀ (relativeReading_bounds (powerResponse β) b_hyb).1 hR_le 4
    have hsplit4 := four_pow_add_le hδ₀_pos.le (Real.rpow_nonneg (occupationWeight_pos N).le σ)
    have hterm2 : 16 * (occupationWeight N ^ σ) ^ 4 = (Λ / 2) * δ₀ := by
      dsimp only [δ₀]
      rw [← Real.rpow_natCast (occupationWeight N ^ σ) 4,
        ← Real.rpow_mul (occupationWeight_pos N).le,
        show σ * (4 : ℕ) = 4 * σ by push_cast; ring]
      field_simp [hΛ.ne']; ring
    have hterm1 : 16 * δ₀ ^ 4 < (Λ / 2) * δ₀ := by
      calc 16 * δ₀ ^ 4 = (16 * δ₀ ^ 3) * δ₀ := by ring
        _ < (Λ / 2) * δ₀ := mul_lt_mul_of_pos_right h16δ₀3_lt hδ₀_pos
    have hΛL : Λ * δ₀ ≤ Λ * relativeReading quadraticResponse b_hyb :=
      mul_le_mul_of_nonneg_left hL_ge hΛ.le
    linarith
  -- 4. Lower bound on `‖jointSurvivingPartition b_hyb z‖`.
  have hrp_ge : c_win * t ^ (1 - σ) - 2 ≤ ‖relativePartition b_hyb z‖ := by
    rw [show relativePartition b_hyb z =
        ∑ k ∈ F, ((occupationWeight k : ℂ) ^ z - (x_hyb k : ℂ) ^ z) from
          finiteProfile_partition F x_hyb hmem_hyb]
    rw [Finset.sum_insert h0_not_mem, Finset.sum_image hinj.injOn]
    have hwin_eq : (∑ j ∈ S, ((occupationWeight (N + j) : ℂ) ^ z - (x_hyb (N + j) : ℂ) ^ z)) =
        ∑ j ∈ S, v_vec j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hne0 : N + j ≠ 0 := by omega
      simp only [x_hyb, if_neg hne0, v_vec]
    rw [hwin_eq]
    have hsum_len : (N : ℝ) * occupationWeight (2 * N) ^ σ ≤ 4 * ‖∑ j ∈ S, v_vec j‖ := by
      have hs1 := Finset.sum_le_sum hlen
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hz_re] at hs1
      exact hs1.trans hsel
    have hocc2N_ge : (t / Real.pi) ^ (-σ) ≤ occupationWeight (2 * N) ^ σ := by
      have h2N1_le : 2 * (N : ℝ) + 1 ≤ t / Real.pi := by
        rw [le_div_iff₀ hpi_pos]
        simpa [hz_im] using hsize
      have hinv_ge : (t / Real.pi)⁻¹ ≤ occupationWeight (2 * N) := by
        rw [occupationWeight_eq]; push_cast
        exact inv_anti₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ) + 1) h2N1_le
      calc (t / Real.pi) ^ (-σ) = ((t / Real.pi)⁻¹) ^ σ := by
            rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
        _ ≤ occupationWeight (2 * N) ^ σ :=
            Real.rpow_le_rpow (by positivity) hinv_ge hσ0.le
    have hwin_ge : c_win * t ^ (1 - σ) ≤ ‖∑ j ∈ S, v_vec j‖ := by
      have hprod : (t / (8 * Real.pi)) * (t / Real.pi) ^ (-σ) = 4 * c_win * t ^ (1 - σ) := by
        have htp : (t / Real.pi) ^ (-σ) = t ^ (-σ) * Real.pi ^ σ := by
          rw [div_eq_mul_inv, Real.mul_rpow ht_pos.le (inv_nonneg.mpr hpi_pos.le),
            Real.inv_rpow hpi_pos.le, Real.rpow_neg hpi_pos.le, inv_inv]
        have ht1 : t * t ^ (-σ) = t ^ (1 - σ) := by
          calc t * t ^ (-σ) = t ^ (1 : ℝ) * t ^ (-σ) := by rw [Real.rpow_one]
            _ = t ^ (1 - σ) := by rw [← Real.rpow_add ht_pos, sub_eq_add_neg]
        dsimp only [c_win]
        rw [htp]
        calc (t / (8 * Real.pi)) * (t ^ (-σ) * Real.pi ^ σ)
            = (1 / (8 * Real.pi)) * Real.pi ^ σ * (t * t ^ (-σ)) := by ring
          _ = 4 * ((1 / (32 * Real.pi)) * Real.pi ^ σ) * t ^ (1 - σ) := by rw [ht1]; ring
      have hm := mul_le_mul hN_ge_half hocc2N_ge (by positivity) (Nat.cast_nonneg N)
      rw [hprod] at hm
      linarith
    have h0_le2 : ‖(occupationWeight 0 : ℂ) ^ z - (x_hyb 0 : ℂ) ^ z‖ ≤ 2 := by
      simp only [x_hyb, ↓reduceIte, occupationWeight_zero, Complex.ofReal_one, Complex.one_cpow]
      have hτ_norm : ‖(τ₀ : ℂ) ^ z‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hτ₀_pos, hz_re]
        exact Real.rpow_le_one hτ₀_pos.le hτ₀_le1 hσ0.le
      have htri := norm_sub_le (1 : ℂ) ((τ₀ : ℂ) ^ z)
      rw [norm_one] at htri
      linarith
    have htri := norm_add_le ((occupationWeight 0 : ℂ) ^ z - (x_hyb 0 : ℂ) ^ z) (∑ j ∈ S, v_vec j)
    have hrev : ‖∑ j ∈ S, v_vec j‖ - ‖(occupationWeight 0 : ℂ) ^ z - (x_hyb 0 : ℂ) ^ z‖ ≤
        ‖((occupationWeight 0 : ℂ) ^ z - (x_hyb 0 : ℂ) ^ z) + ∑ j ∈ S, v_vec j‖ := by
      have h := norm_sub_le (((occupationWeight 0 : ℂ) ^ z - (x_hyb 0 : ℂ) ^ z) + ∑ j ∈ S, v_vec j)
        ((occupationWeight 0 : ℂ) ^ z - (x_hyb 0 : ℂ) ^ z)
      simpa only [add_sub_cancel_left] using h
    linarith
  have hζ_le : ‖riemannZeta z‖ + 2 ≤ (c_win / 2) * t ^ (1 - σ) := by
    have hc_z := hconv σ t (by linarith) (by linarith) ht8
    have hexp_eq : (1 + η - σ) / 2 = 3 * (1 - σ) / 4 := by dsimp only [η]; ring
    rw [hexp_eq] at hc_z
    have h2_le : 2 ≤ 2 * t ^ (3 * (1 - σ) / 4) := by
      have h1 : 1 ≤ t ^ (3 * (1 - σ) / 4) := Real.one_le_rpow (by linarith) (by positivity)
      linarith
    have hgap_ge : (4 * (Cζ + 2)) / c_win ≤ t ^ ((1 - σ) / 4) := hT_gap t ht_gap
    have hmul := mul_le_mul_of_nonneg_right hgap_ge
      (mul_nonneg (div_nonneg hc_win_pos.le (by norm_num))
        (Real.rpow_nonneg ht_pos.le (3 * (1 - σ) / 4)))
    have hlhs : ((4 * (Cζ + 2)) / c_win) * ((c_win / 4) * t ^ (3 * (1 - σ) / 4)) =
        (Cζ + 2) * t ^ (3 * (1 - σ) / 4) := by field_simp [hc_win_pos.ne']
    have hrhs : t ^ ((1 - σ) / 4) * ((c_win / 4) * t ^ (3 * (1 - σ) / 4)) =
        (c_win / 4) * t ^ (1 - σ) := by
      rw [mul_left_comm, ← Real.rpow_add ht_pos,
        show (1 - σ) / 4 + 3 * (1 - σ) / 4 = 1 - σ by ring]
    rw [hlhs, hrhs] at hmul
    have hc_half : (c_win / 4) * t ^ (1 - σ) ≤ (c_win / 2) * t ^ (1 - σ) := by
      have hp : 0 ≤ c_win * t ^ (1 - σ) := by positivity
      linarith
    linarith
  have hjsp_gt : 2 * c_out * t ^ (1 - σ) ≤ ‖jointSurvivingPartition b_hyb z‖ := by
    have hz_ne1 : z ≠ 1 := fun h => by
      have := congrArg Complex.im h; rw [hz_im] at this; simp at this; linarith
    have hcont_z : continued z = ((2 : ℂ) ^ z - 1) * riemannZeta z :=
      continued_eq_zeta z hz_ne1
    rw [jointSurvivingPartition_eq_continued_sub, hcont_z, ← mul_sub, norm_mul]
    have h2_lo : (2 : ℝ) ^ σ - 1 ≤ ‖(2 : ℂ) ^ z - 1‖ := by
      have h2z : ‖(2 : ℂ) ^ z‖ = (2 : ℝ) ^ σ := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
          hz_re]
      have h := norm_sub_norm_le ((2 : ℂ) ^ z) 1
      rwa [h2z, norm_one] at h
    have hdiff_ge : (c_win / 2) * t ^ (1 - σ) ≤ ‖riemannZeta z - relativePartition b_hyb z‖ := by
      have h := norm_sub_norm_le (relativePartition b_hyb z) (riemannZeta z)
      rw [norm_sub_rev] at h
      linarith
    calc 2 * c_out * t ^ (1 - σ)
        = ((2 : ℝ) ^ σ - 1) * ((c_win / 2) * t ^ (1 - σ)) := by dsimp only [c_out]; ring
      _ ≤ ‖(2 : ℂ) ^ z - 1‖ * ‖riemannZeta z - relativePartition b_hyb z‖ :=
          mul_le_mul h2_lo hdiff_ge (by positivity) (norm_nonneg _)
  -- 5. Approximate `b_hyb` in `closure (physicalSpectra 1)` by a physical `v : MissingWave`.
  have hcont_jsp : Continuous (fun b : SpectralBand 1 => ‖jointSurvivingPartition b z‖) := by
    have hc1 : Continuous (fun b : SpectralBand 1 => jointSurvivingPartition b z) := by
      simp_rw [jointSurvivingPartition_eq_continued_sub]
      exact Continuous.sub continuous_const (continuous_const.mul
        (continuous_relativePartition_spectrum hz0 1))
    exact hc1.norm
  let U_open : Set (SpectralBand 1) :=
    {b | relativeReading (powerResponse β) b ^ 4 < Λ * relativeReading quadraticResponse b ∧
      c_out * t ^ (1 - σ) < ‖jointSurvivingPartition b z‖}
  have hU_isOpen : IsOpen U_open :=
    (isOpen_lt ((continuous_relativeReading (powerResponse β) 1).pow 4)
      (continuous_const.mul (continuous_relativeReading quadraticResponse 1))).inter
    (isOpen_lt continuous_const hcont_jsp)
  have hb_in_U : b_hyb ∈ U_open := ⟨huv_strict, by
    have hpos : 0 < c_out * t ^ (1 - σ) := by positivity
    linarith⟩
  have hb_cl : b_hyb ∈ closure (physicalSpectra 1) := by
    rw [closure_rank_one_spectra]; exact mem_univ _
  obtain ⟨_, hb_U, ⟨P, hd, hc_proj, rfl⟩⟩ := mem_closure_iff.mp hb_cl U_open hU_isOpen hb_in_U
  obtain ⟨w_vec, hw_ne, rfl⟩ := (missingDimension_one_iff P).mp hd
  let v : MissingWave := ⟨w_vec, (nonzero_line_conserves_iff w_vec).mp ⟨hw_ne, hc_proj⟩⟩
  have hspec : physicalSpectrum (omitLine w_vec) hd hc_proj = missingWaveSpectrum v := rfl
  rw [hspec, Set.mem_setOf_eq, relativeReading_quadratic_missingWaveSpectrum] at hb_U
  have huv_v : uvRegularRankOne s hs0 Λ v := by
    unfold uvRegularRankOne
    have hβ_eq : (⟨s.re, hs0⟩ : GibbsExponent) = β := Subtype.ext hs_re
    rw [hβ_eq]
    exact hb_U.1.le
  have hnorm_zs : ‖jointSurvivingPartition (missingWaveSpectrum v) z‖ =
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ := by
    rcases le_or_gt 0 s.im with hsim | hsim
    · have hzs : z = s := by
        apply Complex.ext
        · simp [z, hs_re]
        · simp [z, t, abs_of_nonneg hsim]
      rw [hzs]
    · have hzs : z = conj s := by
        apply Complex.ext
        · simp [z, hs_re]
        · simp [z, t, abs_of_neg hsim]
      rw [hzs, norm_jointSurvivingPartition_conj (missingWaveSpectrum v) hs0 (hs_re ▸ hσ1.ne)]
  exact ⟨v, huv_v, by rw [← hnorm_zs]; exact hb_U.2.le⟩

/-! ### Part 3: Uniform single-wave horizontal certificates on Speiser-shadowed ordinates and 75% clean windows -/

/-- Uniform Hölder exponent comparison across any horizontal interval `[a, b]`: for `0 < a ≤ σ`,
`relativeReading (powerResponse σ) b_spec ≤ (σ / a) * relativeReading (powerResponse a) b_spec`. -/
theorem relativeReading_power_le_div_mul (b_spec : SpectralBand 1) {a σ : ℝ}
    (ha : 0 < a) (haσ : a ≤ σ) :
    relativeReading (powerResponse ⟨σ, ha.trans_le haσ⟩) b_spec ≤
      (σ / a) * relativeReading (powerResponse ⟨a, ha⟩) b_spec := by
  let βσ : GibbsExponent := ⟨σ, ha.trans_le haσ⟩
  let βa : GibbsExponent := ⟨a, ha⟩
  have hreal := relativePartition_real b_spec βσ
  have hle := relativePartition_norm_le b_spec βa (z := (σ : ℂ))
    (by simp [βa]; exact haσ)
  dsimp only [βσ, βa] at hreal hle
  rw [hreal, Complex.norm_real, Real.norm_of_nonneg (relativeReading_bounds _ _).1,
    Complex.norm_real, Real.norm_of_nonneg (ha.trans_le haσ).le] at hle
  exact hle

/-- **Quantitative leftward polynomial/exponential amplification of `|ζ|` off Speiser disks:**
on any horizontal segment `[a, b] + iτ` (`0 < a ≤ b < 1 / 2`, `100 ≤ τ`) avoiding all Speiser disks
of strip zeros of `ξ`, `‖ζ(σ ± iτ)‖` grows leftward at least as
`‖ζ(b + iτ)‖ * exp(((log(τ / 2π)) / 2 - 1 / 10) * (b - σ))` (`0 < ‖ζ(b + iτ)‖`). -/
theorem norm_riemannZeta_ge_exp_of_not_mem_speiserDisk_segment
    {a b τ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1 / 2) (hτ : 100 ≤ τ)
    (hno : ∀ u ∈ Icc a b, ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      (ρ.re - 1 / 2) ^ 2 < (u - 1 / 2) ^ 2 + (τ - ρ.im) ^ 2) :
    0 < ‖riemannZeta ((b : ℂ) + (τ : ℂ) * Complex.I)‖ ∧
    ∀ σ ∈ Icc a b,
      ‖riemannZeta ((b : ℂ) + (τ : ℂ) * Complex.I)‖ *
          Real.exp ((Real.log (τ / (2 * Real.pi)) / 2 - 1 / 10) * (b - σ)) ≤
        ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ∧
      ‖riemannZeta ((b : ℂ) + (τ : ℂ) * Complex.I)‖ *
          Real.exp ((Real.log (τ / (2 * Real.pi)) / 2 - 1 / 10) * (b - σ)) ≤
        ‖riemannZeta ((σ : ℂ) - (τ : ℂ) * Complex.I)‖ := by
  have hb_ne0 : riemannZeta ((b : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 :=
    (_root_.RHTower.re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk
      (s := (b : ℂ) + (τ : ℂ) * Complex.I) (by simp; linarith) (by simp; linarith [hb])
      (by simp; exact hτ) (by simpa using hno b ⟨hab, le_rfl⟩)).1
  refine ⟨norm_pos_iff.mpr hb_ne0, fun σ hσ => ?_⟩
  set c : ℝ := Real.log (τ / (2 * Real.pi)) - 1 / 5
  let f : ℝ → ℝ := fun u => ‖riemannZeta ((u : ℂ) + (τ : ℂ) * Complex.I)‖ ^ (2 : ℕ)
  let g : ℝ → ℝ := fun u => Real.log (f u) + c * u
  have hne1 : ∀ u : ℝ, (u : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := fun u h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hf_deriv : ∀ u : ℝ, HasDerivAt f
      (2 * (deriv riemannZeta ((u : ℂ) + (τ : ℂ) * Complex.I) *
        conj (riemannZeta ((u : ℂ) + (τ : ℂ) * Complex.I))).re) u := by
    intro u
    have hlin : HasDerivAt (fun x : ℝ => (x : ℂ) + (τ : ℂ) * Complex.I) 1 u := by
      simpa using (hasDerivAt_id u).ofReal_comp.add_const ((τ : ℂ) * Complex.I)
    have h := (differentiableAt_riemannZeta (hne1 u)).hasDerivAt.scomp u hlin
    rw [one_smul] at h
    exact GaloisForLFunctions.HTGeometry.hasDerivAt_normSq_comp h
  have hf_pos : ∀ u ∈ Icc a b, 0 < f u := by
    intro u hu
    have hζ := (_root_.RHTower.re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk
      (s := (u : ℂ) + (τ : ℂ) * Complex.I) (by simp; linarith [hu.1]) (by simp; linarith [hu.2])
      (by simp; exact hτ) (by simpa using hno u hu)).1
    have hp := norm_pos_iff.mpr hζ
    dsimp only [f]; positivity
  have hg_deriv : ∀ u ∈ Icc a b, HasDerivAt g
      ((2 * (deriv riemannZeta ((u : ℂ) + (τ : ℂ) * Complex.I) *
        conj (riemannZeta ((u : ℂ) + (τ : ℂ) * Complex.I))).re) / f u + c) u := by
    intro u hu
    have hc_deriv : HasDerivAt (fun x : ℝ => c * x) c u := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul c
    exact ((hf_deriv u).log (hf_pos u hu).ne').add hc_deriv
  have hg_anti : AntitoneOn g (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun u hu => (hg_deriv u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hg_deriv u (Ioo_subset_Icc_self (by rwa [interior_Icc] at hu))).differentiableAt.differentiableWithinAt)
      ?_
    intro u hu
    rw [interior_Icc] at hu
    have hu_mem : u ∈ Icc a b := Ioo_subset_Icc_self hu
    rw [(hg_deriv u hu_mem).deriv]
    obtain ⟨hζ, hle⟩ := _root_.RHTower.re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk
      (s := (u : ℂ) + (τ : ℂ) * Complex.I) (by simp; linarith [hu.1]) (by simp; linarith [hu.2])
      (by simp; exact hτ) (by simpa using hno u hu_mem)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero] at hle
    set z := riemannZeta ((u : ℂ) + (τ : ℂ) * Complex.I)
    set z' := deriv riemannZeta ((u : ℂ) + (τ : ℂ) * Complex.I)
    have hid : (z' * conj z).re / f u = (logDeriv riemannZeta ((u : ℂ) + (τ : ℂ) * Complex.I)).re := by
      have hnorm : ((f u : ℝ) : ℂ) = conj z * z := by
        dsimp only [f]
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      have hval : z' * conj z = ((f u : ℝ) : ℂ) * (z' / z) := by
        rw [hnorm]; field_simp [hζ]
      have hfu_pos : 0 < f u := hf_pos u hu_mem
      rw [hval, Complex.re_ofReal_mul, mul_div_cancel_left₀ _ hfu_pos.ne', logDeriv_apply]
    have hdiv2 : (2 * (z' * conj z).re) / f u = 2 * ((z' * conj z).re / f u) := by ring
    rw [hdiv2, hid]
    dsimp only [c]
    linarith
  have hgb_le : g b ≤ g σ := hg_anti hσ ⟨hab, le_rfl⟩ hσ.2
  have hnorm_b_pos : 0 < ‖riemannZeta ((b : ℂ) + (τ : ℂ) * Complex.I)‖ := norm_pos_iff.mpr hb_ne0
  have hnorm_σ_pos : 0 < ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
    have hζ := (_root_.RHTower.re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk
      (s := (σ : ℂ) + (τ : ℂ) * Complex.I) (by simp; linarith [hσ.1]) (by simp; linarith [hσ.2])
      (by simp; exact hτ) (by simpa using hno σ hσ)).1
    exact norm_pos_iff.mpr hζ
  have hlog_le : Real.log ‖riemannZeta ((b : ℂ) + (τ : ℂ) * Complex.I)‖ +
      (Real.log (τ / (2 * Real.pi)) / 2 - 1 / 10) * (b - σ) ≤
      Real.log ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
    dsimp only [g, f] at hgb_le
    rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat] at hgb_le
    dsimp only [c] at hgb_le
    linarith
  have hexp_le := Real.exp_le_exp.mpr hlog_le
  rw [Real.exp_add, Real.exp_log hnorm_b_pos, Real.exp_log hnorm_σ_pos] at hexp_le
  have hconj : ‖riemannZeta ((σ : ℂ) - (τ : ℂ) * Complex.I)‖ =
      ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
    have hc : conj ((σ : ℂ) + (τ : ℂ) * Complex.I) = (σ : ℂ) - (τ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [← hc, riemannZeta_conj, Complex.norm_conj]
  exact ⟨hexp_le, hconj ▸ hexp_le⟩

/-- **Uniform single-wave horizontal certificate outside Speiser disks (valid on Speiser-shadowed
ordinates):** whenever `[a, b] + iτ` (`0 < a ≤ b < 1 / 2`, `100 ≤ τ`) avoids all Speiser disks of
strip zeros of `ξ`, for every `Λ > 0` there exists **one single pair `(v : MissingWave, K : ℕ)`**
(independent of `σ`) that **simultaneously** certifies **every** `σ ∈ [a, b]` on both lines `σ + iτ`
and `σ - iτ` in both the UV-capped fourth-power finite-eigenvalue test and the uncapped
`(2 / σ)`-power finite-eigenvalue test. -/
theorem exists_uniform_single_witness_of_not_mem_speiserDisk_segment
    {a b τ Λ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1 / 2) (hτ : 100 ≤ τ) (hΛ : 0 < Λ)
    (hno : ∀ u ∈ Icc a b, ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      (ρ.re - 1 / 2) ^ 2 < (u - 1 / 2) ^ 2 + (τ - ρ.im) ^ 2) :
    ∃ (v : MissingWave) (K : ℕ), ∀ σ ∈ Icc a b,
      let sPos : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I
      let sNeg : ℂ := (σ : ℂ) - (τ : ℂ) * Complex.I
      ∃ (hsPos : 0 < sPos.re) (hsNeg : 0 < sNeg.re),
        uvRegularRankOne sPos hsPos Λ v ∧
        uvRegularRankOne sNeg hsNeg Λ v ∧
        (uvZeroThresholdFactor sPos Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K sPos <
          ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖ ∧
        (uvZeroThresholdFactor sNeg Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K sNeg <
          ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖ ∧
        (chordZeroThresholdFactor sPos * lineLoss v.val) ^ (sPos.re / 2) + triadTailBound K sPos <
          ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖ ∧
        (chordZeroThresholdFactor sNeg * lineLoss v.val) ^ (sNeg.re / 2) + triadTailBound K sNeg <
          ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖ := by
  obtain ⟨hμ_pos, hseg_ge⟩ :=
    norm_riemannZeta_ge_exp_of_not_mem_speiserDisk_segment ha hab hb hτ hno
  set μ : ℝ := ‖riemannZeta ((b : ℂ) + (τ : ℂ) * Complex.I)‖
  set S_hi : ℝ := (τ + 1) / a
  have hS_hi_pos : 0 < S_hi := by dsimp only [S_hi]; positivity
  have hb_pos : 0 < b := ha.trans_le hab
  -- Choose target loss `δ ∈ (0, 1/4]` small enough for UV regularity and both capped/uncapped margins across `[a, b]`.
  set m_target : ℝ := μ / (4 * S_hi)
  have hm_pos : 0 < m_target := by dsimp only [m_target]; positivity
  set δ : ℝ := min (1 / 4) (min (((a / b) ^ 4 * (Λ / 4)) ^ ((1 : ℝ) / 3))
    (min (m_target / 2)
      (min (m_target ^ 4 / (2 * Λ)) ((min (1 / 2) m_target) ^ (2 / a) / 2))))
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    refine lt_min (by norm_num) (lt_min (Real.rpow_pos_of_pos (by positivity) _)
      (lt_min (by positivity)
        (lt_min (by positivity) (div_pos (Real.rpow_pos_of_pos (lt_min (by norm_num) hm_pos) _) two_pos))))
  have hδ_le_quarter : δ ≤ 1 / 4 := min_le_left _ _
  have hδ_lt_half : 2 * δ < 1 := by linarith
  have hδ_lt_m : δ < m_target := by
    have hd : δ ≤ m_target / 2 :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith
  have h2Λδ_le : (2 * Λ * δ) ^ (1 / 4 : ℝ) ≤ m_target := by
    have hd : δ ≤ m_target ^ 4 / (2 * Λ) :=
      (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hmul : 2 * Λ * δ ≤ m_target ^ 4 := by
      calc 2 * Λ * δ ≤ 2 * Λ * (m_target ^ 4 / (2 * Λ)) :=
            mul_le_mul_of_nonneg_left hd (by positivity)
        _ = m_target ^ 4 := by field_simp [hΛ.ne']
    calc (2 * Λ * δ) ^ (1 / 4 : ℝ) ≤ (m_target ^ 4) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hmul (by norm_num)
      _ = m_target := by
          rw [← Real.rpow_natCast m_target 4, ← Real.rpow_mul hm_pos.le,
            show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one]
  have h2δ_uncap_le : (2 * δ) ^ (a / 2) ≤ m_target := by
    set m1 : ℝ := min (1 / 2) m_target
    have hm1_pos : 0 < m1 := lt_min (by norm_num) hm_pos
    have hd : δ ≤ m1 ^ (2 / a) / 2 :=
      (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
    have hmul : 2 * δ ≤ m1 ^ (2 / a) := by linarith
    calc (2 * δ) ^ (a / 2) ≤ (m1 ^ (2 / a)) ^ (a / 2) :=
          Real.rpow_le_rpow (by positivity) hmul (by positivity)
      _ = m1 := by
          rw [← Real.rpow_mul hm1_pos.le, show (2 / a) * (a / 2) = 1 by field_simp [ha.ne'],
            Real.rpow_one]
      _ ≤ m_target := min_le_right _ _
  have hδ_lt_uv : δ < (a / b) * (Λ * (δ / 2)) ^ (1 / 4 : ℝ) := by
    have hd : δ ≤ ((a / b) ^ 4 * (Λ / 4)) ^ ((1 : ℝ) / 3) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hp3 : δ ^ 3 ≤ (a / b) ^ 4 * (Λ / 4) := by
      have h1 : δ ^ 3 ≤ (((a / b) ^ 4 * (Λ / 4)) ^ ((1 : ℝ) / 3)) ^ 3 :=
        pow_le_pow_left₀ hδ_pos.le hd 3
      have hrhs3 : (((a / b) ^ 4 * (Λ / 4)) ^ ((1 : ℝ) / 3)) ^ 3 = (a / b) ^ 4 * (Λ / 4) := by
        rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity),
          show ((1 : ℝ) / 3) * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
      rwa [hrhs3] at h1
    have hp4 : δ ^ 4 < ((a / b) * (Λ * (δ / 2)) ^ (1 / 4 : ℝ)) ^ 4 := by
      have hrhs : ((a / b) * (Λ * (δ / 2)) ^ (1 / 4 : ℝ)) ^ 4 = (a / b) ^ 4 * (Λ * (δ / 2)) := by
        rw [mul_pow, ← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity),
          show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]
      rw [hrhs]
      have hlt3 : δ ^ 3 < (a / b) ^ 4 * (Λ / 2) := by
        have hpos_ab : 0 < (a / b) ^ 4 * Λ := by positivity
        linarith
      calc δ ^ 4 = δ ^ 3 * δ := by ring
        _ < ((a / b) ^ 4 * (Λ / 2)) * δ := mul_lt_mul_of_pos_right hlt3 hδ_pos
        _ = (a / b) ^ 4 * (Λ * (δ / 2)) := by ring
    by_contra! hge
    exact hp4.not_ge (pow_le_pow_left₀ (by positivity) hge 4)
  -- Ground-attenuation limit profile `b₀` with loss `δ`.
  set τ₀ : ℝ := Real.sqrt (1 - δ)
  have hτ₀_pos : 0 < τ₀ := Real.sqrt_pos.mpr (by linarith)
  have hτ₀_lt1 : τ₀ < 1 := by
    have hsq : τ₀ ^ 2 < 1 ^ 2 := by rw [Real.sq_sqrt (by linarith)]; linarith
    exact (sq_lt_sq₀ hτ₀_pos.le zero_le_one).mp hsq
  have h1mτ₀2 : 1 - τ₀ ^ 2 = δ := by rw [Real.sq_sqrt (by linarith)]; ring
  obtain ⟨b₀, hb₀_cl, hb₀_eq⟩ := exists_ground_attenuation 0 ⟨τ₀, hτ₀_pos, hτ₀_lt1.le⟩
  let βa : GibbsExponent := ⟨a, ha⟩
  have hb₀_q : relativeReading quadraticResponse b₀ = δ := by
    have h := hb₀_eq (z := 2) (by norm_num)
    rw [partition_at_two, show (τ₀ : ℂ) ^ (2 : ℂ) = ((τ₀ ^ 2 : ℝ) : ℂ) by
      rw [Complex.ofReal_pow, ← Complex.cpow_natCast]; rfl,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, h1mτ₀2] at h
    exact Complex.ofReal_injective h
  have hb₀_a_le : relativeReading (powerResponse βa) b₀ ≤ δ := by
    have h := hb₀_eq (z := (a : ℂ)) (by simpa using ha)
    have hrp := relativePartition_real b₀ βa
    dsimp only [βa] at hrp
    rw [hrp, ← Complex.ofReal_cpow hτ₀_pos.le, ← Complex.ofReal_one, ← Complex.ofReal_sub] at h
    have hval : relativeReading (powerResponse βa) b₀ = 1 - τ₀ ^ a := Complex.ofReal_injective h
    rw [hval, ← h1mτ₀2]
    have hle : τ₀ ^ (2 : ℝ) ≤ τ₀ ^ a :=
      Real.rpow_le_rpow_of_exponent_ge hτ₀_pos hτ₀_lt1.le (by linarith)
    rw [Real.rpow_two] at hle
    linarith
  set r_cap : ℝ := min ((a / b) * (Λ * (δ / 2)) ^ (1 / 4 : ℝ)) m_target
  have hb₀_r_lt : relativeReading (powerResponse βa) b₀ < r_cap :=
    hb₀_a_le.trans_lt (lt_min hδ_lt_uv hδ_lt_m)
  let U : Set (SpectralBand 1) :=
    {c | δ / 2 < relativeReading quadraticResponse c ∧
      relativeReading quadraticResponse c < 2 * δ ∧
      relativeReading (powerResponse βa) c < r_cap}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const (continuous_relativeReading quadraticResponse 1)).inter
      ((isOpen_lt (continuous_relativeReading quadraticResponse 1) continuous_const).inter
        (isOpen_lt (continuous_relativeReading (powerResponse βa) 1) continuous_const))
  have hb₀_in_U : b₀ ∈ U := by
    refine ⟨?_, ?_, hb₀_r_lt⟩ <;> rw [hb₀_q] <;> linarith
  obtain ⟨_, hb_U, ⟨P, hd, hc_proj, rfl⟩⟩ := mem_closure_iff.mp hb₀_cl U hU_open hb₀_in_U
  obtain ⟨w_vec, hw_ne, rfl⟩ := (missingDimension_one_iff P).mp hd
  let v : MissingWave := ⟨w_vec, (nonzero_line_conserves_iff w_vec).mp ⟨hw_ne, hc_proj⟩⟩
  have hspec : physicalSpectrum (omitLine w_vec) hd hc_proj = missingWaveSpectrum v := rfl
  rw [hspec, Set.mem_setOf_eq, relativeReading_quadratic_missingWaveSpectrum] at hb_U
  obtain ⟨hL_lo, hL_hi, hRa_lt⟩ := hb_U
  -- Choose a single prefix length `K : ℕ` uniformly controlling `triadTailBound` across `[a, b] ± iτ`.
  have h2a_pos : 0 < (2 : ℝ) ^ a - 1 := sub_pos.mpr (Real.one_lt_rpow one_lt_two ha)
  have h2b_den : 0 < (2 : ℝ) ^ (1 - b) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow one_lt_two (by linarith))
  set gap_u : ℝ := ((2 : ℝ) ^ a - 1) * (μ / 4)
  have hgap_pos : 0 < gap_u := by dsimp only [gap_u]; positivity
  set C_tail : ℝ := (((2 : ℝ) ^ b + 1) / ((2 : ℝ) ^ (1 - b) - 1)) * (4 * S_hi)
  have hC_tail_pos : 0 < C_tail := by dsimp only [C_tail]; positivity
  have htend_occ : Tendsto (fun K : ℕ => C_tail * occupationWeight (2 * K) ^ a) atTop (𝓝 0) := by
    have h2K : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
      tendsto_atTop_mono (fun K => by omega : ∀ K : ℕ, K ≤ 2 * K) tendsto_natCast_atTop_atTop
    have h0 := ((occupationWeight_tendsto.comp h2K).rpow_const (Or.inr ha.le)).const_mul C_tail
    simpa only [Function.comp_apply, Real.zero_rpow ha.ne', mul_zero] using h0
  obtain ⟨K, hK_lt⟩ := (htend_occ.eventually (gt_mem_nhds hgap_pos)).exists
  refine ⟨v, K, fun σ hσ => ?_⟩
  -- Shared verifier at any `s` with `s.re = σ ∈ [a, b]`, `|s.im| = τ`, and `μ ≤ ‖ζ(s)‖`.
  have hpoint : ∀ s : ℂ, ∀ hs0 : 0 < s.re, s.re = σ → |s.im| = τ → μ ≤ ‖riemannZeta s‖ →
      uvRegularRankOne s hs0 Λ v ∧
      (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ ∧
      (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ := by
    intro s hs0 hs_re hs_im hζ_ge
    have hs1 : s.re < 1 := by rw [hs_re]; linarith [hσ.2]
    have hs_ne1 : s ≠ 1 := fun h => by
      have := congrArg Complex.re h; rw [hs_re] at this; linarith [hσ.2]
    have hnorm_s : ‖s‖ ≤ τ + 1 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      rw [hs_re, abs_of_pos (ha.trans_le hσ.1), hs_im] at h
      linarith [hσ.2]
    have hratio_le : ‖s‖ / σ ≤ S_hi := by
      dsimp only [S_hi]
      calc ‖s‖ / σ ≤ (τ + 1) / σ := div_le_div_of_nonneg_right hnorm_s (ha.trans_le hσ.1).le
        _ ≤ (τ + 1) / a := div_le_div_of_nonneg_left (by linarith) ha hσ.1
    have hratio_a_le : ‖s‖ / a ≤ S_hi :=
      div_le_div_of_nonneg_right hnorm_s ha.le
    -- 1. `uvRegularRankOne`
    have huv : uvRegularRankOne s hs0 Λ v := by
      unfold uvRegularRankOne
      have hβ_eq : (⟨s.re, hs0⟩ : GibbsExponent) = ⟨σ, ha.trans_le hσ.1⟩ := Subtype.ext hs_re
      rw [hβ_eq]
      have hpow_cmp := relativeReading_power_le_div_mul (missingWaveSpectrum v) ha hσ.1
      have hdiv_le : σ / a ≤ b / a := div_le_div_of_nonneg_right hσ.2 ha.le
      have hr_uv : r_cap ≤ (a / b) * (Λ * (δ / 2)) ^ (1 / 4 : ℝ) := min_le_left _ _
      have hRσ_le : relativeReading (powerResponse ⟨σ, ha.trans_le hσ.1⟩) (missingWaveSpectrum v) ≤
          (Λ * (δ / 2)) ^ (1 / 4 : ℝ) := by
        calc relativeReading (powerResponse ⟨σ, ha.trans_le hσ.1⟩) (missingWaveSpectrum v)
            ≤ (σ / a) * relativeReading (powerResponse βa) (missingWaveSpectrum v) := hpow_cmp
          _ ≤ (b / a) * r_cap := mul_le_mul hdiv_le hRa_lt.le
              (relativeReading_bounds _ _).1 (by positivity)
          _ ≤ (b / a) * ((a / b) * (Λ * (δ / 2)) ^ (1 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_left hr_uv (by positivity)
          _ = (Λ * (δ / 2)) ^ (1 / 4 : ℝ) := by field_simp [ha.ne', hb_pos.ne']
      have hp4 := pow_le_pow_left₀ (relativeReading_bounds _ _).1 hRσ_le 4
      rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity),
        show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one] at hp4
      exact hp4.trans (mul_le_mul_of_nonneg_left hL_lo.le hΛ.le)
    -- 2. Margin on `‖jointSurvivingPartition‖`
    have hrp_le : ‖relativePartition (missingWaveSpectrum v) s‖ ≤ μ / 4 := by
      have h1 := relativePartition_norm_le (missingWaveSpectrum v) βa
        (by simp [βa, hs_re]; exact hσ.1)
      dsimp only [βa] at h1
      have hr_m : r_cap ≤ m_target := min_le_right _ _
      calc ‖relativePartition (missingWaveSpectrum v) s‖
          ≤ (‖s‖ / a) * relativeReading (powerResponse βa) (missingWaveSpectrum v) := h1
        _ ≤ S_hi * m_target := mul_le_mul hratio_a_le (hRa_lt.le.trans hr_m)
            (relativeReading_bounds _ _).1 hS_hi_pos.le
        _ = μ / 4 := by dsimp only [m_target]; field_simp [hS_hi_pos.ne']
    have h2_lo : (2 : ℝ) ^ a - 1 ≤ ‖(2 : ℂ) ^ s - 1‖ := by
      have h2s : ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ σ := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
          Complex.norm_cpow_eq_rpow_re_of_pos two_pos, hs_re]
      have h := norm_sub_norm_le ((2 : ℂ) ^ s) 1
      rw [h2s, norm_one] at h
      have hmono : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le one_le_two hσ.1
      linarith
    have hjsp_ge : ‖(2 : ℂ) ^ s - 1‖ * (μ / 4) + 2 * gap_u ≤
        ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ := by
      rw [jointSurvivingPartition_eq_continued_sub, continued_eq_zeta s hs_ne1, ← mul_sub, norm_mul]
      have hdiff : (3 / 4) * μ ≤ ‖riemannZeta s - relativePartition (missingWaveSpectrum v) s‖ := by
        have h := norm_sub_norm_le (riemannZeta s) (relativePartition (missingWaveSpectrum v) s)
        linarith
      have hmul := mul_le_mul_of_nonneg_left hdiff (norm_nonneg ((2 : ℂ) ^ s - 1))
      have hgap_le : 2 * gap_u ≤ ‖(2 : ℂ) ^ s - 1‖ * (μ / 2) := by
        dsimp only [gap_u]
        have hm := mul_le_mul_of_nonneg_right h2_lo (by positivity : 0 ≤ μ / 2)
        linarith
      linarith
    -- 3. Tail bound `< gap_u`
    have htail_lt : triadTailBound K s < gap_u := by
      have hfr := factor_ratio_le hs0 hs1
      rw [hs_re] at hfr
      have hnum : (2 : ℝ) ^ σ + 1 ≤ (2 : ℝ) ^ b + 1 := by
        linarith [Real.rpow_le_rpow_of_exponent_le one_le_two hσ.2]
      have hden : (2 : ℝ) ^ (1 - b) - 1 ≤ (2 : ℝ) ^ (1 - σ) - 1 := by
        linarith [Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith [hσ.2] : 1 - b ≤ 1 - σ)]
      have hfr_b : ‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖ ≤
          ((2 : ℝ) ^ b + 1) / ((2 : ℝ) ^ (1 - b) - 1) := by
        refine hfr.trans ?_
        calc ((2 : ℝ) ^ σ + 1) / ((2 : ℝ) ^ (1 - σ) - 1)
            ≤ ((2 : ℝ) ^ b + 1) / ((2 : ℝ) ^ (1 - σ) - 1) :=
              div_le_div_of_nonneg_right hnum (by linarith)
          _ ≤ ((2 : ℝ) ^ b + 1) / ((2 : ℝ) ^ (1 - b) - 1) :=
              div_le_div_of_nonneg_left (by positivity) h2b_den hden
      have hocc_le : occupationWeight (2 * K) ^ σ ≤ occupationWeight (2 * K) ^ a :=
        Real.rpow_le_rpow_of_exponent_ge (occupationWeight_pos _) (occupation_in_unit _).2 hσ.1
      have hmid : (4 * ‖s‖ / σ) * occupationWeight (2 * K) ^ σ ≤
          (4 * S_hi) * occupationWeight (2 * K) ^ a := by
        rw [show 4 * ‖s‖ / σ = 4 * (‖s‖ / σ) by ring]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hratio_le (by norm_num)) hocc_le
          (Real.rpow_nonneg (occupationWeight_pos _).le _) (by positivity)
      have htb_le : triadTailBound K s ≤ C_tail * occupationWeight (2 * K) ^ a := by
        unfold triadTailBound
        rw [hs_re]
        calc (‖(2 : ℂ) ^ s - 1‖ / ‖1 - (2 : ℂ) ^ (1 - s)‖) *
                ((4 * ‖s‖ / σ) * occupationWeight (2 * K) ^ σ)
            ≤ (((2 : ℝ) ^ b + 1) / ((2 : ℝ) ^ (1 - b) - 1)) *
                ((4 * S_hi) * occupationWeight (2 * K) ^ a) :=
              mul_le_mul hfr_b hmid (by positivity) (by positivity)
          _ = C_tail * occupationWeight (2 * K) ^ a := by dsimp only [C_tail]; ring
      exact htb_le.trans_lt hK_lt
    have happrox := norm_jointSurviving_sub_finiteTriadReading_le
      (missingWaveSpectrum v) K hs0 hs1.ne
    have htri : ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ≤
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ +
          ‖jointSurvivingPartition (missingWaveSpectrum v) s -
            finiteTriadReading (missingWaveSpectrum v) K s‖ := by
      have h := norm_add_le (finiteTriadReading (missingWaveSpectrum v) K s)
        (jointSurvivingPartition (missingWaveSpectrum v) s -
          finiteTriadReading (missingWaveSpectrum v) K s)
      simpa only [add_sub_cancel] using h
    -- 4. Capped & uncapped threshold bounds `≤ ‖2^s - 1‖ * (μ / 4)`
    have hcap_le : (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) ≤
        ‖(2 : ℂ) ^ s - 1‖ * (μ / 4) := by
      have hbase_nn : 0 ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) := by positivity
      have hll_pos : 0 < lineLoss v.val := (line_loss_bounds v).1
      have hrew : (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) =
          ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) * (Λ * lineLoss v.val) ^ (1 / 4 : ℝ) := by
        unfold uvZeroThresholdFactor
        rw [hs_re, show ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / σ) ^ 4 * Λ * lineLoss v.val =
          (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) ^ 4 * (Λ * lineLoss v.val) by ring,
          Real.mul_rpow (pow_nonneg hbase_nn 4) (by positivity),
          ← Real.rpow_natCast (‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ)) 4,
          ← Real.rpow_mul hbase_nn, show (4 : ℕ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one]
      rw [hrew]
      have hr4_le : (Λ * lineLoss v.val) ^ (1 / 4 : ℝ) ≤ m_target := by
        have h1 : Λ * lineLoss v.val ≤ 2 * Λ * δ := by
          have hm := mul_le_mul_of_nonneg_left hL_hi.le hΛ.le
          linarith
        exact (Real.rpow_le_rpow (by positivity) h1 (by norm_num)).trans h2Λδ_le
      calc ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) * (Λ * lineLoss v.val) ^ (1 / 4 : ℝ)
          ≤ ‖(2 : ℂ) ^ s - 1‖ * S_hi * m_target := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hratio_le hr4_le (by positivity) hS_hi_pos.le) (norm_nonneg _)
        _ = ‖(2 : ℂ) ^ s - 1‖ * (μ / 4) := by
            dsimp only [m_target]; field_simp [hS_hi_pos.ne']
    have huncap_le : (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) ≤
        ‖(2 : ℂ) ^ s - 1‖ * (μ / 4) := by
      have hbase_nn : 0 ≤ ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) := by positivity
      have hll_pos : 0 < lineLoss v.val := (line_loss_bounds v).1
      have hrew : (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) =
          ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) * lineLoss v.val ^ (σ / 2) := by
        unfold chordZeroThresholdFactor
        rw [hs_re, Real.mul_rpow (Real.rpow_nonneg hbase_nn _) hll_pos.le,
          ← Real.rpow_mul hbase_nn,
          show (2 / σ) * (σ / 2) = 1 by field_simp [(ha.trans_le hσ.1).ne'], Real.rpow_one]
      rw [hrew]
      have hll_pow_le : lineLoss v.val ^ (σ / 2) ≤ m_target := by
        have h1 : lineLoss v.val ^ (σ / 2) ≤ (2 * δ) ^ (σ / 2) :=
          Real.rpow_le_rpow hll_pos.le hL_hi.le (by linarith [ha, hσ.1])
        have h2 : (2 * δ) ^ (σ / 2) ≤ (2 * δ) ^ (a / 2) :=
          Real.rpow_le_rpow_of_exponent_ge (by positivity) hδ_lt_half.le (by linarith [hσ.1])
        exact (h1.trans h2).trans h2δ_uncap_le
      calc ‖(2 : ℂ) ^ s - 1‖ * (‖s‖ / σ) * lineLoss v.val ^ (σ / 2)
          ≤ ‖(2 : ℂ) ^ s - 1‖ * S_hi * m_target := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hratio_le hll_pow_le (by positivity) hS_hi_pos.le) (norm_nonneg _)
        _ = ‖(2 : ℂ) ^ s - 1‖ * (μ / 4) := by
            dsimp only [m_target]; field_simp [hS_hi_pos.ne']
    refine ⟨huv, ?_, ?_⟩ <;> linarith
  -- Apply `hpoint` to both `sPos = σ + iτ` and `sNeg = σ - iτ`.
  set sPos : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I
  set sNeg : ℂ := (σ : ℂ) - (τ : ℂ) * Complex.I
  have hsPos_re : sPos.re = σ := by simp [sPos]
  have hsNeg_re : sNeg.re = σ := by simp [sNeg]
  have hsPos0 : 0 < sPos.re := hsPos_re ▸ ha.trans_le hσ.1
  have hsNeg0 : 0 < sNeg.re := hsNeg_re ▸ ha.trans_le hσ.1
  have hsPos_im : |sPos.im| = τ := by simp [sPos, abs_of_pos (by linarith : 0 < τ)]
  have hsNeg_im : |sNeg.im| = τ := by simp [sNeg, abs_of_pos (by linarith : 0 < τ)]
  have hexp_ge1 : 1 ≤ Real.exp ((Real.log (τ / (2 * Real.pi)) / 2 - 1 / 10) * (b - σ)) := by
    apply Real.one_le_exp
    have h5 := _root_.RHTower.one_fifth_lt_log_div_two_pi hτ
    exact mul_nonneg (by linarith) (sub_nonneg.mpr hσ.2)
  have hμ_le_pos : μ ≤ ‖riemannZeta sPos‖ := by
    calc μ = μ * 1 := (mul_one μ).symm
      _ ≤ μ * Real.exp ((Real.log (τ / (2 * Real.pi)) / 2 - 1 / 10) * (b - σ)) :=
          mul_le_mul_of_nonneg_left hexp_ge1 hμ_pos.le
      _ ≤ ‖riemannZeta sPos‖ := (hseg_ge σ hσ).1
  have hμ_le_neg : μ ≤ ‖riemannZeta sNeg‖ := by
    calc μ = μ * 1 := (mul_one μ).symm
      _ ≤ μ * Real.exp ((Real.log (τ / (2 * Real.pi)) / 2 - 1 / 10) * (b - σ)) :=
          mul_le_mul_of_nonneg_left hexp_ge1 hμ_pos.le
      _ ≤ ‖riemannZeta sNeg‖ := (hseg_ge σ hσ).2
  obtain ⟨huvP, hcapP, huncapP⟩ := hpoint sPos hsPos0 hsPos_re hsPos_im hμ_le_pos
  obtain ⟨huvN, hcapN, huncapN⟩ := hpoint sNeg hsNeg0 hsNeg_re hsNeg_im hμ_le_neg
  exact ⟨hsPos0, hsNeg0, huvP, huvN, hcapP, hcapN, huncapP, huncapN⟩

/-- **75% clean-height window density for uniform single-wave horizontal certificates above `84.5`:**
upgrades `eventually_volume_clean_zero_exception_heights_window_ge` from `(14 / 25) H - 3` (`56%`)
to `(3 / 4) H - 3` (`75%`) of every `[T + 3 / 2, T + H - 3 / 2]` (`T^{24 / 25} ≤ H ≤ T`), and
certifies every compact `[a, b] ⊂ (0, 1 / 2)` on each clean height `±γ` with **one single `(v, K)`**. -/
theorem eventually_volume_clean_zero_exception_heights_window_ge_three_quarters :
    ∀ᶠ T : ℝ in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (3 / 4 * H - 3) ≤
        volume {γ : ℝ | γ ∈ Icc (T + 3 / 2) (T + H - 3 / 2) ∧
          ∀ {a b Λ : ℝ}, 0 < a → a ≤ b → b < 1 / 2 → 0 < Λ →
            ∃ (v : MissingWave) (K : ℕ), ∀ σ ∈ Icc a b,
              let sPos : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
              let sNeg : ℂ := (σ : ℂ) - (γ : ℂ) * Complex.I
              169 / 2 < |sPos.im| ∧ 169 / 2 < |sNeg.im| ∧
              ∃ (hsPos : 0 < sPos.re) (hsNeg : 0 < sNeg.re),
                uvRegularRankOne sPos hsPos Λ v ∧
                uvRegularRankOne sNeg hsNeg Λ v ∧
                (uvZeroThresholdFactor sPos Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K sPos <
                  ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖ ∧
                (uvZeroThresholdFactor sNeg Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K sNeg <
                  ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖ ∧
                (chordZeroThresholdFactor sPos * lineLoss v.val) ^ (sPos.re / 2) + triadTailBound K sPos <
                  ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖ ∧
                (chordZeroThresholdFactor sNeg * lineLoss v.val) ^ (sNeg.re / 2) + triadTailBound K sNeg <
                  ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖} := by
  filter_upwards [_root_.RHTower.eventually_volume_speiserUnshadowed_window_ge_upper,
    eventually_ge_atTop (100 : ℝ)] with T hvol hT100 H hH_lo hH_hi
  refine (hvol H hH_lo hH_hi).trans (measure_mono ?_)
  rintro γ ⟨hγ_mem, hu⟩
  have hγ100 : 100 ≤ γ := by linarith [hγ_mem.1]
  refine ⟨hγ_mem, fun {a b Λ} ha hab hb hΛ => ?_⟩
  have hno : ∀ u ∈ Icc a b, ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      (ρ.re - 1 / 2) ^ 2 < (u - 1 / 2) ^ 2 + (γ - ρ.im) ^ 2 := by
    intro u hu_mem ρ hρ _ _
    have h1 := hu ρ hρ
    have h2 : 0 < (u - 1 / 2) ^ 2 := sq_pos_of_ne_zero (by linarith [hu_mem.2])
    linarith
  obtain ⟨v, K, hvK⟩ :=
    exists_uniform_single_witness_of_not_mem_speiserDisk_segment ha hab hb hγ100 hΛ hno
  refine ⟨v, K, fun σ hσ => ?_⟩
  have him_pos : 169 / 2 < |((σ : ℂ) + (γ : ℂ) * Complex.I).im| := by
    simp [abs_of_pos (by linarith : 0 < γ)]; linarith
  have him_neg : 169 / 2 < |((σ : ℂ) - (γ : ℂ) * Complex.I).im| := by
    simp [abs_of_pos (by linarith : 0 < γ)]; linarith
  exact ⟨him_pos, him_neg, hvK σ hσ⟩

/-- **Exponential shadow decay of outer-segment single-wave certificates across Speiser-shadowed
ordinates:** on admissible windows `[T₁ + 1 / 2, T₂ - 1 / 2]` (`T₁ ∈ (U / 4, U / 4 + 1)`,
`T₂ ∈ (U / 2 - 1, U / 2)`), for every `2 ≤ κ ≤ log U / 2 - 2`, outside an exponentially small height
set of measure `≤ A'(T₂ - T₁) exp(-κ / 2400) + K'(log U)^2` (covering arbitrarily close to 100% of
Speiser-shadowed ordinates), **every** ordinate `γ` in the complement admits **one single `(v, K)`**
simultaneously certifying the entire outer segment `[a, 1 / 2 - κ / log U] ± iγ` (for every
`0 < a ≤ 1 / 2 - κ / log U`, including `a = 3001 / 24000` once `κ / log U ≤ 8999 / 24000`). -/
theorem exists_speiserShadow_exponential_density_uniform_witnesses :
    ∃ A' K' : ℝ, 0 ≤ A' ∧ 0 ≤ K' ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ κ : ℝ, 2 ≤ κ → κ ≤ Real.log U / 2 - 2 →
          ∃ E ⊆ Icc (T₁ + 1 / 2) (T₂ - 1 / 2),
            volume E ≤ ENNReal.ofReal (A' * (T₂ - T₁) * Real.exp (-(κ / 2400)) +
              K' * Real.log U ^ 2) ∧
            ∀ γ ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) \ E,
              ∀ {a Λ : ℝ}, 0 < a → a ≤ 1 / 2 - κ / Real.log U → 0 < Λ →
                ∃ (v : MissingWave) (K : ℕ), ∀ σ ∈ Icc a (1 / 2 - κ / Real.log U),
                  let sPos : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
                  let sNeg : ℂ := (σ : ℂ) - (γ : ℂ) * Complex.I
                  169 / 2 < |sPos.im| ∧ 169 / 2 < |sNeg.im| ∧
                  ∃ (hsPos : 0 < sPos.re) (hsNeg : 0 < sNeg.re),
                    uvRegularRankOne sPos hsPos Λ v ∧
                    uvRegularRankOne sNeg hsNeg Λ v ∧
                    (uvZeroThresholdFactor sPos Λ * lineLoss v.val) ^ (1 / 4 : ℝ) +
                        triadTailBound K sPos <
                      ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖ ∧
                    (uvZeroThresholdFactor sNeg Λ * lineLoss v.val) ^ (1 / 4 : ℝ) +
                        triadTailBound K sNeg <
                      ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖ ∧
                    (chordZeroThresholdFactor sPos * lineLoss v.val) ^ (sPos.re / 2) +
                        triadTailBound K sPos <
                      ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖ ∧
                    (chordZeroThresholdFactor sNeg * lineLoss v.val) ^ (sNeg.re / 2) +
                        triadTailBound K sNeg <
                      ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖ := by
  obtain ⟨A', K', hA', hK', hev⟩ := _root_.RHTower.exists_speiserShadow_exponential_density
  refine ⟨A', K', hA', hK', ?_⟩
  filter_upwards [hev, eventually_ge_atTop (400 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (8 : ℝ)] with U hU hU400 hL8
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun κ hκ2 hκ_hi => ?_⟩
  set L : ℝ := Real.log U
  have hL_pos : 0 < L := by linarith
  have hκL_pos : 0 < κ / L := div_pos (by linarith) hL_pos
  set E : Set ℝ := {t : ℝ | t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) ∧ ∃ ρ : ℂ, _root_.RHTower.xi ρ = 0 ∧
      κ / L ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|}
  refine ⟨E, fun _ ht => ht.1, hbound κ hκ2 hκ_hi, fun γ hγ {a Λ} ha hab hΛ => ?_⟩
  have hγ_mem : γ ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) := hγ.1
  have hγ_not_E : γ ∉ E := hγ.2
  have hγ100 : 100 ≤ γ := by linarith [hT₁.1, hγ_mem.1]
  have hb_lt : 1 / 2 - κ / L < 1 / 2 := by linarith
  have hno : ∀ u ∈ Icc a (1 / 2 - κ / L), ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 →
      0 < ρ.re → ρ.re < 1 → (ρ.re - 1 / 2) ^ 2 < (u - 1 / 2) ^ 2 + (γ - ρ.im) ^ 2 := by
    intro u hu_mem ρ hρ _ _
    rcases lt_or_ge |ρ.re - 1 / 2| (κ / L) with hsmall | hlarge
    · have hu_abs : κ / L ≤ |u - 1 / 2| := by
        rw [abs_of_neg (by linarith [hu_mem.2])]; linarith [hu_mem.2]
      have hlt_abs : |ρ.re - 1 / 2| < |u - 1 / 2| := hsmall.trans_le hu_abs
      have hsq : (ρ.re - 1 / 2) ^ 2 < (u - 1 / 2) ^ 2 := by
        have h := sq_lt_sq.mpr hlt_abs
        simpa only [sq_abs] using h
      nlinarith [sq_nonneg (γ - ρ.im)]
    · have hfar : |ρ.re - 1 / 2| < |γ - ρ.im| := by
        by_contra! hle
        exact hγ_not_E ⟨hγ_mem, ρ, hρ, hlarge, hle⟩
      have hsq : (ρ.re - 1 / 2) ^ 2 < (γ - ρ.im) ^ 2 := by
        have h := sq_lt_sq.mpr hfar
        simpa only [sq_abs] using h
      nlinarith [sq_nonneg (u - 1 / 2)]
  obtain ⟨v, K, hvK⟩ :=
    exists_uniform_single_witness_of_not_mem_speiserDisk_segment ha hab hb_lt hγ100 hΛ hno
  refine ⟨v, K, fun σ hσ => ?_⟩
  have him_pos : 169 / 2 < |((σ : ℂ) + (γ : ℂ) * Complex.I).im| := by
    simp [abs_of_pos (by linarith : 0 < γ)]; linarith
  have him_neg : 169 / 2 < |((σ : ℂ) - (γ : ℂ) * Complex.I).im| := by
    simp [abs_of_pos (by linarith : 0 < γ)]; linarith
  exact ⟨him_pos, him_neg, hvK σ hσ⟩

/-- **Zero-exception all-ordinate Littlewood-strip uniform single-wave certificates (including deep
Speiser-shadowed ordinates):** there exist `c > 0` and `T₀ ≥ 100` such that at **every** ordinate
`γ ≥ T₀` (with **zero** exceptional ordinates), every compact subsegment
`[a, b] ⊂ (0, c * log(log γ) / log γ)` admits **one single `(v, K)`** simultaneously certifying
`[a, b] ± iγ` in both the capped and uncapped finite-eigenvalue tests. -/
theorem exists_all_ordinates_littlewood_strip_uniform_witness :
    ∃ c T₀ : ℝ, 0 < c ∧ 100 ≤ T₀ ∧ ∀ γ : ℝ, T₀ ≤ γ →
      ∀ {a b Λ : ℝ}, 0 < a → a ≤ b → b < c * Real.log (Real.log γ) / Real.log γ → 0 < Λ →
        ∃ (v : MissingWave) (K : ℕ), ∀ σ ∈ Icc a b,
          let sPos : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
          let sNeg : ℂ := (σ : ℂ) - (γ : ℂ) * Complex.I
          169 / 2 < |sPos.im| ∧ 169 / 2 < |sNeg.im| ∧
          ∃ (hsPos : 0 < sPos.re) (hsNeg : 0 < sNeg.re),
            uvRegularRankOne sPos hsPos Λ v ∧
            uvRegularRankOne sNeg hsNeg Λ v ∧
            (uvZeroThresholdFactor sPos Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K sPos <
              ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖ ∧
            (uvZeroThresholdFactor sNeg Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K sNeg <
              ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖ ∧
            (chordZeroThresholdFactor sPos * lineLoss v.val) ^ (sPos.re / 2) + triadTailBound K sPos <
              ‖finiteTriadReading (missingWaveSpectrum v) K sPos‖ ∧
            (chordZeroThresholdFactor sNeg * lineLoss v.val) ^ (sNeg.re / 2) + triadTailBound K sNeg <
              ‖finiteTriadReading (missingWaveSpectrum v) K sNeg‖ := by
  obtain ⟨c, T, hc, _, hreg⟩ := _root_.RHTower.Sieve.exists_littlewood_zero_free_region_abs
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp
    _root_.RHTower.eventually_half_loglog_le_loglog_half
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop ((c + 4) ^ 2 + 16 : ℝ))
  set T₀ : ℝ := max (max (T + 1) (T₁ + 1)) (max T₂ 1000)
  have hT₀_100 : 100 ≤ T₀ := le_trans (by norm_num : (100 : ℝ) ≤ 1000)
    ((le_max_right T₂ 1000).trans (le_max_right _ _))
  refine ⟨c / 4, T₀, by positivity, hT₀_100, fun γ hγ {a b Λ} ha hab hb_lt hΛ => ?_⟩
  have hγT : T + 1 ≤ γ := ((le_max_left _ _).trans (le_max_left _ _)).trans hγ
  have hγT₁ : T₁ + 1 ≤ γ := ((le_max_right _ _).trans (le_max_left _ _)).trans hγ
  have hγT₂ : T₂ ≤ γ := ((le_max_left _ _).trans (le_max_right _ _)).trans hγ
  have hγ1000 : 1000 ≤ γ := ((le_max_right _ _).trans (le_max_right _ _)).trans hγ
  have hlogγ : (c + 4) ^ 2 + 16 ≤ Real.log γ := hT₂ γ hγT₂
  have hlogγ_pos : 0 < Real.log γ := by nlinarith [sq_nonneg (c + 4)]
  have hloglog_pos : 0 < Real.log (Real.log γ) := Real.log_pos (by nlinarith [sq_nonneg (c + 4)])
  have hb_half : b < 1 / 2 := by
    set L : ℝ := Real.log γ
    have hsqL : c + 4 ≤ Real.sqrt L := (Real.le_sqrt (by linarith) hlogγ_pos.le).mpr (by nlinarith)
    have hLL : Real.log L ≤ 2 * Real.sqrt L := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hlogγ_pos)
      rw [Real.log_sqrt hlogγ_pos.le] at h; linarith
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hlogγ_pos.le
    have hkey : c / 4 * Real.log L / L < 1 / 2 := by
      rw [div_lt_iff₀ hlogγ_pos]
      have h1 : c / 4 * Real.log L ≤ c / 4 * (2 * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hLL (by positivity)
      nlinarith [Real.sqrt_nonneg L]
    linarith
  have hno : ∀ u ∈ Icc a b, ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      (ρ.re - 1 / 2) ^ 2 < (u - 1 / 2) ^ 2 + (γ - ρ.im) ^ 2 := by
    intro u hu_mem ρ hρ hρ0 hρ1
    by_contra! hdisk
    have hu_lt : u < c / 4 * Real.log (Real.log γ) / Real.log γ := hu_mem.2.trans_lt hb_lt
    have hu_half : u < 1 / 2 := hu_mem.2.trans_lt hb_half
    have hsq : (u - 1 / 2) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by nlinarith [sq_nonneg (γ - ρ.im)]
    have hγ_diff : |γ - ρ.im| < 1 / 2 := by
      have : (ρ.re - 1 / 2) ^ 2 < 1 / 4 := by nlinarith
      have hq : (γ - ρ.im) ^ 2 < 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
      rw [← sq_lt_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
    obtain ⟨hγ1, hγ2⟩ := abs_lt.mp hγ_diff
    have hρ_im_pos : 0 < ρ.im := by linarith
    have habsρ : |ρ.im| = ρ.im := abs_of_pos hρ_im_pos
    have hdist : 1 / 2 - u ≤ |ρ.re - 1 / 2| := by
      have := sq_le_sq.mp hsq
      rw [abs_of_neg (by linarith : u - 1 / 2 < 0)] at this
      linarith
    have hwidth : c / 4 * Real.log (Real.log γ) / Real.log γ ≤
        c * Real.log (Real.log |ρ.im|) / Real.log |ρ.im| := by
      rw [habsρ]
      have hlo : γ / 2 ≤ ρ.im := by linarith
      have hhi : ρ.im ≤ 2 * γ := by linarith
      have hlogρ_le : Real.log ρ.im ≤ 2 * Real.log γ := by
        have h1 := Real.log_le_log hρ_im_pos hhi
        rw [Real.log_mul (by norm_num) (by linarith)] at h1
        have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
        have hlg16 : 16 ≤ Real.log γ := by nlinarith [sq_nonneg (c + 4)]
        linarith
      have hlogρ_pos : 0 < Real.log ρ.im := Real.log_pos (by linarith)
      have hll : Real.log (Real.log γ) / 2 ≤ Real.log (Real.log ρ.im) := by
        have h1 := hT₁ γ (by linarith)
        have h2 : Real.log (Real.log (γ / 2)) ≤ Real.log (Real.log ρ.im) :=
          Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) hlo)
        linarith
      rw [div_le_div_iff₀ hlogγ_pos hlogρ_pos]
      nlinarith [mul_le_mul_of_nonneg_left hll hc.le,
        mul_le_mul_of_nonneg_left hlogρ_le (mul_nonneg (by positivity : 0 ≤ c / 4) hloglog_pos.le)]
    have hρ_ne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hρ1; exact lt_irrefl 1 hρ1
    obtain ⟨w, hw_zero, hw_re_lo, hw_im, hw_re_hi⟩ :
        ∃ w : ℂ, riemannZeta w = 0 ∧ 1 - u ≤ w.re ∧ w.im = ρ.im ∧ w.re ≤ 1 := by
      rcases le_or_gt (1 / 2) ρ.re with h | h
      · refine ⟨ρ, (_root_.RHTower.xi_eq_zero_iff hρ0 hρ_ne1).mp hρ, ?_, rfl, hρ1.le⟩
        rw [abs_of_nonneg (by linarith)] at hdist; linarith
      · set w : ℂ := 1 - conj ρ
        have hwre : w.re = 1 - ρ.re := by simp [w]
        have hwim : w.im = ρ.im := by simp [w]
        have hxw : _root_.RHTower.xi w = 0 := by
          rw [show w = 1 - (starRingEnd ℂ) ρ from rfl, _root_.RHTower.xi_one_sub,
            _root_.RHTower.xi_conj, hρ, map_zero]
        have hw0 : 0 < w.re := by rw [hwre]; linarith
        have hw1 : w ≠ 1 := fun h' => by rw [h', Complex.one_re] at hwre; linarith
        refine ⟨w, (_root_.RHTower.xi_eq_zero_iff hw0 hw1).mp hxw, ?_, hwim, by rw [hwre]; linarith⟩
        rw [abs_of_neg (by linarith : ρ.re - 1 / 2 < 0)] at hdist
        rw [hwre]; linarith
    have hwT : T ≤ |w.im| := by rw [hw_im, habsρ]; linarith
    have hlt_w : 1 - c * Real.log (Real.log |w.im|) / Real.log |w.im| < w.re := by
      rw [hw_im]; linarith
    apply hreg w.re w.im hwT hw_re_hi hlt_w
    rwa [Complex.re_add_im w]
  obtain ⟨v, K, hvK⟩ := exists_uniform_single_witness_of_not_mem_speiserDisk_segment
    ha hab hb_half (by linarith : 100 ≤ γ) hΛ hno
  refine ⟨v, K, fun σ hσ => ?_⟩
  have him_pos : 169 / 2 < |((σ : ℂ) + (γ : ℂ) * Complex.I).im| := by
    simp [abs_of_pos (by linarith : 0 < γ)]; linarith
  have him_neg : 169 / 2 < |((σ : ℂ) - (γ : ℂ) * Complex.I).im| := by
    simp [abs_of_pos (by linarith : 0 < γ)]; linarith
  exact ⟨him_pos, him_neg, hvK σ hσ⟩

#print axioms mem_range_criticalOperator_iff_of_coord_norm_eq
#print axioms missingWaveSpectrum_eq_of_coord_norm_eq
#print axioms missingWaveSpectrum_modulusMissingWave
#print axioms boundedTwist_missingWaveSpectrum_eq_abs
#print axioms unitTwist_missingWaveSpectrum_eq
#print axioms sum_range_occupationWeight_rpow_le
#print axioms norm_relativePartition_le_rpow_one_sub_re_uniform
#print axioms norm_finiteTriadReading_le_rpow_one_sub_re_uniform
#print axioms norm_jointSurvivingPartition_le_rpow_one_sub_re_uniform
#print axioms capped_witness_lineLoss_lt_rpow_neg_four_re
#print axioms no_witness_at_sublinear_loss_scale
#print axioms uncapped_witness_lineLoss_lt_inv_sq
#print axioms uncapped_witness_operator_sq_dist_le_inv_im
#print axioms norm_finiteTriadReading_le_triadTailBound_of_le_linear
#print axioms no_finite_witness_at_sublinear_prefix_scale
#print axioms exists_uvRegularRankOne_jointSurvivingPartition_ge_rpow_one_sub_re
#print axioms relativeReading_power_le_div_mul
#print axioms norm_riemannZeta_ge_exp_of_not_mem_speiserDisk_segment
#print axioms exists_uniform_single_witness_of_not_mem_speiserDisk_segment
#print axioms eventually_volume_clean_zero_exception_heights_window_ge_three_quarters
#print axioms exists_speiserShadow_exponential_density_uniform_witnesses
#print axioms exists_all_ordinates_littlewood_strip_uniform_witness

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
