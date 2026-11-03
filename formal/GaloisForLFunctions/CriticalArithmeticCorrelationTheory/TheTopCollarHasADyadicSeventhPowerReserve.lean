import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFarReserveBelowTheEighthRoot
import GaloisForLFunctions.BiScaleUncertainty.CompactSourceDerivativeEnergy
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The top collar has a dyadic seventh-power reserve

On the overlapping top collar `(M, N]` (`M = N / linearDefectCutoff c`), an atom at `log n` sits inside
a dyadic shell `[N / 2^{k+1}, N / 2^k]` whose effective overlap is `c_k ≍ c / 2^k` rather than `c`.
Localizing the top atomic test across smooth dyadic bumps in log-space (`dyadicShellBump`), bounding
the smooth partition cost by the real-space `H¹ → Lévy` inequality (`levyEnergy_le_mul_integral_deriv_sq`),
and bounding the point-multiplier commutator in `H¹` (`exists_sum_levyEnergy_dyadicCommutator_le`)
upgrades the top archimedean reserve from `(κ / c⁷) log N Σ_{M < n ≤ N} x_n²` to the dyadically
weighted seventh-power mass

`topCollarSeventhMass M N x = Σ_{M < n ≤ N} (N / n)⁷ x_n²`

(`exists_top_archForm_dyadic_seventh_reserve`). Because `(N / n)⁷` grows geometrically into the collar,
both the top prime self-form (`abs_primeSum_top_le_seventh`) and the pole-orthogonal prefix moment
(`prefixPoleMoment_sq_le_topCollarSeventhMass`) are bounded in terms of `topCollarSeventhMass`
without any `log c` factor. At a small fixed critical multiple `K₁_far > 0`, this yields the
all-scale far reserve on `(V_1)ᗮ` uniformly across `1 ≤ c ≤ 2 K₁_far (log N)^{1/8}`
(`exists_critical_multiple_far_reserve`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace ArithmeticFunction Matrix CompactlySupported

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory
  ArithmeticPositivityTheory

/-! ### The dyadically weighted seventh-power top-collar mass -/

/-- The dyadically weighted top-collar square mass `Σ_{M < n ≤ N} (N/n)⁷ x_n²`. -/
def topCollarSeventhMass (M N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Ioc M N, ((N : ℝ) / n) ^ 7 * x n ^ 2

theorem topCollarSeventhMass_nonneg (M N : ℕ) (x : ℕ → ℝ) :
    0 ≤ topCollarSeventhMass M N x :=
  sum_nonneg fun n _ => mul_nonneg (by positivity) (sq_nonneg _)

theorem sum_sq_Ioc_le_topCollarSeventhMass (M N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Ioc M N, x n ^ 2 ≤ topCollarSeventhMass M N x := by
  unfold topCollarSeventhMass
  refine sum_le_sum fun n hn => ?_
  obtain ⟨hMn, hnN⟩ := mem_Ioc.mp hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 : (1 : ℝ) ≤ (N : ℝ) / n := by
    rw [one_le_div hn0]
    exact_mod_cast hnN
  exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ h1)

/-- On `(V_1)ᗮ`, the squared prefix pole moment is bounded directly by `topCollarSeventhMass M N`
with unit constant and no `log(N/M)` factor. -/
theorem prefixPoleMoment_sq_le_topCollarSeventhMass {N M : ℕ} (hN2 : 2 ≤ N) (hMN : M ≤ N)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace 1 N)ᗮ) :
    prefixPoleMoment M (primeHorizonExtension z) ^ 2 ≤
      topCollarSeventhMass M N (primeHorizonExtension z) := by
  set x := primeHorizonExtension z
  have hpole := poleFunctional_eq_zero_of_mem_conductorSubspace_one_orthogonal hN2 hz
  change ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 at hpole
  have hsplit : ∑ n ∈ Icc 1 N, x n / Real.sqrt n =
      ∑ n ∈ Icc 1 M, x n / Real.sqrt n + ∑ n ∈ Ioc M N, x n / Real.sqrt n := by
    have hdisj : Icc 1 N = Icc 1 M ∪ Ioc M N := by
      ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    rw [hdisj, sum_union]
    exact disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_Icc] at h1; simp only [mem_Ioc] at h2; omega
  have hσ : prefixPoleMoment M x = -∑ n ∈ Ioc M N, x n / Real.sqrt n := by
    unfold prefixPoleMoment; linarith
  rw [hσ, neg_sq]
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfac : ∑ n ∈ Ioc M N, x n / Real.sqrt n =
      ∑ n ∈ Ioc M N, (Real.sqrt n / N) * (((N : ℝ) / n) * x n) := by
    refine sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    calc x n / Real.sqrt n = (Real.sqrt n / (Real.sqrt n * Real.sqrt n)) * x n := by
          field_simp [hsn]
      _ = (Real.sqrt n / n) * x n := by rw [Real.mul_self_sqrt hn0.le]
      _ = (Real.sqrt n / N) * (((N : ℝ) / n) * x n) := by field_simp [hNR.ne', hn0.ne']
  rw [hfac]
  have hcs := sum_mul_sq_le_sq_mul_sq (Ioc M N) (fun n : ℕ => Real.sqrt n / (N : ℝ))
    (fun n : ℕ => ((N : ℝ) / n) * x n)
  have h1 : ∑ n ∈ Ioc M N, (Real.sqrt n / (N : ℝ)) ^ 2 ≤ 1 := by
    have hterm : ∀ n ∈ Ioc M N, (Real.sqrt n / (N : ℝ)) ^ 2 ≤ 1 / (N : ℝ) := fun n hn => by
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp hn).2
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      calc (n : ℝ) / (N : ℝ) ^ 2 ≤ (N : ℝ) / (N : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hnN (sq_nonneg _)
        _ = 1 / (N : ℝ) := by field_simp [hNR.ne']
    have hsub : Ioc M N ⊆ Icc 1 N := fun n hn =>
      mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
    calc ∑ n ∈ Ioc M N, (Real.sqrt n / (N : ℝ)) ^ 2
        ≤ ∑ n ∈ Ioc M N, (1 : ℝ) / N := sum_le_sum hterm
      _ ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) / N :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          field_simp [hNR.ne']
  have h2 : ∑ n ∈ Ioc M N, (((N : ℝ) / n) * x n) ^ 2 ≤ topCollarSeventhMass M N x := by
    unfold topCollarSeventhMass
    refine sum_le_sum fun n hn => ?_
    obtain ⟨hMn, hnN⟩ := mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 1 ≤ n by omega)
    have hge1 : (1 : ℝ) ≤ (N : ℝ) / n := (one_le_div hn0).mpr (by exact_mod_cast hnN)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hge1 (by norm_num : 2 ≤ 7)) (sq_nonneg _)
  exact hcs.trans ((mul_le_mul h1 h2 (sum_nonneg fun _ _ => sq_nonneg _) zero_le_one).trans_eq
    (one_mul _))

/-! ### Real-space `H¹ → Lévy` inequality and triangle bound -/

/-- A `C_c²` function has Lévy energy at most `18` times its Dirichlet energy `∫ (h')²`. -/
theorem levyEnergy_le_mul_integral_deriv_sq {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) :
    levyEnergy h ≤ 18 * ∫ u, deriv h u ^ 2 := by
  let hc : C_c(ℝ, ℝ) := ⟨⟨h, hh.continuous⟩, hhc⟩
  have hpoint : ∀ y ∈ Set.Ioi (0 : ℝ),
      levyIntegrand h y ≤ (y ^ 2 * archLevyDensity y) * ∫ u, deriv h u ^ 2 := by
    intro y hy
    have htr := BiScaleUncertainty.SobolevShear.integral_compactSource_translation_sq_le hc hh y
    have heq : (∫ u, (h u - h (u + y)) ^ 2) = ∫ u, (hc (u + y) - hc u) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun u => by change (h u - h (u + y)) ^ 2 = (h (u + y) - h u) ^ 2; ring)
    unfold levyIntegrand
    rw [heq]
    calc archLevyDensity y * ∫ u, (hc (u + y) - hc u) ^ 2
        ≤ archLevyDensity y * (y ^ 2 * ∫ u, deriv h u ^ 2) :=
          mul_le_mul_of_nonneg_left htr (archLevyDensity_pos hy).le
      _ = (y ^ 2 * archLevyDensity y) * ∫ u, deriv h u ^ 2 := by ring
  have hint := setIntegral_mono_on (integrableOn_levyIntegrand hh hhc)
    (RHTower.integrableOn_sq_mul_archLevyDensity.mul_const _) measurableSet_Ioi hpoint
  have hd0 : 0 ≤ ∫ u, deriv h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  unfold levyEnergy
  change (∫ y in Set.Ioi (0 : ℝ), levyIntegrand h y) ≤ _
  calc (∫ y in Set.Ioi (0 : ℝ), levyIntegrand h y)
      ≤ ∫ y in Set.Ioi (0 : ℝ), (y ^ 2 * archLevyDensity y) * ∫ u, deriv h u ^ 2 := hint
    _ = (∫ y in Set.Ioi (0 : ℝ), y ^ 2 * archLevyDensity y) * ∫ u, deriv h u ^ 2 :=
        integral_mul_const _ _
    _ ≤ 18 * ∫ u, deriv h u ^ 2 := mul_le_mul_of_nonneg_right RHTower.levySecondMoment_le hd0

theorem levyEnergy_neg (h : ℝ → ℝ) : levyEnergy (fun u => -h u) = levyEnergy h := by
  unfold levyEnergy
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun u => by ring)

/-- Quadratic triangle inequality for `levyEnergy`: `levyEnergy (a - b) ≤ 2 levyEnergy a + 2 levyEnergy b`. -/
theorem levyEnergy_sub_le_two_mul {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b) :
    levyEnergy (fun u => a u - b u) ≤ 2 * levyEnergy a + 2 * levyEnergy b := by
  have heq : (fun u => a u - b u) = fun u => a u + -b u := funext fun _ => sub_eq_add_neg _ _
  rw [heq]
  have h1 := SpacingScaleHarmonicAnalysis.levyEnergy_add_le ha hac hb.neg hbc.neg
  rw [levyEnergy_neg] at h1
  have hA := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' a
  have hB := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' b
  have hcs : 2 * (Real.sqrt (levyEnergy a) * Real.sqrt (levyEnergy b)) ≤
      levyEnergy a + levyEnergy b := by
    have hsq := sq_nonneg (Real.sqrt (levyEnergy a) - Real.sqrt (levyEnergy b))
    have hA2 := Real.sq_sqrt hA
    have hB2 := Real.sq_sqrt hB
    nlinarith
  linarith

/-! ### Smooth dyadic bumps and IMS localization -/

/-- Smooth unit plateau bump equal to `1` on `[-1, 1]` and supported in `(-2, 2)`. -/
def baseShellBump : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

theorem baseShellBump_nonneg (t : ℝ) : 0 ≤ (baseShellBump : ℝ → ℝ) t :=
  ContDiffBump.nonneg _

theorem baseShellBump_le_one (t : ℝ) : (baseShellBump : ℝ → ℝ) t ≤ 1 :=
  ContDiffBump.le_one _

theorem contDiff_baseShellBump {n : ℕ∞} : ContDiff ℝ n (baseShellBump : ℝ → ℝ) :=
  baseShellBump.contDiff

theorem hasCompactSupport_baseShellBump : HasCompactSupport (baseShellBump : ℝ → ℝ) :=
  ContDiffBump.hasCompactSupport _

theorem baseShellBump_eq_one {t : ℝ} (ht : |t| ≤ 1) : (baseShellBump : ℝ → ℝ) t = 1 :=
  baseShellBump.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, Real.dist_eq, baseShellBump] using ht)

theorem baseShellBump_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : (baseShellBump : ℝ → ℝ) t = 0 := by
  have h := ContDiffBump.support_eq baseShellBump
  refine Function.notMem_support.mp fun hs => ?_
  rw [h] at hs
  have hlt : |t| < 2 := by simpa [Metric.mem_ball, Real.dist_eq, baseShellBump] using hs
  linarith

theorem exists_baseShellBump_deriv_bound :
    ∃ L_B : ℝ, 0 ≤ L_B ∧ (∀ t, |deriv (baseShellBump : ℝ → ℝ) t| ≤ L_B) ∧
      ∀ a b, |(baseShellBump : ℝ → ℝ) a - (baseShellBump : ℝ → ℝ) b| ≤ L_B * |a - b| := by
  have hcd : Continuous (deriv (baseShellBump : ℝ → ℝ)) :=
    (contDiff_baseShellBump (n := 2)).continuous_deriv (by norm_num)
  have hcs : HasCompactSupport (deriv (baseShellBump : ℝ → ℝ)) :=
    hasCompactSupport_baseShellBump.deriv
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcd
  set L_B := max C 0
  have hLB0 : 0 ≤ L_B := le_max_right _ _
  have hd : ∀ t, |deriv (baseShellBump : ℝ → ℝ) t| ≤ L_B := fun t => by
    have := hC t
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  refine ⟨L_B, hLB0, hd, fun a b => ?_⟩
  have hdiff : Differentiable ℝ (baseShellBump : ℝ → ℝ) :=
    (contDiff_baseShellBump (n := 2)).differentiable (by norm_num)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
    (fun x _ => hdiff.differentiableAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hd x) convex_univ (Set.mem_univ b) (Set.mem_univ a)
  simpa only [Real.norm_eq_abs] using hmvt

/-- Log-space center `log N − (k + 1) log 2` of the `k`-th dyadic shell below `N`. -/
def shellCenter (N k : ℕ) : ℝ := Real.log N - ((k : ℝ) + 1) * Real.log 2

/-- Smooth bump localized around `shellCenter N k`. -/
def dyadicShellBump (N k : ℕ) (u : ℝ) : ℝ := (baseShellBump : ℝ → ℝ) (u - shellCenter N k)

/-- Number of dyadic shells needed to cover `(N / linearDefectCutoff c, N]`. -/
def dyadicShellCount (c : ℝ) : ℕ := ⌊Real.log (linearDefectCutoff c) / Real.log 2⌋₊ + 1

theorem dyadicShellBump_nonneg (N k : ℕ) (u : ℝ) : 0 ≤ dyadicShellBump N k u :=
  baseShellBump_nonneg _

theorem dyadicShellBump_le_one (N k : ℕ) (u : ℝ) : dyadicShellBump N k u ≤ 1 :=
  baseShellBump_le_one _

theorem contDiff_dyadicShellBump (N k : ℕ) : ContDiff ℝ 2 (dyadicShellBump N k) :=
  (contDiff_baseShellBump (n := 2)).comp (contDiff_id.sub contDiff_const)

theorem dyadicShellBump_eq_zero {N k : ℕ} {u : ℝ} (hu : 2 ≤ |u - shellCenter N k|) :
    dyadicShellBump N k u = 0 :=
  baseShellBump_eq_zero hu

theorem dyadicShellBump_eq_one {N k : ℕ} {u : ℝ} (hu : |u - shellCenter N k| ≤ 1) :
    dyadicShellBump N k u = 1 :=
  baseShellBump_eq_one hu

/-- At any point `u`, at most `4 R + 1` dyadic shell centers lie within distance `R` of `u`. -/
theorem card_shellCenter_near_le (s : Finset ℕ) (N : ℕ) (u : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ((s.filter fun k : ℕ => |u - shellCenter N k| ≤ R).card : ℝ) ≤ 4 * R + 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hl2_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  set a := (Real.log N - u) / Real.log 2 - 1
  have hsub : (s.filter fun k : ℕ => |u - shellCenter N k| ≤ R) ⊆
      s.filter fun k : ℕ => |((1 : ℕ) : ℝ) * k - a| ≤ R / Real.log 2 := by
    intro k hk
    obtain ⟨hks, hdist⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hks, ?_⟩
    rw [Nat.cast_one, one_mul, le_div_iff₀ hl2]
    have hid : ((k : ℝ) - a) * Real.log 2 = u - shellCenter N k := by
      dsimp only [a, shellCenter]
      field_simp [hl2.ne']
      ring
    rw [← abs_of_pos hl2, ← abs_mul, hid]
    exact hdist
  have hcard := (Nat.cast_le.mpr (card_le_card hsub)).trans
    (card_mul_near_le s le_rfl a (div_nonneg hR hl2.le))
  rw [Nat.cast_one, div_one] at hcard
  have hdiv : R / Real.log 2 ≤ 2 * R := by
    rw [div_le_iff₀ hl2]
    nlinarith
  linarith

/-- **Smooth dyadic IMS inequality for the Lévy energy.** Summing `levyEnergy (χ_k · f)` across any
finite family of dyadic shells costs at most a bounded multiple of `levyEnergy f + ‖f‖₂²`. -/
theorem sum_levyEnergy_dyadicShellBump_mul_le {L_B : ℝ}
    (hlip : ∀ a b, |(baseShellBump : ℝ → ℝ) a - (baseShellBump : ℝ → ℝ) b| ≤ L_B * |a - b|)
    (s : Finset ℕ) (N : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * f u) ≤
      18 * levyEnergy f + 648 * L_B ^ 2 * ∫ u, f u ^ 2 := by
  have hχf : ∀ k, ContDiff ℝ 2 (fun u => dyadicShellBump N k u * f u) := fun k =>
    (contDiff_dyadicShellBump N k).mul hf
  have hχfc : ∀ k, HasCompactSupport (fun u => dyadicShellBump N k u * f u) := fun k =>
    hfc.mul_left
  have hsum_u : ∀ y > (0 : ℝ),
      (∑ k ∈ s, ∫ u, (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2) ≤
        18 * (∫ u, (f u - f (u + y)) ^ 2) + 36 * L_B ^ 2 * y ^ 2 * ∫ u, f u ^ 2 := by
    intro y hy
    rw [← integral_finsetSum s fun k _ =>
      RHTower.WeilMarkovPole.integrable_sub_shift_sq (hχf k).continuous (hχfc k) y]
    have hpt : ∀ u : ℝ,
        (∑ k ∈ s, (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2) ≤
          18 * (f u - f (u + y)) ^ 2 + 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2 := by
      intro u
      have hterm : ∀ k ∈ s,
          (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2 ≤
            2 * (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) * (f u - f (u + y)) ^ 2 +
              2 * L_B ^ 2 * y ^ 2 *
                ((if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                  (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0)) * f (u + y) ^ 2 := by
        intro k _
        have hsplit : dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y) =
            dyadicShellBump N k u * (f u - f (u + y)) +
              (dyadicShellBump N k u - dyadicShellBump N k (u + y)) * f (u + y) := by ring
        have hsq2 : ∀ A B : ℝ, (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := fun A B => by
          nlinarith [sq_nonneg (A - B)]
        have h1 : dyadicShellBump N k u ^ 2 ≤ if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0 := by
          split_ifs with hle
          · have h0 := dyadicShellBump_nonneg N k u
            have h1' := dyadicShellBump_le_one N k u
            nlinarith
          · rw [dyadicShellBump_eq_zero (le_of_not_ge hle), sq, zero_mul]
        have h2 : (dyadicShellBump N k u - dyadicShellBump N k (u + y)) ^ 2 ≤
            L_B ^ 2 * y ^ 2 * ((if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
              (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0)) := by
          by_cases hu1 : |u - shellCenter N k| ≤ 2
          · have hl := hlip (u - shellCenter N k) (u + y - shellCenter N k)
            have hd : |(u - shellCenter N k) - (u + y - shellCenter N k)| = y := by
              rw [show (u - shellCenter N k) - (u + y - shellCenter N k) = -y by ring,
                abs_neg, abs_of_pos hy]
            rw [hd] at hl
            have hsq := pow_le_pow_left₀ (abs_nonneg _) hl 2
            rw [sq_abs, mul_pow] at hsq
            have hind : (1 : ℝ) ≤ (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) := by
              rw [if_pos hu1]
              split_ifs <;> norm_num
            exact hsq.trans (le_mul_of_one_le_right (by positivity) hind)
          · by_cases hu2 : |u + y - shellCenter N k| ≤ 2
            · have hl := hlip (u - shellCenter N k) (u + y - shellCenter N k)
              have hd : |(u - shellCenter N k) - (u + y - shellCenter N k)| = y := by
                rw [show (u - shellCenter N k) - (u + y - shellCenter N k) = -y by ring,
                  abs_neg, abs_of_pos hy]
              rw [hd] at hl
              have hsq := pow_le_pow_left₀ (abs_nonneg _) hl 2
              rw [sq_abs, mul_pow] at hsq
              have hind : (1 : ℝ) ≤ (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                  (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) := by
                rw [if_neg hu1, if_pos hu2]; norm_num
              exact hsq.trans (le_mul_of_one_le_right (by positivity) hind)
            · rw [dyadicShellBump_eq_zero (le_of_not_ge hu1),
                dyadicShellBump_eq_zero (le_of_not_ge hu2), sub_self, sq, zero_mul]
              positivity
        calc (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2
            ≤ 2 * (dyadicShellBump N k u * (f u - f (u + y))) ^ 2 +
                2 * ((dyadicShellBump N k u - dyadicShellBump N k (u + y)) * f (u + y)) ^ 2 := by
              rw [hsplit]; exact hsq2 _ _
          _ = 2 * dyadicShellBump N k u ^ 2 * (f u - f (u + y)) ^ 2 +
                2 * (dyadicShellBump N k u - dyadicShellBump N k (u + y)) ^ 2 * f (u + y) ^ 2 := by
              ring
          _ ≤ _ := (add_le_add
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 zero_le_two) (sq_nonneg _))
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 zero_le_two)
                (sq_nonneg _))).trans_eq (by ring)
      have hc1 : ∑ k ∈ s, (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) ≤ 9 := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        exact (card_shellCenter_near_le s N u (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)
      have hc2 : ∑ k ∈ s, (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) ≤ 9 := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        exact (card_shellCenter_near_le s N (u + y) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)
      calc ∑ k ∈ s, (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2
          ≤ ∑ k ∈ s, (2 * (if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) * (f u - f (u + y)) ^ 2 +
              2 * L_B ^ 2 * y ^ 2 *
                ((if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                  (if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0)) * f (u + y) ^ 2) :=
            sum_le_sum hterm
        _ = 2 * (∑ k ∈ s, if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) * (f u - f (u + y)) ^ 2 +
              2 * L_B ^ 2 * y ^ 2 *
                ((∑ k ∈ s, if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) +
                  (∑ k ∈ s, if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0)) *
                f (u + y) ^ 2 := by
            rw [sum_add_distrib, ← sum_mul, ← mul_sum, ← sum_mul, ← mul_sum, sum_add_distrib]
        _ ≤ 18 * (f u - f (u + y)) ^ 2 + 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2 := by
            have ha := mul_le_mul_of_nonneg_right (show 2 * (∑ k ∈ s, if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) ≤ 18 by linarith) (sq_nonneg (f u - f (u + y)))
            have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show (∑ k ∈ s, if |u - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) + (∑ k ∈ s, if |u + y - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) ≤ 18 by linarith) (by positivity : 0 ≤ 2 * L_B ^ 2 * y ^ 2)) (sq_nonneg (f (u + y)))
            linarith
    have hi1 : Integrable (fun u => 18 * (f u - f (u + y)) ^ 2) :=
      (RHTower.WeilMarkovPole.integrable_sub_shift_sq hf.continuous hfc y).const_mul 18
    have hi2 : Integrable (fun u => 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2) :=
      ((integrable_sq_of_continuous hf.continuous hfc).comp_add_right y).const_mul
        (36 * L_B ^ 2 * y ^ 2)
    have himono : (∫ u, ∑ k ∈ s,
        (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2) ≤
        ∫ u, (18 * (f u - f (u + y)) ^ 2 + 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2) :=
      integral_mono (integrable_finsetSum s fun k _ =>
        RHTower.WeilMarkovPole.integrable_sub_shift_sq (hχf k).continuous (hχfc k) y)
        (hi1.add hi2) hpt
    calc (∫ u, ∑ k ∈ s,
          (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2)
        ≤ ∫ u, (18 * (f u - f (u + y)) ^ 2 + 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2) := himono
      _ = (∫ u, 18 * (f u - f (u + y)) ^ 2) +
            ∫ u, 36 * L_B ^ 2 * y ^ 2 * f (u + y) ^ 2 := integral_add hi1 hi2
      _ = 18 * (∫ u, (f u - f (u + y)) ^ 2) + 36 * L_B ^ 2 * y ^ 2 * ∫ u, f u ^ 2 := by
          rw [integral_const_mul, integral_const_mul,
            integral_add_right_eq_self (fun u => f u ^ 2) y]
  have hsum_y : ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * f u) =
      ∫ y in Set.Ioi (0 : ℝ), ∑ k ∈ s, levyIntegrand (fun u => dyadicShellBump N k u * f u) y := by
    unfold levyEnergy
    exact (integral_finsetSum s fun k _ => integrableOn_levyIntegrand (hχf k) (hχfc k)).symm
  rw [hsum_y]
  have hiL : IntegrableOn (fun y => 18 * levyIntegrand f y) (Set.Ioi 0) :=
    (integrableOn_levyIntegrand hf hfc).const_mul 18
  have hiM : IntegrableOn (fun y => (36 * L_B ^ 2 * ∫ u, f u ^ 2) * (y ^ 2 * archLevyDensity y))
      (Set.Ioi 0) :=
    RHTower.integrableOn_sq_mul_archLevyDensity.const_mul _
  have hmono : (∫ y in Set.Ioi (0 : ℝ),
        ∑ k ∈ s, levyIntegrand (fun u => dyadicShellBump N k u * f u) y) ≤
      ∫ y in Set.Ioi (0 : ℝ),
        (18 * levyIntegrand f y +
          (36 * L_B ^ 2 * ∫ u, f u ^ 2) * (y ^ 2 * archLevyDensity y)) :=
    setIntegral_mono_on
      (integrable_finsetSum s fun k _ => integrableOn_levyIntegrand (hχf k) (hχfc k))
      (hiL.add hiM) measurableSet_Ioi fun y hy => by
        have hω := (archLevyDensity_pos hy).le
        calc ∑ k ∈ s, levyIntegrand (fun u => dyadicShellBump N k u * f u) y
            = archLevyDensity y * ∑ k ∈ s, ∫ u,
                (dyadicShellBump N k u * f u - dyadicShellBump N k (u + y) * f (u + y)) ^ 2 := by
              unfold levyIntegrand; rw [mul_sum]
          _ ≤ archLevyDensity y * (18 * (∫ u, (f u - f (u + y)) ^ 2) +
                36 * L_B ^ 2 * y ^ 2 * ∫ u, f u ^ 2) :=
              mul_le_mul_of_nonneg_left (hsum_u y hy) hω
          _ = 18 * levyIntegrand f y +
                (36 * L_B ^ 2 * ∫ u, f u ^ 2) * (y ^ 2 * archLevyDensity y) := by
              unfold levyIntegrand; ring
  have hsplit_int : (∫ y in Set.Ioi (0 : ℝ),
        (18 * levyIntegrand f y +
          (36 * L_B ^ 2 * ∫ u, f u ^ 2) * (y ^ 2 * archLevyDensity y))) =
      18 * levyEnergy f + (36 * L_B ^ 2 * ∫ u, f u ^ 2) * RHTower.levySecondMoment := by
    rw [integral_add hiL hiM, integral_const_mul, integral_const_mul]
    rfl
  have hf2 : 0 ≤ 36 * L_B ^ 2 * ∫ u, f u ^ 2 :=
    mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  have hm2 := mul_le_mul_of_nonneg_left RHTower.levySecondMoment_le hf2
  linarith [hmono, hsplit_int, hm2]

/-! ### Shell horizon and point-multiplier commutator in `H¹` -/

/-- Effective integer horizon `min N ⌊4 N / 2^k⌋₊` of the `k`-th dyadic shell. -/
def dyadicShellHorizon (N k : ℕ) : ℕ := min N ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊

/-- Every integer `n ≤ N` above `dyadicShellHorizon N k` lies strictly outside the support of
`dyadicShellBump N k (log ·)`. -/
theorem dyadicShellBump_log_eq_zero_of_gt_horizon {N k n : ℕ} (hN : 1 ≤ N) (hnN : n ≤ N)
    (hgt : dyadicShellHorizon N k < n) :
    dyadicShellBump N k (Real.log n) = 0 := by
  have hfl : ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊ < n := by
    unfold dyadicShellHorizon at hgt
    omega
  have hlt : 4 * (N : ℝ) / (2 : ℝ) ^ k < n := Nat.lt_of_floor_lt hfl
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hlt
  have he2 : Real.exp 2 < 8 := by
    have he1 : Real.exp 1 < 11 / 4 := by have := Real.exp_one_lt_d9; linarith
    have he2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he2']
    nlinarith [Real.exp_pos 1]
  have hexp_sc : Real.exp (shellCenter N k + 2) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k := by
    have hid : shellCenter N k + 2 = Real.log N - (k : ℝ) * Real.log 2 + (2 - Real.log 2) := by
      unfold shellCenter; ring
    rw [hid, Real.exp_add, Real.exp_sub, Real.exp_log hNR,
      show (k : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k) by rw [Real.log_pow],
      Real.exp_log (by positivity), Real.exp_sub, Real.exp_log zero_lt_two]
    have h4 : Real.exp 2 / 2 ≤ 4 := by linarith
    calc (N : ℝ) / (2 : ℝ) ^ k * (Real.exp 2 / 2)
        ≤ (N : ℝ) / (2 : ℝ) ^ k * 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 4 * (N : ℝ) / (2 : ℝ) ^ k := by ring
  have hlog_gt : shellCenter N k + 2 < Real.log n := by
    have := Real.log_lt_log (Real.exp_pos _) (hexp_sc.trans_lt hlt)
    rwa [Real.log_exp] at this
  exact dyadicShellBump_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)

/-- Because `dyadicShellBump N k (log n)` vanishes for `dyadicShellHorizon N k < n ≤ N`, the shell
atomic test at horizon `dyadicShellHorizon N k` equals the atomic test at horizon `N`. -/
theorem atomicTest_dyadicShellHorizon_eq {N k : ℕ} (hN : 1 ≤ N) (y : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest (dyadicShellHorizon N k) (fun n => dyadicShellBump N k (Real.log n) * y n) g =
      atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g := by
  funext u
  unfold atomicTest
  refine sum_subset (Icc_subset_Icc le_rfl (min_le_left N _)) fun n hn hnot => ?_
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hgt : dyadicShellHorizon N k < n := by
    by_contra hle
    exact hnot (mem_Icc.mpr ⟨hn1, not_lt.mp hle⟩)
  dsimp only
  rw [dyadicShellBump_log_eq_zero_of_gt_horizon hN hnN hgt, zero_mul, zero_mul]

/-- **Dyadic commutator bound in Lévy energy.** Replacing smooth multiplication `χ_k · f_y` by
discrete coefficient multiplication `F_k` costs `O(c G Σ y_n²)` summed across all shells. -/
theorem exists_sum_levyEnergy_dyadicCommutator_le :
    ∃ C_comm : ℝ, 0 ≤ C_comm ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → c ≤ N → ∀ (s : Finset ℕ) (y : ℕ → ℝ),
        ∑ k ∈ s, levyEnergy (fun u =>
          dyadicShellBump N k u * atomicTest N y (atomDilate tiltedUnitSpline (c / N)) u -
            atomicTest (dyadicShellHorizon N k)
              (fun n => dyadicShellBump N k (Real.log n) * y n)
              (atomDilate tiltedUnitSpline (c / N)) u) ≤
          C_comm * c * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * ∑ n ∈ Icc 1 N, y n ^ 2 := by
  obtain ⟨L_B, hLB0, hdB, hlipB⟩ := exists_baseShellBump_deriv_bound
  obtain ⟨C₀, hC₀⟩ := hasCompactSupport_tiltedUnitSpline.exists_bound_of_continuous
    contDiff_tiltedUnitSpline.continuous
  obtain ⟨C₁, hC₁⟩ := hasCompactSupport_tiltedUnitSpline.deriv.exists_bound_of_continuous
    (contDiff_tiltedUnitSpline.continuous_deriv (by norm_num))
  set M₀ := max C₀ 0
  set M₁ := max C₁ 0
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hM₁0 : 0 ≤ M₁ := le_max_right _ _
  have hb0 : ∀ t, |tiltedUnitSpline t| ≤ M₀ := fun t => by
    have := hC₀ t; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hb1 : ∀ t, |deriv tiltedUnitSpline t| ≤ M₁ := fun t => by
    have := hC₁ t; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  set K₀ := L_B * (M₀ + M₁)
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hφ2 : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  set C_comm := 18 * 13 * K₀ ^ 2 * (Real.exp 1 + 1) / ∫ u, tiltedUnitSpline u ^ 2
  refine ⟨C_comm, by positivity, ?_⟩
  intro c N hc1 hcN s y
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by exact_mod_cast hc1.trans hcN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  set w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  set g := atomDilate tiltedUnitSpline w
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hdiff_φ : Differentiable ℝ tiltedUnitSpline :=
    contDiff_tiltedUnitSpline.differentiable (by norm_num)
  have hdiff_B : Differentiable ℝ (baseShellBump : ℝ → ℝ) :=
    (contDiff_baseShellBump (n := 2)).differentiable (by norm_num)
  -- Bound each shell commutator by its filtered H¹ norm
  have hshell : ∀ k ∈ s,
      levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g u) ≤
        18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w *
          ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
            y n ^ 2 := by
    intro k _
    rw [atomicTest_dyadicShellHorizon_eq hN1 y g]
    let S_k : Finset ℕ :=
      (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3)
    let h_atom : ℕ → ℝ → ℝ := fun n u =>
      (dyadicShellBump N k u - dyadicShellBump N k (Real.log n)) * g (u - Real.log n)
    have hR_eq : (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u) =
        fun u => ∑ n ∈ S_k, y n * h_atom n u := by
      funext u
      unfold atomicTest
      rw [mul_sum, ← sum_sub_distrib]
      have hfull : ∑ x ∈ Icc 1 N, (dyadicShellBump N k u * (y x * g (u - Real.log x)) -
          dyadicShellBump N k (Real.log x) * y x * g (u - Real.log x)) =
          ∑ x ∈ Icc 1 N, y x * h_atom x u :=
        sum_congr rfl fun n _ => by simp only [h_atom]; ring
      rw [hfull]
      refine (sum_subset (filter_subset _ _) fun n hn hnot => ?_).symm
      have hgt3 : 3 < |Real.log (n : ℝ) - shellCenter N k| :=
        lt_of_not_ge fun hle => hnot (mem_filter.mpr ⟨hn, hle⟩)
      simp only [h_atom]
      by_cases huw : u - Real.log n ∈ Set.Icc 0 w
      · obtain ⟨hu0, huw'⟩ := Set.mem_Icc.mp huw
        have h1 : 2 ≤ |Real.log (n : ℝ) - shellCenter N k| := by linarith
        have h2 : 2 ≤ |u - shellCenter N k| := by
          have htri := abs_sub_abs_le_abs_sub (Real.log (n : ℝ) - shellCenter N k)
            (Real.log (n : ℝ) - u)
          have hdu : |Real.log (n : ℝ) - u| ≤ 1 := by
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]
            linarith
          have hid : (Real.log (n : ℝ) - shellCenter N k) - (Real.log (n : ℝ) - u) =
              u - shellCenter N k := by
            ring
          rw [hid] at htri
          linarith
        rw [dyadicShellBump_eq_zero h2, dyadicShellBump_eq_zero h1, sub_self, zero_mul, mul_zero]
      · have hg0 : g (u - Real.log n) = 0 := hsupp _ huw
        rw [hg0, mul_zero, mul_zero]
    have hRk_cd : ContDiff ℝ 2 (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u) :=
      ((contDiff_dyadicShellBump N k).mul (contDiff_atomicTest hg N y)).sub
        (contDiff_atomicTest hg N _)
    have hRk_cs : HasCompactSupport (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest N (fun n => dyadicShellBump N k (Real.log n) * y n) g u) :=
      ((hasCompactSupport_atomicTest hsupp N y).mul_left).sub
        (hasCompactSupport_atomicTest hsupp N _)
    have hlev := levyEnergy_le_mul_integral_deriv_sq hRk_cd hRk_cs
    rw [hR_eq] at hlev hRk_cd hRk_cs ⊢
    -- Pointwise derivative bound for each atom `h_atom n`
    have hh_diff : ∀ n : ℕ, Differentiable ℝ (h_atom n) := fun n =>
      (((contDiff_dyadicShellBump N k).sub contDiff_const).mul
        (hg.comp (contDiff_id.sub contDiff_const))).differentiable (by norm_num)
    have hderiv_atom : ∀ (n : ℕ) (u : ℝ),
        |deriv (h_atom n) u| ≤
          K₀ * (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
      intro n u
      by_cases huI : u ∈ Set.Icc (Real.log n) (Real.log n + w)
      · rw [Set.indicator_of_mem huI, mul_one]
        obtain ⟨hu_lo, hu_hi⟩ := Set.mem_Icc.mp huI
        have hd1 : HasDerivAt (fun v => dyadicShellBump N k v - dyadicShellBump N k (Real.log n))
            (deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k)) u := by
          have hsub1 : HasDerivAt (fun v : ℝ => v - shellCenter N k) 1 u :=
            (hasDerivAt_id u).sub_const (shellCenter N k)
          have hcomp1 := (hdiff_B.differentiableAt.hasDerivAt).comp u hsub1
          simpa only [Function.comp_def, id_eq, mul_one, dyadicShellBump] using
            hcomp1.sub_const (dyadicShellBump N k (Real.log n))
        have hd2 : HasDerivAt (fun v => g (v - Real.log n))
            (deriv tiltedUnitSpline ((u - Real.log n) / w) / w) u := by
          have hsub : HasDerivAt (fun v : ℝ => (v - Real.log n) / w) (1 / w) u :=
            ((hasDerivAt_id u).sub_const (Real.log n)).div_const w
          have hcomp := (hdiff_φ.differentiableAt.hasDerivAt).comp u hsub
          simpa only [Function.comp_def, id_eq, mul_one_div, g, atomDilate] using hcomp
        have hdmul := (hd1.mul hd2).deriv
        change deriv (h_atom n) u = _ at hdmul
        rw [hdmul]
        have hv1 : |dyadicShellBump N k u - dyadicShellBump N k (Real.log n)| ≤ L_B * w := by
          have hl := hlipB (u - shellCenter N k) (Real.log n - shellCenter N k)
          have hd : |(u - shellCenter N k) - (Real.log n - shellCenter N k)| ≤ w := by
            rw [show (u - shellCenter N k) - (Real.log n - shellCenter N k) = u - Real.log n by ring,
              abs_of_nonneg (by linarith)]
            linarith
          exact hl.trans (mul_le_mul_of_nonneg_left hd hLB0)
        have hv2 : |g (u - Real.log n)| ≤ M₀ := hb0 _
        have hd2_le : |deriv tiltedUnitSpline ((u - Real.log n) / w) / w| ≤ M₁ / w := by
          rw [abs_div, abs_of_pos hw]
          exact div_le_div_of_nonneg_right (hb1 _) hw.le
        calc |deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k) * g (u - Real.log n) +
              (dyadicShellBump N k u - dyadicShellBump N k (Real.log n)) *
                (deriv tiltedUnitSpline ((u - Real.log n) / w) / w)|
            ≤ |deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k) * g (u - Real.log n)| +
                |(dyadicShellBump N k u - dyadicShellBump N k (Real.log n)) *
                  (deriv tiltedUnitSpline ((u - Real.log n) / w) / w)| := abs_add_le _ _
          _ = |deriv (baseShellBump : ℝ → ℝ) (u - shellCenter N k)| * |g (u - Real.log n)| +
                |dyadicShellBump N k u - dyadicShellBump N k (Real.log n)| *
                  |deriv tiltedUnitSpline ((u - Real.log n) / w) / w| := by rw [abs_mul, abs_mul]
          _ ≤ L_B * M₀ + (L_B * w) * (M₁ / w) :=
              add_le_add (mul_le_mul (hdB _) hv2 (abs_nonneg _) hLB0)
                (mul_le_mul hv1 hd2_le (abs_nonneg _) (mul_nonneg hLB0 hw.le))
          _ = K₀ := by simp only [K₀]; field_simp [hw.ne']
      · rw [Set.indicator_of_notMem huI, mul_zero]
        have hev : h_atom n =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
          refine Filter.eventually_of_mem (isClosed_Icc.isOpen_compl.mem_nhds huI) fun v hv => ?_
          have hvw : v - Real.log n ∉ Set.Icc 0 w := fun hmem =>
            hv (Set.mem_Icc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
          simp only [h_atom, g]
          rw [hsupp _ hvw, mul_zero]
        rw [hev.deriv_eq, deriv_const, abs_zero]
    -- Overlap count of intervals `[log n, log n + w]` at any point `u`
    have hoverlap : ∀ u : ℝ,
        ∑ n ∈ S_k, (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u ≤
          (Real.exp 1 + 1) * c := by
      intro u
      by_cases hu_hi : Real.log N + w < u
      · have hz : ∑ n ∈ S_k, (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u = 0 := by
          refine sum_eq_zero fun n hn => Set.indicator_of_notMem ?_ _
          intro hmem
          have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).2
          have hn1 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hn).1).1
          have hlog : Real.log n ≤ Real.log N := Real.log_le_log hn1 hnN
          linarith [hmem.2]
        rw [hz]; positivity
      · push Not at hu_hi
        have hsub : S_k.filter (fun n : ℕ => u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w)) ⊆
            S_k.filter (fun n : ℕ => Real.exp (u - w) ≤ (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u) := by
          intro n hn
          obtain ⟨hnS, hmem⟩ := mem_filter.mp hn
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hnS).1).1
          refine mem_filter.mpr ⟨hnS, ?_, ?_⟩
          · rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr (by linarith [hmem.2])
          · rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr hmem.1
        have hsum_ind : ∑ n ∈ S_k, (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u =
            ((S_k.filter fun n : ℕ => u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w)).card : ℝ) := by
          have heq : ∑ n ∈ S_k, (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u =
              ∑ _n ∈ S_k.filter (fun n : ℕ => u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w)),
                (1 : ℝ) := by
            symm
            rw [sum_filter (s := S_k)]
            refine sum_congr rfl fun n _ => ?_
            by_cases hm : u ∈ Set.Icc (Real.log (n : ℝ)) (Real.log (n : ℝ) + w) <;> simp [hm]
          rw [heq, sum_const, nsmul_eq_mul, mul_one]
        rw [hsum_ind]
        have hcard := (Nat.cast_le.mpr (card_le_card hsub)).trans
          (card_filter_mem_Icc_real_le S_k (Real.exp_le_exp.mpr (by linarith)))
        have hexpu : Real.exp u ≤ Real.exp 1 * N := by
          calc Real.exp u ≤ Real.exp (Real.log N + w) := Real.exp_le_exp.mpr hu_hi
            _ = (N : ℝ) * Real.exp w := by rw [Real.exp_add, Real.exp_log hNR]
            _ ≤ (N : ℝ) * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hNR.le
            _ = Real.exp 1 * N := by ring
        have hdiff_exp : Real.exp u - Real.exp (u - w) ≤ Real.exp 1 * c := by
          have h1 : 1 - Real.exp (-w) ≤ w := by linarith [Real.add_one_le_exp (-w)]
          have h0 : 0 ≤ 1 - Real.exp (-w) := by
            have := Real.exp_le_one_iff.mpr (show -w ≤ 0 by linarith); linarith
          calc Real.exp u - Real.exp (u - w)
              = Real.exp u * (1 - Real.exp (-w)) := by
                rw [show u - w = u + (-w) by ring, Real.exp_add]; ring
            _ ≤ (Real.exp 1 * N) * w :=
                mul_le_mul hexpu h1 h0 (by positivity)
            _ = Real.exp 1 * c := by simp only [w]; field_simp [hNR.ne']
        linarith only [hcard, hdiff_exp, hc1]
    -- Pointwise Cauchy–Schwarz on `deriv R_k u ^ 2`
    have hpt_sq : ∀ u : ℝ,
        deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2 ≤
          K₀ ^ 2 * ((Real.exp 1 + 1) * c) *
            ∑ n ∈ S_k, y n ^ 2 * (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
      intro u
      have hdsum : deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u =
          ∑ n ∈ S_k, y n * deriv (h_atom n) u := by
        have h0 : HasDerivAt (∑ n ∈ S_k, fun v => y n * h_atom n v)
            (∑ n ∈ S_k, y n * deriv (h_atom n) u) u :=
          HasDerivAt.sum fun n (_ : n ∈ S_k) => ((hh_diff n u).hasDerivAt).const_mul (y n)
        have hfn : (∑ n ∈ S_k, fun v => y n * h_atom n v) =
            fun v => ∑ n ∈ S_k, y n * h_atom n v := by
          ext v; exact Finset.sum_apply v S_k _
        rw [hfn] at h0
        exact h0.deriv
      rw [hdsum]
      let ind : ℕ → ℝ := fun n =>
        (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u
      have hind_sq : ∀ n, ind n ^ 2 = ind n := fun n => by
        simp only [ind]; by_cases hm : u ∈ Set.Icc (Real.log n) (Real.log n + w) <;> simp [hm]
      have hind0 : ∀ n, 0 ≤ ind n := fun n => by
        simp only [ind]; by_cases hm : u ∈ Set.Icc (Real.log n) (Real.log n + w) <;> simp [hm]
      have habs : |∑ n ∈ S_k, y n * deriv (h_atom n) u| ≤
          K₀ * ∑ n ∈ S_k, ind n * (|y n| * ind n) := by
        calc |∑ n ∈ S_k, y n * deriv (h_atom n) u|
            ≤ ∑ n ∈ S_k, |y n * deriv (h_atom n) u| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ n ∈ S_k, |y n| * (K₀ * ind n) :=
              sum_le_sum fun n _ => by
                rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hderiv_atom n u) (abs_nonneg _)
          _ = K₀ * ∑ n ∈ S_k, ind n * (|y n| * ind n) := by
              rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
              rw [show ind n * (|y n| * ind n) = |y n| * ind n ^ 2 by ring, hind_sq n]; ring
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs, mul_pow] at hsq
      have hcs := sum_mul_sq_le_sq_mul_sq S_k ind (fun n => |y n| * ind n)
      calc (∑ n ∈ S_k, y n * deriv (h_atom n) u) ^ 2
          ≤ K₀ ^ 2 * ((∑ n ∈ S_k, ind n ^ 2) * ∑ n ∈ S_k, (|y n| * ind n) ^ 2) :=
            hsq.trans (mul_le_mul_of_nonneg_left hcs (sq_nonneg K₀))
        _ = K₀ ^ 2 * (∑ n ∈ S_k, ind n) * ∑ n ∈ S_k, y n ^ 2 * ind n := by
            simp_rw [mul_pow, sq_abs, hind_sq]; ring
        _ ≤ K₀ ^ 2 * ((Real.exp 1 + 1) * c) * ∑ n ∈ S_k, y n ^ 2 * ind n :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hoverlap u) (sq_nonneg K₀))
              (sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (hind0 n))
    have hint_lhs : Integrable (fun u => deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2) :=
      integrable_sq_of_continuous (hRk_cd.continuous_deriv (by norm_num)) hRk_cs.deriv
    have hint_ind : ∀ n : ℕ,
        Integrable (fun u => y n ^ 2 *
          (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u) := fun n =>
      ((integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator
        measurableSet_Icc).const_mul (y n ^ 2)
    have himono : (∫ u, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2) ≤
        K₀ ^ 2 * ((Real.exp 1 + 1) * c) * (w * ∑ n ∈ S_k, y n ^ 2) := by
      have h1 := integral_mono hint_lhs
        ((integrable_finsetSum S_k fun n _ => hint_ind n).const_mul
          (K₀ ^ 2 * ((Real.exp 1 + 1) * c))) hpt_sq
      have hind_int : ∀ n : ℕ,
          (∫ u, y n ^ 2 * (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u) =
            w * y n ^ 2 := fun n => by
        rw [integral_const_mul, MeasureTheory.integral_indicator measurableSet_Icc, setIntegral_const,
          smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
        ring
      calc (∫ u, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2)
          ≤ ∫ u, K₀ ^ 2 * ((Real.exp 1 + 1) * c) *
              ∑ n ∈ S_k, y n ^ 2 *
                (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := h1
        _ = K₀ ^ 2 * ((Real.exp 1 + 1) * c) *
              ∑ n ∈ S_k, ∫ u, y n ^ 2 *
                (Set.Icc (Real.log n) (Real.log n + w)).indicator (fun _ => (1 : ℝ)) u := by
            rw [integral_const_mul, integral_finsetSum S_k fun n _ => hint_ind n]
        _ = K₀ ^ 2 * ((Real.exp 1 + 1) * c) * (w * ∑ n ∈ S_k, y n ^ 2) := by
            simp_rw [hind_int, ← mul_sum]
    calc levyEnergy (fun v => ∑ n ∈ S_k, y n * h_atom n v)
        ≤ 18 * ∫ u, deriv (fun v => ∑ n ∈ S_k, y n * h_atom n v) u ^ 2 := hlev
      _ ≤ 18 * (K₀ ^ 2 * ((Real.exp 1 + 1) * c) * (w * ∑ n ∈ S_k, y n ^ 2)) :=
          mul_le_mul_of_nonneg_left himono (by norm_num)
      _ = 18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w * ∑ n ∈ S_k, y n ^ 2 := by ring
  -- Sum over `k ∈ s` and swap sums
  have hswap : ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
        y n ^ 2 ≤ 13 * ∑ n ∈ Icc 1 N, y n ^ 2 := by
    have heq : ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
          y n ^ 2 =
        ∑ n ∈ Icc 1 N, ((s.filter fun k => |Real.log (n : ℝ) - shellCenter N k| ≤ 3).card : ℝ) *
          y n ^ 2 := by
      simp_rw [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun n _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul]
    rw [heq, mul_sum]
    refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact (card_shellCenter_near_le s N (Real.log n) (by norm_num : (0 : ℝ) ≤ 3)).trans_eq
      (by norm_num)
  calc ∑ k ∈ s, levyEnergy _
      ≤ ∑ k ∈ s, 18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w *
          ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3), y n ^ 2 :=
        sum_le_sum hshell
    _ = 18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w *
          ∑ k ∈ s, ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => |Real.log (n : ℝ) - shellCenter N k| ≤ 3),
            y n ^ 2 := by
        rw [← mul_sum]
    _ ≤ 18 * K₀ ^ 2 * ((Real.exp 1 + 1) * c) * w * (13 * ∑ n ∈ Icc 1 N, y n ^ 2) :=
        mul_le_mul_of_nonneg_left hswap (by positivity)
    _ = C_comm * c * ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * ∑ n ∈ Icc 1 N, y n ^ 2 := by
        simp only [C_comm, w]
        field_simp [hφ2.ne']

/-! ### Unified shell reserve and the dyadic seventh-power Gamma reserve -/

/-- Unified polynomial band floor `c₀⁸ · (sinh⁸ 1 / (64 · 161⁴)) ≤ c⁸ · splineBandFloor c`
valid across every `c ≥ c₀` (`0 < c₀ ≤ 1`), covering both bounded and growing shell overlaps. -/
theorem splineBandFloor_ge_of_ge {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hc : c₀ ≤ c) :
    c₀ ^ 8 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4)) ≤ c ^ 8 * splineBandFloor c := by
  have hc_pos : 0 < c := hc₀.trans_le hc
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr zero_lt_one
  rcases le_or_gt 1 c with hc1 | hc1
  · have hfl := (div_le_iff₀ (pow_pos hc_pos 8)).mp (splineBandFloor_ge hc1)
    have hc₀8 : c₀ ^ 8 ≤ 1 := pow_le_one₀ hc₀.le hc₀1
    calc c₀ ^ 8 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4))
        ≤ 1 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4)) :=
          mul_le_mul_of_nonneg_right hc₀8 (by positivity)
      _ ≤ c ^ 8 * splineBandFloor c := by linarith
  · have hden : (1 + (101 * c / 8) ^ 2) ^ 4 ≤ 161 ^ 4 := by
      have h1 : 1 + (101 * c / 8) ^ 2 ≤ 161 := by nlinarith [hc1.le]
      exact pow_le_pow_left₀ (by positivity) h1 4
    have hfl : Real.sinh 1 ^ 8 / (64 * 161 ^ 4) ≤ splineBandFloor c := by
      unfold splineBandFloor
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hden (by norm_num))
    exact mul_le_mul (pow_le_pow_left₀ hc₀.le hc 8) hfl (by positivity) (pow_nonneg hc_pos.le 8)

/-- Explicit positive constant of the dyadic seventh-power top-collar reserve. -/
def dyadicTopMassConstant : ℝ :=
  (1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7)

theorem dyadicTopMassConstant_pos : 0 < dyadicTopMassConstant := by
  have := growingMassConstant_pos
  unfold dyadicTopMassConstant
  positivity

/-- Lévy-energy reserve on a single shell `F_k` at effective overlap `c_k ∈ [1/2052, N_k]`. -/
theorem levyEnergy_atomicTest_ge_of_ge {c : ℝ} (hc0 : 1 / 2052 ≤ c) {N : ℕ} (hcN : c ≤ N)
    (z : ℕ → ℝ) :
    (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) * Real.log N -
        (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
          (1 + 2 * Real.exp 1 * c)) *
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (∑ n ∈ Icc 1 N, z n ^ 2) ≤
      levyEnergy (atomicTest N z (atomDilate tiltedUnitSpline (c / N))) := by
  have hc_pos : 0 < c := lt_of_lt_of_le (by norm_num) hc0
  have hNR : (0 : ℝ) < N := hc_pos.trans_le hcN
  have hN1 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    subst this; simp at hNR
  have hw : 0 < c / (N : ℝ) := div_pos hc_pos hNR
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
  have hf := contDiff_atomicTest hg N z
  have hfc := hasCompactSupport_atomicTest hgsupp N z
  have hgamma := archForm_ge_log_band_sub_mass hf hfc hNR
  have hband := noRealZero_highBand_mass contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hc_pos
    (splineBandFloor_pos c) (tiltedUnitSpline_band_floor hc_pos) hN1 z
  have hmass := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc_pos hcN hgsupp z
  rw [integral_atomDilate_sq hw] at hmass
  have hlev_eq := archForm_eq_levyEnergy hf hfc
  have hM := integral_tiltedUnitSpline_sq_pos
  have hZ : 0 ≤ ∑ n ∈ Icc 1 N, z n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hfl := splineBandFloor_ge_of_ge (by norm_num : (0 : ℝ) < 1 / 2052) (by norm_num) hc0
  have hcoef : ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) *
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤
      1 / (2 * Real.pi) * (48 * (c / N) ^ 2 * splineBandFloor c * N) := by
    have hl : ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) *
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) =
        24 * ((1 / 2052 : ℝ) ^ 8 * (Real.sinh 1 ^ 8 / (64 * 161 ^ 4))) /
          (Real.pi * c ^ 6 * N) := by
      unfold growingMassConstant
      field_simp [hM.ne', hNR.ne', hc_pos.ne', Real.pi_ne_zero]
    have hr : 1 / (2 * Real.pi) * (48 * (c / N) ^ 2 * splineBandFloor c * N) =
        24 * (c ^ 8 * splineBandFloor c) / (Real.pi * c ^ 6 * N) := by
      field_simp [hNR.ne', hc_pos.ne', Real.pi_ne_zero]; ring
    rw [hl, hr]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfl (by norm_num)) (by positivity)
  have hbandTerm : ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) * Real.log N *
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (∑ n ∈ Icc 1 N, z n ^ 2) ≤
      Real.log N / (2 * Real.pi) * ∫ t in (N : ℝ)..101 * N,
        ‖Zeta23.paperFT (ArithmeticCastelnuovoSeveri.cx
          (atomicTest N z (atomDilate tiltedUnitSpline (c / N)))) (t : ℂ)‖ ^ 2 := by
    calc _ = Real.log N * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) *
          ((c / N) * ∫ u, tiltedUnitSpline u ^ 2)) * (∑ n ∈ Icc 1 N, z n ^ 2) := by ring
      _ ≤ Real.log N * (1 / (2 * Real.pi) * (48 * (c / N) ^ 2 * splineBandFloor c * N)) *
          (∑ n ∈ Icc 1 N, z n ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hlogN) hZ
      _ = Real.log N / (2 * Real.pi) *
          ((48 * (c / N) ^ 2 * splineBandFloor c * N) * (∑ n ∈ Icc 1 N, z n ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hband (by positivity)
  have hf_nn : 0 ≤ ∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hγ : 2 * gammaHardyPhaseRate 0 *
      (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) ≤
      2 * |gammaHardyPhaseRate 0| *
        (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) zero_le_two) hf_nn
  have hcost_coef : 0 ≤ factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0| :=
    add_nonneg (add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg one_le_two))
      (by positivity)
  have hcost := mul_le_mul_of_nonneg_left hmass hcost_coef
  have hid1 : (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
      (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) =
      (factorialSpanGammaOffset + Real.log 2) *
        (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) +
      2 * |gammaHardyPhaseRate 0| *
        (∫ u, atomicTest N z (atomDilate tiltedUnitSpline (c / N)) u ^ 2) := by ring
  have hid2 : (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) * Real.log N -
        (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
          (1 + 2 * Real.exp 1 * c)) *
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (∑ n ∈ Icc 1 N, z n ^ 2) =
      ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / c ^ 7) * Real.log N *
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (∑ n ∈ Icc 1 N, z n ^ 2) -
      (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
        (((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (1 + 2 * Real.exp 1 * c) *
          (∑ n ∈ Icc 1 N, z n ^ 2)) := by ring
  linarith only [hgamma, hlev_eq, hbandTerm, hγ, hcost, hid1, hid2]

/-- **Dyadic seventh-power archimedean reserve on the top collar.** Summing the shell reserves via
smooth IMS and subtracting the `H¹` commutator upgrades the top `archForm` floor to
`topCollarSeventhMass` at only linear `O(c)` mass cost. -/
theorem exists_top_archForm_dyadic_seventh_reserve :
    ∃ C_arch : ℝ, 0 ≤ C_arch ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → (linearDefectCutoff c : ℝ) ^ 2 ≤ N → ∀ x : ℕ → ℝ,
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
          ((dyadicTopMassConstant / c ^ 7) * Real.log N *
              topCollarSeventhMass (N / linearDefectCutoff c) N x -
            C_arch * c * topCollarSeventhMass (N / linearDefectCutoff c) N x) ≤
          archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨L_B, hLB0, -, hlipB⟩ := exists_baseShellBump_deriv_bound
  obtain ⟨C_comm, hCcomm0, hcomm⟩ := exists_sum_levyEnergy_dyadicCommutator_le
  let K_low := (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
    (1 + 8 * Real.exp 1)
  have hKlow0 : 0 ≤ K_low :=
    mul_nonneg (add_nonneg (add_nonneg factorialSpanGammaOffset_nonneg
      (Real.log_nonneg one_le_two)) (by positivity)) (by positivity)
  let C_arch := (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) / 18 +
    2 * |gammaHardyPhaseRate 0| * (1 + 2 * Real.exp 1)
  refine ⟨C_arch, by simp only [C_arch]; positivity, ?_⟩
  intro c N hc1 hL2N x
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc1
  let Lc := linearDefectCutoff c
  let M := N / Lc
  have hL_pos : 0 < Lc := by omega
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLc_R : (3 : ℝ) ≤ Lc := by exact_mod_cast hL3
  have hNR : (9 : ℝ) ≤ N := (by norm_num : (9 : ℝ) ≤ 3 ^ 2).trans
    ((pow_le_pow_left₀ (by norm_num) hLc_R 2).trans hL2N)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < N := by linarith
  have hcN : c ≤ (N : ℝ) := by nlinarith [h4c]
  have hMN : M ≤ N := Nat.div_le_self N Lc
  let w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hN_pos
  let g := atomDilate tiltedUnitSpline w
  let G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  let y := atomicTailCoefficients M x
  have hy_eq : ∑ n ∈ Icc 1 N, y n ^ 2 = ∑ n ∈ Ioc M N, x n ^ 2 :=
    sum_atomicTailCoefficients_sq_eq_Ioc' hMN x
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hfy : ContDiff ℝ 2 (atomicTest N y g) := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport (atomicTest N y g) := hasCompactSupport_atomicTest hsupp N y
  let s := range (dyadicShellCount c)
  -- Shell bounds for every `k ∈ s`
  have h2k_le : ∀ k ∈ s, (2 : ℝ) ^ k ≤ Lc := by
    intro k hk
    have hk_le : (k : ℝ) ≤ Real.log Lc / Real.log 2 := by
      have hk_nat : k ≤ ⌊Real.log Lc / Real.log 2⌋₊ := Nat.lt_succ_iff.mp (mem_range.mp hk)
      exact (Nat.cast_le.mpr hk_nat).trans (Nat.floor_le
        (div_nonneg (Real.log_nonneg (by linarith)) (Real.log_pos one_lt_two).le))
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hmul : (k : ℝ) * Real.log 2 ≤ Real.log Lc := (le_div_iff₀ hl2).mp hk_le
    calc (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
          rw [← Real.log_pow, Real.exp_log (by positivity)]
      _ ≤ Real.exp (Real.log Lc) := Real.exp_le_exp.mpr hmul
      _ = Lc := Real.exp_log (by linarith)
  have hshell_lev : ∀ k ∈ s,
      (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
          (Real.log N / 2) - K_low * c) * G *
        (∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) ≤
      levyEnergy (atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g) := by
    intro k hk
    have h2k := h2k_le k hk
    let Nk := dyadicShellHorizon N k
    have hsqrt_le : Real.sqrt N ≤ Nk := by
      have hsq : Real.sqrt N * Lc ≤ N := by
        have h1 : (Lc : ℝ) ≤ Real.sqrt N := by
          rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ Lc)]
          exact Real.sqrt_le_sqrt hL2N
        calc Real.sqrt N * Lc ≤ Real.sqrt N * Real.sqrt N :=
              mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
          _ = N := Real.mul_self_sqrt hN_pos.le
      have h4N : Real.sqrt N + 1 ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k := by
        have hdiv : Real.sqrt N ≤ (N : ℝ) / (2 : ℝ) ^ k := by
          rw [le_div_iff₀ (by positivity)]
          exact (mul_le_mul_of_nonneg_left h2k (Real.sqrt_nonneg _)).trans hsq
        have hsq3 : 3 ≤ Real.sqrt N := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
          exact Real.sqrt_le_sqrt (by linarith)
        calc Real.sqrt N + 1 ≤ 4 * Real.sqrt N := by linarith only [hsq3]
          _ ≤ 4 * ((N : ℝ) / (2 : ℝ) ^ k) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
          _ = 4 * (N : ℝ) / (2 : ℝ) ^ k := (mul_div_assoc _ _ _).symm
      have hfl : Real.sqrt N ≤ ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊ := by
        have := Nat.lt_floor_add_one (4 * (N : ℝ) / (2 : ℝ) ^ k)
        linarith
      have hN_sq : Real.sqrt N ≤ N := by
        have hsq1 : 1 ≤ Real.sqrt N := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
        calc Real.sqrt N = Real.sqrt N * 1 := (mul_one _).symm
          _ ≤ Real.sqrt N * Real.sqrt N := mul_le_mul_of_nonneg_left hsq1 (Real.sqrt_nonneg _)
          _ = N := Real.mul_self_sqrt hN_pos.le
      simp only [Nk, dyadicShellHorizon]
      rw [Nat.cast_min, le_min_iff]
      exact ⟨hN_sq, hfl⟩
    have hNk_lb : (N : ℝ) / (2 : ℝ) ^ k ≤ Nk := by
      have hdiv3 : 3 ≤ (N : ℝ) / (2 : ℝ) ^ k := by
        rw [le_div_iff₀ (by positivity)]
        have : 3 * (2 : ℝ) ^ k ≤ (Lc : ℝ) * Lc :=
          mul_le_mul hLc_R h2k (by positivity) (by linarith)
        nlinarith [hL2N]
      have hfl : (N : ℝ) / (2 : ℝ) ^ k ≤ ⌊4 * (N : ℝ) / (2 : ℝ) ^ k⌋₊ := by
        have h4 : (N : ℝ) / (2 : ℝ) ^ k + 1 ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k := by
          calc (N : ℝ) / (2 : ℝ) ^ k + 1 ≤ 4 * ((N : ℝ) / (2 : ℝ) ^ k) := by linarith only [hdiv3]
            _ = 4 * (N : ℝ) / (2 : ℝ) ^ k := (mul_div_assoc _ _ _).symm
        have := Nat.lt_floor_add_one (4 * (N : ℝ) / (2 : ℝ) ^ k)
        linarith
      have hN_div : (N : ℝ) / (2 : ℝ) ^ k ≤ N :=
        div_le_self hN_pos.le (one_le_pow₀ one_le_two)
      simp only [Nk, dyadicShellHorizon]
      rw [Nat.cast_min, le_min_iff]
      exact ⟨hN_div, hfl⟩
    have hNk_ub : (Nk : ℝ) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k :=
      (Nat.cast_le.mpr (min_le_right N _)).trans (Nat.floor_le (by positivity))
    let ck := c * (Nk : ℝ) / N
    have hNk_pos : (0 : ℝ) < Nk := lt_of_lt_of_le (Real.sqrt_pos.mpr hN_pos) hsqrt_le
    have hck_min : 1 / 2052 ≤ ck := by
      have he2 : Real.exp 2 < 8 := by
        have he1 : Real.exp 1 < 11 / 4 := by have := Real.exp_one_lt_d9; linarith
        have he2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [he2']; nlinarith [Real.exp_pos 1]
      have hLc_ub : (Lc : ℝ) ≤ 2052 * c := by nlinarith [hLup, hc0]
      have h1 : c / (2 : ℝ) ^ k ≤ ck := by
        simp only [ck]
        rw [div_le_div_iff₀ (by positivity) hN_pos]
        have := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity)).mp hNk_lb) hc0.le
        linarith
      have h2 : 1 / 2052 ≤ c / (2 : ℝ) ^ k := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity), one_mul]
        linarith only [h2k, hLc_ub]
      exact h2.trans h1
    have hck_4c : ck ≤ 4 * c := by
      simp only [ck]
      rw [div_le_iff₀ hN_pos]
      have : (Nk : ℝ) ≤ 4 * N := hNk_ub.trans
        (div_le_self (by positivity) (one_le_pow₀ one_le_two))
      nlinarith
    have hck_Nk : ck ≤ Nk := by
      simp only [ck]
      rw [div_le_iff₀ hN_pos]
      nlinarith [hcN, hNk_pos]
    have hck_div : ck / Nk = w := by
      simp only [ck, w]
      field_simp [hN_pos.ne', hNk_pos.ne']
    have hlogNk : Real.log N / 2 ≤ Real.log Nk := by
      have h1 := Real.log_le_log (Real.sqrt_pos.mpr hN_pos) hsqrt_le
      rwa [Real.log_sqrt hN_pos.le] at h1
    have hsum_eq : ∑ n ∈ Icc 1 Nk, (dyadicShellBump N k (Real.log n) * y n) ^ 2 =
        ∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2 := by
      have hsub := sum_subset (Icc_subset_Icc (le_rfl : 1 ≤ 1) (min_le_left N _))
        (f := fun n : ℕ => dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) fun n hn hnot => by
          obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
          have hgt : Nk < n := by
            by_contra hle; exact hnot (mem_Icc.mpr ⟨hn1, not_lt.mp hle⟩)
          rw [dyadicShellBump_log_eq_zero_of_gt_horizon hN1 hnN hgt, sq, zero_mul, zero_mul]
      rw [← hsub]
      exact sum_congr rfl fun n _ => mul_pow _ _ 2
    have hlev0 := levyEnergy_atomicTest_ge_of_ge hck_min hck_Nk
      (fun n => dyadicShellBump N k (Real.log n) * y n)
    rw [hck_div, hsum_eq] at hlev0
    refine le_trans ?_ hlev0
    have hZ : 0 ≤ ∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2 :=
      sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hG.le) hZ
    have hpos_gain : ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / ck ^ 7) * (Real.log N / 2) ≤
        ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / ck ^ 7) * Real.log Nk :=
      mul_le_mul_of_nonneg_left hlogNk
        (div_nonneg (mul_nonneg (by norm_num) growingMassConstant_pos.le)
          (pow_nonneg (lt_of_lt_of_le (by norm_num) hck_min).le 7))
    have hneg_cost : (factorialSpanGammaOffset + Real.log 2 + 2 * |gammaHardyPhaseRate 0|) *
        (1 + 2 * Real.exp 1 * ck) ≤ K_low * c := by
      have h1 : 2 * Real.exp 1 * ck ≤ 8 * Real.exp 1 * c :=
        (mul_le_mul_of_nonneg_left hck_4c
          (mul_nonneg zero_le_two (Real.exp_pos 1).le)).trans_eq (by ring)
      have h2 : 1 + 2 * Real.exp 1 * ck ≤ (1 + 8 * Real.exp 1) * c := by
        linarith only [hc1, h1]
      have h3 := mul_le_mul_of_nonneg_left h2
        (add_nonneg (add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg one_le_two))
          (mul_nonneg zero_le_two (abs_nonneg (gammaHardyPhaseRate 0))))
      exact h3.trans_eq (by simp only [K_low]; ring)
    linarith only [hpos_gain, hneg_cost]
  -- Coverage of `(M, N]` by the dyadic shells
  have hcov : ∀ n ∈ Ioc M N,
      (((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7)) ≤
        ∑ k ∈ s, (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
          dyadicShellBump N k (Real.log n) ^ 2 := by
    intro n hn
    obtain ⟨hMn, hnN⟩ := mem_Ioc.mp hn
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) hMn)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hrat1 : 1 ≤ (N : ℝ) / n := (one_le_div hn0).mpr (by exact_mod_cast hnN)
    have hrat_lt : (N : ℝ) / n < Lc := by
      rw [div_lt_iff₀ hn0]
      have h1 : N < Lc * (M + 1) := Nat.lt_mul_div_succ N hL_pos
      have h2 : Lc * (M + 1) ≤ Lc * n := Nat.mul_le_mul_left Lc hMn
      have h3 : (N : ℝ) < (Lc : ℝ) * n := by exact_mod_cast h1.trans_le h2
      linarith only [h3, (by ring : (Lc : ℝ) * n = (Lc : ℝ) * (n : ℝ))]
    let t := Real.log ((N : ℝ) / n) / Real.log 2
    have ht0 : 0 ≤ t := div_nonneg (Real.log_nonneg hrat1) hl2.le
    let k₀ := ⌊t⌋₊
    have hk₀_mem : k₀ ∈ s := by
      refine mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono ?_))
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (lt_of_lt_of_le zero_lt_one hrat1) hrat_lt.le) hl2.le
    have hk₀_lo : (k₀ : ℝ) * Real.log 2 ≤ Real.log N - Real.log n := by
      rw [← Real.log_div hN_pos.ne' hn0.ne']
      exact (le_div_iff₀ hl2).mp (Nat.floor_le ht0)
    have hk₀_hi : Real.log N - Real.log n < ((k₀ : ℝ) + 1) * Real.log 2 := by
      rw [← Real.log_div hN_pos.ne' hn0.ne']
      exact (div_lt_iff₀ hl2).mp (Nat.lt_floor_add_one t)
    have hbump1 : dyadicShellBump N k₀ (Real.log n) = 1 := by
      apply dyadicShellBump_eq_one
      have hid : Real.log n - shellCenter N k₀ =
          ((k₀ : ℝ) + 1) * Real.log 2 - (Real.log N - Real.log n) := by
        unfold shellCenter; ring
      rw [hid, abs_of_nonneg (by linarith)]
      have hl2_le1 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hck₀_ub : c * (dyadicShellHorizon N k₀ : ℝ) / N ≤ 8 * c * n / N := by
      have h2k₀_gt : (N : ℝ) / n < 2 * (2 : ℝ) ^ k₀ := by
        have hexp := Real.exp_lt_exp.mpr hk₀_hi
        rw [Real.exp_sub, Real.exp_log hN_pos, Real.exp_log hn0, add_mul, one_mul,
          Real.exp_add, Real.exp_log zero_lt_two,
          show (k₀ : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k₀) by rw [Real.log_pow],
          Real.exp_log (by positivity)] at hexp
        linarith
      have hNk₀ : (dyadicShellHorizon N k₀ : ℝ) ≤ 8 * n := by
        have h1 : (dyadicShellHorizon N k₀ : ℝ) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k₀ :=
          (Nat.cast_le.mpr (min_le_right N _)).trans (Nat.floor_le (by positivity))
        have h2 : 4 * (N : ℝ) / (2 : ℝ) ^ k₀ ≤ 8 * n := by
          rw [div_le_iff₀ (by positivity)]
          have := (div_lt_iff₀ hn0).mp h2k₀_gt
          linarith
        exact h1.trans h2
      calc c * (dyadicShellHorizon N k₀ : ℝ) / N
          ≤ c * (8 * n) / N := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hNk₀ hc0.le) hN_pos.le
        _ = 8 * c * n / N := by ring
    have hNk₀_pos : (0 : ℝ) < dyadicShellHorizon N k₀ := by
      have hdiv1 : (1 : ℝ) ≤ 4 * (N : ℝ) / (2 : ℝ) ^ k₀ := by
        rw [one_le_div (by positivity)]
        have hLc_4N : (Lc : ℝ) ≤ 4 * N := by nlinarith only [hLc_R, hL2N]
        exact (h2k_le k₀ hk₀_mem).trans hLc_4N
      have hpos : 1 ≤ dyadicShellHorizon N k₀ := le_min hN1 ((Nat.one_le_floor_iff _).mpr hdiv1)
      exact_mod_cast hpos
    have hsingle : (1 / (c * (dyadicShellHorizon N k₀ : ℝ) / N) ^ 7) *
          dyadicShellBump N k₀ (Real.log n) ^ 2 ≤
        ∑ k ∈ s, (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
          dyadicShellBump N k (Real.log n) ^ 2 :=
      single_le_sum (f := fun k => (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
          dyadicShellBump N k (Real.log n) ^ 2)
        (fun k _ => mul_nonneg (one_div_nonneg.mpr (pow_nonneg (by positivity) 7)) (sq_nonneg _))
        hk₀_mem
    refine le_trans ?_ hsingle
    rw [hbump1, one_pow, mul_one]
    have hpow := pow_le_pow_left₀ (by positivity) hck₀_ub 7
    have hid : ((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7) = 1 / (8 * c * n / N) ^ 7 := by
      field_simp [hN_pos.ne', hn0.ne', hc0.ne']
    rw [hid]
    exact one_div_le_one_div_of_le (by positivity) hpow
  -- Sum the shell Lévy energies
  have hsum_F : G * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (2 * 8 ^ 7 * c ^ 7)) *
        Real.log N * topCollarSeventhMass M N x -
        9 * K_low * c * ∑ n ∈ Ioc M N, x n ^ 2) ≤
      ∑ k ∈ s, levyEnergy (atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g) := by
    refine le_trans ?_ (sum_le_sum hshell_lev)
    have hswap : ∑ k ∈ s,
          (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
            (Real.log N / 2) - K_low * c) * G *
          (∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2) =
        G * ((1 / 2052 : ℝ) ^ 8 * growingMassConstant * (Real.log N / 2) *
          (∑ n ∈ Ioc M N, (∑ k ∈ s, (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
            dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2) -
          K_low * c * ∑ n ∈ Ioc M N,
            (∑ k ∈ s, dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2) := by
      have hrestrict : ∀ k : ℕ,
          ∑ n ∈ Icc 1 N, dyadicShellBump N k (Real.log n) ^ 2 * y n ^ 2 =
            ∑ n ∈ Ioc M N, dyadicShellBump N k (Real.log n) ^ 2 * x n ^ 2 := fun k => by
        have hIoc : (Ioc M N : Finset ℕ) ⊆ Icc 1 N := fun n hn =>
          mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) (mem_Ioc.mp hn).1),
            (mem_Ioc.mp hn).2⟩
        rw [← sum_subset hIoc fun n hn hnot => by
          have hle : n ≤ M := by
            by_contra hgt; exact hnot (mem_Ioc.mpr ⟨not_le.mp hgt, (mem_Icc.mp hn).2⟩)
          have hy0 : y n = 0 := if_neg (Nat.not_lt.mpr hle)
          rw [hy0]; ring]
        exact sum_congr rfl fun n hn => by
          have hyx : y n = x n := if_pos (mem_Ioc.mp hn).1
          rw [hyx]
      simp_rw [hrestrict, sub_mul, mul_sum]
      rw [sum_sub_distrib, mul_sub]
      congr 1
      · rw [sum_comm, mul_sum]
        refine sum_congr rfl fun n _ => ?_
        rw [sum_mul, mul_sum, mul_sum]
        exact sum_congr rfl fun k _ => by ring
      · rw [sum_comm, mul_sum]
        refine sum_congr rfl fun n _ => ?_
        rw [sum_mul, mul_sum, mul_sum]
        exact sum_congr rfl fun k _ => by ring
    rw [hswap]
    refine mul_le_mul_of_nonneg_left (sub_le_sub ?_ ?_) hG.le
    · have h1 : ∑ n ∈ Ioc M N, (((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7)) * x n ^ 2 ≤
          ∑ n ∈ Ioc M N, (∑ k ∈ s, (1 / (c * (dyadicShellHorizon N k : ℝ) / N) ^ 7) *
            dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2 :=
        sum_le_sum fun n hn => mul_le_mul_of_nonneg_right (hcov n hn) (sq_nonneg _)
      have hlog0 : 0 ≤ (1 / 2052 : ℝ) ^ 8 * growingMassConstant * (Real.log N / 2) := by
        have := growingMassConstant_pos
        have := Real.log_natCast_nonneg N
        positivity
      calc ((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (2 * 8 ^ 7 * c ^ 7)) *
            Real.log N * topCollarSeventhMass M N x
          = (1 / 2052 : ℝ) ^ 8 * growingMassConstant * (Real.log N / 2) *
              ∑ n ∈ Ioc M N, (((N : ℝ) / n) ^ 7 / (8 ^ 7 * c ^ 7)) * x n ^ 2 := by
            unfold topCollarSeventhMass
            rw [mul_sum, mul_sum]
            refine sum_congr rfl fun n _ => ?_
            field_simp [hc0.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 hlog0
    · have hsum9 : ∑ n ∈ Ioc M N, (∑ k ∈ s, dyadicShellBump N k (Real.log n) ^ 2) * x n ^ 2 ≤
          9 * ∑ n ∈ Ioc M N, x n ^ 2 := by
        rw [mul_sum]
        refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        calc ∑ k ∈ s, dyadicShellBump N k (Real.log n) ^ 2
            ≤ ∑ k ∈ s, (if |Real.log n - shellCenter N k| ≤ 2 then (1 : ℝ) else 0) :=
              sum_le_sum fun k _ => by
                split_ifs with hle
                · nlinarith [dyadicShellBump_nonneg N k (Real.log n),
                    dyadicShellBump_le_one N k (Real.log n)]
                · rw [dyadicShellBump_eq_zero (le_of_not_ge hle), sq, zero_mul]
          _ ≤ 9 := by
              rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
              exact (card_shellCenter_near_le s N (Real.log n) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
                (by norm_num)
      exact (mul_le_mul_of_nonneg_left hsum9 (mul_nonneg hKlow0 hc0.le)).trans_eq (by ring)
  -- Relate `∑ levyEnergy F_k` to `levyEnergy f_y` via triangle + IMS + commutator
  have htri_sum : (1 / 2 : ℝ) * ∑ k ∈ s, levyEnergy (atomicTest (dyadicShellHorizon N k)
        (fun n => dyadicShellBump N k (Real.log n) * y n) g) -
      ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u -
        atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g u) ≤
      ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun k _ => ?_
    let a_k : ℝ → ℝ := fun u => dyadicShellBump N k u * atomicTest N y g u
    let F_k : ℝ → ℝ := atomicTest (dyadicShellHorizon N k)
      (fun n => dyadicShellBump N k (Real.log n) * y n) g
    have hak : ContDiff ℝ 2 a_k := (contDiff_dyadicShellBump N k).mul hfy
    have hakc : HasCompactSupport a_k := hfyc.mul_left
    have hFk : ContDiff ℝ 2 F_k := contDiff_atomicTest hg _ _
    have hFkc : HasCompactSupport F_k := hasCompactSupport_atomicTest hsupp _ _
    have heq : F_k = fun u => a_k u - (a_k u - F_k u) := funext fun _ => by ring
    have hsub := levyEnergy_sub_le_two_mul hak hakc (hak.sub hFk) (hakc.sub hFkc)
    rw [← heq] at hsub
    linarith only [hsub]
  have hims := sum_levyEnergy_dyadicShellBump_mul_le hlipB s N hfy hfyc
  have hcomm_s := hcomm hc1 hcN s y
  clear hcomm hshell_lev hcov
  rw [hy_eq] at hcomm_s
  have hfy2 : ∫ u, atomicTest N y g u ^ 2 ≤
      G * ((1 + 2 * Real.exp 1) * c) * ∑ n ∈ Ioc M N, x n ^ 2 := by
    have h0 := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc0 hcN hsupp y
    rw [integral_atomDilate_sq hw, hy_eq] at h0
    refine h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hG.le)
      (sum_nonneg fun _ _ => sq_nonneg _))
    nlinarith only [hc1, Real.exp_pos 1]
  have harch_eq := archForm_eq_levyEnergy hfy hfyc
  have hγ_fy : -2 * |gammaHardyPhaseRate 0| * ∫ u, atomicTest N y g u ^ 2 ≤
      2 * gammaHardyPhaseRate 0 * ∫ u, atomicTest N y g u ^ 2 := by
    have hf0 : 0 ≤ ∫ u, atomicTest N y g u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have habs_rate : -2 * |gammaHardyPhaseRate 0| ≤ 2 * gammaHardyPhaseRate 0 := by
      have := neg_abs_le (gammaHardyPhaseRate 0); linarith only [this]
    exact mul_le_mul_of_nonneg_right habs_rate hf0
  have hS_le_S7 := sum_sq_Ioc_le_topCollarSeventhMass M N x
  have hS7_0 := topCollarSeventhMass_nonneg M N x
  -- Combine all pieces into `archForm (atomicTest N y g)`
  have hlev_fy : G * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7)) *
        Real.log N * topCollarSeventhMass M N x -
        ((9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) / 18) *
          c * topCollarSeventhMass M N x) ≤
      levyEnergy (atomicTest N y g) := by
    have h18 : 18 * levyEnergy (atomicTest N y g) ≥
        (1 / 2 : ℝ) * ∑ k ∈ s, levyEnergy (atomicTest (dyadicShellHorizon N k)
          (fun n => dyadicShellBump N k (Real.log n) * y n) g) -
        ∑ k ∈ s, levyEnergy (fun u => dyadicShellBump N k u * atomicTest N y g u -
          atomicTest (dyadicShellHorizon N k)
            (fun n => dyadicShellBump N k (Real.log n) * y n) g u) -
        648 * L_B ^ 2 * ∫ u, atomicTest N y g u ^ 2 := by
      linarith only [htri_sum, hims]
    have h648 := mul_le_mul_of_nonneg_left hfy2
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 648) (sq_nonneg L_B))
    have hhalf := mul_le_mul_of_nonneg_left hsum_F (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hcost_S : (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) * c * G *
        (∑ n ∈ Ioc M N, x n ^ 2) ≤
        (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) * c * G *
          topCollarSeventhMass M N x :=
      mul_le_mul_of_nonneg_left hS_le_S7
        (mul_nonneg (mul_nonneg (add_nonneg (add_nonneg (by linarith only [hKlow0]) hCcomm0)
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 648) (sq_nonneg L_B))
            (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 1).le)))) hc0.le) hG.le)
    have hid_combine := (fun (G' S S7 L e1 : ℝ) =>
        (by ring :
          (1 / 2 : ℝ) * (G' * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (2 * 8 ^ 7 * c ^ 7)) *
              L * S7 - 9 * K_low * c * S)) -
            C_comm * c * G' * S -
            648 * L_B ^ 2 * (G' * ((1 + 2 * e1) * c) * S) =
          18 * (G' * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7)) *
              L * S7)) -
            (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * e1)) * c * G' * S))
      G (∑ n ∈ Ioc M N, x n ^ 2) (topCollarSeventhMass M N x) (Real.log N) (Real.exp 1)
    have hid_rhs := (fun (G' S7 L e1 : ℝ) =>
        (by ring :
          18 * (G' * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7)) *
              L * S7 -
              ((9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * e1)) / 18) *
                c * S7)) =
          18 * (G' * (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7)) *
              L * S7)) -
            (9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * e1)) * c * G' * S7))
      G (topCollarSeventhMass M N x) (Real.log N) (Real.exp 1)
    linarith only [h18, hhalf, hcomm_s, h648, hcost_S, hid_combine, hid_rhs]
  have hγ_S7 : 2 * |gammaHardyPhaseRate 0| * ∫ u, atomicTest N y g u ^ 2 ≤
      G * (2 * |gammaHardyPhaseRate 0| * (1 + 2 * Real.exp 1) * c * topCollarSeventhMass M N x) := by
    have hγ0 : 0 ≤ 2 * |gammaHardyPhaseRate 0| :=
      mul_nonneg zero_le_two (abs_nonneg (gammaHardyPhaseRate 0))
    have h1 := mul_le_mul_of_nonneg_left hfy2 hγ0
    have h2 := mul_le_mul_of_nonneg_left hS_le_S7
      (mul_nonneg hγ0 (mul_nonneg hG.le
        (mul_nonneg (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 1).le)) hc0.le)))
    have hid1 := (fun (a G' b S : ℝ) => (by ring : a * (G' * b * S) = a * (G' * b) * S))
      (2 * |gammaHardyPhaseRate 0|) G ((1 + 2 * Real.exp 1) * c) (∑ n ∈ Ioc M N, x n ^ 2)
    have hid2 := (fun (a G' e1 S7 : ℝ) =>
        (by ring : a * (G' * ((1 + 2 * e1) * c)) * S7 = G' * (a * (1 + 2 * e1) * c * S7)))
      (2 * |gammaHardyPhaseRate 0|) G (Real.exp 1) (topCollarSeventhMass M N x)
    linarith only [h1, h2, hid1, hid2]
  have hid_const : dyadicTopMassConstant / c ^ 7 =
      (1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7) := by
    unfold dyadicTopMassConstant; field_simp [hc0.ne']
  rw [hid_const, harch_eq]
  have hid_arch := (fun (G' A S7 B1 B2 : ℝ) =>
      (by ring : G' * (A * S7 - (B1 + B2) * c * S7) =
        G' * (A * S7 - B1 * c * S7) - G' * (B2 * c * S7)))
    G (((1 / 2052 : ℝ) ^ 8 * growingMassConstant / (72 * 8 ^ 7 * c ^ 7)) * Real.log N)
    (topCollarSeventhMass M N x)
    ((9 * K_low / 2 + C_comm + 648 * L_B ^ 2 * (1 + 2 * Real.exp 1)) / 18)
    (2 * |gammaHardyPhaseRate 0| * (1 + 2 * Real.exp 1))
  rw [hid_arch]
  have hid_neg := (fun (a I : ℝ) => (by ring : -2 * a * I = -(2 * a * I)))
    |gammaHardyPhaseRate 0| (∫ u, atomicTest N y g u ^ 2)
  linarith only [hγ_fy, hγ_S7, hlev_fy, hid_neg]

/-! ### Logarithm-free prime self-form bound on the top collar -/

/-- Explicit constant for the `log c`-free top-collar prime self-form bound. -/
def topPrimeSeventhConstant : ℝ := 6 * Real.exp 7 + Real.exp 6 + 7

theorem topPrimeSeventhConstant_pos : 0 < topPrimeSeventhConstant := by
  unfold topPrimeSeventhConstant; positivity

/-- **Logarithm-free prime self-form bound on the top collar.** Weighted by `topCollarSeventhMass`,
the prime self-form of the top atomic test costs at most `O(c)` per unit atom mass, with no `log c`
factor. -/
theorem abs_primeSum_top_le_seventh {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ}
    (hLN : linearDefectCutoff c ≤ N) (x : ℕ → ℝ) :
    |primeSum (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
        (atomDilate tiltedUnitSpline (c / N)))| ≤
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * topPrimeSeventhConstant * c *
        topCollarSeventhMass (N / linearDefectCutoff c) N x := by
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  set M := N / linearDefectCutoff c
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by omega
  have hMltN : M < N := Nat.div_lt_self (by omega) (by omega)
  have hMN : M ≤ N := hMltN.le
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  set w := c / (N : ℝ)
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  set g := atomDilate tiltedUnitSpline w
  set G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  set y := atomicTailCoefficients M x
  set K := ⌈(N : ℝ) * Real.exp w⌉₊ + 1
  have hfin : primeSum (atomicTest N y g) =
      ∑ k ∈ range K, vonMangoldtAtom k * lagForm g N k y := by
    rw [primeSum_atomicTest_eq_lags hg.continuous hgc]
    refine tsum_eq_sum fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    have hbig : (N : ℝ) * Real.exp w < k := by
      have := Nat.le_ceil ((N : ℝ) * Real.exp w)
      have h2 : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at h2; linarith
    have hlog : Real.log N + w < Real.log k := by
      rw [← Real.log_exp w, ← Real.log_mul hNR.ne' (Real.exp_pos w).ne']
      exact Real.log_lt_log (by positivity) hbig
    rw [lagForm_eq_zero_of_log_lt hsupp hw.le hlog, mul_zero]
  -- Reduce to `2 Σ_k vonMangoldtAtom k Σ_{m, n ∈ Ioc M N} |x_m| |x_n| lagWin w k m n`
  have hstep1 : |primeSum (atomicTest N y g)| ≤
      G * ∑ k ∈ range K, vonMangoldtAtom k *
        (2 * ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n) := by
    rw [hfin]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [abs_mul, abs_of_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)]
    have hlag := abs_lagForm_le_lagWin hg.continuous hgc hsupp N k y
    rw [hmass] at hlag
    have hsym : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * (lagWin w k m n + lagWin w k n m) =
        2 * ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n := by
      have hsplit : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * (lagWin w k m n + lagWin w k n m) =
          (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * lagWin w k m n) +
            ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * lagWin w k n m := by
        simp_rw [mul_add, sum_add_distrib]
      have hcomm : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * lagWin w k n m =
          ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * lagWin w k m n := by
        rw [sum_comm]
        exact sum_congr rfl fun n _ => sum_congr rfl fun m _ => by ring
      have hIoc_sub : (Ioc M N : Finset ℕ) ⊆ Icc 1 N := fun n hn =>
        mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) (mem_Ioc.mp hn).1),
          (mem_Ioc.mp hn).2⟩
      have hres : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * lagWin w k m n =
          ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n := by
        rw [← sum_subset hIoc_sub fun m hm hnot => by
          have hmM : m ≤ M := by
            by_contra hgt; exact hnot (mem_Ioc.mpr ⟨not_le.mp hgt, (mem_Icc.mp hm).2⟩)
          have hy0 : y m = 0 := if_neg (Nat.not_lt.mpr hmM)
          simp [hy0]]
        refine sum_congr rfl fun m hm => ?_
        rw [← sum_subset hIoc_sub fun n hn hnot => by
          have hnM : n ≤ M := by
            by_contra hgt; exact hnot (mem_Ioc.mpr ⟨not_le.mp hgt, (mem_Icc.mp hn).2⟩)
          have hy0 : y n = 0 := if_neg (Nat.not_lt.mpr hnM)
          simp [hy0]]
        exact sum_congr rfl fun n hn => by
          have hym : y m = x m := if_pos (mem_Ioc.mp hm).1
          have hyn : y n = x n := if_pos (mem_Ioc.mp hn).1
          rw [hym, hyn]
      rw [hsplit, hcomm, hres]; ring
    rw [hsym] at hlag
    calc vonMangoldtAtom k * |lagForm g N k y|
        ≤ vonMangoldtAtom k * (G * (2 * ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N,
            |x m| * |x n| * lagWin w k m n)) :=
          mul_le_mul_of_nonneg_left hlag (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
      _ = G * (vonMangoldtAtom k *
          (2 * ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n)) := by ring
  -- Bound `vonMangoldtAtom k ≤ k` and `e^w - 1 ≤ 3 w`
  have hew1 : Real.exp w - 1 ≤ 3 * w := by
    have h1 : Real.exp w - 1 ≤ w * Real.exp w := by
      have h2 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-w)) (Real.exp_pos w).le
      have h3 : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
      linarith only [h2, h3]
    have hew : Real.exp w ≤ Real.exp 1 := Real.exp_le_exp.mpr hw1
    have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    nlinarith
  have hew0 : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  have hvma_le : ∀ k : ℕ, 2 ≤ k → vonMangoldtAtom k ≤ (k : ℝ) := fun k hk2 => by
    rw [vonMangoldtAtom_eq k]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hsk1 : 1 ≤ Real.sqrt k := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ k by omega))
    calc (Λ k : ℝ) / Real.sqrt k ≤ (Λ k : ℝ) / 1 :=
          div_le_div_of_nonneg_left vonMangoldt_nonneg zero_lt_one hsk1
      _ = (Λ k : ℝ) := div_one _
      _ ≤ Real.log k := vonMangoldt_le_log
      _ ≤ k := (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  -- Apply asymmetric AM-GM `2 |x_m| |x_n| ≤ k^4 x_m^2 + x_n^2 / k^4` for `k ≥ 2`
  have hstep2 : ∑ k ∈ range K, vonMangoldtAtom k *
        (2 * ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n) ≤
      (∑ m ∈ Ioc M N, x m ^ 2 *
        ∑ k ∈ range K, if 2 ≤ k then (k : ℝ) ^ 5 * ∑ n ∈ Ioc M N, lagWin w k m n else 0) +
      (∑ n ∈ Ioc M N, x n ^ 2 *
        ∑ k ∈ range K, if 2 ≤ k then (1 / (k : ℝ) ^ 3) * ∑ m ∈ Ioc M N, lagWin w k m n else 0) := by
    have hk_bound : ∀ k ∈ range K,
        vonMangoldtAtom k * (2 * ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n) ≤
          (∑ m ∈ Ioc M N, x m ^ 2 *
            (if 2 ≤ k then (k : ℝ) ^ 5 * ∑ n ∈ Ioc M N, lagWin w k m n else 0)) +
          (∑ n ∈ Ioc M N, x n ^ 2 *
            (if 2 ≤ k then (1 / (k : ℝ) ^ 3) * ∑ m ∈ Ioc M N, lagWin w k m n else 0)) := by
      intro k _
      rcases lt_or_ge k 2 with hk2 | hk2
      · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
        simp [not_le.mpr hk2]
      · simp only [if_pos hk2]
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
        have hamgm : 2 * ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n ≤
            (∑ m ∈ Ioc M N, x m ^ 2 * ((k : ℝ) ^ 4 * ∑ n ∈ Ioc M N, lagWin w k m n)) +
              ∑ n ∈ Ioc M N, x n ^ 2 * ((1 / (k : ℝ) ^ 4) * ∑ m ∈ Ioc M N, lagWin w k m n) := by
          rw [mul_sum]
          have hpair : ∀ m ∈ Ioc M N,
              2 * ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n ≤
                ∑ n ∈ Ioc M N, (((k : ℝ) ^ 4 * x m ^ 2 + (1 / (k : ℝ) ^ 4) * x n ^ 2) *
                  lagWin w k m n) := fun m _ => by
            rw [mul_sum]
            refine sum_le_sum fun n _ => ?_
            have h1 : 2 * (|x m| * |x n|) ≤ (k : ℝ) ^ 4 * x m ^ 2 + (1 / (k : ℝ) ^ 4) * x n ^ 2 := by
              have hsq := sq_nonneg ((k : ℝ) ^ 2 * |x m| - (1 / (k : ℝ) ^ 2) * |x n|)
              have hexp_sq : ((k : ℝ) ^ 2 * |x m| - (1 / (k : ℝ) ^ 2) * |x n|) ^ 2 =
                  (k : ℝ) ^ 4 * |x m| ^ 2 - 2 * (|x m| * |x n|) + (1 / (k : ℝ) ^ 4) * |x n| ^ 2 := by
                field_simp [hk0.ne']; ring
              rw [sq_abs, sq_abs] at hexp_sq
              linarith only [hsq, hexp_sq]
            calc 2 * (|x m| * |x n| * lagWin w k m n)
                = (2 * (|x m| * |x n|)) * lagWin w k m n := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right h1 (lagWin_nonneg w k m n)
          refine (sum_le_sum hpair).trans (le_of_eq ?_)
          simp_rw [add_mul, sum_add_distrib]
          congr 1
          · refine sum_congr rfl fun m _ => ?_
            rw [← mul_sum]; ring
          · rw [sum_comm]
            refine sum_congr rfl fun n _ => ?_
            rw [← mul_sum]; ring
        have hvma := hvma_le k hk2
        have hnn_sum : 0 ≤ 2 * ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n :=
          mul_nonneg zero_le_two (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
            mul_nonneg (by positivity) (lagWin_nonneg _ _ _ _))
        calc vonMangoldtAtom k * (2 * ∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, |x m| * |x n| * lagWin w k m n)
            ≤ (k : ℝ) * ((∑ m ∈ Ioc M N, x m ^ 2 * ((k : ℝ) ^ 4 * ∑ n ∈ Ioc M N, lagWin w k m n)) +
                ∑ n ∈ Ioc M N, x n ^ 2 * ((1 / (k : ℝ) ^ 4) * ∑ m ∈ Ioc M N, lagWin w k m n)) :=
              mul_le_mul hvma hamgm hnn_sum hk0.le
          _ = _ := by
              rw [mul_add, mul_sum, mul_sum]
              congr 1
              · refine sum_congr rfl fun _ _ => ?_
                field_simp [hk0.ne']
              · refine sum_congr rfl fun _ _ => ?_
                field_simp [hk0.ne']
    refine (sum_le_sum hk_bound).trans (le_of_eq ?_)
    rw [sum_add_distrib]
    congr 1
    · rw [sum_comm]; exact sum_congr rfl fun _ _ => (mul_sum _ _ _).symm
    · rw [sum_comm]; exact sum_congr rfl fun _ _ => (mul_sum _ _ _).symm
  -- Bound the up-sum coefficient by `(6 e^7 + e^6) c (N / m)^7`
  have hup_coef : ∀ m ∈ Ioc M N,
      (∑ k ∈ range K, if 2 ≤ k then (k : ℝ) ^ 5 * ∑ n ∈ Ioc M N, lagWin w k m n else 0) ≤
        (6 * Real.exp 7 + Real.exp 6) * c * ((N : ℝ) / m) ^ 7 := by
    intro m hm
    obtain ⟨hMm, hmN⟩ := mem_Ioc.mp hm
    have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) hMm)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    set k₁ := ⌊(N : ℝ) * Real.exp w / m⌋₊
    have hk_term : ∀ k ∈ range K,
        (if 2 ≤ k then (k : ℝ) ^ 5 * ∑ n ∈ Ioc M N, lagWin w k m n else 0) ≤
          if k ∈ Icc 1 k₁ then 6 * c * ((m : ℝ) / N) * (k₁ : ℝ) ^ 6 + (k₁ : ℝ) ^ 5 else 0 := by
      intro k _
      split_ifs with hk2 hkI
      · have hk1 : 1 ≤ k := by omega
        have hk_le : (k : ℝ) ≤ k₁ := by exact_mod_cast (mem_Icc.mp hkI).2
        set R := ((k * m : ℕ) : ℝ) * (Real.exp w - 1)
        have hR0 : 0 ≤ R := by positivity
        have hcnt : ∑ n ∈ Ioc M N, lagWin w k m n ≤ 6 * c * k * ((m : ℝ) / N) + 1 := by
          have hsub : (Ioc M N).filter (fun n : ℕ => |Real.log k - (Real.log n - Real.log m)| ≤ w) ⊆
              (Ioc M N).filter (fun n : ℕ => |((1 : ℕ) : ℝ) * n - (k * m : ℕ)| ≤ R) := by
            intro n hn
            obtain ⟨hnS, hwin⟩ := mem_filter.mp hn
            have hn1 : 1 ≤ n :=
              Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) (mem_Ioc.mp hnS).1)
            refine mem_filter.mpr ⟨hnS, ?_⟩
            rw [Nat.cast_one, one_mul]
            exact (upWin_bounds hk1 hm1 hn1 hwin).2.1
          have h1 : ∑ n ∈ Ioc M N, lagWin w k m n =
              (((Ioc M N).filter fun n : ℕ => |Real.log k - (Real.log n - Real.log m)| ≤ w).card : ℝ) := by
            unfold lagWin; rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
          rw [h1]
          have hcard := (Nat.cast_le.mpr (card_le_card hsub)).trans
            (card_mul_near_le (Ioc M N) le_rfl ((k * m : ℕ) : ℝ) hR0)
          rw [Nat.cast_one, div_one] at hcard
          have hR_le : 2 * R ≤ 6 * c * k * ((m : ℝ) / N) := by
            simp only [R]
            push_cast
            calc 2 * ((k : ℝ) * m * (Real.exp w - 1))
                ≤ 2 * ((k : ℝ) * m * (3 * w)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hew1 (by positivity)) zero_le_two
              _ = 6 * c * k * ((m : ℝ) / N) := by simp only [w]; field_simp [hNR.ne']; ring
          linarith
        calc (k : ℝ) ^ 5 * ∑ n ∈ Ioc M N, lagWin w k m n
            ≤ (k : ℝ) ^ 5 * (6 * c * k * ((m : ℝ) / N) + 1) :=
              mul_le_mul_of_nonneg_left hcnt (by positivity)
          _ = 6 * c * ((m : ℝ) / N) * (k : ℝ) ^ 6 + (k : ℝ) ^ 5 := by ring
          _ ≤ 6 * c * ((m : ℝ) / N) * (k₁ : ℝ) ^ 6 + (k₁ : ℝ) ^ 5 :=
              add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) hk_le 6)
                (by positivity)) (pow_le_pow_left₀ (Nat.cast_nonneg k) hk_le 5)
      · have hbig : (N : ℝ) * Real.exp w / m < k := by
          have : k₁ < k := by
            by_contra hle; exact hkI (mem_Icc.mpr ⟨by omega, not_lt.mp hle⟩)
          exact Nat.lt_of_floor_lt this
        have hzero : ∑ n ∈ Ioc M N, lagWin w k m n = 0 := by
          refine sum_eq_zero fun n hn => ?_
          obtain ⟨hMn, hnN⟩ := mem_Ioc.mp hn
          have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) hMn)
          unfold lagWin
          split_ifs with h1
          · exfalso
            have hle := (upWin_bounds (by omega) hm1 hn1 h1).2.2
            have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
            rw [div_lt_iff₀ hm0] at hbig
            have he : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
            nlinarith [Real.exp_pos w, Real.exp_pos (-w)]
          · rfl
        rw [hzero, mul_zero]
      · positivity
      · exact le_rfl
    have hsum_Icc : (∑ k ∈ range K, if 2 ≤ k then (k : ℝ) ^ 5 * ∑ n ∈ Ioc M N, lagWin w k m n else 0) ≤
        6 * c * ((m : ℝ) / N) * (k₁ : ℝ) ^ 7 + (k₁ : ℝ) ^ 6 := by
      refine (sum_le_sum hk_term).trans ?_
      rw [← sum_filter]
      have hsub : (range K).filter (fun k : ℕ => k ∈ Icc 1 k₁) ⊆ Icc 1 k₁ :=
        fun k hk => (mem_filter.mp hk).2
      refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      exact le_of_eq (by ring)
    have hk₁_ub : (k₁ : ℝ) ≤ Real.exp 1 * ((N : ℝ) / m) := by
      calc (k₁ : ℝ) ≤ (N : ℝ) * Real.exp w / m := Nat.floor_le (by positivity)
        _ ≤ (N : ℝ) * Real.exp 1 / m := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hNR.le) hm0.le
        _ = Real.exp 1 * ((N : ℝ) / m) := by ring
    have hrat1 : 1 ≤ (N : ℝ) / m := (one_le_div hm0).mpr (by exact_mod_cast hmN)
    have hp7 := pow_le_pow_left₀ (Nat.cast_nonneg k₁) hk₁_ub 7
    have hp6 := pow_le_pow_left₀ (Nat.cast_nonneg k₁) hk₁_ub 6
    have he7 : (Real.exp 1) ^ 7 = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
    have he6 : (Real.exp 1) ^ 6 = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [mul_pow, he7] at hp7
    rw [mul_pow, he6] at hp6
    have ht1 : 6 * c * ((m : ℝ) / N) * (k₁ : ℝ) ^ 7 ≤
        6 * Real.exp 7 * c * ((N : ℝ) / m) ^ 7 := by
      calc 6 * c * ((m : ℝ) / N) * (k₁ : ℝ) ^ 7
          ≤ 6 * c * ((m : ℝ) / N) * (Real.exp 7 * ((N : ℝ) / m) ^ 7) :=
            mul_le_mul_of_nonneg_left hp7 (by positivity)
        _ = 6 * Real.exp 7 * c * ((N : ℝ) / m) ^ 6 := by
            field_simp [hNR.ne', hm0.ne']
        _ ≤ 6 * Real.exp 7 * c * ((N : ℝ) / m) ^ 7 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hrat1 (by norm_num)) (by positivity)
    have ht2 : (k₁ : ℝ) ^ 6 ≤ Real.exp 6 * c * ((N : ℝ) / m) ^ 7 := by
      calc (k₁ : ℝ) ^ 6 ≤ Real.exp 6 * ((N : ℝ) / m) ^ 6 := hp6
        _ ≤ Real.exp 6 * ((N : ℝ) / m) ^ 7 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hrat1 (by norm_num)) (by positivity)
        _ = Real.exp 6 * 1 * ((N : ℝ) / m) ^ 7 := by ring
        _ ≤ Real.exp 6 * c * ((N : ℝ) / m) ^ 7 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1 (by positivity))
              (by positivity)
    linarith
  -- Bound the down-sum coefficient by `7 c` via telescoping `1 / (k(k-1))`
  have hdown_coef : ∀ n ∈ Ioc M N,
      (∑ k ∈ range K, if 2 ≤ k then (1 / (k : ℝ) ^ 3) * ∑ m ∈ Ioc M N, lagWin w k m n else 0) ≤
        7 * c := by
    intro n hn
    obtain ⟨hMn, hnN⟩ := mem_Ioc.mp hn
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) hMn)
    have hnN_R : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have hk_cnt : ∀ k : ℕ, 2 ≤ k → ∑ m ∈ Ioc M N, lagWin w k m n ≤ 7 * c := fun k hk2 => by
      have hk1 : 1 ≤ k := by omega
      have hk1_R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      set R := (n : ℝ) * (Real.exp w - 1)
      have hR0 : 0 ≤ R := by positivity
      have hsub : (Ioc M N).filter (fun m : ℕ => |Real.log k - (Real.log n - Real.log m)| ≤ w) ⊆
          (Ioc M N).filter (fun m : ℕ => |(k : ℝ) * m - n| ≤ R) := by
        intro m hm
        obtain ⟨hmS, hwin⟩ := mem_filter.mp hm
        have hm1 : 1 ≤ m :=
          Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le M) (mem_Ioc.mp hmS).1)
        refine mem_filter.mpr ⟨hmS, ?_⟩
        have h3 := (downWin_bounds hk1 hn1 hm1 hwin).2
        push_cast at h3; exact h3
      have h1 : ∑ m ∈ Ioc M N, lagWin w k m n =
          (((Ioc M N).filter fun m : ℕ => |Real.log k - (Real.log n - Real.log m)| ≤ w).card : ℝ) := by
        unfold lagWin; rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      rw [h1]
      have hcard := (Nat.cast_le.mpr (card_le_card hsub)).trans
        (card_mul_near_le (Ioc M N) hk1 (n : ℝ) hR0)
      have hdiv : 2 * R / k ≤ 6 * c := by
        calc 2 * R / k ≤ 2 * R / 1 := div_le_div_of_nonneg_left (by positivity) zero_lt_one hk1_R
          _ = 2 * ((n : ℝ) * (Real.exp w - 1)) := by simp only [R]; ring
          _ ≤ 2 * ((N : ℝ) * (3 * w)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hnN_R hew1 hew0 hNR.le) zero_le_two
          _ = 6 * c := by simp only [w]; field_simp [hNR.ne']; ring
      linarith [hc1]
    have htele : ∑ k ∈ range K, (if 2 ≤ k then (1 / (k : ℝ) ^ 3) else 0) ≤ 1 := by
      set K' := max K 2
      have hsub : range K ⊆ range K' := range_mono (le_max_left K 2)
      refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by split_ifs <;> positivity).trans ?_
      have hIco : ∑ k ∈ range K', (if 2 ≤ k then (1 / (k : ℝ) ^ 3) else 0) ≤
          ∑ k ∈ Ico 2 K', (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) := by
        have heq : ∑ k ∈ range K', (if 2 ≤ k then (1 / (k : ℝ) ^ 3) else 0) =
            ∑ k ∈ Ico 2 K', (1 / (k : ℝ) ^ 3) := by
          rw [← sum_filter]
          congr 1; ext k; simp only [mem_filter, mem_range, mem_Ico]; omega
        rw [heq]
        refine sum_le_sum fun k hk => ?_
        have hk2 : 2 ≤ k := (mem_Ico.mp hk).1
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
        have hkm1 : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
        have hsub_eq : 1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) =
            1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ)) := by
          have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
          field_simp [hk0.ne', hkm1.ne']
          linarith only [hcast]
        rw [hsub_eq]
        refine one_div_le_one_div_of_le (by positivity) ?_
        have hle1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
        have h1k : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
        calc ((k - 1 : ℕ) : ℝ) * k ≤ (k : ℝ) * k := mul_le_mul_of_nonneg_right hle1 hk0.le
          _ = (k : ℝ) ^ 2 * 1 := by ring
          _ ≤ (k : ℝ) ^ 2 * k := mul_le_mul_of_nonneg_left h1k (sq_nonneg _)
          _ = (k : ℝ) ^ 3 := by ring
      refine hIco.trans ?_
      have htel_eq : ∀ m : ℕ, 2 ≤ m →
          ∑ k ∈ Ico 2 m, (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) =
            1 - 1 / ((m - 1 : ℕ) : ℝ) := by
        refine Nat.le_induction ?_ ?_
        · simp
        · intro m hm ih
          rw [sum_Ico_succ_top hm, ih, show ((m + 1 - 1 : ℕ) : ℝ) = (m : ℝ) by simp]
          ring
      rw [htel_eq K' (le_max_right K 2)]
      have : (0 : ℝ) ≤ 1 / ((K' - 1 : ℕ) : ℝ) := by positivity
      linarith
    calc (∑ k ∈ range K, if 2 ≤ k then (1 / (k : ℝ) ^ 3) * ∑ m ∈ Ioc M N, lagWin w k m n else 0)
        ≤ ∑ k ∈ range K, (if 2 ≤ k then (1 / (k : ℝ) ^ 3) else 0) * (7 * c) :=
          sum_le_sum fun k _ => by
            split_ifs with hk2
            · exact mul_le_mul_of_nonneg_left (hk_cnt k hk2) (by positivity)
            · simp
      _ = (∑ k ∈ range K, if 2 ≤ k then (1 / (k : ℝ) ^ 3) else 0) * (7 * c) := (sum_mul _ _ _).symm
      _ ≤ 1 * (7 * c) := mul_le_mul_of_nonneg_right htele (by positivity)
      _ = 7 * c := one_mul _
  have hup_sum : (∑ m ∈ Ioc M N, x m ^ 2 *
        ∑ k ∈ range K, if 2 ≤ k then (k : ℝ) ^ 5 * ∑ n ∈ Ioc M N, lagWin w k m n else 0) ≤
      (6 * Real.exp 7 + Real.exp 6) * c * topCollarSeventhMass M N x := by
    unfold topCollarSeventhMass
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    calc x m ^ 2 * (∑ k ∈ range K, if 2 ≤ k then (k : ℝ) ^ 5 * ∑ n ∈ Ioc M N, lagWin w k m n else 0)
        ≤ x m ^ 2 * ((6 * Real.exp 7 + Real.exp 6) * c * ((N : ℝ) / m) ^ 7) :=
          mul_le_mul_of_nonneg_left (hup_coef m hm) (sq_nonneg _)
      _ = (6 * Real.exp 7 + Real.exp 6) * c * (((N : ℝ) / m) ^ 7 * x m ^ 2) := by ring
  have hdown_sum : (∑ n ∈ Ioc M N, x n ^ 2 *
        ∑ k ∈ range K, if 2 ≤ k then (1 / (k : ℝ) ^ 3) * ∑ m ∈ Ioc M N, lagWin w k m n else 0) ≤
      7 * c * topCollarSeventhMass M N x := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_sq_Ioc_le_topCollarSeventhMass M N x)
      (by positivity : 0 ≤ 7 * c))
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    calc x n ^ 2 *
          (∑ k ∈ range K, if 2 ≤ k then (1 / (k : ℝ) ^ 3) * ∑ m ∈ Ioc M N, lagWin w k m n else 0)
        ≤ x n ^ 2 * (7 * c) := mul_le_mul_of_nonneg_left (hdown_coef n hn) (sq_nonneg _)
      _ = 7 * c * x n ^ 2 := by ring
  calc |primeSum (atomicTest N y g)|
      ≤ G * ((∑ m ∈ Ioc M N, x m ^ 2 *
            ∑ k ∈ range K, if 2 ≤ k then (k : ℝ) ^ 5 * ∑ n ∈ Ioc M N, lagWin w k m n else 0) +
          (∑ n ∈ Ioc M N, x n ^ 2 *
            ∑ k ∈ range K, if 2 ≤ k then (1 / (k : ℝ) ^ 3) * ∑ m ∈ Ioc M N, lagWin w k m n else 0)) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hG.le)
    _ ≤ G * ((6 * Real.exp 7 + Real.exp 6) * c * topCollarSeventhMass M N x +
          7 * c * topCollarSeventhMass M N x) :=
        mul_le_mul_of_nonneg_left (add_le_add hup_sum hdown_sum) hG.le
    _ = G * topPrimeSeventhConstant * c * topCollarSeventhMass M N x := by
        unfold topPrimeSeventhConstant; ring

/-! ### Critical-multiple far reserve on `(V_1)ᗮ` -/

/-- **The top block with the dyadic seventh-power reserve.** Half of `archForm` keeps the dyadic
seventh-power reserve `dyadicTopMassConstant / c⁷ · log N` on `topCollarSeventhMass`, half pays
frequencies above `T`, and the prime self-form costs only `O(c)` with no `log c` factor. -/
theorem top_block_ge_seventh {C_arch c : ℝ} (hc1 : 1 ≤ c) {N : ℕ}
    (hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N) (x : ℕ → ℝ)
    (harch_top : ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
      ((dyadicTopMassConstant / c ^ 7) * Real.log N *
          topCollarSeventhMass (N / linearDefectCutoff c) N x -
        C_arch * c * topCollarSeventhMass (N / linearDefectCutoff c) N x) ≤
      archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
        (atomDilate tiltedUnitSpline (c / N))))
    {T : ℝ} (hT0 : 0 < T) :
    ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        ((1 / 2 : ℝ) * ((dyadicTopMassConstant / c ^ 7) * Real.log N *
            topCollarSeventhMass (N / linearDefectCutoff c) N x -
          C_arch * c * topCollarSeventhMass (N / linearDefectCutoff c) N x) -
          topPrimeSeventhConstant * c *
            topCollarSeventhMass (N / linearDefectCutoff c) N x) +
      (1 / 2 : ℝ) * ((Real.log T - factorialSpanGammaOffset) *
          highFourierMass (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N))) T -
        (factorialSpanGammaOffset + Real.log 2) *
          lowFourierMass (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N))) T) ≤
      archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
          (atomDilate tiltedUnitSpline (c / N))) -
        primeSum (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
          (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨hL3, -, -, -⟩ := linearDefectCutoff_bounds hc1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLN : linearDefectCutoff c ≤ N := by
    have hLc_R : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
    have : (linearDefectCutoff c : ℝ) ≤ N := by nlinarith [hL2N]
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by
    have : 1 ≤ N := (by omega : 1 ≤ linearDefectCutoff c).trans hLN
    exact_mod_cast this
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hNR
  set g := atomDilate tiltedUnitSpline (c / N)
  set y := atomicTailCoefficients (N / linearDefectCutoff c) x
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw
  have hfy : ContDiff ℝ 2 (atomicTest N y g) := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport (atomicTest N y g) := hasCompactSupport_atomicTest hsupp N y
  have hband := archForm_ge_high_band hfy hfyc (T := T) (R := T) hT0 le_rfl
  rw [sub_self, zero_mul, add_zero] at hband
  have htop := (le_abs_self _).trans (abs_primeSum_top_le_seventh hc1 hLN x)
  linarith

/-- **The far reserve through the window average with the dyadic seventh-power top norm.**
Upgrades `exists_completeWeilEnergy_prefix_top_window_reserve` by replacing the uniform top `ℓ²`
mass with `topCollarSeventhMass` and eliminating the `1 + log c` factor on the top collar. -/
theorem exists_completeWeilEnergy_prefix_top_window_reserve_seventh :
    ∃ C_S C_P C_ψ c₀ t₀ : ℝ, 0 < C_S ∧ 0 < C_P ∧ 0 ≤ C_ψ ∧ 0 < c₀ ∧ 1 ≤ t₀ ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → (linearDefectCutoff c : ℝ) ^ 2 ≤ N →
      ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {h T : ℝ} {K' : ℕ}, 0 < h → h ≤ 1 → 0 < T →
        factorialSpanGammaOffset + 1 ≤ Real.log T → 1 ≤ K' → t₀ ≤ K' * Real.exp (-1) →
        (7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension z) +
          (3 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * Real.log N *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) -
          C_S * c *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) -
          C_P * c * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) -
          16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * Real.log N) *
            (splineWindowConstant * ((c / N) / h ^ 2)) *
            windowSumBound C_ψ c₀ (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)
              ⌊(N : ℝ) * Real.exp (c / N)⌋₊ (N / linearDefectCutoff c) K'
              (primeHorizonExtension z) h -
          (16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * Real.log N) *
              (T * h) ^ 2 + 8 / (Real.log T - factorialSpanGammaOffset)) *
            ((1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
              (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
                (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ /
                  (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨C_arch, hCarch, harch_top⟩ := exists_top_archForm_dyadic_seventh_reserve
  obtain ⟨C_ψ, c₀, t₀, hCψ, hc₀, ht₀1, hpnt⟩ := exists_vonMangoldtAtom_window_error
  have hG₀ : 0 ≤ factorialSpanGammaOffset := factorialSpanGammaOffset_nonneg
  have hC₄ : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith only [this]
  have hAsep : 0 ≤ separatedCrossMassCost := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    unfold separatedCrossMassCost; positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hCtop7 : 0 < topPrimeSeventhConstant := topPrimeSeventhConstant_pos
  set E2 : ℝ := (factorialSpanGammaOffset + Real.log 2) / 2 + 2 * Real.pi
  have hE2 : 0 ≤ E2 := by
    have : 0 ≤ 2 * Real.pi := by positivity
    simp only [E2]; linarith
  let C_S := C_arch / 2 + E2 * (1 + 2 * Real.exp 1) + topPrimeSeventhConstant + 1
  let C_P := 1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost + (Real.log 4 + 4) +
    2 * Real.pi
  have hCS : 0 < C_S := by
    have h1 : 0 ≤ E2 * (1 + 2 * Real.exp 1) := mul_nonneg hE2 (by positivity)
    simp only [C_S]; linarith
  have hCP : 0 < C_P := by
    have : 0 ≤ 2 * |gammaHardyPhaseRate 0| := by positivity
    have : 0 ≤ 2 * Real.pi := by positivity
    simp only [C_P]; linarith
  refine ⟨C_S, C_P, C_ψ, c₀, t₀, hCS, hCP, hCψ, hc₀, ht₀1, ?_⟩
  intro c N hc1 hL2N z hz h T K' hh hh1 hT0 hT hK' ht₀
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have h2LN : 2 * linearDefectCutoff c ≤ N := by
    have hLc_R : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
    have : (2 * linearDefectCutoff c : ℝ) ≤ N := by nlinarith [hL2N]
    exact_mod_cast this
  have hLN : linearDefectCutoff c ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hM : 1 ≤ N / linearDefectCutoff c :=
    (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hNR
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hMN : N / linearDefectCutoff c ≤ N := Nat.div_le_self _ _
  have henergy := completeWeilEnergy_eq_arch_sub_primeSum hc0 hN2 hz
  rw [integral_atomDilate_sq hw] at henergy
  have hPb := prefix_block_ge hc1 hLN hM (primeHorizonExtension z)
  have hYb := top_block_ge_seventh hc1 hL2N (primeHorizonExtension z)
    (harch_top hc1 hL2N (primeHorizonExtension z)) hT0
  have hAb := archForm_prefix_top_split_ge hc1 hLN hM (primeHorizonExtension z)
  have hSb := primeSum_prefix_top_split hc1 h2LN (primeHorizonExtension z)
  obtain ⟨hFh, hF⟩ := translate_masses_le hCψ hc₀ hpnt hc1 h2LN (primeHorizonExtension z) hh hh1
    hK' ht₀
  set x := primeHorizonExtension z
  set M := N / linearDefectCutoff c
  set P := ∑ n ∈ Icc 1 M, x n ^ 2
  set S := ∑ n ∈ Ioc M N, x n ^ 2
  set S7 := topCollarSeventhMass M N x
  set w := c / (N : ℝ)
  set g := atomDilate tiltedUnitSpline w
  set G := w * ∫ u, tiltedUnitSpline u ^ 2
  set y := atomicTailCoefficients M x
  set δ := dyadicTopMassConstant / c ^ 7
  set Bn := ⌊(N : ℝ) * Real.exp w⌋₊
  set V : ℕ → ℝ := fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv (primeOrderCutoff N w) M x n
  set WSB := windowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x h
  set Φ := (1 + 2 * Real.exp 1 * (w * Bn)) *
    (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS7_0 : 0 ≤ S7 := topCollarSeventhMass_nonneg M N x
  have hS_le_S7 : S ≤ S7 := sum_sq_Ioc_le_topCollarSeventhMass M N x
  have hδ : 0 < δ := div_pos dyadicTopMassConstant_pos (by positivity)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hfy : ContDiff ℝ 2 (atomicTest N y g) := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport (atomicTest N y g) := hasCompactSupport_atomicTest hsupp N y
  set γc := 1 + 2 * Real.exp 1 * c
  have hγc : 0 < γc := by positivity
  have hfy2_S : (∫ u, atomicTest N y g u ^ 2) ≤ G * γc * S := by
    have h0 := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc0 hcN hsupp y
    rw [integral_atomDilate_sq hw, sum_atomicTailCoefficients_sq_eq_Ioc' hMN x] at h0
    exact h0
  have hfy2 : (∫ u, atomicTest N y g u ^ 2) ≤ G * γc * S7 :=
    hfy2_S.trans (mul_le_mul_of_nonneg_left hS_le_S7 (by positivity))
  have hAb' : archForm (atomicTest M x g) + archForm (atomicTest N y g) -
      2 * Real.pi * (G * P + G * γc * S7) ≤ archForm (atomicTest N x g) := by
    have hpiS : 2 * Real.pi * (G * γc * S) ≤ 2 * Real.pi * (G * γc * S7) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS_le_S7 (by positivity)) (by positivity)
    linarith only [hAb, hpiS]
  have hLMy := lowFourierMass_le_integral_sq hfy hfyc T
  set η := δ * Real.log N / (16 * γc)
  have hη : 0 < η := by positivity
  set lam := (Real.log T - factorialSpanGammaOffset) / 2
  have hlam : 0 < lam := by simp only [lam]; linarith only [hT]
  have hX := two_mul_abs_integral_mul_atomicTest_le (f := atomicTest N y g) hfy hfyc hg hsupp
    Bn V (T := T) hh hη hlam
  have hηinv : η⁻¹ = 16 * γc / (δ * Real.log N) := by simp only [η]; rw [inv_div]
  have hlaminv : lam⁻¹ * 4 = 8 / (Real.log T - factorialSpanGammaOffset) := by
    simp only [lam]; field_simp; ring
  have hfyη : η * (∫ u, atomicTest N y g u ^ 2) ≤ η * (G * γc * S7) :=
    mul_le_mul_of_nonneg_left hfy2 hη.le
  have hLMη : η * lowFourierMass (atomicTest N y g) T ≤ η * (G * γc * S7) :=
    mul_le_mul_of_nonneg_left (hLMy.trans hfy2) hη.le
  have hLME : (factorialSpanGammaOffset + Real.log 2) *
      lowFourierMass (atomicTest N y g) T ≤ (factorialSpanGammaOffset + Real.log 2) * (G * γc * S7) :=
    mul_le_mul_of_nonneg_left (hLMy.trans hfy2) (add_nonneg hG₀ hlog2)
  have hFhη : η⁻¹ * (∫ u, atomicTest Bn V (smoothedBump g h) u ^ 2) ≤
      η⁻¹ * (G * (splineWindowConstant * (w / h ^ 2)) * WSB) :=
    mul_le_mul_of_nonneg_left hFh (inv_nonneg.mpr hη.le)
  have hFη : η⁻¹ * ((T * h) ^ 2 * ∫ u, atomicTest Bn V g u ^ 2) ≤
      η⁻¹ * ((T * h) ^ 2 * (G * Φ * P)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF (sq_nonneg _)) (inv_nonneg.mpr hη.le)
  have hFlam : lam⁻¹ * (4 * ∫ u, atomicTest Bn V g u ^ 2) ≤ lam⁻¹ * (4 * (G * Φ * P)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF (by norm_num)) (inv_nonneg.mpr hlam.le)
  have hηG : 2 * (η * (G * γc * S7)) = G * ((δ / 8) * Real.log N * S7) := by
    simp only [η]; field_simp; ring
  have hlamHM : lam * highFourierMass (atomicTest N y g) T =
      (1 / 2 : ℝ) * ((Real.log T - factorialSpanGammaOffset) *
        highFourierMass (atomicTest N y g) T) := by simp only [lam]; ring
  have hXabs := le_abs_self (∫ u, atomicTest N y g u * atomicTest Bn V g u)
  have hcoefS : C_arch / 2 * c + topPrimeSeventhConstant * c + E2 * γc ≤ C_S * c := by
    have h2 : γc ≤ (1 + 2 * Real.exp 1) * c := by
      simp only [γc]; nlinarith only [hc1, Real.exp_pos 1]
    have h3 := mul_le_mul_of_nonneg_left h2 hE2
    simp only [C_S]
    nlinarith only [h3, hc0.le]
  have hcoefP : c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
      (Real.log 4 + 4) + 2 * Real.pi ≤ C_P * c := by
    have h1 : 2 * |gammaHardyPhaseRate 0| ≤ 2 * |gammaHardyPhaseRate 0| * c :=
      le_mul_of_one_le_right (by positivity) hc1
    have h2 : Real.log 4 + 4 ≤ (Real.log 4 + 4) * c := le_mul_of_one_le_right hC₄ hc1
    have h3 : 2 * Real.pi ≤ 2 * Real.pi * c := le_mul_of_one_le_right (by positivity) hc1
    simp only [C_P]
    nlinarith only [h1, h2, h3]
  have hSG : G * ((C_arch / 2 * c + topPrimeSeventhConstant * c + E2 * γc) * S7) ≤
      G * (C_S * c * S7) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoefS hS7_0) hG.le
  have hPG := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoefP hP0) hG.le
  rw [henergy, ← sub_div, le_div_iff₀ hG]
  rw [hηinv] at hFhη hFη hX
  have hE2exp : G * (E2 * γc * S7) = (1 / 2 : ℝ) * ((factorialSpanGammaOffset + Real.log 2) *
      (G * γc * S7)) + 2 * Real.pi * (G * γc * S7) := by simp only [E2]; ring
  have hfinalF : (16 * γc / (δ * Real.log N) * (T * h) ^ 2 +
      8 / (Real.log T - factorialSpanGammaOffset)) * Φ * P * G =
      16 * γc / (δ * Real.log N) * ((T * h) ^ 2 * (G * Φ * P)) +
        lam⁻¹ * (4 * (G * Φ * P)) := by
    rw [← hlaminv]; ring
  have hfinalW : 16 * γc / (δ * Real.log N) * (splineWindowConstant * (w / h ^ 2)) * WSB * G =
      16 * γc / (δ * Real.log N) * (G * (splineWindowConstant * (w / h ^ 2)) * WSB) := by ring
  change ((7 / 8 : ℝ) * poleDefect M x + (3 / 8 : ℝ) * δ * Real.log N * S7 -
      C_S * c * S7 - C_P * c * P -
      16 * γc / (δ * Real.log N) * (splineWindowConstant * (w / h ^ 2)) * WSB -
      (16 * γc / (δ * Real.log N) * (T * h) ^ 2 +
        8 / (Real.log T - factorialSpanGammaOffset)) * Φ * P) * G ≤ _
  linarith only [hAb', hSb, hPb, hYb, hX, hXabs, hfyη, hLMη, hLME, hFhη, hFη, hFlam, hηG,
    hlamHM, hSG, hPG, hfinalF, hfinalW, hfy2, hE2exp]

private theorem two_mul_one_div_two_mul (M : ℝ) : 2 * (1 / (2 * M)) = 1 / M := by
  rw [one_div_mul_eq_div, mul_div_cancel_left₀ _ two_ne_zero]

private theorem one_eighth_div_mul_eq (g c7 l : ℝ) :
    (1 / 8 : ℝ) * (g / c7) * l = (g * l) / (8 * c7) := by
  rw [one_div_mul_eq_div, div_div, mul_comm 8 c7, div_mul_eq_mul_div, mul_comm c7 8]

private theorem mul_eq_quarter_mul {cp c th : ℝ} (hth : th ≠ 0) :
    cp * c = th / 4 * (4 * cp / th * c) := by
  field_simp [hth]

private theorem eta_num_eq {A g l c : ℝ} (hc : c ≠ 0) :
    A * (g * l) = (A * c ^ 7) * ((g / c ^ 7) * l) := by
  field_simp [hc]

private theorem window_pole_algebraic_eq {u c g0 l s e2 S7 : ℝ}
    (hg : g0 ≠ 0) (hl : l ≠ 0) (hc : c ≠ 0) :
    (16 * u * c ^ 8 / (g0 * l) * s) * (8 * e2 * c * S7) =
      (1 / 8 : ℝ) * (g0 / c ^ 7) * l * S7 *
        (1024 * u * s * e2 * c ^ 16 / (g0 ^ 2 * l ^ 2)) := by
  field_simp [hg, hl, hc]; ring

private theorem window_mass_algebraic_eq {u c g0 l s w cb lm P' th : ℝ}
    (hg : g0 ≠ 0) (hl : l ≠ 0) (hth : th ≠ 0) :
    16 * u * c ^ 8 / (g0 * l) * s * ((c * w * (cb * lm)) * P') =
      th / 4 * l * P' * ((64 * u * s * w * cb / (g0 * th)) * (c ^ 9 * lm) / l ^ 2) := by
  field_simp [hg, hl, hth]; ring

private theorem top_budget_algebraic_eq {g0 c l S : ℝ} (hc : c ≠ 0) :
    (g0 / (8 * c ^ 7)) * l * S =
      (3 / 8 : ℝ) * (g0 / c ^ 7) * l * S -
        (1 / 8 : ℝ) * (g0 / c ^ 7) * l * S -
        (1 / 8 : ℝ) * (g0 / c ^ 7) * l * S := by
  field_simp [hc]; ring

/-- **Critical-multiple far reserve on `(V_1)ᗮ`.** There exists a fixed critical multiple
`K₁_far > 0` such that for any polylogarithmic exponent `B : ℕ` and any `κ_P > 0`, eventually in
`N` and uniformly across `1 ≤ c ≤ 2 K₁_far (log N)^{1/8}`, every pole-orthogonal vector keeps
`(7/8) D_M` on the prefix and `(dyadicTopMassConstant / (8 c⁷)) log N` per unit
`topCollarSeventhMass` on the top collar, at a prefix mass cost of at most
`(κ_P log N / (1 + log log N)^B) P`. -/
theorem exists_critical_multiple_far_reserve :
    ∃ K₁_far : ℝ, 0 < K₁_far ∧ 2 * K₁_far ≤ 1 ∧
      ∀ (B : ℕ) {κ_P : ℝ}, 0 < κ_P →
        ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ 2 * K₁_far * Real.log N ^ (1 / 8 : ℝ) →
          ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
            (7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension z) +
              (dyadicTopMassConstant / (8 * c ^ 7)) * Real.log N *
                topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) -
              (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ B) *
                (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) ≤
              completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨C_S, C_P, C_ψ, c₀, t₀, hCS, hCP, hCψ, hc₀, ht₀1, hres⟩ :=
    exists_completeWeilEnergy_prefix_top_window_reserve_seventh
  have hg₀ : 0 < dyadicTopMassConstant := dyadicTopMassConstant_pos
  have hκ_nn : 0 ≤ splineWindowConstant := splineWindowConstant_nonneg
  set M_far := max 1 (max (8 * C_S / dyadicTopMassConstant)
    (1024 * (1 + 2 * Real.exp 1) * (splineWindowConstant + 1) * Real.exp 2 /
      dyadicTopMassConstant ^ 2))
  have hM1 : 1 ≤ M_far := le_max_left _ _
  have hM_pos : 0 < M_far := zero_lt_one.trans_le hM1
  set K₁_far := 1 / (2 * M_far)
  have hK₁_pos : 0 < K₁_far := by positivity
  have h2K₁ : 2 * K₁_far = 1 / M_far := two_mul_one_div_two_mul M_far
  have h2K₁_le1 : 2 * K₁_far ≤ 1 := by rw [h2K₁]; exact div_le_one_of_le₀ hM1 hM_pos.le
  refine ⟨K₁_far, hK₁_pos, h2K₁_le1, ?_⟩
  intro B κ_P hκP
  set α' : ℝ := 1 / 7
  have hα'0 : 0 < α' := by simp only [α']; norm_num
  set C_β := 1 + 25 / c₀ ^ 2 + |Real.log t₀|
  have hCβ : 0 ≤ C_β :=
    add_nonneg (add_nonneg zero_le_one (div_nonneg (by norm_num : (0 : ℝ) ≤ 25) (sq_nonneg c₀)))
      (abs_nonneg _)
  set C_B := C_β + 1 + (Real.log 4 + 4)
  set K₂ := Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev_ℓ : ∀ᶠ ℓ : ℝ in atTop,
      1 ≤ ℓ ∧
      8 * (256 * Real.exp 2 + 4) ≤ ℓ ∧
      2 * factorialSpanGammaOffset + 2 + Real.log (4 * C_ψ + 1) ≤ ℓ ^ α' ∧
      Real.log ℓ ≤ ℓ ^ α' ∧
      (4 * C_P / κ_P) * ℓ ^ (1 / 8 : ℝ) * (1 + Real.log ℓ) ^ B ≤ ℓ ^ (1 : ℝ) ∧
      (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
        (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
        (dyadicTopMassConstant * κ_P)) * ℓ ^ (13 * α') * (1 + Real.log ℓ) ^ B ≤ ℓ ^ (2 : ℝ) ∧
      (256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) * K₂ /
        (dyadicTopMassConstant * κ_P)) * ℓ ^ (9 * α' + 1) * (1 + Real.log ℓ) ^ (B + 1) ≤
        ℓ ^ (4 : ℝ) ∧
      (256 * (1 + 2 * Real.exp 2) * K₂ / κ_P) * ℓ ^ (1 / 8 + 1 : ℝ) *
        (1 + Real.log ℓ) ^ (B + 1) ≤ ℓ ^ (1 + α') ∧
      (|Real.log (2 * (Real.log 4 + 4))| + 4 + C_β) * ℓ ^ (2 * α') * (1 + Real.log ℓ) ^ 1 ≤
        ℓ ^ (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (8 * (256 * Real.exp 2 + 4)),
      (tendsto_rpow_atTop hα'0).eventually_ge_atTop
        (2 * factorialSpanGammaOffset + 2 + Real.log (4 * C_ψ + 1)),
      eventually_mul_rpow_polylog_le_rpow hα'0 1 1,
      eventually_mul_rpow_polylog_le_rpow (by norm_num : (1 / 8 : ℝ) < 1) B _,
      eventually_mul_rpow_polylog_le_rpow (by simp only [α']; norm_num : 13 * α' < 2) B _,
      eventually_mul_rpow_polylog_le_rpow (by simp only [α']; norm_num : 9 * α' + 1 < 4) (B + 1) _,
      eventually_mul_rpow_polylog_le_rpow (by simp only [α']; norm_num : (1 / 8 + 1 : ℝ) < 1 + α')
        (B + 1) _,
      eventually_mul_rpow_polylog_le_rpow (by simp only [α']; norm_num : 2 * α' < 1) 1 _]
      with ℓ h1 h2 h3 h4 h5 h6 h7 h8 h9
    refine ⟨h1, h2, h3, ?_, h5, h6, h7, h8, h9⟩
    rw [Real.rpow_zero, mul_one, one_mul, pow_one] at h4
    linarith only [h4]
  filter_upwards [hlogN.eventually hev_ℓ, eventually_ge_atTop 2] with N hN hN2
  clear hev_ℓ
  intro c hc1 hc_ub z hz
  obtain ⟨hℓ1, hℓ_L, hC0, hlogℓ, hQb, hQP, hQd, hQd', hQ5⟩ := hN
  set ℓ := Real.log (N : ℝ)
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have h1logℓ_pos : 0 < (1 + Real.log ℓ) ^ B := pow_pos (by linarith only [hlogℓ0]) B
  obtain ⟨θ, hθ_def⟩ : ∃ v, v = κ_P / (1 + Real.log ℓ) ^ B := ⟨_, rfl⟩
  have hθ : 0 < θ := hθ_def.symm ▸ div_pos hκP h1logℓ_pos
  have hθ_inv : ∀ X : ℝ, X / θ = (X / κ_P) * (1 + Real.log ℓ) ^ B := fun X => by
    rw [hθ_def, div_div_eq_mul_div, div_mul_eq_mul_div]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNexp : Real.exp ℓ = N := Real.exp_log hNR
  have hc18 : c ≤ ℓ ^ (1 / 8 : ℝ) :=
    hc_ub.trans ((mul_le_mul_of_nonneg_right h2K₁_le1 (Real.rpow_nonneg hℓpos.le _)).trans_eq
      (one_mul _))
  have hcα' : c ≤ ℓ ^ α' :=
    hc18.trans (Real.rpow_le_rpow_of_exponent_le hℓ1 (by simp only [α']; norm_num))
  have hcℓ : c ≤ ℓ :=
    hc18.trans ((Real.rpow_le_rpow_of_exponent_le hℓ1 (by norm_num)).trans_eq (Real.rpow_one _))
  -- Verify `(linearDefectCutoff c : ℝ) ^ 2 ≤ N` from `Real.quadratic_le_exp_of_nonneg` at `ℓ / 2`
  have hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N := by
    obtain ⟨-, -, -, hLup⟩ := linearDefectCutoff_bounds hc1
    have hCL : 0 < 256 * Real.exp 2 + 4 := by positivity
    have hLc_ℓ : (linearDefectCutoff c : ℝ) ≤ (256 * Real.exp 2 + 4) * ℓ :=
      hLup.trans (mul_le_mul_of_nonneg_left hcℓ hCL.le)
    have hquad := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ ℓ / 2 by linarith only [hℓ1])
    have hℓ2_le : (256 * Real.exp 2 + 4) * ℓ ≤ Real.exp (ℓ / 2) := by
      have hm := mul_le_mul_of_nonneg_right hℓ_L hℓpos.le
      have h1 : (256 * Real.exp 2 + 4) * ℓ ≤ (ℓ / 2) ^ 2 / 2 := by
        linarith only [hm, (by ring : ℓ * ℓ = 8 * ((ℓ / 2) ^ 2 / 2))]
      linarith only [h1, hquad, hℓ1]
    calc (linearDefectCutoff c : ℝ) ^ 2
        ≤ ((256 * Real.exp 2 + 4) * ℓ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLc_ℓ 2
      _ ≤ (Real.exp (ℓ / 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hℓ2_le 2
      _ = Real.exp ℓ := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ = N := hNexp
  have h2LN : 2 * linearDefectCutoff c ≤ N := by
    obtain ⟨hL3, -, -, -⟩ := linearDefectCutoff_bounds hc1
    have hLc_R : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
    have : (2 * linearDefectCutoff c : ℝ) ≤ N := by nlinarith only [hLc_R, hL2N]
    exact_mod_cast this
  obtain ⟨h, T, lam, β, K', hlam, hlam1, hhdef, hh0, hh1, hT0, hT, hlogT, hTh, hhℓ, hlamG, hK'1,
    ht₀', hpnt', hlogK', hK'le, hβ, hβ0⟩ := exists_far_parameters hCψ hc₀ ht₀1 hℓ1 hC0 hlogℓ
  have hexp := far_exp_le hNexp hc1 hcℓ hℓ1 hα'0 hlam hCβ hβ hQ5
  clear hQ5
  set M := N / linearDefectCutoff c
  set x := primeHorizonExtension z
  set P := ∑ n ∈ Icc 1 M, x n ^ 2
  set S7 := topCollarSeventhMass M N x
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS7_0 : 0 ≤ S7 := topCollarSeventhMass_nonneg M N x
  -- Power bounds on `2 K₁_far`: `(2 K₁_far)^8 ≤ 1 / M_far` and `(2 K₁_far)^16 ≤ 1 / M_far`
  have h2K₁_8 : (2 * K₁_far) ^ 8 ≤ 1 / M_far := by
    rw [h2K₁, one_div_pow]
    exact one_div_le_one_div_of_le hM_pos (by
      calc M_far = M_far ^ 1 := (pow_one _).symm
        _ ≤ M_far ^ 8 := pow_le_pow_right₀ hM1 (by norm_num))
  have h2K₁_16 : (2 * K₁_far) ^ 16 ≤ 1 / M_far := by
    rw [h2K₁, one_div_pow]
    exact one_div_le_one_div_of_le hM_pos (by
      calc M_far = M_far ^ 1 := (pow_one _).symm
        _ ≤ M_far ^ 16 := pow_le_pow_right₀ hM1 (by norm_num))
  have hc8_ub : c ^ 8 ≤ (2 * K₁_far) ^ 8 * ℓ := by
    have hp := pow_le_pow_left₀ hc0.le hc_ub 8
    rw [mul_pow, ← Real.rpow_natCast (ℓ ^ (1 / 8 : ℝ)), ← Real.rpow_mul hℓpos.le] at hp
    norm_num at hp
    exact hp
  have hc16_ub : c ^ 16 ≤ (2 * K₁_far) ^ 16 * ℓ ^ 2 := by
    have hp := pow_le_pow_left₀ (pow_nonneg hc0.le 8) hc8_ub 2
    linarith only [hp, (by ring : (c ^ 8) ^ 2 = c ^ 16),
      (by ring : ((2 * K₁_far) ^ 8 * ℓ) ^ 2 = (2 * K₁_far) ^ 16 * ℓ ^ 2)]
  -- 1. Top mass cost `C_S c ≤ (1 / 8) (dyadicTopMassConstant / c^7) ℓ`
  have ha : C_S * c ≤ (1 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * ℓ := by
    have hM_CS : 8 * C_S / dyadicTopMassConstant ≤ M_far :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hprod : 8 * C_S * (2 * K₁_far) ^ 8 ≤ dyadicTopMassConstant := by
      have hmul := mul_le_mul_of_nonneg_left h2K₁_8
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hCS.le)
      have hdiv : 8 * C_S * (1 / M_far) ≤ dyadicTopMassConstant := by
        rw [mul_one_div, div_le_iff₀ hM_pos]
        have := (div_le_iff₀ hg₀).mp hM_CS
        linarith
      exact hmul.trans hdiv
    rw [one_eighth_div_mul_eq, le_div_iff₀ (by positivity)]
    calc C_S * c * (8 * c ^ 7) = 8 * C_S * c ^ 8 := by ring
      _ ≤ 8 * C_S * ((2 * K₁_far) ^ 8 * ℓ) :=
          mul_le_mul_of_nonneg_left hc8_ub (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hCS.le)
      _ = (8 * C_S * (2 * K₁_far) ^ 8) * ℓ := by ring
      _ ≤ dyadicTopMassConstant * ℓ := mul_le_mul_of_nonneg_right hprod hℓpos.le
  -- 2. Prefix mass cost `C_P c ≤ (θ / 4) ℓ`
  have hb : C_P * c ≤ θ / 4 * ℓ := by
    rw [Real.rpow_one] at hQb
    have h1 : 4 * C_P / θ * c ≤ ℓ := by
      calc 4 * C_P / θ * c ≤ 4 * C_P / θ * ℓ ^ (1 / 8 : ℝ) :=
            mul_le_mul_of_nonneg_left hc18
              (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCP.le) hθ.le)
        _ = (4 * C_P / κ_P) * ℓ ^ (1 / 8 : ℝ) * (1 + Real.log ℓ) ^ B := by
            rw [hθ_inv]; ring
        _ ≤ ℓ := hQb
    calc C_P * c = θ / 4 * (4 * C_P / θ * c) := mul_eq_quarter_mul hθ.ne'
      _ ≤ θ / 4 * ℓ :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hθ.le (by norm_num : (0 : ℝ) ≤ 4))
  clear hQb
  -- 3. Window cost: pole part paid by `(1 / 8) (dyadicTopMassConstant / c^7) ℓ S7`, mass part by `(θ / 4) ℓ P`
  have hc_win : 16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * ℓ) *
        (splineWindowConstant * ((c / N) / h ^ 2)) *
        windowSumBound C_ψ c₀ ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp (c / N)⌋₊ M K' x h ≤
      (1 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * ℓ * S7 + θ / 4 * ℓ * P := by
    obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
    have hMN : M ≤ N := Nat.div_le_self _ _
    have hM1_nat : 1 ≤ M :=
      (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
    have hσ_S7 : prefixPoleMoment M x ^ 2 ≤ S7 :=
      prefixPoleMoment_sq_le_topCollarSeventhMass hN2 hMN hz
    have hHM : prefixHarmonic M ≤ 1 + ℓ := by
      have h1 := RHTower.sum_Icc_one_div_le hM1_nat
      have h2 : Real.log (M : ℝ) ≤ ℓ :=
        Real.log_le_log (by exact_mod_cast hM1_nat) (by exact_mod_cast hMN)
      unfold prefixHarmonic; linarith only [h1, h2]
    have hH0 : 0 ≤ prefixHarmonic M :=
      sum_nonneg fun m _ => div_nonneg zero_le_one (Nat.cast_nonneg m)
    have hC₄ : 1 ≤ Real.log 4 + 4 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
    have hw0 : 0 < c / (N : ℝ) := div_pos hc0 hNR
    have hcN : c ≤ (N : ℝ) := by
      have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by
        exact_mod_cast (show linearDefectCutoff c ≤ N by omega)
      linarith only [h4c, hLNR, hc0]
    have hw1 : c / (N : ℝ) ≤ 1 := (div_le_one hNR).mpr hcN
    have hwB : (c / (N : ℝ)) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ ≤ Real.exp 1 * c := by
      have hBn_le : (⌊(N : ℝ) * Real.exp (c / N)⌋₊ : ℝ) ≤ N * Real.exp (c / N) :=
        Nat.floor_le (by positivity)
      calc (c / (N : ℝ)) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊
          ≤ (c / (N : ℝ)) * (N * Real.exp (c / N)) := mul_le_mul_of_nonneg_left hBn_le hw0.le
        _ = c * Real.exp (c / N) := by rw [← mul_assoc, div_mul_cancel₀ _ hNR.ne']
        _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hc0.le
        _ = Real.exp 1 * c := by ring
    have hAB : ((M : ℝ) / 2) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
      have h1 : (N : ℝ) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
        exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hNR.le (Real.one_le_exp hw0.le))
      have h2 : (M : ℝ) ≤ N := by exact_mod_cast hMN
      linarith only [h1, h2]
    set ΛK := β + 1 + (Real.log 4 + 4)
    have hLK' : shortOrderWeight K' ≤ ΛK := by
      have := shortOrderWeight_le hK'1; simp only [ΛK]; linarith only [this, hlogK']
    have hΨK' : ∑ k ∈ range K', (Λ k : ℝ) ≤ (Real.log 4 + 4) * (2 * Real.exp β) :=
      (sum_vonMangoldt_range_le K').trans
        (mul_le_mul_of_nonneg_left hK'le (zero_le_one.trans hC₄))
    have hWS := windowSumBound_div_le (M := M) x hh0 hh1 hCψ hpnt' hw0.le hc0.le hwB
      (by positivity) hAB hLK' hΨK'
    have hwhΨ : ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)) ≤ 1 := by
      rw [hhdef]; exact window_ratio_le hNR hℓpos hexp
    set ηi := 16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * ℓ)
    have hηi0 : 0 ≤ ηi := by simp only [ηi]; positivity
    have hηi : ηi ≤ 16 * (1 + 2 * Real.exp 1) * c ^ 8 / (dyadicTopMassConstant * ℓ) := by
      simp only [ηi]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hγ : 1 + 2 * Real.exp 1 * c ≤ (1 + 2 * Real.exp 1) * c := by
        nlinarith only [hc1, Real.exp_pos 1]
      rw [eta_num_eq hc0.ne']
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have := mul_le_mul_of_nonneg_left hγ (show (0 : ℝ) ≤ 16 * c ^ 7 by positivity)
      nlinarith only [this]
    have hX := mul_le_mul_of_nonneg_left hWS (mul_nonneg hηi0 hκ_nn)
    rw [show ηi * (splineWindowConstant * ((c / N) / h ^ 2)) *
        windowSumBound C_ψ c₀ ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp (c / N)⌋₊ M K' x h =
      (ηi * splineWindowConstant) * (((c / N) / h ^ 2) *
        windowSumBound C_ψ c₀ ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp (c / N)⌋₊ M K' x h) by ring]
    refine hX.trans ?_
    rw [mul_add]
    refine add_le_add ?_ ?_
    · -- Pole part `≤ (1 / 8) * (dyadicTopMassConstant / c ^ 7) * ℓ * S7`
      have hM_win : 1024 * (1 + 2 * Real.exp 1) * (splineWindowConstant + 1) * Real.exp 2 /
          dyadicTopMassConstant ^ 2 ≤ M_far :=
        (le_max_right _ _).trans (le_max_right _ _)
      have hprod16 : 1024 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 *
          (2 * K₁_far) ^ 16 ≤ dyadicTopMassConstant ^ 2 := by
        have h1 : 1024 * (1 + 2 * Real.exp 1) * (splineWindowConstant + 1) * Real.exp 2 *
            (2 * K₁_far) ^ 16 ≤ dyadicTopMassConstant ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_left h2K₁_16
            (by positivity : 0 ≤ 1024 * (1 + 2 * Real.exp 1) * (splineWindowConstant + 1) * Real.exp 2)
          have hdiv : 1024 * (1 + 2 * Real.exp 1) * (splineWindowConstant + 1) * Real.exp 2 *
              (1 / M_far) ≤ dyadicTopMassConstant ^ 2 := by
            rw [mul_one_div, div_le_iff₀ hM_pos]
            have := (div_le_iff₀ (pow_pos hg₀ 2)).mp hM_win
            linarith
          exact hmul.trans hdiv
        have h2 : 1024 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 *
            (2 * K₁_far) ^ 16 ≤
            1024 * (1 + 2 * Real.exp 1) * (splineWindowConstant + 1) * Real.exp 2 *
              (2 * K₁_far) ^ 16 := by
          have : 0 ≤ 1024 * (1 + 2 * Real.exp 1) * Real.exp 2 * (2 * K₁_far) ^ 16 := by positivity
          linarith
        exact h2.trans h1
      calc (ηi * splineWindowConstant) * (8 * Real.exp 2 * c * prefixPoleMoment M x ^ 2)
          ≤ (16 * (1 + 2 * Real.exp 1) * c ^ 8 / (dyadicTopMassConstant * ℓ) *
              splineWindowConstant) * (8 * Real.exp 2 * c * S7) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hηi hκ_nn)
              (mul_le_mul_of_nonneg_left hσ_S7 (by positivity)) (by positivity) (by positivity)
        _ = (1 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * ℓ * S7 *
            (1024 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 * c ^ 16 /
              (dyadicTopMassConstant ^ 2 * ℓ ^ 2)) :=
            window_pole_algebraic_eq hg₀.ne' hℓpos.ne' hc0.ne'
        _ ≤ (1 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * ℓ * S7 * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [div_le_one (by positivity)]
            calc 1024 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 * c ^ 16
                ≤ 1024 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 *
                    ((2 * K₁_far) ^ 16 * ℓ ^ 2) :=
                  mul_le_mul_of_nonneg_left hc16_ub (by positivity)
              _ = (1024 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 *
                    (2 * K₁_far) ^ 16) * ℓ ^ 2 := by ring
              _ ≤ dyadicTopMassConstant ^ 2 * ℓ ^ 2 :=
                  mul_le_mul_of_nonneg_right hprod16 (sq_nonneg _)
        _ = (1 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * ℓ * S7 := mul_one _
    · -- Mass part `≤ θ / 4 * ℓ * P`
      have hL2K : Real.log (2 * K') ≤ ΛK + 1 := by
        have hK'R : (0 : ℝ) < K' := by exact_mod_cast hK'1
        rw [Real.log_mul (by norm_num) hK'R.ne']
        have := Real.log_two_lt_d9
        simp only [ΛK]; linarith only [hlogK', this, hC₄]
      have hΛK1 : 1 ≤ ΛK := by simp only [ΛK]; linarith only [hβ0, hC₄]
      have hΛKb : ΛK ≤ C_B * lam ^ 2 := by
        have hl2 : 1 ≤ lam ^ 2 := one_le_pow₀ hlam1
        simp only [ΛK, C_B]
        have := mul_le_mul_of_nonneg_left hl2
          (show (0 : ℝ) ≤ 1 + (Real.log 4 + 4) by linarith only [hC₄])
        linarith only [hβ, this]
      have hhH : h * prefixHarmonic M ≤ 2 := by
        have := mul_le_mul_of_nonneg_left hHM hh0.le; linarith only [this, hhℓ]
      have hh2H : h ^ 2 * prefixHarmonic M ≤ 2 := by
        calc h ^ 2 * prefixHarmonic M = h * (h * prefixHarmonic M) := by ring
          _ ≤ 1 * 2 := mul_le_mul hh1 hhH (mul_nonneg hh0.le hH0) zero_le_one
          _ = 2 := by ring
      have hΛ2 : ΛK ≤ ΛK ^ 2 := le_self_pow₀ hΛK1 two_ne_zero
      have hΛ1 : 1 ≤ ΛK ^ 2 := one_le_pow₀ hΛK1
      have hPc : 8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
          48 * Real.exp 1 * c * h * prefixHarmonic M +
          2 * ΛK * (Real.exp 2 * c * ΛK +
            ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β))) ≤
          c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2 := by
        have t1 : 1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M ≤ 11 * ΛK ^ 2 := by
          linarith only [hL2K, hh2H, hΛ2, hΛ1, hΛK1]
        have t1' := mul_le_mul_of_nonneg_left t1 (show 0 ≤ 8 * Real.exp 2 * c by positivity)
        have t2 : 48 * Real.exp 1 * c * h * prefixHarmonic M ≤ 96 * Real.exp 1 * c * ΛK ^ 2 := by
          have a1 := mul_le_mul_of_nonneg_left hhH (show 0 ≤ 48 * Real.exp 1 * c by positivity)
          have a2 := mul_le_mul_of_nonneg_left hΛ1 (show 0 ≤ 96 * Real.exp 1 * c by positivity)
          linarith only [a1, a2,
            (by ring : 48 * Real.exp 1 * c * h * prefixHarmonic M =
              48 * Real.exp 1 * c * (h * prefixHarmonic M))]
        have t3 : 2 * ΛK * (Real.exp 2 * c * ΛK +
            ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β))) ≤
            (2 * Real.exp 2 + 2) * c * ΛK ^ 2 := by
          have a1 := mul_le_mul_of_nonneg_left hwhΨ (show 0 ≤ 2 * ΛK by linarith only [hΛK1])
          have a2 : ΛK ^ 2 ≤ c * ΛK ^ 2 := le_mul_of_one_le_left (by positivity) hc1
          linarith only [a1, a2, hΛ2]
        have hcΛ : 0 ≤ (10 * Real.exp 2 + 4 * Real.exp 1 + 8) * (c * ΛK ^ 2) := by positivity
        linarith only [t1', t2, t3, hcΛ]
      have hΛsq : ΛK ^ 2 ≤ C_B ^ 2 * lam ^ 4 := by
        have := pow_le_pow_left₀ (by linarith) hΛKb 2
        rw [mul_pow, ← pow_mul] at this; exact this
      have hc9 : c ^ 9 ≤ ℓ ^ (9 * α') := pow_le_rpow_of_le_rpow hc1 hcα' hℓpos.le 9
      have hlam4 : lam ^ 4 = ℓ ^ (4 * α') := by
        rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul hℓpos.le]; ring_nf
      have hc13 : c ^ 9 * lam ^ 4 ≤ ℓ ^ (13 * α') := by
        rw [hlam4, show 13 * α' = 9 * α' + 4 * α' by ring, Real.rpow_add hℓpos]
        exact mul_le_mul_of_nonneg_right hc9 (by positivity)
      have hL2K0 : 0 ≤ 1 + Real.log (2 * K') := by
        have hK'R : (1 : ℝ) ≤ K' := by exact_mod_cast hK'1
        have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * K' by linarith only [hK'R])
        linarith only [this]
      have hwhΨ0 : 0 ≤ ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)) := by
        have := zero_le_one.trans hC₄; positivity
      have hb1 : (ηi * splineWindowConstant) *
          ((8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
            48 * Real.exp 1 * c * h * prefixHarmonic M +
            2 * ΛK * (Real.exp 2 * c * ΛK +
              ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)))) * P) ≤
          16 * (1 + 2 * Real.exp 1) * c ^ 8 / (dyadicTopMassConstant * ℓ) * splineWindowConstant *
            ((c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * (C_B ^ 2 * lam ^ 4)) * P) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hηi hκ_nn)
          (mul_le_mul_of_nonneg_right (hPc.trans (mul_le_mul_of_nonneg_left hΛsq (by positivity)))
            hP0) (by positivity) (by positivity)
      refine hb1.trans ?_
      rw [Real.rpow_two] at hQP
      have hAw_nn : 0 ≤ 64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
          (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 / (dyadicTopMassConstant * θ) :=
        div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64)
            (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 1).le))) hκ_nn)
          (add_nonneg (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) (Real.exp_pos 2).le)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) (Real.exp_pos 1).le))
            (by norm_num : (0 : ℝ) ≤ 10)))
          (sq_nonneg C_B)) (mul_nonneg hg₀.le hθ.le)
      have hQP_θ : (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
          (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
          (dyadicTopMassConstant * θ)) * (c ^ 9 * lam ^ 4) ≤ ℓ ^ 2 := by
        calc (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
              (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
              (dyadicTopMassConstant * θ)) * (c ^ 9 * lam ^ 4)
            ≤ (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
                (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
                (dyadicTopMassConstant * θ)) * ℓ ^ (13 * α') :=
              mul_le_mul_of_nonneg_left hc13 hAw_nn
          _ = (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
                (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
                (dyadicTopMassConstant * κ_P)) * ℓ ^ (13 * α') * (1 + Real.log ℓ) ^ B := by
              rw [← div_div, hθ_inv, div_div]; ring
          _ ≤ ℓ ^ 2 := hQP
      rw [window_mass_algebraic_eq hg₀.ne' hℓpos.ne' hθ.ne']
      calc _ ≤ θ / 4 * ℓ * P * 1 :=
            mul_le_mul_of_nonneg_left ((div_le_one (pow_pos hℓpos 2)).mpr hQP_θ)
              (mul_nonneg (mul_nonneg (div_nonneg hθ.le (by norm_num : (0 : ℝ) ≤ 4)) hℓpos.le) hP0)
        _ = θ / 4 * ℓ * P := mul_one _
  clear hQP
  -- 4. Translate cost `≤ (θ / 4) ℓ` via `far_cost_translate`
  have hd : (16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * ℓ) * (T * h) ^ 2 +
        8 / (Real.log T - factorialSpanGammaOffset)) *
      ((1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
        (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
          (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ / ((M : ℝ) / 2)) +
            2 * (Real.log 4 + 4)))) ≤ θ / 4 * ℓ := by
    have hK₂ : 0 ≤ K₂ := by
      have he1 := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
      have he2 := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
      have h1 : 0 ≤ Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) :=
        Real.log_nonneg (by nlinarith only [he1, he2])
      have hl4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      simp only [K₂]; linarith only [h1, hl4]
    have hΦ := translate_factor_le hc1 h2LN
    set Φ := (1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
      (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
        (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))
    have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
    have hΦ' : Φ ≤ (1 + 2 * Real.exp 2) * K₂ * c * (2 * ℓ) * (1 + Real.log c) := by
      refine hΦ.trans ?_
      have h1 : 1 + ℓ ≤ 2 * ℓ := by linarith only [hℓ1]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h1
          (mul_nonneg (mul_nonneg
            (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 2).le)) hK₂) hc0.le))
        (by linarith only [hlogc0])
    have hΦ0 : 0 ≤ Φ := by
      have hN1 : 1 ≤ N := by omega
      have hBn1 : (1 : ℝ) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
        have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        have : 1 ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := Nat.le_floor (by
          push_cast
          exact hN1R.trans (le_mul_of_one_le_right hNR.le
            (Real.one_le_exp (div_nonneg hc0.le hNR.le))))
        exact_mod_cast this
      have hlogBn := Real.log_nonneg hBn1
      have hM1_nat : 1 ≤ M :=
        (Nat.le_div_iff_mul_le (by have := (linearDefectCutoff_bounds hc1).1; omega)).mpr (by omega)
      have hMN : M ≤ N := Nat.div_le_self _ _
      have hrat : 1 ≤ 2 * (⌊(N : ℝ) * Real.exp (c / N)⌋₊ : ℝ) / ((M : ℝ) / 2) := by
        have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1_nat
        rw [le_div_iff₀ (by linarith only [hM1R])]
        have h1 : (M : ℝ) ≤ N := by exact_mod_cast hMN
        have h2 : (N : ℝ) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
          exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hNR.le
            (Real.one_le_exp (div_nonneg hc0.le hNR.le)))
        linarith only [h1, h2]
      have h3 := Real.log_nonneg hrat
      have hl4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      refine mul_nonneg (add_nonneg zero_le_one (mul_nonneg
        (mul_nonneg zero_le_two (Real.exp_pos 1).le)
        (mul_nonneg (div_nonneg hc0.le hNR.le) (Nat.cast_nonneg _))))
        (mul_nonneg hlogBn (by linarith only [h3, hl4]))
    have hηi : 16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * ℓ) ≤
        16 * (1 + 2 * Real.exp 1) * c ^ 8 / (dyadicTopMassConstant * ℓ) := by
      rw [div_le_div_iff₀ (mul_pos (div_pos hg₀ (pow_pos hc0 7)) hℓpos) (mul_pos hg₀ hℓpos)]
      have hγ : 1 + 2 * Real.exp 1 * c ≤ (1 + 2 * Real.exp 1) * c := by
        nlinarith only [hc1, Real.exp_pos 1]
      rw [eta_num_eq hc0.ne']
      refine mul_le_mul_of_nonneg_right ?_ (mul_pos (div_pos hg₀ (pow_pos hc0 7)) hℓpos).le
      have := mul_le_mul_of_nonneg_left hγ
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (pow_nonneg hc0.le 7))
      nlinarith only [this]
    have h9 := pow_le_rpow_of_le_rpow hc1 hcα' hℓpos.le 9
    norm_num at h9
    have hQd_θ : 256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) * K₂ /
        (dyadicTopMassConstant * θ) * ℓ ^ (9 * α' + 1) * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (4 : ℝ) := by
      refine le_trans (le_of_eq ?_) hQd
      rw [← div_div, hθ_inv, div_div, pow_one, pow_succ]
      ring
    have hQd'_θ : 256 * (1 + 2 * Real.exp 2) * K₂ / θ * ℓ ^ (1 / 8 + 1 : ℝ) *
        (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (1 + α') := by
      refine le_trans (le_of_eq ?_) hQd'
      rw [hθ_inv, pow_one, pow_succ]
      ring
    rw [hTh, hlogT]
    exact far_cost_translate hℓ1 hc1 hθ hg₀ hK₂ hηi hΦ' hΦ0 h9 hc18
      (Real.log_le_log hc0 hcℓ) hlogc0 hQd_θ hQd'_θ hlam hlamG (zero_lt_one.trans_le hlam1)
  clear hQd hQd'
  -- Assemble all four budgets
  have hE := hres hc1 hL2N hz hh0 hh1 hT0 hT hK'1 ht₀'
  clear hres
  have haS := mul_le_mul_of_nonneg_right ha hS7_0
  have hbP := mul_le_mul_of_nonneg_right hb hP0
  have hdP := mul_le_mul_of_nonneg_right hd hP0
  have hθP_nn : 0 ≤ θ * ℓ * P := mul_nonneg (mul_nonneg hθ.le hℓpos.le) hP0
  have hid_top := top_budget_algebraic_eq (g0 := dyadicTopMassConstant) (l := ℓ) (S := S7) hc0.ne'
  have hid_θ : (κ_P * ℓ / (1 + Real.log ℓ) ^ B) * P = θ * ℓ * P := by
    rw [hθ_def]; ring
  linarith only [hE, haS, hbP, hc_win, hdP, hθP_nn, hid_top, hid_θ]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_critical_multiple_far_reserve
