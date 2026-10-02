import GaloisForLFunctions.RHTower.ChiDualSpatialMeanSquare
import GaloisForLFunctions.RHTower.ZetaChiDualResonatorIntegral
import GaloisForLFunctions.RHTower.Sieve.LogSeparation
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanIntervalMeanSquare
import GaloisForLFunctions.RHTower.ZetaChiDualHarmonicAllocation

/-!
# Physical quadratic energy of actual prime-masked dual blocks

The sharp separated-frequency mean-square theorem gives 53N times coefficient
energy for literal positive integer frequencies up to N. The actual unit-height
Gaussian amplitude and chi normalization turn this into a constant times the
cardinality of every masked subset of the spatial block. Applying the complete
harmonic cofactor counting bound gives physical free-prime-mask energy with
cost (1+log H)/log N, without the extra logarithmic mean-value loss.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The sharp corpus mean-square inequality applied to every literal positive
integer frequency in a finite physical resonator. No support-cardinality loss. -/
theorem integral_zetaChiDualResonator_sq_sharp_le {N : ℕ} (hN : 0 < N)
    (S : Finset ℕ) (c : ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) (T U : ℝ) :
    (∫ t in T..(T + U), ‖zetaChiDualResonator S c t‖ ^ 2) ≤
      (U + 52 * (N : ℝ)) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < 2 * Real.pi := by positivity
  let u : S → ℝ := fun n => Real.log (n : ℕ) / (2 * Real.pi)
  have hsep (a b : S) (hab : a ≠ b) : 1 / (2 * Real.pi * (N : ℝ)) ≤ |u a - u b| := by
    have hne : (a : ℕ) ≠ b := fun h => hab (Subtype.ext h)
    have hg := Sieve.one_div_nat_upper_le_abs_log_sub (hS a a.property).1
      (hS b b.property).1 (hS a a.property).2 (hS b b.property).2 hne
    dsimp only [u]
    rw [← sub_div, abs_div, abs_of_pos hp]
    calc
      _ = (1 / (N : ℝ)) / (2 * Real.pi) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hg hp.le
  have hb := GaloisForLFunctions.HTGeometry.interval_integral_normSq_expSum_le
    u (fun n : S => c n) (a := T) (ℓ := U) (by positivity : 0 < 1 / (2 * Real.pi * (N : ℝ))) hsep
  have hphase (n : S) (t : ℝ) : GaloisForLFunctions.HTGeometry.mvExp (u n) t =
      bourgainOscillation (t * Real.log (n : ℕ)) := by
    unfold GaloisForLFunctions.HTGeometry.mvExp bourgainOscillation u
    congr 1
    push_cast
    field_simp
  have he (t : ℝ) : (∑ n : S, c n * GaloisForLFunctions.HTGeometry.mvExp (u n) t) =
      zetaChiDualResonator S c t := by
    simp_rw [hphase]
    exact Finset.sum_coe_sort S (fun n => c n * bourgainOscillation (t * Real.log n))
  simp_rw [he] at hb
  rw [Finset.sum_coe_sort S (fun n => ‖c n‖ ^ 2)] at hb
  have hc : 26 / (Real.pi * (1 / (2 * Real.pi * (N : ℝ)))) = 52 * (N : ℝ) := by
    field_simp; ring
  rwa [hc] at hb

/-- Continuity of every literal finite masked dual block on the strict left-of-one region. -/
theorem continuous_chiDualMaskedBlock {s : ℂ} (hs : s.re < 1)
    (N : ℝ) (S : Finset ℕ) : Continuous (fun t =>
      ∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) := by
  have hchi : Continuous (fun t : ℝ => zetaChi (s + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hG : Gammaℝ (1 - (s + (t : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simpa using sub_pos.mpr hs
    have hpath : Continuous (fun u : ℝ => s + (u : ℂ) * I) := by fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => s + (u : ℂ) * I) (x := t)
      (zetaChi_analyticAt hG).continuousAt hpath.continuousAt
  apply continuous_finsetSum
  intro n hn
  unfold zetaChiDualInteriorAtom bourgainOscillation
  exact continuous_const.mul ((hchi.mul continuous_const).mul (by fun_prop))

/-- Every actual masked subset of the spatial block has physical quadratic
energy at most a constant times its cardinality, with no logarithmic loss.
The chi normalization and every coefficient bound are source-derived. -/
theorem exists_chiDual_masked_block_mean_square_bound
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ S : Finset ℕ, (∀ n ∈ S, (N : ℝ) / 5 ≤ n ∧ (n : ℝ) ≤ 6 * N / 25) →
      (∫ t in (N : ℝ)..(2 * N), ‖∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) *
        zetaChiDualInteriorAtom s n t‖ ^ 2) ≤ C * S.card := by
  obtain ⟨C₀, hC₀, hunit⟩ := exists_chiDualUnitSpatialJets_bound c r
  obtain ⟨C₁, hC₁, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  refine ⟨53 * C₀ ^ 2 * C₁ ^ 2, by positivity, ?_⟩
  filter_upwards [hrow, eventually_ge_atTop (1 : ℕ)] with N hrow hN1
  have hN : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  intro s hs S hS
  have hdist : dist s c ≤ r := Metric.mem_closedBall.mp hs
  have hre : |s.re - c.re| ≤ dist s c := by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
  have hs1 : s.re < 1 := by
    have hl := (abs_le.mp (hre.trans hdist)).2
    linarith only [hl, hc1]
  have hn (n : ℕ) (hn : n ∈ S) : 0 < n ∧ n ≤ N := by
    have hb := hS n hn
    have hp : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hN0 (by norm_num)) hb.1
    have hu : (n : ℝ) ≤ N := by linarith only [hb.2, hN0]
    exact ⟨by exact_mod_cast hp, by exact_mod_cast hu⟩
  have hratio (n : ℕ) (hn : n ∈ S) : (n : ℝ) / N ∈ Icc (1 / 6 : ℝ) (1 / 3) := by
    have hb := hS n hn
    constructor
    · apply (le_div_iff₀ hN0).mpr
      linarith only [hb.1, hN0]
    · apply (div_le_iff₀ hN0).mpr
      linarith only [hb.2, hN0]
  let a : ℕ → ℂ := fun n => chiDualUnitSpatialAmplitude s ((n : ℝ) / N)
  let P : ℝ → ℂ := zetaChiDualResonator S a
  have hP : Continuous P := by
    unfold P zetaChiDualResonator
    apply continuous_finsetSum
    intro n _
    unfold bourgainOscillation
    fun_prop
  have heq (t : ℝ) : (∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) =
      (zetaChi (s + (t : ℂ) * I) * (N : ℂ) ^ (s - 1)) * P t := by
    dsimp only [P, zetaChiDualResonator]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hnS
    have hscl := chiDualSpatialSlowAmplitude_eq s (x := (n : ℝ)) hN0 (by exact_mod_cast (hn n hnS).1)
    simp only [chiDualSpatialSlowAmplitude, Complex.ofReal_natCast] at hscl
    unfold zetaChiDualInteriorAtom
    dsimp only [a]
    calc
      _ = zetaChi (s + (t : ℂ) * I) *
          (smoothAFECutoff ((n : ℝ) / N) * (n : ℂ) ^ (s - 1)) *
            bourgainOscillation (t * Real.log n) := by ring
      _ = _ := by rw [← hscl]; ring
  have hfac (t : ℝ) (ht : t ∈ Icc (N : ℝ) (2 * N)) :
      ‖zetaChi (s + (t : ℂ) * I) * (N : ℂ) ^ (s - 1)‖ ^ 2 ≤ C₁ ^ 2 / N := by
    have hi : ‖zetaChi (s + (t : ℂ) * I) * (N : ℂ) ^ (s - 1)‖ * Real.sqrt N =
        ‖reflectedCompactGaussianRow s N t‖ := by
      have hpow : ‖(N : ℂ) ^ (s - 1)‖ = (N : ℝ) ^ (s.re - 1) := by
        simpa only [Complex.ofReal_natCast, Complex.sub_re, Complex.one_re] using
          Complex.norm_cpow_eq_rpow_re_of_pos hN0 (s - 1)
      rw [norm_mul, hpow, norm_reflectedCompactGaussianRow s hN0 t]
      have hp : (N : ℝ) ^ (s.re - 1) * Real.sqrt N = (N : ℝ) ^ (s.re - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
        congr 1
        ring
      calc
        _ = ‖zetaChi (s + (t : ℂ) * I)‖ * ((N : ℝ) ^ (s.re - 1) * Real.sqrt N) := by ring
        _ = _ := by rw [hp]
    have hsq := congrArg (fun x : ℝ => x ^ 2) hi
    rw [mul_pow, Real.sq_sqrt hN0.le] at hsq
    apply (le_div_iff₀ hN0).mpr
    rw [hsq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hrow t ht s hs).1 2
  have hpoint (t : ℝ) (ht : t ∈ Icc (N : ℝ) (2 * N)) :
      ‖∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t‖ ^ 2 ≤
        (C₁ ^ 2 / N) * ‖P t‖ ^ 2 := by
    rw [heq, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (hfac t ht) (sq_nonneg _)
  have hleft : IntervalIntegrable (fun t =>
      ‖∑ n ∈ S, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t‖ ^ 2)
      volume (N : ℝ) (2 * N) :=
    ((continuous_chiDualMaskedBlock hs1 N S).norm.pow 2).intervalIntegrable _ _
  have hright : IntervalIntegrable (fun t => (C₁ ^ 2 / (N : ℝ)) * ‖P t‖ ^ 2)
      volume (N : ℝ) (2 * N) :=
    (continuous_const.mul (hP.norm.pow 2)).intervalIntegrable _ _
  have hb := intervalIntegral.integral_mono_on (a := (N : ℝ)) (b := 2 * (N : ℝ))
    (by linarith only [hN0]) hleft hright hpoint
  rw [intervalIntegral.integral_const_mul] at hb
  have hp := integral_zetaChiDualResonator_sq_sharp_le hN S a hn (N : ℝ) N
  rw [show (N : ℝ) + N = 2 * N by ring] at hp
  have he : (∑ n ∈ S, ‖a n‖ ^ 2) ≤ S.card * C₀ ^ 2 := by
    calc
      _ ≤ ∑ _n ∈ S, C₀ ^ 2 := Finset.sum_le_sum (fun n hnS =>
        pow_le_pow_left₀ (norm_nonneg _) (hunit s hs _ (hratio n hnS)).1 2)
      _ = _ := by simp
  apply hb.trans
  calc
    _ ≤ (C₁ ^ 2 / N) * (((N : ℝ) + 52 * N) * (S.card * C₀ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hp.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ = _ := by field_simp; ring

/-- The complete actual free-prime mask pays harmonic cofactor cost in its
physical second moment. Every selected integer and product cutoff is retained. -/
theorem exists_chiDual_prime_mask_mean_square_log_bound
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ S : Finset ℕ, (∀ n ∈ S, (N : ℝ) / 5 ≤ n ∧ (n : ℝ) ≤ 6 * N / 25) →
      ∀ H : ℕ, 1 ≤ H → H ^ 2 ≤ N →
      (∫ t in (N : ℝ)..(2 * N),
        ‖∑ n ∈ primeWindowSupported S N H, smoothAFECutoff ((n : ℝ) / N) *
          zetaChiDualInteriorAtom s n t‖ ^ 2) * Real.log N ≤
        C * (1 + Real.log H) * N := by
  obtain ⟨C, hC, hbound⟩ := exists_chiDual_masked_block_mean_square_bound c hr hc0 hc1
  refine ⟨C * (2 * Real.log 4), by positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with N hbound hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1R
  intro s hs S hS H hH hHN
  have hsub : primeWindowSupported S N H ⊆ S := Finset.filter_subset _ _
  have hn (n : ℕ) (hn : n ∈ S) : 0 < n ∧ n ≤ N := by
    have hb := hS n hn
    have hp : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hN0 (by norm_num)) hb.1
    have hu : (n : ℝ) ≤ N := by linarith only [hb.2, hN0]
    exact ⟨by exact_mod_cast hp, by exact_mod_cast hu⟩
  have hb := hbound s hs (primeWindowSupported S N H) (fun n hn => hS n (hsub hn))
  have hc := card_primeWindowSupported_mul_log_le_log hH hHN hn
  calc
    _ ≤ (C * (primeWindowSupported S N H).card) * Real.log N :=
      mul_le_mul_of_nonneg_right hb hlog
    _ = C * ((primeWindowSupported S N H).card * Real.log N) := by ring
    _ ≤ C * (2 * (N : ℝ) * Real.log 4 * (1 + Real.log H)) :=
      mul_le_mul_of_nonneg_left hc hC.le
    _ = _ := by ring

end RHTower
