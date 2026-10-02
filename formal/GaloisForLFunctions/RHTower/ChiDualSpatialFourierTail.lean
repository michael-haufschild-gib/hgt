import GaloisForLFunctions.RHTower.ChiDualUnitAmplitudeBounds
import GaloisForLFunctions.RHTower.ChiDualSignedIntegrationByParts
import GaloisForLFunctions.RHTower.ChiDualSpatialFrequencyBounds
import GaloisForLFunctions.RHTower.ZetaChiDualIntegerBlockPoisson
import GaloisForLFunctions.RHTower.CompactGaussianReflectedRowBounds
import GaloisForLFunctions.HTGeometry.SquarefreeDensityLowerBound

/-!
# Complete high-frequency tail of the literal chi-dual spatial block

Height-rescaled Gaussian amplitude jets and two exact integrations by parts
control every paired Fourier mode. At half-integer endpoints, opposite first
boundary terms combine before taking norms, giving inverse-square frequency
decay. The bound passes through the full Poisson limit. On every fixed
right-strip disc the actual chi-scaled integer block differs from its spatial
mean and paired first mode by O(N^(-1/2)), uniformly in the physical height.
All amplitude, domain and phase estimates come from the literal source.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- Unit-height normalization of the literal slow spatial amplitude. -/
def chiDualSpatialSlowAmplitude (s : ℂ) (N x : ℝ) : ℂ :=
  (N : ℂ) ^ (s - 1) * chiDualUnitSpatialAmplitude s (x / N)

/-- Actual first spatial derivative after height rescaling. -/
def chiDualSpatialSlowFirst (s : ℂ) (N x : ℝ) : ℂ :=
  ((N : ℂ) ^ (s - 1) / (N : ℂ)) * chiDualUnitSpatialFirst s (x / N)

/-- Actual second spatial derivative after height rescaling. -/
def chiDualSpatialSlowSecond (s : ℂ) (N x : ℝ) : ℂ :=
  ((N : ℂ) ^ (s - 1) / (N : ℂ) ^ 2) * chiDualUnitSpatialSecond s (x / N)

/-- This rescaling is exactly the original cutoff/power coefficient. -/
theorem chiDualSpatialSlowAmplitude_eq (s : ℂ) {N x : ℝ} (hN : 0 < N) (hx : 0 < x) :
    chiDualSpatialSlowAmplitude s N x = smoothAFECutoff (x / N) * (x : ℂ) ^ (s - 1) := by
  have hp : (x : ℂ) ^ (s - 1) = (N : ℂ) ^ (s - 1) * ((x / N : ℝ) : ℂ) ^ (s - 1) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hN.le (div_pos hx hN).le,
      ← Complex.ofReal_mul, mul_div_cancel₀ x hN.ne']
  rw [hp]
  unfold chiDualSpatialSlowAmplitude chiDualUnitSpatialAmplitude
  ring

theorem zetaChiDualSpatialAmplitude_eq_slow (s : ℂ) {N x : ℝ} (hN : 0 < N)
    (hx : 0 < x) (t : ℝ) :
    zetaChiDualSpatialAmplitude s N t x =
      chiDualSpatialSlowAmplitude s N x * bourgainOscillation (t * Real.log x) := by
  rw [chiDualSpatialSlowAmplitude_eq s hN hx]
  rfl

theorem hasDerivAt_chiDualSpatialSlowAmplitude (s : ℂ) {N x : ℝ}
    (hN : 0 < N) (hx : 0 < x) :
    HasDerivAt (chiDualSpatialSlowAmplitude s N) (chiDualSpatialSlowFirst s N x) x := by
  have h := ((hasDerivAt_chiDualUnitSpatialAmplitude s (div_pos hx hN)).scomp x
    ((hasDerivAt_id x).div_const N)).const_mul ((N : ℂ) ^ (s - 1))
  refine h.congr_deriv ?_
  unfold chiDualSpatialSlowFirst
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem hasDerivAt_chiDualSpatialSlowFirst (s : ℂ) {N x : ℝ}
    (hN : 0 < N) (hx : 0 < x) :
    HasDerivAt (chiDualSpatialSlowFirst s N) (chiDualSpatialSlowSecond s N x) x := by
  have h := ((hasDerivAt_chiDualUnitSpatialFirst s (div_pos hx hN)).scomp x
    ((hasDerivAt_id x).div_const N)).const_mul ((N : ℂ) ^ (s - 1) / (N : ℂ))
  refine h.congr_deriv ?_
  unfold chiDualSpatialSlowSecond
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- The rescaled literal amplitude and both actual spatial derivatives
remain continuous on the whole positive ray. -/
theorem continuousOn_chiDualSpatialSlowJets (s : ℂ) {N : ℝ} (hN : 0 < N) :
    ContinuousOn (chiDualSpatialSlowAmplitude s N) (Ioi (0 : ℝ)) ∧
    ContinuousOn (chiDualSpatialSlowFirst s N) (Ioi (0 : ℝ)) ∧
    ContinuousOn (chiDualSpatialSlowSecond s N) (Ioi (0 : ℝ)) := by
  obtain ⟨h0, h1, h2⟩ := continuousOn_chiDualUnitSpatialJets
  have hm : MapsTo (fun x : ℝ => (s, x / N)) (Ioi (0 : ℝ)) {p : ℂ × ℝ | 0 < p.2} :=
    fun _ hx => div_pos hx hN
  have hc : ContinuousOn (fun x : ℝ => (s, x / N)) (Ioi (0 : ℝ)) :=
    (continuous_const.prodMk (continuous_id.div_const N)).continuousOn
  have h0' : ContinuousOn (fun x : ℝ => chiDualUnitSpatialAmplitude s (x / N)) (Ioi (0 : ℝ)) :=
    ContinuousOn.comp (f := fun x : ℝ => (s, x / N))
      (g := fun p : ℂ × ℝ => chiDualUnitSpatialAmplitude p.1 p.2) h0 hc hm
  have h1' : ContinuousOn (fun x : ℝ => chiDualUnitSpatialFirst s (x / N)) (Ioi (0 : ℝ)) :=
    ContinuousOn.comp (f := fun x : ℝ => (s, x / N))
      (g := fun p : ℂ × ℝ => chiDualUnitSpatialFirst p.1 p.2) h1 hc hm
  have h2' : ContinuousOn (fun x : ℝ => chiDualUnitSpatialSecond s (x / N)) (Ioi (0 : ℝ)) :=
    ContinuousOn.comp (f := fun x : ℝ => (s, x / N))
      (g := fun p : ℂ × ℝ => chiDualUnitSpatialSecond p.1 p.2) h2 hc hm
  unfold chiDualSpatialSlowAmplitude chiDualSpatialSlowFirst chiDualSpatialSlowSecond
  exact ⟨continuousOn_const.mul h0', continuousOn_const.mul h1', continuousOn_const.mul h2'⟩

/-- Compact-uniform actual amplitude jet bounds with every height factor
explicit. No derivative bound is supplied as an analytic assumption. -/
theorem exists_chiDualSpatialSlowJets_bound (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 0 < N →
      ∀ x : ℝ, x / N ∈ Icc (1 / 6 : ℝ) (1 / 3) →
        ‖chiDualSpatialSlowAmplitude s N x‖ ≤ C * N ^ (s.re - 1) ∧
        ‖chiDualSpatialSlowFirst s N x‖ ≤ C * N ^ (s.re - 1) / N ∧
        ‖chiDualSpatialSlowSecond s N x‖ ≤ C * N ^ (s.re - 1) / N ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_chiDualUnitSpatialJets_bound c r
  refine ⟨C, hC, ?_⟩
  intro s hs N hN x hx
  obtain ⟨h0, h1, h2⟩ := hb s hs (x / N) hx
  have hp : ‖(N : ℂ) ^ (s - 1)‖ = N ^ (s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
    simp only [Complex.sub_re, Complex.one_re]
  have hn : ‖(N : ℂ)‖ = N := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  refine ⟨?_, ?_, ?_⟩
  · unfold chiDualSpatialSlowAmplitude
    rw [norm_mul, hp]
    calc
      _ ≤ N ^ (s.re - 1) * C := mul_le_mul_of_nonneg_left h0 (Real.rpow_nonneg hN.le _)
      _ = _ := by ring
  · unfold chiDualSpatialSlowFirst
    rw [norm_mul, norm_div, hp, hn]
    calc
      _ ≤ (N ^ (s.re - 1) / N) * C := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  · unfold chiDualSpatialSlowSecond
    rw [norm_mul, norm_div, hp, norm_pow, hn]
    calc
      _ ≤ (N ^ (s.re - 1) / N ^ 2) * C := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring

/-- The first exact oscillatory integration-by-parts coefficient. -/
def chiDualIBPFirst (v g : ℂ) : ℂ := v / (I * g)

/-- The second exact coefficient, with the amplitude and phase derivatives explicit. -/
def chiDualIBPSecond (v v1 g g1 : ℂ) : ℂ := -v1 / g ^ 2 + v * g1 / g ^ 3

/-- The entire second integration-by-parts interior derivative. -/
def chiDualIBPRemainder (v v1 v2 g g1 g2 : ℂ) : ℂ :=
  -v2 / g ^ 2 + 3 * v1 * g1 / g ^ 3 + v * g2 / g ^ 3 - 3 * v * g1 ^ 2 / g ^ 4

theorem chiDualIBPFirst_mul_phase (v : ℂ) {g : ℂ} (hg : g ≠ 0) :
    chiDualIBPFirst v g * (I * g) = v := by
  exact div_mul_cancel₀ v (mul_ne_zero I_ne_zero hg)

/-- Differentiation of the actual first coefficient gives iG times the
second coefficient, retaining both amplitude and phase derivative terms. -/
theorem hasDerivAt_chiDualIBPFirst {A G : ℝ → ℂ} {v1 g1 : ℂ} {x : ℝ}
    (hA : HasDerivAt A v1 x) (hG : HasDerivAt G g1 x) (hg : G x ≠ 0) :
    HasDerivAt (fun y => chiDualIBPFirst (A y) (G y))
      (chiDualIBPSecond (A x) v1 (G x) g1 * (I * G x)) x := by
  have h := hA.div (hG.const_mul I) (mul_ne_zero I_ne_zero hg)
  refine h.congr_deriv ?_
  unfold chiDualIBPSecond
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The full second coefficient derivative has all four required terms. -/
theorem hasDerivAt_chiDualIBPSecond {A A1 G G1 : ℝ → ℂ} {v2 g2 : ℂ} {x : ℝ}
    (hA : HasDerivAt A (A1 x) x) (hA1 : HasDerivAt A1 v2 x)
    (hG : HasDerivAt G (G1 x) x) (hG1 : HasDerivAt G1 g2 x) (hg : G x ≠ 0) :
    HasDerivAt (fun y => chiDualIBPSecond (A y) (A1 y) (G y) (G1 y))
      (chiDualIBPRemainder (A x) (A1 x) v2 (G x) (G1 x) g2) x := by
  have h := (hA1.neg.div (hG.pow 2) (pow_ne_zero 2 hg)).add
    ((hA.mul hG1).div (hG.pow 3) (pow_ne_zero 3 hg))
  refine h.congr_deriv ?_
  unfold chiDualIBPRemainder
  dsimp
  field_simp
  ring

/-- The literal spatial log-phase with arbitrary signed Fourier frequency. -/
def chiDualSpatialPhase (t w x : ℝ) : ℝ := t * Real.log x + w * x

def chiDualSpatialPhaseSlope (t w x : ℝ) : ℝ := t / x + w

def chiDualSpatialPhaseSecond (t x : ℝ) : ℝ := -(t / x ^ 2)

def chiDualSpatialPhaseThird (t x : ℝ) : ℝ := 2 * t / x ^ 3

theorem hasDerivAt_chiDualSpatialPhase (t w : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (chiDualSpatialPhase t w) (chiDualSpatialPhaseSlope t w x) x := by
  have h := ((Real.hasDerivAt_log hx.ne').const_mul t).add ((hasDerivAt_id x).const_mul w)
  refine h.congr_deriv ?_
  unfold chiDualSpatialPhaseSlope
  ring

theorem hasDerivAt_chiDualSpatialPhaseSlope (t w : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (chiDualSpatialPhaseSlope t w) (chiDualSpatialPhaseSecond t x) x := by
  have h := ((hasDerivAt_const x t).div (hasDerivAt_id x) hx.ne').add_const w
  refine h.congr_deriv ?_
  unfold chiDualSpatialPhaseSecond
  dsimp
  ring

theorem hasDerivAt_chiDualSpatialPhaseSecond (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (chiDualSpatialPhaseSecond t) (chiDualSpatialPhaseThird t x) x := by
  have h := ((hasDerivAt_const x t).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx.ne')).neg
  refine h.congr_deriv ?_
  unfold chiDualSpatialPhaseThird
  dsimp
  field_simp
  ring

/-- Complex casts of the actual two phase-slope derivatives supply the
coefficient differentiation theorem without a new analytic premise. -/
theorem hasDerivAt_chiDualSpatialPhaseSlope_complex (t w : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => (chiDualSpatialPhaseSlope t w y : ℂ))
      (chiDualSpatialPhaseSecond t x : ℂ) x :=
  (hasDerivAt_chiDualSpatialPhaseSlope t w hx).ofReal_comp

theorem hasDerivAt_chiDualSpatialPhaseSecond_complex (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => (chiDualSpatialPhaseSecond t y : ℂ))
      (chiDualSpatialPhaseThird t x : ℂ) x :=
  (hasDerivAt_chiDualSpatialPhaseSecond t hx).ofReal_comp

theorem norm_chiDualIBPSecond_le (v v1 g g1 : ℂ) :
    ‖chiDualIBPSecond v v1 g g1‖ ≤ ‖v1‖ / ‖g‖ ^ 2 + ‖v‖ * ‖g1‖ / ‖g‖ ^ 3 := by
  unfold chiDualIBPSecond
  calc
    _ ≤ ‖-v1 / g ^ 2‖ + ‖v * g1 / g ^ 3‖ := norm_add_le _ _
    _ = _ := by simp only [norm_div, norm_neg, norm_mul, norm_pow]

theorem norm_chiDualIBPRemainder_le (v v1 v2 g g1 g2 : ℂ) :
    ‖chiDualIBPRemainder v v1 v2 g g1 g2‖ ≤
      ‖v2‖ / ‖g‖ ^ 2 + 3 * ‖v1‖ * ‖g1‖ / ‖g‖ ^ 3 +
        ‖v‖ * ‖g2‖ / ‖g‖ ^ 3 + 3 * ‖v‖ * ‖g1‖ ^ 2 / ‖g‖ ^ 4 := by
  unfold chiDualIBPRemainder
  calc
    _ ≤ ‖-v2 / g ^ 2 + 3 * v1 * g1 / g ^ 3 + v * g2 / g ^ 3‖ +
        ‖3 * v * g1 ^ 2 / g ^ 4‖ := norm_sub_le _ _
    _ ≤ (‖-v2 / g ^ 2‖ + ‖3 * v1 * g1 / g ^ 3‖ + ‖v * g2 / g ^ 3‖) +
        ‖3 * v * g1 ^ 2 / g ^ 4‖ := by
      exact add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
    _ = _ := by simp only [norm_div, norm_neg, norm_mul, norm_pow, norm_ofNat]

/-- The complete second boundary coefficient has a summable frequency bound
and the actual first inverse-height gain. -/
theorem norm_chiDualIBPSecond_scaled_le {v v1 g g1 : ℂ} {u N k : ℝ}
    (hu : 0 ≤ u) (hN : 0 < N) (hk : 1 ≤ k)
    (hv : ‖v‖ ≤ u) (hv1 : ‖v1‖ ≤ u / N)
    (hg : k / 2 ≤ ‖g‖) (hg1 : ‖g1‖ ≤ 100 / N) :
    ‖chiDualIBPSecond v v1 g g1‖ ≤ 804 * u / (N * k ^ 2) := by
  have hk0 : 0 < k := by linarith
  have hkg : 0 < ‖g‖ := lt_of_lt_of_le (by positivity) hg
  have hk23 : k ^ 2 ≤ k ^ 3 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg k)]
  calc
    _ ≤ ‖v1‖ / ‖g‖ ^ 2 + ‖v‖ * ‖g1‖ / ‖g‖ ^ 3 := norm_chiDualIBPSecond_le _ _ _ _
    _ ≤ (u / N) / (k / 2) ^ 2 + u * (100 / N) / (k / 2) ^ 3 := by gcongr
    _ = 4 * u / (N * k ^ 2) + 800 * u / (N * k ^ 3) := by ring
    _ ≤ 4 * u / (N * k ^ 2) + 800 * u / (N * k ^ 2) := by gcongr
    _ = _ := by ring

/-- All four terms of the full interior derivative retain two inverse-height
factors and summable frequency decay. -/
theorem norm_chiDualIBPRemainder_scaled_le {v v1 v2 g g1 g2 : ℂ} {u N k : ℝ}
    (hu : 0 ≤ u) (hN : 0 < N) (hk : 1 ≤ k)
    (hv : ‖v‖ ≤ u) (hv1 : ‖v1‖ ≤ u / N) (hv2 : ‖v2‖ ≤ u / N ^ 2)
    (hg : k / 2 ≤ ‖g‖) (hg1 : ‖g1‖ ≤ 100 / N) (hg2 : ‖g2‖ ≤ 1000 / N ^ 2) :
    ‖chiDualIBPRemainder v v1 v2 g g1 g2‖ ≤ 490404 * u / (N ^ 2 * k ^ 2) := by
  have hk0 : 0 < k := by linarith
  have hkg : 0 < ‖g‖ := lt_of_lt_of_le (by positivity) hg
  have hk23 : k ^ 2 ≤ k ^ 3 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg k)]
  have hk2 : 1 ≤ k ^ 2 := by nlinarith only [hk, sq_nonneg (k - 1)]
  have hk24 : k ^ 2 ≤ k ^ 4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hk2) (sq_nonneg k)]
  calc
    _ ≤ ‖v2‖ / ‖g‖ ^ 2 + 3 * ‖v1‖ * ‖g1‖ / ‖g‖ ^ 3 +
        ‖v‖ * ‖g2‖ / ‖g‖ ^ 3 + 3 * ‖v‖ * ‖g1‖ ^ 2 / ‖g‖ ^ 4 :=
      norm_chiDualIBPRemainder_le _ _ _ _ _ _
    _ ≤ (u / N ^ 2) / (k / 2) ^ 2 + 3 * (u / N) * (100 / N) / (k / 2) ^ 3 +
        u * (1000 / N ^ 2) / (k / 2) ^ 3 + 3 * u * (100 / N) ^ 2 / (k / 2) ^ 4 := by gcongr
    _ = 4 * u / (N ^ 2 * k ^ 2) + 2400 * u / (N ^ 2 * k ^ 3) +
        8000 * u / (N ^ 2 * k ^ 3) + 480000 * u / (N ^ 2 * k ^ 4) := by ring
    _ ≤ 4 * u / (N ^ 2 * k ^ 2) + 2400 * u / (N ^ 2 * k ^ 2) +
        8000 * u / (N ^ 2 * k ^ 2) + 480000 * u / (N ^ 2 * k ^ 2) := by gcongr
    _ = _ := by ring

/-- The complete actual spatial block has the quantitative second boundary
coefficient and full interior derivative bounds, uniformly on any fixed compact
disc. All amplitude and phase hypotheses are derived from their literal sources. -/
theorem exists_chiDualActualIBP_bounds (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ t : ℝ, N ≤ t ∧ t ≤ 2 * N →
      ∀ x : ℝ, N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2 →
      ∀ k : ℕ, 2 ≤ k → ∀ w : ℝ, w = 2 * Real.pi * k ∨ w = -(2 * Real.pi * k) →
        ‖chiDualSpatialSlowAmplitude s N x‖ ≤ C * N ^ (s.re - 1) ∧
        ‖chiDualIBPSecond (chiDualSpatialSlowAmplitude s N x) (chiDualSpatialSlowFirst s N x)
          (chiDualSpatialPhaseSlope t w x) (chiDualSpatialPhaseSecond t x)‖ ≤
            804 * (C * N ^ (s.re - 1)) / (N * (k : ℝ) ^ 2) ∧
        ‖chiDualIBPRemainder (chiDualSpatialSlowAmplitude s N x) (chiDualSpatialSlowFirst s N x)
          (chiDualSpatialSlowSecond s N x) (chiDualSpatialPhaseSlope t w x)
          (chiDualSpatialPhaseSecond t x) (chiDualSpatialPhaseThird t x)‖ ≤
            490404 * (C * N ^ (s.re - 1)) / (N ^ 2 * (k : ℝ) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_chiDualSpatialSlowJets_bound c r
  refine ⟨C, hC, ?_⟩
  intro s hs N hN t ht x hx k hk w hw
  have hN0 : 0 < N := by linarith
  obtain ⟨hx0, hxlo, hxhi, _, _⟩ := chiDual_spatial_block_ratio_bounds hN ht hx
  have hxn : x / N ∈ Icc (1 / 6 : ℝ) (1 / 3) := by
    constructor
    · apply (le_div_iff₀ hN0).mpr
      linarith
    · apply (div_le_iff₀ hN0).mpr
      linarith
  obtain ⟨hv, hv1, hv2⟩ := hb s hs N hN0 x hxn
  have hu : 0 ≤ C * N ^ (s.re - 1) := mul_nonneg hC.le (Real.rpow_nonneg hN0.le _)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  obtain ⟨hgneg, hgpos⟩ := chiDual_spatial_fourier_frequency_gap hN ht hx hk
  have hg : (k : ℝ) / 2 ≤ ‖(chiDualSpatialPhaseSlope t w x : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold chiDualSpatialPhaseSlope
    rcases hw with rfl | rfl
    · exact hgpos.trans (le_abs_self _)
    · have h : (k : ℝ) / 2 ≤ -(t / x - 2 * Real.pi * k) := by linarith
      simpa only [sub_eq_add_neg] using h.trans (neg_le_abs _)
  obtain ⟨h1, h2⟩ := chiDual_spatial_phase_derivative_bounds hN ht hx
  have hg1 : ‖(chiDualSpatialPhaseSecond t x : ℂ)‖ ≤ 100 / N := by
    simpa only [chiDualSpatialPhaseSecond, Complex.norm_real, Real.norm_eq_abs] using h1
  have hg2 : ‖(chiDualSpatialPhaseThird t x : ℂ)‖ ≤ 1000 / N ^ 2 := by
    simpa only [chiDualSpatialPhaseThird, Complex.norm_real, Real.norm_eq_abs] using h2
  exact ⟨hv, norm_chiDualIBPSecond_scaled_le hu hN0 hkR hv hv1 hg hg1,
    norm_chiDualIBPRemainder_scaled_le hu hN0 hkR hv hv1 hv2 hg hg1 hg2⟩

/-- Exact first integration coefficient of the literal spatial mode. -/
def chiDualSpatialIBPFirst (s : ℂ) (N t w x : ℝ) : ℂ :=
  chiDualIBPFirst (chiDualSpatialSlowAmplitude s N x) (chiDualSpatialPhaseSlope t w x)

/-- Exact second integration coefficient of the literal spatial mode. -/
def chiDualSpatialIBPSecond (s : ℂ) (N t w x : ℝ) : ℂ :=
  chiDualIBPSecond (chiDualSpatialSlowAmplitude s N x) (chiDualSpatialSlowFirst s N x)
    (chiDualSpatialPhaseSlope t w x) (chiDualSpatialPhaseSecond t x)

/-- The entire remaining spatial-mode integrand coefficient. -/
def chiDualSpatialIBPRemainder (s : ℂ) (N t w x : ℝ) : ℂ :=
  chiDualIBPRemainder (chiDualSpatialSlowAmplitude s N x) (chiDualSpatialSlowFirst s N x)
    (chiDualSpatialSlowSecond s N x) (chiDualSpatialPhaseSlope t w x)
    (chiDualSpatialPhaseSecond t x) (chiDualSpatialPhaseThird t x)

/-- Exact twice-integrated literal spatial mode. Only the interval-domain
nonstationarity condition remains here; all source derivatives and continuity
conditions are derived from the actual Gaussian/power amplitude and log phase. -/
theorem integral_chiDualSpatial_eq_two_boundaries (s : ℂ) {N a b : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hab : a ≤ b) (t w : ℝ)
    (hg : ∀ x ∈ Icc a b, chiDualSpatialPhaseSlope t w x ≠ 0) :
    (∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
      Complex.exp (I * (chiDualSpatialPhase t w x : ℂ))) =
      (chiDualSpatialIBPFirst s N t w b - chiDualSpatialIBPSecond s N t w b) *
        Complex.exp (I * (chiDualSpatialPhase t w b : ℂ)) -
      (chiDualSpatialIBPFirst s N t w a - chiDualSpatialIBPSecond s N t w a) *
        Complex.exp (I * (chiDualSpatialPhase t w a : ℂ)) +
      ∫ x in a..b, chiDualSpatialIBPRemainder s N t w x *
        Complex.exp (I * (chiDualSpatialPhase t w x : ℂ)) := by
  have hxpos : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hgc : ∀ x ∈ uIcc a b, (chiDualSpatialPhaseSlope t w x : ℂ) ≠ 0 := by
    intro x hx
    exact Complex.ofReal_ne_zero.mpr (hg x (by simpa only [uIcc_of_le hab] using hx))
  obtain ⟨hA, hA1, hA2⟩ := continuousOn_chiDualSpatialSlowJets s hN
  have hsub : uIcc a b ⊆ Ioi (0 : ℝ) := hxpos
  have hAc := hA.mono hsub
  have hA1c := hA1.mono hsub
  have hA2c := hA2.mono hsub
  have hG : ContinuousOn (fun x => (chiDualSpatialPhaseSlope t w x : ℂ)) (uIcc a b) :=
    fun x hx => (hasDerivAt_chiDualSpatialPhaseSlope_complex t w (hxpos x hx)).continuousAt.continuousWithinAt
  have hG1 : ContinuousOn (fun x => (chiDualSpatialPhaseSecond t x : ℂ)) (uIcc a b) :=
    fun x hx => (hasDerivAt_chiDualSpatialPhaseSecond_complex t (hxpos x hx)).continuousAt.continuousWithinAt
  have hraw : ContinuousOn (chiDualSpatialPhaseThird t) (uIcc a b) := by
    exact continuousOn_const.div (continuousOn_id.pow 3) (fun x hx => pow_ne_zero 3 (hxpos x hx).ne')
  have hG2 : ContinuousOn (fun x => (chiDualSpatialPhaseThird t x : ℂ)) (uIcc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hraw
  have hCc : ContinuousOn (chiDualSpatialIBPSecond s N t w) (uIcc a b) := by
    exact (hA1c.neg.div (hG.pow 2) (fun x hx => pow_ne_zero 2 (hgc x hx))).add
      ((hAc.mul hG1).div (hG.pow 3) (fun x hx => pow_ne_zero 3 (hgc x hx)))
  have hRc : ContinuousOn (chiDualSpatialIBPRemainder s N t w) (uIcc a b) := by
    exact (((hA2c.neg.div (hG.pow 2) (fun x hx => pow_ne_zero 2 (hgc x hx))).add
      (((continuousOn_const.mul hA1c).mul hG1).div (hG.pow 3)
        (fun x hx => pow_ne_zero 3 (hgc x hx)))).add
      ((hAc.mul hG2).div (hG.pow 3) (fun x hx => pow_ne_zero 3 (hgc x hx)))).sub
      (((continuousOn_const.mul hAc).mul (hG1.pow 2)).div (hG.pow 4)
        (fun x hx => pow_ne_zero 4 (hgc x hx)))
  apply integral_cexp_eq_of_two_antiderivatives
    (B' := fun x => chiDualSpatialIBPSecond s N t w x * (I * (chiDualSpatialPhaseSlope t w x : ℂ)))
  · exact fun x hx => hasDerivAt_chiDualSpatialPhase t w (hxpos x hx)
  · intro x hx
    exact hasDerivAt_chiDualIBPFirst (hasDerivAt_chiDualSpatialSlowAmplitude s hN (hxpos x hx))
      (hasDerivAt_chiDualSpatialPhaseSlope_complex t w (hxpos x hx)) (hgc x hx)
  · intro x hx
    exact hasDerivAt_chiDualIBPSecond (hasDerivAt_chiDualSpatialSlowAmplitude s hN (hxpos x hx))
      (hasDerivAt_chiDualSpatialSlowFirst s hN (hxpos x hx))
      (hasDerivAt_chiDualSpatialPhaseSlope_complex t w (hxpos x hx))
      (hasDerivAt_chiDualSpatialPhaseSecond_complex t (hxpos x hx)) (hgc x hx)
  · exact hAc
  · exact hCc.mul (continuousOn_const.mul hG)
  · exact hRc
  · exact fun x hx => chiDualIBPFirst_mul_phase _ (hgc x hx)
  · exact fun _ _ => rfl

/-- The literal opposite spatial phases agree at the actual half-integer
endpoints, including their full height-dependent logarithmic part. -/
theorem chiDualSpatialPhase_half_integer (t : ℝ) (z : ℤ) (k : ℕ) :
    Complex.exp (I * (chiDualSpatialPhase t (2 * Real.pi * k) ((z : ℝ) + 1 / 2) : ℂ)) =
    Complex.exp (I * (chiDualSpatialPhase t (-(2 * Real.pi * k)) ((z : ℝ) + 1 / 2) : ℂ)) := by
  simpa only [chiDualSpatialPhase, Int.cast_natCast, neg_mul, sub_eq_add_neg] using
    chiDual_spatial_phase_half_integer (t * Real.log ((z : ℝ) + 1 / 2)) z (k : ℤ)

/-- Paired first boundary terms of the actual spatial mode have summable
frequency decay on the complete half-integer block. -/
theorem norm_chiDualSpatialIBPFirst_paired_le (s : ℂ) {N t x : ℝ} (hN : 50 ≤ N)
    (ht : N ≤ t ∧ t ≤ 2 * N) (hx : N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2)
    {k : ℕ} (hk : 2 ≤ k) (z : ℤ) (hz : x = (z : ℝ) + 1 / 2) :
    ‖chiDualSpatialIBPFirst s N t (2 * Real.pi * k) x *
        Complex.exp (I * (chiDualSpatialPhase t (2 * Real.pi * k) x : ℂ)) +
      chiDualSpatialIBPFirst s N t (-(2 * Real.pi * k)) x *
        Complex.exp (I * (chiDualSpatialPhase t (-(2 * Real.pi * k)) x : ℂ))‖ ≤
      22 * ‖chiDualSpatialSlowAmplitude s N x‖ / (k : ℝ) ^ 2 := by
  have he : Complex.exp (I * (chiDualSpatialPhase t (2 * Real.pi * k) x : ℂ)) =
      Complex.exp (I * (chiDualSpatialPhase t (-(2 * Real.pi * k)) x : ℂ)) := by
    rw [hz]
    exact chiDualSpatialPhase_half_integer t z k
  rw [he, ← add_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  obtain ⟨_, _, _, hlo, hhi⟩ := chiDual_spatial_block_ratio_bounds hN ht hx
  simpa only [chiDualSpatialIBPFirst, chiDualIBPFirst, chiDualSpatialPhaseSlope, sub_eq_add_neg] using
    norm_chiDual_paired_inverse_frequency_le (chiDualSpatialSlowAmplitude s N x)
      (by linarith : 0 ≤ t / x) hhi hk

/-- Every complete paired nonstationary spatial mode has a summable norm
bound, retaining both endpoint extensions and the entire second-IBP remainder. -/
theorem exists_chiDualSpatialPairedIntegral_bound (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ t : ℝ, N ≤ t ∧ t ≤ 2 * N →
      ∀ a b : ℝ, N / 5 - 1 / 2 ≤ a → b ≤ 6 * N / 25 + 1 / 2 → a ≤ b →
      ∀ za zb : ℤ, a = (za : ℝ) + 1 / 2 → b = (zb : ℝ) + 1 / 2 →
      ∀ k : ℕ, 2 ≤ k →
      ‖(∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
          Complex.exp (I * (chiDualSpatialPhase t (2 * Real.pi * k) x : ℂ))) +
        ∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
          Complex.exp (I * (chiDualSpatialPhase t (-(2 * Real.pi * k)) x : ℂ))‖ ≤
        C * N ^ (s.re - 1) / (k : ℝ) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_chiDualActualIBP_bounds c r
  refine ⟨1000000 * C, by positivity, ?_⟩
  intro s hs N hN t ht a b ha hb' hab za zb hza hzb k hk
  have hN0 : 0 < N := by linarith
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hxa : N / 5 - 1 / 2 ≤ a ∧ a ≤ 6 * N / 25 + 1 / 2 := ⟨ha, hab.trans hb'⟩
  have hxb : N / 5 - 1 / 2 ≤ b ∧ b ≤ 6 * N / 25 + 1 / 2 := ⟨ha.trans hab, hb'⟩
  have ha0 : 0 < a := by linarith
  have hlen : b - a ≤ N := by linarith
  have hxx : ∀ x ∈ Icc a b, N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2 :=
    fun _ hx => ⟨ha.trans hx.1, hx.2.trans hb'⟩
  let w : ℝ := 2 * Real.pi * k
  let u : ℝ := C * N ^ (s.re - 1)
  let L : ℝ := 804 * u / (N * (k : ℝ) ^ 2)
  let R : ℝ := 490404 * u / (N ^ 2 * (k : ℝ) ^ 2)
  let E : ℝ → ℝ → ℂ := fun v x => Complex.exp (I * (chiDualSpatialPhase t v x : ℂ))
  let J : ℝ → ℂ := fun v => ∫ x in a..b, chiDualSpatialSlowAmplitude s N x * E v x
  let Q : ℝ → ℂ := fun v => ∫ x in a..b, chiDualSpatialIBPRemainder s N t v x * E v x
  let F : ℝ → ℂ := fun x =>
    (chiDualSpatialIBPFirst s N t w x - chiDualSpatialIBPSecond s N t w x) * E w x +
    (chiDualSpatialIBPFirst s N t (-w) x - chiDualSpatialIBPSecond s N t (-w) x) * E (-w) x
  have hu : 0 ≤ u := mul_nonneg hC.le (Real.rpow_nonneg hN0.le _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hE (v x : ℝ) : ‖E v x‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hgap (v : ℝ) (hv : v = w ∨ v = -w) :
      ∀ x ∈ Icc a b, chiDualSpatialPhaseSlope t v x ≠ 0 := by
    intro x hx
    obtain ⟨hm, hp⟩ := chiDual_spatial_fourier_frequency_gap hN ht (hxx x hx) hk
    rcases hv with rfl | rfl
    · exact ne_of_gt ((by positivity : (0 : ℝ) < (k : ℝ) / 2).trans_le hp)
    · have hn : t / x - 2 * Real.pi * k < 0 := lt_of_le_of_lt hm (by linarith)
      simpa only [chiDualSpatialPhaseSlope, w, sub_eq_add_neg] using ne_of_lt hn
  have hsplit (v : ℝ) (hv : v = w ∨ v = -w) : J v =
      (chiDualSpatialIBPFirst s N t v b - chiDualSpatialIBPSecond s N t v b) * E v b -
      (chiDualSpatialIBPFirst s N t v a - chiDualSpatialIBPSecond s N t v a) * E v a + Q v :=
    integral_chiDualSpatial_eq_two_boundaries s hN0 ha0 hab t v (hgap v hv)
  have hpoint (x : ℝ) (hx : N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2)
      (v : ℝ) (hv : v = w ∨ v = -w) :
      ‖chiDualSpatialSlowAmplitude s N x‖ ≤ u ∧
      ‖chiDualSpatialIBPSecond s N t v x‖ ≤ L ∧
      ‖chiDualSpatialIBPRemainder s N t v x‖ ≤ R := by
    exact hb s hs N hN t ht x hx k hk v hv
  have hF (x : ℝ) (hx : N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2)
      (z : ℤ) (hz : x = (z : ℝ) + 1 / 2) : ‖F x‖ ≤ 22 * u / (k : ℝ) ^ 2 + 2 * L := by
    obtain ⟨huv, hcp, _⟩ := hpoint x hx w (Or.inl rfl)
    obtain ⟨_, hcm, _⟩ := hpoint x hx (-w) (Or.inr rfl)
    have hp := norm_chiDualSpatialIBPFirst_paired_le s hN ht hx hk z hz
    have hp' : ‖chiDualSpatialIBPFirst s N t w x * E w x +
        chiDualSpatialIBPFirst s N t (-w) x * E (-w) x‖ ≤ 22 * u / (k : ℝ) ^ 2 := by
      apply hp.trans
      gcongr
    have hcp' : ‖chiDualSpatialIBPSecond s N t w x * E w x‖ ≤ L := by
      simpa only [norm_mul, hE, mul_one] using hcp
    have hcm' : ‖chiDualSpatialIBPSecond s N t (-w) x * E (-w) x‖ ≤ L := by
      simpa only [norm_mul, hE, mul_one] using hcm
    calc
      _ = ‖(chiDualSpatialIBPFirst s N t w x * E w x +
          chiDualSpatialIBPFirst s N t (-w) x * E (-w) x) -
          chiDualSpatialIBPSecond s N t w x * E w x -
          chiDualSpatialIBPSecond s N t (-w) x * E (-w) x‖ := by
        congr 1
        dsimp only [F]
        ring
      _ ≤ ‖chiDualSpatialIBPFirst s N t w x * E w x +
          chiDualSpatialIBPFirst s N t (-w) x * E (-w) x‖ +
          ‖chiDualSpatialIBPSecond s N t w x * E w x‖ +
          ‖chiDualSpatialIBPSecond s N t (-w) x * E (-w) x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hQ (v : ℝ) (hv : v = w ∨ v = -w) : ‖Q v‖ ≤ R * N := by
    have hi : ‖Q v‖ ≤ R * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le hab] at hx
      have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
      have hr := (hpoint x (hxx x hx') v hv).2.2
      simpa only [norm_mul, hE, mul_one] using hr
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hlen hR)
  have heq : J w + J (-w) = F b - F a + Q w + Q (-w) := by
    rw [hsplit w (Or.inl rfl), hsplit (-w) (Or.inr rfl)]
    dsimp only [F]
    ring
  change ‖J w + J (-w)‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖F b‖ + ‖F a‖ + ‖Q w‖ + ‖Q (-w)‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ 2 * (22 * u / (k : ℝ) ^ 2 + 2 * L) + 2 * (R * N) := by
      linarith [hF b hxb zb hzb, hF a hxa za hza, hQ w (Or.inl rfl), hQ (-w) (Or.inr rfl)]
    _ = 44 * u / (k : ℝ) ^ 2 + 984024 * u / (N * (k : ℝ) ^ 2) := by
      dsimp only [L, R]
      field_simp
      ring
    _ ≤ 44 * u / (k : ℝ) ^ 2 + 984024 * u / (k : ℝ) ^ 2 := by
      have hden : (k : ℝ) ^ 2 ≤ N * (k : ℝ) ^ 2 := by nlinarith [sq_nonneg (k : ℝ)]
      gcongr
    _ = 984068 * (u / (k : ℝ) ^ 2) := by ring
    _ ≤ 1000000 * (u / (k : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hu (sq_nonneg (k : ℝ)))
    _ = _ := by dsimp only [u]; ring

private theorem two_cexp_mul_cos (v w : ℝ) :
    (2 : ℂ) * Complex.exp (I * (v : ℂ)) * (Real.cos w : ℂ) =
      Complex.exp (I * ((v + w : ℝ) : ℂ)) + Complex.exp (I * ((v - w : ℝ) : ℂ)) := by
  rw [Complex.ofReal_cos]
  calc
    _ = Complex.exp (I * (v : ℂ)) * (2 * Complex.cos (w : ℂ)) := by ring
    _ = Complex.exp (I * (v : ℂ)) *
        (Complex.exp ((w : ℂ) * I) + Complex.exp (-(w : ℂ) * I)) := by rw [Complex.two_cos]
    _ = _ := by
      rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The actual cosine transform is exactly the sum of both signed spatial
modes; no Fourier sign is replaced by an absolute-value majorant here. -/
theorem chiDualSpatial_cos_integral_eq_pair (s : ℂ) {N a b : ℝ} (hN : 0 < N)
    (ha : 0 < a) (hab : a ≤ b) (t : ℝ) (k : ℕ) :
    (2 : ℂ) * (∫ x in a..b, zetaChiDualSpatialAmplitude s N t x *
      (Real.cos (2 * Real.pi * x * k) : ℂ)) =
      (∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
        Complex.exp (I * (chiDualSpatialPhase t (2 * Real.pi * k) x : ℂ))) +
      ∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
        Complex.exp (I * (chiDualSpatialPhase t (-(2 * Real.pi * k)) x : ℂ)) := by
  have hxpos : ∀ x ∈ uIcc a b, 0 < x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hA : ContinuousOn (chiDualSpatialSlowAmplitude s N) (uIcc a b) :=
    (continuousOn_chiDualSpatialSlowJets s hN).1.mono hxpos
  have hi (w : ℝ) : IntervalIntegrable (fun x => chiDualSpatialSlowAmplitude s N x *
      Complex.exp (I * (chiDualSpatialPhase t w x : ℂ))) volume a b := by
    have hp : ContinuousOn (chiDualSpatialPhase t w) (uIcc a b) :=
      fun x hx => (hasDerivAt_chiDualSpatialPhase t w (hxpos x hx)).continuousAt.continuousWithinAt
    exact (hA.mul (Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hp)))).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hi (2 * Real.pi * k)) (hi (-(2 * Real.pi * k)))]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [zetaChiDualSpatialAmplitude_eq_slow s hN (hxpos x hx) t]
  have he := two_cexp_mul_cos (t * Real.log x) (2 * Real.pi * x * k)
  have hp : t * Real.log x + 2 * Real.pi * x * k = chiDualSpatialPhase t (2 * Real.pi * k) x := by
    unfold chiDualSpatialPhase
    ring
  have hm : t * Real.log x - 2 * Real.pi * x * k = chiDualSpatialPhase t (-(2 * Real.pi * k)) x := by
    unfold chiDualSpatialPhase
    ring
  rw [hp, hm] at he
  unfold bourgainOscillation
  calc
    _ = chiDualSpatialSlowAmplitude s N x *
      ((2 : ℂ) * Complex.exp (I * ((t * Real.log x : ℝ) : ℂ)) *
        (Real.cos (2 * Real.pi * x * k) : ℂ)) := by ring
    _ = _ := by rw [he]; ring

/-- The complete finite high-frequency Poisson tail has a bound independent
of its cutoff. Every mode k>=2 is retained with both Fourier signs. -/
theorem exists_chiDualSpatialFourierTail_bound (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ t : ℝ, N ≤ t ∧ t ≤ 2 * N →
      ∀ a b : ℝ, N / 5 - 1 / 2 ≤ a → b ≤ 6 * N / 25 + 1 / 2 → a ≤ b →
      ∀ za zb : ℤ, a = (za : ℝ) + 1 / 2 → b = (zb : ℝ) + 1 / 2 →
      ∀ K : ℕ,
      ‖∑ k ∈ Finset.Ico 2 K, (2 : ℂ) * ∫ x in a..b, zetaChiDualSpatialAmplitude s N t x *
          (Real.cos (2 * Real.pi * x * k) : ℂ)‖ ≤ C * N ^ (s.re - 1) := by
  obtain ⟨C, hC, hb⟩ := exists_chiDualSpatialPairedIntegral_bound c r
  refine ⟨C, hC, ?_⟩
  intro s hs N hN t ht a b ha hb' hab za zb hza hzb K
  have hN0 : 0 < N := by linarith
  have ha0 : 0 < a := by linarith
  have hu : 0 ≤ C * N ^ (s.re - 1) := mul_nonneg hC.le (Real.rpow_nonneg hN0.le _)
  have hk (k : ℕ) (hkm : k ∈ Finset.Ico 2 K) :
      ‖(2 : ℂ) * ∫ x in a..b, zetaChiDualSpatialAmplitude s N t x *
        (Real.cos (2 * Real.pi * x * k) : ℂ)‖ ≤ C * N ^ (s.re - 1) / (k : ℝ) ^ 2 := by
    rw [chiDualSpatial_cos_integral_eq_pair s hN0 ha0 hab t k]
    exact hb s hs N hN t ht a b ha hb' hab za zb hza hzb k (Finset.mem_Ico.mp hkm).1
  have hsum : ∑ k ∈ Finset.Ico 2 K, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 := by
    convert sum_Ico_one_div_sq_le (K := 2) (M := K) (by omega) using 1
    norm_num
  calc
    _ ≤ ∑ k ∈ Finset.Ico 2 K,
        ‖(2 : ℂ) * ∫ x in a..b, zetaChiDualSpatialAmplitude s N t x *
          (Real.cos (2 * Real.pi * x * k) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ico 2 K, C * N ^ (s.re - 1) / (k : ℝ) ^ 2 := Finset.sum_le_sum hk
    _ = (C * N ^ (s.re - 1)) * (∑ k ∈ Finset.Ico 2 K, (1 : ℝ) / (k : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (C * N ^ (s.re - 1)) * 1 := mul_le_mul_of_nonneg_left hsum hu
    _ = _ := mul_one _

/-- The entire spatial zero mode and paired first mode, with the literal chi
factor. The remaining modes are estimated rather than discarded. -/
def chiDualLowSpatialModes (s : ℂ) (N t : ℝ) (A B : ℕ) : ℂ :=
  zetaChi (s + (t : ℂ) * I) *
    ((∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), zetaChiDualSpatialAmplitude s N t x) +
      (2 : ℂ) * ∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2),
        zetaChiDualSpatialAmplitude s N t x * (Real.cos (2 * Real.pi * x) : ℂ))

private theorem sum_shifted_range_eq_first_add_tail (f : ℕ → ℂ) {K : ℕ} (hK : 1 ≤ K) :
    ∑ j ∈ Finset.range K, f (j + 1) = f 1 + ∑ k ∈ Finset.Ico 2 (K + 1), f k := by
  have hr : ∑ j ∈ Finset.range K, f (j + 1) = ∑ k ∈ Finset.Ico 1 (K + 1), f k := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm]
  rw [hr]
  have he := Finset.sum_Ico_consecutive f (show 1 ≤ 2 by omega) (show 2 ≤ K + 1 by omega)
  simpa using he.symm

/-- The literal full integer block differs from its retained low spatial modes
by the complete high-frequency tail. This bound is obtained from the actual
Poisson limit, with every Fourier mode and endpoint contribution accounted for. -/
theorem exists_chiDual_integer_block_low_modes_error (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ t : ℝ, N ≤ t ∧ t ≤ 2 * N →
      ∀ A B : ℕ, N / 5 ≤ (A : ℝ) → (B : ℝ) ≤ 6 * N / 25 → A ≤ B →
      ‖(∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) -
          chiDualLowSpatialModes s N t A B‖ ≤
        C * N ^ (s.re - 1) * ‖zetaChi (s + (t : ℂ) * I)‖ := by
  obtain ⟨C, hC, hb⟩ := exists_chiDualSpatialFourierTail_bound c r
  refine ⟨C, hC, ?_⟩
  intro s hs N hN t ht A B hA hB hAB
  have hN0 : 0 < N := by linarith
  have hA0 : 0 < A := by
    have hAR : (0 : ℝ) < A := by linarith
    exact_mod_cast hAR
  let a : ℝ := (A : ℝ) - 1 / 2
  let b : ℝ := (B : ℝ) + 1 / 2
  let q : ℂ := zetaChi (s + (t : ℂ) * I)
  let M : ℂ := ∫ x in a..b, zetaChiDualSpatialAmplitude s N t x
  let f : ℕ → ℂ := fun k => (2 : ℂ) * ∫ x in a..b,
    zetaChiDualSpatialAmplitude s N t x * (Real.cos (2 * Real.pi * x * k) : ℂ)
  have ha : N / 5 - 1 / 2 ≤ a := by dsimp only [a]; linarith
  have hb' : b ≤ 6 * N / 25 + 1 / 2 := by dsimp only [b]; linarith
  have hab : a ≤ b := by
    have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
    dsimp only [a, b]
    linarith
  have hza : a = (((A : ℤ) - 1 : ℤ) : ℝ) + 1 / 2 := by dsimp only [a]; push_cast; ring
  have hzb : b = ((B : ℤ) : ℝ) + 1 / 2 := by simp only [b, Int.cast_natCast]
  have htail (K : ℕ) : ‖∑ k ∈ Finset.Ico 2 K, f k‖ ≤ C * N ^ (s.re - 1) :=
    hb s hs N hN t ht a b ha hb' hab ((A : ℤ) - 1) (B : ℤ) hza hzb K
  have hp : Tendsto (fun K : ℕ => q * (M + ∑ j ∈ Finset.range K, f (j + 1))) atTop
      (𝓝 (∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t)) := by
    simpa only [q, M, f, a, b, Nat.cast_add, Nat.cast_one] using
      tendsto_zetaChi_dual_integer_block_poisson s hN0 t hA0 hAB
  have hlow : chiDualLowSpatialModes s N t A B = q * (M + f 1) := by
    simp only [chiDualLowSpatialModes, q, M, f, a, b, Nat.cast_one, mul_one]
  rw [hlow]
  apply le_of_tendsto (hp.sub_const (q * (M + f 1))).norm
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with K hK
  rw [sum_shifted_range_eq_first_add_tail f hK]
  have he : q * (M + (f 1 + ∑ k ∈ Finset.Ico 2 (K + 1), f k)) - q * (M + f 1) =
      q * (∑ k ∈ Finset.Ico 2 (K + 1), f k) := by ring
  rw [he, norm_mul]
  calc
    _ ≤ ‖q‖ * (C * N ^ (s.re - 1)) := mul_le_mul_of_nonneg_left (htail (K + 1)) (norm_nonneg q)
    _ = _ := by dsimp only [q]; ring


/-- On every fixed right-strip disc the complete high-mode contribution to
an actual dual integer block tends to zero uniformly at the inverse square-root
conductor rate. The zero mode and both first-mode signs remain explicit. -/
theorem exists_chiDual_integer_block_low_modes_error_decay
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (N : ℝ) (2 * N),
      ∀ s ∈ Metric.closedBall c r,
      ∀ A B : ℕ, (N : ℝ) / 5 ≤ A → (B : ℝ) ≤ 6 * N / 25 → A ≤ B →
      ‖(∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) -
          chiDualLowSpatialModes s N t A B‖ ≤ C * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C₀, hC₀, htail⟩ := exists_chiDual_integer_block_low_modes_error c r
  obtain ⟨C₁, hC₁, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  filter_upwards [hrow, eventually_ge_atTop (50 : ℕ)] with N hrow hN
  have hNR : (50 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  intro t ht s hs A B hA hB hAB
  have hp : (N : ℝ) ^ (s.re - 1) =
      (N : ℝ) ^ (s.re - 1 / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  calc
    _ ≤ C₀ * (N : ℝ) ^ (s.re - 1) * ‖zetaChi (s + (t : ℂ) * I)‖ :=
      htail s hs N hNR t ht A B hA hB hAB
    _ = C₀ * ‖reflectedCompactGaussianRow s N t‖ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [norm_reflectedCompactGaussianRow s hN0 t, hp]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
      exact mul_le_mul_of_nonneg_left (hrow t ht s hs).1 hC₀.le

end RHTower
