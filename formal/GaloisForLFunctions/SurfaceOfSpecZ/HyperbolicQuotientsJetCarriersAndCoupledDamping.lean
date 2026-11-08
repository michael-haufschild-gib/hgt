import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanFrobeniusIsAHyperbolicGreenFunction
import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanFrobeniusHasInfiniteRank
import GaloisForLFunctions.SurfaceOfSpecZ.TheAtomicGenusIsNLogN
import GaloisForLFunctions.SurfaceOfSpecZ.HasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.ArithmeticElectrostatics.TheSelfIntersectionOfATorsionOrbit
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.EachEntryConfinesItsWeight
import GaloisForLFunctions.RHTower.WeilBlindPoleSignLaw

/-!
# Hyperbolic quotients, causal jet carriers, and coupled damping of Weil's form

This module develops four connected chapters in the archimedean and renormalized geometry of the
surface of `Spec ℤ`.

## 1. Hyperbolic three-space `ℍ³`, geodesic stabilizer rigidity, and the free-space Robin limit

We construct the upper half-space model `H3 = {(z, t) ∈ ℂ × ℝ : 0 < t}` with geodesic distance
`h3Dist`, Hermitian `2 × 2` matrix embedding `toHermMat`, isometric `SL(2, ℂ)` action `h3Act`
(`h3Dist_h3Act`, `h3Dist_triangle`), and `SL(2, ℂ)`-invariant hyperbolic volume measure
`h3Measure = t⁻³ dx dy dt` (`h3Measure_h3Act`). Along the vertical dilation geodesic
`degPoint t = (0, t)`, `SL(2, ℂ)` elements preserving the off-diagonal archimedean Frobenius
profile on distinct integer degrees are classified as the elliptic rotations `diag(a, a⁻¹)`,
`‖a‖ = 1`, fixing the geodesic pointwise (`sl2_preserves_archFrobenius_iff`). Removing the
Newtonian pole `1 / (2 d)` from `2π G_s(d)` yields the constant free-space Robin limit `(1 - s) / 2`
(`1 / 4` at `s = 1 / 2`, `tendsto_freeSpace_robin`), whereas the normalized prime-orbit
self-intersection `I(p, p) / φ(p) = ((p - 2) / (p - 1)) log p` grows unboundedly
(`tendsto_prime_selfIntersection_atTop`, `not_exists_const_robin_prime_selfIntersection`).

## 2. Finite-covolume Kleinian quotients and parabolic cusp divergence

Inscribed Euclidean boxes give a scale-invariant lower bound on the hyperbolic volume of geodesic
balls along the vertical axis (`h3Measure_ball_ge`). Consequently, every discrete subgroup
`Γ ≤ SL(2, ℂ)` of finite hyperbolic covolume obeys a thin–thick dichotomy on any infinite set of
positive integer degrees (`kleinian_thin_thick_dichotomy`): either infinitely many degrees have
bounded injectivity radius modulo the finite pointwise geodesic stabilizer `vertStab Γ`, or pairs of
arbitrarily large degree ratio fold within arbitrarily small quotient distance, forcing any
Newtonian quotient kernel to blow up along prime pairs of arbitrarily large ratio while
`archProfile(log(q / p)) → 0` (`newtonian_quotient_unbounded_on_primes`). Independently, every
non-zero parabolic cusp translation `!![1, ω; 0, 1]` has a harmonically divergent Poincaré series
at the critical weight `s = 1 / 2` (`parabolic_poincare_not_summable_half`), and the horospherical
cusp zero-mode integral equals `min(t, u)^s max(t, u)^{2 - s} / (2 (s - 1) Λ_area)` for `s > 1`
(`integral_horospherical_green_eq`), whose meromorphic continuation to `s = 1 / 2` diverges as
`-n^{3/2} / Λ_area` off-diagonally and `-n² / Λ_area` diagonally (`cuspZeroMode_at_half`,
`tendsto_abs_cuspZeroMode_diag_div_log`).

## 3. Pure trivial-zero jet Cauchy blocks and the causal Taylor-jet Hilbert bundle

Stripping the `𝔽₁`-cusp `min(m, n)` from `archKernel m n` isolates the pure trivial-zero jet kernel
`jetKernel m n = min(m, n)³ / (max(m, n)² - min(m, n)²)`. Every ordered square block `m_i < n_j`
factors into `diag(m_i³)` times the Cauchy matrix `1 / (n_j² - m_i²)` (`det_jetBlock_eq`,
`det_jetBlock_ne_zero_of_lt`), proving that the pure jets alone have infinite rank on coprime
primes (`not_finiteRank_jetKernel_on_coprime`, `not_finiteRank_frobeniusSubCusp_on_coprime`). On
`L²((0, ∞))`, the dilation-covariant causal monomial waves
`causalJetWave a k x = √(4k + 1) · 1_{(0, a]}(x) · (x / a)^{2k}` satisfy the exact Gram identity
`∫_{x > 0} causalJetWave a k x * causalJetWave b k x = min(a, b) (min(a, b) / max(a, b))^{2k}`
(`integral_causalJetWave_mul`), carrying both the `𝔽₁`-cusp (`k = 0`) and every trivial-zero jet
(`k ≥ 1`) with uniform norm `a`, and realizing `dampedFrobenius` and the positive-semidefinite pure
damped jet kernel `dampedJet` (`hasSum_dampedFrobenius_gram`, `hasSum_dampedJet_gram`,
`dampedJet_posSemidef`, `tendsto_dampedJet_of_ne`, `tendsto_dampedJet_diag`).

## 4. Counterterm-free damping walls, ultraviolet correlation locking, and smoothed RH equivalence

* **Atomic `N log N` diagonal wall** (`atomic_countertermFree_diag_lower_bound`,
  `not_atomic_countertermFree_log_diag`): any counterterm-free positive-semidefinite limit matching
  `weilDeltaKernel` off-diagonal on `ℕ₊` must satisfy `∃ n ∈ [N, 2N), K₁(n, n) ≥ N (log N - 17) / 8`,
  excluding every `O(1)` or `O(log n)` diagonal.
* **Additive decoupling no-go and correlation locking** (`tendsto_add_twistedEnergy_atTop`,
  `ultraviolet_correlation_locking`): for any positive-semidefinite family `A_r`, `A_r + twistedEnergy r`
  diverges to `+∞` on every non-zero finite support; any Hilbert-space difference presentation
  `‖u_r - v_r‖² → D` with `‖v_r‖ → +∞` locks `‖u_r‖ / ‖v_r‖ → 1` and
  `Re ⟪u_r, v_r⟫ / (‖u_r‖ ‖v_r‖) → 1`.
* **Smoothed equivalence and single-channel impossibility**
  (`riemannHypothesis_iff_exists_damped_psd_limit`, `not_psd_limit_smoothedPrime`,
  `not_psd_limit_smoothedArchPole`): on cubic-spline Frobenius graphs, `RiemannHypothesis` holds iff
  `c_B(log m - log n)` is a counterterm-free pointwise limit (diagonal included) of
  positive-semidefinite kernels `K_r`, whereas for every non-zero nonnegative test `f ∈ realTests`
  neither the smoothed prime channel nor the smoothed archimedean-plus-pole channel alone is such a
  limit.
-/

open Finset Filter Topology Set MeasureTheory Matrix
open scoped ComplexConjugate ENNReal Pointwise ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri

/-! ## Section 1. Hyperbolic three-space `ℍ³`, `SL(2, ℂ)` action, and stabilizer rigidity -/

/-- Upper half-space model `{(z, t) ∈ ℂ × ℝ : 0 < t}` of hyperbolic three-space `ℍ³`. -/
@[ext]
structure H3 where
  /-- Boundary complex coordinate. -/
  z : ℂ
  /-- Vertical radial height. -/
  t : ℝ
  /-- Positivity of the height. -/
  t_pos : 0 < t

/-- Coordinate embedding of `H3` into `Fin 3 → ℝ` as `![Re z, Im z, t]`. -/
def h3Vec (p : H3) : Fin 3 → ℝ := ![p.z.re, p.z.im, p.t]

@[simp] theorem h3Vec_zero (p : H3) : h3Vec p 0 = p.z.re := rfl
@[simp] theorem h3Vec_one (p : H3) : h3Vec p 1 = p.z.im := rfl
@[simp] theorem h3Vec_two (p : H3) : h3Vec p 2 = p.t := rfl

theorem h3Vec_injective : Function.Injective h3Vec := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [h3Vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  ext
  · exact Complex.ext h0 h1
  · exact h2

theorem range_h3Vec : Set.range h3Vec = {w : Fin 3 → ℝ | 0 < w 2} := by
  ext w
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, rfl⟩
    exact p.t_pos
  · intro hw
    refine ⟨⟨⟨w 0, w 1⟩, w 2, hw⟩, ?_⟩
    ext i
    fin_cases i <;> rfl

instance : TopologicalSpace H3 := TopologicalSpace.induced h3Vec inferInstance
instance : MeasurableSpace H3 := MeasurableSpace.comap h3Vec inferInstance

theorem isOpen_range_h3Vec : IsOpen (Set.range h3Vec) := by
  rw [range_h3Vec]
  exact isOpen_lt continuous_const (continuous_apply 2)

theorem continuous_h3Vec : Continuous h3Vec := continuous_induced_dom

theorem measurableEmbedding_h3Vec : MeasurableEmbedding h3Vec where
  injective := h3Vec_injective
  measurable _ hs := ⟨_, hs, rfl⟩
  measurableSet_image' := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Set.image_preimage_eq_inter_range]
    exact hu.inter isOpen_range_h3Vec.measurableSet

instance : BorelSpace H3 := measurableEmbedding_h3Vec.borelSpace ⟨rfl⟩

/-- Point `(0, t)` on the vertical dilation geodesic of `ℍ³`. -/
def degPoint (t : ℝ) (ht : 0 < t) : H3 := ⟨0, t, ht⟩

/-- Integer-degree point `(0, n)` on the vertical geodesic of `ℍ³`. -/
def natPoint (n : ℕ) (hn : 0 < n) : H3 := ⟨0, n, by exact_mod_cast hn⟩

/-- Chordal invariant `cosh d(p, q) = 1 + (‖z_p - z_q‖² + (t_p - t_q)²) / (2 t_p t_q)` on `ℍ³`. -/
def h3Cosh (p q : H3) : ℝ :=
  1 + (‖p.z - q.z‖ ^ 2 + (p.t - q.t) ^ 2) / (2 * p.t * q.t)

/-- Hyperbolic geodesic distance `d(p, q) = arcosh(h3Cosh p q)` on `ℍ³`. -/
def h3Dist (p q : H3) : ℝ := Real.arcosh (h3Cosh p q)

theorem one_le_h3Cosh (p q : H3) : 1 ≤ h3Cosh p q := by
  unfold h3Cosh
  have hp := p.t_pos
  have hq := q.t_pos
  have hdiv : 0 ≤ (‖p.z - q.z‖ ^ 2 + (p.t - q.t) ^ 2) / (2 * p.t * q.t) := by positivity
  linarith

theorem h3Cosh_pos (p q : H3) : 0 < h3Cosh p q :=
  lt_of_lt_of_le zero_lt_one (one_le_h3Cosh p q)

theorem h3Cosh_comm (p q : H3) : h3Cosh p q = h3Cosh q p := by
  unfold h3Cosh
  rw [norm_sub_rev]
  ring

@[simp]
theorem h3Cosh_self (p : H3) : h3Cosh p p = 1 := by
  simp [h3Cosh]

theorem h3Cosh_eq_one_iff (p q : H3) : h3Cosh p q = 1 ↔ p = q := by
  constructor
  · intro h
    unfold h3Cosh at h
    have hp := p.t_pos
    have hq := q.t_pos
    have hden : 0 < 2 * p.t * q.t := by positivity
    have hnum : ‖p.z - q.z‖ ^ 2 + (p.t - q.t) ^ 2 = 0 := by
      have hdiv : (‖p.z - q.z‖ ^ 2 + (p.t - q.t) ^ 2) / (2 * p.t * q.t) = 0 := by linarith
      exact (div_eq_zero_iff.mp hdiv).resolve_right hden.ne'
    have hz0 : ‖p.z - q.z‖ = 0 := by
      have h1 : ‖p.z - q.z‖ ^ 2 = 0 := by nlinarith [sq_nonneg (‖p.z - q.z‖), sq_nonneg (p.t - q.t)]
      exact sq_eq_zero_iff.mp h1
    have ht0 : p.t - q.t = 0 := by
      have h2 : (p.t - q.t) ^ 2 = 0 := by nlinarith [sq_nonneg (‖p.z - q.z‖), sq_nonneg (p.t - q.t)]
      exact sq_eq_zero_iff.mp h2
    ext
    · exact sub_eq_zero.mp (norm_eq_zero.mp hz0)
    · linarith
  · rintro rfl
    exact h3Cosh_self p

theorem h3Dist_nonneg (p q : H3) : 0 ≤ h3Dist p q :=
  Real.arcosh_nonneg (one_le_h3Cosh p q)

theorem h3Dist_comm (p q : H3) : h3Dist p q = h3Dist q p := by
  rw [h3Dist, h3Dist, h3Cosh_comm]

@[simp]
theorem h3Dist_self (p : H3) : h3Dist p p = 0 := by
  rw [h3Dist, h3Cosh_self, Real.arcosh_zero]

theorem h3Dist_eq_zero_iff (p q : H3) : h3Dist p q = 0 ↔ p = q := by
  rw [h3Dist, Real.arcosh_eq_zero_iff (one_le_h3Cosh p q), h3Cosh_eq_one_iff]

theorem cosh_h3Dist (p q : H3) : Real.cosh (h3Dist p q) = h3Cosh p q :=
  Real.cosh_arcosh (one_le_h3Cosh p q)

theorem h3Dist_degPoint {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    h3Dist (degPoint t ht) (degPoint u hu) = |Real.log u - Real.log t| := by
  have hc : h3Cosh (degPoint t ht) (degPoint u hu) = Real.cosh |Real.log u - Real.log t| := by
    rw [Real.cosh_abs, cosh_log_sub_log ht hu]
    simp [h3Cosh, degPoint]
    ring
  rw [h3Dist, hc, Real.arcosh_cosh (abs_nonneg _)]

/-- Special linear group `SL(2, ℂ)`. -/
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- Positive-definite determinant-`1` Hermitian matrix attached to `p ∈ H3`. -/
def toHermMat (p : H3) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((‖p.z‖ ^ 2 + p.t ^ 2) / p.t : ℝ) : ℂ), p.z / (p.t : ℂ);
     conj p.z / (p.t : ℂ), ((1 / p.t : ℝ) : ℂ)]

theorem toHermMat_injective : Function.Injective toHermMat := by
  intro p q h
  have h11 : (toHermMat p 1 1).re = (toHermMat q 1 1).re := congrArg Complex.re (congrFun₂ h 1 1)
  simp only [toHermMat, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_re, one_div] at h11
  have ht : p.t = q.t := inv_injective h11
  have h01 : toHermMat p 0 1 = toHermMat q 0 1 := congrFun₂ h 0 1
  simp only [toHermMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, ht] at h01
  have hqt : (q.t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr q.t_pos.ne'
  have hz : p.z = q.z := div_left_inj' hqt |>.mp h01
  exact H3.ext hz ht

theorem re_trace_toHermMat_mul_adjugate (p q : H3) :
    ((toHermMat p * (toHermMat q).adjugate).trace).re = 2 * h3Cosh p q := by
  have hp : p.t ≠ 0 := p.t_pos.ne'
  have hq : q.t ≠ 0 := q.t_pos.ne'
  unfold h3Cosh
  simp only [toHermMat, Matrix.adjugate_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hnorm : ‖p.z - q.z‖ ^ 2 = ‖p.z‖ ^ 2 + ‖q.z‖ ^ 2 - 2 * (p.z.re * q.z.re + p.z.im * q.z.im) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  rw [hnorm]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.mul_re, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im]
  field_simp
  ring

/-- Denominator `‖c z + d‖² + ‖c‖² t²` of the `SL(2, ℂ)` action on `ℍ³`. -/
def h3Denom (g : SL2C) (p : H3) : ℝ :=
  ‖g.1 1 0 * p.z + g.1 1 1‖ ^ 2 + ‖g.1 1 0‖ ^ 2 * p.t ^ 2

theorem h3Denom_pos (g : SL2C) (p : H3) : 0 < h3Denom g p := by
  by_contra hle
  push Not at hle
  unfold h3Denom at hle
  have hp := p.t_pos
  have hc2 : ‖g.1 1 0‖ ^ 2 * p.t ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖g.1 1 0 * p.z + g.1 1 1‖, sq_nonneg ‖g.1 1 0‖, sq_nonneg p.t]
  have hc0 : g.1 1 0 = 0 := by
    rcases mul_eq_zero.mp hc2 with h | h
    · exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)
    · exact absurd (sq_eq_zero_iff.mp h) hp.ne'
  have hd0 : g.1 1 1 = 0 := by
    rw [hc0, zero_mul, zero_add, norm_zero, zero_pow two_ne_zero, zero_mul, add_zero] at hle
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _)))
  have hdet := g.prop
  rw [Matrix.det_fin_two, hc0, hd0] at hdet
  norm_num at hdet

/-- Isometric Poincaré-extension action of `SL(2, ℂ)` on `ℍ³`. -/
def h3Act (g : SL2C) (p : H3) : H3 where
  z := ((g.1 0 0 * p.z + g.1 0 1) * conj (g.1 1 0 * p.z + g.1 1 1) +
        g.1 0 0 * conj (g.1 1 0) * (p.t : ℂ) ^ 2) / (h3Denom g p : ℂ)
  t := p.t / h3Denom g p
  t_pos := div_pos p.t_pos (h3Denom_pos g p)

@[simp]
theorem h3Act_z (g : SL2C) (p : H3) :
    (h3Act g p).z = ((g.1 0 0 * p.z + g.1 0 1) * conj (g.1 1 0 * p.z + g.1 1 1) +
      g.1 0 0 * conj (g.1 1 0) * (p.t : ℂ) ^ 2) / (h3Denom g p : ℂ) := rfl

@[simp]
theorem h3Act_t (g : SL2C) (p : H3) :
    (h3Act g p).t = p.t / h3Denom g p := rfl

theorem toHermMat_h3Act (g : SL2C) (p : H3) :
    toHermMat (h3Act g p) = g.1 * toHermMat p * g.1.conjTranspose := by
  have hp : p.t ≠ 0 := p.t_pos.ne'
  have hpc : (p.t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  have hden : h3Denom g p ≠ 0 := (h3Denom_pos g p).ne'
  have hdenc : (h3Denom g p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden
  have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    have h := g.prop
    rwa [Matrix.det_fin_two] at h
  set A := g.1 0 0 * p.z + g.1 0 1
  set C := g.1 1 0 * p.z + g.1 1 1
  have hAC : A * g.1 1 0 - C * g.1 0 0 = -1 := by
    simp only [A, C]
    linear_combination -hdet
  have hlag : ‖A * conj C + g.1 0 0 * conj (g.1 1 0) * (p.t : ℂ) ^ 2‖ ^ 2 + p.t ^ 2 =
      (‖A‖ ^ 2 + ‖g.1 0 0‖ ^ 2 * p.t ^ 2) * (‖C‖ ^ 2 + ‖g.1 1 0‖ ^ 2 * p.t ^ 2) := by
    have hlag_c : Complex.normSq (A * conj C + g.1 0 0 * conj (g.1 1 0) * (p.t : ℂ) ^ 2) +
        Complex.normSq ((A * g.1 1 0 - C * g.1 0 0) * (p.t : ℂ)) =
        (Complex.normSq A + Complex.normSq (g.1 0 0) * p.t ^ 2) *
          (Complex.normSq C + Complex.normSq (g.1 1 0) * p.t ^ 2) := by
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        sq (p.t : ℂ), Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hAC, neg_one_mul, Complex.normSq_neg, Complex.normSq_ofReal, ← sq] at hlag_c
    simpa only [Complex.normSq_eq_norm_sq] using hlag_c
  have hmul_conj : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * conj z := fun z => by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  ext i j
  fin_cases i <;> fin_cases j
  · -- Entry (0, 0)
    simp only [Fin.zero_eta, toHermMat, h3Act_z, h3Act_t, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hnum_simp :
        (‖(A * conj C + g.1 0 0 * conj (g.1 1 0) * (p.t : ℂ) ^ 2) / (h3Denom g p : ℂ)‖ ^ 2 +
          (p.t / h3Denom g p) ^ 2) / (p.t / h3Denom g p) =
        (‖A‖ ^ 2 + ‖g.1 0 0‖ ^ 2 * p.t ^ 2) / p.t := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (h3Denom_pos g p).le, div_pow, div_pow,
        ← add_div, hlag]
      have hden_eq : ‖C‖ ^ 2 + ‖g.1 1 0‖ ^ 2 * p.t ^ 2 = h3Denom g p := rfl
      rw [hden_eq]
      field_simp
    rw [show g.1 0 0 * p.z + g.1 0 1 = A from rfl, show g.1 1 0 * p.z + g.1 1 1 = C from rfl,
      hnum_simp]
    push_cast
    simp only [hmul_conj, A, map_add, map_mul]
    field_simp
    ring
  · -- Entry (0, 1)
    simp only [Fin.zero_eta, Fin.mk_one, toHermMat, h3Act_z, h3Act_t, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    simp only [hmul_conj, map_add, map_mul]
    field_simp
    ring
  · -- Entry (1, 0)
    simp only [Fin.zero_eta, Fin.mk_one, toHermMat, h3Act_z, h3Act_t, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    simp only [hmul_conj, map_div₀, map_add, map_mul, map_pow, Complex.conj_conj,
      Complex.conj_ofReal]
    field_simp
    ring
  · -- Entry (1, 1)
    simp only [Fin.mk_one, toHermMat, h3Act_t, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    unfold h3Denom
    push_cast
    simp only [hmul_conj, map_add, map_mul]
    field_simp
    ring

@[simp]
theorem h3Act_one (p : H3) : h3Act 1 p = p := by
  apply toHermMat_injective
  rw [toHermMat_h3Act]
  simp

theorem h3Act_mul (g h : SL2C) (p : H3) : h3Act (g * h) p = h3Act g (h3Act h p) := by
  apply toHermMat_injective
  rw [toHermMat_h3Act, toHermMat_h3Act, toHermMat_h3Act]
  change (g.1 * h.1) * toHermMat p * (g.1 * h.1).conjTranspose = _
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

instance : MulAction SL2C H3 where
  smul := h3Act
  one_smul := h3Act_one
  mul_smul := h3Act_mul

theorem smul_h3_def (g : SL2C) (p : H3) : g • p = h3Act g p := rfl

/-- `SL(2, ℂ)` preserves `h3Cosh`. -/
theorem h3Cosh_h3Act (g : SL2C) (p q : H3) :
    h3Cosh (h3Act g p) (h3Act g q) = h3Cosh p q := by
  have h1 := re_trace_toHermMat_mul_adjugate (h3Act g p) (h3Act g q)
  have h2 := re_trace_toHermMat_mul_adjugate p q
  have hadj_prod : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
      (A * B).adjugate = B.adjugate * A.adjugate := by
    intro A B; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hadj_g : g.1.adjugate * g.1 = 1 := by
    rw [Matrix.adjugate_mul, g.prop, one_smul]
  have hadj_gh : g.1.conjTranspose * g.1.conjTranspose.adjugate = 1 := by
    rw [Matrix.mul_adjugate, Matrix.det_conjTranspose, g.prop, star_one, one_smul]
  have htr : (toHermMat (h3Act g p) * (toHermMat (h3Act g q)).adjugate).trace =
      (toHermMat p * (toHermMat q).adjugate).trace := by
    rw [toHermMat_h3Act g p, toHermMat_h3Act g q,
      hadj_prod (g.1 * toHermMat q) g.1.conjTranspose, hadj_prod g.1 (toHermMat q)]
    calc (g.1 * toHermMat p * g.1.conjTranspose *
            (g.1.conjTranspose.adjugate * ((toHermMat q).adjugate * g.1.adjugate))).trace
        = (g.1 * (toHermMat p * (g.1.conjTranspose * g.1.conjTranspose.adjugate) *
            (toHermMat q).adjugate * g.1.adjugate)).trace := by
          simp only [Matrix.mul_assoc]
      _ = (g.1 * (toHermMat p * (toHermMat q).adjugate * g.1.adjugate)).trace := by
          rw [hadj_gh, Matrix.mul_one]
      _ = ((toHermMat p * (toHermMat q).adjugate * g.1.adjugate) * g.1).trace :=
          Matrix.trace_mul_comm _ _
      _ = (toHermMat p * (toHermMat q).adjugate * (g.1.adjugate * g.1)).trace := by
          rw [Matrix.mul_assoc]
      _ = (toHermMat p * (toHermMat q).adjugate).trace := by
          rw [hadj_g, Matrix.mul_one]
  rw [htr] at h1
  linarith

/-- `SL(2, ℂ)` acts by isometries on `(ℍ³, h3Dist)`. -/
theorem h3Dist_h3Act (g : SL2C) (p q : H3) :
    h3Dist (h3Act g p) (h3Act g q) = h3Dist p q := by
  rw [h3Dist, h3Dist, h3Cosh_h3Act]

/-- Upper-triangular Borel element mapping `(0, 1)` to `q = (z, t) ∈ ℍ³`. -/
def borelToPoint (q : H3) : SL2C :=
  ⟨!![(Real.sqrt q.t : ℂ), q.z / (Real.sqrt q.t : ℂ);
      0, (1 / Real.sqrt q.t : ℂ)], by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hsq : (Real.sqrt q.t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr q.t_pos).ne'
    field_simp
    ring⟩

theorem h3Act_borelToPoint_origin (q : H3) :
    h3Act (borelToPoint q) (degPoint 1 zero_lt_one) = q := by
  have hsq_pos : 0 < Real.sqrt q.t := Real.sqrt_pos.mpr q.t_pos
  have hsq : Real.sqrt q.t ^ 2 = q.t := Real.sq_sqrt q.t_pos.le
  have hden : h3Denom (borelToPoint q) (degPoint 1 zero_lt_one) = 1 / q.t := by
    unfold h3Denom borelToPoint degPoint
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, zero_mul, zero_add, norm_zero, zero_pow two_ne_zero, add_zero,
      one_div, norm_inv, Complex.norm_real, Real.norm_of_nonneg hsq_pos.le, inv_pow, hsq]
  ext
  · rw [h3Act_z, hden]
    simp only [borelToPoint, degPoint, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_add,
      map_zero, add_zero, one_div, map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv]
    have hsqc : (Real.sqrt q.t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq_pos.ne'
    have htc : (q.t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr q.t_pos.ne'
    have hsqc2 : (Real.sqrt q.t : ℂ) ^ 2 = (q.t : ℂ) := by exact_mod_cast hsq
    field_simp
    rw [sq, ← hsqc2]; ring
  · rw [h3Act_t, hden]
    simp only [degPoint]
    field_simp

/-- **Hyperbolic triangle inequality on `ℍ³`.** -/
theorem h3Dist_triangle (p q r : H3) : h3Dist p r ≤ h3Dist p q + h3Dist q r := by
  -- Reduce to `q = (0, 1)` by transitive `SL(2, ℂ)` action
  set g := (borelToPoint q)⁻¹
  have hq : h3Act g q = degPoint 1 zero_lt_one := by
    calc h3Act g q = h3Act (borelToPoint q)⁻¹ (h3Act (borelToPoint q) (degPoint 1 zero_lt_one)) := by
          rw [h3Act_borelToPoint_origin]
      _ = h3Act ((borelToPoint q)⁻¹ * borelToPoint q) (degPoint 1 zero_lt_one) :=
          (h3Act_mul _ _ _).symm
      _ = degPoint 1 zero_lt_one := by rw [inv_mul_cancel, h3Act_one]
  rw [← h3Dist_h3Act g p r, ← h3Dist_h3Act g p q, ← h3Dist_h3Act g q r, hq]
  set u := h3Act g p
  set v := h3Act g r
  set o := degPoint 1 zero_lt_one
  have hu : u.t ≠ 0 := u.t_pos.ne'
  have hv : v.t ≠ 0 := v.t_pos.ne'
  -- Hyperboloid coordinates centered at `o = (0, 1)`
  set Cu := h3Cosh u o
  set Cv := h3Cosh v o
  set xu1 := u.z.re / u.t
  set xu2 := u.z.im / u.t
  set xu3 := (‖u.z‖ ^ 2 + u.t ^ 2 - 1) / (2 * u.t)
  set xv1 := v.z.re / v.t
  set xv2 := v.z.im / v.t
  set xv3 := (‖v.z‖ ^ 2 + v.t ^ 2 - 1) / (2 * v.t)
  have hCu_sq : xu1 ^ 2 + xu2 ^ 2 + xu3 ^ 2 = Cu ^ 2 - 1 := by
    simp only [Cu, h3Cosh, o, degPoint, xu1, xu2, xu3, sub_zero, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    field_simp
    ring
  have hCv_sq : xv1 ^ 2 + xv2 ^ 2 + xv3 ^ 2 = Cv ^ 2 - 1 := by
    simp only [Cv, h3Cosh, o, degPoint, xv1, xv2, xv3, sub_zero, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    field_simp
    ring
  have hdot : h3Cosh u v = Cu * Cv - (xu1 * xv1 + xu2 * xv2 + xu3 * xv3) := by
    have hnorm : ‖u.z - v.z‖ ^ 2 =
        ‖u.z‖ ^ 2 + ‖v.z‖ ^ 2 - 2 * (u.z.re * v.z.re + u.z.im * v.z.im) := by
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    simp only [Cu, Cv, h3Cosh, o, degPoint, xu1, xu2, xu3, xv1, xv2, xv3, sub_zero]
    rw [hnorm]
    field_simp
    ring
  -- 3-term Cauchy–Schwarz
  have hcs_sq : (-(xu1 * xv1 + xu2 * xv2 + xu3 * xv3)) ^ 2 ≤ (Cu ^ 2 - 1) * (Cv ^ 2 - 1) := by
    rw [← hCu_sq, ← hCv_sq]
    nlinarith [sq_nonneg (xu1 * xv2 - xu2 * xv1), sq_nonneg (xu1 * xv3 - xu3 * xv1),
      sq_nonneg (xu2 * xv3 - xu3 * xv2)]
  have hsinh_u : Real.sinh (h3Dist u o) = Real.sqrt (Cu ^ 2 - 1) :=
    Real.sinh_arcosh (one_le_h3Cosh u o)
  have hsinh_v : Real.sinh (h3Dist o v) = Real.sqrt (Cv ^ 2 - 1) := by
    rw [h3Dist_comm o v]
    exact Real.sinh_arcosh (one_le_h3Cosh v o)
  have hprod_nonneg : 0 ≤ Real.sinh (h3Dist u o) * Real.sinh (h3Dist o v) := by
    rw [hsinh_u, hsinh_v]
    positivity
  have hcs : -(xu1 * xv1 + xu2 * xv2 + xu3 * xv3) ≤
      Real.sinh (h3Dist u o) * Real.sinh (h3Dist o v) := by
    rw [hsinh_u, hsinh_v, ← Real.sqrt_mul (by nlinarith [one_le_h3Cosh u o])]
    exact Real.le_sqrt_of_sq_le hcs_sq
  have hcosh_le : h3Cosh u v ≤ Real.cosh (h3Dist u o + h3Dist o v) := by
    rw [Real.cosh_add, cosh_h3Dist u o, show h3Dist o v = h3Dist v o from h3Dist_comm o v,
      cosh_h3Dist v o, ← show h3Dist o v = h3Dist v o from h3Dist_comm o v, hdot]
    linarith
  calc h3Dist u v = Real.arcosh (h3Cosh u v) := rfl
    _ ≤ Real.arcosh (Real.cosh (h3Dist u o + h3Dist o v)) :=
        (Real.arcosh_le_arcosh (h3Cosh_pos u v) (Real.cosh_pos _)).mpr hcosh_le
    _ = h3Dist u o + h3Dist o v :=
        Real.arcosh_cosh (add_nonneg (h3Dist_nonneg u o) (h3Dist_nonneg o v))

/-! ### Invariant hyperbolic measure `h3Measure = t⁻³ dx dy dt` -/

/-- Hyperbolic volume measure `t⁻³ dx dy dt` on `ℍ³`. -/
def h3Measure : Measure H3 :=
  (volume.comap h3Vec).withDensity fun p => ENNReal.ofReal (p.t⁻¹ ^ 3)

theorem h3Measure_eq_lintegral {s : Set H3} (hs : MeasurableSet s) :
    h3Measure s = ∫⁻ w in h3Vec '' s, ENNReal.ofReal ((w 2)⁻¹ ^ 3) ∂volume := by
  have hmp : MeasurePreserving h3Vec (volume.comap h3Vec)
      (volume.restrict (Set.range h3Vec)) :=
    ⟨measurableEmbedding_h3Vec.measurable, by rw [measurableEmbedding_h3Vec.map_comap]⟩
  rw [h3Measure, withDensity_apply _ hs,
    ← Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _),
    ← Measure.restrict_restrict' measurableEmbedding_h3Vec.measurableSet_range,
    ← hmp.setLIntegral_comp_emb measurableEmbedding_h3Vec]
  rfl

theorem continuous_h3Act (g : SL2C) : Continuous (h3Act g) := by
  rw [continuous_induced_rng]
  have hc0 : Continuous (fun p : H3 => h3Vec p 0) :=
    (continuous_apply 0).comp continuous_h3Vec
  have hc1 : Continuous (fun p : H3 => h3Vec p 1) :=
    (continuous_apply 1).comp continuous_h3Vec
  have hct : Continuous (fun p : H3 => p.t) :=
    (continuous_apply 2).comp continuous_h3Vec
  have hcz : Continuous (fun p : H3 => p.z) := by
    have heq : (fun p : H3 => p.z) =
        fun p => (h3Vec p 0 : ℂ) + (h3Vec p 1 : ℂ) * Complex.I :=
      funext fun p => (Complex.re_add_im p.z).symm
    rw [heq]
    exact (Complex.continuous_ofReal.comp hc0).add
      ((Complex.continuous_ofReal.comp hc1).mul continuous_const)
  have hcden : Continuous (fun p : H3 => h3Denom g p) := by
    unfold h3Denom
    exact (((continuous_const.mul hcz).add continuous_const).norm.pow 2).add
      (continuous_const.mul (hct.pow 2))
  have hcz' : Continuous (fun p : H3 => (h3Act g p).z) := by
    simp only [h3Act_z]
    refine Continuous.div ?_ (Complex.continuous_ofReal.comp hcden)
      (fun p => Complex.ofReal_ne_zero.mpr (h3Denom_pos g p).ne')
    refine (((continuous_const.mul hcz).add continuous_const).mul
      (Complex.continuous_conj.comp ((continuous_const.mul hcz).add continuous_const))).add ?_
    exact continuous_const.mul ((Complex.continuous_ofReal.comp hct).pow 2)
  have hct' : Continuous (fun p : H3 => (h3Act g p).t) :=
    hct.div hcden fun p => (h3Denom_pos g p).ne'
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact Complex.continuous_re.comp hcz'
  · exact Complex.continuous_im.comp hcz'
  · exact hct'

/-- Homeomorphism of `ℍ³` induced by `g ∈ SL(2, ℂ)`. -/
def h3ActHomeomorph (g : SL2C) : H3 ≃ₜ H3 where
  toFun := h3Act g
  invFun := h3Act g⁻¹
  left_inv p := by rw [← h3Act_mul, inv_mul_cancel, h3Act_one]
  right_inv p := by rw [← h3Act_mul, mul_inv_cancel, h3Act_one]
  continuous_toFun := continuous_h3Act g
  continuous_invFun := continuous_h3Act g⁻¹

theorem measurableEmbedding_h3Act (g : SL2C) : MeasurableEmbedding (h3Act g) :=
  (h3ActHomeomorph g).isClosedEmbedding.measurableEmbedding

theorem continuous_h3Dist_right (q : H3) : Continuous (h3Dist q) := by
  have hc0 : Continuous (fun p : H3 => h3Vec p 0) :=
    (continuous_apply 0).comp continuous_h3Vec
  have hc1 : Continuous (fun p : H3 => h3Vec p 1) :=
    (continuous_apply 1).comp continuous_h3Vec
  have hct : Continuous (fun p : H3 => p.t) :=
    (continuous_apply 2).comp continuous_h3Vec
  have hcz : Continuous (fun p : H3 => p.z) := by
    have heq : (fun p : H3 => p.z) =
        fun p => (h3Vec p 0 : ℂ) + (h3Vec p 1 : ℂ) * Complex.I :=
      funext fun p => (Complex.re_add_im p.z).symm
    rw [heq]
    exact (Complex.continuous_ofReal.comp hc0).add
      ((Complex.continuous_ofReal.comp hc1).mul continuous_const)
  have hcont_cosh : Continuous (fun p : H3 => h3Cosh q p) := by
    unfold h3Cosh
    refine continuous_const.add (Continuous.div ?_ ?_ fun p => ?_)
    · exact ((continuous_const.sub hcz).norm.pow 2).add ((continuous_const.sub hct).pow 2)
    · exact continuous_const.mul hct
    · have := q.t_pos; have := p.t_pos; positivity
  exact Real.continuousOn_arcosh.comp_continuous hcont_cosh fun p => one_le_h3Cosh q p

/-- Parabolic translation matrix `!![1, ω; 0, 1]` in `SL(2, ℂ)`. -/
def parabolicSL2 (ω : ℂ) : SL2C :=
  ⟨!![1, ω; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- Diagonal loxodromic/elliptic matrix `!![a, 0; 0, a⁻¹]` (`a ≠ 0`) in `SL(2, ℂ)`. -/
def diagSL2 (a : ℂ) (ha : a ≠ 0) : SL2C :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, mul_inv_cancel₀ ha]⟩

/-- Inversion matrix `S = !![0, -1; 1, 0]` in `SL(2, ℂ)`. -/
def invSL2 : SL2C :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem h3Vec_parabolicSL2 (ω : ℂ) (p : H3) :
    h3Vec (h3Act (parabolicSL2 ω) p) = h3Vec p + ![ω.re, ω.im, 0] := by
  have hden : h3Denom (parabolicSL2 ω) p = 1 := by
    simp [h3Denom, parabolicSL2]
  ext i
  fin_cases i
  · change (h3Act (parabolicSL2 ω) p).z.re = p.z.re + ω.re
    rw [h3Act_z, hden]; simp [parabolicSL2]
  · change (h3Act (parabolicSL2 ω) p).z.im = p.z.im + ω.im
    rw [h3Act_z, hden]; simp [parabolicSL2]
  · change (h3Act (parabolicSL2 ω) p).t = p.t + 0
    rw [h3Act_t, hden]; simp

/-- Linear map on `Fin 3 → ℝ` representing `diagSL2 a ha`. -/
def diagVecMat (a : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(a ^ 2).re, -(a ^ 2).im, 0;
     (a ^ 2).im,  (a ^ 2).re, 0;
     0,           0,          ‖a‖ ^ 2]

theorem det_diagVecMat (a : ℂ) : (diagVecMat a).det = ‖a‖ ^ 6 := by
  rw [diagVecMat, Matrix.det_fin_three]
  have hsq : (a ^ 2).re ^ 2 + (a ^ 2).im ^ 2 = ‖a‖ ^ 4 := by
    have h1 : (a ^ 2).re ^ 2 + (a ^ 2).im ^ 2 = ‖a ^ 2‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [h1, norm_pow]; ring
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination ‖a‖ ^ 2 * hsq

theorem h3Vec_diagSL2 {a : ℂ} (ha : a ≠ 0) (p : H3) :
    h3Vec (h3Act (diagSL2 a ha) p) = (Matrix.toLin' (diagVecMat a)) (h3Vec p) := by
  have hden : h3Denom (diagSL2 a ha) p = ‖a‖⁻¹ ^ 2 := by
    simp [h3Denom, diagSL2]
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hz : (a * p.z * conj a⁻¹) / ((‖a‖⁻¹ ^ 2 : ℝ) : ℂ) = a ^ 2 * p.z := by
    have hmul : ((‖a‖ ^ 2 : ℝ) : ℂ) = a * conj a := by
      rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
    have hca : conj a ≠ 0 := map_ne_zero _ |>.mpr ha
    rw [inv_pow, Complex.ofReal_inv, div_inv_eq_mul, hmul, map_inv₀]
    field_simp
  ext i
  fin_cases i
  · change (h3Act (diagSL2 a ha) p).z.re = (Matrix.toLin' (diagVecMat a)) (h3Vec p) 0
    rw [h3Act_z, hden]
    simp only [diagSL2, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, add_zero, zero_mul, map_zero, mul_zero]
    rw [hz]
    simp [diagVecMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  · change (h3Act (diagSL2 a ha) p).z.im = (Matrix.toLin' (diagVecMat a)) (h3Vec p) 1
    rw [h3Act_z, hden]
    simp only [diagSL2, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, add_zero, zero_mul, map_zero, mul_zero]
    rw [hz]
    simp [diagVecMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · change (h3Act (diagSL2 a ha) p).t = (Matrix.toLin' (diagVecMat a)) (h3Vec p) 2
    rw [h3Act_t, hden]
    simp only [diagVecMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, h3Vec_zero, h3Vec_one, h3Vec_two, mul_zero, zero_mul,
      zero_add]
    field_simp

/-- Coordinate map on `Fin 3 → ℝ` representing `invSL2 = !![0, -1; 1, 0]`. -/
def invVecMap (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let r2 := w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2
  ![-w 0 / r2, w 1 / r2, w 2 / r2]

theorem h3Vec_invSL2 (p : H3) : h3Vec (h3Act invSL2 p) = invVecMap (h3Vec p) := by
  have hden : h3Denom invSL2 p = p.z.re ^ 2 + p.z.im ^ 2 + p.t ^ 2 := by
    unfold h3Denom invSL2
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, one_mul, add_zero, norm_one, one_pow,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  ext i
  fin_cases i
  · change (h3Act invSL2 p).z.re = invVecMap (h3Vec p) 0
    rw [h3Act_z, hden]; simp [invSL2, invVecMap, Complex.div_ofReal_re]
  · change (h3Act invSL2 p).z.im = invVecMap (h3Vec p) 1
    rw [h3Act_z, hden]; simp [invSL2, invVecMap, Complex.div_ofReal_im]
  · change (h3Act invSL2 p).t = invVecMap (h3Vec p) 2
    rw [h3Act_t, hden]; simp [invVecMap]

theorem invVecMap_involutive {w : Fin 3 → ℝ} (hw : 0 < w 2) : invVecMap (invVecMap w) = w := by
  set r2 := w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2
  have hr2 : 0 < r2 := by positivity
  have hsq : (-w 0 / r2) ^ 2 + (w 1 / r2) ^ 2 + (w 2 / r2) ^ 2 = 1 / r2 := by
    have hnum : (-w 0) ^ 2 + w 1 ^ 2 + w 2 ^ 2 = r2 := by simp [r2]
    field_simp
    linear_combination hnum
  ext i
  fin_cases i
  · change -(-w 0 / r2) / ((-w 0 / r2) ^ 2 + (w 1 / r2) ^ 2 + (w 2 / r2) ^ 2) = w 0
    rw [hsq]; field_simp
  · change (w 1 / r2) / ((-w 0 / r2) ^ 2 + (w 1 / r2) ^ 2 + (w 2 / r2) ^ 2) = w 1
    rw [hsq]; field_simp
  · change (w 2 / r2) / ((-w 0 / r2) ^ 2 + (w 1 / r2) ^ 2 + (w 2 / r2) ^ 2) = w 2
    rw [hsq]; field_simp

/-- Explicit `3 × 3` Jacobian matrix of `invVecMap` at `w`. -/
def invVecJac (w : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let r2 := w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2
  let r4 := r2 ^ 2
  !![(-r2 + 2 * w 0 ^ 2) / r4, (2 * w 0 * w 1) / r4, (2 * w 0 * w 2) / r4;
     (-2 * w 1 * w 0) / r4,    (r2 - 2 * w 1 ^ 2) / r4, (-2 * w 1 * w 2) / r4;
     (-2 * w 2 * w 0) / r4,    (-2 * w 2 * w 1) / r4,   (r2 - 2 * w 2 ^ 2) / r4]

theorem det_invVecJac {w : Fin 3 → ℝ} (hw : 0 < w 2) :
    (invVecJac w).det = (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2)⁻¹ ^ 3 := by
  set r2 := w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2
  have hr2 : 0 < r2 := by positivity
  rw [invVecJac, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hr2_def : r2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := rfl
  field_simp
  rw [hr2_def]
  ring

theorem hasFDerivAt_invVecMap {w : Fin 3 → ℝ} (hw : 0 < w 2) :
    HasFDerivAt invVecMap (Matrix.toLin' (invVecJac w)).toContinuousLinearMap w := by
  let L := (Matrix.toLin' (invVecJac w)).toContinuousLinearMap
  set p0 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  set p1 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  set p2 : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 2
  have hd0 : HasFDerivAt (fun v : Fin 3 → ℝ => v 0) p0 w := p0.hasFDerivAt
  have hd1 : HasFDerivAt (fun v : Fin 3 → ℝ => v 1) p1 w := p1.hasFDerivAt
  have hd2 : HasFDerivAt (fun v : Fin 3 → ℝ => v 2) p2 w := p2.hasFDerivAt
  have hdr2 : HasFDerivAt (fun v : Fin 3 → ℝ => v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)
      ((2 * w 0) • p0 + (2 * w 1) • p1 + (2 * w 2) • p2) w := by
    have h0 := (hd0.pow 2).congr_fderiv (by ext v; simp [p0]; ring)
    have h1 := (hd1.pow 2).congr_fderiv (by ext v; simp [p1]; ring)
    have h2 := (hd2.pow 2).congr_fderiv (by ext v; simp [p2]; ring)
    exact (h0.add h1).add h2
  have hr2_ne : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 ≠ 0 := (by positivity : 0 < w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2).ne'
  refine (hasFDerivAt_pi.mpr fun i => (?_ : HasFDerivAt (fun v => invVecMap v i)
    ((ContinuousLinearMap.proj i).comp L) w)).congr_fderiv (by ext v i; rfl)
  fin_cases i
  · change HasFDerivAt (fun v : Fin 3 → ℝ => -v 0 / (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)) _ w
    refine (hd0.neg.div hdr2 hr2_ne).congr_fderiv ?_
    ext v
    simp [L, invVecJac, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, p0, p1, p2]
    ring
  · change HasFDerivAt (fun v : Fin 3 → ℝ => v 1 / (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)) _ w
    refine (hd1.div hdr2 hr2_ne).congr_fderiv ?_
    ext v
    simp [L, invVecJac, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, p0, p1, p2]
    ring
  · change HasFDerivAt (fun v : Fin 3 → ℝ => v 2 / (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)) _ w
    refine (hd2.div hdr2 hr2_ne).congr_fderiv ?_
    ext v
    simp [L, invVecJac, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, p0, p1, p2]
    ring

private theorem h3Measure_parabolicSL2 (ω : ℂ) {s : Set H3} (hs : MeasurableSet s) :
    h3Measure ((parabolicSL2 ω) • s) = h3Measure s := by
  have hgs : MeasurableSet ((parabolicSL2 ω) • s) :=
    (measurableEmbedding_h3Act (parabolicSL2 ω)).measurableSet_image.mpr hs
  rw [h3Measure_eq_lintegral hgs, h3Measure_eq_lintegral hs]
  set c : Fin 3 → ℝ := ![ω.re, ω.im, 0]
  have himg : h3Vec '' ((parabolicSL2 ω) • s) = (fun w => w + c) '' (h3Vec '' s) := by
    ext v
    simp only [Set.mem_image, Set.mem_smul_set, smul_h3_def]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨h3Vec p, ⟨p, hp, rfl⟩, (h3Vec_parabolicSL2 ω p).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨h3Act (parabolicSL2 ω) p, ⟨p, hp, rfl⟩, h3Vec_parabolicSL2 ω p⟩
  have hms : MeasurableSet (h3Vec '' s) := measurableEmbedding_h3Vec.measurableSet_image.mpr hs
  have hinj : Set.InjOn (fun w : Fin 3 → ℝ => w + c) (h3Vec '' s) :=
    (add_left_injective c).injOn
  have hfderiv : ∀ w ∈ h3Vec '' s,
      HasFDerivWithinAt (fun w : Fin 3 → ℝ => w + c) (ContinuousLinearMap.id ℝ (Fin 3 → ℝ))
        (h3Vec '' s) w := fun w _ =>
    ((hasFDerivAt_id w).add_const c).hasFDerivWithinAt
  rw [himg, MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hms hfderiv hinj]
  refine setLIntegral_congr_fun hms fun w _ => ?_
  have hdet : LinearMap.det (ContinuousLinearMap.id ℝ (Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = 1 :=
    LinearMap.det_id
  simp [hdet, c]

private theorem h3Measure_diagSL2 {a : ℂ} (ha : a ≠ 0) {s : Set H3} (hs : MeasurableSet s) :
    h3Measure ((diagSL2 a ha) • s) = h3Measure s := by
  have hgs : MeasurableSet ((diagSL2 a ha) • s) :=
    (measurableEmbedding_h3Act (diagSL2 a ha)).measurableSet_image.mpr hs
  rw [h3Measure_eq_lintegral hgs, h3Measure_eq_lintegral hs]
  set L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := (Matrix.toLin' (diagVecMat a)).toContinuousLinearMap
  have himg : h3Vec '' ((diagSL2 a ha) • s) = L '' (h3Vec '' s) := by
    ext v
    simp only [Set.mem_image, Set.mem_smul_set, smul_h3_def, L, LinearMap.coe_toContinuousLinearMap']
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨h3Vec p, ⟨p, hp, rfl⟩, (h3Vec_diagSL2 ha p).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨h3Act (diagSL2 a ha) p, ⟨p, hp, rfl⟩, h3Vec_diagSL2 ha p⟩
  have hms : MeasurableSet (h3Vec '' s) := measurableEmbedding_h3Vec.measurableSet_image.mpr hs
  have hinj : Set.InjOn L (h3Vec '' s) := by
    intro w₁ ⟨p₁, _, hp₁⟩ w₂ ⟨p₂, _, hp₂⟩ heq
    subst hp₁ hp₂
    have hact : h3Vec (h3Act (diagSL2 a ha) p₁) = h3Vec (h3Act (diagSL2 a ha) p₂) := by
      rw [h3Vec_diagSL2 ha p₁, h3Vec_diagSL2 ha p₂]; exact heq
    have hp12 : h3Act (diagSL2 a ha) p₁ = h3Act (diagSL2 a ha) p₂ := h3Vec_injective hact
    have : p₁ = p₂ := by
      calc p₁ = h3Act ((diagSL2 a ha)⁻¹ * diagSL2 a ha) p₁ := by rw [inv_mul_cancel, h3Act_one]
        _ = h3Act (diagSL2 a ha)⁻¹ (h3Act (diagSL2 a ha) p₁) := h3Act_mul _ _ _
        _ = h3Act (diagSL2 a ha)⁻¹ (h3Act (diagSL2 a ha) p₂) := by rw [hp12]
        _ = p₂ := by rw [← h3Act_mul, inv_mul_cancel, h3Act_one]
    rw [this]
  have hfderiv : ∀ w ∈ h3Vec '' s, HasFDerivWithinAt L L (h3Vec '' s) w := fun w _ =>
    L.hasFDerivAt.hasFDerivWithinAt
  rw [himg, MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hms hfderiv hinj]
  refine setLIntegral_congr_fun hms fun w hw => ?_
  obtain ⟨p, _, rfl⟩ := hw
  have hdet : |(L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)).det| = ‖a‖ ^ 6 := by
    have hd : (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)).det = (diagVecMat a).det :=
      LinearMap.det_toLin' (diagVecMat a)
    rw [hd, det_diagVecMat, abs_of_nonneg (by positivity)]
  have hw2 : L (h3Vec p) 2 = ‖a‖ ^ 2 * p.t := by
    simp [L, h3Vec, diagVecMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [hdet, hw2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [h3Vec_two]
  field_simp

private theorem h3Measure_invSL2 {s : Set H3} (hs : MeasurableSet s) :
    h3Measure (invSL2 • s) = h3Measure s := by
  have hgs : MeasurableSet (invSL2 • s) :=
    (measurableEmbedding_h3Act invSL2).measurableSet_image.mpr hs
  rw [h3Measure_eq_lintegral hgs, h3Measure_eq_lintegral hs]
  have himg : h3Vec '' (invSL2 • s) = invVecMap '' (h3Vec '' s) := by
    ext v
    simp only [Set.mem_image, Set.mem_smul_set, smul_h3_def]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨h3Vec p, ⟨p, hp, rfl⟩, (h3Vec_invSL2 p).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨h3Act invSL2 p, ⟨p, hp, rfl⟩, h3Vec_invSL2 p⟩
  have hms : MeasurableSet (h3Vec '' s) := measurableEmbedding_h3Vec.measurableSet_image.mpr hs
  have hinj : Set.InjOn invVecMap (h3Vec '' s) := by
    rintro _ ⟨p₁, -, rfl⟩ _ ⟨p₂, -, rfl⟩ heq
    have := congrArg invVecMap heq
    rwa [invVecMap_involutive p₁.t_pos, invVecMap_involutive p₂.t_pos] at this
  have hfderiv : ∀ w ∈ h3Vec '' s,
      HasFDerivWithinAt invVecMap (Matrix.toLin' (invVecJac w)).toContinuousLinearMap
        (h3Vec '' s) w := by
    rintro _ ⟨p, -, rfl⟩
    exact (hasFDerivAt_invVecMap p.t_pos).hasFDerivWithinAt
  rw [himg, MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hms hfderiv hinj]
  refine setLIntegral_congr_fun hms fun w hw => ?_
  obtain ⟨p, -, rfl⟩ := hw
  set r2 := (h3Vec p 0) ^ 2 + (h3Vec p 1) ^ 2 + (h3Vec p 2) ^ 2
  have hr2 : 0 < r2 := by
    have : 0 < h3Vec p 2 := p.t_pos
    positivity
  have hdet : |((Matrix.toLin' (invVecJac (h3Vec p))).toContinuousLinearMap :
      (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)).det| = r2⁻¹ ^ 3 := by
    change |(Matrix.toLin' (invVecJac (h3Vec p))).det| = r2⁻¹ ^ 3
    rw [LinearMap.det_toLin', det_invVecJac p.t_pos, abs_of_pos (by positivity)]
  have hw2 : invVecMap (h3Vec p) 2 = p.t / r2 := by
    simp [invVecMap, h3Vec, r2]
  rw [hdet, hw2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [h3Vec_two]
  field_simp

/-- Bruhat factorization of any `g ∈ SL(2, ℂ)` into parabolic, diagonal, and inversion generators. -/
theorem bruhat_sl2c (g : SL2C) :
    (∃ (ω a : ℂ) (ha : a ≠ 0), g = parabolicSL2 ω * diagSL2 a ha) ∨
    (∃ (ω₁ c ω₂ : ℂ) (hc : c ≠ 0),
      g = parabolicSL2 ω₁ * (diagSL2 c⁻¹ (inv_ne_zero hc) * (invSL2 * parabolicSL2 ω₂))) := by
  set a := g.1 0 0
  set b := g.1 0 1
  set c := g.1 1 0
  set d := g.1 1 1
  have hdet : a * d - b * c = 1 := by
    have h := g.prop
    rwa [Matrix.det_fin_two] at h
  by_cases hc : c = 0
  · left
    have had : a * d = 1 := by rw [hc, mul_zero, sub_zero] at hdet; exact hdet
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    have hd : d = a⁻¹ := eq_inv_of_mul_eq_one_right had
    refine ⟨b * a, a, ha, Subtype.ext <| Matrix.ext fun i j => ?_⟩
    change g.1 i j = ((parabolicSL2 (b * a)).1 * (diagSL2 a ha).1) i j
    fin_cases i <;> fin_cases j <;>
      simp [parabolicSL2, diagSL2, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, d, hc, hd]
    exact (mul_inv_cancel_right₀ ha b).symm
  · right
    refine ⟨a / c, c, d / c, hc, Subtype.ext <| Matrix.ext fun i j => ?_⟩
    change g.1 i j = ((parabolicSL2 (a / c)).1 *
      ((diagSL2 c⁻¹ (inv_ne_zero hc)).1 * (invSL2.1 * (parabolicSL2 (d / c)).1))) i j
    fin_cases i <;> fin_cases j <;>
      simp [parabolicSL2, diagSL2, invSL2, Matrix.mul_apply, Fin.sum_univ_two, a, c, d]
    · exact (div_mul_cancel₀ a hc).symm
    · change b = _
      field_simp [hc]
      linear_combination -hdet
    · exact (mul_div_cancel₀ d hc).symm

/-- **`SL(2, ℂ)` preserves the hyperbolic measure `h3Measure = t⁻³ dx dy dt`.** -/
theorem h3Measure_h3Act (g : SL2C) {s : Set H3} (hs : MeasurableSet s) :
    h3Measure (g • s) = h3Measure s := by
  have hmul_smul : ∀ (g₁ g₂ : SL2C) (E : Set H3), (g₁ * g₂) • E = g₁ • (g₂ • E) :=
    fun g₁ g₂ E => mul_smul g₁ g₂ E
  have hm : ∀ (h : SL2C) {E : Set H3}, MeasurableSet E → MeasurableSet (h • E) := by
    intro h E hE
    have : h • E = h3Act h '' E := rfl
    rw [this]
    exact (measurableEmbedding_h3Act h).measurableSet_image.mpr hE
  rcases bruhat_sl2c g with ⟨ω, a, ha, rfl⟩ | ⟨ω₁, c, ω₂, hc, rfl⟩
  · rw [hmul_smul, h3Measure_parabolicSL2 ω (hm _ hs), h3Measure_diagSL2 ha hs]
  · rw [hmul_smul, hmul_smul, hmul_smul,
      h3Measure_parabolicSL2 ω₁ (hm _ (hm _ (hm _ hs))),
      h3Measure_diagSL2 (inv_ne_zero hc) (hm _ (hm _ hs)),
      h3Measure_invSL2 (hm _ hs),
      h3Measure_parabolicSL2 ω₂ hs]

/-! ### Vertical geodesic stabilizer rigidity and the free-space Robin limit -/

@[simp]
theorem archProfile_zero : archProfile 0 = 0 := by
  simp [archProfile]

theorem archProfile_pos {d : ℝ} (hd : 0 < d) : 0 < archProfile d := by
  unfold archProfile
  refine div_pos (Real.exp_pos _) ?_
  have : Real.exp (-2 * d) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem strictAntiOn_archProfile : StrictAntiOn archProfile (Set.Ioi 0) := by
  intro d₁ hd₁ d₂ hd₂ hlt
  rw [Set.mem_Ioi] at hd₁ hd₂
  unfold archProfile
  have hnum : Real.exp (-d₂ / 2) < Real.exp (-d₁ / 2) := Real.exp_lt_exp.mpr (by linarith)
  have hden₁ : 0 < 1 - Real.exp (-2 * d₁) := by
    have : Real.exp (-2 * d₁) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hden₂ : 1 - Real.exp (-2 * d₁) < 1 - Real.exp (-2 * d₂) := by
    have : Real.exp (-2 * d₂) < Real.exp (-2 * d₁) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  calc Real.exp (-d₂ / 2) / (1 - Real.exp (-2 * d₂))
      < Real.exp (-d₂ / 2) / (1 - Real.exp (-2 * d₁)) :=
        div_lt_div_of_pos_left (Real.exp_pos _) hden₁ hden₂
    _ < Real.exp (-d₁ / 2) / (1 - Real.exp (-2 * d₁)) :=
        div_lt_div_of_pos_right hnum hden₁

theorem injOn_archProfile_Ici : Set.InjOn archProfile (Set.Ici 0) := by
  intro d₁ hd₁ d₂ hd₂ heq
  rw [Set.mem_Ici] at hd₁ hd₂
  rcases hd₁.eq_or_lt with rfl | h₁
  · rcases hd₂.eq_or_lt with rfl | h₂
    · rfl
    · rw [archProfile_zero] at heq
      exact absurd heq.symm (archProfile_pos h₂).ne'
  · rcases hd₂.eq_or_lt with rfl | h₂
    · rw [archProfile_zero] at heq
      exact absurd heq (archProfile_pos h₁).ne'
    · exact strictAntiOn_archProfile.injOn h₁ h₂ heq

theorem h3Act_degPoint_of_vertRot {g : SL2C} (hb : g.1 0 1 = 0) (hc : g.1 1 0 = 0)
    (ha : ‖g.1 0 0‖ = 1) {t : ℝ} (ht : 0 < t) :
    h3Act g (degPoint t ht) = degPoint t ht := by
  have hdet : g.1 0 0 * g.1 1 1 = 1 := by
    have := g.prop
    rw [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero] at this
    exact this
  have hd_norm : ‖g.1 1 1‖ = 1 := by
    have := congrArg norm hdet
    rwa [norm_mul, ha, one_mul, norm_one] at this
  have hden : h3Denom g (degPoint t ht) = 1 := by
    simp [h3Denom, degPoint, hc, hd_norm]
  ext
  · rw [h3Act_z, hden]; simp [degPoint, hb, hc]
  · rw [h3Act_t, hden]; simp [degPoint]

/-- **Vertical geodesic stabilizer rigidity.** An element `g ∈ SL(2, ℂ)` preserves the off-diagonal
archimedean Frobenius profile on integer degrees if and only if `g = diag(a, a⁻¹)` with `‖a‖ = 1`,
fixing the entire vertical geodesic pointwise. -/
theorem sl2_preserves_archFrobenius_iff (g : SL2C) :
    (∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n), m ≠ n →
      archProfile (h3Dist (natPoint m hm) (h3Act g (natPoint n hn))) =
        archProfile |Real.log n - Real.log m|) ↔
      g.1 0 1 = 0 ∧ g.1 1 0 = 0 ∧ ‖g.1 0 0‖ = 1 := by
  constructor
  · intro h
    have hcosh : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n), m ≠ n →
        h3Cosh (natPoint m hm) (h3Act g (natPoint n hn)) =
          ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) / (2 * m * n) := by
      intro m n hm hn hmn
      have hd : h3Dist (natPoint m hm) (h3Act g (natPoint n hn)) = |Real.log n - Real.log m| :=
        injOn_archProfile_Ici (Set.mem_Ici.mpr (h3Dist_nonneg _ _))
          (Set.mem_Ici.mpr (abs_nonneg _)) (h m n hm hn hmn)
      have h1 := cosh_h3Dist (natPoint m hm) (h3Act g (natPoint n hn))
      rw [hd, Real.cosh_abs, cosh_log_sub_log (by exact_mod_cast hm) (by exact_mod_cast hn)] at h1
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [← h1]
      field_simp
      ring
    -- Pin `g • natPoint 2 = natPoint 2` via anchors `m = 1` and `m = 4`
    have hp2 : h3Act g (natPoint 2 (by norm_num)) = natPoint 2 (by norm_num) := by
      set p := h3Act g (natPoint 2 (by norm_num))
      have hp_pos : p.t ≠ 0 := p.t_pos.ne'
      have c1 := hcosh 1 2 (by norm_num) (by norm_num) (by norm_num)
      have c4 := hcosh 4 2 (by norm_num) (by norm_num) (by norm_num)
      rw [← show p = h3Act g (natPoint 2 (by norm_num)) from rfl] at c1 c4
      simp only [h3Cosh, natPoint, zero_sub, norm_neg, Nat.cast_one, Nat.cast_ofNat] at c1 c4
      norm_num at c1 c4
      have e1 : ‖p.z‖ ^ 2 + (1 - p.t) ^ 2 = p.t / 2 := by
        have : (‖p.z‖ ^ 2 + (1 - p.t) ^ 2) / (2 * p.t) = 1 / 4 := by linarith
        field_simp at this ⊢; linarith
      have e4 : ‖p.z‖ ^ 2 + (4 - p.t) ^ 2 = 2 * p.t := by
        have : (‖p.z‖ ^ 2 + (4 - p.t) ^ 2) / (8 * p.t) = 1 / 4 := by linarith
        field_simp at this ⊢; linarith
      have ht2 : p.t = 2 := by linarith
      have hz0 : p.z = 0 := by
        rw [ht2] at e1
        have : ‖p.z‖ ^ 2 = 0 := by linarith
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
      exact H3.ext hz0 (by simpa [natPoint] using ht2)
    -- Pin `g • natPoint 3 = natPoint 3` via anchors `m = 1` and `m = 9`
    have hp3 : h3Act g (natPoint 3 (by norm_num)) = natPoint 3 (by norm_num) := by
      set q := h3Act g (natPoint 3 (by norm_num))
      have hq_pos : q.t ≠ 0 := q.t_pos.ne'
      have c1 := hcosh 1 3 (by norm_num) (by norm_num) (by norm_num)
      have c9 := hcosh 9 3 (by norm_num) (by norm_num) (by norm_num)
      rw [← show q = h3Act g (natPoint 3 (by norm_num)) from rfl] at c1 c9
      simp only [h3Cosh, natPoint, zero_sub, norm_neg, Nat.cast_one, Nat.cast_ofNat] at c1 c9
      norm_num at c1 c9
      have e1 : ‖q.z‖ ^ 2 + (1 - q.t) ^ 2 = 4 * q.t / 3 := by
        have : (‖q.z‖ ^ 2 + (1 - q.t) ^ 2) / (2 * q.t) = 2 / 3 := by linarith
        field_simp at this ⊢; linarith
      have e9 : ‖q.z‖ ^ 2 + (9 - q.t) ^ 2 = 12 * q.t := by
        have : (‖q.z‖ ^ 2 + (9 - q.t) ^ 2) / (18 * q.t) = 2 / 3 := by linarith
        field_simp at this ⊢; linarith
      have hu3 : q.t = 3 := by linarith
      have hw0 : q.z = 0 := by
        rw [hu3] at e1
        have : ‖q.z‖ ^ 2 = 0 := by linarith
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
      exact H3.ext hw0 (by simpa [natPoint] using hu3)
    -- Deduce `c = 0`, `‖d‖ = 1`, `b = 0`, `‖a‖ = 1`
    have hden2 : h3Denom g (natPoint 2 (by norm_num)) = 1 := by
      have ht : (2 : ℝ) / h3Denom g (natPoint 2 (by norm_num)) = 2 := by
        have h2 := congrArg H3.t hp2
        unfold h3Act at h2
        simpa [natPoint] using h2
      have hpos := (h3Denom_pos g (natPoint 2 (by norm_num))).ne'
      field_simp at ht
      linarith
    have hden3 : h3Denom g (natPoint 3 (by norm_num)) = 1 := by
      have ht : (3 : ℝ) / h3Denom g (natPoint 3 (by norm_num)) = 3 := by
        have h3 := congrArg H3.t hp3
        unfold h3Act at h3
        simpa [natPoint] using h3
      have hpos := (h3Denom_pos g (natPoint 3 (by norm_num))).ne'
      field_simp at ht
      linarith
    simp only [h3Denom, natPoint, mul_zero, zero_add] at hden2 hden3
    norm_num at hden2 hden3
    have hc_sq : ‖g.1 1 0‖ ^ 2 = 0 := by linarith
    have hc : g.1 1 0 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hc_sq)
    have hd_sq : ‖g.1 1 1‖ ^ 2 = 1 := by linarith
    have hd_norm : ‖g.1 1 1‖ = 1 := by
      nlinarith [norm_nonneg (g.1 1 1), sq_abs ‖g.1 1 1‖]
    have hd_ne : g.1 1 1 ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hd_norm; norm_num at hd_norm
    have hb : g.1 0 1 = 0 := by
      have hz := congrArg H3.z hp2
      have hden_one : h3Denom g (natPoint 2 (by norm_num)) = 1 := by
        simp [h3Denom, natPoint, hc, hd_norm]
      rw [h3Act_z, hden_one] at hz
      simp only [natPoint, mul_zero, zero_add, hc, map_zero, add_zero,
        Complex.ofReal_one, div_one] at hz
      exact (mul_eq_zero.mp hz).resolve_right (map_ne_zero _ |>.mpr hd_ne)
    have ha_norm : ‖g.1 0 0‖ = 1 := by
      have hdet := g.prop
      rw [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero] at hdet
      have := congrArg norm hdet
      rwa [norm_mul, hd_norm, mul_one, norm_one] at this
    exact ⟨hb, hc, ha_norm⟩
  · rintro ⟨hb, hc, ha⟩ m n hm hn _
    have hfix : h3Act g (natPoint n hn) = natPoint n hn :=
      h3Act_degPoint_of_vertRot hb hc ha (by exact_mod_cast hn)
    rw [hfix]
    congr 1
    exact h3Dist_degPoint (by exact_mod_cast hm) (by exact_mod_cast hn)

private theorem abs_sinh_sub_le (d : ℝ) : |Real.sinh d - d| ≤ d ^ 2 * |Real.sinh d| := by
  have hpos_case : ∀ x : ℝ, 0 ≤ x → |Real.sinh x - x| ≤ x ^ 2 * |Real.sinh x| := by
    intro x hx
    rcases hx.eq_or_lt with rfl | hx_pos
    · simp
    -- Bound `cosh t - 1 ≤ x * sinh x` on `[0, x]`
    have hc_bound : ∀ t ∈ Set.Icc 0 x, ‖Real.cosh t - 1‖ ≤ x * Real.sinh x := by
      intro t ht
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := Real.cosh) (f' := Real.sinh)
        (fun u _ => (Real.hasDerivAt_cosh u).hasDerivWithinAt)
        (fun u hu => by
          rw [Real.norm_of_nonneg (Real.sinh_nonneg_iff.mpr hu.1), Real.sinh_le_sinh]
          exact hu.2.trans ht.2)
        (convex_Icc 0 t) (Set.left_mem_Icc.mpr ht.1) (Set.right_mem_Icc.mpr ht.1)
      rw [Real.cosh_zero, Real.norm_of_nonneg (sub_nonneg.mpr ht.1), sub_zero] at hmvt
      exact hmvt.trans (by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right ht.2 (Real.sinh_nonneg_iff.mpr hx))
    have hmvt2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => Real.sinh t - t) (f' := fun t => Real.cosh t - 1)
      (fun t _ => ((Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)).hasDerivWithinAt)
      hc_bound (convex_Icc 0 x) (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx)
    simp only [Real.sinh_zero, sub_self, sub_zero, Real.norm_eq_abs, abs_of_nonneg hx,
      abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx)] at hmvt2 ⊢
    calc |Real.sinh x - x| ≤ x * Real.sinh x * x := hmvt2
      _ = x ^ 2 * Real.sinh x := by ring
  rcases le_total 0 d with hd | hd
  · exact hpos_case d hd
  · have h := hpos_case (-d) (by linarith)
    rw [Real.sinh_neg, show -Real.sinh d - -d = -(Real.sinh d - d) by ring, abs_neg,
      neg_sq, abs_neg] at h
    exact h

/-- **Free-space Robin constant of `ℍ³`.** Removing the Newtonian singularity `1 / (2 d)` from
`2π G_s(d)` leaves the finite limit `(1 - s) / 2` (`1 / 4` at `s = 1 / 2`), independent of the
base point on the vertical geodesic. -/
theorem tendsto_freeSpace_robin (s : ℝ) :
    Tendsto (fun d : ℝ => 2 * Real.pi * hyperbolicGreen s d - 1 / (2 * d))
      (𝓝[≠] 0) (𝓝 ((1 - s) / 2)) := by
  have hslope_sinh : Tendsto (fun d : ℝ => Real.sinh d / d) (𝓝[≠] 0) (𝓝 1) := by
    have := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_sinh 0)
    rw [Real.cosh_zero] at this
    exact this.congr fun d => by rw [slope_def_field, Real.sinh_zero, sub_zero, sub_zero]
  have hslope_exp : Tendsto (fun d : ℝ => (Real.exp (-(s - 1) * d) - 1) / d) (𝓝[≠] 0)
      (𝓝 (-(s - 1))) := by
    have hd := hasDerivAt_exp_neg_mul (s - 1) 0
    rw [mul_zero, Real.exp_zero, mul_one] at hd
    have := hasDerivAt_iff_tendsto_slope.mp hd
    exact this.congr fun d => by rw [slope_def_field, mul_zero, Real.exp_zero, sub_zero]
  have hrem : Tendsto (fun d : ℝ => (Real.sinh d - d) / d ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun d => |Real.sinh d|) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with d hd
      rw [Real.norm_eq_abs, abs_div, abs_sq]
      rw [Set.mem_compl_singleton_iff] at hd
      have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
      exact (div_le_iff₀ hd2).mpr (by rw [mul_comm]; exact abs_sinh_sub_le d)
    · have hc : Continuous fun d : ℝ => |Real.sinh d| := continuous_abs.comp Real.continuous_sinh
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hcomb := (hslope_exp.sub hrem).div (hslope_sinh.const_mul 2) (by norm_num)
  have hlim : (-(s - 1) - 0) / (2 * 1) = (1 - s) / 2 := by ring
  rw [hlim] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  rw [Set.mem_compl_singleton_iff] at hd
  have hs : Real.sinh d ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  dsimp only [Pi.div_apply, Pi.sub_apply]
  unfold hyperbolicGreen
  field_simp
  ring

theorem tendsto_archProfile_robin :
    Tendsto (fun d : ℝ => archProfile d - 1 / (2 * d)) (𝓝[≠] 0) (𝓝 (1 / 4)) := by
  have h := tendsto_freeSpace_robin (1 / 2)
  rw [show (1 - (1 / 2 : ℝ)) / 2 = 1 / 4 by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  rw [archProfile_eq_hyperbolicGreen hd]

/-- **Prime-orbit self-intersection per point.** At a prime `p`, the normalized self-intersection is
`((p - 2) / (p - 1)) log p`. -/
theorem prime_selfIntersection_per_point {p : ℕ} (hp : p.Prime) :
    orbitIntersection p p / Nat.totient p =
      ((p : ℝ) - 2) / ((p : ℝ) - 1) * Real.log p := by
  have h1 := ArithmeticElectrostatics.orbitIntersection_self_prime_pow hp 0
  simp only [zero_add, pow_one, pow_zero, one_mul, Nat.totient_prime hp] at h1 ⊢
  have hp2 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  rw [h1, hsub]
  field_simp
  ring

/-- The prime-orbit self-intersection per point grows unboundedly along the primes. -/
theorem tendsto_prime_selfIntersection_atTop :
    Tendsto (fun k : ℕ => orbitIntersection (Nat.nth Nat.Prime k) (Nat.nth Nat.Prime k) /
      Nat.totient (Nat.nth Nat.Prime k)) atTop atTop := by
  have hP : ∀ k, (Nat.nth Nat.Prime k).Prime := Nat.prime_nth_prime
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  have hge : ∀ k, k ≤ Nat.nth Nat.Prime k := hmono.id_le
  refine tendsto_atTop_mono' atTop ?_
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono hge tendsto_id))).const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 3] with k hk
  set p := Nat.nth Nat.Prime k
  have hp3 : 3 ≤ p := le_trans hk (hge k)
  have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  rw [prime_selfIntersection_per_point (hP k)]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hfrac : 1 / 2 ≤ ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  exact mul_le_mul_of_nonneg_right hfrac hlog

/-- No constant geodesic Robin shift agrees with the prime-orbit diagonal counterterm. -/
theorem not_exists_const_robin_prime_selfIntersection (c : ℝ) :
    ¬ ∀ p : ℕ, p.Prime → orbitIntersection p p / Nat.totient p = c := by
  intro h
  have hconst : (fun k : ℕ => orbitIntersection (Nat.nth Nat.Prime k) (Nat.nth Nat.Prime k) /
      Nat.totient (Nat.nth Nat.Prime k)) = fun _ => c :=
    funext fun k => h _ (Nat.prime_nth_prime k)
  have ht := tendsto_prime_selfIntersection_atTop
  rw [hconst] at ht
  exact not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds ht

/-! ## Section 2. Finite-covolume Kleinian quotients and parabolic cusp divergence -/

/-- Inscribed Euclidean box parameter `δ(ρ) = min(1 / 2, √((cosh ρ - 1) / 4))`. -/
def h3BallDelta (ρ : ℝ) : ℝ :=
  min (1 / 2) (Real.sqrt ((Real.cosh ρ - 1) / 4))

theorem h3BallDelta_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < h3BallDelta ρ := by
  unfold h3BallDelta
  refine lt_min (by norm_num) (Real.sqrt_pos.mpr ?_)
  have : 1 < Real.cosh ρ := Real.one_lt_cosh.mpr hρ.ne'
  linarith

theorem h3BallDelta_le_half (ρ : ℝ) : h3BallDelta ρ ≤ 1 / 2 :=
  min_le_left _ _

/-- **Scale-invariant hyperbolic ball volume.** Every geodesic ball of radius `ρ > 0` centered at
`degPoint t` has hyperbolic measure at least `(64 / 27) δ(ρ)³ > 0`, independent of `t > 0`. -/
theorem h3Measure_ball_ge {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    ENNReal.ofReal (64 / 27 * h3BallDelta ρ ^ 3) ≤
      h3Measure {p : H3 | h3Dist (degPoint t ht) p < ρ} := by
  set δ := h3BallDelta ρ
  have hδ_pos : 0 < δ := h3BallDelta_pos hρ
  have hδ_half : δ ≤ 1 / 2 := h3BallDelta_le_half ρ
  have hδ_sq : 4 * δ ^ 2 ≤ Real.cosh ρ - 1 := by
    have hle : δ ≤ Real.sqrt ((Real.cosh ρ - 1) / 4) := min_le_right _ _
    have h1 : 1 < Real.cosh ρ := Real.one_lt_cosh.mpr hρ.ne'
    have hsq := pow_le_pow_left₀ hδ_pos.le hle 2
    rw [Real.sq_sqrt (by linarith)] at hsq
    linarith
  -- Inscribed Euclidean box `Q ⊆ Fin 3 → ℝ`
  set a : Fin 3 → ℝ := ![-δ * t, -δ * t, (1 - δ) * t]
  set b : Fin 3 → ℝ := ![δ * t, δ * t, (1 + δ) * t]
  set Q : Set (Fin 3 → ℝ) := Set.pi Set.univ fun i => Set.Icc (a i) (b i)
  have hQ_meas : MeasurableSet Q :=
    MeasurableSet.univ_pi fun i => measurableSet_Icc
  have hQ_sub : Q ⊆ h3Vec '' {p : H3 | h3Dist (degPoint t ht) p < ρ} := by
    intro w hw
    have hw0 : w 0 ∈ Set.Icc (-δ * t) (δ * t) := hw 0 trivial
    have hw1 : w 1 ∈ Set.Icc (-δ * t) (δ * t) := hw 1 trivial
    have hw2 : w 2 ∈ Set.Icc ((1 - δ) * t) ((1 + δ) * t) := hw 2 trivial
    have hu_lo : t / 2 ≤ w 2 := by nlinarith [hw2.1]
    have hu_pos : 0 < w 2 := by linarith
    set p : H3 := ⟨⟨w 0, w 1⟩, w 2, hu_pos⟩
    have hpvec : h3Vec p = w := by ext i; fin_cases i <;> rfl
    refine ⟨p, ?_, hpvec⟩
    rw [Set.mem_setOf_eq, h3Dist, ← Real.arcosh_cosh hρ.le,
      Real.arcosh_lt_arcosh (h3Cosh_pos _ _) (Real.cosh_pos ρ)]
    unfold h3Cosh degPoint
    have hx2 : w 0 ^ 2 ≤ δ ^ 2 * t ^ 2 := by
      have : |w 0| ≤ δ * t := abs_le.mpr ⟨by linarith [hw0.1], by linarith [hw0.2]⟩
      nlinarith [sq_abs (w 0), abs_nonneg (w 0)]
    have hy2 : w 1 ^ 2 ≤ δ ^ 2 * t ^ 2 := by
      have : |w 1| ≤ δ * t := abs_le.mpr ⟨by linarith [hw1.1], by linarith [hw1.2]⟩
      nlinarith [sq_abs (w 1), abs_nonneg (w 1)]
    have hz2 : (t - w 2) ^ 2 ≤ δ ^ 2 * t ^ 2 := by
      have : |t - w 2| ≤ δ * t := abs_le.mpr ⟨by linarith [hw2.2], by linarith [hw2.1]⟩
      nlinarith [sq_abs (t - w 2), abs_nonneg (t - w 2)]
    have hnorm : ‖(0 : ℂ) - p.z‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
      simp [p, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rw [hnorm]
    dsimp only [p]
    have hden_lo : t ^ 2 ≤ 2 * t * w 2 := by nlinarith
    have hfrac : (w 0 ^ 2 + w 1 ^ 2 + (t - w 2) ^ 2) / (2 * t * w 2) ≤ 3 * δ ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      calc w 0 ^ 2 + w 1 ^ 2 + (t - w 2) ^ 2
          ≤ 3 * δ ^ 2 * t ^ 2 := by linarith
        _ ≤ 3 * δ ^ 2 * (2 * t * w 2) :=
            mul_le_mul_of_nonneg_left hden_lo (by positivity)
    nlinarith [sq_nonneg δ]
  have hvol_Q : volume Q = ENNReal.ofReal (8 * δ ^ 3 * t ^ 3) := by
    rw [MeasureTheory.volume_pi_pi, Fin.prod_univ_three]
    simp only [a, b, Real.volume_Icc, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [← ENNReal.ofReal_mul (by nlinarith), ← ENNReal.ofReal_mul (by nlinarith)]
    congr 1
    ring
  rw [h3Measure_eq_lintegral (isOpen_lt (continuous_h3Dist_right _) continuous_const).measurableSet]
  calc ENNReal.ofReal (64 / 27 * δ ^ 3)
      = ENNReal.ofReal ((2 / (3 * t)) ^ 3) * volume Q := by
        rw [hvol_Q, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ∫⁻ _ in Q, ENNReal.ofReal ((2 / (3 * t)) ^ 3) ∂volume := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ w in Q, ENNReal.ofReal ((w 2)⁻¹ ^ 3) ∂volume := by
        refine setLIntegral_mono' hQ_meas fun w hw => ?_
        have hw2 : w 2 ∈ Set.Icc ((1 - δ) * t) ((1 + δ) * t) := hw 2 trivial
        have hu_pos : 0 < w 2 := by nlinarith [hw2.1]
        have hu_hi : w 2 ≤ 3 * t / 2 := by nlinarith [hw2.2]
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 3)
        rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hu_pos]
        linarith
    _ ≤ ∫⁻ w in h3Vec '' {p : H3 | h3Dist (degPoint t ht) p < ρ},
          ENNReal.ofReal ((w 2)⁻¹ ^ 3) ∂volume :=
        lintegral_mono_set hQ_sub

/-- Pointwise stabilizer of the vertical geodesic inside a subgroup `Γ ≤ SL(2, ℂ)`. -/
def vertStab (Γ : Subgroup SL2C) : Subgroup Γ where
  carrier := {γ : Γ | ∀ (t : ℝ) (ht : 0 < t), h3Act (γ : SL2C) (degPoint t ht) = degPoint t ht}
  one_mem' _ _ := h3Act_one _
  mul_mem' {γ₁ γ₂} h₁ h₂ t ht := by
    change h3Act ((γ₁ : SL2C) * (γ₂ : SL2C)) (degPoint t ht) = degPoint t ht
    rw [h3Act_mul, h₂ t ht, h₁ t ht]
  inv_mem' {γ} h t ht := by
    calc h3Act (γ⁻¹ : SL2C) (degPoint t ht)
        = h3Act (γ⁻¹ : SL2C) (h3Act (γ : SL2C) (degPoint t ht)) := by rw [h t ht]
      _ = h3Act ((γ⁻¹ : SL2C) * (γ : SL2C)) (degPoint t ht) := (h3Act_mul _ _ _).symm
      _ = degPoint t ht := by rw [inv_mul_cancel, h3Act_one]

theorem finite_vertStab (Γ : Subgroup SL2C) [DiscreteTopology Γ] : Finite (vertStab Γ) := by
  -- Every element of `vertStab Γ` has matrix entries of norm at most `1`
  set B : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1
  have hB_comp : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ProperSpace.isCompact_closedBall 0 1
  have hSL_closed : IsClosed (Set.range (Subtype.val : SL2C → Matrix (Fin 2) (Fin 2) ℂ)) := by
    have heq : Set.range (Subtype.val : SL2C → Matrix (Fin 2) (Fin 2) ℂ) =
        {M | M.det = 1} := by
      ext M
      simp only [Set.mem_range, Set.mem_setOf_eq]
      exact ⟨fun ⟨g, hg⟩ => hg ▸ g.prop, fun h => ⟨⟨M, h⟩, rfl⟩⟩
    rw [heq]
    exact isClosed_eq continuous_id.matrix_det continuous_const
  have hK_comp : IsCompact ((Subtype.val : SL2C → Matrix (Fin 2) (Fin 2) ℂ) ⁻¹' B) :=
    IsClosedEmbedding.isCompact_preimage ⟨⟨⟨rfl⟩, Subtype.val_injective⟩, hSL_closed⟩ hB_comp
  have hdisc : IsDiscrete (Γ : Set SL2C) := isDiscrete_iff_discreteTopology.mpr ‹_›
  have htend := Subgroup.tendsto_coe_cofinite_of_discrete Γ hdisc
  have hfin : {γ : Γ | (γ : SL2C) ∈ (Subtype.val : SL2C → Matrix (Fin 2) (Fin 2) ℂ) ⁻¹' B}.Finite :=
    (Filter.eventually_cofinite.mp (htend.eventually hK_comp.compl_mem_cocompact)).subset
      fun _ h hnot => hnot h
  refine Set.Finite.to_subtype (hfin.subset fun γ hγ => ?_)
  have hpres : ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n), m ≠ n →
      archProfile (h3Dist (natPoint m hm) (h3Act (γ : SL2C) (natPoint n hn))) =
        archProfile |Real.log n - Real.log m| := by
    intro m n hm hn _
    have hfix : h3Act (γ : SL2C) (natPoint n hn) = natPoint n hn :=
      hγ n (by exact_mod_cast hn)
    rw [hfix, show natPoint m hm = degPoint m (by exact_mod_cast hm) from rfl,
      show natPoint n hn = degPoint n (by exact_mod_cast hn) from rfl,
      h3Dist_degPoint]
  obtain ⟨hb, hc, ha⟩ := (sl2_preserves_archFrobenius_iff (γ : SL2C)).mp hpres
  have hd_norm : ‖(γ : SL2C).1 1 1‖ = 1 := by
    have hdet := (γ : SL2C).prop
    rw [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero] at hdet
    have := congrArg norm hdet
    rwa [norm_mul, ha, one_mul, norm_one] at this
  intro i _ j _
  rw [Metric.mem_closedBall, dist_zero_right]
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd_norm]

/-- A subgroup `Γ ≤ SL(2, ℂ)` has finite hyperbolic covolume when a measurable set of finite
`h3Measure` sweeps out `ℍ³` under `Γ`. -/
def HasFiniteCovolume (Γ : Subgroup SL2C) : Prop :=
  ∃ F : Set H3, MeasurableSet F ∧ h3Measure F < ⊤ ∧ ∀ p : H3, ∃ γ : Γ, h3Act (γ : SL2C) p ∈ F

/-- **Thin–thick dichotomy on finite-covolume Kleinian quotients.** For any discrete finite-covolume
subgroup `Γ ≤ SL(2, ℂ)`, any infinite set `S` of positive integer degrees, and any `ε > 0`, either:
1. *(Thin end / orbifold collapse)* Infinitely many `n ∈ S` satisfy `d(ζ_n, γ • ζ_n) < ε` for some
   `γ ∈ Γ \ vertStab Γ`; or
2. *(Thick-end off-diagonal folding)* For every ratio bound `R > 1`, there exist `m, n ∈ S` with
   `n / m > R` and `γ ∈ Γ` such that `d(ζ_m, γ • ζ_n) < ε`. -/
theorem kleinian_thin_thick_dichotomy (Γ : Subgroup SL2C) [DiscreteTopology Γ]
    (hcov : HasFiniteCovolume Γ) {S : Set ℕ} (hS_inf : S.Infinite) (hS_pos : ∀ n ∈ S, 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    Set.Infinite {n : ℕ | ∃ hn : n ∈ S, ∃ γ : Γ, γ ∉ vertStab Γ ∧
      h3Dist (natPoint n (hS_pos n hn)) (h3Act (γ : SL2C) (natPoint n (hS_pos n hn))) < ε} ∨
    ∀ R : ℝ, 1 < R → ∃ m, ∃ hm : m ∈ S, ∃ n, ∃ hn : n ∈ S, R < (n : ℝ) / m ∧ ∃ γ : Γ,
      h3Dist (natPoint m (hS_pos m hm)) (h3Act (γ : SL2C) (natPoint n (hS_pos n hn))) < ε := by
  classical
  by_contra hboth
  push Not at hboth
  obtain ⟨hfin_thin, R, hR1, hno_fold⟩ := hboth
  obtain ⟨F, hF_meas, hF_lt, hF_cov⟩ := hcov
  -- Countability of `Γ` and finiteness of `vertStab Γ`
  haveI : SecondCountableTopology SL2C := inferInstance
  haveI : SecondCountableTopology Γ := TopologicalSpace.SecondCountableTopology.induced _
  haveI : Countable Γ := TopologicalSpace.countable_of_isOpen_disjoint
    (fun γ => ({γ} : Set Γ)) (fun _ => isOpen_discrete _) (fun _ => rfl)
    (fun a b hab => Set.disjoint_singleton.mpr hab)
  haveI : Finite (vertStab Γ) := finite_vertStab Γ
  haveI : Fintype (vertStab Γ) := Fintype.ofFinite (vertStab Γ)
  -- Infinite thick subset `S₁ = S \ thinSet`
  set thinSet : Set ℕ := {n : ℕ | ∃ hn : n ∈ S, ∃ γ : Γ, γ ∉ vertStab Γ ∧
    h3Dist (natPoint n (hS_pos n hn)) (h3Act (γ : SL2C) (natPoint n (hS_pos n hn))) < ε}
  set S₁ : Set ℕ := S \ thinSet
  have hS₁_inf : S₁.Infinite := hS_inf.diff hfin_thin
  -- Extract a sequence `seq : ℕ → ℕ` in `S₁` with ratio `> R`
  have hstep : ∀ a : ℕ, ∃ b ∈ S₁, a < b ∧ R * (a : ℝ) < b := by
    intro a
    set bound := max a ⌊R * (a : ℝ)⌋₊ + 1
    obtain ⟨b, hbS₁, hble⟩ := hS₁_inf.exists_gt bound
    refine ⟨b, hbS₁, by omega, ?_⟩
    have hfl : R * (a : ℝ) < (⌊R * (a : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hba : (⌊R * (a : ℝ)⌋₊ : ℝ) + 1 ≤ b := by
      have : ⌊R * (a : ℝ)⌋₊ + 1 ≤ b := by omega
      exact_mod_cast this
    linarith
  choose nextN hnext_mem hnext_gt hnext_rat using hstep
  obtain ⟨n₀, hn₀⟩ := hS₁_inf.nonempty
  let seq : ℕ → ℕ := fun k => Nat.rec n₀ (fun _ prev => nextN prev) k
  have hseq_mem : ∀ k, seq k ∈ S₁ := by
    intro k; induction k with
    | zero => exact hn₀
    | succ k _ => exact hnext_mem _
  have hseq_S : ∀ k, seq k ∈ S := fun k => (hseq_mem k).1
  have hseq_pos : ∀ k, 0 < seq k := fun k => hS_pos _ (hseq_S k)
  have hseq_rat_succ : ∀ k, R < (seq (k + 1) : ℝ) / (seq k : ℝ) := by
    intro k
    have hp : (0 : ℝ) < seq k := by exact_mod_cast hseq_pos k
    rw [lt_div_iff₀ hp]
    exact hnext_rat (seq k)
  have hseq_rat : ∀ {i j : ℕ}, i < j → R < (seq j : ℝ) / (seq i : ℝ) := by
    intro i j hij
    obtain ⟨d, hd, rfl⟩ := Nat.exists_eq_add_of_lt hij
    induction d with
    | zero => omega
    | succ d ih =>
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · simpa using hseq_rat_succ i
      · have h1 := ih hd_pos
        have h2 := hseq_rat_succ (i + d)
        have hp1 : (0 : ℝ) < seq i := by exact_mod_cast hseq_pos i
        have hp2 : (0 : ℝ) < seq (i + d) := by exact_mod_cast hseq_pos (i + d)
        calc R < R * R := lt_mul_of_one_lt_right (by linarith) hR1
          _ < ((seq (i + d) : ℝ) / seq i) * ((seq (i + d + 1) : ℝ) / seq (i + d)) :=
              mul_lt_mul'' h1 h2 (by linarith) (by linarith)
          _ = (seq (i + (d + 1)) : ℝ) / seq i := by
              rw [show i + (d + 1) = i + d + 1 by omega]; field_simp
  -- Geodesic balls of radius `ε / 2` and their fundamental-domain projections `E k`
  have hε2 : 0 < ε / 2 := half_pos hε
  let B : ℕ → Set H3 := fun k =>
    {p : H3 | h3Dist (natPoint (seq k) (hseq_pos k)) p < ε / 2}
  have hB_open : ∀ k, IsOpen (B k) := by
    intro k
    set q0 := natPoint (seq k) (hseq_pos k)
    have hcont_cosh : Continuous (fun p : H3 => h3Cosh q0 p) := by
      have hc0 : Continuous (fun p : H3 => h3Vec p 0) :=
        (continuous_apply 0).comp continuous_induced_dom
      have hc1 : Continuous (fun p : H3 => h3Vec p 1) :=
        (continuous_apply 1).comp continuous_induced_dom
      have hct : Continuous (fun p : H3 => p.t) :=
        (continuous_apply 2).comp continuous_induced_dom
      have hcz : Continuous (fun p : H3 => p.z) := by
        have heq : (fun p : H3 => p.z) =
            fun p => (h3Vec p 0 : ℂ) + (h3Vec p 1 : ℂ) * Complex.I :=
          funext fun p => (Complex.re_add_im p.z).symm
        rw [heq]
        exact (Complex.continuous_ofReal.comp hc0).add
          ((Complex.continuous_ofReal.comp hc1).mul continuous_const)
      unfold h3Cosh
      refine continuous_const.add (Continuous.div ?_ ?_ fun p => ?_)
      · exact (((continuous_const.sub hcz).norm.pow 2).add ((continuous_const.sub hct).pow 2))
      · exact continuous_const.mul hct
      · have := q0.t_pos; have := p.t_pos; positivity
    have hcont_dist : Continuous (fun p : H3 => h3Dist q0 p) :=
      Real.continuousOn_arcosh.comp_continuous hcont_cosh fun p => one_le_h3Cosh q0 p
    exact isOpen_lt hcont_dist continuous_const
  have hB_meas : ∀ k, MeasurableSet (B k) := fun k => (hB_open k).measurableSet
  let E : ℕ → Set H3 := fun k => (⋃ γ : Γ, (γ : SL2C) • B k) ∩ F
  have hE_meas : ∀ k, MeasurableSet (E k) := fun k =>
    (MeasurableSet.iUnion fun γ =>
      (measurableEmbedding_h3Act (γ : SL2C)).measurableSet_image.mpr (hB_meas k)).inter hF_meas
  -- Pairwise disjointness of `E i` and `E j` (`i ≠ j`)
  have hE_disj : Pairwise (Disjoint on E) := by
    intro i j hij
    rw [Set.disjoint_iff]
    rintro x ⟨⟨hxi, -⟩, ⟨hxj, -⟩⟩
    rw [Set.mem_iUnion] at hxi hxj
    obtain ⟨γ₁, p₁, hp₁, rfl⟩ := hxi
    obtain ⟨γ₂, p₂, hp₂, heq⟩ := hxj
    have hd_lt : ∀ a b : ℕ, (∃ γ : Γ,
        h3Dist (natPoint (seq a) (hseq_pos a))
          (h3Act (γ : SL2C) (natPoint (seq b) (hseq_pos b))) < ε) → a < b → False := by
      rintro a b ⟨γ, hd⟩ hab
      exact not_le.mpr hd (hno_fold (seq a) (hseq_S a) (seq b) (hseq_S b) (hseq_rat hab) γ)
    -- Triangle inequality gives `d(ζ_{seq i}, (γ₁⁻¹ * γ₂) • ζ_{seq j}) < ε`
    have htri : h3Dist (natPoint (seq i) (hseq_pos i))
        (h3Act ((γ₁⁻¹ * γ₂ : Γ) : SL2C) (natPoint (seq j) (hseq_pos j))) < ε := by
      have hp12 : p₁ = h3Act ((γ₁⁻¹ * γ₂ : Γ) : SL2C) p₂ := by
        change (γ₁ : SL2C) • p₁ = (γ₂ : SL2C) • p₂ at heq
        calc p₁ = ((γ₁ : SL2C)⁻¹ * (γ₁ : SL2C)) • p₁ := by rw [inv_mul_cancel, one_smul]
          _ = (γ₁ : SL2C)⁻¹ • ((γ₁ : SL2C) • p₁) := mul_smul _ _ _
          _ = (γ₁ : SL2C)⁻¹ • ((γ₂ : SL2C) • p₂) := by rw [heq]
          _ = ((γ₁⁻¹ * γ₂ : Γ) : SL2C) • p₂ := (mul_smul _ _ _).symm
      calc h3Dist (natPoint (seq i) (hseq_pos i))
            (h3Act ((γ₁⁻¹ * γ₂ : Γ) : SL2C) (natPoint (seq j) (hseq_pos j)))
          ≤ h3Dist (natPoint (seq i) (hseq_pos i)) p₁ +
              h3Dist p₁ (h3Act ((γ₁⁻¹ * γ₂ : Γ) : SL2C) (natPoint (seq j) (hseq_pos j))) :=
            h3Dist_triangle _ _ _
        _ = h3Dist (natPoint (seq i) (hseq_pos i)) p₁ +
              h3Dist (natPoint (seq j) (hseq_pos j)) p₂ := by
            rw [hp12, h3Dist_h3Act, h3Dist_comm p₂ _]
        _ < ε / 2 + ε / 2 := add_lt_add hp₁ hp₂
        _ = ε := add_halves ε
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact hd_lt i j ⟨γ₁⁻¹ * γ₂, htri⟩ hlt
    · exact hij rfl
    · have htri' : h3Dist (natPoint (seq j) (hseq_pos j))
          (h3Act ((γ₂⁻¹ * γ₁ : Γ) : SL2C) (natPoint (seq i) (hseq_pos i))) < ε := by
        rw [← h3Dist_h3Act ((γ₁⁻¹ * γ₂ : Γ) : SL2C), h3Dist_comm]
        have : h3Act ((γ₁⁻¹ * γ₂ : Γ) : SL2C)
            (h3Act ((γ₂⁻¹ * γ₁ : Γ) : SL2C) (natPoint (seq i) (hseq_pos i))) =
            natPoint (seq i) (hseq_pos i) := by
          rw [← h3Act_mul]
          have hmul : ((γ₁⁻¹ * γ₂ : Γ) : SL2C) * ((γ₂⁻¹ * γ₁ : Γ) : SL2C) = 1 := by
            exact_mod_cast (show (γ₁⁻¹ * γ₂) * (γ₂⁻¹ * γ₁) = 1 by group)
          rw [hmul, h3Act_one]
        rwa [this]
      exact hd_lt j i ⟨γ₂⁻¹ * γ₁, htri'⟩ hgt
  -- Uniform lower bound `c₀ ≤ |vertStab Γ| * h3Measure (E k)` via left cosets `Γ ⧸ vertStab Γ`
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (64 / 27 * h3BallDelta (ε / 2) ^ 3)
  have hc₀_pos : 0 < c₀ :=
    ENNReal.ofReal_pos.mpr (by have := h3BallDelta_pos hε2; positivity)
  set M : ℕ := Fintype.card (vertStab Γ)
  have hM_pos : 0 < M := Fintype.card_pos
  haveI : Countable (Γ ⧸ vertStab Γ) := Quotient.countable
  have hcs_surj : Function.Surjective (QuotientGroup.mk : Γ → Γ ⧸ vertStab Γ) :=
    QuotientGroup.mk_surjective
  choose rep hrep using hcs_surj
  have hstab_ball : ∀ (τ : vertStab Γ) (k : ℕ), ((τ : Γ) : SL2C) • B k = B k := by
    intro τ k
    ext p
    simp only [Set.mem_smul_set, B, mem_setOf_eq, smul_h3_def]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hfix : natPoint (seq k) (hseq_pos k) =
          h3Act ((τ : Γ) : SL2C) (natPoint (seq k) (hseq_pos k)) :=
        (τ.2 (seq k) (by exact_mod_cast hseq_pos k)).symm
      rw [hfix, h3Dist_h3Act]
      exact hq
    · intro hp
      refine ⟨h3Act (((τ⁻¹ : vertStab Γ) : Γ) : SL2C) p, ?_, ?_⟩
      · have hfix : natPoint (seq k) (hseq_pos k) =
            h3Act (((τ⁻¹ : vertStab Γ) : Γ) : SL2C) (natPoint (seq k) (hseq_pos k)) :=
          ((τ⁻¹ : vertStab Γ).2 (seq k) (by exact_mod_cast hseq_pos k)).symm
        rw [hfix, h3Dist_h3Act]
        exact hp
      · rw [← h3Act_mul]
        have h1 : ((τ : Γ) : SL2C) * (((τ⁻¹ : vertStab Γ) : Γ) : SL2C) = 1 := by
          exact_mod_cast mul_inv_cancel (τ : Γ)
        rw [h1, h3Act_one]
  have hE_lower : ∀ k : ℕ, c₀ ≤ (M : ℝ≥0∞) * h3Measure (E k) := by
    intro k
    let piece : (Γ ⧸ vertStab Γ) → Set H3 := fun c => (((rep c : SL2C) • B k) ∩ F)
    have hpiece_meas : ∀ c, MeasurableSet (piece c) := fun c =>
      ((measurableEmbedding_h3Act (rep c : SL2C)).measurableSet_image.mpr (hB_meas k)).inter hF_meas
    have hpiece_sub : ∀ c, piece c ⊆ E k := fun c x hx =>
      ⟨Set.mem_iUnion.mpr ⟨rep c, hx.1⟩, hx.2⟩
    have hpiece_disj : Pairwise (Disjoint on piece) := by
      intro c₁ c₂ hc12
      rw [Set.disjoint_iff]
      rintro x ⟨⟨⟨p₁, hp₁, rfl⟩, _⟩, ⟨⟨p₂, hp₂, heq⟩, _⟩⟩
      have hp12 : p₁ = h3Act (((rep c₁)⁻¹ * rep c₂ : Γ) : SL2C) p₂ := by
        change (rep c₁ : SL2C) • p₁ = (rep c₂ : SL2C) • p₂ at heq
        calc p₁ = ((rep c₁ : SL2C)⁻¹ * (rep c₁ : SL2C)) • p₁ := by rw [inv_mul_cancel, one_smul]
          _ = (rep c₁ : SL2C)⁻¹ • ((rep c₁ : SL2C) • p₁) := mul_smul _ _ _
          _ = (rep c₁ : SL2C)⁻¹ • ((rep c₂ : SL2C) • p₂) := by rw [heq]
          _ = (((rep c₁)⁻¹ * rep c₂ : Γ) : SL2C) • p₂ := (mul_smul _ _ _).symm
      have htri : h3Dist (natPoint (seq k) (hseq_pos k))
          (h3Act (((rep c₁)⁻¹ * rep c₂ : Γ) : SL2C) (natPoint (seq k) (hseq_pos k))) < ε := by
        calc h3Dist (natPoint (seq k) (hseq_pos k))
              (h3Act (((rep c₁)⁻¹ * rep c₂ : Γ) : SL2C) (natPoint (seq k) (hseq_pos k)))
            ≤ h3Dist (natPoint (seq k) (hseq_pos k)) p₁ +
                h3Dist p₁ (h3Act (((rep c₁)⁻¹ * rep c₂ : Γ) : SL2C)
                  (natPoint (seq k) (hseq_pos k))) := h3Dist_triangle _ _ _
          _ = h3Dist (natPoint (seq k) (hseq_pos k)) p₁ +
                h3Dist (natPoint (seq k) (hseq_pos k)) p₂ := by
              rw [hp12, h3Dist_h3Act, h3Dist_comm p₂ _]
          _ < ε / 2 + ε / 2 := add_lt_add hp₁ hp₂
          _ = ε := add_halves ε
      have hmem_stab : (rep c₁)⁻¹ * rep c₂ ∈ vertStab Γ := by
        by_contra hnot
        exact (hseq_mem k).2 ⟨hseq_S k, (rep c₁)⁻¹ * rep c₂, hnot, htri⟩
      have hcoset : QuotientGroup.mk (rep c₁) = QuotientGroup.mk (rep c₂) :=
        QuotientGroup.eq.mpr hmem_stab
      rw [hrep c₁, hrep c₂] at hcoset
      exact hc12 hcoset
    -- Cover `B k` by `(c, τ) ↦ B k ∩ ((rep c * τ)⁻¹ • F)`
    have hcover : B k ⊆ ⋃ c : Γ ⧸ vertStab Γ, ⋃ τ : vertStab Γ,
        B k ∩ (((rep c * (τ : Γ) : Γ) : SL2C)⁻¹ • F) := by
      intro p hp
      obtain ⟨γ, hγF⟩ := hF_cov p
      set c := QuotientGroup.mk γ
      have hcos : QuotientGroup.mk (rep c) = QuotientGroup.mk γ := hrep c
      have hτ_mem : (rep c)⁻¹ * γ ∈ vertStab Γ := QuotientGroup.eq.mp hcos
      set τ : vertStab Γ := ⟨(rep c)⁻¹ * γ, hτ_mem⟩
      have hγ_eq : rep c * (τ : Γ) = γ := mul_inv_cancel_left (rep c) γ
      refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨τ, hp, ?_⟩⟩
      rw [hγ_eq]
      refine ⟨h3Act (γ : SL2C) p, hγF, ?_⟩
      change (γ : SL2C)⁻¹ • ((γ : SL2C) • p) = p
      rw [← mul_smul, inv_mul_cancel, one_smul]
    -- Each `(c, τ)` slice is mapped by `rep c * τ` onto `piece c`
    have hslice_eq : ∀ (c : Γ ⧸ vertStab Γ) (τ : vertStab Γ),
        h3Measure (B k ∩ (((rep c * (τ : Γ) : Γ) : SL2C)⁻¹ • F)) = h3Measure (piece c) := by
      intro c τ
      set g : SL2C := ((rep c * (τ : Γ) : Γ) : SL2C)
      have hs_meas : MeasurableSet (B k ∩ (g⁻¹ • F)) :=
        (hB_meas k).inter ((measurableEmbedding_h3Act g⁻¹).measurableSet_image.mpr hF_meas)
      rw [← h3Measure_h3Act g hs_meas]
      congr 1
      have himg : g • (B k ∩ (g⁻¹ • F)) = (g • B k) ∩ F := by
        ext x
        simp only [Set.mem_smul_set, Set.mem_inter_iff]
        constructor
        · rintro ⟨y, ⟨hyB, ⟨z, hzF, rfl⟩⟩, rfl⟩
          refine ⟨⟨g⁻¹ • z, hyB, rfl⟩, ?_⟩
          rw [← mul_smul, mul_inv_cancel, one_smul]; exact hzF
        · rintro ⟨⟨y, hyB, rfl⟩, hxF⟩
          refine ⟨y, ⟨hyB, ⟨g • y, hxF, ?_⟩⟩, rfl⟩
          rw [← mul_smul, inv_mul_cancel, one_smul]
      have hgB : g • B k = (rep c : SL2C) • B k := by
        have hmul : g = (rep c : SL2C) * ((τ : Γ) : SL2C) := rfl
        rw [hmul, mul_smul, hstab_ball τ k]
      rw [himg, hgB]
    have hBk_ge : c₀ ≤ h3Measure (B k) :=
      h3Measure_ball_ge hε2 (by exact_mod_cast hseq_pos k)
    calc c₀ ≤ h3Measure (B k) := hBk_ge
      _ ≤ h3Measure (⋃ c : Γ ⧸ vertStab Γ, ⋃ τ : vertStab Γ,
            B k ∩ (((rep c * (τ : Γ) : Γ) : SL2C)⁻¹ • F)) := measure_mono hcover
      _ ≤ ∑' c : Γ ⧸ vertStab Γ,
            h3Measure (⋃ τ : vertStab Γ, B k ∩ (((rep c * (τ : Γ) : Γ) : SL2C)⁻¹ • F)) :=
          measure_iUnion_le _
      _ ≤ ∑' c : Γ ⧸ vertStab Γ, ∑ τ : vertStab Γ,
            h3Measure (B k ∩ (((rep c * (τ : Γ) : Γ) : SL2C)⁻¹ • F)) := by
          refine ENNReal.tsum_le_tsum fun c => ?_
          simpa using measure_iUnion_fintype_le h3Measure
            (fun τ : vertStab Γ => B k ∩ (((rep c * (τ : Γ) : Γ) : SL2C)⁻¹ • F))
      _ = ∑' c : Γ ⧸ vertStab Γ, (M : ℝ≥0∞) * h3Measure (piece c) := by
          congr 1; funext c
          simp_rw [hslice_eq c, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, M]
      _ = (M : ℝ≥0∞) * ∑' c : Γ ⧸ vertStab Γ, h3Measure (piece c) := ENNReal.tsum_mul_left
      _ = (M : ℝ≥0∞) * h3Measure (⋃ c : Γ ⧸ vertStab Γ, piece c) := by
          rw [measure_iUnion hpiece_disj hpiece_meas]
      _ ≤ (M : ℝ≥0∞) * h3Measure (E k) :=
          mul_le_mul_left' (measure_mono (Set.iUnion_subset hpiece_sub)) _
  -- Sum over `K` disjoint sets `E 0, …, E (K - 1) ⊆ F` to contradict `h3Measure F < ⊤`
  have hsum_le : ∀ K : ℕ, (K : ℝ≥0∞) * c₀ ≤ (M : ℝ≥0∞) * h3Measure F := by
    intro K
    have hdisj_fin : (Finset.range K : Set ℕ).PairwiseDisjoint E :=
      fun i _ j _ hij => hE_disj hij
    calc (K : ℝ≥0∞) * c₀
        = ∑ _k ∈ Finset.range K, c₀ := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range K, (M : ℝ≥0∞) * h3Measure (E k) :=
            Finset.sum_le_sum fun k _ => hE_lower k
      _ = (M : ℝ≥0∞) * ∑ k ∈ Finset.range K, h3Measure (E k) := (Finset.mul_sum _ _ _).symm
      _ = (M : ℝ≥0∞) * h3Measure (⋃ k ∈ Finset.range K, E k) := by
            rw [measure_biUnion_finset hdisj_fin (fun k _ => hE_meas k)]
      _ ≤ (M : ℝ≥0∞) * h3Measure F := by
            refine mul_le_mul_left' (measure_mono ?_) _
            exact Set.iUnion₂_subset fun k _ => Set.inter_subset_right
  have htop_lt : (M : ℝ≥0∞) * h3Measure F < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.natCast_ne_top M).lt_top hF_lt
  have hdiv_lt : ((M : ℝ≥0∞) * h3Measure F) / c₀ < ⊤ :=
    ENNReal.div_lt_top htop_lt.ne hc₀_pos.ne'
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt hdiv_lt.ne
  have hmul_lt : (M : ℝ≥0∞) * h3Measure F < (K : ℝ≥0∞) * c₀ := by
    have hc₀_top : c₀ ≠ ⊤ := ENNReal.ofReal_ne_top
    exact (ENNReal.div_lt_iff (Or.inl hc₀_pos.ne') (Or.inl hc₀_top)).mp hK
  exact absurd (hsum_le K) (not_le.mpr hmul_lt)

/-- **Off-diagonal blowup of Newtonian quotient kernels on primes.** Under thick-end folding on the
primes, any `Γ`-invariant kernel `K : H3 → H3 → ℝ` bounded below by a Newtonian singularity
`c₁ / (h3Dist p q + δ₁) - C₁` (or `c₁ / h3Dist p (γ • q) - C₁` on distinct points, extended by any
real value on the diagonal) becomes arbitrarily large on prime pairs `(p, q)` of arbitrarily large
ratio `q / p > R`, whereas `archProfile (log (q / p)) → 0`. -/
theorem newtonian_quotient_unbounded_on_primes (Γ : Subgroup SL2C)
    (hfold : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 1 < R → ∃ p : ℕ, ∃ hp : p.Prime, ∃ q : ℕ, ∃ hq : q.Prime,
      R < (q : ℝ) / p ∧ ∃ γ : Γ,
        h3Dist (natPoint p hp.pos) (h3Act (γ : SL2C) (natPoint q hq.pos)) < ε)
    {K : H3 → H3 → ℝ} {c₁ C₁ : ℝ} (hc₁ : 0 < c₁)
    (hK_inv : ∀ (γ : Γ) (x y : H3), K x (h3Act (γ : SL2C) y) = K x y)
    (hK_pole : ∀ x y : H3, x ≠ y → c₁ / h3Dist x y - C₁ ≤ K x y)
    (hK_diag_or_off : ∀ (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (γ : Γ),
      p ≠ q → natPoint p hp.pos ≠ h3Act (γ : SL2C) (natPoint q hq.pos)) :
    ∀ (M R : ℝ), 1 < R → ∃ (p q : ℕ) (hp : p.Prime) (hq : q.Prime),
      R < (q : ℝ) / p ∧ M < K (natPoint p hp.pos) (natPoint q hq.pos) := by
  intro M R hR
  set B := max 1 (|M| + |C₁| + 1)
  have hB_pos : 0 < B := by positivity
  set ε := c₁ / B
  have hε_pos : 0 < ε := div_pos hc₁ hB_pos
  obtain ⟨p, hp, q, hq, hrat, γ, hdist⟩ := hfold ε hε_pos R hR
  have hpq : p ≠ q := by
    intro heq; subst heq
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [div_self hp_pos.ne'] at hrat
    linarith
  have hne := hK_diag_or_off p q hp hq γ hpq
  have hd_pos : 0 < h3Dist (natPoint p hp.pos) (h3Act (γ : SL2C) (natPoint q hq.pos)) :=
    lt_of_le_of_ne (h3Dist_nonneg _ _) (Ne.symm ((h3Dist_eq_zero_iff _ _).not.mpr hne))
  refine ⟨p, q, hp, hq, hrat, ?_⟩
  rw [← hK_inv γ]
  have hpole := hK_pole _ _ hne
  have hdiv : B < c₁ / h3Dist (natPoint p hp.pos) (h3Act (γ : SL2C) (natPoint q hq.pos)) := by
    have h1 : c₁ / ε < c₁ / h3Dist (natPoint p hp.pos) (h3Act (γ : SL2C) (natPoint q hq.pos)) :=
      div_lt_div_of_pos_left hc₁ hd_pos hdist
    have h2 : c₁ / ε = B := by simp [ε]; field_simp
    rwa [h2] at h1
  have hMC : M + C₁ < B := by
    have : M + C₁ ≤ |M| + |C₁| := add_le_add (le_abs_self M) (le_abs_self C₁)
    have : |M| + |C₁| + 1 ≤ B := le_max_right _ _
    linarith
  linarith

/-! ### Parabolic cusp harmonic divergence and horospherical zero-mode at `s = 1 / 2` -/

theorem parabolicSL2_pow (ω : ℂ) (k : ℕ) :
    parabolicSL2 ω ^ k = parabolicSL2 ((k : ℂ) * ω) := by
  induction k with
  | zero =>
    refine Subtype.ext <| Matrix.ext fun i j => ?_
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) i j = (parabolicSL2 ((0 : ℕ) * ω)).1 i j
    fin_cases i <;> fin_cases j <;> simp [parabolicSL2]
  | succ k ih =>
    rw [pow_succ, ih]
    refine Subtype.ext <| Matrix.ext fun i j => ?_
    change ((parabolicSL2 ((k : ℂ) * ω)).1 * (parabolicSL2 ω).1) i j =
      (parabolicSL2 (((k + 1 : ℕ) : ℂ) * ω)).1 i j
    fin_cases i <;> fin_cases j <;>
      simp [parabolicSL2, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- **Parabolic cusp harmonic divergence at `s = 1 / 2`.** Every non-zero parabolic translation
`!![1, ω; 0, 1]` generates a divergent cyclic Poincaré series of `G_{1/2}` between any two points on
the vertical geodesic. -/
theorem parabolic_poincare_not_summable_half {ω : ℂ} (hω : ω ≠ 0) {t u : ℝ} (ht : 0 < t)
    (hu : 0 < u) :
    ¬ Summable (fun k : ℕ =>
      hyperbolicGreen (1 / 2) (h3Dist (degPoint t ht) (h3Act (parabolicSL2 ω ^ k) (degPoint u hu)))) := by
  intro hsum
  have hsum_shift : Summable (fun k : ℕ =>
      hyperbolicGreen (1 / 2)
        (h3Dist (degPoint t ht) (h3Act (parabolicSL2 ω ^ (k + 1)) (degPoint u hu)))) :=
    (summable_nat_add_iff 1).mpr hsum
  set C := 1 + (‖ω‖ ^ 2 + (t - u) ^ 2) / (2 * t * u)
  have hC_pos : 0 < C := by positivity
  set c_lo := (2 * Real.pi * Real.sqrt (2 * C))⁻¹
  have hc_lo_pos : 0 < c_lo := by positivity
  -- Lower bound each `k + 1` term by `c_lo / (k + 1)`
  have hterm : ∀ k : ℕ, c_lo * ((k : ℝ) + 1)⁻¹ ≤
      hyperbolicGreen (1 / 2)
        (h3Dist (degPoint t ht) (h3Act (parabolicSL2 ω ^ (k + 1)) (degPoint u hu))) := by
    intro k
    set m : ℕ := k + 1
    have hm_pos : 0 < m := Nat.succ_pos k
    have hm_r : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
    have hp_act : h3Act (parabolicSL2 ω ^ m) (degPoint u hu) = ⟨(m : ℂ) * ω, u, hu⟩ := by
      rw [parabolicSL2_pow]
      have hden : h3Denom (parabolicSL2 ((m : ℂ) * ω)) (degPoint u hu) = 1 := by
        simp [h3Denom, parabolicSL2, degPoint]
      ext
      · rw [h3Act_z, hden]; simp [parabolicSL2, degPoint]
      · rw [h3Act_t, hden]; simp [degPoint]
    set d := h3Dist (degPoint t ht) (h3Act (parabolicSL2 ω ^ m) (degPoint u hu))
    have hd_pos : 0 < d := by
      dsimp only [d]
      rw [h3Dist]
      refine Real.arcosh_pos ?_
      rw [hp_act]
      unfold h3Cosh degPoint
      have hmw : 0 < ‖(0 : ℂ) - (m : ℂ) * ω‖ ^ 2 := by
        rw [zero_sub, norm_neg, norm_mul, Complex.norm_natCast]
        have : 0 < ‖ω‖ := norm_pos_iff.mpr hω
        positivity
      have hdiv : 0 < (‖(0 : ℂ) - (m : ℂ) * ω‖ ^ 2 + (t - u) ^ 2) / (2 * t * u) := by positivity
      linarith
    have hcosh_le : Real.cosh d ≤ C * (m : ℝ) ^ 2 := by
      rw [cosh_h3Dist, hp_act]
      unfold h3Cosh degPoint
      rw [zero_sub, norm_neg, norm_mul, Complex.norm_natCast, mul_pow]
      have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
      simp only [C]
      have h1 : 1 ≤ 1 * (m : ℝ) ^ 2 := by linarith
      have h2 : ((m : ℝ) ^ 2 * ‖ω‖ ^ 2 + (t - u) ^ 2) / (2 * t * u) ≤
          ((‖ω‖ ^ 2 + (t - u) ^ 2) / (2 * t * u)) * (m : ℝ) ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
        nlinarith [sq_nonneg (t - u)]
      linarith
    have hexp_le : Real.exp d ≤ 2 * C * (m : ℝ) ^ 2 := by
      have : Real.exp d < 2 * Real.cosh d := by
        rw [Real.cosh_eq]; linarith [Real.exp_pos (-d)]
      linarith
    have hexp_half : Real.exp (d / 2) ≤ Real.sqrt (2 * C) * m := by
      have hsq : Real.exp (d / 2) ^ 2 = Real.exp d := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hrhs : (Real.sqrt (2 * C) * m) ^ 2 = 2 * C * (m : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      exact le_of_sq_le_sq (by linarith) (by positivity)
    have hsinh_lt : 2 * Real.sinh d ≤ Real.exp d := by
      rw [Real.sinh_eq]; linarith [Real.exp_pos (-d)]
    have hgreen_lo : (2 * Real.pi * Real.exp (d / 2))⁻¹ ≤ hyperbolicGreen (1 / 2) d := by
      unfold hyperbolicGreen
      rw [show -((1 / 2 : ℝ) - 1) * d = d / 2 by ring]
      have hsh_pos : 0 < Real.sinh d := Real.sinh_pos_iff.mpr hd_pos
      have hed : Real.exp d = Real.exp (d / 2) * Real.exp (d / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos, Real.exp_pos (d / 2)]
    calc c_lo * ((k : ℝ) + 1)⁻¹
        = (2 * Real.pi * (Real.sqrt (2 * C) * m))⁻¹ := by
          simp only [c_lo, m]; push_cast; field_simp
      _ ≤ (2 * Real.pi * Real.exp (d / 2))⁻¹ := by
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          exact mul_le_mul_of_nonneg_left hexp_half (by positivity)
      _ ≤ hyperbolicGreen (1 / 2) d := hgreen_lo
  have hharm : Summable (fun k : ℕ => c_lo * ((k : ℝ) + 1)⁻¹) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hterm hsum_shift
  have hharm' : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ)⁻¹) := by
    have := hharm.mul_left c_lo⁻¹
    refine this.congr fun k => ?_
    push_cast; field_simp [hc_lo_pos.ne']
  have hharm0 : Summable (fun k : ℕ => (k : ℝ)⁻¹) :=
    (summable_nat_add_iff 1).mp hharm'
  exact Real.not_summable_natCast_inv hharm0

/-- Horospherical distance `arcosh(1 + (r² + (t - u)²) / (2 t u))` at horizontal offset `r`. -/
def horoDist (t u r : ℝ) : ℝ :=
  Real.arcosh (1 + (r ^ 2 + (t - u) ^ 2) / (2 * t * u))

/-- Exact meromorphic horospherical cusp zero-mode `(min^s * max^{2 - s}) / (2 (s - 1) Λ_area)`. -/
def cuspZeroMode (Λ_area s t u : ℝ) : ℝ :=
  (min t u) ^ s * (max t u) ^ (2 - s) / (2 * (s - 1) * Λ_area)

/-- **Exact horospherical cusp zero-mode integral.** For `s > 1`, `t, u > 0`, and cusp covolume
`Λ_area > 0`, integrating `2π r G_s(horoDist t u r)` over `r ∈ (0, ∞)` yields
`cuspZeroMode Λ_area s t u`. -/
theorem integral_horospherical_green_eq {Λ_area s t u : ℝ} (hΛ : 0 < Λ_area) (hs : 1 < s)
    (ht : 0 < t) (hu : 0 < u) :
    Λ_area⁻¹ * (∫ r in Set.Ioi 0, 2 * Real.pi * r * hyperbolicGreen s (horoDist t u r)) =
      cuspZeroMode Λ_area s t u := by
  set α := s - 1
  have hα : 0 < α := sub_pos.mpr hs
  let F : ℝ → ℝ := fun r => -(t * u / (2 * α)) * Real.exp (-α * horoDist t u r)
  let F' : ℝ → ℝ := fun r => 2 * Real.pi * r * hyperbolicGreen s (horoDist t u r)
  -- Continuity of `F` on `[0, ∞)`
  have hcont_arg : Continuous (fun r : ℝ => 1 + (r ^ 2 + (t - u) ^ 2) / (2 * t * u)) := by fun_prop
  have hge1 : ∀ r : ℝ, 1 ≤ 1 + (r ^ 2 + (t - u) ^ 2) / (2 * t * u) := fun r => by
    have : 0 ≤ (r ^ 2 + (t - u) ^ 2) / (2 * t * u) := by positivity
    linarith
  have hcont_horo : Continuous (horoDist t u) :=
    Real.continuousOn_arcosh.comp_continuous hcont_arg hge1
  have hcont_F : Continuous F := by
    unfold F
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcont_horo))
  -- Derivative on `(0, ∞)`
  have hderiv : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' r) r := by
    intro r hr
    rw [Set.mem_Ioi] at hr
    set C := 1 + (r ^ 2 + (t - u) ^ 2) / (2 * t * u)
    have hC1 : 1 < C := by
      simp only [C]
      have : 0 < (r ^ 2 + (t - u) ^ 2) / (2 * t * u) := by positivity
      linarith
    have hd_arg : HasDerivAt (fun x : ℝ => 1 + (x ^ 2 + (t - u) ^ 2) / (2 * t * u))
        (r / (t * u)) r := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + (t - u) ^ 2) (2 * r) r := by
        simpa using (hasDerivAt_pow 2 r).add_const ((t - u) ^ 2)
      have h2 := (h1.div_const (2 * t * u)).const_add 1
      refine h2.congr_deriv ?_
      field_simp
    have hd_horo : HasDerivAt (horoDist t u) ((Real.sqrt (C ^ 2 - 1))⁻¹ * (r / (t * u))) r :=
      (Real.hasDerivAt_arcosh hC1).comp r hd_arg
    have hd_exp : HasDerivAt (fun x => Real.exp (-α * horoDist t u x))
        (Real.exp (-α * horoDist t u r) * (-α * ((Real.sqrt (C ^ 2 - 1))⁻¹ * (r / (t * u))))) r :=
      (hd_horo.const_mul (-α)).exp
    have hd_F := hd_exp.const_mul (-(t * u / (2 * α)))
    refine hd_F.congr_deriv ?_
    have hsinh : Real.sinh (horoDist t u r) = Real.sqrt (C ^ 2 - 1) :=
      Real.sinh_arcosh hC1.le
    have hsinh_ne : Real.sqrt (C ^ 2 - 1) ≠ 0 := by
      refine (Real.sqrt_pos.mpr ?_).ne'
      nlinarith
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hα_ne : α ≠ 0 := hα.ne'
    simp only [F', hyperbolicGreen]
    rw [show -(s - 1) * horoDist t u r = -α * horoDist t u r by simp [α], hsinh]
    field_simp
    ring
  -- Nonnegativity of `F'` on `(0, ∞)`
  have hnonneg : ∀ r ∈ Set.Ioi (0 : ℝ), 0 ≤ F' r := by
    intro r hr
    rw [Set.mem_Ioi] at hr
    have hd_pos : 0 < horoDist t u r := by
      unfold horoDist
      refine Real.arcosh_pos ?_
      have : 0 < (r ^ 2 + (t - u) ^ 2) / (2 * t * u) := by positivity
      linarith
    have hsh_pos : 0 < Real.sinh (horoDist t u r) := Real.sinh_pos_iff.mpr hd_pos
    simp only [F', hyperbolicGreen]
    positivity
  -- Limit `F r → 0` as `r → +∞`
  have htend_F : Tendsto F atTop (𝓝 0) := by
    have htend_horo : Tendsto (horoDist t u) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      filter_upwards [eventually_ge_atTop (Real.sqrt (2 * t * u * Real.cosh (max 0 b)) + 1)] with r hr
      have hr0 : 0 ≤ Real.sqrt (2 * t * u * Real.cosh (max 0 b)) := Real.sqrt_nonneg _
      have hr_sq : 2 * t * u * Real.cosh (max 0 b) ≤ r ^ 2 := by
        calc 2 * t * u * Real.cosh (max 0 b)
            = Real.sqrt (2 * t * u * Real.cosh (max 0 b)) ^ 2 :=
              (Real.sq_sqrt (by positivity)).symm
          _ ≤ r ^ 2 := pow_le_pow_left₀ hr0 (by linarith) 2
      have hC_ge : Real.cosh (max 0 b) ≤ 1 + (r ^ 2 + (t - u) ^ 2) / (2 * t * u) := by
        have hdiv : Real.cosh (max 0 b) ≤ (r ^ 2 + (t - u) ^ 2) / (2 * t * u) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (t - u)]
        linarith
      calc b ≤ max 0 b := le_max_right 0 b
        _ = Real.arcosh (Real.cosh (max 0 b)) := (Real.arcosh_cosh (le_max_left 0 b)).symm
        _ ≤ horoDist t u r :=
            (Real.arcosh_le_arcosh (Real.cosh_pos _) (by linarith [hge1 r])).mpr hC_ge
    have htend_neg : Tendsto (fun r => -α * horoDist t u r) atTop atBot := by
      have h := tendsto_neg_atTop_atBot.comp (htend_horo.const_mul_atTop hα)
      exact h.congr fun r => by simp [neg_mul]
    have htend_exp : Tendsto (fun r => Real.exp (-α * horoDist t u r)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp htend_neg
    simpa [F] using htend_exp.const_mul (-(t * u / (2 * α)))
  -- Apply FTC on `(0, ∞)`
  have hint := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg
    hcont_F.continuousWithinAt hderiv hnonneg htend_F
  -- Evaluate `-F 0 = min(t, u)^s * max(t, u)^{2 - s} / (2 * (s - 1))`
  have hhoro0 : horoDist t u 0 = |Real.log u - Real.log t| := by
    have h1 := h3Dist_degPoint ht hu
    simp only [h3Dist, h3Cosh, degPoint, sub_self, norm_zero, zero_pow two_ne_zero, zero_add] at h1
    simpa [horoDist] using h1
  have hF0 : 0 - F 0 = (min t u) ^ s * (max t u) ^ (2 - s) / (2 * α) := by
    simp only [F, zero_sub, neg_mul, neg_neg, hhoro0]
    have hmin_pos : 0 < min t u := lt_min ht hu
    have hmax_pos : 0 < max t u := lt_of_lt_of_le ht (le_max_left t u)
    have hprod : t * u = min t u * max t u := (min_mul_max t u).symm
    have habs : |Real.log u - Real.log t| = Real.log (max t u) - Real.log (min t u) := by
      rcases le_total t u with htu | hut
      · rw [min_eq_left htu, max_eq_right htu,
          abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log ht htu))]
      · rw [min_eq_right hut, max_eq_left hut, abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hu hut))]
    rw [hprod, habs, Real.rpow_def_of_pos hmin_pos, Real.rpow_def_of_pos hmax_pos]
    conv_lhs =>
      rw [show min t u * max t u = Real.exp (Real.log (min t u)) * Real.exp (Real.log (max t u)) by
        rw [Real.exp_log hmin_pos, Real.exp_log hmax_pos]]
    rw [div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
    congr 2
    simp only [α]; ring
  rw [hint, hF0]
  unfold cuspZeroMode
  simp only [α]
  field_simp

/-- At the critical parameter `s = 1 / 2`, the meromorphically continued cusp zero-mode equals
`-min(t, u)^{1/2} * max(t, u)^{3/2} / Λ_area`. -/
theorem cuspZeroMode_at_half (Λ_area t u : ℝ) :
    cuspZeroMode Λ_area (1 / 2) t u =
      -((min t u) ^ (1 / 2 : ℝ) * (max t u) ^ (3 / 2 : ℝ)) / Λ_area := by
  unfold cuspZeroMode
  rw [show (2 : ℝ) - 1 / 2 = 3 / 2 by ring]
  ring

theorem cuspZeroMode_at_half_diag {Λ_area : ℝ} (n : ℕ) :
    cuspZeroMode Λ_area (1 / 2) n n = -((n : ℝ) ^ 2) / Λ_area := by
  rw [cuspZeroMode_at_half, min_self, max_self,
    ← Real.rpow_add_of_nonneg (Nat.cast_nonneg n) (by positivity) (by positivity),
    show (1 / 2 : ℝ) + 3 / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- On the diagonal `(n, n)`, the cusp zero-mode at `s = 1 / 2` dominates `log n` (`n² / log n → +∞`). -/
theorem tendsto_abs_cuspZeroMode_diag_div_log {Λ_area : ℝ} (hΛ : 0 < Λ_area) :
    Tendsto (fun n : ℕ => |cuspZeroMode Λ_area (1 / 2) n n| / Real.log n) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.const_mul_atTop (inv_pos.mpr hΛ))
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlog_le : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn_pos).trans (by linarith)
  rw [cuspZeroMode_at_half_diag, abs_div, abs_neg, abs_of_nonneg (sq_nonneg _),
    abs_of_pos hΛ, div_div]
  rw [le_div_iff₀ (mul_pos hΛ hlog_pos)]
  calc Λ_area⁻¹ * (n : ℝ) * (Λ_area * Real.log n)
      = (n : ℝ) * Real.log n := by field_simp
    _ ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left hlog_le hn_pos.le
    _ = (n : ℝ) ^ 2 := (sq _).symm

/-! ## Section 3. Pure trivial-zero jet Cauchy determinant and causal Taylor-jet Hilbert bundle -/

/-- Pure trivial-zero jet kernel `min(m, n)³ / (max(m, n)² - min(m, n)²)`. -/
def jetKernel (m n : ℕ) : ℝ :=
  min (m : ℝ) n ^ 3 / (max (m : ℝ) n ^ 2 - min (m : ℝ) n ^ 2)

/-- Pure trivial-zero jet profile `e^{-5d / 2} / (1 - e^{-2d})`. -/
def jetProfile (d : ℝ) : ℝ :=
  Real.exp (-5 * d / 2) / (1 - Real.exp (-2 * d))

/-- **Cusp–jet decomposition of `archKernel`.** Off the diagonal, the archimedean Frobenius splits
into the `𝔽₁`-cusp `min(m, n)` plus the pure trivial-zero jet kernel `jetKernel m n`. -/
theorem archKernel_eq_min_add_jetKernel {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    archKernel m n = min (m : ℝ) n + jetKernel m n := by
  set a := min (m : ℝ) n
  set b := max (m : ℝ) n
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hab : a < b := min_lt_max.mpr (by exact_mod_cast hmn)
  have ha0 : 0 < a := lt_min hm' hn'
  have hb0 : 0 < b := ha0.trans hab
  have hden : b ^ 2 - a ^ 2 ≠ 0 := by nlinarith
  have hden1 : 1 - (a / b) ^ 2 ≠ 0 := by
    intro h0
    have : a ^ 2 = b ^ 2 := by field_simp at h0; linarith
    nlinarith
  unfold archKernel jetKernel
  change a / (1 - (a / b) ^ 2) = a + a ^ 3 / (b ^ 2 - a ^ 2)
  field_simp
  ring

theorem hasSum_jetProfile {d : ℝ} (hd : 0 < d) :
    HasSum (fun k : ℕ => Real.exp (-(2 * ((k : ℝ) + 1) + 1 / 2) * d)) (jetProfile d) := by
  have hq0 : 0 ≤ Real.exp (-2 * d) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * d) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (-5 * d / 2))
  have hf : (fun k : ℕ => Real.exp (-(2 * ((k : ℝ) + 1) + 1 / 2) * d)) =
      fun k : ℕ => Real.exp (-5 * d / 2) * Real.exp (-2 * d) ^ k := by
    funext k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  rw [hf, show jetProfile d = Real.exp (-5 * d / 2) * (1 - Real.exp (-2 * d))⁻¹ from
    div_eq_mul_inv _ _]
  exact h

theorem jetKernel_eq_sqrt_mul_jetProfile {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    jetKernel m n = Real.sqrt ((m : ℝ) * n) * jetProfile |Real.log n - Real.log m| := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set d := |Real.log n - Real.log m|
  have hexp : Real.exp (-2 * d) = (min (m : ℝ) n / max (m : ℝ) n) ^ 2 := by
    simpa [d, abs_sub_comm] using exp_neg_two_abs_log_sub hm' hn'
  have harch := archKernel_eq hm hn hmn
  have hsplit := archKernel_eq_min_add_jetKernel hm hn hmn
  have hmin : min (m : ℝ) n = Real.sqrt ((m : ℝ) * n) * Real.exp (-d / 2) := by
    simpa [d, abs_sub_comm, mul_comm] using min_eq_sqrt_mul_exp hm' hn'
  have hden : 1 - Real.exp (-2 * d) ≠ 0 := by
    refine one_sub_exp_neg_two_mul_ne_zero ?_
    rw [abs_ne_zero, sub_ne_zero]
    intro heq
    exact hmn (by exact_mod_cast (Real.log_injOn_pos hn' hm' heq).symm)
  have hjet : jetProfile d = archProfile d - Real.exp (-d / 2) := by
    unfold jetProfile archProfile
    have he5 : Real.exp (-5 * d / 2) = Real.exp (-d / 2) * Real.exp (-2 * d) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he5]
    set u := Real.exp (-2 * d)
    have hu : 1 - u ≠ 0 := hden
    field_simp [hu]
    ring
  rw [hjet, mul_sub, ← harch, ← hmin, hsplit]
  ring

theorem jetKernel_of_lt {m n : ℕ} (hmn : m < n) :
    jetKernel m n = (m : ℝ) ^ 3 * ((n : ℝ) ^ 2 - (m : ℝ) ^ 2)⁻¹ := by
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  rw [jetKernel, min_eq_left hmn'.le, max_eq_right hmn'.le, div_eq_mul_inv]

/-- **Exact Cauchy determinant of every ordered pure-jet block.** -/
theorem det_jetBlock_eq {r : ℕ} (m n : Fin r → ℕ) (hlt : ∀ i j, m i < n j) :
    (Matrix.of fun i j => jetKernel (m i) (n j)).det =
      (∏ i, (m i : ℝ) ^ 3) *
        (HTGeometry.cauchyMatrix (fun i => -((m i : ℝ) ^ 2)) (fun j => (n j : ℝ) ^ 2)).det := by
  have hfac : (Matrix.of fun i j => jetKernel (m i) (n j)) =
      Matrix.diagonal (fun i => (m i : ℝ) ^ 3) *
        HTGeometry.cauchyMatrix (fun i => -((m i : ℝ) ^ 2)) (fun j => (n j : ℝ) ^ 2) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.of_apply, jetKernel_of_lt (hlt i j),
      HTGeometry.cauchyMatrix_apply]
    ring
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal]

/-- Every ordered square block of the pure trivial-zero jet kernel is nonsingular. -/
theorem det_jetBlock_ne_zero_of_lt {r : ℕ} {m n : Fin r → ℕ} (hm : ∀ i, 0 < m i)
    (hmi : Function.Injective m) (hni : Function.Injective n) (hlt : ∀ i j, m i < n j) :
    (Matrix.of fun i j => jetKernel (m i) (n j)).det ≠ 0 := by
  rw [det_jetBlock_eq m n hlt]
  set x : Fin r → ℝ := fun i => -((m i : ℝ) ^ 2)
  set y : Fin r → ℝ := fun j => (n j : ℝ) ^ 2
  have hpos : ∀ i j, 0 < x i + y j := by
    intro i j
    have h1 : (m i : ℝ) < n j := by exact_mod_cast hlt i j
    have h0 : (0 : ℝ) < m i := by exact_mod_cast hm i
    simp only [x, y]; nlinarith
  have hcd := HTGeometry.det_cauchyMatrix x y fun i j => (hpos i j).ne'
  have hprod : ∏ i, ∏ j ∈ Finset.Ioi i, ((x i - x j) * (y i - y j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_Ioi.mp hj).ne
    refine mul_ne_zero ?_ ?_
    · simp only [x]
      intro h
      have hsq : (m i : ℝ) ^ 2 = (m j : ℝ) ^ 2 := by linarith
      have heq := (sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp hsq
      exact hij (hmi (by exact_mod_cast heq))
    · simp only [y]
      intro h
      have hsq : (n i : ℝ) ^ 2 = (n j : ℝ) ^ 2 := by linarith
      have heq := (sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp hsq
      exact hij (hni (by exact_mod_cast heq))
  have hc : (HTGeometry.cauchyMatrix x y).det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hcd; exact hprod hcd.symm
  refine mul_ne_zero ?_ hc
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero 3 (by exact_mod_cast (hm i).ne')

/-- **Pure trivial-zero jets have infinite rank on coprime primes.** Even after removing the
`𝔽₁`-cusp `min(p, q)`, no finite-rank kernel agrees with `jetKernel` on distinct primes. -/
theorem not_finiteRank_jetKernel_on_coprime {r' : ℕ} (u v : Fin r' → ℕ → ℝ) :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → jetKernel p q = ∑ k, u k p * v k q := by
  intro h
  set r := r' + 1
  set P : ℕ → ℕ := Nat.nth Nat.Prime
  have hPmono : StrictMono P := Nat.nth_strictMono Nat.infinite_setOf_prime
  have hPprime : ∀ k, (P k).Prime := Nat.prime_nth_prime
  set m : Fin r → ℕ := fun i => P i
  set n : Fin r → ℕ := fun j => P (r + j)
  have hlt : ∀ i j, m i < n j := fun i j => hPmono (by have := i.isLt; omega)
  have hdet := det_jetBlock_ne_zero_of_lt (fun i => (hPprime _).pos)
    (fun i j hij => Fin.ext (hPmono.injective hij))
    (fun i j hij => by have := hPmono.injective hij; exact Fin.ext (by omega)) hlt
  have hfac : (Matrix.of fun i j => jetKernel (m i) (n j)) =
      (Matrix.of fun (i : Fin r) (k : Fin r') => u k (m i)) *
        (Matrix.of fun (k : Fin r') (j : Fin r) => v k (n j)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, h _ _ (hPprime _) (hPprime _) (hlt i j).ne]
    rfl
  have hrank : (Matrix.of fun i j => jetKernel (m i) (n j)).rank = r := by
    rw [Matrix.rank_of_isUnit _
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)), Fintype.card_fin]
  have hle : (Matrix.of fun i j => jetKernel (m i) (n j)).rank ≤ r' := by
    rw [hfac]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_width _).trans (by simp))
  omega

/-- Subtracting the `𝔽₁`-cusp `min(p, q)` from `frobeniusIntersection p q` leaves infinite rank on
distinct primes. -/
theorem not_finiteRank_frobeniusSubCusp_on_coprime {r' : ℕ} (u v : Fin r' → ℕ → ℝ) :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      frobeniusIntersection p q - min (p : ℝ) q = ∑ k, u k p * v k q := by
  intro h
  refine not_finiteRank_jetKernel_on_coprime u v fun p q hp hq hpq => ?_
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hfrob := frobeniusIntersection_of_coprime hp.one_lt hq.one_lt hcop
  have hsplit := archKernel_eq_min_add_jetKernel hp.pos hq.pos hpq
  linarith [h p q hp hq hpq]

/-! ### Causal Taylor-jet Hilbert bundle on `L²(0, ∞)` -/

/-- Causal monomial jet wave `√(4k + 1) · 1_{(0, a]}(x) · (x / a)^{2k}` on `(0, ∞)`. -/
def causalJetWave (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (Set.Ioc 0 a).indicator (fun u => Real.sqrt (4 * (k : ℝ) + 1) * (u / a) ^ (2 * k)) x

/-- Multiplicative dilation covariance of `causalJetWave`: scaling `x ↦ x / c` (`c > 0`) shifts the
cutoff `a` to `c * a`. -/
theorem causalJetWave_dilate {c a : ℝ} (hc : 0 < c) (k : ℕ) (x : ℝ) :
    causalJetWave a k (x / c) = causalJetWave (c * a) k x := by
  unfold causalJetWave
  by_cases hx : x ∈ Set.Ioc 0 (c * a)
  · have hxc : x / c ∈ Set.Ioc 0 a := by
      rw [Set.mem_Ioc] at hx ⊢
      exact ⟨div_pos hx.1 hc, (div_le_iff₀ hc).mpr (by linarith [hx.2])⟩
    rw [indicator_of_mem hxc, indicator_of_mem hx]
    congr 2
    rw [div_div, mul_comm c a]
  · have hxc : x / c ∉ Set.Ioc 0 a := by
      intro hmem
      apply hx
      rw [Set.mem_Ioc] at hmem ⊢
      exact ⟨(div_pos_iff_of_pos_right hc).mp hmem.1,
        by linarith [(div_le_iff₀ hc).mp hmem.2]⟩
    rw [indicator_of_notMem hxc, indicator_of_notMem hx]

/-- **Exact causal Taylor-jet Gram identity.** On `L²(0, ∞)`, the inner product of the mode-`k`
causal waves at cutoffs `a, b > 0` equals `min(a, b) * (min(a, b) / max(a, b))^{2k}`: mode `0`
carries the `𝔽₁`-cusp `min(a, b)`, and modes `k ≥ 1` carry the trivial-zero jets. -/
theorem integral_causalJetWave_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    (∫ x in Set.Ioi 0, causalJetWave a k x * causalJetWave b k x) =
      min a b * (min a b / max a b) ^ (2 * k) := by
  set m := min a b
  set M := max a b
  have hm : 0 < m := lt_min ha hb
  have hprod_ab : a * b = m * M := (min_mul_max a b).symm
  have hfun : (fun x => causalJetWave a k x * causalJetWave b k x) =
      (Set.Ioc 0 m).indicator (fun x => (4 * (k : ℝ) + 1) * x ^ (4 * k) / (a * b) ^ (2 * k)) := by
    funext x
    simp only [causalJetWave]
    rw [← Set.inter_indicator_mul, Set.Ioc_inter_Ioc, max_self]
    refine congrFun (Set.indicator_congr fun u _ => ?_) x
    have hsq : Real.sqrt (4 * (k : ℝ) + 1) * Real.sqrt (4 * (k : ℝ) + 1) = 4 * (k : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    calc (Real.sqrt (4 * (k : ℝ) + 1) * (u / a) ^ (2 * k)) *
            (Real.sqrt (4 * (k : ℝ) + 1) * (u / b) ^ (2 * k))
        = (Real.sqrt (4 * (k : ℝ) + 1) * Real.sqrt (4 * (k : ℝ) + 1)) *
            ((u / a) ^ (2 * k) * (u / b) ^ (2 * k)) := by ring
      _ = (4 * (k : ℝ) + 1) * (u ^ (2 * k) * u ^ (2 * k) / (a * b) ^ (2 * k)) := by
          rw [hsq, div_pow, div_pow, mul_pow, div_mul_div_comm]
      _ = (4 * (k : ℝ) + 1) * u ^ (4 * k) / (a * b) ^ (2 * k) := by
          rw [← pow_add, show 2 * k + 2 * k = 4 * k by omega, mul_div_assoc]
  rw [hfun, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le hm.le]
  -- Evaluate `∫ u in 0..m, (4k + 1) * u^{4k} / (a * b)^{2k}` via FTC
  let G : ℝ → ℝ := fun u => u ^ (4 * k + 1) / (a * b) ^ (2 * k)
  have hderiv : ∀ u ∈ Set.uIcc 0 m,
      HasDerivAt G ((4 * (k : ℝ) + 1) * u ^ (4 * k) / (a * b) ^ (2 * k)) u := by
    intro u _
    have h1 := (hasDerivAt_pow (4 * k + 1) u).div_const ((a * b) ^ (2 * k))
    refine h1.congr_deriv ?_
    push_cast
    rfl
  have hint_cont : IntervalIntegrable
      (fun u => (4 * (k : ℝ) + 1) * u ^ (4 * k) / (a * b) ^ (2 * k)) volume 0 m :=
    (by fun_prop : Continuous _).intervalIntegrable 0 m
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_cont]
  simp only [G, zero_pow (Nat.succ_ne_zero _), zero_div, sub_zero, hprod_ab, mul_pow, div_pow]
  have hm_ne : m ^ (2 * k) ≠ 0 := pow_ne_zero _ hm.ne'
  have hM_pos : 0 < M := hm.trans_le min_le_max
  have hM_ne : M ^ (2 * k) ≠ 0 := pow_ne_zero _ hM_pos.ne'
  rw [show 4 * k + 1 = 2 * k + 2 * k + 1 by omega, pow_succ, pow_add]
  field_simp

theorem integral_causalJetWave_sq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (∫ x in Set.Ioi 0, causalJetWave a k x ^ 2) = a := by
  have h := integral_causalJetWave_mul ha ha k
  simp only [sq, min_self, max_self, div_self ha.ne', one_pow, mul_one] at h ⊢
  exact h

/-- Damped pure trivial-zero jet kernel `dampedFrobenius r m n - min(m, n)` (`k ≥ 1` modes). -/
def dampedJet (r : ℝ) (m n : ℕ) : ℝ :=
  dampedFrobenius r m n - min (m : ℝ) n

/-- **Gram realization of `dampedFrobenius` on `L²((0, ∞)) ⊗ ℓ²(ℕ)`.** -/
theorem hasSum_dampedFrobenius_gram {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    HasSum (fun k : ℕ =>
      ∫ x in Set.Ioi 0, (r ^ k * causalJetWave m k x) * (r ^ k * causalJetWave n k x))
      (dampedFrobenius r m n) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set d := Real.log m - Real.log n
  have hterm : ∀ k : ℕ,
      (∫ x in Set.Ioi 0, (r ^ k * causalJetWave m k x) * (r ^ k * causalJetWave n k x)) =
        Real.sqrt ((m : ℝ) * n) * (r ^ (2 * k) * Real.exp (-(2 * k + 1 / 2) * |d|)) := by
    intro k
    have hpull : (fun x => (r ^ k * causalJetWave m k x) * (r ^ k * causalJetWave n k x)) =
        fun x => r ^ (2 * k) * (causalJetWave m k x * causalJetWave n k x) := by
      funext x; rw [pow_mul, sq]; ring
    rw [hpull, MeasureTheory.integral_const_mul, integral_causalJetWave_mul hm' hn' k]
    have hmin : min (m : ℝ) n = Real.sqrt ((m : ℝ) * n) * Real.exp (-|d| / 2) := by
      simpa [d, mul_comm] using min_eq_sqrt_mul_exp hm' hn'
    have hrat : (min (m : ℝ) n / max (m : ℝ) n) ^ (2 * k) = Real.exp (-2 * (k : ℝ) * |d|) := by
      rw [pow_mul, ← exp_neg_two_abs_log_sub hm' hn', ← Real.exp_nat_mul]
      congr 1; simp only [d]; ring
    rw [hrat, hmin]
    calc r ^ (2 * k) * (Real.sqrt ((m : ℝ) * n) * Real.exp (-|d| / 2) *
            Real.exp (-2 * (k : ℝ) * |d|))
        = Real.sqrt ((m : ℝ) * n) * (r ^ (2 * k) *
            (Real.exp (-|d| / 2) * Real.exp (-2 * (k : ℝ) * |d|))) := by ring
      _ = Real.sqrt ((m : ℝ) * n) * (r ^ (2 * k) * Real.exp (-(2 * k + 1 / 2) * |d|)) := by
          rw [← Real.exp_add]; congr 3; ring
  simp_rw [hterm]
  exact (hasSum_archDamped hr0 hr1 d).mul_left (Real.sqrt ((m : ℝ) * n))

/-- **Gram realization of `dampedJet` on the `k ≥ 1` causal modes.** -/
theorem hasSum_dampedJet_gram {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    HasSum (fun k : ℕ =>
      ∫ x in Set.Ioi 0, (r ^ (k + 1) * causalJetWave m (k + 1) x) *
        (r ^ (k + 1) * causalJetWave n (k + 1) x))
      (dampedJet r m n) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfull := hasSum_dampedFrobenius_gram hr0 hr1 hm hn
  have h0 : (∫ x in Set.Ioi (0 : ℝ), (r ^ 0 * causalJetWave m 0 x) * (r ^ 0 * causalJetWave n 0 x)) =
      min (m : ℝ) n := by
    simp only [pow_zero, one_mul]
    simpa using integral_causalJetWave_mul hm' hn' 0
  have heq : dampedFrobenius r m n = dampedJet r m n +
      ∑ i ∈ Finset.range 1, ∫ x in Set.Ioi (0 : ℝ),
        (r ^ i * causalJetWave m i x) * (r ^ i * causalJetWave n i x) := by
    rw [Finset.sum_range_one, h0, dampedJet, sub_add_cancel]
  rw [heq] at hfull
  exact (hasSum_nat_add_iff 1).mpr hfull

/-- **Positive semidefiniteness of the damped pure-jet kernel `dampedJet`.** -/
theorem dampedJet_posSemidef {ι : Type*} (s : Finset ι) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {n : ι → ℕ} (hn : ∀ i ∈ s, 0 < n i) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * dampedJet r (n i) (n j) := by
  classical
  let f : ℕ → ι → ι → ℝ := fun k i j =>
    if i ∈ s ∧ j ∈ s then
      c i * c j * ∫ x in Set.Ioi 0,
        (r ^ (k + 1) * causalJetWave (n i) (k + 1) x) *
        (r ^ (k + 1) * causalJetWave (n j) (k + 1) x)
    else 0
  have hsum : ∀ i ∈ s, ∀ j ∈ s, Summable (fun k => f k i j) := by
    intro i hi j hj
    have := (hasSum_dampedJet_gram hr0 hr1 (hn i hi) (hn j hj)).mul_left (c i * c j)
    refine this.summable.congr fun k => ?_
    simp [f, hi, hj]
  have hrow : ∀ i ∈ s, ∀ j ∈ s, c i * c j * dampedJet r (n i) (n j) = ∑' k, f k i j := by
    intro i hi j hj
    have := (hasSum_dampedJet_gram hr0 hr1 (hn i hi) (hn j hj)).mul_left (c i * c j)
    rw [← this.tsum_eq]
    exact tsum_congr fun k => by simp [f, hi, hj]
  have hrewrite : ∑ i ∈ s, ∑ j ∈ s, c i * c j * dampedJet r (n i) (n j) =
      ∑' k, ∑ i ∈ s, ∑ j ∈ s, f k i j := by
    calc ∑ i ∈ s, ∑ j ∈ s, c i * c j * dampedJet r (n i) (n j)
        = ∑ i ∈ s, ∑ j ∈ s, ∑' k, f k i j :=
          Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hrow i hi j hj
      _ = ∑ i ∈ s, ∑' k, ∑ j ∈ s, f k i j :=
          Finset.sum_congr rfl fun i hi => (Summable.tsum_finsetSum fun j hj => hsum i hi j hj).symm
      _ = ∑' k, ∑ i ∈ s, ∑ j ∈ s, f k i j :=
          (Summable.tsum_finsetSum fun i hi => summable_sum fun j hj => hsum i hi j hj).symm
  rw [hrewrite]
  refine tsum_nonneg fun k => ?_
  -- Each mode `k + 1` is `r^{2(k+1)}` times an `L²(0, ∞)` square
  have hint_prod : ∀ i ∈ s, ∀ j ∈ s,
      IntegrableOn (fun x => (r ^ (k + 1) * causalJetWave (n i) (k + 1) x) *
        (r ^ (k + 1) * causalJetWave (n j) (k + 1) x)) (Set.Ioi 0) := by
    intro i _ j _
    have hcont : Continuous (fun u : ℝ =>
        (r ^ (k + 1) * (Real.sqrt (4 * ((k + 1 : ℕ) : ℝ) + 1) * (u / n i) ^ (2 * (k + 1)))) *
        (r ^ (k + 1) * (Real.sqrt (4 * ((k + 1 : ℕ) : ℝ) + 1) * (u / n j) ^ (2 * (k + 1))))) := by
      fun_prop
    have hon : IntegrableOn (fun x => (r ^ (k + 1) * causalJetWave (n i) (k + 1) x) *
        (r ^ (k + 1) * causalJetWave (n j) (k + 1) x)) (Set.Ioc 0 (min (n i : ℝ) (n j : ℝ))) := by
      refine hcont.integrableOn_Ioc.congr_fun (fun x hx => ?_) measurableSet_Ioc
      have hxi : x ∈ Set.Ioc 0 (n i : ℝ) := ⟨hx.1, hx.2.trans (min_le_left _ _)⟩
      have hxj : x ∈ Set.Ioc 0 (n j : ℝ) := ⟨hx.1, hx.2.trans (min_le_right _ _)⟩
      simp [causalJetWave, indicator_of_mem hxi, indicator_of_mem hxj]
    have heq_ind : (fun x => (r ^ (k + 1) * causalJetWave (n i) (k + 1) x) *
        (r ^ (k + 1) * causalJetWave (n j) (k + 1) x)) =
        (Set.Ioc 0 (min (n i : ℝ) (n j : ℝ))).indicator (fun x =>
          (r ^ (k + 1) * causalJetWave (n i) (k + 1) x) *
          (r ^ (k + 1) * causalJetWave (n j) (k + 1) x)) := by
      funext x
      by_cases hx : x ∈ Set.Ioc 0 (min (n i : ℝ) (n j : ℝ))
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        rcases not_and_or.mp hx with hx0 | hxmin
        · have hni : x ∉ Set.Ioc 0 (n i : ℝ) := fun h => hx0 h.1
          simp [causalJetWave, indicator_of_notMem hni]
        · rw [not_le, min_lt_iff] at hxmin
          rcases hxmin with hi_lt | hj_lt
          · have hni : x ∉ Set.Ioc 0 (n i : ℝ) := fun h => not_lt_of_ge h.2 hi_lt
            simp [causalJetWave, indicator_of_notMem hni]
          · have hnj : x ∉ Set.Ioc 0 (n j : ℝ) := fun h => not_lt_of_ge h.2 hj_lt
            simp [causalJetWave, indicator_of_notMem hnj]
    rw [heq_ind]
    exact (hon.integrable_indicator measurableSet_Ioc).integrableOn
  have hmode_sq : ∑ i ∈ s, ∑ j ∈ s, f k i j =
      ∫ x in Set.Ioi 0, (∑ i ∈ s, c i * (r ^ (k + 1) * causalJetWave (n i) (k + 1) x)) ^ 2 := by
    have hsq_exp : ∀ x, (∑ i ∈ s, c i * (r ^ (k + 1) * causalJetWave (n i) (k + 1) x)) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, c i * c j *
          ((r ^ (k + 1) * causalJetWave (n i) (k + 1) x) *
           (r ^ (k + 1) * causalJetWave (n j) (k + 1) x)) := by
      intro x
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hsq_exp]
    rw [MeasureTheory.integral_finsetSum s fun i hi =>
      integrable_finsetSum s fun j hj => (hint_prod i hi j hj).const_mul _]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_finsetSum s fun j hj => (hint_prod i hi j hj).const_mul _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [MeasureTheory.integral_const_mul]
    simp [f, hi, hj]
  rw [hmode_sq]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun x _ => sq_nonneg _

/-- Off the diagonal, `dampedJet r m n → jetKernel m n` as `r → 1`. -/
theorem tendsto_dampedJet_of_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Tendsto (fun r => dampedJet r m n) (𝓝 1) (𝓝 (jetKernel m n)) := by
  have h := (tendsto_dampedFrobenius hm hn hmn).sub_const (min (m : ℝ) n)
  rwa [archKernel_eq_min_add_jetKernel hm hn hmn, add_sub_cancel_left] at h

/-- On the diagonal, `dampedJet r n n = n r² / (1 - r²) → +∞` as `r → 1⁻`. -/
theorem tendsto_dampedJet_diag {n : ℕ} (hn : 0 < n) :
    Tendsto (fun r => dampedJet r n n) (𝓝[<] 1) atTop := by
  have h := tendsto_atTop_add_const_right (𝓝[<] (1 : ℝ)) (-(n : ℝ))
    (tendsto_dampedFrobenius_diag hn)
  refine h.congr fun r => ?_
  simp [dampedJet, sub_eq_add_neg]

/-! ## Section 4. Counterterm-free damping walls, correlation locking, and smoothed RH equivalence -/

/-- **Atomic super-Arakelov `N log N` diagonal wall.** If any family of positive-semidefinite
kernels `K r` (`0 ≤ r < 1`) converges pointwise on `ℕ₊ × ℕ₊` (diagonal included) to `K₁` with
`K₁ m n = weilDeltaKernel m n` off the diagonal, then on every dyadic block `[N, 2N)` (`N ≥ 1`)
there exists `n ∈ [N, 2N)` with `K₁ n n ≥ N * (log N - 17) / 8`. -/
theorem atomic_countertermFree_diag_lower_bound {K : ℝ → ℕ → ℕ → ℝ} {K₁ : ℕ → ℕ → ℝ}
    (hpsd : ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ x : ℕ → ℝ,
      0 ≤ ∑ m ∈ S, ∑ n ∈ S, x m * x n * K r m n)
    (htend : ∀ m n : ℕ, 0 < m → 0 < n → Tendsto (fun r => K r m n) (𝓝[<] 1) (𝓝 (K₁ m n)))
    (hoff : ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n → K₁ m n = weilDeltaKernel m n)
    {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ) ^ 3 / 4) * (Real.log N - 17) ≤ ∑ n ∈ Finset.Ico N (2 * N), (n : ℝ) * K₁ n n ∧
      ∃ n ∈ Finset.Ico N (2 * N), (N : ℝ) * (Real.log N - 17) / 8 ≤ K₁ n n := by
  set B := Finset.Ico N (2 * N)
  have hB_pos : ∀ n ∈ B, 0 < n := fun n hn => by have := (Finset.mem_Ico.mp hn).1; omega
  -- Limit `K₁` is positive semidefinite on `B`
  have hK₁_psd : ∀ x : ℕ → ℝ, 0 ≤ ∑ m ∈ B, ∑ n ∈ B, x m * x n * K₁ m n := by
    intro x
    have hlim : Tendsto (fun r => ∑ m ∈ B, ∑ n ∈ B, x m * x n * K r m n) (𝓝[<] 1)
        (𝓝 (∑ m ∈ B, ∑ n ∈ B, x m * x n * K₁ m n)) :=
      tendsto_finsetSum B fun m hm => tendsto_finsetSum B fun n hn =>
        (htend m n (hB_pos m hm) (hB_pos n hn)).const_mul _
    have hge : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ ∑ m ∈ B, ∑ n ∈ B, x m * x n * K r m n := by
      have hgt0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), (0 : ℝ) < r :=
        nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)
      filter_upwards [hgt0, self_mem_nhdsWithin] with r hr0 hr1
      exact hpsd r hr0.le hr1 B hB_pos x
    haveI : (𝓝[<] (1 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
    exact ge_of_tendsto hlim hge
  -- Evaluate `K₁` on `x n = √n`
  have hx := hK₁_psd (fun n => Real.sqrt n)
  have hsplit_sum : ∑ m ∈ B, ∑ n ∈ B, Real.sqrt m * Real.sqrt n * K₁ m n =
      ∑ n ∈ B, (n : ℝ) * K₁ n n +
        ∑ m ∈ B, ∑ n ∈ B, if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n) := by
    have hterm : ∀ m ∈ B, ∀ n ∈ B, Real.sqrt m * Real.sqrt n * K₁ m n =
        (if m = n then (n : ℝ) * K₁ n n else 0) +
          (if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n)) := by
      intro m hm n hn
      by_cases hmn : m = n
      · subst hmn
        rw [if_pos rfl, if_pos rfl, add_zero, Real.mul_self_sqrt (Nat.cast_nonneg m)]
      · rw [if_neg hmn, if_neg hmn, zero_add, hoff m n (hB_pos m hm) (hB_pos n hn) hmn,
          ← Real.sqrt_mul (Nat.cast_nonneg m)]
        unfold frobeniusIntersection
        ring
    calc ∑ m ∈ B, ∑ n ∈ B, Real.sqrt m * Real.sqrt n * K₁ m n
        = ∑ m ∈ B, ∑ n ∈ B, ((if m = n then (n : ℝ) * K₁ n n else 0) +
            (if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n))) :=
          Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => hterm m hm n hn
      _ = (∑ m ∈ B, ∑ n ∈ B, if m = n then (n : ℝ) * K₁ n n else 0) +
            ∑ m ∈ B, ∑ n ∈ B, if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n) := by
          simp_rw [Finset.sum_add_distrib]
      _ = ∑ n ∈ B, (n : ℝ) * K₁ n n +
            ∑ m ∈ B, ∑ n ∈ B, if m = n then 0 else (((m : ℝ) + n) - frobeniusIntersection m n) := by
          congr 1
          refine Finset.sum_congr rfl fun m hm => ?_
          simp [hm]
  rw [hsplit_sum] at hx
  -- Bound the off-diagonal dyadic block sum via `frobeniusIntersection_block_bounds` and `sum_block_ge`
  have hcard : (B.card : ℝ) = N := by
    rw [Nat.card_Ico, show 2 * N - N = N by omega]
  have hrow : ∀ m ∈ B, (∑ n ∈ B, if m = n then (0 : ℝ) else (((m : ℝ) + n) - frobeniusIntersection m n)) ≤
      4 * N * N - (N : ℝ) ^ 2 / 4 * ∑ n ∈ Finset.Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
    intro m hm
    have hpt : ∀ n ∈ B, (if m = n then (0 : ℝ) else (((m : ℝ) + n) - frobeniusIntersection m n)) ≤
        4 * N - (if m < n then (N : ℝ) ^ 2 / 4 * (1 / ((n : ℝ) - m)) else 0) := by
      intro n hn
      have hm' := Finset.mem_Ico.mp hm
      have hn' := Finset.mem_Ico.mp hn
      have hsum_le : (m : ℝ) + n ≤ 4 * N := by exact_mod_cast (by omega : m + n ≤ 4 * N)
      by_cases hmn : m = n
      · subst hmn; simp
      rw [if_neg hmn]
      obtain ⟨hlo, -⟩ := frobeniusIntersection_block_bounds hm hn hmn
      by_cases hlt : m < n
      · rw [if_pos hlt]
        have hlt' : (m : ℝ) < n := by exact_mod_cast hlt
        rw [abs_of_neg (by linarith), neg_sub] at hlo
        have : (N : ℝ) ^ 2 / 4 * (1 / ((n : ℝ) - m)) = (N : ℝ) ^ 2 / (4 * ((n : ℝ) - m)) := by
          field_simp
        linarith
      · rw [if_neg hlt]
        have h0 : 0 ≤ (N : ℝ) ^ 2 / (4 * |(m : ℝ) - n|) := by positivity
        linarith
    calc _ ≤ ∑ n ∈ B, (4 * (N : ℝ) - (if m < n then (N : ℝ) ^ 2 / 4 * (1 / ((n : ℝ) - m)) else 0)) :=
          Finset.sum_le_sum hpt
      _ = 4 * N * N - (N : ℝ) ^ 2 / 4 * ∑ n ∈ Finset.Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.sum_filter,
            Finset.mul_sum]
          have hf : B.filter (fun n => m < n) = Finset.Ico (m + 1) (2 * N) := by
            have hm' := Finset.mem_Ico.mp hm
            ext n; simp only [B, Finset.mem_filter, Finset.mem_Ico]; omega
          rw [hf]; ring
  have hoff_ub : (∑ m ∈ B, ∑ n ∈ B, if m = n then (0 : ℝ) else (((m : ℝ) + n) - frobeniusIntersection m n)) ≤
      4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 * ((N : ℝ) * Real.log N - N) := by
    calc _ ≤ ∑ m ∈ B, (4 * N * N - (N : ℝ) ^ 2 / 4 * ∑ n ∈ Finset.Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m)) :=
          Finset.sum_le_sum hrow
      _ = 4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 *
            ∑ m ∈ B, ∑ n ∈ Finset.Ico (m + 1) (2 * N), 1 / ((n : ℝ) - m) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.mul_sum]
          ring
      _ ≤ 4 * (N : ℝ) ^ 3 - (N : ℝ) ^ 2 / 4 * ((N : ℝ) * Real.log N - N) := by
          have := sum_block_ge N
          have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 4 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left this h4]
  have hsum_lb : ((N : ℝ) ^ 3 / 4) * (Real.log N - 17) ≤ ∑ n ∈ B, (n : ℝ) * K₁ n n := by
    linarith
  refine ⟨hsum_lb, ?_⟩
  by_contra hall
  push Not at hall
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm_lt : ∀ n ∈ B, (n : ℝ) * K₁ n n < (N : ℝ) ^ 2 * (Real.log N - 17) / 4 := by
    intro n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hB_pos n hn
    have hn_lt : (n : ℝ) < 2 * N := by exact_mod_cast (Finset.mem_Ico.mp hn).2
    have hKn := hall n hn
    have hKn_pos_or : (n : ℝ) * K₁ n n < (n : ℝ) * ((N : ℝ) * (Real.log N - 17) / 8) :=
      mul_lt_mul_of_pos_left hKn hn_pos
    have hK₁_nn : 0 ≤ K₁ n n := by
      have h1 := hK₁_psd (fun m => if m = n then 1 else 0)
      have heq : (∑ m ∈ B, ∑ l ∈ B, (if m = n then (1 : ℝ) else 0) *
          (if l = n then 1 else 0) * K₁ m l) = K₁ n n := by
        rw [Finset.sum_eq_single n]
        · rw [Finset.sum_eq_single n]
          · simp
          · intro l _ hln; simp [hln]
          · intro hnB; exact absurd hn hnB
        · intro m _ hmn; simp [hmn]
        · intro hnB; exact absurd hn hnB
      rwa [heq] at h1
    have hlog17 : 0 ≤ (N : ℝ) * (Real.log N - 17) / 8 := by
      by_contra hneg; push Not at hneg; linarith
    calc (n : ℝ) * K₁ n n
        < (n : ℝ) * ((N : ℝ) * (Real.log N - 17) / 8) := hKn_pos_or
      _ ≤ (2 * (N : ℝ)) * ((N : ℝ) * (Real.log N - 17) / 8) :=
          mul_le_mul_of_nonneg_right hn_lt.le hlog17
      _ = (N : ℝ) ^ 2 * (Real.log N - 17) / 4 := by ring
  have hB_nonempty : B.Nonempty := Finset.nonempty_Ico.mpr (by omega)
  have hsum_lt : ∑ n ∈ B, (n : ℝ) * K₁ n n < ((N : ℝ) ^ 3 / 4) * (Real.log N - 17) := by
    calc ∑ n ∈ B, (n : ℝ) * K₁ n n
        < ∑ _n ∈ B, (N : ℝ) ^ 2 * (Real.log N - 17) / 4 :=
          Finset.sum_lt_sum_of_nonempty hB_nonempty hterm_lt
      _ = ((N : ℝ) ^ 3 / 4) * (Real.log N - 17) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  linarith

/-- No counterterm-free positive-semidefinite damping of atomic `weilDeltaKernel` can converge on
the diagonal to a `C (1 + log n)` profile (including any multiple of the torsion self-intersection
`I(n, n) / φ(n)`). -/
theorem not_atomic_countertermFree_log_diag (C : ℝ) :
    ¬ ∃ (K : ℝ → ℕ → ℕ → ℝ) (K₁ : ℕ → ℕ → ℝ),
      (∀ r : ℝ, 0 ≤ r → r < 1 → ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ x : ℕ → ℝ,
        0 ≤ ∑ m ∈ S, ∑ n ∈ S, x m * x n * K r m n) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → Tendsto (fun r => K r m n) (𝓝[<] 1) (𝓝 (K₁ m n))) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → m ≠ n → K₁ m n = weilDeltaKernel m n) ∧
      (∀ n : ℕ, 0 < n → K₁ n n ≤ C * (1 + Real.log n)) := by
  rintro ⟨K, K₁, hpsd, htend, hoff, hdiag⟩
  set C₀ := max 1 |C|
  have hC₀_pos : 0 < C₀ := by positivity
  set N : ℕ := (⌊Real.exp 19⌋₊ + 1) * (⌊32 * C₀⌋₊ + 1)
  have hN1 : 1 ≤ N := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hexp19_lt : Real.exp 19 < N := by
    have h1 : Real.exp 19 < (⌊Real.exp 19⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (1 : ℝ) ≤ (⌊32 * C₀⌋₊ : ℝ) + 1 := by linarith [Nat.cast_nonneg ⌊32 * C₀⌋₊]
    push_cast [N]
    nlinarith
  have hN_pos : (0 : ℝ) < N := (Real.exp_pos 19).trans hexp19_lt
  have hlogN_gt : 19 < Real.log N := (Real.lt_log_iff_exp_lt hN_pos).mpr hexp19_lt
  obtain ⟨-, n, hnB, hlo⟩ := atomic_countertermFree_diag_lower_bound hpsd htend hoff hN1
  have hn_pos : 0 < n := by have := (Finset.mem_Ico.mp hnB).1; omega
  have hn_lt : (n : ℝ) < 2 * N := by exact_mod_cast (Finset.mem_Ico.mp hnB).2
  have hhi := hdiag n hn_pos
  have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
  have hlog_n_le : 1 + Real.log n ≤ 2 * (Real.log N - 17) * 8 := by
    have hn_pos' : (0 : ℝ) < n := by exact_mod_cast hn_pos
    have hln : Real.log n ≤ Real.log (2 * N) := Real.log_le_log hn_pos' hn_lt.le
    rw [Real.log_mul two_ne_zero hN_pos.ne'] at hln
    linarith
  have hC_le : C * (1 + Real.log n) ≤ C₀ * (16 * (Real.log N - 17)) := by
    have h1 : 0 ≤ 1 + Real.log n := by
      have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn_pos)
      linarith
    have hCC₀ : C ≤ C₀ := (le_abs_self C).trans (le_max_right 1 |C|)
    calc C * (1 + Real.log n) ≤ C₀ * (1 + Real.log n) := mul_le_mul_of_nonneg_right hCC₀ h1
      _ ≤ C₀ * (2 * (Real.log N - 17) * 8) := mul_le_mul_of_nonneg_left hlog_n_le hC₀_pos.le
      _ = C₀ * (16 * (Real.log N - 17)) := by ring
  have hstrict : C₀ * (16 * (Real.log N - 17)) < (N : ℝ) * (Real.log N - 17) / 8 := by
    have hpos_diff : 0 < Real.log N - 17 := by linarith
    rw [lt_div_iff₀ (by norm_num)]
    have : 128 * C₀ < N := by
      have he19 : (20 : ℝ) ≤ Real.exp 19 := by linarith [Real.add_one_le_exp (19 : ℝ)]
      have hf1 : (20 : ℝ) ≤ (⌊Real.exp 19⌋₊ : ℝ) + 1 := by
        linarith [Nat.lt_floor_add_one (Real.exp 19)]
      have hf2 : 32 * C₀ < (⌊32 * C₀⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      push_cast [N]
      nlinarith
    nlinarith
  linarith

/-! ### Additive channel decoupling no-go and ultraviolet correlation locking -/

/-- **Additive decoupling no-go.** For any family of positive-semidefinite kernels `A r` (`0 ≤ r < 1`)
and any non-zero real vector `x` on a finite set `S` of positive integers (`0 < ∑_{n ∈ S} x_n²`),
the decoupled quadratic form `∑_{m, n ∈ S} x_m x_n (A_r m n + twistedEnergy r m n)` diverges to
`+∞` as `r → 1⁻`. -/
theorem tendsto_add_twistedEnergy_atTop {A : ℝ → ℕ → ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n)
    (hA_psd : ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ y : ℕ → ℝ,
      0 ≤ ∑ m ∈ S, ∑ n ∈ S, y m * y n * A r m n)
    {x : ℕ → ℝ} (hx : 0 < ∑ n ∈ S, x n ^ 2) :
    Tendsto (fun r => ∑ m ∈ S, ∑ n ∈ S, x m * x n * (A r m n + twistedEnergy r m n))
      (𝓝[<] 1) atTop := by
  have hren : Tendsto (fun r => ∑ m ∈ S, ∑ n ∈ S, x m * x n * twistedEnergy r m n +
      Real.log |1 - r| * ∑ n ∈ S, x n ^ 2) (𝓝[<] 1) (𝓝 _) :=
    (weilPrimeKernel_renormalized_torsion_energy hS x).2.mono_left nhdsWithin_le_nhds
  -- `-log |1 - r| → +∞` as `r → 1⁻`
  have hneg_log : Tendsto (fun r : ℝ => -Real.log |1 - r|) (𝓝[<] 1) atTop := by
    have hsub : Tendsto (fun r : ℝ => |1 - r|) (𝓝[<] 1) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun r : ℝ => |1 - r|) := by fun_prop
        simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        rw [Set.mem_Iio] at hr
        exact Set.mem_Ioi.mpr (abs_pos.mpr (by linarith))
    exact Filter.tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hsub)
  have hdiv_T : Tendsto (fun r : ℝ => ∑ m ∈ S, ∑ n ∈ S, x m * x n * twistedEnergy r m n)
      (𝓝[<] 1) atTop := by
    have hsum := Filter.Tendsto.atTop_add (hneg_log.atTop_mul_const hx) hren
    refine hsum.congr fun r => ?_
    ring
  refine tendsto_atTop_mono' (𝓝[<] 1) ?_ hdiv_T
  have hgt0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), (0 : ℝ) < r :=
    nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)
  filter_upwards [hgt0, self_mem_nhdsWithin] with r hr0 hr1
  have hA := hA_psd r hr0.le hr1 x
  have hsplit : ∑ m ∈ S, ∑ n ∈ S, x m * x n * (A r m n + twistedEnergy r m n) =
      (∑ m ∈ S, ∑ n ∈ S, x m * x n * A r m n) +
        ∑ m ∈ S, ∑ n ∈ S, x m * x n * twistedEnergy r m n := by
    simp_rw [mul_add, Finset.sum_add_distrib]
  linarith

/-- **Ultraviolet correlation-locking law.** In any real inner-product space `H`, if `u r` and `v r`
have finite difference limit `‖u r - v r‖² → D` while `‖v r‖ → +∞` along a filter `l`, then
`‖u r‖ / ‖v r‖ → 1` and the inner-product correlation `⟪u r, v r⟫_ℝ / (‖u r‖ ‖v r‖) → 1`. -/
theorem ultraviolet_correlation_locking {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {α : Type*} {l : Filter α} {u v : α → H} {D : ℝ}
    (hv : Tendsto (fun r => ‖v r‖) l atTop)
    (hdiff : Tendsto (fun r => ‖u r - v r‖ ^ 2) l (𝓝 D)) :
    Tendsto (fun r => ‖u r‖ / ‖v r‖) l (𝓝 1) ∧
      Tendsto (fun r => @inner ℝ H _ (u r) (v r) / (‖u r‖ * ‖v r‖)) l (𝓝 1) := by
  -- Step 1: `(‖u r‖ - ‖v r‖) / ‖v r‖ → 0`, hence `‖u r‖ / ‖v r‖ → 1`
  have hnorm_diff_sq : Tendsto (fun r => (‖u r - v r‖ / ‖v r‖) ^ 2) l (𝓝 0) := by
    have hinv_sq : Tendsto (fun r => (‖v r‖ ^ 2)⁻¹) l (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (hv.atTop_mul_atTop₀ hv |>.congr fun r => (sq ‖v r‖).symm)
    have hmul := hdiff.mul hinv_sq
    rw [mul_zero] at hmul
    exact hmul.congr fun r => by rw [div_pow, div_eq_mul_inv]
  have hnorm_diff_div : Tendsto (fun r => ‖u r - v r‖ / ‖v r‖) l (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hnorm_diff_sq
    rw [Real.sqrt_zero] at hsqrt
    refine hsqrt.congr' ?_
    filter_upwards [hv.eventually_gt_atTop 0] with r hvr
    exact Real.sqrt_sq (div_nonneg (norm_nonneg _) hvr.le)
  have hsub_div : Tendsto (fun r => (‖u r‖ - ‖v r‖) / ‖v r‖) l (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero_norm' ?_ hnorm_diff_div)
    filter_upwards [hv.eventually_gt_atTop 0] with r hvr
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hvr]
    exact div_le_div_of_nonneg_right (abs_norm_sub_norm_le (u r) (v r)) hvr.le
  have hratio : Tendsto (fun r => ‖u r‖ / ‖v r‖) l (𝓝 1) := by
    have h1 := hsub_div.add_const 1
    rw [zero_add] at h1
    refine h1.congr' ?_
    filter_upwards [hv.eventually_gt_atTop 0] with r hvr
    have hne : ‖v r‖ ≠ 0 := hvr.ne'
    field_simp; ring
  refine ⟨hratio, ?_⟩
  -- Step 2: `⟪u r, v r⟫ / (‖u r‖ ‖v r‖) = (‖u‖ / (2 ‖v‖) + ‖v‖ / (2 ‖u‖)) - ‖u - v‖² / (2 ‖u‖ ‖v‖)`
  have hratio_inv : Tendsto (fun r => ‖v r‖ / ‖u r‖) l (𝓝 1) := by
    have h := hratio.inv₀ one_ne_zero
    rw [inv_one] at h
    exact h.congr fun r => inv_div ‖u r‖ ‖v r‖
  have hu_top : Tendsto (fun r => ‖u r‖) l atTop := by
    have hmul := hratio.pos_mul_atTop zero_lt_one hv
    refine hmul.congr' ?_
    filter_upwards [hv.eventually_gt_atTop 0] with r hvr
    exact div_mul_cancel₀ ‖u r‖ hvr.ne'
  have hden_top : Tendsto (fun r => 2 * (‖u r‖ * ‖v r‖)) l atTop :=
    (hu_top.atTop_mul_atTop₀ hv).const_mul_atTop two_pos
  have htail : Tendsto (fun r => ‖u r - v r‖ ^ 2 / (2 * (‖u r‖ * ‖v r‖))) l (𝓝 0) := by
    have h := hdiff.mul (tendsto_inv_atTop_zero.comp hden_top)
    rw [mul_zero] at h
    exact h.congr fun r => (div_eq_mul_inv _ _).symm
  have hmain := ((hratio.div_const 2).add (hratio_inv.div_const 2)).sub htail
  rw [show (1 : ℝ) / 2 + 1 / 2 - 0 = 1 by ring] at hmain
  refine hmain.congr' ?_
  filter_upwards [hv.eventually_gt_atTop 0, hu_top.eventually_gt_atTop 0] with r hvr hur
  have hv_ne : ‖v r‖ ≠ 0 := hvr.ne'
  have hu_ne : ‖u r‖ ≠ 0 := hur.ne'
  have hpol : 2 * @inner ℝ H _ (u r) (v r) = ‖u r‖ ^ 2 + ‖v r‖ ^ 2 - ‖u r - v r‖ ^ 2 := by
    linarith [norm_sub_sq_real (u r) (v r)]
  calc ((‖u r‖ / ‖v r‖) / 2 + (‖v r‖ / ‖u r‖) / 2) - ‖u r - v r‖ ^ 2 / (2 * (‖u r‖ * ‖v r‖))
      = (‖u r‖ ^ 2 + ‖v r‖ ^ 2 - ‖u r - v r‖ ^ 2) / (2 * (‖u r‖ * ‖v r‖)) := by
        field_simp
    _ = (2 * @inner ℝ H _ (u r) (v r)) / (2 * (‖u r‖ * ‖v r‖)) := by rw [← hpol]
    _ = @inner ℝ H _ (u r) (v r) / (‖u r‖ * ‖v r‖) := by field_simp

/-! ### Smoothed Frobenius counterterm-free damping equivalence to RH -/

/-- Finite Schur-product lemma for `min(A_i, A_j)`: multiplying any positive-semidefinite kernel `Q`
pointwise by `min(A_i, A_j)` (`A ≥ 0` on `S`) preserves positive semidefiniteness. -/
theorem schur_min_posSemidef {ι : Type*} [DecidableEq ι] (S : Finset ι) {A : ι → ℝ}
    (hA : ∀ i ∈ S, 0 ≤ A i) {Q : ι → ι → ℝ}
    (hQ : ∀ y : ι → ℝ, 0 ≤ ∑ i ∈ S, ∑ j ∈ S, y i * y j * Q i j) (z : ι → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, z i * z j * (min (A i) (A j) * Q i j) := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS_ne
    · simp
    obtain ⟨i₀, hi₀S, hi₀_min⟩ := S.exists_min_image A hS_ne
    set c := A i₀
    have hc0 : 0 ≤ c := hA i₀ hi₀S
    have hmin_split : ∀ i ∈ S, ∀ j ∈ S,
        min (A i) (A j) = c + min (A i - c) (A j - c) := by
      intro i hi j hj
      rcases le_total (A i) (A j) with hij | hji
      · rw [min_eq_left hij, min_eq_left (sub_le_sub_right hij c)]; ring
      · rw [min_eq_right hji, min_eq_right (sub_le_sub_right hji c)]; ring
    have hsplit : ∑ i ∈ S, ∑ j ∈ S, z i * z j * (min (A i) (A j) * Q i j) =
        c * (∑ i ∈ S, ∑ j ∈ S, z i * z j * Q i j) +
          ∑ i ∈ S, ∑ j ∈ S, z i * z j * (min (A i - c) (A j - c) * Q i j) := by
      calc ∑ i ∈ S, ∑ j ∈ S, z i * z j * (min (A i) (A j) * Q i j)
          = ∑ i ∈ S, ∑ j ∈ S, (c * (z i * z j * Q i j) +
              z i * z j * (min (A i - c) (A j - c) * Q i j)) :=
            Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
              rw [hmin_split i hi j hj]; ring
        _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsplit]
    -- The `A - c` term vanishes whenever `i = i₀` or `j = i₀`, reducing to `S.erase i₀`
    set S' := S.erase i₀
    have hcard_lt : S' ⊂ S := Finset.erase_ssubset hi₀S
    have hA' : ∀ i ∈ S', 0 ≤ A i - c := fun i hi =>
      sub_nonneg.mpr (hi₀_min i (Finset.mem_of_mem_erase hi))
    have hQ'_clean : ∀ y : ι → ℝ, 0 ≤ ∑ i ∈ S', ∑ j ∈ S', y i * y j * Q i j := by
      intro y
      have h := hQ (fun i => if i ∈ S' then y i else 0)
      have hf : S.filter (fun i => i ∈ S') = S' := by
        ext i; simp only [S', Finset.mem_filter, Finset.mem_erase]; tauto
      have heq : (∑ i ∈ S, ∑ j ∈ S,
          (if i ∈ S' then y i else 0) * (if j ∈ S' then y j else 0) * Q i j) =
          ∑ i ∈ S', ∑ j ∈ S', y i * y j * Q i j := by
        have houter : ∀ i ∈ S, (∑ j ∈ S,
            (if i ∈ S' then y i else 0) * (if j ∈ S' then y j else 0) * Q i j) =
            if i ∈ S' then ∑ j ∈ S', y i * y j * Q i j else 0 := by
          intro i _
          by_cases hi : i ∈ S'
          · rw [if_pos hi]
            have hinner : ∀ j ∈ S, y i * (if j ∈ S' then y j else 0) * Q i j =
                if j ∈ S' then y i * y j * Q i j else 0 := fun j _ => by split_ifs <;> ring
            rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, hf]
          · simp [hi]
        rw [Finset.sum_congr rfl houter, ← Finset.sum_filter, hf]
      rwa [heq] at h
    have herase_eq : ∑ i ∈ S, ∑ j ∈ S, z i * z j * (min (A i - c) (A j - c) * Q i j) =
        ∑ i ∈ S', ∑ j ∈ S', z i * z j * (min (A i - c) (A j - c) * Q i j) := by
      rw [← Finset.add_sum_erase _ _ hi₀S]
      have hzero_row : ∑ j ∈ S, z i₀ * z j * (min (A i₀ - c) (A j - c) * Q i₀ j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hle : 0 ≤ A j - c := sub_nonneg.mpr (hi₀_min j hj)
        have hmin0 : min (A i₀ - c) (A j - c) = 0 := by
          simp only [c, sub_self]
          exact min_eq_left hle
        rw [hmin0]; ring
      rw [hzero_row, zero_add]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.add_sum_erase _ _ hi₀S]
      have hmin0' : min (A i - c) (A i₀ - c) = 0 := by
        simp only [c, sub_self]
        exact min_eq_right (hA' i hi)
      rw [hmin0']; simp [S']
    rw [herase_eq]
    exact add_nonneg (mul_nonneg hc0 (hQ z)) (ih S' hcard_lt hA' hQ'_clean z)

/-- Ornstein–Uhlenbeck Schur damping: multiplying any positive-semidefinite kernel `Q` pointwise by
`exp(-λ |x_i - x_j|)` (`λ ≥ 0`) preserves positive semidefiniteness. -/
theorem ornsteinUhlenbeck_schur_posSemidef {ι : Type*} [DecidableEq ι] (S : Finset ι) {l : ℝ}
    (hl : 0 ≤ l) (x : ι → ℝ) {Q : ι → ι → ℝ}
    (hQ : ∀ y : ι → ℝ, 0 ≤ ∑ i ∈ S, ∑ j ∈ S, y i * y j * Q i j) (z : ι → ℝ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, z i * z j * (Real.exp (-l * |x i - x j|) * Q i j) := by
  have hexp_eq : ∀ i j : ι, Real.exp (-l * |x i - x j|) =
      Real.exp (-l * x i) * Real.exp (-l * x j) *
        min (Real.exp (2 * l * x i)) (Real.exp (2 * l * x j)) := by
    intro i j
    rcases le_total (x i) (x j) with hij | hji
    · have h2 : 2 * l * x i ≤ 2 * l * x j := mul_le_mul_of_nonneg_left hij (by linarith)
      rw [min_eq_left (Real.exp_le_exp.mpr h2), abs_of_nonpos (sub_nonpos.mpr hij),
        ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    · have h2 : 2 * l * x j ≤ 2 * l * x i := mul_le_mul_of_nonneg_left hji (by linarith)
      rw [min_eq_right (Real.exp_le_exp.mpr h2), abs_of_nonneg (sub_nonneg.mpr hji),
        ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
  have h := schur_min_posSemidef S (A := fun i => Real.exp (2 * l * x i))
    (fun i _ => (Real.exp_pos _).le) hQ (fun i => z i * Real.exp (-l * x i))
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  rw [hexp_eq i j]; ring

/-- **Smoothed counterterm-free damping equivalence to RH.** `RiemannHypothesis` holds if and only
if the cubic-spline Frobenius correlation `zetaScalingDatum.orbitCorr splineCycle (log m - log n)`
is the pointwise `r → 1⁻` limit on all of `ℕ₊ × ℕ₊` (diagonal included, with zero counterterm
subtraction) of a family of positive-semidefinite kernels `K r` (`0 ≤ r < 1`). -/
theorem riemannHypothesis_iff_exists_damped_psd_limit :
    RiemannHypothesis ↔ ∃ K : ℝ → ℕ → ℕ → ℝ,
      (∀ r : ℝ, 0 ≤ r → r < 1 → ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ c : ℕ → ℝ,
        0 ≤ ∑ m ∈ S, ∑ n ∈ S, c m * c n * K r m n) ∧
      (∀ m n : ℕ, 0 < m → 0 < n →
        Tendsto (fun r => K r m n) (𝓝[<] 1)
          (𝓝 (zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n)))) := by
  constructor
  · intro hRH
    have hHW := riemannHypothesis_iff_splineOrbit_hasseWeil.mp hRH
    have hHW_cfg : ∀ v : ℝ,
        (configScalingDatum Zeta23.zetaZeroConfig
          SquareRootThreshold.temperedConfig_zetaZeroConfig).HasseWeilAt splineCycle v :=
      fun v => (zeta_hasseWeilAt_iff splineCycle v).mp (hHW v)
    have hOHI : (configScalingDatum Zeta23.zetaZeroConfig
        SquareRootThreshold.temperedConfig_zetaZeroConfig).OrbitHodgeIndex splineCycle :=
      ((orientation_tfae Zeta23.zetaZeroConfig
        SquareRootThreshold.temperedConfig_zetaZeroConfig
        fesSymmetric_zetaZeroConfig splineCycle).out 0 1).mp hHW_cfg
    have hQ_psd : ∀ (S : Finset ℕ) (c : ℕ → ℝ),
        0 ≤ ∑ m ∈ S, ∑ n ∈ S, c m * c n *
          zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n) := by
      intro S c
      set T : Finset ℝ := S.image (fun n : ℕ => Real.log n)
      let w : ℝ → ℝ := fun g => ∑ n ∈ S.filter (fun n => Real.log n = g), c n
      have h0 := hOHI T w
      have hcorr_eq : ∀ g h : ℝ,
          (configScalingDatum Zeta23.zetaZeroConfig
            SquareRootThreshold.temperedConfig_zetaZeroConfig).orbitCorr splineCycle (g - h) =
            zetaScalingDatum.orbitCorr splineCycle (g - h) :=
        fun g h => configScalingDatum_zeta_orbitCorr splineCycle (g - h)
      simp_rw [hcorr_eq] at h0
      refine le_of_le_of_eq h0 ?_
      have hfiber : ∀ F : ℝ → ℝ, ∑ g ∈ T, w g * F g = ∑ m ∈ S, c m * F (Real.log m) := by
        intro F
        have hstep : ∀ g ∈ T, w g * F g =
            ∑ m ∈ S.filter (fun n => Real.log n = g), c m * F (Real.log m) := by
          intro g _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [(Finset.mem_filter.mp hm).2]
        rw [Finset.sum_congr rfl hstep, ← Finset.sum_biUnion]
        · congr 1
          ext m
          simp [T]
        · intro g₁ _ g₂ _ hg12
          rw [Finset.disjoint_left]
          intro m hm1 hm2
          exact hg12 ((Finset.mem_filter.mp hm1).2.symm.trans (Finset.mem_filter.mp hm2).2)
      calc ∑ g ∈ T, ∑ h ∈ T, w g * w h * zetaScalingDatum.orbitCorr splineCycle (g - h)
          = ∑ g ∈ T, w g * (∑ h ∈ T, w h * zetaScalingDatum.orbitCorr splineCycle (g - h)) := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun h _ => by ring
        _ = ∑ g ∈ T, w g *
              (∑ n ∈ S, c n * zetaScalingDatum.orbitCorr splineCycle (g - Real.log n)) :=
            Finset.sum_congr rfl fun g _ =>
              congrArg (w g * ·) (hfiber fun h => zetaScalingDatum.orbitCorr splineCycle (g - h))
        _ = ∑ m ∈ S, c m *
              (∑ n ∈ S, c n * zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n)) :=
            hfiber fun g => ∑ n ∈ S, c n * zetaScalingDatum.orbitCorr splineCycle (g - Real.log n)
        _ = ∑ m ∈ S, ∑ n ∈ S, c m * c n *
              zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => by ring
    refine ⟨fun r m n => Real.exp (-(1 - r) * |Real.log m - Real.log n|) *
      zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n), ?_, ?_⟩
    · intro r _ hr1 S _ c
      exact ornsteinUhlenbeck_schur_posSemidef S (sub_nonneg.mpr hr1.le) (fun n => Real.log n)
        (hQ_psd S) c
    · intro m n _ _
      have hcont : Continuous fun r : ℝ =>
          Real.exp (-(1 - r) * |Real.log m - Real.log n|) *
            zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n) := by fun_prop
      have hval : Real.exp (-(1 - 1) * |Real.log m - Real.log n|) *
          zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n) =
          zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n) := by simp
      exact tendsto_nhdsWithin_of_tendsto_nhds (hval ▸ hcont.tendsto 1)
  · rintro ⟨K, hpsd, hlim⟩
    rw [riemannHypothesis_iff_hasseWeil_integerDegrees]
    have hQ : ∀ (S : Finset ℕ), (∀ k ∈ S, 0 < k) → ∀ c : ℕ → ℝ,
        0 ≤ ∑ m ∈ S, ∑ n ∈ S, c m * c n *
          zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n) := by
      intro S hS c
      have htend : Tendsto (fun r => ∑ m ∈ S, ∑ n ∈ S, c m * c n * K r m n) (𝓝[<] 1)
          (𝓝 (∑ m ∈ S, ∑ n ∈ S, c m * c n *
            zetaScalingDatum.orbitCorr splineCycle (Real.log m - Real.log n))) :=
        tendsto_finset_sum S fun m hm => tendsto_finset_sum S fun n hn =>
          (hlim m n (hS m hm) (hS n hn)).const_mul (c m * c n)
      have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ ∑ m ∈ S, ∑ n ∈ S, c m * c n * K r m n := by
        filter_upwards [Ico_mem_nhdsLT zero_lt_one] with r hr
        exact hpsd r hr.1 hr.2 S hS c
      haveI : (𝓝[<] (1 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
      exact ge_of_tendsto htend hev
    intro n hn
    rw [ScalingDatum.HasseWeilAt]
    set c0 := zetaScalingDatum.orbitCorr splineCycle 0
    set cn := zetaScalingDatum.orbitCorr splineCycle (Real.log n)
    by_cases hn1 : n = 1
    · subst hn1
      have h11 := hQ {1} (fun k hk => by simp at hk; omega) (fun _ => 1)
      simp only [Finset.sum_singleton, Nat.cast_one, Real.log_one, sub_self, one_mul] at h11
      rw [Nat.cast_one, Real.log_one, abs_of_nonneg h11]
    · have h1_ne : (1 : ℕ) ≠ n := Ne.symm hn1
      have hpair_pos : ∀ k ∈ ({1, n} : Finset ℕ), 0 < k := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk'
        · exact Nat.one_pos
        · rw [Finset.mem_singleton.mp hk']; exact hn
      have hplus := hQ {1, n} hpair_pos (fun k => if k = 1 then 1 else 1)
      have hminus := hQ {1, n} hpair_pos (fun k => if k = 1 then 1 else -1)
      simp only [Finset.sum_pair h1_ne, ↓reduceIte, h1_ne.symm, Nat.cast_one, Real.log_one,
        sub_self, zero_sub, sub_zero, zetaScalingDatum.orbitCorr_neg] at hplus hminus
      change |cn| ≤ c0
      rw [abs_le]
      constructor <;> linarith

/-! ### Single-channel impossibility for smoothed prime and archimedean-plus-pole kernels -/

/-- The smoothed prime-comb kernel on `ℕ × ℕ` associated to a real test `f`,
`P_f(m, n) = -Re(weightedPrimePart Λ (f_m ⋆ f̃_n))` where `f_m = scaleShift (log m) f`. -/
def smoothedPrimeKernel (f : ℝ → ℝ) (m n : ℕ) : ℝ :=
  -(FrustratedArithmeticDirichletForms.weightedPrimePart
    (fun k => (Λ k : ℝ))
    (Zeta23.EF.weilTest (cx (scaleShift (Real.log m) f)) (cx (scaleShift (Real.log n) f)))).re

/-- The smoothed archimedean-plus-pole kernel on `ℕ × ℕ` associated to a real test `f`,
`C_{∞, f}(m, n) = Re(weilFullFunctional 0 (f_m ⋆ f̃_n))`. -/
def smoothedArchPoleKernel (f : ℝ → ℝ) (m n : ℕ) : ℝ :=
  (RHTower.weilFullFunctional (fun _ => 0)
    (Zeta23.EF.weilTest (cx (scaleShift (Real.log m) f)) (cx (scaleShift (Real.log n) f)))).re

/-- The sum of the smoothed prime kernel and the smoothed archimedean-plus-pole kernel is the exact
orbit correlation `zetaScalingDatum.orbitCorr (0, 0, ⟨f, hf⟩) (log m - log n)`. -/
theorem smoothedPrime_add_smoothedArchPole_eq_orbitCorr {f : ℝ → ℝ} (hf : f ∈ realTests)
    (m n : ℕ) :
    smoothedPrimeKernel f m n + smoothedArchPoleKernel f m n =
      zetaScalingDatum.orbitCorr (0, 0, ⟨f, hf⟩) (Real.log m - Real.log n) := by
  have hsplit := FrustratedArithmeticDirichletForms.weilFullFunctional_eq_sub_weightedPrimePart
    (fun k => (Λ k : ℝ))
    (Zeta23.EF.weilTest (cx (scaleShift (Real.log m) f)) (cx (scaleShift (Real.log n) f)))
  have hsum : smoothedPrimeKernel f m n + smoothedArchPoleKernel f m n =
      weilPair (scaleShift (Real.log m) f) (scaleShift (Real.log n) f) := by
    rw [weilPair, hsplit, Complex.sub_re, smoothedPrimeKernel, smoothedArchPoleKernel]
    ring
  rw [hsum, weilPair_scaleShift, ← configWeil_zeta_eq_weilPair
    (scaleShift_mem (Real.log m - Real.log n) hf) hf, ← configScalingDatum_zeta_orbitCorr]
  rw [ScalingDatum.orbitCorr]
  change (configSurface Zeta23.zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig).defect
    (scalingAction (Real.log m - Real.log n) (0, 0, ⟨f, hf⟩)) (0, 0, ⟨f, hf⟩) = _
  rw [configSurface_defect]
  rfl

private theorem integral_pos_of_nonneg_nonzero {g : ℝ → ℝ} (hg_cont : Continuous g)
    (hg_int : Integrable g) (hg_nn : ∀ u, 0 ≤ g u) {u₀ : ℝ} (hu₀ : g u₀ ≠ 0) :
    0 < ∫ u, g u := by
  by_contra hle
  have hzero : ∫ u, g u = 0 := le_antisymm (not_lt.mp hle) (integral_nonneg hg_nn)
  have hae := (integral_eq_zero_iff_of_nonneg hg_nn hg_int).mp hzero
  have hfun : g = 0 := (Continuous.ae_eq_iff_eq volume hg_cont continuous_const).mp hae
  exact hu₀ (congrFun hfun u₀)

/-- **Single-channel impossibility (prime comb).** For every non-zero nonnegative test
`f ∈ realTests`, the smoothed prime kernel `smoothedPrimeKernel f` fails positive semidefiniteness
on `{1, 2}` and therefore cannot be a counterterm-free pointwise limit of positive-semidefinite
kernels `K r` (`0 ≤ r < 1`) on `ℕ₊ × ℕ₊`. -/
theorem not_psd_limit_smoothedPrime {f : ℝ → ℝ} (hf : f ∈ realTests) (hf_nn : ∀ u, 0 ≤ f u)
    (hf_ne : ∃ u₀, f u₀ ≠ 0) :
    ¬ ∃ K : ℝ → ℕ → ℕ → ℝ,
      (∀ r : ℝ, 0 ≤ r → r < 1 → ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ c : ℕ → ℝ,
        0 ≤ ∑ m ∈ S, ∑ n ∈ S, c m * c n * K r m n) ∧
      (∀ m n : ℕ, 0 < m → 0 < n →
        Tendsto (fun r => K r m n) (𝓝[<] 1) (𝓝 (smoothedPrimeKernel f m n))) := by
  obtain ⟨u₀, hu₀⟩ := hf_ne
  have hf_sq_pos : 0 < ∫ u, f u ^ 2 :=
    integral_pos_of_nonneg_nonzero (hf.1.continuous.pow 2)
      ((hf.1.continuous.pow 2).integrable_of_hasCompactSupport
        (by simpa [sq] using hf.2.mul_right))
      (fun u => sq_nonneg (f u)) (pow_ne_zero 2 hu₀)
  -- Every summand in `weightedPrimePart Λ (f_m ⋆ f̃_n)` is real and nonnegative when `f ≥ 0`
  have hterm_nn : ∀ (m n k : ℕ), 0 ≤
      (((if 2 ≤ k then (Λ k : ℝ) / Real.sqrt k else 0 : ℝ) : ℂ) *
        (Zeta23.EF.weilTest (cx (scaleShift (Real.log m) f)) (cx (scaleShift (Real.log n) f))
            (Real.log k) +
          Zeta23.EF.weilTest (cx (scaleShift (Real.log m) f)) (cx (scaleShift (Real.log n) f))
            (-Real.log k))).re := by
    intro m n k
    have hw : 0 ≤ (if 2 ≤ k then (Λ k : ℝ) / Real.sqrt k else 0 : ℝ) := by
      split_ifs with hk
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
      · exact le_rfl
    have hk_nn : ∀ x : ℝ, 0 ≤
        (Zeta23.EF.weilTest (cx (scaleShift (Real.log m) f)) (cx (scaleShift (Real.log n) f))
          x).re := by
      intro x
      rw [weilTest_ofReal, Complex.ofReal_re]
      exact integral_nonneg fun u => mul_nonneg (hf_nn _) (hf_nn _)
    rw [Complex.re_ofReal_mul, Complex.add_re]
    exact mul_nonneg hw (add_nonneg (hk_nn _) (hk_nn _))
  have hsum_prime : ∀ m n : ℕ, Summable fun k : ℕ =>
      (((if 2 ≤ k then (Λ k : ℝ) / Real.sqrt k else 0 : ℝ) : ℂ) *
        (Zeta23.EF.weilTest (cx (scaleShift (Real.log m) f)) (cx (scaleShift (Real.log n) f))
            (Real.log k) +
          Zeta23.EF.weilTest (cx (scaleShift (Real.log m) f)) (cx (scaleShift (Real.log n) f))
            (-Real.log k))).re := fun m n =>
    Complex.reCLM.summable (RHTower.summable_primeAtoms _ (Zeta23.EF.weilTest_hasCompactSupport
      (cx_hasCompactSupport (scaleShift_mem (Real.log m) hf).2)
      (cx_hasCompactSupport (scaleShift_mem (Real.log n) hf).2)))
  have hdiag_nonpos : ∀ n : ℕ, smoothedPrimeKernel f n n ≤ 0 := by
    intro n
    rw [smoothedPrimeKernel, FrustratedArithmeticDirichletForms.weightedPrimePart,
      Complex.re_tsum (RHTower.summable_primeAtoms _ (Zeta23.EF.weilTest_hasCompactSupport
        (cx_hasCompactSupport (scaleShift_mem (Real.log n) hf).2)
        (cx_hasCompactSupport (scaleShift_mem (Real.log n) hf).2)))]
    exact neg_nonpos.mpr (tsum_nonneg (hterm_nn n n))
  -- Off-diagonal `(2, 1)` and `(1, 2)` hit the `k = 2` bullseye with positive mass `‖f‖₂²`
  have hoff_neg : smoothedPrimeKernel f 2 1 < 0 ∧ smoothedPrimeKernel f 1 2 < 0 := by
    have hc_pos : 0 < Real.log 2 / Real.sqrt 2 * ∫ u, f u ^ 2 :=
      mul_pos (div_pos (Real.log_pos one_lt_two) (Real.sqrt_pos.mpr two_pos)) hf_sq_pos
    have hk0 : (Zeta23.EF.weilTest (cx f) (cx f) 0).re = ∫ u, f u ^ 2 := by
      rw [weilTest_ofReal, Complex.ofReal_re]
      exact integral_congr_ae (Eventually.of_forall fun u => by rw [sub_zero, sq])
    constructor
    · rw [smoothedPrimeKernel, FrustratedArithmeticDirichletForms.weightedPrimePart,
        Complex.re_tsum (RHTower.summable_primeAtoms _ (Zeta23.EF.weilTest_hasCompactSupport
          (cx_hasCompactSupport (scaleShift_mem (Real.log (2 : ℕ)) hf).2)
          (cx_hasCompactSupport (scaleShift_mem (Real.log (1 : ℕ)) hf).2)))]
      have h2 := Summable.le_tsum (hsum_prime 2 1) 2 (fun k _ => hterm_nn 2 1 k)
      have h2_val : Real.log 2 / Real.sqrt 2 * (∫ u, f u ^ 2) ≤
          (((if 2 ≤ (2 : ℕ) then (Λ 2 : ℝ) / Real.sqrt (2 : ℕ) else 0 : ℝ) : ℂ) *
            (Zeta23.EF.weilTest (cx (scaleShift (Real.log (2 : ℕ)) f))
                (cx (scaleShift (Real.log (1 : ℕ)) f)) (Real.log (2 : ℕ)) +
              Zeta23.EF.weilTest (cx (scaleShift (Real.log (2 : ℕ)) f))
                (cx (scaleShift (Real.log (1 : ℕ)) f)) (-Real.log (2 : ℕ)))).re := by
        rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
          Complex.re_ofReal_mul, Complex.add_re, weilTest_scaleShift, Nat.cast_one, Real.log_one,
          add_zero, sub_self, hk0]
        have hother : 0 ≤ (Zeta23.EF.weilTest (cx (scaleShift (Real.log (2 : ℕ)) f))
            (cx (scaleShift (Real.log (1 : ℕ)) f)) (-Real.log (2 : ℕ))).re := by
          rw [weilTest_ofReal, Complex.ofReal_re]
          exact integral_nonneg fun u => mul_nonneg (hf_nn _) (hf_nn _)
        have hw : 0 ≤ Real.log 2 / Real.sqrt (2 : ℕ) :=
          div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
        push_cast at hw ⊢
        nlinarith
      linarith
    · rw [smoothedPrimeKernel, FrustratedArithmeticDirichletForms.weightedPrimePart,
        Complex.re_tsum (RHTower.summable_primeAtoms _ (Zeta23.EF.weilTest_hasCompactSupport
          (cx_hasCompactSupport (scaleShift_mem (Real.log (1 : ℕ)) hf).2)
          (cx_hasCompactSupport (scaleShift_mem (Real.log (2 : ℕ)) hf).2)))]
      have h2 := Summable.le_tsum (hsum_prime 1 2) 2 (fun k _ => hterm_nn 1 2 k)
      have h2_val : Real.log 2 / Real.sqrt 2 * (∫ u, f u ^ 2) ≤
          (((if 2 ≤ (2 : ℕ) then (Λ 2 : ℝ) / Real.sqrt (2 : ℕ) else 0 : ℝ) : ℂ) *
            (Zeta23.EF.weilTest (cx (scaleShift (Real.log (1 : ℕ)) f))
                (cx (scaleShift (Real.log (2 : ℕ)) f)) (Real.log (2 : ℕ)) +
              Zeta23.EF.weilTest (cx (scaleShift (Real.log (1 : ℕ)) f))
                (cx (scaleShift (Real.log (2 : ℕ)) f)) (-Real.log (2 : ℕ)))).re := by
        rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
          Complex.re_ofReal_mul, Complex.add_re,
          weilTest_scaleShift (Real.log (1 : ℕ)) (Real.log (2 : ℕ)) f f (-Real.log (2 : ℕ)),
          Nat.cast_one, Real.log_one, sub_zero, neg_add_cancel, hk0]
        have hother : 0 ≤ (Zeta23.EF.weilTest (cx (scaleShift (Real.log (1 : ℕ)) f))
            (cx (scaleShift (Real.log (2 : ℕ)) f)) (Real.log (2 : ℕ))).re := by
          rw [weilTest_ofReal, Complex.ofReal_re]
          exact integral_nonneg fun u => mul_nonneg (hf_nn _) (hf_nn _)
        have hw : 0 ≤ Real.log 2 / Real.sqrt (2 : ℕ) :=
          div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
        push_cast at hw ⊢
        nlinarith
      linarith
  rintro ⟨K, hpsd, hlim⟩
  have hpair_pos : ∀ k ∈ ({1, 2} : Finset ℕ), 0 < k := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  have htend : Tendsto (fun r => ∑ m ∈ ({1, 2} : Finset ℕ), ∑ n ∈ ({1, 2} : Finset ℕ),
      (1 : ℝ) * 1 * K r m n) (𝓝[<] 1)
      (𝓝 (∑ m ∈ ({1, 2} : Finset ℕ), ∑ n ∈ ({1, 2} : Finset ℕ),
        (1 : ℝ) * 1 * smoothedPrimeKernel f m n)) :=
    tendsto_finset_sum _ fun m hm => tendsto_finset_sum _ fun n hn =>
      (hlim m n (hpair_pos m hm) (hpair_pos n hn)).const_mul _
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      0 ≤ ∑ m ∈ ({1, 2} : Finset ℕ), ∑ n ∈ ({1, 2} : Finset ℕ), (1 : ℝ) * 1 * K r m n := by
    filter_upwards [Ico_mem_nhdsLT zero_lt_one] with r hr
    exact hpsd r hr.1 hr.2 {1, 2} hpair_pos (fun _ => 1)
  haveI : (𝓝[<] (1 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
  have hge := ge_of_tendsto htend hev
  have h12 : (1 : ℕ) ≠ 2 := by omega
  simp only [Finset.sum_pair h12, one_mul] at hge
  linarith [hdiag_nonpos 1, hdiag_nonpos 2, hoff_neg.1, hoff_neg.2]

/-- **Single-channel impossibility (archimedean plus pole).** For every non-zero nonnegative test
`f ∈ realTests`, the smoothed archimedean-plus-pole kernel `smoothedArchPoleKernel f` has constant
diagonal `C_{∞, f}(1, 1)` while its off-diagonal pole term grows unboundedly with the degree ratio,
so it fails positive semidefiniteness and cannot be a counterterm-free pointwise limit of
positive-semidefinite kernels `K r` (`0 ≤ r < 1`) on `ℕ₊ × ℕ₊`. -/
theorem not_psd_limit_smoothedArchPole {f : ℝ → ℝ} (hf : f ∈ realTests) (hf_nn : ∀ u, 0 ≤ f u)
    (hf_ne : ∃ u₀, f u₀ ≠ 0) :
    ¬ ∃ K : ℝ → ℕ → ℕ → ℝ,
      (∀ r : ℝ, 0 ≤ r → r < 1 → ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n) → ∀ c : ℕ → ℝ,
        0 ≤ ∑ m ∈ S, ∑ n ∈ S, c m * c n * K r m n) ∧
      (∀ m n : ℕ, 0 < m → 0 < n →
        Tendsto (fun r => K r m n) (𝓝[<] 1) (𝓝 (smoothedArchPoleKernel f m n))) := by
  obtain ⟨u₀, hu₀⟩ := hf_ne
  have hB_pos : 0 < poleB f := by
    have he : (fun u => f u * Real.exp (-(1 / 2) * u)) = fun u => f u * Real.exp (-u / 2) := by
      funext u; congr 2; ring
    have hint := integrable_mul_exp hf (-(1 / 2))
    rw [he] at hint
    exact integral_pos_of_nonneg_nonzero
      (hf.1.continuous.mul (Real.continuous_exp.comp (continuous_id.neg.div_const 2))) hint
      (fun u => mul_nonneg (hf_nn u) (Real.exp_pos _).le)
      (mul_ne_zero hu₀ (Real.exp_pos _).ne')
  have hA_pos : 0 < poleA f := by
    have he : (fun u => f u * Real.exp ((1 / 2) * u)) = fun u => f u * Real.exp (u / 2) := by
      funext u; congr 2; ring
    have hint := integrable_mul_exp hf (1 / 2)
    rw [he] at hint
    exact integral_pos_of_nonneg_nonzero
      (hf.1.continuous.mul (Real.continuous_exp.comp (continuous_id.div_const 2))) hint
      (fun u => mul_nonneg (hf_nn u) (Real.exp_pos _).le)
      (mul_ne_zero hu₀ (Real.exp_pos _).ne')
  have hBA_pos : 0 < poleB f * poleA f := mul_pos hB_pos hA_pos
  -- Constant diagonal `C_{∞, f}(n, n) = C_{∞, f}(1, 1)` and symmetry `C_{∞, f}(1, n) = C_{∞, f}(n, 1)`
  have hdiag_eq : ∀ n : ℕ, smoothedArchPoleKernel f n n = smoothedArchPoleKernel f 1 1 := by
    intro n
    simp only [smoothedArchPoleKernel, weilTest_scaleShift_same]
  have hsymm : ∀ m n : ℕ, smoothedArchPoleKernel f m n = smoothedArchPoleKernel f n m := by
    intro m n
    rw [smoothedArchPoleKernel, smoothedArchPoleKernel,
      ← RHTower.OddResolvent.tilde_weilTest_mixed, RHTower.WeilSpectral.weilFullFunctional_tilde,
      Complex.conj_re]
  -- Uniform bound `M` on the archimedean Gamma integral across all shifts `(n, 1)`
  set k₀ := Zeta23.EF.weilTest (cx f) (cx f)
  set M := (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖Zeta23.paperFT k₀ r * (Zeta23.EF.gammaBracket r : ℂ)‖
  have hM_nn : 0 ≤ M :=
    mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  have hoff_ge : ∀ n : ℕ, 1 ≤ n →
      Real.exp (Real.log n / 2) * (poleB f * poleA f) - M ≤ smoothedArchPoleKernel f n 1 := by
    intro n _
    set fn := scaleShift (Real.log n) f
    have hfn : fn ∈ realTests := scaleShift_mem (Real.log n) hf
    set kn := Zeta23.EF.weilTest (cx fn) (cx f)
    have hkn_eq : Zeta23.EF.weilTest (cx (scaleShift (Real.log n) f))
        (cx (scaleShift (Real.log (1 : ℕ)) f)) = kn := by
      simp [kn, fn]
    -- Evaluate `weilFullFunctional 0 kn` into pole part + archimedean integral
    have hzero_sum : (∑' k : ℕ, ((if 2 ≤ k then (0 : ℝ) / Real.sqrt k else 0 : ℝ) : ℂ) *
        (kn (Real.log k) + kn (-Real.log k))) = 0 := by
      have h0 : ∀ k : ℕ, ((if 2 ≤ k then (0 : ℝ) / Real.sqrt k else 0 : ℝ) : ℂ) *
          (kn (Real.log k) + kn (-Real.log k)) = 0 := fun k => by split_ifs <;> simp
      simp [h0]
    have hW_eq : smoothedArchPoleKernel f n 1 =
        (Zeta23.paperFT kn (Complex.I / 2) + Zeta23.paperFT kn (-Complex.I / 2)).re +
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ r : ℝ, Zeta23.paperFT kn r * (Zeta23.EF.gammaBracket r : ℂ)).re := by
      rw [smoothedArchPoleKernel, hkn_eq, RHTower.weilFullFunctional, hzero_sum, sub_zero,
        Complex.add_re]
      congr 2
      push_cast; ring
    -- Pole part equals `(e^{-log n / 2} + e^{log n / 2}) * poleB f * poleA f`
    have hpFT_B : ∀ g : ℝ → ℝ, Zeta23.paperFT (cx g) (Complex.I / 2) = (poleB g : ℂ) := by
      intro g
      rw [RHTower.LebesgueAtomWeil.paperFT_I_div_two, poleB, ← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall fun u => by simp [cx])
    have hpFT_A : ∀ g : ℝ → ℝ, Zeta23.paperFT (cx g) (-Complex.I / 2) = (poleA g : ℂ) := by
      intro g
      rw [RHTower.LebesgueAtomWeil.paperFT_neg_I_div_two, poleA, ← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall fun u => by simp [cx])
    have hconj1 : conj (Complex.I / 2) = -Complex.I / 2 := by
      rw [map_div₀, Complex.conj_I, map_ofNat]
    have hconj2 : conj (-Complex.I / 2) = Complex.I / 2 := by
      rw [neg_div, map_neg, hconj1, neg_div, neg_neg]
    have hpole_eq : (Zeta23.paperFT kn (Complex.I / 2) + Zeta23.paperFT kn (-Complex.I / 2)).re =
        (Real.exp (-Real.log n / 2) + Real.exp (Real.log n / 2)) * (poleB f * poleA f) := by
      rw [Zeta23.EF.paperFT_weilTest (cx_contDiff hfn.1).continuous (cx_contDiff hf.1).continuous
          (cx_hasCompactSupport hfn.2) (cx_hasCompactSupport hf.2) (Complex.I / 2),
        Zeta23.EF.paperFT_weilTest (cx_contDiff hfn.1).continuous (cx_contDiff hf.1).continuous
          (cx_hasCompactSupport hfn.2) (cx_hasCompactSupport hf.2) (-Complex.I / 2),
        hconj1, hconj2, hpFT_B fn, hpFT_A f, hpFT_A fn, hpFT_B f]
      simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_add,
        Complex.ofReal_re, fn, poleB_scaleShift, poleA_scaleShift]
      ring
    -- Archimedean part has norm at most `M` because translation acts unitarily on real frequencies
    have hnorm_eq : ∀ r : ℝ, ‖Zeta23.paperFT kn r * (Zeta23.EF.gammaBracket r : ℂ)‖ =
        ‖Zeta23.paperFT k₀ r * (Zeta23.EF.gammaBracket r : ℂ)‖ := by
      intro r
      rw [Zeta23.EF.paperFT_weilTest (cx_contDiff hfn.1).continuous (cx_contDiff hf.1).continuous
          (cx_hasCompactSupport hfn.2) (cx_hasCompactSupport hf.2) (r : ℂ),
        Zeta23.EF.paperFT_weilTest (cx_contDiff hf.1).continuous (cx_contDiff hf.1).continuous
          (cx_hasCompactSupport hf.2) (cx_hasCompactSupport hf.2) (r : ℂ),
        Complex.conj_ofReal, paperFT_cx_scaleShift_apply]
      have hcexp_norm : ‖Complex.exp ((Real.log n : ℂ) * (Complex.I * (r : ℂ)))‖ = 1 := by
        rw [Complex.norm_exp]
        have hre : ((Real.log n : ℂ) * (Complex.I * (r : ℂ))).re = 0 := by simp
        rw [hre, Real.exp_zero]
      simp only [norm_mul, hcexp_norm, one_mul]
    have harch_le : |(((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, Zeta23.paperFT kn r * (Zeta23.EF.gammaBracket r : ℂ)).re| ≤ M := by
      rw [Complex.re_ofReal_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc |(∫ r : ℝ, Zeta23.paperFT kn r * (Zeta23.EF.gammaBracket r : ℂ)).re|
          ≤ ‖∫ r : ℝ, Zeta23.paperFT kn r * (Zeta23.EF.gammaBracket r : ℂ)‖ :=
            Complex.abs_re_le_norm _
        _ ≤ ∫ r : ℝ, ‖Zeta23.paperFT kn r * (Zeta23.EF.gammaBracket r : ℂ)‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ r : ℝ, ‖Zeta23.paperFT k₀ r * (Zeta23.EF.gammaBracket r : ℂ)‖ := by
            simp_rw [hnorm_eq]
    have hpole_ge : Real.exp (Real.log n / 2) * (poleB f * poleA f) ≤
        (Real.exp (-Real.log n / 2) + Real.exp (Real.log n / 2)) * (poleB f * poleA f) := by
      have : 0 < Real.exp (-Real.log n / 2) := Real.exp_pos _
      nlinarith
    have harch_lo : -M ≤ (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ, Zeta23.paperFT kn r * (Zeta23.EF.gammaBracket r : ℂ)).re :=
      (abs_le.mp harch_le).1
    rw [hW_eq, hpole_eq]
    linarith
  -- Choose `n ≥ 2` large enough that `smoothedArchPoleKernel f n 1 > smoothedArchPoleKernel f 1 1`
  set C₀ := smoothedArchPoleKernel f 1 1
  set R := max 1 ((|C₀| + M + 1) / (poleB f * poleA f))
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set n := ⌈Real.exp (2 * R)⌉₊ + 2
  have hn_gt1 : 1 < n := by omega
  have h1_ne : (1 : ℕ) ≠ n := hn_gt1.ne
  have hn_gt_exp : Real.exp (2 * R) < n := by
    have h1 : Real.exp (2 * R) ≤ ⌈Real.exp (2 * R)⌉₊ := Nat.le_ceil _
    push_cast [n]
    linarith
  have hlog_gt : 2 * R < Real.log n :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr hn_gt_exp
  have hexp_gt_R : R < Real.exp (Real.log n / 2) := by
    calc R < R + 1 := lt_add_one R
      _ ≤ Real.exp R := by linarith [Real.add_one_le_exp R]
      _ < Real.exp (Real.log n / 2) := Real.exp_lt_exp.mpr (by linarith)
  have hR_ge : (|C₀| + M + 1) / (poleB f * poleA f) ≤ R := le_max_right _ _
  have hprod_gt : |C₀| + M + 1 < Real.exp (Real.log n / 2) * (poleB f * poleA f) := by
    have h1 := (div_le_iff₀ hBA_pos).mp hR_ge
    nlinarith
  have hoff_gt : C₀ < smoothedArchPoleKernel f n 1 := by
    have hlo := hoff_ge n (by omega)
    have habs : C₀ ≤ |C₀| := le_abs_self C₀
    linarith
  rintro ⟨K, hpsd, hlim⟩
  have hpair_pos : ∀ k ∈ ({1, n} : Finset ℕ), 0 < k := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk'
    · exact Nat.one_pos
    · rw [Finset.mem_singleton.mp hk']; omega
  let c : ℕ → ℝ := fun k => if k = 1 then 1 else -1
  have htend : Tendsto (fun r => ∑ i ∈ ({1, n} : Finset ℕ), ∑ j ∈ ({1, n} : Finset ℕ),
      c i * c j * K r i j) (𝓝[<] 1)
      (𝓝 (∑ i ∈ ({1, n} : Finset ℕ), ∑ j ∈ ({1, n} : Finset ℕ),
        c i * c j * smoothedArchPoleKernel f i j)) :=
    tendsto_finset_sum _ fun i hi => tendsto_finset_sum _ fun j hj =>
      (hlim i j (hpair_pos i hi) (hpair_pos j hj)).const_mul _
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      0 ≤ ∑ i ∈ ({1, n} : Finset ℕ), ∑ j ∈ ({1, n} : Finset ℕ), c i * c j * K r i j := by
    filter_upwards [Ico_mem_nhdsLT zero_lt_one] with r hr
    exact hpsd r hr.1 hr.2 {1, n} hpair_pos c
  haveI : (𝓝[<] (1 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
  have hge := ge_of_tendsto htend hev
  simp only [c, Finset.sum_pair h1_ne, ↓reduceIte, h1_ne.symm, hdiag_eq n, hsymm 1 n] at hge
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ



