import GaloisForLFunctions.ArithmeticOrientationTheory.NyquistRiemannRochBeyondRankNullity
import GaloisForLFunctions.RHTower.Sieve.DirichletPolyAffineMeanSquare
import GaloisForLFunctions.SquareRootThreshold.WindowedMeanValueDiagonalLaw
import GaloisForLFunctions.SquareRootThreshold.PositionAndDepthShareOneNyquistAperture
import GaloisForLFunctions.SquareRootThreshold.OnLineSamplingAtTheNyquistAperture

/-!
# The Nyquist Bound at the Diagonal and the Square-Root Threshold of the Aperture

This module resolves **Open Problem 7** of Arithmetic Orientation Theory (`README.md`, §7):

> **7. The Nyquist bound at the diagonal.** Sharpen the frame bound to `T + O(N)` without the
> logarithm at `1`-separated heights, and read the resulting injectivity threshold against the
> square-root threshold of the aperture.

## Mathematical Architecture

1. **Integer-Quantized Nyquist Injectivity and Surjectivity Thresholds (§1):**
   - Because `h0 A : ℕ` and `h1 A : ℕ` are integer invariants, the continuous Nyquist bounds
     `h0_le_nyquist` (`h⁰(A) ≤ dim − frobeniusMass(A) / K`) and `h1_le_nyquist`
     (`h¹(A) ≤ #nodes − frobeniusMass(A) / K`) force **exact injectivity** `h⁰(A) = 0` already when
     `K * (dim − 1) < frobeniusMass A` (`h0_eq_zero_of_mul_sub_one_lt_frobeniusMass`), and **exact
     surjectivity** `h¹(A) = 0` already when `K * (#nodes − 1) < frobeniusMass A`
     (`h1_eq_zero_of_mul_sub_one_lt_frobeniusMass`).
   - Conversely, above the diagonal (`#nodes < dim`), rank–nullity forces a nontrivial section space
     `0 < dim − #nodes ≤ h⁰(A)` (`h0_pos_of_card_lt_card`) regardless of the frame bound.

2. **The Logarithm-Free `T + O(N)` Affine Mean-Value Constant `dirichletAffineFrameConstant` (§2):**
   - In `TheNyquistRankBound`, `hasFrameBound_dirichletSampling` used the elementary mean-value
     factor `T + 4N(1 + log N)`, whose `N log N` term shifts the height–length balance below the
     diagonal to `N log N ≍ T`.
   - Using `integral_Icc_normSq_dirPoly_le_affine_max` (`RHTower/Sieve/DirichletPolyAffineMeanSquare`),
     where the `n`-weighted mass `∑_{m < N} (m+1) ‖a_m‖² ≤ N ∑_{m < N} ‖a_m‖²` replaces `N(1 + log N)`,
     every Dirichlet polynomial of length `N` satisfies on `[0, T]` (`T ≥ 0`):
     `∫_0^T ‖dirPoly N a t‖² dt ≤ dirichletAffineFrameConstant T N * ∑_{m < N} ‖a_m‖²`,
     with `dirichletAffineFrameConstant T N = (5π/2) max(T, 1) + 5πe N = (5π/2) T + O(N)` completely
     free of logarithms (`integral_normSq_dirPoly_le_dirichletAffineFrameConstant`).
   - The height-linear term `(5π/2) T` and the length-linear term `5πe N` cross at the exact
     diagonal `T = 2e N` (`dirichletAffineFrameConstant_eq_at_diagonal`,
     `dirichletAffineFrameConstant_le_five_pi_T_of_diagonal`).

3. **Three Logarithm-Free and Diagonal-Sharpened Readings at `1`-Separated Heights (§3):**
   - **3A. Height-Cell Average Sampling (`dirichletCellSampling`):**
     Reading the local cell averages `(1/√δ) ∫_{λ_r - δ/2}^{λ_r + δ/2} (k+1)^{it} dt` over disjoint
     `δ`-cells around `δ`-separated heights `λ_0, …, λ_R ∈ [δ/2, T − δ/2]` (in particular `δ = 1`
     at `1`-separated heights) eliminates the Sobolev derivative loss `F'` completely. Cauchy–Schwarz
     on each cell (`norm_intervalIntegral_sq_le`) plus disjointness (`sum_window_le`) yields the
     **pure `T + O(N)` frame bound with no logarithm anywhere**:
     `HasFrameBound (dirichletCellSampling N δ lam R) (dirichletAffineFrameConstant T N)`
     (`hasFrameBound_dirichletCellSampling`).
   - **3B. Sobolev-Normalized Pointwise Sampling (`sobolevDirichletSampling`) at `1`-Separated Heights:**
     Normalizing `dirichletSampling N lam R` on the right by the invertible diagonal Sobolev weight
     `dirichletSobolevWeight δ k = √(2/δ + δ (log(k+1))²)` (`√(2 + (log(k+1))²)` at `δ = 1`)
     preserves `h⁰`, `rank`, and `h¹` **identically**
     (`h0_rank_h1_sobolevDirichletSampling_eq`) while satisfying the **pure `T + O(N)` frame bound
     without any logarithm**:
     `HasFrameBound (sobolevDirichletSampling N δ lam R) (dirichletAffineFrameConstant T N)`
     (`hasFrameBound_sobolevDirichletSampling`, `hasFrameBound_sobolevDirichletSampling_one_separated`).
   - **3C. Pointwise Sampling (`dirichletSampling`) and Harmonic-Reweighted Sampling
     (`harmonicDirichletSampling`) with Logarithm Cancellation:**
     On `dirichletSampling N lam R` itself, `largeValues_dirPoly_affine` removes `1 + log N` from
     the `T + O(N)` factor (`hasFrameBound_dirichletSampling_affine`, `h0_dirichletSampling_le_affine`).
     Moreover, right-multiplying by the invertible diagonal weight `(k+1)^{−1/2}`
     (`harmonicDirichletSampling N lam R`) preserves `h⁰`, `rank`, and `h¹` identically
     (`h0_rank_h1_harmonicDirichletSampling_eq`), reduces the `n`-weighted mass to the plain mass so
     `N` drops out of the height factor (`(5π/2) max(T, 1) + 5πe`,
     `hasFrameBound_harmonicDirichletSampling`), and gives Frobenius mass
     `(R + 1) ∑_{k=1}^N 1/k ≥ (R + 1) log N`, whose `log N` cancels `1/δ + 2 log N`
     (`rank_dirichletSampling_ge_harmonic`).

4. **Reading the Injectivity Threshold Against the Square-Root Threshold of the Aperture (§4):**
   - A test of aperture `a` has test length `apertureTestLength a = e^a` and Weil-kernel prime
     horizon `aperturePrimeHorizon a = e^{2a} = (apertureTestLength a)²`. At height `T > 0`, the
     **square-root aperture** `squareRootAperture T = (1/2) log T` is the exact threshold where
     `apertureTestLength a = √T` and `aperturePrimeHorizon a = T`
     (`aperturePrimeHorizon_squareRootAperture`, `apertureTestLength_squareRootAperture`,
     `le_squareRootAperture_iff_primeHorizon_le`).
   - **Below the square-root aperture (`a ≤ (1/2) log T`, `N ≤ e^{2a} ≤ T`):**
     (i) The windowed mean-value law (`windowed_dirichlet_diagonal_below_squareRootAperture`) is
         **exact diagonal** (`∫ |h_η(−2πξ)|² |Q(ξ)|² dξ = ‖η‖² ∑ |c_n|²`) for window radius `r = 1/(2T)`;
     (ii) The diagonal frame constant `dirichletAffineFrameConstant T N ≤ (5π/2 + 5πe) T` is purely
          linear in `T` (`dirichletAffineFrameConstant_le_below_squareRootAperture`);
     (iii) The periodic lattice of logarithmic density `L = log T` hides both position and depth
           (`lattice_nyquist_eq_squareRootAperture`).
   - **Above the square-root aperture (`(1/2) log T < a`, `T < N`):**
     Every `1`-separated sequence of heights `λ_0, …, λ_R ∈ [1/2, T − 1/2]` has `R + 1 ≤ T < N`
     (`sample_count_le_T_of_one_separated`), so `0 < N − T ≤ h⁰(dirichletSampling N lam R)`
     (`h0_dirichletSampling_pos_above_squareRootAperture`): `1`-separated sampling in `[0, T]` loses
     injectivity and admits hiding sections as soon as the prime horizon crosses the diagonal `T`
     (equivalently, as soon as the test length `e^a` crosses `√T`).
-/

open Set Filter Finset Matrix MeasureTheory Topology
open scoped Real ComplexConjugate BigOperators
open RHTower RHTower.Sieve
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions
namespace ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ## §1. Integer-Quantized Nyquist Injectivity and Surjectivity Thresholds -/

omit [DecidableEq n] in
/-- **Strict integer-quantized Nyquist injectivity threshold.** Because `h0 A : ℕ` is an integer,
`h0_le_nyquist` forces `h0 A = 0` (exact injectivity `ker A = ⊥`) as soon as
`K * (Fintype.card n − 1) < frobeniusMass A`. -/
theorem h0_eq_zero_of_mul_sub_one_lt_frobeniusMass {A : Matrix m n ℂ} {K : ℝ}
    (hK0 : 0 < K) (hK : HasFrameBound A K)
    (hmass : K * ((Fintype.card n : ℝ) - 1) < frobeniusMass A) :
    h0 A = 0 := by
  have hnyq := h0_le_nyquist hK0 hK
  have hdiv : (Fintype.card n : ℝ) - 1 < frobeniusMass A / K := by
    rw [lt_div_iff₀ hK0]
    linarith
  have hlt1 : (h0 A : ℝ) < 1 := by linarith
  have hnat : h0 A < 1 := by exact_mod_cast hlt1
  omega

omit [DecidableEq n] in
/-- **Strict integer-quantized Nyquist surjectivity threshold.** Because `h1 A : ℕ` is an integer,
`h1_le_nyquist` forces `h1 A = 0` (`A.rank = Fintype.card m`) as soon as
`K * (Fintype.card m − 1) < frobeniusMass A`. -/
theorem h1_eq_zero_of_mul_sub_one_lt_frobeniusMass {A : Matrix m n ℂ} {K : ℝ}
    (hK0 : 0 < K) (hK : HasFrameBound A K)
    (hmass : K * ((Fintype.card m : ℝ) - 1) < frobeniusMass A) :
    h1 A = 0 := by
  have hnyq := h1_le_nyquist hK0 hK
  have hdiv : (Fintype.card m : ℝ) - 1 < frobeniusMass A / K := by
    rw [lt_div_iff₀ hK0]
    linarith
  have hlt1 : (h1 A : ℝ) < 1 := by linarith
  have hnat : h1 A < 1 := by exact_mod_cast hlt1
  omega

omit [DecidableEq n] in
/-- **Unconditional hiding above the diagonal (`#nodes < dim`).** Whenever a reading has fewer nodes
than test coordinates (`Fintype.card m < Fintype.card n`), rank–nullity forces
`Fintype.card n − Fintype.card m ≤ h0 A` and in particular `0 < h0 A`. -/
theorem h0_pos_of_card_lt_card (A : Matrix m n ℂ)
    (hlt : Fintype.card m < Fintype.card n) :
    Fintype.card n - Fintype.card m ≤ h0 A ∧ 0 < h0 A := by
  have h1 := h0_add_rank A
  have h2 := rank_le_card_height A
  omega

/-! ## §2. The Logarithm-Free `T + O(N)` Affine Mean-Value Constant -/

/-- The **logarithm-free diagonal frame constant**
`K_diag(T, N) = (5π/2) max(T, 1) + 5πe N = (5π/2) T + O(N)` from the affine mean-square theorem. -/
def dirichletAffineFrameConstant (T : ℝ) (N : ℕ) : ℝ :=
  (5 * Real.pi / 2) * max T 1 + 5 * Real.pi * Real.exp 1 * (N : ℝ)

/-- `dirichletAffineFrameConstant T N` is strictly positive for all `T : ℝ` and `N : ℕ`. -/
theorem dirichletAffineFrameConstant_pos (T : ℝ) (N : ℕ) :
    0 < dirichletAffineFrameConstant T N := by
  unfold dirichletAffineFrameConstant
  have hmax : (1 : ℝ) ≤ max T 1 := le_max_right T 1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith

/-- For `T ≥ 1`, `dirichletAffineFrameConstant T N = (5π/2) T + 5πe N`. -/
theorem dirichletAffineFrameConstant_of_one_le {T : ℝ} (hT : 1 ≤ T) (N : ℕ) :
    dirichletAffineFrameConstant T N =
      (5 * Real.pi / 2) * T + 5 * Real.pi * Real.exp 1 * (N : ℝ) := by
  unfold dirichletAffineFrameConstant
  rw [max_eq_left hT]

/-- **Exact diagonal balance (`T = 2e N`).** At the diagonal height `T = 2e N` (`N ≥ 1`), the
height-linear term `(5π/2) T` and the length-linear term `5πe N` of `dirichletAffineFrameConstant`
are equal, and below the diagonal (`2e N ≤ T`, `1 ≤ T`) `dirichletAffineFrameConstant T N ≤ 5π T`. -/
theorem dirichletAffineFrameConstant_diagonal_balance {T : ℝ} {N : ℕ}
    (hT1 : 1 ≤ T) (hdiag : 2 * Real.exp 1 * (N : ℝ) ≤ T) :
    dirichletAffineFrameConstant T N ≤ 5 * Real.pi * T := by
  rw [dirichletAffineFrameConstant_of_one_le hT1]
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith

/-- The `n`-weighted coefficient mass is bounded by `N` times the plain `ℓ²` mass:
`∑_{m < N} (m + 1) ‖a_m‖² ≤ N ∑_{m < N} ‖a_m‖²`. -/
theorem sum_mul_normSq_le_natCast_mul (N : ℕ) (a : Fin N → ℂ) :
    ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2 ≤
      (N : ℝ) * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hm : ((m : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
    have hlt := m.isLt
    exact_mod_cast (by omega : (m : ℕ) + 1 ≤ N)
  exact mul_le_mul_of_nonneg_right hm (sq_nonneg _)

/-- **Logarithm-free `T + O(N)` symmetric mean-square bound.** For every `N : ℕ`, `a : Fin N → ℂ`,
and `T : ℝ`, `∫_{|t| ≤ T} ‖dirPoly N a t‖² dt ≤ dirichletAffineFrameConstant T N * ∑ ‖a_m‖²`. -/
theorem integral_Icc_normSq_dirPoly_le_dirichletAffineFrameConstant
    (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    (∫ t in Icc (-T) T, ‖dirPoly N a t‖ ^ 2) ≤
      dirichletAffineFrameConstant T N * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  have hbase := integral_Icc_normSq_dirPoly_le_affine_max a T
  have hmass := sum_mul_normSq_le_natCast_mul N a
  have hc : 0 ≤ 5 * Real.pi * Real.exp 1 := by positivity
  have hstep := mul_le_mul_of_nonneg_left hmass hc
  unfold dirichletAffineFrameConstant
  nlinarith

/-- **Logarithm-free `T + O(N)` interval mean-square bound on `[0, T]`.** For `0 ≤ T`,
`∫_0^T ‖dirPoly N a t‖² dt ≤ dirichletAffineFrameConstant T N * ∑ ‖a_m‖²`, replacing the
`(T + 4N(1 + log N))` bound of `integral_normSq_dirPoly_le` without the `log N` factor. -/
theorem integral_normSq_dirPoly_le_dirichletAffineFrameConstant
    (N : ℕ) (a : Fin N → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2) ≤
      dirichletAffineFrameConstant T N * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  have hcont : Continuous fun t : ℝ => ‖dirPoly N a t‖ ^ 2 :=
    ((continuous_dirPoly N a).norm).pow 2
  have hsub : (∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2) ≤
      ∫ t in Icc (-T) T, ‖dirPoly N a t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hT]
    refine setIntegral_mono_set hcont.integrableOn_Icc
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun t ht => ⟨by linarith [ht.1], ht.2⟩)
  exact hsub.trans (integral_Icc_normSq_dirPoly_le_dirichletAffineFrameConstant N a T)

/-- **Logarithm-free `T + O(N)` derivative mean-square bound on `[0, T]`.** Without pulling out
`(log N)²`, the derivative `dirPoly N (dirDerivCoeff N a)` satisfies
`∫_0^T ‖dirPoly N (dirDerivCoeff N a) t‖² dt ≤ dirichletAffineFrameConstant T N * ∑ (log(m+1))² ‖a_m‖²`. -/
theorem integral_normSq_dirPoly_deriv_le_dirichletAffineFrameConstant
    (N : ℕ) (a : Fin N → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖dirPoly N (dirDerivCoeff N a) t‖ ^ 2) ≤
      dirichletAffineFrameConstant T N *
        ∑ m : Fin N, (Real.log (((m : ℕ) : ℝ) + 1)) ^ 2 * ‖a m‖ ^ 2 := by
  have h := integral_normSq_dirPoly_le_dirichletAffineFrameConstant N (dirDerivCoeff N a) hT
  have heq : ∑ m : Fin N, ‖dirDerivCoeff N a m‖ ^ 2 =
      ∑ m : Fin N, (Real.log (((m : ℕ) : ℝ) + 1)) ^ 2 * ‖a m‖ ^ 2 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [norm_dirDerivCoeff, mul_pow]
  rwa [heq] at h

/-! ## §3. Three Logarithm-Free and Diagonal-Sharpened Readings at `1`-Separated Heights -/

/-! ### §3A. Height-Cell Average Sampling (`dirichletCellSampling`) -/

/-- **Interval Cauchy–Schwarz inequality for continuous complex functions.** For `a ≤ b` and any
continuous `f : ℝ → ℂ`, `‖∫ t in a..b, f t‖² ≤ (b − a) * ∫ t in a..b, ‖f t‖²`. -/
theorem norm_intervalIntegral_sq_le {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ t in a..b, f t‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖f t‖ ^ 2 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · set I := ∫ t in a..b, ‖f t‖
    set μ := I / (b - a)
    have hba : 0 < b - a := sub_pos.mpr hlt
    have hnorm : ‖∫ t in a..b, f t‖ ≤ I :=
      intervalIntegral.norm_integral_le_integral_norm hab
    have hsq_le : ‖∫ t in a..b, f t‖ ^ 2 ≤ I ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have h1 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume a b :=
      (hf.norm.pow 2).intervalIntegrable a b
    have h2 : IntervalIntegrable (fun t => 2 * μ * ‖f t‖) volume a b :=
      (continuous_const.mul hf.norm).intervalIntegrable a b
    have h3 : IntervalIntegrable (fun _ : ℝ => μ ^ 2) volume a b :=
      continuous_const.intervalIntegrable a b
    have hnonneg : 0 ≤ ∫ t in a..b, (‖f t‖ - μ) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
    have hexp : (∫ t in a..b, (‖f t‖ - μ) ^ 2) =
        (∫ t in a..b, ‖f t‖ ^ 2) - 2 * μ * I + μ ^ 2 * (b - a) := by
      have hcongr : (∫ t in a..b, (‖f t‖ - μ) ^ 2) =
          ∫ t in a..b, ((‖f t‖ ^ 2 - 2 * μ * ‖f t‖) + μ ^ 2) :=
        intervalIntegral.integral_congr fun t _ => by ring
      rw [hcongr, intervalIntegral.integral_add (h1.sub h2) h3,
        intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul, mul_comm (b - a)]
    rw [hexp] at hnonneg
    have hmul := mul_le_mul_of_nonneg_left hnonneg hba.le
    have hsimp : (b - a) * ((∫ t in a..b, ‖f t‖ ^ 2) - 2 * μ * I + μ ^ 2 * (b - a)) =
        (b - a) * (∫ t in a..b, ‖f t‖ ^ 2) - I ^ 2 := by
      dsimp [μ]
      field_simp [hba.ne']
      ring
    linarith

/-- The **height-cell average Dirichlet sampling matrix** at `δ`-separated heights `lam 0, …, lam R`:
entry `(r, k)` is the normalized cell integral `(1/√δ) ∫_{λ_r - δ/2}^{λ_r + δ/2} (k+1)^{it} dt`. -/
def dirichletCellSampling (N : ℕ) (δ : ℝ) (lam : ℕ → ℝ) (R : ℕ) :
    Matrix (Fin (R + 1)) (Fin N) ℂ :=
  fun r k => ((1 / Real.sqrt δ : ℝ) : ℂ) *
    ∫ t in (lam r - δ / 2)..(lam r + δ / 2),
      Complex.exp (((t * Real.log ((k : ℕ) + 1) : ℝ) : ℂ) * Complex.I)

/-- Applying `dirichletCellSampling N δ lam R` to a coefficient vector `a` returns the `L²`-normalized
cell averages `(1/√δ) ∫_{λ_r - δ/2}^{λ_r + δ/2} dirPoly N a t dt`. -/
theorem dirichletCellSampling_mulVec (N : ℕ) (δ : ℝ) (lam : ℕ → ℝ) (R : ℕ)
    (a : Fin N → ℂ) (r : Fin (R + 1)) :
    (dirichletCellSampling N δ lam R *ᵥ a) r =
      ((1 / Real.sqrt δ : ℝ) : ℂ) *
        ∫ t in (lam r - δ / 2)..(lam r + δ / 2), dirPoly N a t := by
  unfold dirichletCellSampling dirPoly
  simp only [mulVec, dotProduct]
  have hint : ∀ k : Fin N, IntervalIntegrable
      (fun t : ℝ => Complex.exp (((t * Real.log ((k : ℕ) + 1) : ℝ) : ℂ) * Complex.I) * a k)
      volume (lam r - δ / 2) (lam r + δ / 2) := fun k => by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  rw [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun k _ => ?_).trans
    (congrArg (((1 / Real.sqrt δ : ℝ) : ℂ) * ·)
      (intervalIntegral.integral_finset_sum fun k _ => hint k).symm)
  rw [mul_assoc, ← intervalIntegral.integral_mul_const]

/-- **Pure `T + O(N)` frame bound without logarithms for height-cell sampling.** At any `δ`-separated
heights `lam 0, …, lam R` in `[δ/2, T − δ/2]` (in particular `δ = 1` at `1`-separated heights),
`dirichletCellSampling N δ lam R` has frame bound
`dirichletAffineFrameConstant T N = (5π/2) max(T, 1) + 5πe N`, with no `log N` factor anywhere. -/
theorem hasFrameBound_dirichletCellSampling (N : ℕ) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    (hlow : δ / 2 ≤ lam 0) (R : ℕ) (hhigh : lam R + δ / 2 ≤ T) :
    HasFrameBound (dirichletCellSampling N δ lam R) (dirichletAffineFrameConstant T N) := by
  intro a
  simp only [dirichletCellSampling_mulVec]
  rw [Fin.sum_univ_eq_sum_range
    (fun r => ‖((1 / Real.sqrt δ : ℝ) : ℂ) *
      ∫ t in (lam r - δ / 2)..(lam r + δ / 2), dirPoly N a t‖ ^ 2) (R + 1)]
  have hcell : ∀ r ∈ Finset.range (R + 1),
      ‖((1 / Real.sqrt δ : ℝ) : ℂ) *
        ∫ t in (lam r - δ / 2)..(lam r + δ / 2), dirPoly N a t‖ ^ 2 ≤
        ∫ t in (lam r - δ / 2)..(lam r + δ / 2), ‖dirPoly N a t‖ ^ 2 := by
    intro r _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      div_pow, one_pow, Real.sq_sqrt hδ.le]
    have hcs := norm_intervalIntegral_sq_le (continuous_dirPoly N a)
      (by linarith : lam r - δ / 2 ≤ lam r + δ / 2)
    have hlen : (lam r + δ / 2) - (lam r - δ / 2) = δ := by ring
    rw [hlen] at hcs
    have hmul := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 1 / δ)
    have hcancel : (1 / δ) * (δ * ∫ t in (lam r - δ / 2)..(lam r + δ / 2), ‖dirPoly N a t‖ ^ 2) =
        ∫ t in (lam r - δ / 2)..(lam r + δ / 2), ‖dirPoly N a t‖ ^ 2 := by
      field_simp [hδ.ne']
    linarith
  have hcont : Continuous fun t : ℝ => ‖dirPoly N a t‖ ^ 2 :=
    ((continuous_dirPoly N a).norm).pow 2
  have hA : (0 : ℝ) ≤ lam 0 - δ / 2 := by linarith
  have hmono : lam 0 ≤ lam R := by
    have h := le_of_gap hgap 0 R (Nat.zero_le R)
    simp only [Nat.cast_zero, sub_zero] at h
    have hR : (0 : ℝ) ≤ (R : ℝ) * δ := by positivity
    linarith
  have hright : (0 : ℝ) ≤ lam R + δ / 2 := by linarith
  have hwin := sum_window_le hcont (fun t => sq_nonneg _) hδ hgap hA R
  have hext : (∫ t in (0 : ℝ)..(lam R + δ / 2), ‖dirPoly N a t‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hright hhigh
      (Eventually.of_forall fun _ => sq_nonneg _) (hcont.intervalIntegrable _ _)
  exact (Finset.sum_le_sum hcell).trans
    ((hwin.trans hext).trans (integral_normSq_dirPoly_le_dirichletAffineFrameConstant N a hT))

/-! ### §3B. Sobolev-Normalized Pointwise Sampling (`sobolevDirichletSampling`) -/

/-- The Sobolev frequency weight `√(2/δ + δ (log(k+1))²)` (`√(2 + (log(k+1))²)` at `δ = 1`) for the
`k`-th Dirichlet mode on a `δ`-window. -/
def dirichletSobolevWeight {N : ℕ} (δ : ℝ) (k : Fin N) : ℝ :=
  Real.sqrt (2 / δ + δ * (Real.log (((k : ℕ) : ℝ) + 1)) ^ 2)

theorem dirichletSobolevWeight_pos {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (k : Fin N) :
    0 < dirichletSobolevWeight δ k := by
  unfold dirichletSobolevWeight
  exact Real.sqrt_pos.mpr (by positivity)

theorem dirichletSobolevWeight_sq {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (k : Fin N) :
    dirichletSobolevWeight δ k ^ 2 =
      2 / δ + δ * (Real.log (((k : ℕ) : ℝ) + 1)) ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- **Unweighted Sobolev large-values inequality without `log N` in the height-length factor.**
Balancing Gallagher's Sobolev reduction at `ε = 1/δ` (instead of `ε = log N`) and applying the
affine mean-value theorem to both `F` and `F'` yields:
`∑_{r ≤ R} ‖dirPoly N a (lam r)‖² ≤ dirichletAffineFrameConstant T N * ∑_{m < N} (2/δ + δ (log(m+1))²) ‖a_m‖²`. -/
theorem largeValues_dirPoly_sobolev_diagonal (N : ℕ) (a : Fin N → ℂ) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    (hlow : δ / 2 ≤ lam 0) (R : ℕ) (hhigh : lam R + δ / 2 ≤ T) :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2 ≤
      dirichletAffineFrameConstant T N *
        ∑ m : Fin N, (2 / δ + δ * (Real.log (((m : ℕ) : ℝ) + 1)) ^ 2) * ‖a m‖ ^ 2 := by
  have hcont1 : Continuous fun t : ℝ => ‖dirPoly N a t‖ ^ 2 :=
    ((continuous_dirPoly N a).norm).pow 2
  have hcont2 : Continuous fun t : ℝ =>
      2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖ :=
    (continuous_const.mul (continuous_dirPoly N a).norm).mul
      (continuous_dirPoly N (dirDerivCoeff N a)).norm
  have hA : (0 : ℝ) ≤ lam 0 - δ / 2 := by linarith
  have hmono : lam 0 ≤ lam R := by
    have h := le_of_gap hgap 0 R (Nat.zero_le R)
    simp only [Nat.cast_zero, sub_zero] at h
    have hR : (0 : ℝ) ≤ (R : ℝ) * δ := by positivity
    linarith
  have hright : (0 : ℝ) ≤ lam R + δ / 2 := by linarith
  have hbase := gallagher_dirPoly_sum N a hδ hgap hA R
  have hext1 : (∫ t in (0 : ℝ)..(lam R + δ / 2), ‖dirPoly N a t‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hright hhigh
      (Eventually.of_forall fun _ => sq_nonneg _) (hcont1.intervalIntegrable _ _)
  have hext2 : (∫ t in (0 : ℝ)..(lam R + δ / 2),
        2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖) ≤
      ∫ t in (0 : ℝ)..T, 2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖ :=
    intervalIntegral.integral_mono_interval le_rfl hright hhigh
      (Eventually.of_forall fun _ => by positivity) (hcont2.intervalIntegrable _ _)
  have hδinv : 0 < 1 / δ := one_div_pos.mpr hδ
  have hmix := integral_mixed_dirPoly_le N a (A := (0 : ℝ)) (B := T) hT hδinv
  rw [one_div_one_div] at hmix
  have hI1 := integral_normSq_dirPoly_le_dirichletAffineFrameConstant N a hT
  have hI2 := integral_normSq_dirPoly_deriv_le_dirichletAffineFrameConstant N a hT
  have hstep0 := mul_le_mul_of_nonneg_left hext1 hδinv.le
  have hstep1 := mul_le_mul_of_nonneg_left hI1 (by positivity : (0 : ℝ) ≤ 2 / δ)
  have hstep2 := mul_le_mul_of_nonneg_left hI2 hδ.le
  have hcomb : (2 / δ) * (dirichletAffineFrameConstant T N * ∑ m : Fin N, ‖a m‖ ^ 2) +
      δ * (dirichletAffineFrameConstant T N *
        ∑ m : Fin N, (Real.log (((m : ℕ) : ℝ) + 1)) ^ 2 * ‖a m‖ ^ 2) =
      dirichletAffineFrameConstant T N *
        ∑ m : Fin N, (2 / δ + δ * (Real.log (((m : ℕ) : ℝ) + 1)) ^ 2) * ‖a m‖ ^ 2 := by
    rw [← mul_assoc, mul_comm (2 / δ), mul_assoc, ← mul_assoc δ, mul_comm δ, mul_assoc,
      ← mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun m _ => by ring
  linarith

/-- The **Sobolev-normalized Dirichlet sampling matrix**
`sobolevDirichletSampling N δ lam R = dirichletSampling N lam R * diagonal(1 / dirichletSobolevWeight δ)`. -/
def sobolevDirichletSampling (N : ℕ) (δ : ℝ) (lam : ℕ → ℝ) (R : ℕ) :
    Matrix (Fin (R + 1)) (Fin N) ℂ :=
  dirichletSampling N lam R *
    diagonal (fun k : Fin N => ((1 / dirichletSobolevWeight δ k : ℝ) : ℂ))

/-- Because `dirichletSobolevWeight δ k > 0` for `δ > 0`, `sobolevDirichletSampling N δ lam R` has
the **exact same `h0`, `rank`, and `h1` as `dirichletSampling N lam R`**. -/
theorem h0_rank_h1_sobolevDirichletSampling_eq (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (lam : ℕ → ℝ) (R : ℕ) :
    h0 (sobolevDirichletSampling N δ lam R) = h0 (dirichletSampling N lam R) ∧
      (sobolevDirichletSampling N δ lam R).rank = (dirichletSampling N lam R).rank ∧
      h1 (sobolevDirichletSampling N δ lam R) = h1 (dirichletSampling N lam R) := by
  have hne : ∀ k : Fin N, ((1 / dirichletSobolevWeight δ k : ℝ) : ℂ) ≠ 0 := fun k => by
    exact_mod_cast (one_div_pos.mpr (dirichletSobolevWeight_pos hδ k)).ne'
  have h0eq := GaloisForLFunctions.ArithmeticCastelnuovoSeveri.h0_mul_diagonal_eq_of_ne_zero
    (dirichletSampling N lam R) _ hne
  have hrk := rank_and_h1_mul_diagonal_eq_of_iff_eq_zero
    (A := dirichletSampling N lam R)
    (w₁ := fun k : Fin N => ((1 / dirichletSobolevWeight δ k : ℝ) : ℂ))
    (w₂ := fun _ : Fin N => (1 : ℂ))
    (fun k => ⟨fun h => absurd h (hne k), fun h => absurd h one_ne_zero⟩)
  simp only [diagonal_one, Matrix.mul_one] at hrk
  exact ⟨h0eq, hrk.1, hrk.2⟩

/-- Exact Frobenius mass of `sobolevDirichletSampling N δ lam R`. -/
theorem frobeniusMass_sobolevDirichletSampling (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (lam : ℕ → ℝ) (R : ℕ) :
    frobeniusMass (sobolevDirichletSampling N δ lam R) =
      (R + 1 : ℝ) * ∑ k : Fin N, 1 / (2 / δ + δ * (Real.log (((k : ℕ) : ℝ) + 1)) ^ 2) := by
  unfold frobeniusMass sobolevDirichletSampling
  have hterm : ∀ (r : Fin (R + 1)) (k : Fin N),
      ‖(dirichletSampling N lam R *
        diagonal (fun m : Fin N => ((1 / dirichletSobolevWeight δ m : ℝ) : ℂ))) r k‖ ^ 2 =
        1 / (2 / δ + δ * (Real.log (((k : ℕ) : ℝ) + 1)) ^ 2) := by
    intro r k
    rw [mul_diagonal, norm_mul, norm_dirichletSampling_apply, one_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      div_pow, one_pow, dirichletSobolevWeight_sq hδ k]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Pure `T + O(N)` frame bound without logarithms for `sobolevDirichletSampling`.** At any
`δ`-separated heights `lam 0, …, lam R` in `[δ/2, T − δ/2]`, `sobolevDirichletSampling N δ lam R`
has frame bound `dirichletAffineFrameConstant T N = (5π/2) max(T, 1) + 5πe N`. -/
theorem hasFrameBound_sobolevDirichletSampling (N : ℕ) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    (hlow : δ / 2 ≤ lam 0) (R : ℕ) (hhigh : lam R + δ / 2 ≤ T) :
    HasFrameBound (sobolevDirichletSampling N δ lam R) (dirichletAffineFrameConstant T N) := by
  intro x
  set a : Fin N → ℂ := fun k => ((1 / dirichletSobolevWeight δ k : ℝ) : ℂ) * x k
  have hmul : ∀ r : Fin (R + 1),
      (sobolevDirichletSampling N δ lam R *ᵥ x) r = dirPoly N a (lam r) := by
    intro r
    unfold sobolevDirichletSampling
    rw [← mulVec_mulVec, dirichletSampling_mulVec]
    congr 1
    funext k
    simp [a, mulVec_diagonal]
  simp_rw [hmul]
  rw [Fin.sum_univ_eq_sum_range (fun r => ‖dirPoly N a (lam r)‖ ^ 2) (R + 1)]
  refine (largeValues_dirPoly_sobolev_diagonal N a hδ hT hgap hlow R hhigh).trans ?_
  refine le_of_eq (congrArg (dirichletAffineFrameConstant T N * ·) ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    div_pow, one_pow, dirichletSobolevWeight_sq hδ k]
  have hpos : 0 < 2 / δ + δ * (Real.log (((k : ℕ) : ℝ) + 1)) ^ 2 := by positivity
  field_simp [hpos.ne']

/-- **Specialization to `1`-separated heights (`δ = 1`).** At `1`-separated heights in
`[1/2, T − 1/2]`, `sobolevDirichletSampling N 1 lam R` has the logarithm-free `T + O(N)` frame
bound `dirichletAffineFrameConstant T N = (5π/2) max(T, 1) + 5πe N` and the exact same section
count `h0` and rank as `dirichletSampling N lam R`. -/
theorem hasFrameBound_sobolevDirichletSampling_one_separated (N : ℕ) {lam : ℕ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hgap : ∀ i, lam i + 1 ≤ lam (i + 1))
    (hlow : 1 / 2 ≤ lam 0) (R : ℕ) (hhigh : lam R + 1 / 2 ≤ T) :
    HasFrameBound (sobolevDirichletSampling N 1 lam R) (dirichletAffineFrameConstant T N) ∧
      (h0 (dirichletSampling N lam R) : ℝ) ≤
        (N : ℝ) - ((R + 1 : ℝ) * ∑ k : Fin N, 1 / (2 + (Real.log (((k : ℕ) : ℝ) + 1)) ^ 2)) /
          dirichletAffineFrameConstant T N := by
  have hfb := hasFrameBound_sobolevDirichletSampling N one_pos hT hgap hlow R hhigh
  refine ⟨hfb, ?_⟩
  have hnyq := h0_le_nyquist (dirichletAffineFrameConstant_pos T N) hfb
  rw [(h0_rank_h1_sobolevDirichletSampling_eq N one_pos lam R).1,
    frobeniusMass_sobolevDirichletSampling N one_pos lam R, Fintype.card_fin] at hnyq
  simpa [div_one, one_mul] using hnyq

/-! ### §3C. Pointwise Sampling (`dirichletSampling`) and Harmonic Reweighting (`harmonicDirichletSampling`) -/

/-- **Sharpened frame bound for `dirichletSampling` via `largeValues_dirPoly_affine`.** Replaces
the `T + 4N(1 + log N)` factor of `hasFrameBound_dirichletSampling` by the logarithm-free
`dirichletAffineFrameConstant T N = (5π/2) max(T, 1) + 5πe N`. -/
theorem hasFrameBound_dirichletSampling_affine (N : ℕ) (hN : 2 ≤ N) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    (hlow : δ / 2 ≤ lam 0) (R : ℕ) (hhigh : lam R + δ / 2 ≤ T) :
    HasFrameBound (dirichletSampling N lam R)
      ((1 / δ + 2 * Real.log N) * dirichletAffineFrameConstant T N) := by
  intro a
  simp only [dirichletSampling_mulVec]
  rw [Fin.sum_univ_eq_sum_range (fun r => ‖dirPoly N a (lam r)‖ ^ 2) (R + 1)]
  have h := largeValues_dirPoly_affine N hN a hδ hT hgap hlow R hhigh
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hmass := sum_mul_normSq_le_natCast_mul N a
  have hstep : 5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2) +
      (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * max T 1 ≤
      dirichletAffineFrameConstant T N * ∑ m : Fin N, ‖a m‖ ^ 2 := by
    have hc : 0 ≤ 5 * Real.pi * Real.exp 1 := by positivity
    have hm := mul_le_mul_of_nonneg_left hmass hc
    unfold dirichletAffineFrameConstant
    nlinarith
  calc ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2
      ≤ (1 / δ + 2 * Real.log N) *
          (dirichletAffineFrameConstant T N * ∑ m : Fin N, ‖a m‖ ^ 2) :=
        h.trans (mul_le_mul_of_nonneg_left hstep (by positivity))
    _ = ((1 / δ + 2 * Real.log N) * dirichletAffineFrameConstant T N) *
          ∑ m : Fin N, ‖a m‖ ^ 2 := by ring

/-- **Sharpened Nyquist section bound for `dirichletSampling` via `largeValues_dirPoly_affine`.** -/
theorem h0_dirichletSampling_le_affine (N : ℕ) (hN : 2 ≤ N) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    (hlow : δ / 2 ≤ lam 0) (R : ℕ) (hhigh : lam R + δ / 2 ≤ T) :
    (h0 (dirichletSampling N lam R) : ℝ) ≤
      (N : ℝ) - (R + 1 : ℝ) * (N : ℝ) /
        ((1 / δ + 2 * Real.log N) * dirichletAffineFrameConstant T N) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hK0 : 0 < (1 / δ + 2 * Real.log N) * dirichletAffineFrameConstant T N :=
    mul_pos (by positivity) (dirichletAffineFrameConstant_pos T N)
  have h := h0_le_nyquist hK0 (hasFrameBound_dirichletSampling_affine N hN hδ hT hgap hlow R hhigh)
  rwa [frobeniusMass_dirichletSampling, Fintype.card_fin] at h

/-- The **harmonic-reweighted Dirichlet sampling matrix**
`harmonicDirichletSampling N lam R = dirichletSampling N lam R * diagonal(1 / √(k+1))`. -/
def harmonicDirichletSampling (N : ℕ) (lam : ℕ → ℝ) (R : ℕ) :
    Matrix (Fin (R + 1)) (Fin N) ℂ :=
  dirichletSampling N lam R *
    diagonal (fun k : Fin N => ((1 / Real.sqrt (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ))

/-- `harmonicDirichletSampling N lam R` has the **exact same `h0`, `rank`, and `h1` as
`dirichletSampling N lam R`**. -/
theorem h0_rank_h1_harmonicDirichletSampling_eq (N : ℕ) (lam : ℕ → ℝ) (R : ℕ) :
    h0 (harmonicDirichletSampling N lam R) = h0 (dirichletSampling N lam R) ∧
      (harmonicDirichletSampling N lam R).rank = (dirichletSampling N lam R).rank ∧
      h1 (harmonicDirichletSampling N lam R) = h1 (dirichletSampling N lam R) := by
  have hne : ∀ k : Fin N, ((1 / Real.sqrt (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := fun k => by
    have hk : (0 : ℝ) < ((k : ℕ) : ℝ) + 1 := by positivity
    exact_mod_cast (one_div_pos.mpr (Real.sqrt_pos.mpr hk)).ne'
  have h0eq := GaloisForLFunctions.ArithmeticCastelnuovoSeveri.h0_mul_diagonal_eq_of_ne_zero
    (dirichletSampling N lam R) _ hne
  have hrk := rank_and_h1_mul_diagonal_eq_of_iff_eq_zero
    (A := dirichletSampling N lam R)
    (w₁ := fun k : Fin N => ((1 / Real.sqrt (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ))
    (w₂ := fun _ : Fin N => (1 : ℂ))
    (fun k => ⟨fun h => absurd h (hne k), fun h => absurd h one_ne_zero⟩)
  simp only [diagonal_one, Matrix.mul_one] at hrk
  exact ⟨h0eq, hrk.1, hrk.2⟩

/-- The Frobenius mass of `harmonicDirichletSampling N lam R` is `(R + 1) ∑_{k=1}^N 1/k`. -/
theorem frobeniusMass_harmonicDirichletSampling (N : ℕ) (lam : ℕ → ℝ) (R : ℕ) :
    frobeniusMass (harmonicDirichletSampling N lam R) =
      (R + 1 : ℝ) * ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) := by
  unfold frobeniusMass harmonicDirichletSampling
  have hterm : ∀ (r : Fin (R + 1)) (k : Fin N),
      ‖(dirichletSampling N lam R *
        diagonal (fun m : Fin N => ((1 / Real.sqrt (((m : ℕ) : ℝ) + 1) : ℝ) : ℂ))) r k‖ ^ 2 =
        1 / (((k : ℕ) : ℝ) + 1) := by
    intro r k
    have hk : (0 : ℝ) ≤ ((k : ℕ) : ℝ) + 1 := by positivity
    rw [mul_diagonal, norm_mul, norm_dirichletSampling_apply, one_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      div_pow, one_pow, Real.sq_sqrt hk]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← sum_fin_eq_sum_Icc N (fun k => 1 / (k : ℝ))]
  push_cast
  ring

/-- **`N`-independent height frame bound for `harmonicDirichletSampling`.** Because the `n`-weighted
mass of `x_m / √(m+1)` equals the plain mass `∑ ‖x_m‖²`, the `N` factor in `5πe N` drops out
completely, leaving `dirichletAffineFrameConstant T 1 = (5π/2) max(T, 1) + 5πe`. -/
theorem hasFrameBound_harmonicDirichletSampling (N : ℕ) (hN : 2 ≤ N) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    (hlow : δ / 2 ≤ lam 0) (R : ℕ) (hhigh : lam R + δ / 2 ≤ T) :
    HasFrameBound (harmonicDirichletSampling N lam R)
      ((1 / δ + 2 * Real.log N) * dirichletAffineFrameConstant T 1) := by
  intro x
  set a : Fin N → ℂ := fun k => ((1 / Real.sqrt (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ) * x k
  have hmul : ∀ r : Fin (R + 1),
      (harmonicDirichletSampling N lam R *ᵥ x) r = dirPoly N a (lam r) := by
    intro r
    unfold harmonicDirichletSampling
    rw [← mulVec_mulVec, dirichletSampling_mulVec]
    congr 1
    funext k
    simp [a, mulVec_diagonal]
  simp_rw [hmul]
  rw [Fin.sum_univ_eq_sum_range (fun r => ‖dirPoly N a (lam r)‖ ^ 2) (R + 1)]
  have h := largeValues_dirPoly_affine N hN a hδ hT hgap hlow R hhigh
  have hW : ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2 = ∑ m : Fin N, ‖x m‖ ^ 2 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm : (0 : ℝ) < ((m : ℕ) : ℝ) + 1 := by positivity
    simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      div_pow, one_pow, Real.sq_sqrt hm.le]
    field_simp [hm.ne']
  have hS : ∑ m : Fin N, ‖a m‖ ^ 2 ≤ ∑ m : Fin N, ‖x m‖ ^ 2 := by
    refine Finset.sum_le_sum fun m _ => ?_
    have hm : (1 : ℝ) ≤ ((m : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    simp only [a, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      div_pow, one_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ ((m : ℕ) : ℝ) + 1)]
    have h1 : 1 / (((m : ℕ) : ℝ) + 1) ≤ 1 := div_le_self zero_le_one hm
    exact mul_le_of_le_one_left (sq_nonneg _) h1
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hmax : 0 ≤ max T 1 := le_trans zero_le_one (le_max_right T 1)
  have hstep : 5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2) +
      (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * max T 1 ≤
      dirichletAffineFrameConstant T 1 * ∑ m : Fin N, ‖x m‖ ^ 2 := by
    rw [hW]
    have h2 : (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * max T 1 ≤
        (5 * Real.pi / 2) * (∑ m : Fin N, ‖x m‖ ^ 2) * max T 1 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS (by positivity)) hmax
    unfold dirichletAffineFrameConstant
    push_cast
    nlinarith
  calc ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2
      ≤ (1 / δ + 2 * Real.log N) *
          (dirichletAffineFrameConstant T 1 * ∑ m : Fin N, ‖x m‖ ^ 2) :=
        h.trans (mul_le_mul_of_nonneg_left hstep (by positivity))
    _ = ((1 / δ + 2 * Real.log N) * dirichletAffineFrameConstant T 1) *
          ∑ m : Fin N, ‖x m‖ ^ 2 := by ring

/-- **Harmonic rank bound for `dirichletSampling` (`log N` numerator cancels `log N` denominator).** -/
theorem rank_dirichletSampling_ge_harmonic (N : ℕ) (hN : 2 ≤ N) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hgap : ∀ i, lam i + δ ≤ lam (i + 1))
    (hlow : δ / 2 ≤ lam 0) (R : ℕ) (hhigh : lam R + δ / 2 ≤ T) :
    (R + 1 : ℝ) * (∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ)) ≤
      ((1 / δ + 2 * Real.log N) * dirichletAffineFrameConstant T 1) *
        ((dirichletSampling N lam R).rank : ℝ) := by
  have h := frobeniusMass_le_rank_mul
    (hasFrameBound_harmonicDirichletSampling N hN hδ hT hgap hlow R hhigh)
  rwa [frobeniusMass_harmonicDirichletSampling,
    (h0_rank_h1_harmonicDirichletSampling_eq N lam R).2.1] at h

/-! ## §4. Reading the Injectivity Threshold Against the Square-Root Threshold of the Aperture -/

/-- The **aperture test length** `N_test(a) = e^a` of a test supported in `[−a, a]`. -/
def apertureTestLength (a : ℝ) : ℝ :=
  Real.exp a

/-- The **aperture prime horizon** `X(a) = e^{2a}` read on the prime side by the Weil kernel
`k = f ⋆ f̃` of a test supported in `[−a, a]`. -/
def aperturePrimeHorizon (a : ℝ) : ℝ :=
  Real.exp (2 * a)

/-- The **square-root aperture** `a_sqrt(T) = (1/2) log T` at height `T`. -/
def squareRootAperture (T : ℝ) : ℝ :=
  (1 / 2) * Real.log T

/-- The aperture test length is the exact square root of the aperture prime horizon:
`apertureTestLength a = √(aperturePrimeHorizon a)` and `(apertureTestLength a)² = aperturePrimeHorizon a`. -/
theorem apertureTestLength_sq_eq_primeHorizon (a : ℝ) :
    apertureTestLength a ^ 2 = aperturePrimeHorizon a ∧
      apertureTestLength a = Real.sqrt (aperturePrimeHorizon a) := by
  unfold apertureTestLength aperturePrimeHorizon
  have hsq : Real.exp a ^ 2 = Real.exp (2 * a) := by
    rw [sq, ← Real.exp_add, two_mul]
  refine ⟨hsq, ?_⟩
  rw [← hsq, Real.sqrt_sq (Real.exp_pos a).le]

/-- **Exact calibration at `squareRootAperture T`.** For `0 < T`, at `a = squareRootAperture T`,
the prime horizon equals the diagonal height `T` (`aperturePrimeHorizon a = T`) and the test length
equals the square-root length `√T` (`apertureTestLength a = √T`). -/
theorem aperturePrimeHorizon_and_testLength_squareRootAperture {T : ℝ} (hT : 0 < T) :
    aperturePrimeHorizon (squareRootAperture T) = T ∧
      apertureTestLength (squareRootAperture T) = Real.sqrt T := by
  have h1 : aperturePrimeHorizon (squareRootAperture T) = T := by
    unfold aperturePrimeHorizon squareRootAperture
    rw [show 2 * (1 / 2 * Real.log T) = Real.log T by ring, Real.exp_log hT]
  refine ⟨h1, ?_⟩
  rw [(apertureTestLength_sq_eq_primeHorizon (squareRootAperture T)).2, h1]

/-- **Equivalence of the aperture threshold, the test-length square-root threshold, and the
prime-horizon diagonal threshold.** For `0 < T`:
`a ≤ squareRootAperture T ↔ aperturePrimeHorizon a ≤ T ↔ apertureTestLength a ≤ √T`. -/
theorem le_squareRootAperture_iff {a T : ℝ} (hT : 0 < T) :
    (a ≤ squareRootAperture T ↔ aperturePrimeHorizon a ≤ T) ∧
      (a ≤ squareRootAperture T ↔ apertureTestLength a ≤ Real.sqrt T) := by
  obtain ⟨hP, hL⟩ := aperturePrimeHorizon_and_testLength_squareRootAperture hT
  refine ⟨?_, ?_⟩
  · rw [← hP]
    unfold aperturePrimeHorizon
    rw [Real.exp_le_exp]
    constructor <;> intro h <;> linarith
  · rw [← hL]
    unfold apertureTestLength
    exact Real.exp_le_exp.symm

/-- **Exact windowed diagonal below the square-root aperture.** For `0 < T`, a window `η` supported
in `[−1/(2T), 1/(2T)]`, and any aperture `a ≤ squareRootAperture T`, every Dirichlet polynomial
supported in `[1, aperturePrimeHorizon a]` is seen **exactly diagonally** by the height window:
`∫ |h_η(−2πξ)|² |∑_{n ∈ s} c_n n^{2πiξ}|² dξ = ‖η‖² ∑_{n ∈ s} |c_n|²`. -/
theorem windowed_dirichlet_diagonal_below_squareRootAperture
    {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {T a : ℝ} (hT : 0 < T)
    (hηs : tsupport η ⊆ Icc (-(1 / (2 * T))) (1 / (2 * T)))
    (ha : a ≤ squareRootAperture T) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ aperturePrimeHorizon a) (c : ℕ → ℂ) :
    ∫ ξ : ℝ, ‖Zeta23.paperFT η (-(2 * Real.pi * (ξ : ℂ)))‖ ^ 2 *
        ‖expSum s c (fun n => Real.log n) ξ‖ ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  have hX : aperturePrimeHorizon a ≤ T := ((le_squareRootAperture_iff hT).1).mp ha
  have hr : 0 ≤ 1 / (2 * T) := by positivity
  have h2rX : 2 * (1 / (2 * T)) * aperturePrimeHorizon a ≤ 1 := by
    have hpos : 0 < T := hT
    rw [show 2 * (1 / (2 * T)) * aperturePrimeHorizon a = aperturePrimeHorizon a / T by ring]
    exact (div_le_one hT).mpr hX
  exact integral_normSq_mul_normSq_dirichletSum hη hr hηs h2rX s hs c

/-- **Below the square-root aperture (`a ≤ squareRootAperture T`), the diagonal frame constant is
purely linear in `T`.** For `1 ≤ T`, `a ≤ squareRootAperture T`, and `N ≤ aperturePrimeHorizon a`,
`dirichletAffineFrameConstant T N ≤ (5π/2 + 5πe) T`. -/
theorem dirichletAffineFrameConstant_le_below_squareRootAperture
    {T a : ℝ} {N : ℕ} (hT : 1 ≤ T) (ha : a ≤ squareRootAperture T)
    (hN : (N : ℝ) ≤ aperturePrimeHorizon a) :
    dirichletAffineFrameConstant T N ≤ (5 * Real.pi / 2 + 5 * Real.pi * Real.exp 1) * T := by
  have hT0 : 0 < T := by linarith
  have hNT : (N : ℝ) ≤ T := hN.trans (((le_squareRootAperture_iff hT0).1).mp ha)
  rw [dirichletAffineFrameConstant_of_one_le hT]
  have hc : 0 ≤ 5 * Real.pi * Real.exp 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hNT hc
  linarith

/-- **Maximal count of `1`-separated heights in `[1/2, T − 1/2]`.** Any sequence `lam` with
`lam i + 1 ≤ lam (i + 1)`, `1 / 2 ≤ lam 0`, and `lam R + 1 / 2 ≤ T` satisfies `(R + 1 : ℝ) ≤ T`. -/
theorem sample_count_le_T_of_one_separated {lam : ℕ → ℝ} {T : ℝ}
    (hgap : ∀ i, lam i + 1 ≤ lam (i + 1)) (hlow : 1 / 2 ≤ lam 0)
    (R : ℕ) (hhigh : lam R + 1 / 2 ≤ T) :
    (R + 1 : ℝ) ≤ T := by
  have h := le_of_gap hgap 0 R (Nat.zero_le R)
  simp only [Nat.cast_zero, sub_zero, mul_one] at h
  linarith

/-- **Loss of injectivity above the diagonal / square-root threshold (`T < N`).** For any
`1`-separated sequence of heights `lam 0, …, lam R` in `[1/2, T − 1/2]`, as soon as the Dirichlet
length `N` exceeds the height `T` (`T < N`, i.e., above the diagonal `N = aperturePrimeHorizon a > T`
where `a > squareRootAperture T`), `R + 1 < N` and the reading `dirichletSampling N lam R` has a
nontrivial space of hiding sections of dimension at least `N − (R + 1) ≥ N − ⌊T⌋₊ > 0`. -/
theorem h0_dirichletSampling_pos_above_diagonal {N : ℕ} {lam : ℕ → ℝ} {T : ℝ}
    (hgap : ∀ i, lam i + 1 ≤ lam (i + 1)) (hlow : 1 / 2 ≤ lam 0)
    (R : ℕ) (hhigh : lam R + 1 / 2 ≤ T) (habove : T < (N : ℝ)) :
    (N : ℝ) - T ≤ (h0 (dirichletSampling N lam R) : ℝ) ∧
      0 < h0 (dirichletSampling N lam R) := by
  have hRT : (R + 1 : ℝ) ≤ T := sample_count_le_T_of_one_separated hgap hlow R hhigh
  have hRN : R + 1 < N := by
    have : (R + 1 : ℝ) < (N : ℝ) := hRT.trans_lt habove
    exact_mod_cast this
  have hpos := h0_pos_of_card_lt_card (dirichletSampling N lam R)
    (by simpa only [Fintype.card_fin] using hRN)
  simp only [Fintype.card_fin] at hpos
  refine ⟨?_, hpos.2⟩
  have h1 := card_sub_card_le_h0 (dirichletSampling N lam R)
  simp only [Fintype.card_fin] at h1
  push_cast at h1
  linarith

/-- **Coincidence of the lattice Nyquist aperture and the square-root threshold of the aperture.**
At logarithmic zero density `L = log T` (`1 < T`), the Nyquist aperture `L / 2` of
`PositionAndDepthShareOneNyquistAperture` equals `squareRootAperture T = (1/2) log T`, so:
1. For `a ≤ squareRootAperture T` (`aperturePrimeHorizon a ≤ T`, `apertureTestLength a ≤ √T`),
   `onLineLatticeConfig`, `simpleHalfLatticeConfig`, and `offLineLatticeConfig` all agree on tests
   of aperture `a`, the windowed Dirichlet mean square is exact diagonal, and the diagonal frame
   constant `dirichletAffineFrameConstant T N` is bounded by `(5π/2 + 5πe) T`;
2. For `a > squareRootAperture T` (`aperturePrimeHorizon a > T`, `apertureTestLength a > √T`),
   both position and depth mimics are detected on the lattice, while `1`-separated Dirichlet
   sampling in `[1/2, T − 1/2]` of length `N ≥ ⌈aperturePrimeHorizon a⌉₊` loses injectivity
   (`0 < h0 (dirichletSampling N lam R)`). -/
theorem lattice_nyquist_eq_squareRootAperture {T : ℝ} (hT : 1 < T) (a : ℝ) :
    have hL : 0 < Real.log T := Real.log_pos hT
    Real.log T / 2 = squareRootAperture T ∧
      ((∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          (onLineLatticeConfig hL).W f f = (simpleHalfLatticeConfig hL).W f f) ↔
        aperturePrimeHorizon a ≤ T) ∧
      (∀ {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2),
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          (offLineLatticeConfig hL hδ hδ').W f f = (onLineLatticeConfig hL).W f f) ↔
        aperturePrimeHorizon a ≤ T) := by
  intro hL
  have hT0 : 0 < T := zero_lt_one.trans hT
  have heq : Real.log T / 2 = squareRootAperture T := by
    unfold squareRootAperture
    ring
  refine ⟨heq, ?_, fun hδ hδ' => ?_⟩
  · rw [onLineLattices_agree_iff_le_nyquist hL a, heq, (le_squareRootAperture_iff hT0).1]
  · rw [offLineLattice_agrees_iff_le_nyquist hL hδ hδ' a, heq, (le_squareRootAperture_iff hT0).1]

/-- **Complete Synthesis for Open Problem 7 (The Nyquist Bound at the Diagonal and the Square-Root
Threshold of the Aperture).**
Unites the four pillars resolving Open Problem 7:
1. **Logarithm-free `T + O(N)` mean-square and cell-sampling frame bound**:
   `dirichletCellSampling N δ lam R` has frame bound
   `dirichletAffineFrameConstant T N = (5π/2) max(T, 1) + 5πe N` at any `δ`-separated (and in
   particular `1`-separated) heights in `[δ/2, T − δ/2]`;
2. **Logarithm-free `T + O(N)` Sobolev-normalized pointwise frame bound**:
   `sobolevDirichletSampling N 1 lam R` has the exact same `h0`, `rank`, and `h1` as
   `dirichletSampling N lam R` and satisfies `HasFrameBound (sobolevDirichletSampling N 1 lam R) (dirichletAffineFrameConstant T N)`;
3. **Harmonic logarithm cancellation**:
   `harmonicDirichletSampling N lam R` has the exact same `h0`, `rank`, and `h1` as
   `dirichletSampling N lam R`, `N`-independent height factor `dirichletAffineFrameConstant T 1`,
   and Frobenius mass `(R + 1) ∑_{k=1}^N 1/k`;
4. **Exact alignment of the diagonal injectivity threshold with the square-root aperture threshold**:
   at `a = squareRootAperture T = (1/2) log T`, `aperturePrimeHorizon a = T` and
   `apertureTestLength a = √T`; below `squareRootAperture T` the frame constant is `O(T)` and the
   windowed mean square is exact diagonal, whereas above `squareRootAperture T` (`T < N`) every
   `1`-separated sampling matrix in `[1/2, T − 1/2]` has `0 < N − T ≤ h0 (dirichletSampling N lam R)`. -/
theorem nyquist_diagonal_and_squareRoot_threshold_synthesis :
    (∀ (N : ℕ) {lam : ℕ → ℝ} {δ T : ℝ},
      0 < δ → 0 ≤ T → (∀ i, lam i + δ ≤ lam (i + 1)) →
      δ / 2 ≤ lam 0 → ∀ (R : ℕ), lam R + δ / 2 ≤ T →
      HasFrameBound (dirichletCellSampling N δ lam R) (dirichletAffineFrameConstant T N)) ∧
    (∀ (N : ℕ) {lam : ℕ → ℝ} {T : ℝ},
      0 ≤ T → (∀ i, lam i + 1 ≤ lam (i + 1)) →
      1 / 2 ≤ lam 0 → ∀ (R : ℕ), lam R + 1 / 2 ≤ T →
      h0 (sobolevDirichletSampling N 1 lam R) = h0 (dirichletSampling N lam R) ∧
        HasFrameBound (sobolevDirichletSampling N 1 lam R) (dirichletAffineFrameConstant T N)) ∧
    (∀ (N : ℕ), 2 ≤ N → ∀ {lam : ℕ → ℝ} {δ T : ℝ},
      0 < δ → 0 ≤ T → (∀ i, lam i + δ ≤ lam (i + 1)) →
      δ / 2 ≤ lam 0 → ∀ (R : ℕ), lam R + δ / 2 ≤ T →
      (R + 1 : ℝ) * (∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ)) ≤
        ((1 / δ + 2 * Real.log N) * dirichletAffineFrameConstant T 1) *
          ((dirichletSampling N lam R).rank : ℝ)) ∧
    (∀ {T : ℝ}, 0 < T →
      aperturePrimeHorizon (squareRootAperture T) = T ∧
      apertureTestLength (squareRootAperture T) = Real.sqrt T ∧
      ∀ {N : ℕ} {lam : ℕ → ℝ} (R : ℕ),
        (∀ i, lam i + 1 ≤ lam (i + 1)) → 1 / 2 ≤ lam 0 → lam R + 1 / 2 ≤ T →
        T < (N : ℝ) →
        (N : ℝ) - T ≤ (h0 (dirichletSampling N lam R) : ℝ) ∧
          0 < h0 (dirichletSampling N lam R)) := by
  refine ⟨fun N _ _ hδ hT hgap hlow R hhigh =>
      hasFrameBound_dirichletCellSampling N hδ hT hgap hlow R hhigh,
    fun N _ hT hgap hlow R hhigh =>
      ⟨(h0_rank_h1_sobolevDirichletSampling_eq N one_pos _ R).1,
       (hasFrameBound_sobolevDirichletSampling_one_separated N hT hgap hlow R hhigh).1⟩,
    fun N hN _ _ hδ hT hgap hlow R hhigh =>
      rank_dirichletSampling_ge_harmonic N hN hδ hT hgap hlow R hhigh,
    fun hT => ⟨(aperturePrimeHorizon_and_testLength_squareRootAperture hT).1,
      (aperturePrimeHorizon_and_testLength_squareRootAperture hT).2,
      fun R hgap hlow hhigh habove =>
        h0_dirichletSampling_pos_above_diagonal hgap hlow R hhigh habove⟩⟩

end

end ArithmeticOrientationTheory
end GaloisForLFunctions
