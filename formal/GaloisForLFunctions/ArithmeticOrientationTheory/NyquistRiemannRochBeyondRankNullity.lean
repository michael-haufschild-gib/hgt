import GaloisForLFunctions.ArithmeticOrientationTheory.TheEffectivityConeFromSections
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerZeroPoleNodeCriticality
import GaloisForLFunctions.RHTower.AdmixturesAndTheShiftedPairLeaveTheWeilCone
import GaloisForLFunctions.RHTower.MarkovJointResolventEnvelopeAndPastThirtyFourPBAP
import GaloisForLFunctions.RHTower.SharpWeilNearRadicalCount

/-!
# Nyquist–Riemann–Roch beyond rank–nullity: Landau–Markov frame bounds, prime-power nodes, and the Chebyshev `h¹` correction

This module resolves Open Problem 3 of Arithmetic Orientation Theory:
> *"Replace the finite-dimensional test space by band-limited tests on an aperture, the node set by
> the prime-power nodes, and the frame bound by a Landau-type density theorem; identify the `h¹`
> term and the Chebyshev defect `E(s) = e^s + s − 1 − ψ(e^s)` as its correction."*

## Mathematical architecture

1. **Spectral-defect Nyquist–Riemann–Roch, the dual `h¹` bound, and Frobenius-mass selectivity (§1):**
   For any discrete reading `A : Matrix m n ℂ` and frame parameter `K : ℝ`, we define the
   **Nyquist effective rank** `nyquistEffectiveRank A K := frobeniusMass A / K` and the
   **Nyquist spectral defect** `nyquistSpectralDefect A K := (A.rank : ℝ) - frobeniusMass A / K`.
   - Under `HasFrameBound A K` and `0 < K`, `0 ≤ nyquistSpectralDefect A K`
     (`nyquistSpectralDefect_nonneg`), vanishing iff `frobeniusMass A = K * A.rank`
     (`nyquistSpectralDefect_eq_zero_iff`).
   - Both `h⁰` and `h¹` satisfy exact spectral-defect decompositions
     (`h0_add_nyquistEffectiveRank_add_spectralDefect`, `h1_add_nyquistEffectiveRank_add_spectralDefect`),
     yielding the **dual Nyquist bound on `h¹`** (`h1_le_nyquist`):
     `(h1 A : ℝ) ≤ Fintype.card m - frobeniusMass A / K`.
   - Whereas the algebraic counts `h0`, `rank`, and `h1` are invariant under support-preserving
     diagonal reweighting (`rank_and_h1_mul_diagonal_eq_of_iff_eq_zero`) and therefore cannot
     distinguish `shiftedPairVonMangoldt a` from `Λ` on `weightedDirichletSampling`
     (`h0_rank_h1_weightedDirichletSampling_shiftedPair_eq_vonMangoldt`), the Frobenius mass is
     strictly selective: for every `a ≠ 0` and `2 ≤ N`,
     `frobeniusMass (weightedDirichletSampling N (shiftedPairVonMangoldt a) lam R) ≥
     (2^a + 2^{-a})^2 * frobeniusMass (weightedDirichletSampling N Λ lam R) >
     4 * frobeniusMass (weightedDirichletSampling N Λ lam R)`
     (`frobeniusMass_weightedDirichletSampling_shiftedPair_ge`,
     `frobeniusMass_weightedDirichletSampling_shiftedPair_gt`).

2. **Band-limited tests on an aperture, prime-power nodes, and the Landau–Markov & Landau–Widom
   density theorems (§2):**
   - **Landau–Markov frame bound on the prime-power nodes (`l2_le_two_sixty_ninths_spectralSecondMoment_of_primeBlind`):**
     For every `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` that vanishes on the prime-power node
     divisor (`logVector (realWeilTestFn f hf hfc) = 0`),
     `∫ x, f x ^ 2 ≤ (2 / 69) * spectralSecondMoment (realWeilTestFn f hf hfc).1`
     (with strict inequality `<` whenever `0 < ∫ f²`).
   - **Sub-Nyquist prime-blind section vanishing (`primeBlind_eq_zero_of_spectralSecondMoment_le_sixty_nine_halves`,
     `finrank_primeBlind_subspace_eq_zero`):**
     On any subspace `W` of `C²_c(ℝ)` prime-blind sections with `coshHalfMoment f = 0` and rms
     spectral height `T² ≤ 69 / 2` (`spectralSecondMoment ≤ T² ∫ f²`), `W = ⊥` and
     `Module.finrank ℝ W = 0` at **every** aperture `r > 0`.
   - **Nonnegative log-value and general primitive-hyperplane Landau–Markov bounds
     (`sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg_unconditional`,
     `thirty_three_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg_unconditional`):**
     On the nonnegative log-value cone the Landau–Markov frame constant remains `69 / 2 = 34.5`,
     and on the general unit-step cone it is `33`.
   - **Prime-power node criticality vs. trans-Nyquist Landau–Widom section supply
     (`primePower_node_criticality_and_landauWidom_supply`):**
     Deleting even one prime-power node (`4`) or restricting to primes falsifies zero-pole-blind
     positivity unconditionally (`not_zeroPoleBlindPositiveOn_diff_four`,
     `not_zeroPoleBlindPositiveOn_primes`), whereas at the trans-Nyquist Landau–Shannon height
     `T = 2π e^{2ℓ}` on aperture `[-L, L]`, the near-radical subspace has dimension at least
     `(2 - η) e^{2L}` (`zeta_weil_near_radical_sharp_count`).

3. **Identifying the `h¹` term and the Chebyshev defect `E(s) = e^s + s - 1 - ψ(e^s)` as its
   correction (§3):**
   - **Box level (`nodeDivisorEulerChar`, `boxH0Supply`, `boxH1Obstruction`):**
     On `[0, s]`, `nodeDivisorEulerChar s := polarBoxDoF s - primeNodeCount s =
     chebyshevTwoPoleDefect s = e^s + s - 1 - ψ(e^s)` splits orthogonally into
     `boxH0Supply s - boxH1Obstruction s` (`boxH0Supply_sub_boxH1Obstruction`). On `[0, log 2]`,
     `boxH1Obstruction s = 0` (`boxH1Obstruction_eq_zero_below_log_two`,
     `boxH1Obstruction_eq_zero_at_log_two`), whereas for `shiftedPairVonMangoldt a` with
     `2^a + 2^{-a} > 1 + 1 / log 2`, the `h¹` obstruction `generalizedBoxH1Obstruction` is strictly
     positive already at `s = log 2` (`generalizedBoxH1Obstruction_shiftedPair_log_two_pos`).
   - **Aperture level (`archGaugeBudget`, `apertureNetPolarGauge`, `apertureH1ChebyshevCorrection`,
     `primeNodeCorrelationObstruction`):**
     On `scalingSubsurface (oddRealTestsAt r)` (`0 < r < R`), the `E(s)` integral against the lag
     derivative `lagDerivativeWeight F s` (`apertureH1ChebyshevCorrection r F`) equals
     `reflectedPrimePolarCost F r = poleCharge F + primeNodeCorrelationObstruction r F`
     (`apertureH1ChebyshevCorrection_eq_poleCharge_add_primeNodeObstruction`), and satisfies the
     exact continuous Nyquist–Riemann–Roch identities:
     - `(scalingSubsurface (oddRealTestsAt r)).defect x x + apertureH1ChebyshevCorrection r F = archGaugeBudget r R F`
       (`aperture_nyquist_riemannRoch_defect_identity`),
     - `(scalingSubsurface (oddRealTestsAt r)).pair x x = apertureNetPolarGauge r R x + apertureH1ChebyshevCorrection r F`
       (`aperture_nyquist_riemannRoch_selfIntersection_identity`).
     On horizon-prime-blind tests (`IsHorizonPrimeBlind F r`), `primeNodeCorrelationObstruction r F = 0`
     and `apertureH1ChebyshevCorrection r F = poleCharge F ≥ 0` (vanishing identically when
     `oddPoleMoment F = 0`, `apertureH1ChebyshevCorrection_of_isHorizonPrimeBlind`). Globally,
     all-aperture payment of `apertureH1ChebyshevCorrection` by `archGaugeBudget` is equivalent to
     every unit of the width dictionary (`nyquistRiemannRoch_beyond_rankNullity_tfae`), holds
     unconditionally on `(0, 181/500]`, and obeys the de la Vallée Poussin Sobolev and `(3 + ε) e^r`
     bounds across all apertures `r > 0` (`nyquistRiemannRoch_beyond_rankNullity_synthesis`).
-/

open Complex Finset Matrix MeasureTheory Set Filter Topology
open scoped Real BigOperators
open Zeta23 RHTower RHTower.Sieve RHTower.WeilOneSided RHTower.WeilSpectral RHTower.WeilLevyPole
open RHTower.LebesgueAtomWeil RHTower.NonnegativeCone RHTower.EvenSector
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### 1. Spectral-defect Nyquist–Riemann–Roch, the dual `h¹` bound, and Frobenius-mass selectivity -/

section SpectralDefectNyquist

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The **Nyquist effective rank** `frobeniusMass A / K` of a linear reading `A : Matrix m n ℂ`
at frame parameter `K`. -/
def nyquistEffectiveRank (A : Matrix m n ℂ) (K : ℝ) : ℝ :=
  frobeniusMass A / K

/-- The **Nyquist spectral defect** `(A.rank : ℝ) - frobeniusMass A / K`, measuring the gap between
the algebraic rank of `A` and its trace-normalized effective rank `(1 / K) Tr(Aᴴ A)`. -/
def nyquistSpectralDefect (A : Matrix m n ℂ) (K : ℝ) : ℝ :=
  (A.rank : ℝ) - frobeniusMass A / K

omit [DecidableEq n] in
/-- For any reading `A` and `K : ℝ`, `nyquistEffectiveRank A K + nyquistSpectralDefect A K = A.rank`. -/
theorem nyquistEffectiveRank_add_spectralDefect (A : Matrix m n ℂ) (K : ℝ) :
    nyquistEffectiveRank A K + nyquistSpectralDefect A K = A.rank := by
  unfold nyquistEffectiveRank nyquistSpectralDefect
  ring

/-- Under a frame bound `HasFrameBound A K` with `0 < K`, the Nyquist spectral defect is
nonnegative (`0 ≤ nyquistSpectralDefect A K`). -/
theorem nyquistSpectralDefect_nonneg {A : Matrix m n ℂ} {K : ℝ} (hK0 : 0 < K)
    (hK : HasFrameBound A K) :
    0 ≤ nyquistSpectralDefect A K := by
  unfold nyquistSpectralDefect
  have h := frobeniusMass_le_rank_mul hK
  have hdiv : frobeniusMass A / K ≤ A.rank := (div_le_iff₀ hK0).mpr (by linarith)
  linarith

omit [DecidableEq n] in
/-- For `0 < K`, the Nyquist spectral defect vanishes if and only if `frobeniusMass A = K * A.rank`
(every nonzero eigenvalue of `Aᴴ A` saturates the frame bound `K`). -/
theorem nyquistSpectralDefect_eq_zero_iff (A : Matrix m n ℂ) {K : ℝ} (hK0 : 0 < K) :
    nyquistSpectralDefect A K = 0 ↔ frobeniusMass A = K * (A.rank : ℝ) := by
  unfold nyquistSpectralDefect
  rw [sub_eq_zero, eq_div_iff hK0.ne']
  constructor <;> intro h <;> linarith

omit [DecidableEq n] in
/-- **Exact spectral-defect decomposition of `h⁰`:**
`(h0 A : ℝ) + nyquistEffectiveRank A K + nyquistSpectralDefect A K = Fintype.card n`. -/
theorem h0_add_nyquistEffectiveRank_add_spectralDefect (A : Matrix m n ℂ) (K : ℝ) :
    (h0 A : ℝ) + nyquistEffectiveRank A K + nyquistSpectralDefect A K = Fintype.card n := by
  have h : (h0 A : ℝ) + (A.rank : ℝ) = Fintype.card n := by exact_mod_cast h0_add_rank A
  have hd := nyquistEffectiveRank_add_spectralDefect A K
  linarith

omit [DecidableEq n] in
/-- **Exact spectral-defect decomposition of `h¹`:**
`(h1 A : ℝ) + nyquistEffectiveRank A K + nyquistSpectralDefect A K = Fintype.card m`. -/
theorem h1_add_nyquistEffectiveRank_add_spectralDefect (A : Matrix m n ℂ) (K : ℝ) :
    (h1 A : ℝ) + nyquistEffectiveRank A K + nyquistSpectralDefect A K = Fintype.card m := by
  have hr : A.rank ≤ Fintype.card m := rank_le_card_height A
  have h1_eq : (h1 A : ℝ) + (A.rank : ℝ) = Fintype.card m := by
    unfold h1
    exact_mod_cast Nat.sub_add_cancel hr
  have hd := nyquistEffectiveRank_add_spectralDefect A K
  linarith

omit [DecidableEq n] in
/-- `h0 A` equals the Nyquist upper bound `Fintype.card n - frobeniusMass A / K` minus
`nyquistSpectralDefect A K`. -/
theorem h0_eq_nyquist_sub_spectralDefect (A : Matrix m n ℂ) (K : ℝ) :
    (h0 A : ℝ) = ((Fintype.card n : ℝ) - frobeniusMass A / K) - nyquistSpectralDefect A K := by
  have h := h0_add_nyquistEffectiveRank_add_spectralDefect A K
  unfold nyquistEffectiveRank at h
  linarith

omit [DecidableEq n] in
/-- `h1 A` equals the dual Nyquist upper bound `Fintype.card m - frobeniusMass A / K` minus
`nyquistSpectralDefect A K`. -/
theorem h1_eq_nyquist_sub_spectralDefect (A : Matrix m n ℂ) (K : ℝ) :
    (h1 A : ℝ) = ((Fintype.card m : ℝ) - frobeniusMass A / K) - nyquistSpectralDefect A K := by
  have h := h1_add_nyquistEffectiveRank_add_spectralDefect A K
  unfold nyquistEffectiveRank at h
  linarith

/-- **The dual Nyquist bound on obstructions (`h1_le_nyquist`):** for any reading `A` with frame
bound `K > 0`, `h¹(A) ≤ #nodes - (Frobenius mass) / K`. -/
theorem h1_le_nyquist {A : Matrix m n ℂ} {K : ℝ} (hK0 : 0 < K) (hK : HasFrameBound A K) :
    (h1 A : ℝ) ≤ (Fintype.card m : ℝ) - frobeniusMass A / K := by
  rw [h1_eq_nyquist_sub_spectralDefect A K]
  have hd := nyquistSpectralDefect_nonneg hK0 hK
  linarith

omit [DecidableEq n] in
/-- In the Euler characteristic `h⁰(A) - h¹(A)`, both `nyquistEffectiveRank A K` and
`nyquistSpectralDefect A K` cancel identically, recovering `dim - #nodes`. -/
theorem h0_sub_h1_eq_nyquist_diff (A : Matrix m n ℂ) (K : ℝ) :
    (h0 A : ℝ) - (h1 A : ℝ) =
      ((Fintype.card n : ℝ) - frobeniusMass A / K) -
        ((Fintype.card m : ℝ) - frobeniusMass A / K) ∧
    (h0 A : ℝ) - (h1 A : ℝ) = (Fintype.card n : ℝ) - (Fintype.card m : ℝ) := by
  rw [h0_eq_nyquist_sub_spectralDefect A K, h1_eq_nyquist_sub_spectralDefect A K]
  exact ⟨by ring, by ring⟩

/-- **Diagonal relabeling invariance of `rank` and `h1`:** right-multiplying any reading `A` by
diagonal weights `w₁, w₂` with identical support (`∀ j, w₁ j = 0 ↔ w₂ j = 0`) leaves `h0`, `rank`,
and `h1` unchanged. -/
theorem rank_and_h1_mul_diagonal_eq_of_iff_eq_zero (A : Matrix m n ℂ) {w₁ w₂ : n → ℂ}
    (hw : ∀ j, w₁ j = 0 ↔ w₂ j = 0) :
    h0 (A * Matrix.diagonal w₁) = h0 (A * Matrix.diagonal w₂) ∧
    (A * Matrix.diagonal w₁).rank = (A * Matrix.diagonal w₂).rank ∧
    h1 (A * Matrix.diagonal w₁) = h1 (A * Matrix.diagonal w₂) := by
  have hh0 := h0_mul_diagonal_eq_of_iff_eq_zero A hw
  have hr1 := h0_add_rank (A * Matrix.diagonal w₁)
  have hr2 := h0_add_rank (A * Matrix.diagonal w₂)
  have hrank : (A * Matrix.diagonal w₁).rank = (A * Matrix.diagonal w₂).rank := by omega
  have hh1 : h1 (A * Matrix.diagonal w₁) = h1 (A * Matrix.diagonal w₂) := by
    unfold h1
    rw [hrank]
  exact ⟨hh0, hrank, hh1⟩

end SpectralDefectNyquist

/-- **Weighted Dirichlet sampling matrix (`weightedDirichletSampling`):** the `(R + 1) × N` matrix
reading `w`-weighted Dirichlet polynomials `∑_{m < N} a_m w_m (m + 1)^{i λ_r}` at `λ_0, …, λ_R`. -/
def weightedDirichletSampling (N : ℕ) (w : Fin N → ℂ) (lam : ℕ → ℝ) (R : ℕ) :
    Matrix (Fin (R + 1)) (Fin N) ℂ :=
  dirichletSampling N lam R * Matrix.diagonal w

@[simp]
theorem weightedDirichletSampling_apply (N : ℕ) (w : Fin N → ℂ) (lam : ℕ → ℝ) (R : ℕ)
    (r : Fin (R + 1)) (m : Fin N) :
    weightedDirichletSampling N w lam R r m = dirichletSampling N lam R r m * w m :=
  Matrix.mul_diagonal _ _ _ _

/-- Every entry of `dirichletSampling N lam R` has unit complex norm. -/
@[simp]
theorem norm_dirichletSampling_apply (N : ℕ) (lam : ℕ → ℝ) (R : ℕ)
    (r : Fin (R + 1)) (m : Fin N) :
    ‖dirichletSampling N lam R r m‖ = 1 := by
  unfold dirichletSampling
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Frobenius mass of `weightedDirichletSampling`:**
`frobeniusMass (weightedDirichletSampling N w lam R) = (R + 1) * ∑_{m < N} ‖w m‖²`. -/
theorem frobeniusMass_weightedDirichletSampling (N : ℕ) (w : Fin N → ℂ) (lam : ℕ → ℝ) (R : ℕ) :
    frobeniusMass (weightedDirichletSampling N w lam R) =
      ((R : ℝ) + 1) * ∑ m : Fin N, ‖w m‖ ^ 2 := by
  unfold frobeniusMass
  simp only [weightedDirichletSampling_apply, norm_mul, norm_dirichletSampling_apply, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one, nsmul_eq_mul]

/-- For every `a ∈ ℝ` and `n ∈ ℕ`, `shiftedPairVonMangoldt a n = 0 ↔ Λ(n) = 0`. -/
theorem shiftedPairVonMangoldt_eq_zero_iff (a : ℝ) (n : ℕ) :
    shiftedPairVonMangoldt a n = 0 ↔ (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
  by_cases hn : 1 ≤ n
  · unfold shiftedPairVonMangoldt
    rw [mul_eq_zero]
    have hpos : (n : ℝ) ^ a + (n : ℝ) ^ (-a) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (two_le_rpow_add_rpow_neg hn a))
    exact or_iff_left hpos
  · have hn0 : n = 0 := by omega
    subst hn0
    simp [shiftedPairVonMangoldt]

/-- **Blindness of `h0`, `rank`, and `h1` to diagonal reweighting by `shiftedPairVonMangoldt a`:**
for every length `N`, shift `a ∈ ℝ`, sample sequence `lam`, and sample count `R`, weighting
`dirichletSampling N lam R` by `shiftedPairVonMangoldt a` versus `Λ` yields the exact same `h0`,
the exact same `rank`, and the exact same obstruction count `h1`. -/
theorem h0_rank_h1_weightedDirichletSampling_shiftedPair_eq_vonMangoldt
    (N : ℕ) (a : ℝ) (lam : ℕ → ℝ) (R : ℕ) :
    h0 (weightedDirichletSampling N
        (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R) =
      h0 (weightedDirichletSampling N
        (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) ∧
    (weightedDirichletSampling N
        (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R).rank =
      (weightedDirichletSampling N
        (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R).rank ∧
    h1 (weightedDirichletSampling N
        (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R) =
      h1 (weightedDirichletSampling N
        (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) := by
  apply rank_and_h1_mul_diagonal_eq_of_iff_eq_zero
  intro m
  simp only [Complex.ofReal_eq_zero]
  exact shiftedPairVonMangoldt_eq_zero_iff a ((m : ℕ) + 1)

/-- For every `n ≥ 2` and `a ∈ ℝ`, `2^a + 2^{-a} ≤ n^a + n^{-a}`. -/
theorem two_rpow_add_two_rpow_neg_le {n : ℕ} (hn : 2 ≤ n) (a : ℝ) :
    (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) ≤ (n : ℝ) ^ a + (n : ℝ) ^ (-a) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have hn_pos : (0 : ℝ) < n := by linarith
  have h_mono : ∀ b : ℝ, 0 ≤ b →
      (2 : ℝ) ^ b + (2 : ℝ) ^ (-b) ≤ (n : ℝ) ^ b + (n : ℝ) ^ (-b) := by
    intro b hb
    have hu : (2 : ℝ) ^ b ≤ (n : ℝ) ^ b := Real.rpow_le_rpow (by norm_num) hn2 hb
    have hu1 : 1 ≤ (2 : ℝ) ^ b := Real.one_le_rpow (by norm_num) hb
    have hprod2 : (2 : ℝ) ^ b * (2 : ℝ) ^ (-b) = 1 := by
      rw [← Real.rpow_add h2_pos, add_neg_cancel, Real.rpow_zero]
    have hprodn : (n : ℝ) ^ b * (n : ℝ) ^ (-b) = 1 := by
      rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero]
    have hinvn0 : 0 ≤ (n : ℝ) ^ (-b) := le_of_lt (Real.rpow_pos_of_pos hn_pos (-b))
    have hfac : 0 ≤ 1 - (2 : ℝ) ^ (-b) * (n : ℝ) ^ (-b) := by
      have hinv2 : (2 : ℝ) ^ (-b) ≤ 1 := by nlinarith
      have hinvn : (n : ℝ) ^ (-b) ≤ 1 := by nlinarith
      nlinarith
    have hdiff :
        ((n : ℝ) ^ b + (n : ℝ) ^ (-b)) - ((2 : ℝ) ^ b + (2 : ℝ) ^ (-b)) =
          ((n : ℝ) ^ b - (2 : ℝ) ^ b) * (1 - (2 : ℝ) ^ (-b) * (n : ℝ) ^ (-b)) := by
      linear_combination ((2 : ℝ) ^ (-b)) * hprodn - ((n : ℝ) ^ (-b)) * hprod2
    linarith [mul_nonneg (sub_nonneg.mpr hu) hfac]
  rcases le_or_gt 0 a with ha | ha
  · exact h_mono a ha
  · have h := h_mono (-a) (by linarith)
    simpa [neg_neg, add_comm] using h

/-- For every `n ∈ ℕ` and `a ∈ ℝ`, `((2 : ℝ)^a + (2 : ℝ)^(-a)) * Λ(n) ≤ shiftedPairVonMangoldt a n`. -/
theorem two_rpow_mul_vonMangoldt_le_shiftedPair (a : ℝ) (n : ℕ) :
    ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) * (ArithmeticFunction.vonMangoldt n : ℝ) ≤
      shiftedPairVonMangoldt a n := by
  by_cases hn : 2 ≤ n
  · unfold shiftedPairVonMangoldt
    rw [mul_comm (ArithmeticFunction.vonMangoldt n : ℝ)]
    exact mul_le_mul_of_nonneg_right (two_rpow_add_two_rpow_neg_le hn a)
      ArithmeticFunction.vonMangoldt_nonneg
  · have hz : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
      interval_cases n <;> simp
    simp [shiftedPairVonMangoldt, hz]

/-- **Frobenius-mass inflation on `weightedDirichletSampling` under `shiftedPairVonMangoldt a`:**
for every `N : ℕ`, `a ∈ ℝ`, sample sequence `lam`, and `R : ℕ`,
`((2 : ℝ)^a + (2 : ℝ)^(-a))^2 * frobeniusMass (weightedDirichletSampling N Λ lam R) ≤
frobeniusMass (weightedDirichletSampling N (shiftedPairVonMangoldt a) lam R)`. -/
theorem frobeniusMass_weightedDirichletSampling_shiftedPair_ge
    (N : ℕ) (a : ℝ) (lam : ℕ → ℝ) (R : ℕ) :
    ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) ^ 2 *
        frobeniusMass (weightedDirichletSampling N
          (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) ≤
      frobeniusMass (weightedDirichletSampling N
        (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R) := by
  rw [frobeniusMass_weightedDirichletSampling, frobeniusMass_weightedDirichletSampling,
    mul_left_comm (((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) ^ 2) ((R : ℝ) + 1), Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by positivity)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hle := two_rpow_mul_vonMangoldt_le_shiftedPair a ((m : ℕ) + 1)
  have h0 : 0 ≤ ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) *
      (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℝ) :=
    mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg
  have hsq :
      (((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) *
          (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℝ)) ^ 2 ≤
        shiftedPairVonMangoldt a ((m : ℕ) + 1) ^ 2 :=
    pow_le_pow_left₀ h0 hle 2
  linarith [show (((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) *
      (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℝ)) ^ 2 =
    ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) ^ 2 *
      (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℝ) ^ 2 by ring]

/-- **Strict Frobenius-mass selectivity against `shiftedPairVonMangoldt a` (`a ≠ 0`, `2 ≤ N`):**
while `h0`, `rank`, and `h1` cannot distinguish `shiftedPairVonMangoldt a` from `Λ`, the Frobenius
mass of `weightedDirichletSampling` is strictly positive for `Λ` and strictly more than `4` times
larger for `shiftedPairVonMangoldt a`. -/
theorem frobeniusMass_weightedDirichletSampling_shiftedPair_gt
    {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : a ≠ 0) (lam : ℕ → ℝ) (R : ℕ) :
    0 < frobeniusMass (weightedDirichletSampling N
        (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) ∧
    4 * frobeniusMass (weightedDirichletSampling N
        (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) <
      frobeniusMass (weightedDirichletSampling N
        (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R) := by
  have hpos_mass :
      0 < frobeniusMass (weightedDirichletSampling N
          (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) := by
    rw [frobeniusMass_weightedDirichletSampling]
    refine mul_pos (by positivity) ?_
    let m₁ : Fin N := ⟨1, hN⟩
    have hm₁_pos : 0 < ‖(ArithmeticFunction.vonMangoldt ((m₁ : ℕ) + 1) : ℂ)‖ ^ 2 := by
      simp only [m₁, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [show (1 : ℕ) + 1 = 2 by rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact pow_pos (Real.log_pos (by norm_num)) 2
    have hle_sum :
        ‖(ArithmeticFunction.vonMangoldt ((m₁ : ℕ) + 1) : ℂ)‖ ^ 2 ≤
          ∑ m : Fin N, ‖(ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun m : Fin N => ‖(ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)‖ ^ 2)
        (fun m _ => sq_nonneg _) (Finset.mem_univ m₁)
    exact lt_of_lt_of_le hm₁_pos hle_sum
  refine ⟨hpos_mass, ?_⟩
  have hgt2 := two_lt_two_rpow_add_two_rpow_neg ha
  have hgt4 : 4 < ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) ^ 2 := by nlinarith
  have hge := frobeniusMass_weightedDirichletSampling_shiftedPair_ge N a lam R
  nlinarith

/-! ### 2. Band-limited tests on an aperture, prime-power nodes, and the Landau–Markov & Landau–Widom density theorems -/

/-- The `L²` norm squared of `(realWeilTestFn f hf hfc).1` equals `∫ x, f x ^ 2`. -/
theorem integral_norm_realWeilTestFn_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) = ∫ x : ℝ, f x ^ 2 := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change ‖(f u : ℂ)‖ ^ 2 = f u ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Cutoff-free `69/2` Landau–Markov spectral gap on prime-blind real tests:**
for any real `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, vanishing prime-power node evaluation
`logVector (realWeilTestFn f hf hfc) = 0`, and `0 < ∫ x, f x ^ 2`,
`(69 / 2) * ∫ x, f x ^ 2 < spectralSecondMoment (realWeilTestFn f hf hfc).1`. -/
theorem sixty_nine_halves_l2_lt_spectralSecondMoment_of_primeBlind
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hpos : 0 < ∫ x : ℝ, f x ^ 2) :
    (69 / 2 : ℝ) * (∫ x : ℝ, f x ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  have hpos' : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
    rwa [integral_norm_realWeilTestFn_sq hf hfc]
  have hlt :=
    sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero_unconditional
      hf hfc hcosh hint2 hblind hpos'
  rwa [integral_norm_realWeilTestFn_sq hf hfc] at hlt

/-- **The Landau–Markov frame bound on prime-blind sections (`K_Landau = 69 / 2`):**
every `f ∈ C²_c(ℝ)` annihilated by the even pole (`coshHalfMoment f = 0`) and by the prime-power
node divisor (`logVector (realWeilTestFn f hf hfc) = 0`) satisfies
`∫ x, f x ^ 2 ≤ (2 / 69) * spectralSecondMoment (realWeilTestFn f hf hfc).1`. -/
theorem l2_le_two_sixty_ninths_spectralSecondMoment_of_primeBlind
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hblind : logVector (realWeilTestFn f hf hfc) = 0) :
    (∫ x : ℝ, f x ^ 2) ≤
      (2 / 69 : ℝ) * spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  have hl2_nonneg : 0 ≤ ∫ x : ℝ, f x ^ 2 := integral_nonneg fun x => sq_nonneg (f x)
  rcases eq_or_lt_of_le hl2_nonneg with h0 | hpos
  · rw [← h0]
    have hspec_nonneg : 0 ≤ spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
      unfold spectralSecondMoment
      positivity
    positivity
  · have hlt :=
      sixty_nine_halves_l2_lt_spectralSecondMoment_of_primeBlind hf hfc hcosh hint2 hblind hpos
    linarith

private theorem eq_zero_of_integral_sq_eq_zero {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hint0 : (∫ x, f x ^ 2) = 0) (x : ℝ) :
    f x = 0 := by
  have hint_mul : Integrable fun u : ℝ => f u * f u :=
    (hf.mul hf).integrable_of_hasCompactSupport hfc.mul_right
  have hint : Integrable fun u : ℝ => f u ^ 2 := by
    simpa only [sq] using hint_mul
  have hae : (fun u : ℝ => f u ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg (f u)) hint).mp hint0
  have hfun : (fun u : ℝ => f u ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq volume (hf.pow 2) continuous_zero).mp hae
  exact sq_eq_zero_iff.mp (congrFun hfun x)

/-- **The `69/2` Prime-Blind Section Vanishing Theorem:**
if `f ∈ C²_c(ℝ)` vanishes on all prime-power nodes (`logVector (realWeilTestFn f hf hfc) = 0`),
has `coshHalfMoment f = 0`, and has spectral second moment at most `(69 / 2) ∫ f²`, then
`∫ f² = 0` and `f` vanishes identically on `ℝ`. -/
theorem primeBlind_eq_zero_of_spectralSecondMoment_le_sixty_nine_halves
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hspec : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (69 / 2 : ℝ) * ∫ x, f x ^ 2) :
    (∫ x, f x ^ 2) = 0 ∧ ∀ x : ℝ, f x = 0 := by
  have hl2_nonneg : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg (f x)
  have hl2_zero : (∫ x, f x ^ 2) = 0 := by
    by_contra hne
    have hpos : 0 < ∫ x, f x ^ 2 := lt_of_le_of_ne hl2_nonneg (Ne.symm hne)
    have hlt :=
      sixty_nine_halves_l2_lt_spectralSecondMoment_of_primeBlind hf hfc hcosh hint2 hblind hpos
    exact lt_irrefl _ (lt_of_lt_of_le hlt hspec)
  exact ⟨hl2_zero, eq_zero_of_integral_sq_eq_zero hf.continuous hfc hl2_zero⟩

/-- **Continuous Nyquist section-space vanishing (`finrank = 0`):**
any `ℝ`-subspace `W ⊆ (ℝ → ℝ)` of `C²_c(ℝ)` prime-blind sections with `coshHalfMoment = 0` and rms
spectral height `T² ≤ 69 / 2` is the zero subspace and has `Module.finrank ℝ W = 0` at every
aperture. -/
theorem finrank_primeBlind_subspace_eq_zero (W : Submodule ℝ (ℝ → ℝ)) {T : ℝ}
    (hT : T ^ 2 ≤ 69 / 2)
    (hW : ∀ f ∈ W, ∃ (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f),
      coshHalfMoment f = 0 ∧
        (Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2)) ∧
        logVector (realWeilTestFn f hf hfc) = 0 ∧
        spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤ T ^ 2 * ∫ x, f x ^ 2) :
    W = ⊥ ∧ Module.finrank ℝ W = 0 := by
  have hbot : W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hfW
    obtain ⟨hf, hfc, hcosh, hint2, hlog, hspec⟩ := hW f hfW
    have hl2_nonneg : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg (f x)
    have hspec' : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
        (69 / 2 : ℝ) * ∫ x, f x ^ 2 :=
      le_trans hspec (mul_le_mul_of_nonneg_right hT hl2_nonneg)
    funext x
    exact (primeBlind_eq_zero_of_spectralSecondMoment_le_sixty_nine_halves
      hf hfc hcosh hint2 hlog hspec').2 x
  refine ⟨hbot, ?_⟩
  rw [hbot, finrank_bot]

/-- **Cutoff-free `69/2` Landau–Markov spectral gap on the nonnegative log-value cone:**
if `f ∈ C²_c(ℝ)` has `coshHalfMoment f = 0` and nonnegative node evaluations
`0 ≤ logValue (realWeilTestFn f hf hfc).1 n` at all `n ≥ 2`, then `0 < ∫ f²` forces
`(69 / 2) * ∫ f² < spectralSecondMoment (realWeilTestFn f hf hfc).1`. -/
theorem sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg_unconditional
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hpos_log : ∀ n : ℕ, 2 ≤ n → 0 ≤ logValue (realWeilTestFn f hf hfc).1 n)
    (hpos : 0 < ∫ x : ℝ, f x ^ 2) :
    (69 / 2 : ℝ) * (∫ x : ℝ, f x ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest (realWeilTestFn f hf hfc)
  have hpos' : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
    rwa [integral_norm_realWeilTestFn_sq hf hfc]
  have hlt :=
    sixty_nine_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg
      hf hfc hcosh hint2 (by omega) hN0 hN
      (fun n hn => hpos_log n (Finset.mem_Icc.mp hn).1) hpos'
  rwa [integral_norm_realWeilTestFn_sq hf hfc] at hlt

/-- **Cutoff-free `33` Landau–Markov spectral gap on the general unit-step cone:**
if `f ∈ C²_c(ℝ)` has `coshHalfMoment f = 0` and nonnegative unit-step prime-blind counterterm, then
`0 < ∫ f²` forces `33 * ∫ f² < spectralSecondMoment (realWeilTestFn f hf hfc).1`. -/
theorem thirty_three_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg_unconditional
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc))
    (hpos : 0 < ∫ x : ℝ, f x ^ 2) :
    33 * (∫ x : ℝ, f x ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  obtain ⟨N, hN2, hN0, hN⟩ := exists_support_cutoff_weilTest (realWeilTestFn f hf hfc)
  have hpos' : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
    rwa [integral_norm_realWeilTestFn_sq hf hfc]
  have hlt :=
    thirty_three_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg
      hf hfc hcosh hint2 (by omega) hN0 hN hunit hpos'
  rwa [integral_norm_realWeilTestFn_sq hf hfc] at hlt

/-- **Prime-power node criticality vs. trans-Nyquist Landau–Widom section supply:**
1. *Node criticality:* `ZeroPoleBlindPositiveOn 𝒩` holds iff `RiemannHypothesis` holds and `𝒩`
   contains every prime power; deleting `4` or restricting to `{p | p.Prime}` falsifies it
   unconditionally, whereas deleting `6` changes nothing.
2. *Sub-Nyquist Landau–Markov vanishing (`T² ≤ 69/2`):* every `C²_c` prime-blind test with
   `coshHalfMoment = 0` and `spectralSecondMoment ≤ (69 / 2) ∫ f²` vanishes identically.
3. *Trans-Nyquist Landau–Widom near-radical supply (`T = 2π e^{2ℓ}`):* for every `0 < η ≤ 1` and
   all large `L`, the level-`L` Hodge-class tests contain a subspace `V` of dimension at least
   `(2 - η) e^{2L}` on which `‖zetaZeroConfig.W f f‖ ≤ exp(-η² e^{2L} / (300 L)) ∫ ‖f‖²`. -/
theorem primePower_node_criticality_and_landauWidom_supply :
    (∀ 𝒩 : Set ℕ,
      ZeroPoleBlindPositiveOn 𝒩 ↔
        RiemannHypothesis ∧ ∀ n, 2 ≤ n → ArithmeticFunction.vonMangoldt n ≠ 0 → n ∈ 𝒩) ∧
    (∀ 𝒩 : Set ℕ, ¬ ZeroPoleBlindPositiveOn (𝒩 \ {4})) ∧
    (∀ 𝒩 : Set ℕ, ZeroPoleBlindPositiveOn (𝒩 \ {6}) ↔ ZeroPoleBlindPositiveOn 𝒩) ∧
    ¬ ZeroPoleBlindPositiveOn {n | n.Prime} ∧
    (∀ {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f),
      coshHalfMoment f = 0 →
      (Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2)) →
      logVector (realWeilTestFn f hf hfc) = 0 →
      spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤ (69 / 2 : ℝ) * ∫ x, f x ^ 2 →
      ∀ x : ℝ, f x = 0) ∧
    (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
        (2 - η) * Real.exp (2 * L) ≤ (Module.finrank ℂ V : ℝ) ∧
        (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧
          paperFT f (-(I / 2)) = 0) ∧
        ∀ f ∈ V, ‖zetaZeroConfig.W f f‖ ≤
          Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L))) * ∫ u, ‖f u‖ ^ 2) :=
  ⟨fun _ => zeroPoleBlindPositiveOn_iff,
   not_zeroPoleBlindPositiveOn_diff_four,
   zeroPoleBlindPositiveOn_diff_six_iff,
   not_zeroPoleBlindPositiveOn_primes,
   fun hf hfc hcosh hint2 hblind hspec =>
     (primeBlind_eq_zero_of_spectralSecondMoment_le_sixty_nine_halves
       hf hfc hcosh hint2 hblind hspec).2,
   zeta_weil_near_radical_sharp_count⟩

/-! ### 3. Identifying `h⁰`, `h¹`, and the Chebyshev defect `E(s) = e^s + s - 1 - ψ(e^s)` as the correction -/

/-- **Box-level continuous `h⁰` section supply** on `[0, s]`: the nonnegative excess
`max (polarBoxDoF s - primeNodeCount s) 0` of polar degrees of freedom over prime-power nodes. -/
def boxH0Supply (s : ℝ) : ℝ :=
  max (polarBoxDoF s - primeNodeCount s) 0

/-- **Box-level continuous `h¹` node obstruction** on `[0, s]`: the nonnegative excess
`max (primeNodeCount s - polarBoxDoF s) 0` of prime-power node weight over polar degrees of
freedom. -/
def boxH1Obstruction (s : ℝ) : ℝ :=
  max (primeNodeCount s - polarBoxDoF s) 0

/-- **Generalized box-level continuous `h¹` node obstruction** for an arbitrary weight
`w : ℕ → ℝ` on `[0, s]`: `max (-generalizedTwoPoleDefect w s) 0`. -/
def generalizedBoxH1Obstruction (w : ℕ → ℝ) (s : ℝ) : ℝ :=
  max (-generalizedTwoPoleDefect w s) 0

/-- **Orthogonal `h⁰ - h¹` decomposition of the box Chebyshev defect `E(s)`:**
for every `s : ℝ`, `boxH0Supply s ≥ 0`, `boxH1Obstruction s ≥ 0`,
`boxH0Supply s * boxH1Obstruction s = 0`, and
`boxH0Supply s - boxH1Obstruction s = polarBoxDoF s - primeNodeCount s = chebyshevTwoPoleDefect s`. -/
theorem boxH0Supply_sub_boxH1Obstruction (s : ℝ) :
    0 ≤ boxH0Supply s ∧
    0 ≤ boxH1Obstruction s ∧
    boxH0Supply s * boxH1Obstruction s = 0 ∧
    boxH0Supply s - boxH1Obstruction s = chebyshevTwoPoleDefect s := by
  unfold boxH0Supply boxH1Obstruction
  refine ⟨le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · rcases le_total 0 (polarBoxDoF s - primeNodeCount s) with h | h
    · have h2 : max (primeNodeCount s - polarBoxDoF s) 0 = 0 :=
        max_eq_right (by linarith)
      rw [h2, mul_zero]
    · have h1 : max (polarBoxDoF s - primeNodeCount s) 0 = 0 :=
        max_eq_right h
      rw [h1, zero_mul]
  · rw [← polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect s]
    rcases le_total 0 (polarBoxDoF s - primeNodeCount s) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring

/-- Below the first prime (`0 ≤ s < log 2`), `boxH1Obstruction s = 0` and
`boxH0Supply s = e^s + s - 1`. -/
theorem boxH1Obstruction_eq_zero_below_log_two {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s < Real.log 2) :
    boxH1Obstruction s = 0 ∧ boxH0Supply s = Real.exp s + s - 1 := by
  have hexp : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hs2
      _ = 2 := Real.exp_log (by norm_num)
  have hfl : ⌊Real.exp s⌋₊ < 2 := (Nat.floor_lt (by positivity)).mpr hexp
  have hlag : primeNodeCount s = 0 := by
    unfold primeNodeCount lagChebyshev
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk1 : k = 0 ∨ k = 1 := by omega
    rcases hk1 with rfl | rfl <;> simp
  have hdof : polarBoxDoF s = Real.exp s + s - 1 := by
    rw [polarBoxDoF_eq_twoPoleWeight, twoPoleWeight]
  have hnn : 0 ≤ Real.exp s + s - 1 := by
    have hexp1 : 1 ≤ Real.exp s := Real.one_le_exp hs0
    linarith
  unfold boxH1Obstruction boxH0Supply
  rw [hlag, hdof, sub_zero, zero_sub]
  exact ⟨max_eq_right (neg_nonpos.mpr hnn), max_eq_left hnn⟩

/-- At the first prime scale `s = log 2`, `chebyshevTwoPoleDefect (log 2) = 1 > 0`, so
`boxH1Obstruction (log 2) = 0` and `boxH0Supply (log 2) = 1`. -/
theorem boxH1Obstruction_eq_zero_at_log_two :
    chebyshevTwoPoleDefect (Real.log 2) = 1 ∧
    boxH1Obstruction (Real.log 2) = 0 ∧
    boxH0Supply (Real.log 2) = 1 := by
  have hcheb : chebyshevTwoPoleDefect (Real.log 2) = 1 := by
    unfold chebyshevTwoPoleDefect twoPoleWeight lagChebyshev
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
    have hIcc : Finset.Icc 0 2 = ({0, 1, 2} : Finset ℕ) := rfl
    rw [hfl, hIcc]
    simp only [Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1, 2} : Finset ℕ)),
      Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)), Finset.sum_singleton,
      ArithmeticFunction.map_zero, ArithmeticFunction.vonMangoldt_apply_one,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
    ring
  have hdiff : polarBoxDoF (Real.log 2) - primeNodeCount (Real.log 2) = 1 := by
    rw [polarBoxDoF_sub_primeNodeCount_eq_chebyshevTwoPoleDefect, hcheb]
  have hneg : primeNodeCount (Real.log 2) - polarBoxDoF (Real.log 2) = -1 := by linarith
  unfold boxH1Obstruction boxH0Supply
  rw [hdiff, hneg]
  exact ⟨hcheb, max_eq_right (by norm_num), max_eq_left (by norm_num)⟩

/-- **Selectivity of the box `h¹` obstruction against `shiftedPairVonMangoldt a` at `s = log 2`:**
whenever `1 + 1 / log 2 < 2^a + 2^{-a}`, the shifted-pair node weight already exceeds the polar box
degrees of freedom at the first prime `s = log 2`, turning on a strictly positive `h¹` obstruction
`0 < generalizedBoxH1Obstruction (shiftedPairVonMangoldt a) (log 2)`. -/
theorem generalizedBoxH1Obstruction_shiftedPair_log_two_pos {a : ℝ}
    (ha : 1 + 1 / Real.log 2 < (2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) :
    0 < generalizedBoxH1Obstruction (shiftedPairVonMangoldt a) (Real.log 2) := by
  have hdef : generalizedTwoPoleDefect (shiftedPairVonMangoldt a) (Real.log 2) =
      1 + Real.log 2 - ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) * Real.log 2 := by
    unfold generalizedTwoPoleDefect twoPoleWeight weightedNodeCount
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
    have hIcc : Finset.Icc 0 2 = ({0, 1, 2} : Finset ℕ) := rfl
    rw [hfl, hIcc]
    simp only [Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1, 2} : Finset ℕ)),
      Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)), Finset.sum_singleton,
      shiftedPairVonMangoldt, ArithmeticFunction.map_zero,
      ArithmeticFunction.vonMangoldt_apply_one,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_lt_mul_of_pos_right ha hlog2
  have hsimp : (1 + 1 / Real.log 2) * Real.log 2 = Real.log 2 + 1 := by
    field_simp [ne_of_gt hlog2]
  have hneg : generalizedTwoPoleDefect (shiftedPairVonMangoldt a) (Real.log 2) < 0 := by linarith
  unfold generalizedBoxH1Obstruction
  exact lt_max_of_lt_left (neg_pos.mpr hneg)

/-- The **lag-derivative test density**
`2 e^{-s/2} (crossCorrelation F s - autoCorrelation F s / 2)` appearing in the Chebyshev-defect
Riemann–Roch ledger on `(0, 2r]`. -/
def lagDerivativeWeight (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2)

/-- The **archimedean gauge budget (`archGaugeBudget`)** of a test `F` on `(0, 2r]` at plateau
radius `R`: `surplusPool + crossingPotentialTerm + gaugeRemainder`. -/
def archGaugeBudget (r R : ℝ) (F : ℝ → ℝ) : ℝ :=
  surplusPool (aperturePlateau r R) F +
    crossingPotentialTerm (aperturePlateau r R) F +
    gaugeRemainder (aperturePlateau r R) F

/-- The **net polar minus archimedean gauge budget (`apertureNetPolarGauge`)** of a cycle
`x : ℝ × ℝ × oddRealTestsAt r` on `scalingSubsurface (oddRealTestsAt r)`:
`(scalingSubsurface (oddRealTestsAt r)).polar x x - archGaugeBudget r R (x.2.2.1 : ℝ → ℝ)`. -/
def apertureNetPolarGauge (r R : ℝ) (x : ℝ × ℝ × oddRealTestsAt r) : ℝ :=
  (scalingSubsurface (oddRealTestsAt r)).polar x x -
    archGaugeBudget r R (x.2.2.1 : ℝ → ℝ)

/-- The **continuous `h¹` Chebyshev-defect correction (`apertureH1ChebyshevCorrection`)** of a test
`F` at aperture `r`: the integral of `chebyshevTwoPoleDefect s = e^s + s - 1 - ψ(e^s)` against
`lagDerivativeWeight F s` over `(0, 2r]`. -/
def apertureH1ChebyshevCorrection (r : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s * lagDerivativeWeight F s

/-- The **prime-power node correlation obstruction (`primeNodeCorrelationObstruction`)** of a test
`F` at aperture `r`: the weighted sum of `autoCorrelation F (log n)` over all prime-power shifts
`n ∈ relevantShifts r`. -/
def primeNodeCorrelationObstruction (r : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∑ n ∈ relevantShifts r, 2 * vonMangoldtAtom n * autoCorrelation F (Real.log n)

/-- A test `F : ℝ → ℝ` is **horizon-prime-blind** at aperture `r` if its autocorrelation vanishes
at every prime-power node `log n` with `n ∈ relevantShifts r`. -/
def IsHorizonPrimeBlind (F : ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ n ∈ relevantShifts r, autoCorrelation F (Real.log n) = 0

/-- **Decomposition of the `h¹` Chebyshev-defect correction into pole charge plus prime-power node
obstruction:** for every odd `F ∈ C¹_c(ℝ)` supported in `[-r, r]` (`r > 0`),
`apertureH1ChebyshevCorrection r F = reflectedPrimePolarCost F r =
poleCharge F + primeNodeCorrelationObstruction r F`. -/
theorem apertureH1ChebyshevCorrection_eq_poleCharge_add_primeNodeObstruction
    {F : ℝ → ℝ} {r : ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    apertureH1ChebyshevCorrection r F = reflectedPrimePolarCost F r ∧
    apertureH1ChebyshevCorrection r F =
      poleCharge F + primeNodeCorrelationObstruction r F := by
  have h1 : apertureH1ChebyshevCorrection r F = reflectedPrimePolarCost F r := by
    unfold apertureH1ChebyshevCorrection lagDerivativeWeight
    exact (reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc hF hFc hodd hr hsupp).symm
  have h2 : reflectedPrimePolarCost F r =
      primeNodeCorrelationObstruction r F + poleCharge F := by
    unfold primeNodeCorrelationObstruction
    exact reflectedPrimePolarCost_eq_sum_autoCorrelation_add_poleCharge
      hF.continuous hodd hr.le hsupp
  exact ⟨h1, by linarith⟩

/-- **Exact Continuous Nyquist–Riemann–Roch Defect Identity on `scalingSubsurface (oddRealTestsAt r)`:**
for every `0 < r < R` and every cycle `x : ℝ × ℝ × oddRealTestsAt r` with test component
`F = (x.2.2.1 : ℝ → ℝ)`, the Castelnuovo–Severi defect plus the `E(s)` Chebyshev-defect correction
equals the archimedean gauge budget:
`(scalingSubsurface (oddRealTestsAt r)).defect x x + apertureH1ChebyshevCorrection r F =
archGaugeBudget r R F`. -/
theorem aperture_nyquist_riemannRoch_defect_identity {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (x : ℝ × ℝ × oddRealTestsAt r) :
    (scalingSubsurface (oddRealTestsAt r)).defect x x +
        apertureH1ChebyshevCorrection r (x.2.2.1 : ℝ → ℝ) =
      archGaugeBudget r R (x.2.2.1 : ℝ → ℝ) := by
  have hled := scalingSubsurface_odd_defect_eq_chebyshevDefectLedger hr hrR x
  unfold apertureH1ChebyshevCorrection lagDerivativeWeight archGaugeBudget
  linarith

/-- **Exact Continuous Nyquist–Riemann–Roch Self-Intersection Identity on `scalingSubsurface (oddRealTestsAt r)`:**
for every `0 < r < R` and every cycle `x : ℝ × ℝ × oddRealTestsAt r`,
`x · x = apertureNetPolarGauge r R x + apertureH1ChebyshevCorrection r (x.2.2.1 : ℝ → ℝ)`. -/
theorem aperture_nyquist_riemannRoch_selfIntersection_identity {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (x : ℝ × ℝ × oddRealTestsAt r) :
    (scalingSubsurface (oddRealTestsAt r)).pair x x =
      apertureNetPolarGauge r R x +
        apertureH1ChebyshevCorrection r (x.2.2.1 : ℝ → ℝ) := by
  have hdef := aperture_nyquist_riemannRoch_defect_identity hr hrR x
  have hpol : (scalingSubsurface (oddRealTestsAt r)).defect x x =
      (scalingSubsurface (oddRealTestsAt r)).polar x x -
        (scalingSubsurface (oddRealTestsAt r)).pair x x := rfl
  unfold apertureNetPolarGauge
  rw [← hdef, hpol]
  ring

/-- **Bézout Criterion on `scalingSubsurface (oddRealTestsAt r)` in terms of the `E(s)` Correction:**
for every fixed `0 < r < R`, `sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r))`
satisfies `BezoutAxiom` (and `RiemannRochAxiom`) if and only if for every `f : oddRealTestsAt r`,
its `h¹` Chebyshev-defect correction is paid by its archimedean gauge budget:
`apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤ archGaugeBudget r R (f.1 : ℝ → ℝ)`. -/
theorem sectionEffectivityCone_odd_bezout_iff_apertureH1ChebyshevCorrection_le
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom
        (sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r))) ↔
      ∀ f : oddRealTestsAt r,
        apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤ archGaugeBudget r R (f.1 : ℝ → ℝ) := by
  rw [sectionEffectivityCone_bezout_iff_hodgeIndex,
    (scalingSubsurface (oddRealTestsAt r)).hodgeIndex_iff_defect_nonneg]
  constructor
  · intro h f
    have hd := h (0, 0, f)
    have hid := aperture_nyquist_riemannRoch_defect_identity hr hrR (0, 0, f)
    linarith
  · intro h x
    have hle := h x.2.2
    have hid := aperture_nyquist_riemannRoch_defect_identity hr hrR x
    linarith

/-- **Horizon-Prime-Blind Reduction of the `E(s)` Correction:**
if an odd test `F ∈ C¹_c(ℝ)` supported in `[-r, r]` (`r > 0`) vanishes on all prime-power nodes in
`(0, 2r]` (`IsHorizonPrimeBlind F r`), then `primeNodeCorrelationObstruction r F = 0` and
`apertureH1ChebyshevCorrection r F = poleCharge F = 2 * oddPoleMoment F ^ 2 ≥ 0`; if in addition
`oddPoleMoment F = 0`, then `apertureH1ChebyshevCorrection r F = 0` identically. -/
theorem apertureH1ChebyshevCorrection_of_isHorizonPrimeBlind
    {F : ℝ → ℝ} {r : ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0)
    (hpb : IsHorizonPrimeBlind F r) :
    primeNodeCorrelationObstruction r F = 0 ∧
    apertureH1ChebyshevCorrection r F = poleCharge F ∧
    0 ≤ apertureH1ChebyshevCorrection r F ∧
    (oddPoleMoment F = 0 → apertureH1ChebyshevCorrection r F = 0) := by
  have hobs : primeNodeCorrelationObstruction r F = 0 :=
    Finset.sum_eq_zero fun n hn => by rw [hpb n hn, mul_zero]
  have hdecomp :=
    (apertureH1ChebyshevCorrection_eq_poleCharge_add_primeNodeObstruction hF hFc hodd hr hsupp).2
  rw [hobs, add_zero] at hdecomp
  refine ⟨hobs, hdecomp, hdecomp ▸ poleCharge_nonneg F, fun hmom => ?_⟩
  rw [hdecomp, poleCharge, hmom, sq, mul_zero, mul_zero]

/-- **Unconditional payment of the `h¹` Chebyshev-defect correction past the first prime
(`0 < r ≤ 181/500`):** for every `0 < r ≤ 181/500`, `r < R`, and `f : oddRealTestsAt r`,
`apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤ archGaugeBudget r R (f.1 : ℝ → ℝ)`. -/
theorem apertureH1ChebyshevCorrection_le_archGaugeBudget_of_le
    {r R : ℝ} (hr0 : 0 < r) (hr : r ≤ 181 / 500) (hrR : r < R) (f : oddRealTestsAt r) :
    apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤ archGaugeBudget r R (f.1 : ℝ → ℝ) := by
  have hHI := scalingSubsurface_odd_hodgeIndex hr
  have hdef : 0 ≤ (scalingSubsurface (oddRealTestsAt r)).defect (0, 0, f) (0, 0, f) :=
    (scalingSubsurface (oddRealTestsAt r)).hodgeIndex_iff_defect_nonneg.mp hHI (0, 0, f)
  have hid := aperture_nyquist_riemannRoch_defect_identity hr0 hrR (0, 0, f)
  linarith

/-- **Unconditional all-aperture rate-`1/2` and PNT bounds on the `h¹` Chebyshev-defect correction:**
for every `0 < r < R` and `f : oddRealTestsAt r`,
`apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤ archGaugeBudget r R (f.1 : ℝ → ℝ) + 78 * e^r * ∫ f²`,
and for every `ε > 0` there exists `C ≥ 0` such that
`apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤ archGaugeBudget r R (f.1 : ℝ → ℝ) + ((8 + ε) * e^r + C) * ∫ f²`. -/
theorem apertureH1ChebyshevCorrection_le_archGaugeBudget_add_exp :
    (∀ (r R : ℝ), 0 < r → r < R → ∀ f : oddRealTestsAt r,
      apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤
        archGaugeBudget r R (f.1 : ℝ → ℝ) +
          78 * Real.exp r * ∫ u, (f.1 : ℝ → ℝ) u ^ 2) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r R : ℝ), 0 < r → r < R → ∀ f : oddRealTestsAt r,
      apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤
        archGaugeBudget r R (f.1 : ℝ → ℝ) +
          ((8 + ε) * Real.exp r + C) * ∫ u, (f.1 : ℝ → ℝ) u ^ 2) := by
  refine ⟨fun r R hr hrR f => ?_, fun ε hε => ?_⟩
  · have hd := scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp hr (0, 0, f)
    have hid := aperture_nyquist_riemannRoch_defect_identity hr hrR (0, 0, f)
    linarith
  · obtain ⟨C, hC0, hdef⟩ := exists_scalingSubsurface_odd_defect_ge_neg_eight_add_eps_mul_exp hε
    refine ⟨C, hC0, fun r R hr hrR f => ?_⟩
    have hd := hdef r hr (0, 0, f)
    have hid := aperture_nyquist_riemannRoch_defect_identity hr hrR (0, 0, f)
    linarith

/-- **The Nyquist–Riemann–Roch Width Dictionary Beyond Rank–Nullity:**
all-aperture payment of the `h¹` Chebyshev-defect correction `apertureH1ChebyshevCorrection r f`
by `archGaugeBudget r R f` (and its subexponential self-improvement) is unconditionally equivalent
to `RiemannHypothesis`, `rightZeros zetaZeroConfig = ∅`, `scalingSurface.HodgeIndex`,
`ZeroPoleBlindPositiveOn {n | IsPrimePow n}`, and the Bézout and Riemann–Roch axioms for
`sectionEffectivityCone` across all apertures. -/
theorem nyquistRiemannRoch_beyond_rankNullity_tfae : List.TFAE [
    RiemannHypothesis,
    rightZeros zetaZeroConfig = ∅,
    scalingSurface.HodgeIndex,
    ZeroPoleBlindPositiveOn {n : ℕ | IsPrimePow n},
    ∀ (r R : ℝ), 0 < r → r < R → ∀ f : oddRealTestsAt r,
      apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤ archGaugeBudget r R (f.1 : ℝ → ℝ),
    ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ f : oddRealTestsAt r,
      apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤
        archGaugeBudget r (r + 1) (f.1 : ℝ → ℝ) +
          C * Real.exp (2 * σ * r) * ∫ u, (f.1 : ℝ → ℝ) u ^ 2,
    ∀ r : ℝ, 0 < r →
      (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
        (sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r))),
    ∀ r : ℝ, 0 < r →
      (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom
        (sectionEffectivityCone (scalingSubsurface (oddRealTestsAt r)))] := by
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_rightZeros_zeta_eq_empty
  tfae_have 1 ↔ 3 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers
  tfae_have 2 ↔ 5 := by
    rw [rightZeros_zeta_eq_empty_iff_forall_odd_chebyshevDefectAllocation]
    rfl
  tfae_have 5 → 6 := by
    intro h σ _
    refine ⟨0, fun r hr f => ?_⟩
    have hle := h r (r + 1) hr (by linarith) f
    linarith
  tfae_have 6 → 2 := by
    intro h
    rw [rightZeros_zeta_eq_empty_iff_subexponential_scalingSubsurface_odd_defect_floor]
    intro σ hσ
    obtain ⟨C, hC⟩ := h σ hσ
    refine ⟨C, fun r hr x => ?_⟩
    have hid := aperture_nyquist_riemannRoch_defect_identity hr (by linarith : r < r + 1) x
    have hle := hC r hr x.2.2
    linarith
  tfae_have 2 ↔ 7 := by
    rw [rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex]
    exact forall₂_congr fun r _ =>
      (sectionEffectivityCone_riemannRoch_iff_hodgeIndex (scalingSubsurface (oddRealTestsAt r))).symm
  tfae_have 2 ↔ 8 := by
    rw [rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex]
    exact forall₂_congr fun r _ =>
      (sectionEffectivityCone_bezout_iff_hodgeIndex (scalingSubsurface (oddRealTestsAt r))).symm
  tfae_finish

/-- **Master Synthesis for Open Problem 3 (`nyquistRiemannRoch_beyond_rankNullity_synthesis`):**
1. *Dual Nyquist `h¹` bound and Frobenius-mass selectivity:* for every finite reading `A` with frame
   bound `K > 0`, `h1 A ≤ #nodes - frobeniusMass A / K`; while `h0`, `rank`, and `h1` of
   `weightedDirichletSampling` are blind to `shiftedPairVonMangoldt a`, its Frobenius mass is
   strictly more than `4` times larger for every `a ≠ 0` and `2 ≤ N`.
2. *Landau–Markov frame bound on the prime-power nodes:* every `C²_c` test `f` with
   `coshHalfMoment f = 0` vanishing on all prime-power nodes obeys
   `∫ f² ≤ (2 / 69) * spectralSecondMoment (realWeilTestFn f hf hfc).1`, so any subspace `W` of
   prime-blind sections with spectral height `T² ≤ 69 / 2` has `finrank ℝ W = 0`.
3. *Identification of the `h¹` Chebyshev-defect correction:* on `[0, s]`,
   `boxH0Supply s - boxH1Obstruction s = chebyshevTwoPoleDefect s = e^s + s - 1 - ψ(e^s)`, and on
   `scalingSubsurface (oddRealTestsAt r)`,
   `apertureH1ChebyshevCorrection r F = poleCharge F + primeNodeCorrelationObstruction r F`
   satisfies `defect x x + apertureH1ChebyshevCorrection r F = archGaugeBudget r R F`, is
   unconditionally paid on `(0, 181/500]`, and obeys the PNT `(8 + ε) e^r + C` bound across
   all apertures `r > 0`. -/
theorem nyquistRiemannRoch_beyond_rankNullity_synthesis :
    (∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ} {K : ℝ},
      0 < K → HasFrameBound A K →
      (h1 A : ℝ) ≤ (Fintype.card m : ℝ) - frobeniusMass A / K) ∧
    (∀ (N : ℕ), 2 ≤ N → ∀ (a : ℝ), a ≠ 0 → ∀ (lam : ℕ → ℝ) (R : ℕ),
      h0 (weightedDirichletSampling N
          (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R) =
        h0 (weightedDirichletSampling N
          (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) ∧
      h1 (weightedDirichletSampling N
          (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R) =
        h1 (weightedDirichletSampling N
          (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) ∧
      4 * frobeniusMass (weightedDirichletSampling N
          (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) <
        frobeniusMass (weightedDirichletSampling N
          (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R)) ∧
    (∀ {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f),
      coshHalfMoment f = 0 →
      (Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2)) →
      logVector (realWeilTestFn f hf hfc) = 0 →
      (∫ x : ℝ, f x ^ 2) ≤ (2 / 69 : ℝ) * spectralSecondMoment (realWeilTestFn f hf hfc).1) ∧
    (∀ s : ℝ, boxH0Supply s - boxH1Obstruction s = chebyshevTwoPoleDefect s) ∧
    (∀ {r R : ℝ}, 0 < r → r < R → ∀ x : ℝ × ℝ × oddRealTestsAt r,
      (scalingSubsurface (oddRealTestsAt r)).defect x x +
          apertureH1ChebyshevCorrection r (x.2.2.1 : ℝ → ℝ) =
        archGaugeBudget r R (x.2.2.1 : ℝ → ℝ) ∧
      (scalingSubsurface (oddRealTestsAt r)).pair x x =
        apertureNetPolarGauge r R x +
          apertureH1ChebyshevCorrection r (x.2.2.1 : ℝ → ℝ)) ∧
    (∀ {r R : ℝ}, 0 < r → r ≤ 181 / 500 → r < R → ∀ f : oddRealTestsAt r,
      apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤ archGaugeBudget r R (f.1 : ℝ → ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r R : ℝ), 0 < r → r < R → ∀ f : oddRealTestsAt r,
      apertureH1ChebyshevCorrection r (f.1 : ℝ → ℝ) ≤
        archGaugeBudget r R (f.1 : ℝ → ℝ) +
          ((8 + ε) * Real.exp r + C) * ∫ u, (f.1 : ℝ → ℝ) u ^ 2) :=
  ⟨fun hK0 hK => h1_le_nyquist hK0 hK,
   fun N hN a ha lam R =>
     ⟨(h0_rank_h1_weightedDirichletSampling_shiftedPair_eq_vonMangoldt N a lam R).1,
      (h0_rank_h1_weightedDirichletSampling_shiftedPair_eq_vonMangoldt N a lam R).2.2,
      (frobeniusMass_weightedDirichletSampling_shiftedPair_gt hN ha lam R).2⟩,
   fun hf hfc hcosh hint2 hblind =>
     l2_le_two_sixty_ninths_spectralSecondMoment_of_primeBlind hf hfc hcosh hint2 hblind,
   fun s => (boxH0Supply_sub_boxH1Obstruction s).2.2.2,
   fun hr hrR x =>
     ⟨aperture_nyquist_riemannRoch_defect_identity hr hrR x,
      aperture_nyquist_riemannRoch_selfIntersection_identity hr hrR x⟩,
   fun hr0 hr hrR f => apertureH1ChebyshevCorrection_le_archGaugeBudget_of_le hr0 hr hrR f,
   apertureH1ChebyshevCorrection_le_archGaugeBudget_add_exp.2⟩

end

end GaloisForLFunctions.ArithmeticOrientationTheory
