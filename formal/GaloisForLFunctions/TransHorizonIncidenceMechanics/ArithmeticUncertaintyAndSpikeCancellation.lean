import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedRenormalizedDefectAndPronicCeiling

/-!
# Pillar XI: Trans-Horizon Arithmetic Uncertainty Principle, Boundary-Spike Cancellation, and Two-Point Bézout Defect Averaging (`ArithmeticUncertaintyAndSpikeCancellation`)

A central analytical challenge in the trans-horizon regime `M > N` is that while the Dirichlet
polarization identity
$$2\,\widetilde{\mathcal{D}}_N(M; c) =
  -\sum_{k=1}^M \bigl(s_{N,c}(k + 1) - s_{N,c}(k)\bigr)^2 +
    s_{N,c}(M + 1)^2 - s_{N,c}(1)^2$$
controls every checkpoint where `s_{N,c}(M + 1)² ≤ s_{N,c}(1)²`, at a highly composite trans-horizon
integer `M + 1` the boundary spike `s_{N,c}(M + 1)²` can exceed `s_{N,c}(1)²`.

In this eleventh foundational pillar of **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics**,
we resolve how the Dirichlet oscillation sum itself absorbs composite trans-horizon spikes via three
unconditional structural theorems:

## Core Main Theorems (100% Unconditional)

1. **Exact Boundary-Spike Cancellation & Sign-Change / Predecessor-Zero Absorption
   (`two_mul_sieveRenormalizedPrefixDefect_eq_neg_init_dirichlet_add_coprime_pair`,
   `sieveRenormalizedPrefixDefect_nonpos_of_mul_succ_nonpos`,
   `sieveRenormalizedPrefixDefect_nonpos_of_eq_zero`)**:
   Extracting the final step `k = M` from the Dirichlet sum cancels `+s_{N,c}(M + 1)²` **100%
   identically** at every `M ≥ 1`:
   $$2\,\widetilde{\mathcal{D}}_N(M; c) =
     -\sum_{k=1}^{M-1} \bigl(s_{N,c}(k + 1) - s_{N,c}(k)\bigr)^2 +
       2\,s_{N,c}(M)\,s_{N,c}(M + 1) - s_{N,c}(M)^2 - s_{N,c}(1)^2.$$
   Consequently, **regardless of how large the composite spike `|s_{N,c}(M + 1)|` is**:
   - Whenever `s_{N,c}(M) * s_{N,c}(M + 1) ≤ 0` (the sieve changes sign or vanishes between the
     coprime neighbors `M` and `M + 1`),
     $$2\,\widetilde{\mathcal{D}}_N(M; c) \le -s_{N,c}(M)^2 - s_{N,c}(1)^2 \le 0.$$
   - In particular, whenever `s_{N,c}(M) = 0` (for example, anywhere in the infinite trans-horizon
     Möbius zero cone `M = q * r`), the spike `s_{N,c}(M + 1)²` at `M + 1` is **100% absorbed** by
     the single Dirichlet jump `-(s_{N,c}(M + 1) - s_{N,c}(M))²`, forcing
     `sieveRenormalizedPrefixDefect N M c ≤ -(s_{N,c}(1)²) / 2 ≤ 0`.

2. **Two-Point Consecutive Defect Average Law (`sieveRenormalizedPrefixDefect_pred_add_self_eq`,
   `sieveRenormalizedPrefixDefect_pred_add_self_nonpos_of_mul_le_one_sq`)**:
   Averaging `sieveRenormalizedPrefixDefect` across two consecutive prefixes `M - 1` and `M` (`M ≥ 2`)
   cancels **both** squared boundary spikes `s_{N,c}(M)²` and `s_{N,c}(M + 1)²` simultaneously,
   leaving only the coprime Bézout product `s_{N,c}(M) s_{N,c}(M + 1)`:
   $$\widetilde{\mathcal{D}}_N(M - 1; c) + \widetilde{\mathcal{D}}_N(M; c) =
     -\sum_{k=1}^{M-1} \bigl(s_{N,c}(k + 1) - s_{N,c}(k)\bigr)^2 +
       s_{N,c}(M)\,s_{N,c}(M + 1) - s_{N,c}(1)^2.$$

3. **Discrete Path Poincaré Inequality & Trans-Horizon Arithmetic Uncertainty Principle
   (`path_poincare_step_identity`, `sq_sub_le_length_mul_sum_range_addDiff_sq`,
   `sieve_uncertainty_lower_bound_of_eq_zero`,
   `sieve_uncertainty_lower_bound_of_rough_anchor`)**:
   Via the exact variance-defect identity
   $$L\Bigl((L + 1)(S + Y^2) - (X + Y)^2\Bigr) = (L + 1)(L S - X^2) + (X - L Y)^2,$$
   every sequence `f : ℕ → ℝ` satisfies the **Discrete Path Poincaré Inequality** across any
   window `[a, a + L]`:
   $$\bigl(f(a + L) - f(a)\bigr)^2 \le
     (L : \mathbb{R}) \sum_{j=0}^{L-1} \bigl(f(a + j + 1) - f(a + j)\bigr)^2.$$
   Applied to `sieveSeq N c`, this establishes the **Trans-Horizon Arithmetic Uncertainty Principle**:
   any composite spike `s_{N,c}(a + L)` at additive distance `L ≥ 1` from a zero-cone anchor
   (`s_{N,c}(a) = 0`) or an `N`-rough anchor (`s_{N,c}(a) = s_{N,c}(1)`) must pay at least
   `s_{N,c}(a + L)² / L` (respectively `(s_{N,c}(a + L) - s_{N,c}(1))² / L`) in local step-to-step
   Dirichlet variation energy.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Boundary-Spike Cancellation & Predecessor-Zero / Sign-Change Absorption -/

/-- **Exact Boundary-Spike Cancellation Identity
(`two_mul_sieveRenormalizedPrefixDefect_eq_neg_init_dirichlet_add_coprime_pair`):**
For every cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and `M ≥ 1`, extracting the `k = M` jump from the
Dirichlet sum cancels `+s_{N,c}(M + 1)²` identically:
`2 * sieveRenormalizedPrefixDefect N M c = -(∑ k ∈ Icc 1 (M - 1), (s_{N,c}(k+1) - s_{N,c}(k))²) + 2 * s_{N,c}(M) * s_{N,c}(M + 1) - s_{N,c}(M)² - s_{N,c}(1)²`. -/
theorem two_mul_sieveRenormalizedPrefixDefect_eq_neg_init_dirichlet_add_coprime_pair
    (N : ℕ) {M : ℕ} (hM : 1 ≤ M) (c : ℕ → ℝ) :
    2 * sieveRenormalizedPrefixDefect N M c =
      -(∑ k ∈ Finset.Icc 1 (M - 1),
          (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) +
        2 * sieveSeq N c M * sieveSeq N c (M + 1) -
        sieveSeq N c M ^ (2 : ℕ) -
        sieveSeq N c 1 ^ (2 : ℕ) := by
  have hpol := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hM c
  have hsplit := Finset.sum_Icc_succ_top (by omega : 1 ≤ M - 1 + 1)
    (fun k => (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ))
  rw [Nat.sub_add_cancel hM] at hsplit
  rw [hsplit] at hpol
  linarith [hpol, sq (sieveSeq N c (M + 1) - sieveSeq N c M)]

/-- **Sign-Change Spike Absorption Theorem
(`sieveRenormalizedPrefixDefect_nonpos_of_mul_succ_nonpos`):**
For every `N : ℕ`, weight `c : ℕ → ℝ`, and `M ≥ 1`, whenever `sieveSeq N c M * sieveSeq N c (M + 1) ≤ 0`
(i.e. `sieveSeq N c` changes sign or vanishes across `M ↦ M + 1`), the boundary spike
`sieveSeq N c (M + 1)²` is completely absorbed by the `k = M` Dirichlet jump, yielding:
`2 * sieveRenormalizedPrefixDefect N M c ≤ -sieveSeq N c M ^ 2 - sieveSeq N c 1 ^ 2 ≤ 0`. -/
theorem sieveRenormalizedPrefixDefect_nonpos_of_mul_succ_nonpos
    (N : ℕ) {M : ℕ} (hM : 1 ≤ M) (c : ℕ → ℝ)
    (hsign : sieveSeq N c M * sieveSeq N c (M + 1) ≤ 0) :
    2 * sieveRenormalizedPrefixDefect N M c ≤
        -sieveSeq N c M ^ (2 : ℕ) - sieveSeq N c 1 ^ (2 : ℕ) ∧
      sieveRenormalizedPrefixDefect N M c ≤ 0 := by
  have heq :=
    two_mul_sieveRenormalizedPrefixDefect_eq_neg_init_dirichlet_add_coprime_pair N hM c
  have hdir : 0 ≤ ∑ k ∈ Finset.Icc 1 (M - 1),
      (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsqM : 0 ≤ sieveSeq N c M ^ (2 : ℕ) := sq_nonneg _
  have hsq1 : 0 ≤ sieveSeq N c 1 ^ (2 : ℕ) := sq_nonneg _
  constructor <;> linarith

/-- **Predecessor-Zero Spike Absorption Theorem
(`sieveRenormalizedPrefixDefect_nonpos_of_eq_zero`):**
Whenever `sieveSeq N c M = 0` (`M ≥ 1`), `sieveRenormalizedPrefixDefect N M c ≤ -(sieveSeq N c 1 ^ 2) / 2 ≤ 0`
**regardless of the magnitude of `sieveSeq N c (M + 1)`**! -/
theorem sieveRenormalizedPrefixDefect_nonpos_of_eq_zero
    (N : ℕ) {M : ℕ} (hM : 1 ≤ M) (c : ℕ → ℝ) (hz : sieveSeq N c M = 0) :
    2 * sieveRenormalizedPrefixDefect N M c =
        -(∑ k ∈ Finset.Icc 1 (M - 1),
            (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) -
          sieveSeq N c 1 ^ (2 : ℕ) ∧
      sieveRenormalizedPrefixDefect N M c ≤ 0 := by
  have heq :=
    two_mul_sieveRenormalizedPrefixDefect_eq_neg_init_dirichlet_add_coprime_pair N hM c
  rw [hz] at heq
  have hdir : 0 ≤ ∑ k ∈ Finset.Icc 1 (M - 1),
      (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq1 : 0 ≤ sieveSeq N c 1 ^ (2 : ℕ) := sq_nonneg _
  exact ⟨by linarith, by linarith⟩

/-! ## §2. Two-Point Consecutive Defect Average Law -/

/-- **Two-Point Consecutive Defect Average Identity
(`sieveRenormalizedPrefixDefect_pred_add_self_eq`):**
For every `N : ℕ`, weight `c : ℕ → ℝ`, and `M ≥ 2`, adding the renormalized defects at `M - 1` and
`M` cancels **both** squared boundary terms `s_{N,c}(M)²` and `s_{N,c}(M + 1)²`, leaving only the
coprime Bézout product `s_{N,c}(M) * s_{N,c}(M + 1)`:
`sieveRenormalizedPrefixDefect N (M - 1) c + sieveRenormalizedPrefixDefect N M c = -(∑ k ∈ Icc 1 (M - 1), (s_{N,c}(k+1) - s_{N,c}(k))²) + s_{N,c}(M) * s_{N,c}(M + 1) - s_{N,c}(1)²`. -/
theorem sieveRenormalizedPrefixDefect_pred_add_self_eq
    (N : ℕ) {M : ℕ} (hM : 2 ≤ M) (c : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N (M - 1) c +
        sieveRenormalizedPrefixDefect N M c =
      -(∑ k ∈ Finset.Icc 1 (M - 1),
          (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) +
        sieveSeq N c M * sieveSeq N c (M + 1) -
        sieveSeq N c 1 ^ (2 : ℕ) := by
  have hM1 : 1 ≤ M - 1 := by omega
  have hM_pos : 1 ≤ M := by omega
  have hadd : M - 1 + 1 = M := Nat.sub_add_cancel hM_pos
  have hpred := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hM1 c
  rw [hadd] at hpred
  have hself :=
    two_mul_sieveRenormalizedPrefixDefect_eq_neg_init_dirichlet_add_coprime_pair N hM_pos c
  linarith

/-- **Non-Positivity of the Two-Point Defect Average Under Coprime Product Bound
(`sieveRenormalizedPrefixDefect_pred_add_self_nonpos_of_mul_le_one_sq`):**
For every `N : ℕ`, weight `c : ℕ → ℝ`, and `M ≥ 2`, whenever
`sieveSeq N c M * sieveSeq N c (M + 1) ≤ sieveSeq N c 1 ^ 2`, the consecutive defect sum is
non-positive:
`sieveRenormalizedPrefixDefect N (M - 1) c + sieveRenormalizedPrefixDefect N M c ≤ 0`. -/
theorem sieveRenormalizedPrefixDefect_pred_add_self_nonpos_of_mul_le_one_sq
    (N : ℕ) {M : ℕ} (hM : 2 ≤ M) (c : ℕ → ℝ)
    (hmul : sieveSeq N c M * sieveSeq N c (M + 1) ≤ sieveSeq N c 1 ^ (2 : ℕ)) :
    sieveRenormalizedPrefixDefect N (M - 1) c +
      sieveRenormalizedPrefixDefect N M c ≤ 0 := by
  have heq := sieveRenormalizedPrefixDefect_pred_add_self_eq N hM c
  have hdir : 0 ≤ ∑ k ∈ Finset.Icc 1 (M - 1),
      (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-! ## §3. Discrete Path Poincaré Inequality & Trans-Horizon Arithmetic Uncertainty Principle -/

/-- **Exact Algebraic Variance-Defect Identity for Discrete Path Poincaré
(`path_poincare_step_identity`):**
For all real numbers `L, S, X, Y : ℝ`:
`L * ((L + 1) * (S + Y^2) - (X + Y)^2) = (L + 1) * (L * S - X^2) + (X - L * Y)^2`. -/
theorem path_poincare_step_identity (L S X Y : ℝ) :
    L * ((L + 1) * (S + Y ^ (2 : ℕ)) - (X + Y) ^ (2 : ℕ)) =
      (L + 1) * (L * S - X ^ (2 : ℕ)) + (X - L * Y) ^ (2 : ℕ) := by
  ring

/-- **Discrete Path Poincaré Inequality (`sq_sub_le_length_mul_sum_range_addDiff_sq`):**
For every sequence `f : ℕ → ℝ`, starting point `a : ℕ`, and path length `L : ℕ`, the squared net
displacement across `[a, a + L]` is bounded by `L` times the cumulative Dirichlet step energy:
`(f (a + L) - f a) ^ 2 ≤ L * ∑ j ∈ range L, (f (a + j + 1) - f (a + j)) ^ 2`. -/
theorem sq_sub_le_length_mul_sum_range_addDiff_sq (f : ℕ → ℝ) (a L : ℕ) :
    (f (a + L) - f a) ^ (2 : ℕ) ≤
      (L : ℝ) * ∑ j ∈ Finset.range L, (f (a + j + 1) - f (a + j)) ^ (2 : ℕ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rcases L with _ | L
    · simp
    · rw [Finset.sum_range_succ, Nat.cast_succ]
      set S := ∑ j ∈ Finset.range (L + 1), (f (a + j + 1) - f (a + j)) ^ (2 : ℕ)
      set X := f (a + (L + 1)) - f a
      set Y := f (a + (L + 1) + 1) - f (a + (L + 1))
      have hXY : f (a + (L + 1 + 1)) - f a = X + Y := by
        rw [show a + (L + 1 + 1) = a + (L + 1) + 1 by omega]
        unfold X Y
        ring
      rw [hXY]
      have hL_pos : (0 : ℝ) < ((L + 1 : ℕ) : ℝ) := by positivity
      have hid := path_poincare_step_identity ((L + 1 : ℕ) : ℝ) S X Y
      have hdiff_nonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) * S - X ^ (2 : ℕ) := by linarith [ih]
      have hsq : 0 ≤ (X - ((L + 1 : ℕ) : ℝ) * Y) ^ (2 : ℕ) := sq_nonneg _
      have hrhs : 0 ≤ (((L + 1 : ℕ) : ℝ) + 1) * (((L + 1 : ℕ) : ℝ) * S - X ^ (2 : ℕ)) +
          (X - ((L + 1 : ℕ) : ℝ) * Y) ^ (2 : ℕ) := by positivity
      have hprod : 0 ≤ ((L + 1 : ℕ) : ℝ) *
          ((((L + 1 : ℕ) : ℝ) + 1) * (S + Y ^ (2 : ℕ)) - (X + Y) ^ (2 : ℕ)) := by
        linarith [hid, hrhs]
      have hfac : 0 ≤ (((L + 1 : ℕ) : ℝ) + 1) * (S + Y ^ (2 : ℕ)) - (X + Y) ^ (2 : ℕ) :=
        nonneg_of_mul_nonneg_right hprod hL_pos
      linarith

/-- **Trans-Horizon Arithmetic Uncertainty Inequality from a Zero-Cone Anchor
(`sieve_uncertainty_lower_bound_of_eq_zero`):**
Whenever `sieveSeq N c a = 0` (for example at any trans-horizon Möbius zero `a = q * r`), any spike
`sieveSeq N c (a + L)` at distance `L : ℕ` forces cumulative Dirichlet oscillation energy at least
`sieveSeq N c (a + L) ^ 2`:
`sieveSeq N c (a + L) ^ 2 ≤ L * ∑ j ∈ range L, (s_{N,c}(a + j + 1) - s_{N,c}(a + j)) ^ 2`. -/
theorem sieve_uncertainty_lower_bound_of_eq_zero (N a L : ℕ) (c : ℕ → ℝ)
    (hz : sieveSeq N c a = 0) :
    sieveSeq N c (a + L) ^ (2 : ℕ) ≤
      (L : ℝ) * ∑ j ∈ Finset.range L,
        (sieveSeq N c (a + j + 1) - sieveSeq N c (a + j)) ^ (2 : ℕ) := by
  have h := sq_sub_le_length_mul_sum_range_addDiff_sq (sieveSeq N c) a L
  rw [hz, sub_zero] at h
  exact h

/-- **Trans-Horizon Arithmetic Uncertainty Inequality from a Rough Anchor
(`sieve_uncertainty_lower_bound_of_rough_anchor`):**
Whenever `a` is `N`-rough (`∀ d, d ∣ a → d ≤ N → d = 1`), any trans-horizon excursion at `a + L`
forces cumulative Dirichlet oscillation energy at least `(s_{N,c}(a + L) - s_{N,c}(1)) ^ 2`:
`(s_{N,c}(a + L) - s_{N,c}(1)) ^ 2 ≤ L * ∑ j ∈ range L, (s_{N,c}(a + j + 1) - s_{N,c}(a + j)) ^ 2`. -/
theorem sieve_uncertainty_lower_bound_of_rough_anchor (N a L : ℕ) (c : ℕ → ℝ)
    (ha : ∀ d : ℕ, d ∣ a → d ≤ N → d = 1) :
    (sieveSeq N c (a + L) - sieveSeq N c 1) ^ (2 : ℕ) ≤
      (L : ℝ) * ∑ j ∈ Finset.range L,
        (sieveSeq N c (a + j + 1) - sieveSeq N c (a + j)) ^ (2 : ℕ) := by
  have h := sq_sub_le_length_mul_sum_range_addDiff_sq (sieveSeq N c) a L
  have ha1 : sieveSeq N c a = sieveSeq N c 1 := by
    unfold sieveSeq
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd1, hdN⟩, hda⟩
      exact ⟨⟨hd1, hdN⟩, by rw [ha d hda hdN]⟩
    · rintro ⟨⟨hd1, hdN⟩, hd1'⟩
      exact ⟨⟨hd1, hdN⟩, hd1'.trans (one_dvd a)⟩
  rw [ha1] at h
  exact h

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
