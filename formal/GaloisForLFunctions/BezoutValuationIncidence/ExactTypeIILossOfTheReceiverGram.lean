import GaloisForLFunctions.BezoutValuationIncidence.CrossScaleFactorizationOfThePrimePronicGram
import GaloisForLFunctions.BezoutValuationIncidence.SummatoryFunctionBoundForTheDyadicPronicGram

/-!
# Exact Type-II loss of the receiver's pronic Gram

The receiver form is `Q(c) = Σ_M V_c(M)²/(M(M+1))`, `V_c(M) = R(c) - Σ_n c(n) (M mod n)/n`, over all
moduli `n ≤ N`. This module pins its Type-II loss, log-free, in both regimes.

**The receiver window `θ = 2`.** For a row on `(N₀, 2N₀]` and `M ≤ 2N₀`, every residue has jumped
at most once, so `V_c(M) = R(c) - M H(c) + S(M)` with `H(c) = Σ c(n)/n` and the summatory
function `S(M) = Σ_{n ≤ M} c(n)`. On `J + 3` consecutive blocks of `k` integers, block-constant
rows make `S` a ramp in each block. For any `J` linear side conditions there is a row satisfying
them with `R = H = 0` and

`Q(c) ≥ (k² - 1)/(24 (2N₀ + 1)) · D(c)`,  `D(c) = Σ c(n)²/n`.

With `k = ⌊N₀/(J+3)⌋` this is `≈ N₀/(48 (J+3)²)` times the diagonal, while Cauchy–Schwarz loses
the number `N₀` of moduli: Cauchy–Schwarz is sharp up to the constant `48 (J+3)²`.

**Every window below the quadratic horizon.** The unit row on `[n₀, n₀ + ℓ]` is exactly affine,
`V(M) = R + k j - M s`, between the clusters of multiples, and on `[J₀ n₀, 2 J₀ n₀)` with
`4 J₀ ℓ ≤ n₀` its window energy is at least `k/2304` times the window diagonal bound
`k Σ_W 1/(M(M+1))`, `k = ℓ + 1 ≈ n₀²/(4X)` at `X = J₀ n₀`. The log-free large sieve gives the
matching `1 + 2(2n₀)²/X`. So the exact Type-II loss of the receiver Gram is `Θ(N²/X)` at every
window `X ≤ N²` and `Θ(N/J²)` at the receiver window: no Type-II input reaches `θ > 1`. The
replacement hypothesis is square-root size of the row's summatory function on intervals of length
`N²/X`.
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Energy of a sequence that is affine on clean regions -/

/-- **Clean-region energy.** If `V` is affine with slope `-s` on each region
`[j(p₀+ℓ), (j+1)p₀)`, `J₀ ≤ j < 2J₀`, with `s ≥ k/(2p₀)`, `p₀ ≥ 4`, `4J₀ℓ ≤ p₀`, then the pronic
energy on `[J₀p₀, 2J₀p₀)` is at least `(k/2304) · k Σ_W 1/(n(n+1))`. -/
theorem window_energy_ge_of_clean_affine (V : ℕ → ℝ) (α : ℕ → ℝ) {k s : ℝ} {p₀ ℓ J₀ : ℕ}
    (hp₀ : 4 ≤ p₀) (hJ : 0 < J₀) (hJℓ : 4 * J₀ * ℓ ≤ p₀) (hk : 0 ≤ k) (hs : k / (2 * p₀) ≤ s)
    (hval : ∀ j ∈ Ico J₀ (2 * J₀), ∀ n ∈ Ico (j * (p₀ + ℓ)) (j * (p₀ + ℓ) + (p₀ - j * ℓ)),
      V n = α j - n * s) :
    k / 2304 * (k * ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀), 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀), V n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hp₀R : (4 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
  have hJR : (1 : ℝ) ≤ J₀ := by exact_mod_cast hJ
  set D : ℝ := (2 * (J₀ * p₀ : ℕ) : ℝ) * (2 * (J₀ * p₀ : ℕ) + 1) with hD
  have hDpos : 0 < D := by positivity
  have hreg : ∀ j ∈ Ico J₀ (2 * J₀), s ^ 2 * ((p₀ : ℝ) ^ 3 / 16 / 12) / D ≤
      ∑ n ∈ Ico (j * p₀) ((j + 1) * p₀), V n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro j hj
    obtain ⟨hj0, hj1⟩ := mem_Ico.mp hj
    have hjℓ : 2 * (j * ℓ) ≤ p₀ := by nlinarith
    set r := p₀ - j * ℓ with hr
    have hsub : Ico (j * (p₀ + ℓ)) (j * (p₀ + ℓ) + r) ⊆ Ico (j * p₀) ((j + 1) * p₀) := by
      intro n hn
      simp only [mem_Ico] at hn ⊢
      constructor <;> nlinarith [Nat.sub_add_cancel (show j * ℓ ≤ p₀ by omega)]
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
      div_nonneg (sq_nonneg _) (by positivity))
    have hwt : ∀ n ∈ Ico (j * (p₀ + ℓ)) (j * (p₀ + ℓ) + r),
        V n ^ 2 / D ≤ V n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      intro n hn
      have hn' := mem_Ico.mp hn
      have hnD : n + 1 ≤ 2 * (J₀ * p₀) := by
        nlinarith [Nat.sub_add_cancel (show j * ℓ ≤ p₀ by omega)]
      have hnR : (n : ℝ) + 1 ≤ 2 * (J₀ * p₀ : ℕ) := by exact_mod_cast hnD
      have h0 : 0 < n := by nlinarith
      have : (n : ℝ) * ((n : ℝ) + 1) ≤ D := by
        rw [hD]; apply mul_le_mul <;> [linarith; linarith; positivity; positivity]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) this
    refine le_trans ?_ (sum_le_sum hwt)
    rw [← sum_div]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    refine le_trans ?_ ((sum_Ico_affine_sq_ge _ r (α j) s).trans_eq
      (sum_congr rfl fun n hn => by rw [hval j hj n hn]))
    have hr2' : (p₀ : ℝ) ≤ 2 * r := by
      have : p₀ ≤ 2 * r := by omega
      exact_mod_cast this
    have hr2 : (p₀ : ℝ) ^ 3 / 16 ≤ (r : ℝ) * ((r : ℝ) ^ 2 - 1) := by
      nlinarith [sq_nonneg ((r : ℝ) - p₀ / 2), mul_pos (by linarith : (0 : ℝ) < p₀)
        (by linarith : (0 : ℝ) < p₀)]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr2 (by norm_num)) (sq_nonneg s)
  have hsplit := sum_Ico_mul_eq_sum_blocks
    (fun n => V n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) p₀ J₀ (J₁ := 2 * J₀) (by omega)
  rw [show 2 * J₀ * p₀ = (2 * J₀) * p₀ by ring, hsplit]
  refine le_trans ?_ (sum_le_sum hreg)
  rw [sum_const, Nat.card_Ico, show 2 * J₀ - J₀ = J₀ by omega, nsmul_eq_mul,
    show (2 * J₀) * p₀ = 2 * (J₀ * p₀) by ring,
    sum_Ico_pronic_mass (by positivity) (by omega)]
  have hX1 : (1 : ℝ) ≤ (J₀ * p₀ : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hDle : D ≤ 6 * ((J₀ * p₀ : ℕ) : ℝ) ^ 2 := by rw [hD]; nlinarith
  have hs2 : (k / (2 * p₀)) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  push_cast at hDle ⊢
  rw [show (1 : ℝ) / (J₀ * p₀) - 1 / (2 * (J₀ * p₀)) = 1 / (2 * (J₀ * p₀)) by field_simp; ring]
  calc k / 2304 * (k * (1 / (2 * ((J₀ : ℝ) * p₀))))
      = (J₀ : ℝ) * ((k / (2 * p₀)) ^ 2 * ((p₀ : ℝ) ^ 3 / 16 / 12)) /
          (6 * ((J₀ : ℝ) * p₀) ^ 2) := by
        field_simp
        ring
    _ ≤ (J₀ : ℝ) * (s ^ 2 * ((p₀ : ℝ) ^ 3 / 16 / 12)) / D := by
        apply div_le_div₀ (by positivity) ?_ hDpos hDle
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hs2 (by positivity)) (by positivity)
    _ = (J₀ : ℝ) * (s ^ 2 * ((p₀ : ℝ) ^ 3 / 16 / 12) / D) := by ring

/-! ## §2. Every window: the coherent integer block -/

/-- The unit row on `[n₀, n₀ + ℓ]`. -/
def integerBlockRow (n₀ ℓ : ℕ) (n : ℕ) : ℝ := if n ∈ Icc n₀ (n₀ + ℓ) then 1 else 0

theorem sieveEnergyCenteredPrefixDiscrepancy_eq_residue (N M : ℕ) (c : ℕ → ℝ) :
    sieveEnergyCenteredPrefixDiscrepancy N M c =
      vonMangoldtReadout N c - ∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n := by
  rw [sieveEnergyCenteredPrefixDiscrepancy_eq_add_vonMangoldt,
    sievePrefixDiscrepancy_eq_neg_residue, vonMangoldtReadout]
  ring

/-- **No Type-II dispersion for the receiver Gram below the quadratic horizon.** -/
theorem integerBlockRow_window_energy_ge {N n₀ ℓ J₀ : ℕ} (hn₀ : 4 ≤ n₀) (hN : n₀ + ℓ ≤ N)
    (hJ : 0 < J₀) (hJℓ : 4 * J₀ * ℓ ≤ n₀) :
    ((ℓ + 1 : ℕ) : ℝ) / 2304 * (((ℓ + 1 : ℕ) : ℝ) *
        ∑ M ∈ Ico (J₀ * n₀) (2 * J₀ * n₀), 1 / ((M : ℝ) * ((M : ℝ) + 1))) ≤
      ∑ M ∈ Ico (J₀ * n₀) (2 * J₀ * n₀),
        sieveEnergyCenteredPrefixDiscrepancy N M (integerBlockRow n₀ ℓ) ^ 2 /
          ((M : ℝ) * ((M : ℝ) + 1)) := by
  set c := integerBlockRow n₀ ℓ
  set s : ℝ := ∑ d ∈ Icc n₀ (n₀ + ℓ), 1 / (d : ℝ) with hsdef
  have hsub : Icc n₀ (n₀ + ℓ) ⊆ Icc 1 N := Icc_subset_Icc (by omega) hN
  have hres : ∀ M, ∑ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n =
      ∑ d ∈ Icc n₀ (n₀ + ℓ), ((M % d : ℕ) : ℝ) / d := by
    intro M
    rw [← sum_subset hsub fun n _ hn => by simp [c, integerBlockRow, hn]]
    exact sum_congr rfl fun d hd => by simp [c, integerBlockRow, hd]
  refine window_energy_ge_of_clean_affine _
    (fun j => vonMangoldtReadout N c + ((ℓ + 1 : ℕ) : ℝ) * j) (s := s) hn₀ hJ hJℓ
    (Nat.cast_nonneg _) ?_ ?_
  · -- the slope is at least `k/(2n₀)`
    rw [hsdef, show ((ℓ + 1 : ℕ) : ℝ) / (2 * n₀) = ∑ _d ∈ Icc n₀ (n₀ + ℓ), 1 / (2 * (n₀ : ℝ)) by
      rw [sum_const, Nat.card_Icc, show n₀ + ℓ + 1 - n₀ = ℓ + 1 by omega, nsmul_eq_mul]; ring]
    have hℓn : ℓ ≤ n₀ := by nlinarith
    refine sum_le_sum fun d hd => ?_
    have hd' := mem_Icc.mp hd
    exact one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < d))
      (by exact_mod_cast (by omega : d ≤ 2 * n₀))
  · intro j hj M hM
    have hM' := mem_Ico.mp hM
    have hj' := mem_Ico.mp hj
    have hjℓ : j * ℓ ≤ n₀ := by nlinarith
    rw [sieveEnergyCenteredPrefixDiscrepancy_eq_residue, hres]
    have hterm : ∀ d ∈ Icc n₀ (n₀ + ℓ), ((M % d : ℕ) : ℝ) / d = M * (1 / (d : ℝ)) - j := by
      intro d hd
      have hd' := mem_Icc.mp hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hdiv : M / d = j := Nat.div_eq_of_lt_le (by nlinarith)
        (by nlinarith [Nat.sub_add_cancel hjℓ])
      have hmod := Nat.mod_add_div M d
      rw [hdiv] at hmod
      have hcast : ((M % d : ℕ) : ℝ) = M - d * j := by
        have := congrArg (Nat.cast (R := ℝ)) hmod
        push_cast at this
        linarith
      rw [hcast]
      field_simp
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul,
      show n₀ + ℓ + 1 - n₀ = ℓ + 1 by omega]
    ring

/-! ## §3. The receiver window: a codimension no-go with Cauchy–Schwarz sharp -/

/-- For a row on `(N₀, 2N₀]` and `M ≤ 2N₀`: `V(M) = R - M H + S(M)`. -/
theorem sieveEnergyCenteredPrefixDiscrepancy_first_window (N N₀ M : ℕ) (c : ℕ → ℝ)
    (hsupp : ∀ n, c n ≠ 0 → N₀ < n ∧ n ≤ 2 * N₀) (h2N : 2 * N₀ ≤ N) (hM : M ≤ 2 * N₀) :
    sieveEnergyCenteredPrefixDiscrepancy N M c =
      vonMangoldtReadout N c - M * finiteHarmonicSum N c + ∑ n ∈ Icc 1 M, c n := by
  rw [sieveEnergyCenteredPrefixDiscrepancy_eq_residue, finiteHarmonicSum, mul_sum]
  have hpt : ∀ n ∈ Icc 1 N, c n * ((M % n : ℕ) : ℝ) / n =
      M * (c n / n) - (if n ≤ M then c n else 0) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    by_cases hc : c n = 0
    · simp [hc]
    have hs := hsupp n hc
    by_cases hnM : n ≤ M
    · have hmod : M % n = M - n := by
        rw [Nat.mod_eq_sub_mod hnM, Nat.mod_eq_of_lt (by omega)]
      rw [if_pos hnM, hmod, Nat.cast_sub hnM]
      field_simp
    · rw [if_neg hnM, Nat.mod_eq_of_lt (by omega)]
      field_simp
      ring
  rw [sum_congr rfl hpt, sum_sub_distrib, ← sum_filter]
  have hfilt : (Icc 1 N).filter (fun n => n ≤ M) = Icc 1 M := by
    ext n; simp only [mem_filter, mem_Icc]; omega
  rw [hfilt]
  ring

/-- The block row: `blockJump` placed on the integers `N₀ + 1, …, N₀ + B k`. -/
def blockRow (N₀ B k : ℕ) (c : Fin B → ℝ) (n : ℕ) : ℝ :=
  if n ∈ Ico (N₀ + 1) (N₀ + 1 + B * k) then blockJump B k c (n - (N₀ + 1)) else 0

/-- `blockRow` as a linear map of the block amplitudes. -/
def blockRowLinear (N₀ B k : ℕ) : (Fin B → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun c := blockRow N₀ B k c
  map_add' c d := by
    funext n
    simp only [blockRow, blockJump, Pi.add_apply]
    split_ifs <;> ring
  map_smul' r c := by
    funext n
    simp only [blockRow, blockJump, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The harmonic coefficient `H(c) = Σ_{n ≤ N} c(n)/n` as a linear functional. -/
def finiteHarmonicSumLinear (N : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun c := finiteHarmonicSum N c
  map_add' c d := by simp [finiteHarmonicSum, add_div, sum_add_distrib]
  map_smul' r c := by simp [finiteHarmonicSum, mul_sum, mul_div_assoc]

/-- The von Mangoldt readout `R(c) = Σ_{n ≤ N} c(n) log n/n` as a linear functional. -/
def vonMangoldtReadoutLinear (N : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun c := vonMangoldtReadout N c
  map_add' c d := by
    simp only [vonMangoldtReadout_eq_log_harmonic, Pi.add_apply, add_mul, add_div, sum_add_distrib]
  map_smul' r c := by
    simp only [vonMangoldtReadout_eq_log_harmonic, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_sum]
    exact sum_congr rfl fun _ _ => by ring

theorem sum_Icc_eq_sum_range_of_support {N N₀ L : ℕ} (hL : N₀ + L ≤ N) (f : ℕ → ℝ)
    (hf : ∀ n ∈ Icc 1 N, n ∉ Ico (N₀ + 1) (N₀ + 1 + L) → f n = 0) :
    ∑ n ∈ Icc 1 N, f n = ∑ t ∈ range L, f (N₀ + 1 + t) := by
  rw [← sum_subset (show Ico (N₀ + 1) (N₀ + 1 + L) ⊆ Icc 1 N by
      intro n hn; simp only [mem_Ico, mem_Icc] at hn ⊢; omega) fun n hn hn' => hf n hn hn',
    sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-- Block-constant sequences: `Σ_{t < B k} f(⌊t/k⌋) = k Σ_{i < B} f(i)`. -/
theorem sum_range_mul_div_eq (B k : ℕ) (hk : 0 < k) (f : ℕ → ℝ) :
    ∑ t ∈ range (B * k), f (t / k) = k * ∑ i ∈ range B, f i := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [sum_congr rfl fun v hv => by
      rw [show B * k + v = v + B * k by ring, Nat.add_mul_div_right _ _ hk,
        Nat.div_eq_of_lt (mem_range.mp hv), zero_add], sum_const, card_range, nsmul_eq_mul]

/-- **Codimension no-go at the receiver window, log-free.** For a block of `(J + 3) k ≤ N₀`
moduli in `(N₀, 2N₀]` and any `J` linear side conditions on rows, some nonzero row satisfies
them with `R = H = 0` and `Q(c) ≥ (k² - 1)/(24 (2N₀ + 1)) · Σ c(n)²/n`. -/
theorem exists_constrained_row_brownian_energy {N N₀ J k : ℕ} (hN₀ : 0 < N₀) (hk : 0 < k)
    (hcard : (J + 3) * k ≤ N₀) (h2N : 2 * N₀ ≤ N) (φ : Fin J → (ℕ → ℝ) →ₗ[ℝ] ℝ) :
    ∃ c : ℕ → ℝ, (∀ n, c n ≠ 0 → N₀ < n ∧ n ≤ 2 * N₀) ∧ (∀ j, φ j c = 0) ∧
      finiteHarmonicSum N c = 0 ∧ vonMangoldtReadout N c = 0 ∧
      0 < ∑ n ∈ Icc 1 N, c n ^ 2 / n ∧
      ((k : ℝ) ^ 2 - 1) / (24 * (2 * N₀ + 1)) * ∑ n ∈ Icc 1 N, c n ^ 2 / n ≤
        sieveEnergyCenteredPronicGramForm N c := by
  set B := J + 3 with hB
  set Ψ : (Fin B → ℝ) →ₗ[ℝ] (Fin (J + 2) → ℝ) := LinearMap.pi
    (Fin.cons ((finiteHarmonicSumLinear N).comp (blockRowLinear N₀ B k))
      (Fin.cons ((vonMangoldtReadoutLinear N).comp (blockRowLinear N₀ B k))
        fun j => (φ j).comp (blockRowLinear N₀ B k))) with hΨ
  have hker : LinearMap.ker Ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp [hB])
  obtain ⟨c, hcker, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hΨc : ∀ i, Ψ c i = 0 := fun i => by rw [LinearMap.mem_ker.mp hcker]; rfl
  set row := blockRow N₀ B k c with hrow
  have hH : finiteHarmonicSum N row = 0 := by
    have h := hΨc 0
    simp only [hΨ, LinearMap.pi_apply, Fin.cons_zero, LinearMap.comp_apply] at h
    exact h
  have hR : vonMangoldtReadout N row = 0 := by
    have h := hΨc 1
    simp only [hΨ, LinearMap.pi_apply] at h
    exact h
  have hφ : ∀ j, φ j row = 0 := fun j => by
    have h := hΨc j.succ.succ
    simp only [hΨ, LinearMap.pi_apply, Fin.cons_succ, LinearMap.comp_apply] at h
    exact h
  have hBk : B * k ≤ N₀ := by rw [hB]; exact hcard
  have hsupp : ∀ n, row n ≠ 0 → N₀ < n ∧ n ≤ 2 * N₀ := fun n h => by
    simp only [hrow, blockRow] at h
    split_ifs at h with hn
    · simp only [mem_Ico] at hn; omega
    · exact absurd rfl h
  set cn : ℕ → ℝ := fun i => if h : i < B then c ⟨i, h⟩ else 0 with hcn
  have hjump : ∀ s, blockJump B k c s = cn (s / k) := fun s => rfl
  have hrow_shift : ∀ t, t < B * k → row (N₀ + 1 + t) = cn (t / k) := fun t ht => by
    simp only [hrow, blockRow, mem_Ico, show N₀ + 1 ≤ N₀ + 1 + t from Nat.le_add_right _ _,
      show N₀ + 1 + t < N₀ + 1 + B * k by omega, and_self, if_true,
      show N₀ + 1 + t - (N₀ + 1) = t by omega, hjump]
  have hrow_out : ∀ n, n ∉ Ico (N₀ + 1) (N₀ + 1 + B * k) → row n = 0 := fun n hn => by
    simp only [hrow, blockRow, if_neg hn]
  have hL : N₀ + B * k ≤ N := by omega
  -- energy: the cumulative sums at the block integers
  have hS : ∀ t, t < B * k → ∑ n ∈ Icc 1 (N₀ + 1 + t), row n = ∑ s ∈ range (t + 1), cn (s / k) := by
    intro t ht
    rw [sum_Icc_eq_sum_range_of_support (N := N₀ + 1 + t) (N₀ := N₀) (L := t + 1) (by omega) row
      (fun n hn hn' => by
        by_cases h : n ∈ Ico (N₀ + 1) (N₀ + 1 + B * k)
        · simp only [mem_Ico, mem_Icc] at hn hn' h
          omega
        · exact hrow_out n h)]
    exact sum_congr rfl fun s hs => hrow_shift s (by have := mem_range.mp hs; omega)
  have hQ := hasSum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq N row
  have hwin : ∑ M ∈ Ico (N₀ + 1) (N₀ + 1 + B * k),
      sieveEnergyCenteredPrefixDiscrepancy N M row ^ (2 : ℕ) / (pronicSeq M : ℝ) ≤
        sieveEnergyCenteredPronicGramForm N row :=
    sum_le_hasSum _ (fun M _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hQ
  set D : ℝ := (2 * N₀ : ℝ) * (2 * N₀ + 1) with hD
  have hden : 0 < D := by positivity
  have henergy : (k : ℝ) * ((k : ℝ) ^ 2 - 1) / 12 * (∑ i ∈ range B, cn i ^ 2) / D ≤
      sieveEnergyCenteredPronicGramForm N row := by
    refine le_trans ?_ hwin
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    have hpt : ∀ t ∈ range (B * k), (∑ s ∈ range (t + 1), cn (s / k)) ^ 2 / D ≤
        sieveEnergyCenteredPrefixDiscrepancy N (N₀ + 1 + t) row ^ (2 : ℕ) /
          (pronicSeq (N₀ + 1 + t) : ℝ) := by
      intro t ht
      have ht' := mem_range.mp ht
      rw [sieveEnergyCenteredPrefixDiscrepancy_first_window N N₀ _ row hsupp h2N (by omega),
        hH, hR, hS t ht', mul_zero, sub_zero, zero_add, cast_pronicSeq_eq]
      refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
      have hM : ((N₀ + 1 + t : ℕ) : ℝ) ≤ 2 * N₀ := by exact_mod_cast (by omega : N₀ + 1 + t ≤ 2 * N₀)
      rw [hD]
      apply mul_le_mul hM (by linarith) (by positivity) (by positivity)
    refine le_trans ?_ (sum_le_sum hpt)
    rw [← sum_div]
    exact div_le_div_of_nonneg_right (sum_range_blockPartialSum_sq_ge B k cn) hden.le
  -- the diagonal `D(c) ≤ (k/N₀) Σ c_i²`
  have hdiag : ∑ n ∈ Icc 1 N, row n ^ 2 / n ≤ (k : ℝ) / N₀ * ∑ i ∈ range B, cn i ^ 2 := by
    rw [sum_Icc_eq_sum_range_of_support hL (fun n => row n ^ 2 / n)
      (fun n _ hn => by simp [hrow_out n hn])]
    calc ∑ t ∈ range (B * k), row (N₀ + 1 + t) ^ 2 / ((N₀ + 1 + t : ℕ) : ℝ)
        ≤ ∑ t ∈ range (B * k), cn (t / k) ^ 2 / N₀ := sum_le_sum fun t ht => by
          rw [hrow_shift t (mem_range.mp ht)]
          exact div_le_div_of_nonneg_left (sq_nonneg _) (by exact_mod_cast hN₀)
            (by exact_mod_cast (by omega : N₀ ≤ N₀ + 1 + t))
      _ = (k : ℝ) / N₀ * ∑ i ∈ range B, cn i ^ 2 := by
          rw [← sum_div, sum_range_mul_div_eq B k hk (fun i => cn i ^ 2)]
          ring
  -- nondegeneracy
  have hpos : 0 < ∑ n ∈ Icc 1 N, row n ^ 2 / n := by
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      exact hc0 (funext fun i => not_not.mp (not_exists.mp h i))
    have hik : (i : ℕ) * k < B * k := Nat.mul_lt_mul_of_pos_right i.isLt hk
    have hrow_i : row (N₀ + 1 + (i : ℕ) * k) ≠ 0 := by
      rw [hrow_shift _ hik, hcn]
      simp only [Nat.mul_div_cancel _ hk, dif_pos i.isLt]
      exact hi
    rw [sum_Icc_eq_sum_range_of_support hL (fun n => row n ^ 2 / n)
      (fun n _ hn => by simp [hrow_out n hn])]
    refine sum_pos' (fun t _ => by positivity) ⟨(i : ℕ) * k, mem_range.mpr hik, ?_⟩
    exact div_pos (pow_pos (abs_pos.mpr hrow_i) 2 |>.trans_eq (sq_abs _)) (by positivity)
  refine ⟨row, hsupp, hφ, hH, hR, hpos, ?_⟩
  have hP0 : (0 : ℝ) < N₀ := by exact_mod_cast hN₀
  have hk1 : (0 : ℝ) ≤ (k : ℝ) ^ 2 - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  calc ((k : ℝ) ^ 2 - 1) / (24 * (2 * N₀ + 1)) * ∑ n ∈ Icc 1 N, row n ^ 2 / n
      ≤ ((k : ℝ) ^ 2 - 1) / (24 * (2 * N₀ + 1)) * ((k : ℝ) / N₀ * ∑ i ∈ range B, cn i ^ 2) :=
        mul_le_mul_of_nonneg_left hdiag (by positivity)
    _ = (k : ℝ) * ((k : ℝ) ^ 2 - 1) / 12 * (∑ i ∈ range B, cn i ^ 2) / D := by
        rw [hD]; field_simp; ring
    _ ≤ sieveEnergyCenteredPronicGramForm N row := henergy

end

end GaloisForLFunctions.BezoutValuationIncidence

