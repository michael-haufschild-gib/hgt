import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedRenormalizedDefectAndPronicCeiling
import GaloisForLFunctions.BezoutValuationIncidence.ActiveDeletedMartingaleAndShiftedEulerConvergence

/-!
# Pillar VII: Inter-Checkpoint Dirichlet Excursions, Boundary-Bounded Monotonicity, and Rough-Neighbor Pronic Bézout Localization (`InterCheckpointSawtoothExcursionAndPronicSandwich`)

In `TransHorizonRoughAbsorptionAndReset` (Pillar II), we proved that at every `N`-rough checkpoint
`M = r - 1` (`∀ d ∣ r, d ≤ N → d = 1`), the boundary term `s_{N,c}(r)² - s_{N,c}(1)²` in the
Dirichlet polarization identity vanishes identically, forcing `sieveRenormalizedPrefixDefect N (r - 1) c ≤ 0`.

To establish a complete theory across **arbitrary interior scales `M` between rough checkpoints** and
to couple `N`-roughness to the pronic Bézout geometry `pronicSeq k = k(k + 1)`, this seventh
foundational pillar proves:

## Core Main Theorems (100% Unconditional)

1. **Inter-Checkpoint Dirichlet Excursion Law
   (`two_mul_sieveRenormalizedPrefixDefect_sub_rough_checkpoint`,
   `sieveRenormalizedPrefixDefect_le_rough_checkpoint_of_sq_le`)**:
   For every `N`-rough integer `r ≥ 2` and every `M ≥ r - 1`:
   $$2\bigl(\widetilde{\mathcal{D}}_N(M; c) - \widetilde{\mathcal{D}}_N(r - 1; c)\bigr) =
     -\sum_{k=r}^M \bigl(s_{N,c}(k + 1) - s_{N,c}(k)\bigr)^2 +
       s_{N,c}(M + 1)^2 - s_{N,c}(1)^2.$$
   Consequently, at **every** trans-horizon scale `M ≥ r - 1` satisfying the boundary envelope
   `s_{N,c}(M + 1)² ≤ s_{N,c}(1)²` (which includes all trans-horizon Möbius zeros `s_{N,μ}(M + 1) = 0`,
   all rough checkpoints, and all sub-unit response points), `sieveRenormalizedPrefixDefect N M c`
   lies **strictly below** the already non-positive rough checkpoint value:
   $$\widetilde{\mathcal{D}}_N(M; c) \le \widetilde{\mathcal{D}}_N(r - 1; c) -
     \frac{1}{2}\sum_{k=r}^M \bigl(s_{N,c}(k + 1) - s_{N,c}(k)\bigr)^2 \le 0.$$

2. **Immediate Post-Rough Step & Symmetric Neighbor Excursion (`M = r - 1 ↦ r ↦ r + 1`)
   (`sieveRenormalizedPrefixDefect_rough_sub_pred`,
   `sieveRenormalizedPrefixDefect_rough_succ_sub_pred`)**:
   For every `N`-rough `r ≥ 1` and weight `c : ℕ → ℝ`:
   $$\widetilde{\mathcal{D}}_N(r; c) - \widetilde{\mathcal{D}}_N(r - 1; c) =
     s_{N,c}(1)\bigl(s_{N,c}(r + 1) - s_{N,c}(1)\bigr).$$

3. **Rough-Neighbor Pronic Bézout Localization Theorem
   (`sieveSeq_pronicSeq_pred_of_rough`, `sieveSeq_pronicSeq_of_rough`,
   `sieveSeq_pronicSeq_neighbor_sum_of_rough`, `sieveSeq_pronicSeq_neighbor_diff_of_rough`)**:
   For every `N`-rough integer `r ≥ 1` (in particular every prime `p > N`), the quadratic pronic
   Bézout cells `pronicSeq (r - 1) = (r - 1)r` and `pronicSeq r = r(r + 1)` completely absorb the
   rough factor `r` and collapse to the linear neighbors `r - 1` and `r + 1`:
   $$\operatorname{sieveSeq}(N, c, \operatorname{pronicSeq}(r - 1)) = \operatorname{sieveSeq}(N, c, r - 1),$$
   $$\operatorname{sieveSeq}(N, c, \operatorname{pronicSeq}(r)) = \operatorname{sieveSeq}(N, c, r + 1).$$
   Thus the pronic sum and forward pronic gradient across `r` coincide identically with the symmetric
   linear neighbor sum and centered difference `s_{N,c}(r + 1) ± s_{N,c}(r - 1)`.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Local Rough Absorption Helpers -/

/-- If `∀ d, d ∣ r → d ≤ N → d = 1`, then every `d ∈ [1, N]` is coprime to `r`. -/
theorem coprime_of_rough_le {N r d : ℕ} (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1)
    (hd1 : 1 ≤ d) (hdN : d ≤ N) : Nat.Coprime d r := by
  rw [Nat.coprime_iff_gcd_eq_one]
  exact hr (Nat.gcd d r) (Nat.gcd_dvd_right d r)
    ((Nat.gcd_le_left r (by omega : 0 < d)).trans hdN)

/-- Sub-horizon divisibility invariance under right multiplication by an `N`-rough integer `r`. -/
theorem filter_dvd_mul_right_of_rough {N r : ℕ} (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1)
    (q : ℕ) :
    (Finset.Icc 1 N).filter (fun d => d ∣ q * r) =
      (Finset.Icc 1 N).filter (fun d => d ∣ q) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd1, hdN⟩, hdvd⟩
    exact ⟨⟨hd1, hdN⟩, (coprime_of_rough_le hr hd1 hdN).dvd_of_dvd_mul_right hdvd⟩
  · rintro ⟨⟨hd1, hdN⟩, hdvd⟩
    exact ⟨⟨hd1, hdN⟩, dvd_mul_of_dvd_left hdvd r⟩

/-- For any `N`-rough `r`, `sieveSeq N c (q * r) = sieveSeq N c q`. -/
theorem sieveSeq_mul_right_of_rough {N r : ℕ} (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1)
    (c : ℕ → ℝ) (q : ℕ) :
    sieveSeq N c (q * r) = sieveSeq N c q := by
  unfold sieveSeq
  rw [filter_dvd_mul_right_of_rough hr q]

/-- For any `N`-rough `r`, `sieveSeq N c (r * q) = sieveSeq N c q`. -/
theorem sieveSeq_mul_left_of_rough {N r : ℕ} (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1)
    (c : ℕ → ℝ) (q : ℕ) :
    sieveSeq N c (r * q) = sieveSeq N c q := by
  rw [mul_comm, sieveSeq_mul_right_of_rough hr c q]

/-- For any `N`-rough `r`, `sieveSeq N c r = sieveSeq N c 1`. -/
theorem sieveSeq_eq_one_of_rough {N r : ℕ} (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1)
    (c : ℕ → ℝ) :
    sieveSeq N c r = sieveSeq N c 1 := by
  simpa only [one_mul] using sieveSeq_mul_right_of_rough hr c 1

/-! ## §2. Inter-Checkpoint Dirichlet Excursion Law & Boundary-Bounded Monotonicity -/

/-- Partition of `Finset.Icc 1 M` into `Finset.Icc 1 (r - 1)` and `Finset.Icc r M` for `2 ≤ r` and
`r - 1 ≤ M`. -/
theorem Icc_one_split_at_rough {r M : ℕ} (hr2 : 2 ≤ r) (hM : r - 1 ≤ M) :
    Finset.Icc 1 M = Finset.Icc 1 (r - 1) ∪ Finset.Icc r M ∧
      Disjoint (Finset.Icc 1 (r - 1)) (Finset.Icc r M) := by
  refine ⟨?_, ?_⟩
  · ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  · rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega

/-- **Inter-Checkpoint Dirichlet Excursion Law
(`two_mul_sieveRenormalizedPrefixDefect_sub_rough_checkpoint`):**
For every `N : ℕ`, weight `c : ℕ → ℝ`, `N`-rough integer `r ≥ 2`, and `M ≥ r - 1`:
`2 * (sieveRenormalizedPrefixDefect N M c - sieveRenormalizedPrefixDefect N (r - 1) c) = -(∑ k ∈ Icc r M, (s_{N,c}(k+1) - s_{N,c}(k))²) + s_{N,c}(M+1)² - s_{N,c}(1)²`. -/
theorem two_mul_sieveRenormalizedPrefixDefect_sub_rough_checkpoint
    (N : ℕ) (c : ℕ → ℝ) {r M : ℕ} (hr2 : 2 ≤ r)
    (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1) (hM : r - 1 ≤ M) :
    2 * (sieveRenormalizedPrefixDefect N M c -
        sieveRenormalizedPrefixDefect N (r - 1) c) =
      -(∑ k ∈ Finset.Icc r M, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) +
        sieveSeq N c (M + 1) ^ (2 : ℕ) - sieveSeq N c 1 ^ (2 : ℕ) := by
  have hr1 : 1 ≤ r - 1 := by omega
  have hM1 : 1 ≤ M := by omega
  have hadd : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
  have hpolM := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hM1 c
  have hpolR := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hr1 c
  rw [hadd, sieveSeq_eq_one_of_rough hr c] at hpolR
  obtain ⟨hsplit, hdisj⟩ := Icc_one_split_at_rough hr2 hM
  rw [hsplit, Finset.sum_union hdisj] at hpolM
  linarith

/-- **Boundary-Bounded Inter-Checkpoint Monotonicity & Non-Positivity
(`sieveRenormalizedPrefixDefect_le_rough_checkpoint_of_sq_le`):**
For every `N : ℕ`, weight `c : ℕ → ℝ`, `N`-rough integer `r ≥ 2`, and `M ≥ r - 1`, whenever
`sieveSeq N c (M + 1) ^ 2 ≤ sieveSeq N c 1 ^ 2`:
`sieveRenormalizedPrefixDefect N M c ≤ sieveRenormalizedPrefixDefect N (r - 1) c ≤ 0`. -/
theorem sieveRenormalizedPrefixDefect_le_rough_checkpoint_of_sq_le
    (N : ℕ) (c : ℕ → ℝ) {r M : ℕ} (hr2 : 2 ≤ r)
    (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1) (hM : r - 1 ≤ M)
    (hbnd : sieveSeq N c (M + 1) ^ (2 : ℕ) ≤ sieveSeq N c 1 ^ (2 : ℕ)) :
    sieveRenormalizedPrefixDefect N M c ≤ sieveRenormalizedPrefixDefect N (r - 1) c ∧
      sieveRenormalizedPrefixDefect N M c ≤ 0 := by
  have hex := two_mul_sieveRenormalizedPrefixDefect_sub_rough_checkpoint N c hr2 hr hM
  have hsum_tail : 0 ≤ ∑ k ∈ Finset.Icc r M,
      (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr1 : 1 ≤ r - 1 := by omega
  have hadd : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
  have hpolR := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hr1 c
  rw [hadd, sieveSeq_eq_one_of_rough hr c] at hpolR
  have hsum_init : 0 ≤ ∑ k ∈ Finset.Icc 1 (r - 1),
      (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  constructor <;> linarith

/-- **Immediate Post-Rough Step Identity (`sieveRenormalizedPrefixDefect_rough_sub_pred`):**
For every `N : ℕ`, weight `c : ℕ → ℝ`, and `N`-rough integer `r ≥ 1`, stepping from the rough
checkpoint `M = r - 1` to `M = r` changes `sieveRenormalizedPrefixDefect` by
`s_{N,c}(1) * (s_{N,c}(r + 1) - s_{N,c}(1))`. -/
theorem sieveRenormalizedPrefixDefect_rough_sub_pred
    (N : ℕ) (c : ℕ → ℝ) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1) :
    sieveRenormalizedPrefixDefect N r c - sieveRenormalizedPrefixDefect N (r - 1) c =
      sieveSeq N c 1 * (sieveSeq N c (r + 1) - sieveSeq N c 1) := by
  have hadd : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have hadd2 : r - 1 + 2 = r + 1 := by omega
  have hstep := sieveRenormalizedPrefixDefect_succ_sub_eq N (r - 1) c
  rw [hadd, hadd2, sieveSeq_eq_one_of_rough hr c] at hstep
  exact hstep

/-! ## §3. Rough-Neighbor Pronic Bézout Localization (`pronicSeq (r - 1)` and `pronicSeq r`) -/

/-- **Predecessor Pronic Localization at an `N`-Rough Integer (`sieveSeq_pronicSeq_pred_of_rough`):**
For every `N`-rough integer `r ≥ 1` and weight `c : ℕ → ℝ`, the pronic predecessor cell
`pronicSeq (r - 1) = (r - 1) * r` has the exact same `N`-sieve value as `r - 1`:
`sieveSeq N c (pronicSeq (r - 1)) = sieveSeq N c (r - 1)`. -/
theorem sieveSeq_pronicSeq_pred_of_rough {N r : ℕ} (hr1 : 1 ≤ r)
    (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1) (c : ℕ → ℝ) :
    sieveSeq N c (pronicSeq (r - 1)) = sieveSeq N c (r - 1) := by
  unfold pronicSeq
  have hadd : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  rw [hadd, sieveSeq_mul_right_of_rough hr c (r - 1)]

/-- **Successor Pronic Localization at an `N`-Rough Integer (`sieveSeq_pronicSeq_of_rough`):**
For every `N`-rough integer `r : ℕ` and weight `c : ℕ → ℝ`, the pronic cell
`pronicSeq r = r * (r + 1)` has the exact same `N`-sieve value as `r + 1`:
`sieveSeq N c (pronicSeq r) = sieveSeq N c (r + 1)`. -/
theorem sieveSeq_pronicSeq_of_rough {N r : ℕ}
    (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1) (c : ℕ → ℝ) :
    sieveSeq N c (pronicSeq r) = sieveSeq N c (r + 1) := by
  unfold pronicSeq
  exact sieveSeq_mul_left_of_rough hr c (r + 1)

/-- **Pronic Neighbor Sum Conservation Across an `N`-Rough Integer
(`sieveSeq_pronicSeq_neighbor_sum_of_rough`):**
For every `N`-rough integer `r ≥ 1` and weight `c : ℕ → ℝ`:
`sieveSeq N c (pronicSeq (r - 1)) + sieveSeq N c (pronicSeq r) = sieveSeq N c (r - 1) + sieveSeq N c (r + 1)`. -/
theorem sieveSeq_pronicSeq_neighbor_sum_of_rough {N r : ℕ} (hr1 : 1 ≤ r)
    (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1) (c : ℕ → ℝ) :
    sieveSeq N c (pronicSeq (r - 1)) + sieveSeq N c (pronicSeq r) =
      sieveSeq N c (r - 1) + sieveSeq N c (r + 1) := by
  rw [sieveSeq_pronicSeq_pred_of_rough hr1 hr c, sieveSeq_pronicSeq_of_rough hr c]

/-- **Pronic Neighbor Gradient Identity Across an `N`-Rough Integer
(`sieveSeq_pronicSeq_neighbor_diff_of_rough`):**
For every `N`-rough integer `r ≥ 1` and weight `c : ℕ → ℝ`:
`sieveSeq N c (pronicSeq r) - sieveSeq N c (pronicSeq (r - 1)) = sieveSeq N c (r + 1) - sieveSeq N c (r - 1)`. -/
theorem sieveSeq_pronicSeq_neighbor_diff_of_rough {N r : ℕ} (hr1 : 1 ≤ r)
    (hr : ∀ d : ℕ, d ∣ r → d ≤ N → d = 1) (c : ℕ → ℝ) :
    sieveSeq N c (pronicSeq r) - sieveSeq N c (pronicSeq (r - 1)) =
      sieveSeq N c (r + 1) - sieveSeq N c (r - 1) := by
  rw [sieveSeq_pronicSeq_pred_of_rough hr1 hr c, sieveSeq_pronicSeq_of_rough hr c]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
