import GaloisForLFunctions.BiScaleUncertainty.BarbanVehovLogarithmicDiagonalAndKerPCauchyPinch
import GaloisForLFunctions.BiScaleUncertainty.WitnessCellTransferAndTopOctaveTailInequality

/-!
# First- and Second-Moment Fractional-Part Reciprocity & `ker P`-Centered Sieve Projection (`KerPCenteredSieveAndFirstSecondMomentReciprocity`)

This module completes the three-module synthesis in `BiScaleUncertainty` for exact signed
sieve cancellation and `ker P` harmonic-pole elimination:

1. **First-Moment vs. Second-Moment Additive-Multiplicative Reciprocity Duality
   (`sievedFractSum_succ_sub_eq`, `finiteFloorSum_nat_eq_harmonic_sub_sievedFractSum`):**
   Defining the linear fractional-part defect `sievedFractSum N c m = ∑_{d=1}^N c(d) {m / d}`,
   we prove the exact first-moment counterpart to `signedLcmFractDefect_succ_sub_eq`:
   - **First-Moment Reciprocity:**
     `sievedFractSum N c (m + 1) - sievedFractSum N c m = selbergMultiplesCoord N c 1 - sievedDivisorSum N c (m + 1)`,
     `∑_{k=1}^m s_{N,c}(k) = m · selbergMultiplesCoord N c 1 - sievedFractSum N c m`.
   - **Second-Moment Reciprocity (`signedLcmFractDefect_succ_sub_eq`):**
     `signedLcmFractDefect N (m + 1) c - signedLcmFractDefect N m c = selbergTotientDiagonalForm N c - sievedDivisorSum N c (m + 1)²`,
     `∑_{k=1}^m s_{N,c}(k)² = m · selbergTotientDiagonalForm N c - signedLcmFractDefect N m c`.
   When `c ∈ ker P` (`finiteHarmonicSum N c = selbergMultiplesCoord N c 1 = 0`), the linear drift
   `m · selbergMultiplesCoord N c 1` vanishes identically and the cumulative step profile
   `finiteFloorSum N c m = -sievedFractSum N c m` is uniformly bounded by `∑_{d=1}^N |c(d)|` for
   all `m : ℕ` (`abs_finiteFloorSum_nat_le_of_harmonic_eq_zero`).

2. **Explicit `ker P`-Centered Sieve Projection (`kerPEndpointWeight`):**
   For any cutoff `N ≥ 2` and sieve weight `c : ℕ → ℝ`, subtracting `N · finiteHarmonicSum N c` at
   the top scale `d = N` produces `kerPEndpointWeight N c`, which:
   - has **identically vanishing** harmonic pole sum `finiteHarmonicSum N (kerPEndpointWeight N c) = 0`
     (`selbergMultiplesCoord N (kerPEndpointWeight N c) 1 = 0`),
   - preserves `c(d)` for all `1 ≤ d < N` (in particular at `d = 1`),
   - preserves the sieved divisor sum `sievedDivisorSum N (kerPEndpointWeight N c) k = sievedDivisorSum N c k`
     for every `1 ≤ k < N` (hence preserving `log X` at `k = 1` and `Λ(k)` on `2 ≤ k ≤ X` when
     applied to `barbanVehovWeight X` with `X < N`), and
   - satisfies the sharpened `ker P` Selberg Cauchy–Schwarz lower bound over `2 ≤ e ≤ N`.

3. **Master Synthesis of the Exact Signed Sieve & `ker P` Calculus
   (`exact_signed_sieve_and_barbanVehov_master_synthesis`):**
   Packages the lossless signed Selberg mean-square decomposition, additive-multiplicative successor
   reciprocity, complete-fibre Möbius collapse, Jordan `J₂` Franel diagonalization, Barban–Vehov
   logarithmic diagonal pinch, and `ker P` endpoint projection into a single unconditional theorem.
-/

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

open Finset ArithmeticFunction RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

/-! ## §1. First-Moment Fractional-Part Defect & Drift Elimination on `ker P` -/

/-- The linear fractional-part defect `sievedFractSum N c m = ∑_{d=1}^N c(d) {m / d}`. -/
def sievedFractSum (N : ℕ) (c : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, c d * fractDivSeq d m

/-- At `m = 0`, `sievedFractSum` vanishes identically. -/
@[simp]
theorem sievedFractSum_zero (N : ℕ) (c : ℕ → ℝ) :
    sievedFractSum N c 0 = 0 := by
  unfold sievedFractSum fractDivSeq
  simp

/-- **First-Moment Additive-Multiplicative Successor Reciprocity (`sievedFractSum_succ_sub_eq`):**
Stepping `m ↦ m + 1` changes `sievedFractSum N c m` by the difference between the `e = 1` Selberg
coordinate `selbergMultiplesCoord N c 1 = finiteHarmonicSum N c` and the sieved divisor sum
`sievedDivisorSum N c (m + 1)`. -/
theorem sievedFractSum_succ_sub_eq (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    sievedFractSum N c (m + 1) - sievedFractSum N c m =
      selbergMultiplesCoord N c 1 - sievedDivisorSum N c (m + 1) := by
  rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum,
    sievedDivisorSum_succ_eq_sum_filter_Icc, Finset.sum_filter]
  unfold sievedFractSum finiteHarmonicSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hd_eq : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  have hstep := addDiff_fractDivSeq_succ (d - 1) m
  rw [hd_eq, addDiff_floorDivSeq_eq_ite_dvd] at hstep
  unfold addDiff at hstep
  calc c d * fractDivSeq d (m + 1) - c d * fractDivSeq d m
      = c d * (fractDivSeq d (m + 1) - fractDivSeq d m) := by ring
    _ = c d * (1 / (d : ℝ) - if d ∣ (m + 1) then (1 : ℝ) else 0) := by rw [hstep]
    _ = c d / (d : ℝ) - (if d ∣ (m + 1) then c d else 0) := by
        split_ifs <;> ring

/-- **Exact Linear Decomposition of `finiteFloorSum` at Integer Arguments:**
For every `N m : ℕ` and `c : ℕ → ℝ`,
`finiteFloorSum N c m = ∑_{k=1}^m s_{N,c}(k) = m · selbergMultiplesCoord N c 1 - sievedFractSum N c m`. -/
theorem finiteFloorSum_nat_eq_selbergOne_sub_sievedFractSum (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    finiteFloorSum N c (m : ℝ) =
      (m : ℝ) * selbergMultiplesCoord N c 1 - sievedFractSum N c m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfl := finiteFloorSum_nat_succ_sub N c m
    have hfr := sievedFractSum_succ_sub_eq N c m
    have hcast : (((m + 1 : ℕ) : ℝ) * selbergMultiplesCoord N c 1) =
        (m : ℝ) * selbergMultiplesCoord N c 1 + selbergMultiplesCoord N c 1 := by
      push_cast
      ring
    rw [hcast]
    linarith

/-- **Exact Drift Elimination on `ker P` (`finiteHarmonicSum N c = 0`):**
When `finiteHarmonicSum N c = 0`, the linear drift `m · selbergMultiplesCoord N c 1` vanishes for
all `m : ℕ`, so `finiteFloorSum N c m = -sievedFractSum N c m`. -/
theorem finiteFloorSum_nat_eq_neg_sievedFractSum_of_harmonic_eq_zero
    (N : ℕ) (c : ℕ → ℝ) (hker : finiteHarmonicSum N c = 0) (m : ℕ) :
    finiteFloorSum N c (m : ℝ) = -sievedFractSum N c m := by
  rw [finiteFloorSum_nat_eq_selbergOne_sub_sievedFractSum,
    selbergMultiplesCoord_one_eq_finiteHarmonicSum, hker, mul_zero, zero_sub]

/-- For every `d m : ℕ`, `|fractDivSeq d m| ≤ 1`. -/
theorem abs_fractDivSeq_le_one (d m : ℕ) : |fractDivSeq d m| ≤ 1 := by
  unfold fractDivSeq
  rw [abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

/-- **Uniform `ℓ¹` Bound on `sievedFractSum` for All `m : ℕ`:**
For every `N m : ℕ` and `c : ℕ → ℝ`, `|sievedFractSum N c m| ≤ ∑_{d=1}^N |c(d)|`. -/
theorem abs_sievedFractSum_le_sum_abs (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    |sievedFractSum N c m| ≤ ∑ d ∈ Finset.Icc 1 N, |c d| := by
  unfold sievedFractSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [abs_mul]
  calc |c d| * |fractDivSeq d m|
      ≤ |c d| * 1 := mul_le_mul_of_nonneg_left (abs_fractDivSeq_le_one d m) (abs_nonneg _)
    _ = |c d| := mul_one _

/-- **Uniform Boundedness of the Cumulative Sieved Divisor Sum on `ker P`:**
Whenever `finiteHarmonicSum N c = 0`, the cumulative sum `∑_{k=1}^m s_{N,c}(k)` is uniformly
bounded in absolute value by `∑_{d=1}^N |c(d)|` for **all** `m : ℕ` (with zero linear growth in `m`). -/
theorem abs_sum_sievedDivisorSum_le_of_harmonic_eq_zero
    (N : ℕ) (c : ℕ → ℝ) (hker : finiteHarmonicSum N c = 0) (m : ℕ) :
    |∑ k ∈ Finset.Icc 1 m, sievedDivisorSum N c k| ≤ ∑ d ∈ Finset.Icc 1 N, |c d| := by
  rw [← finiteFloorSum_nat_eq_sum_sievedDivisorSum,
    finiteFloorSum_nat_eq_neg_sievedFractSum_of_harmonic_eq_zero N c hker m, abs_neg]
  exact abs_sievedFractSum_le_sum_abs N c m

/-! ## §2. Explicit `ker P`-Centered Sieve Projection (`kerPEndpointWeight`) -/

/-- The **endpoint-centered `ker P` sieve weight** on `[1, N]`, obtained by subtracting
`N · finiteHarmonicSum N c` at the endpoint scale `d = N`. -/
def kerPEndpointWeight (N : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  c d - if d = N then (N : ℝ) * finiteHarmonicSum N c else 0

/-- **Exact `ker P` Centering of `kerPEndpointWeight`:**
For every `N ≥ 1` and `c : ℕ → ℝ`, `finiteHarmonicSum N (kerPEndpointWeight N c) = 0`. -/
theorem finiteHarmonicSum_kerPEndpointWeight_eq_zero {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    finiteHarmonicSum N (kerPEndpointWeight N c) = 0 := by
  have hsplit : finiteHarmonicSum N (kerPEndpointWeight N c) =
      finiteHarmonicSum N c -
        ∑ d ∈ Finset.Icc 1 N,
          (if d = N then (N : ℝ) * finiteHarmonicSum N c else 0) / (d : ℝ) := by
    unfold finiteHarmonicSum kerPEndpointWeight
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => sub_div _ _ _
  rw [hsplit]
  have hNmem : N ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hN, le_rfl⟩
  have hsingle : (∑ d ∈ Finset.Icc 1 N,
      (if d = N then (N : ℝ) * finiteHarmonicSum N c else 0) / (d : ℝ)) =
      finiteHarmonicSum N c := by
    rw [Finset.sum_eq_single_of_mem N hNmem (fun d _ hdN => by simp [hdN])]
    simp only [↓reduceIte]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    exact mul_div_cancel_left₀ _ hN0
  rw [hsingle, sub_self]

/-- The `e = 1` Selberg multiples-coordinate of `kerPEndpointWeight N c` vanishes identically. -/
theorem selbergMultiplesCoord_one_kerPEndpointWeight_eq_zero {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    selbergMultiplesCoord N (kerPEndpointWeight N c) 1 = 0 := by
  rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum,
    finiteHarmonicSum_kerPEndpointWeight_eq_zero hN c]

/-- For every `d < N`, `kerPEndpointWeight N c d = c d`. -/
theorem kerPEndpointWeight_eq_of_lt {N d : ℕ} (hdN : d < N) (c : ℕ → ℝ) :
    kerPEndpointWeight N c d = c d := by
  unfold kerPEndpointWeight
  rw [if_neg (by omega), sub_zero]

/-- For `N ≥ 2`, `kerPEndpointWeight N c 1 = c 1`. -/
theorem kerPEndpointWeight_one {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    kerPEndpointWeight N c 1 = c 1 :=
  kerPEndpointWeight_eq_of_lt (by omega) c

/-- **Bulk-Head Preservation of `sievedDivisorSum` Under `kerPEndpointWeight` (`1 ≤ k < N`):**
For every `1 ≤ k < N`, `sievedDivisorSum N (kerPEndpointWeight N c) k = sievedDivisorSum N c k`
because every divisor `d ∣ k` satisfies `d ≤ k < N`. -/
theorem sievedDivisorSum_kerPEndpointWeight_eq_of_lt
    {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) (c : ℕ → ℝ) :
    sievedDivisorSum N (kerPEndpointWeight N c) k = sievedDivisorSum N c k := by
  unfold sievedDivisorSum truncatedSieveWeight
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_le_k : d ≤ k := Nat.le_of_dvd hk1 (Nat.dvd_of_mem_divisors hd)
  rw [kerPEndpointWeight_eq_of_lt (by omega) c]

/-- **Exact Recovery of `vonMangoldt` by `kerPEndpointWeight N (barbanVehovWeight X)`:**
For `1 < k ≤ X < N`, the `ker P`-centered Barban–Vehov weight has
`sievedDivisorSum N (kerPEndpointWeight N (barbanVehovWeight X)) k = Λ(k)`, while its harmonic
pole sum `finiteHarmonicSum N (kerPEndpointWeight N (barbanVehovWeight X))` is identically `0`. -/
theorem sievedDivisorSum_kerPEndpointWeight_barbanVehovWeight_eq_vonMangoldt
    {X N k : ℕ} (hk : 1 < k) (hkX : k ≤ X) (hXN : X < N) :
    sievedDivisorSum N (kerPEndpointWeight N (barbanVehovWeight X)) k = vonMangoldt k := by
  rw [sievedDivisorSum_kerPEndpointWeight_eq_of_lt (by omega) (by omega),
    sievedDivisorSum_barbanVehovWeight_eq_vonMangoldt hk hkX hXN.le]

/-- **Sharpened `ker P` Selberg Lower Bound for `kerPEndpointWeight`:**
For `N ≥ 2` and any `c : ℕ → ℝ`, `kerPEndpointWeight N c` satisfies the `ker P` Cauchy–Schwarz
bound over `2 ≤ e ≤ N` with unaltered numerator `c(1)²`. -/
theorem sq_div_sum_sqfreeTotientInv_Icc_two_le_selbergTotientDiagonalForm_kerPEndpointWeight
    {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    (c 1) ^ (2 : ℕ) / (∑ e ∈ Finset.Icc 2 N, sqfreeTotientInv e) ≤
      selbergTotientDiagonalForm N (kerPEndpointWeight N c) := by
  have h := sq_div_sum_sqfreeTotientInv_Icc_two_le_selbergTotientDiagonalForm_of_harmonic_eq_zero
    (by omega : 1 ≤ N) (kerPEndpointWeight N c)
    (finiteHarmonicSum_kerPEndpointWeight_eq_zero (by omega) c)
  rwa [kerPEndpointWeight_one hN c] at h

/-! ## §3. Master Synthesis of the Exact Signed Sieve, `ker P` Reciprocity & Barban–Vehov Calculus -/

/-- **Master Synthesis of the Exact Signed LCM Fractional-Part Defect, Complete-Fibre Collapse,
Jordan `J₂` Franel Diagonalization, and Barban–Vehov Logarithmic Selberg Pinch:**
Unconditionally establishes:
1. **Lossless Signed Selberg Decomposition & Additive-Multiplicative Reciprocity:**
   `∑_{k=1}^M s_{N,c}(k)² = M · Q_Sel(N, c) - signedLcmFractDefect N M c` and
   `signedLcmFractDefect N (M + 1) c - signedLcmFractDefect N M c = Q_Sel(N, c) - s_{N,c}(M + 1)²`.
2. **Complete-Fibre Möbius Collapse:**
   For `1 ≤ L ≤ N`, `sievedLcmFibre N μ L = μ(L)`.
3. **Rank-One Harmonic Shadow Cancellation Between `Q_Franel` and `Q_Sel`:**
   For `N ≥ 1`, `Q_Franel(N, c) - Q_Sel(N, c) = ∑_{e=2}^N (J₂(e) - φ(e)) Y_{N,c}(e)²`.
4. **Two-Sided `O(1 / log X)` Pinch for `normalizedBarbanVehovWeight X` (`2 ≤ X ≤ N`):**
   `1 / ∑_{e=1}^X sqfreeTotientInv e ≤ Q_Sel(N, w_X) ≤ 4 A² (1 + log X) / (log X)²`.
5. **Exact `ker P` Endpoint Projection:**
   For `N ≥ 2`, `finiteHarmonicSum N (kerPEndpointWeight N c) = 0` and
   `∑_{k=1}^m s_{N, kerPEndpointWeight N c}(k) = -sievedFractSum N (kerPEndpointWeight N c) m`. -/
theorem exact_signed_sieve_and_barbanVehov_master_synthesis :
    (∀ (N M : ℕ) (c : ℕ → ℝ),
      (∑ k ∈ Finset.Icc 1 M, sievedDivisorSum N c k ^ (2 : ℕ)) =
        (M : ℝ) * selbergTotientDiagonalForm N c - signedLcmFractDefect N M c ∧
      signedLcmFractDefect N (M + 1) c - signedLcmFractDefect N M c =
        selbergTotientDiagonalForm N c - sievedDivisorSum N c (M + 1) ^ (2 : ℕ)) ∧
    (∀ {N L : ℕ}, 1 ≤ L → L ≤ N →
      sievedLcmFibre N (fun d => ((μ d : ℤ) : ℝ)) L = ((μ L : ℤ) : ℝ)) ∧
    (∀ {N : ℕ}, 1 ≤ N → ∀ c : ℕ → ℝ,
      franelGcdQuadraticForm N c - selbergTotientDiagonalForm N c =
        ∑ e ∈ Finset.Icc 2 N,
          (jordanTotient2 e - (Nat.totient e : ℝ)) * (selbergMultiplesCoord N c e) ^ (2 : ℕ)) ∧
    (∀ {X N : ℕ}, 2 ≤ X → X ≤ N →
      1 / (∑ e ∈ Finset.Icc 1 X, sqfreeTotientInv e) ≤
          selbergTotientDiagonalForm N (normalizedBarbanVehovWeight X) ∧
        selbergTotientDiagonalForm N (normalizedBarbanVehovWeight X) ≤
          4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ)) /
            (Real.log (X : ℝ)) ^ (2 : ℕ)) ∧
    (∀ {N : ℕ}, 2 ≤ N → ∀ (c : ℕ → ℝ) (m : ℕ),
      finiteHarmonicSum N (kerPEndpointWeight N c) = 0 ∧
      finiteFloorSum N (kerPEndpointWeight N c) (m : ℝ) =
        -sievedFractSum N (kerPEndpointWeight N c) m) :=
  ⟨fun N M c =>
    ⟨sievedDivisorPrefixMeanSquare_eq_selberg_sub_signedLcmFractDefect N M c,
     signedLcmFractDefect_succ_sub_eq N M c⟩,
   fun hL1 hLN => sievedLcmFibre_moebius_eq_moebius_of_le hL1 hLN,
   fun hN c => franelGcdQuadraticForm_sub_selbergTotientDiagonalForm_eq_Icc_two hN c,
   fun hX hXN => selbergTotientDiagonalForm_normalizedBarbanVehovWeight_pinch hX hXN,
   fun {N} hN c m =>
    ⟨finiteHarmonicSum_kerPEndpointWeight_eq_zero (by omega) c,
     finiteFloorSum_nat_eq_neg_sievedFractSum_of_harmonic_eq_zero N (kerPEndpointWeight N c)
       (finiteHarmonicSum_kerPEndpointWeight_eq_zero (by omega) c) m⟩⟩

end GaloisForLFunctions.BiScaleUncertainty

end
