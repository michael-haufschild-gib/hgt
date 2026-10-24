import GaloisForLFunctions.SquareRootThreshold.DoubleWindowMinApertureAndPairCorrelationExchange
import GaloisForLFunctions.SquareRootThreshold.DyadicWindowMultiplicativeIndependence

/-!
# Threshold-localized explicit formula and parity variance law beyond the square-root threshold

At aperture `a` (`X = e^{2a}`, `N = ⌊X⌋`) and height window `η` of aperture `r`, the localized Weil
form of `ζ` splits as `W_ζ(S_ξ f, S_ξ f) = A_f(ξ) − Π_f(ξ)`. In `WindowedOffDiagonalBeyondThreshold`,
the off-diagonal of `Π_f` beyond the square-root threshold `2rX = 1` was bounded by replacing every
frequency's local neighbour count `|(closeSet j)| ≤ n(e^{2r} − e^{−2r})` with the global cutoff
`X(e^{2r} − e^{−2r})`, charging the sub-threshold core and losing a factor of `log X`.

Organizing the localized explicit formula around the **square-root threshold** and the **`2`-adic
parity split** `Π_f = Π_f^odd + Π_f^even` yields four unconditional improvements:

1. **Exact sub-threshold core silence and degree-weight cancellation**
   (`closeSet_primeFreq_eq_empty_of_le`, `sum_card_closeSet_primeFreq_mul_norm_sq_le`,
   `integral_windowed_sq_deviation_le_transThreshold_chebyshev`):
   For any cutoff `N` and `r ≤ log 2`, every sub-threshold index `2r(n + 1) ≤ 1` has
   `closeSet ... (n, b) = ∅`. Above the threshold, the local neighbour count `n(e^{2r} − e^{−2r})`
   cancels the denominator `n` in `|c_{n,b}|² = (Λ(n)²/n)|k_f(±log n)|²`, confining the off-diagonal
   to the trans-threshold Chebyshev sum `(e^{2r} − e^{−2r}) Σ_{2r(n+1) > 1} Λ(n)²(|k_f(log n)|² + |k_f(−log n)|²)`.

2. **Global exact diagonalization of the even prime-power sector at all bandwidths**
   (`integral_normSq_mul_normSq_evenPrimePolynomial_eq`):
   Every even integer `n ≥ 2` with `Λ(n) ≠ 0` is a power of `2` (`n = 2^k`), whose frequencies
   `±k log 2` are `log 2`-separated at every scale. Consequently, whenever `2r ≤ log 2`, the even
   sector `Π_f^even` has **identically zero off-diagonal at every prime cutoff `N`** (for all
   bandwidths `λ > 1`).

3. **`2`-adic parity doubling of the exact diagonalization threshold on the odd sector**
   (`odd_primeFreq_separated`, `integral_normSq_mul_normSq_oddPrimePolynomial_eq`,
   `integral_windowed_sq_deviation_le_of_doubled_threshold`,
   `lintegral_bad_heights_le_of_doubled_threshold`):
   Distinct odd integers satisfy `|m − n| ≥ 2`, so the odd frequencies `±log n` up to `X` are
   `2/X`-separated. Hence `Π_f^odd` is **100% diagonal up to `rX ≤ 1` (`2rX ≤ 2`)**, doubling the
   prime-cutoff threshold of `ZetaLocalizedFormWindowedVarianceLaw` and extending the Chebyshev
   bad-height density bound across the entire trans-threshold octave `1/(2r) < X ≤ 1/r` with no
   `O(rX)` off-diagonal blowup.

4. **Half-density odd neighbour bound and parity-split trans-threshold Chebyshev law**
   (`card_odd_close_log_le`, `odd_closeSet_primeFreq_eq_empty_of_le`,
   `integral_normSq_mul_normSq_oddPrimePolynomial_le_transThreshold_chebyshev`,
   `integral_windowed_sq_deviation_parity_chebyshev_le`):
   At arbitrary bandwidth `rX > 1`, an odd integer `n` has at most `(n/2)(e^{2r} − e^{−2r})` odd
   neighbours within `2r`, and none when `r(n + 2) ≤ 1`. Combining global diagonalization of
   `Π_f^even` with degree cancellation on `Π_f^odd` confines all trans-threshold off-diagonal mass
   to odd prime powers `n > 1/r − 2` at half density.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-! ### 1. Degree-local off-diagonal bounds -/

/-- **Degree-local off-diagonal energy.** Without any uniform bound on neighbour counts,
`Σ_j Σ_{k ∈ closeSet j} ‖c_j‖ ‖c_k‖ ≤ Σ_j |closeSet j| ‖c_j‖²`. -/
theorem sum_closeSet_norm_mul_le_sum_card {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (ν : ι → ℝ) (r : ℝ) :
    ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ * ‖c k‖ ≤
      ∑ j ∈ s, ((closeSet s ν r j).card : ℝ) * ‖c j‖ ^ 2 := by
  have hamgm : ∀ j k, ‖c j‖ * ‖c k‖ ≤ (‖c j‖ ^ 2 + ‖c k‖ ^ 2) / 2 := fun j k => by
    nlinarith [two_mul_le_add_sq ‖c j‖ ‖c k‖]
  have hswap : ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c k‖ ^ 2 =
      ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ ^ 2 := by
    have h1 : ∀ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c k‖ ^ 2 =
        ∑ k ∈ s, if k ∈ closeSet s ν r j then ‖c k‖ ^ 2 else 0 := fun j _ => by
      rw [← Finset.sum_filter]
      congr 1; ext k; simp only [closeSet, Finset.mem_filter]; tauto
    have h2 : ∀ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ ^ 2 =
        ∑ k ∈ s, if j ∈ closeSet s ν r k then ‖c j‖ ^ 2 else 0 := fun j hj => by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext k; simp only [Finset.mem_filter]
      exact ⟨fun hk => ⟨(Finset.mem_filter.mp hk).1, (mem_closeSet_comm hj (Finset.mem_filter.mp hk).1).mp hk⟩,
        fun ⟨hks, hk⟩ => (mem_closeSet_comm hj hks).mpr hk⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  calc ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ * ‖c k‖
      ≤ ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, (‖c j‖ ^ 2 + ‖c k‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hamgm j k
    _ = (∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ ^ 2 +
          ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c k‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ j ∈ s, ((closeSet s ν r j).card : ℝ) * ‖c j‖ ^ 2 := by
        rw [hswap, add_self_div_two]
        refine Finset.sum_congr rfl fun j _ => by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Degree-local off-diagonal norm bound.** For a window supported in `[-r, r]`, the off-diagonal
is at most `‖η‖² Σ_j |closeSet j| ‖c_j‖²`. -/
theorem norm_offDiag_le_sum_card {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (ν : ι → ℝ) :
    ‖∑ j ∈ s, ∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (ν j - ν k)‖ ≤
      (∫ t, ‖η t‖ ^ 2) * ∑ j ∈ s, ((closeSet s ν r j).card : ℝ) * ‖c j‖ ^ 2 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hrestrict : ∀ j ∈ s, ∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (ν j - ν k) =
      ∑ k ∈ closeSet s ν r j, c j * conj (c k) * EF.weilTest η η (ν j - ν k) := by
    intro j _
    refine (Finset.sum_subset (fun k hk => ?_) fun k hk hkn => ?_).symm
    · simp only [closeSet, Finset.mem_filter] at hk
      exact Finset.mem_erase.mpr ⟨hk.2.1, hk.1⟩
    · have hks := Finset.mem_erase.mp hk
      have hfar : 2 * r ≤ |ν j - ν k| := by
        by_contra h
        exact hkn (Finset.mem_filter.mpr ⟨hks.2, hks.1, not_le.mp h⟩)
      rw [weilTest_self_eq_zero_of_le hη hηs hfar, mul_zero]
  rw [Finset.sum_congr rfl hrestrict]
  have hk : ∀ v, ‖EF.weilTest η η v‖ ≤ ∫ t, ‖η t‖ ^ 2 := norm_weilTest_self_le hη.continuous hηc
  have hN0 : 0 ≤ ∫ t, ‖η t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  calc ‖∑ j ∈ s, ∑ k ∈ closeSet s ν r j, c j * conj (c k) * EF.weilTest η η (ν j - ν k)‖
      ≤ ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j * conj (c k) * EF.weilTest η η (ν j - ν k)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, (∫ t, ‖η t‖ ^ 2) * (‖c j‖ * ‖c k‖) := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]
        nlinarith [hk (ν j - ν k), norm_nonneg (c j), norm_nonneg (c k),
          mul_nonneg (norm_nonneg (c j)) (norm_nonneg (c k))]
    _ = (∫ t, ‖η t‖ ^ 2) * ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ * ‖c k‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    _ ≤ (∫ t, ‖η t‖ ^ 2) * ∑ j ∈ s, ((closeSet s ν r j).card : ℝ) * ‖c j‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_closeSet_norm_mul_le_sum_card s c ν r) hN0

/-- **Degree-local windowed mean value bound.** -/
theorem integral_normSq_mul_normSq_expSum_le_sum_card {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (ν : ι → ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖expSum s c ν ξ‖ ^ 2 ≤
      (∫ t, ‖η t‖ ^ 2) * ∑ j ∈ s, (1 + ((closeSet s ν r j).card : ℝ)) * ‖c j‖ ^ 2 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  rw [integral_normSq_mul_normSq_expSum_eq_diag_add hη hηc]
  have hoff := (Complex.re_le_norm _).trans (norm_offDiag_le_sum_card hη hηs s c ν)
  have hsum : ∑ j ∈ s, (1 + ((closeSet s ν r j).card : ℝ)) * ‖c j‖ ^ 2 =
      (∑ j ∈ s, ‖c j‖ ^ 2) + ∑ j ∈ s, ((closeSet s ν r j).card : ℝ) * ‖c j‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, mul_add]
  linarith

/-! ### 2. Sub-threshold core silence and degree-weight cancellation -/

/-- **Sub-threshold core silence.** For any cutoff `N` and `r ≤ log 2`, every index `(n, b)` with
`2 ≤ n` and `2r(n + 1) ≤ 1` has no close neighbours in `[2, N] × Bool`. -/
theorem closeSet_primeFreq_eq_empty_of_le (N : ℕ) {r : ℝ} (hr2 : r ≤ Real.log 2) {n : ℕ}
    (hn2 : 2 ≤ n) (hnr : 2 * r * ((n : ℝ) + 1) ≤ 1) (b : Bool) :
    closeSet (Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool)) primeFreq r (n, b) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨m, b₀⟩ hx
  simp only [closeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ,
    and_true, ne_eq, Prod.mk.injEq, not_and] at hx
  obtain ⟨hmN, hne, hclose⟩ := hx
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2r : 2 * r ≤ 1 / ((n : ℝ) + 1) := (le_div_iff₀ hn1).mpr hnr
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hmN.1)
  have hb : b₀ = b := by
    by_contra hbb
    cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
    · exact hbb rfl
    · rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
        abs_of_nonneg (by linarith)] at hclose
      linarith
    · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
        abs_of_nonneg (by linarith)] at hclose
      linarith
    · exact hbb rfl
  subst b₀
  have hmn : m ≠ n := fun h => hne h rfl
  have hlog_close : |Real.log n - Real.log m| < 2 * r := by
    cases b <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
    · rwa [show -Real.log n - -Real.log m = -(Real.log n - Real.log m) by ring, abs_neg] at hclose
    · exact hclose
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hsep := inv_le_log_sub_log (show 1 ≤ m by omega) hlt (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
    rw [abs_of_nonneg (by linarith [div_pos one_pos hn1])] at hlog_close
    linarith
  · have hsucc : n + 1 ≤ m := hgt
    have hsep1 := inv_le_log_sub_log (show 1 ≤ n by omega) (Nat.lt_succ_self n)
      (show ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 by push_cast; rfl)
    have hsep2 : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hsucc)
    rw [abs_sub_comm, abs_of_nonneg (by linarith [div_pos one_pos hn1])] at hlog_close
    linarith

/-- Per-index neighbour bound for `primeFreq`: `|(closeSet (n, b))| ≤ n(e^{2r} − e^{−2r})` without
replacing `n` by `X`. -/
theorem card_closeSet_primeFreq_le_self (N : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2)
    {n : ℕ} (hn2 : 2 ≤ n) (b : Bool) :
    ((closeSet (Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool)) primeFreq r (n, b)).card : ℝ) ≤
      (n : ℝ) * (Real.exp (2 * r) - Real.exp (-(2 * r))) := by
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hinj : Set.InjOn Prod.fst
      ((closeSet (Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool)) primeFreq r (n, b) :
        Finset (ℕ × Bool)) : Set (ℕ × Bool)) := by
    rintro ⟨m, b₁⟩ hm ⟨m', b₂⟩ hm' hmm
    change m = m' at hmm
    simp only [closeSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_univ, and_true] at hm hm'
    have hb : ∀ {m₀ : ℕ} {b₀ : Bool}, 2 ≤ m₀ → |primeFreq (n, b) - primeFreq (m₀, b₀)| < 2 * r →
        b₀ = b := by
      intro m₀ b₀ hm₀ hclose
      by_contra hne
      have hlm : Real.log 2 ≤ Real.log m₀ := Real.log_le_log (by norm_num) (by exact_mod_cast hm₀)
      cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
      · exact hne rfl
      · rw [show -Real.log n - Real.log m₀ = -(Real.log n + Real.log m₀) by ring, abs_neg,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · rw [show Real.log n - -Real.log m₀ = Real.log n + Real.log m₀ by ring,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · exact hne rfl
    rw [hb hm.1.1 hm.2.2, hb hm'.1.1 hm'.2.2, hmm]
  have hmaps : ∀ x ∈ closeSet (Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool)) primeFreq r (n, b),
      x.1 ∈ (Finset.Icc 2 N).filter fun m => m ≠ n ∧ |Real.log n - Real.log m| < 2 * r := by
    rintro ⟨m, b₀⟩ hx
    simp only [closeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ,
      and_true, ne_eq, Prod.mk.injEq, not_and] at hx
    obtain ⟨hmN, hne, hclose⟩ := hx
    have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hmN.1)
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨hmN, ?_, ?_⟩
    · intro hmn
      cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
      · exact hne hmn rfl
      · rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · exact hne hmn rfl
    · cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
      · rwa [show -Real.log n - -Real.log m = -(Real.log n - Real.log m) by ring, abs_neg] at hclose
      · rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · exact hclose
  have hcard := Finset.card_le_card_of_injOn Prod.fst hmaps hinj
  exact (Nat.cast_le.mpr hcard).trans (card_close_log_le hr (by omega))

/-- **Degree-weight cancellation on the trans-threshold tail.** Multiplying `|(closeSet (n, b))|`
by `‖primeCoeff f (n, b)‖² = (Λ(n)²/n) ‖k_f(±log n)‖²` cancels the denominator `n` and vanishes on
the sub-threshold core `2r(n + 1) ≤ 1`. -/
theorem sum_card_closeSet_primeFreq_mul_norm_sq_le (f : ℝ → ℂ) (N : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2) (ξ₀ : ℝ) :
    ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool),
        ((closeSet (Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool)) primeFreq r j).card : ℝ) *
          ‖primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)‖ ^ 2 ≤
      (Real.exp (2 * r) - Real.exp (-(2 * r))) *
        ∑ n ∈ Finset.Icc 2 N,
          if 1 < 2 * r * ((n : ℝ) + 1) then
            (ArithmeticFunction.vonMangoldt n) ^ 2 *
              (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)
          else 0 := by
  rw [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Fintype.sum_bool]
  have hnorm (b : Bool) : ‖primeCoeff f (n, b) * cexp (2 * π * I * ξ₀ * primeFreq (n, b))‖ ^ 2 =
      (ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) * ‖EF.weilTest f f (primeFreq (n, b))‖ ^ 2 := by
    simp only [primeCoeff, norm_mul, norm_cexp_two_pi_I_mul, mul_one, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, div_pow, Real.sq_sqrt hn0.le]
  rw [hnorm true, hnorm false]
  split_ifs with htrans
  · have h1 := card_closeSet_primeFreq_le_self N hr hr2 hn2 true
    have h2 := card_closeSet_primeFreq_le_self N hr hr2 hn2 false
    have hpos1 : 0 ≤ (ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
        ‖EF.weilTest f f (primeFreq (n, true))‖ ^ 2 := by positivity
    have hpos2 : 0 ≤ (ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
        ‖EF.weilTest f f (primeFreq (n, false))‖ ^ 2 := by positivity
    calc ((closeSet (Finset.Icc 2 N ×ˢ Finset.univ) primeFreq r (n, true)).card : ℝ) *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
              ‖EF.weilTest f f (primeFreq (n, true))‖ ^ 2) +
          ((closeSet (Finset.Icc 2 N ×ˢ Finset.univ) primeFreq r (n, false)).card : ℝ) *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
              ‖EF.weilTest f f (primeFreq (n, false))‖ ^ 2)
        ≤ (n : ℝ) * (Real.exp (2 * r) - Real.exp (-(2 * r))) *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
              ‖EF.weilTest f f (Real.log n)‖ ^ 2) +
          (n : ℝ) * (Real.exp (2 * r) - Real.exp (-(2 * r))) *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
              ‖EF.weilTest f f (-Real.log n)‖ ^ 2) := by
          exact add_le_add (mul_le_mul_of_nonneg_right h1 hpos1)
            (mul_le_mul_of_nonneg_right h2 hpos2)
      _ = (Real.exp (2 * r) - Real.exp (-(2 * r))) *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 *
              (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)) := by
          have hne : (n : ℝ) ≠ 0 := hn0.ne'
          field_simp
  · have hle : 2 * r * ((n : ℝ) + 1) ≤ 1 := not_lt.mp htrans
    rw [closeSet_primeFreq_eq_empty_of_le N hr2 hn2 hle true,
      closeSet_primeFreq_eq_empty_of_le N hr2 hn2 hle false]
    simp

/-- **Threshold-localized windowed variance bound for `ζ`.** The sub-threshold core
`2r(n + 1) ≤ 1` contributes only to the diagonal `V_f`, while the trans-threshold tail
`2r(n + 1) > 1` enters with its degree-cancelled Chebyshev weight `Λ(n)²`. -/
theorem integral_windowed_sq_deviation_le_transThreshold_chebyshev {a r : ℝ} {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hη : ContDiff ℝ 2 η)
    (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2) (hηs : tsupport η ⊆ Icc (-r) r) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
          archPart f (ξ + ξ₀)‖ ^ 2 ≤
      (∫ t, ‖η t‖ ^ 2) *
        (primeVariance f ⌊Real.exp (2 * a)⌋₊ +
          (Real.exp (2 * r) - Real.exp (-(2 * r))) *
            ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
              if 1 < 2 * r * ((n : ℝ) + 1) then
                (ArithmeticFunction.vonMangoldt n) ^ 2 *
                  (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)
              else 0) := by
  have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
      archPart f (ξ + ξ₀)‖ = ‖primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)‖ := by
    intro ξ
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
  simp_rw [hdev, primePolynomial, expSum_add]
  have h1 := integral_normSq_mul_normSq_expSum_le_sum_card hη hηs
    (Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ ×ˢ (Finset.univ : Finset Bool))
    (fun j => primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)) primeFreq
  have hsplit : ∑ j ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ ×ˢ (Finset.univ : Finset Bool),
      (1 + ((closeSet (Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ ×ˢ Finset.univ) primeFreq r j).card : ℝ)) *
        ‖primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)‖ ^ 2 =
      primeVariance f ⌊Real.exp (2 * a)⌋₊ +
        ∑ j ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ ×ˢ (Finset.univ : Finset Bool),
          ((closeSet (Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ ×ˢ Finset.univ) primeFreq r j).card : ℝ) *
            ‖primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)‖ ^ 2 := by
    rw [← sum_norm_sq_primeCoeff_shift_eq f ⌊Real.exp (2 * a)⌋₊ ξ₀, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit] at h1
  have hN0 : 0 ≤ ∫ t, ‖η t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsum := sum_card_closeSet_primeFreq_mul_norm_sq_le f ⌊Real.exp (2 * a)⌋₊ hr hr2 ξ₀
  exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) hN0)

/-! ### 3. Parity decomposition of the prime polynomial and global diagonalization of the even sector -/

/-- The odd-index part of the prime polynomial `Π_f^odd(ξ)`. -/
def oddPrimePolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) : ℂ :=
  expSum (((Finset.Icc 2 N).filter Odd) ×ˢ Finset.univ) (primeCoeff f) primeFreq ξ

/-- The even-index part of the prime polynomial `Π_f^even(ξ)`. -/
def evenPrimePolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) : ℂ :=
  expSum (((Finset.Icc 2 N).filter Even) ×ˢ Finset.univ) (primeCoeff f) primeFreq ξ

/-- The diagonal energy `V_f^odd` of the odd prime polynomial. -/
def oddPrimeVariance (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 2 N).filter Odd, (ArithmeticFunction.vonMangoldt n) ^ 2 / n *
    (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)

/-- The diagonal energy `V_f^even` of the even prime polynomial. -/
def evenPrimeVariance (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 2 N).filter Even, (ArithmeticFunction.vonMangoldt n) ^ 2 / n *
    (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)

/-- **Parity decomposition of the prime polynomial:** `Π_f = Π_f^odd + Π_f^even`. -/
theorem primePolynomial_eq_odd_add_even (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    primePolynomial f N ξ = oddPrimePolynomial f N ξ + evenPrimePolynomial f N ξ := by
  classical
  simp only [primePolynomial, oddPrimePolynomial, evenPrimePolynomial, expSum, Finset.sum_product]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 N) Odd]
  congr 2
  ext n
  simp [Nat.not_odd_iff_even]

/-- **Parity decomposition of the diagonal energy:** `V_f = V_f^odd + V_f^even`. -/
theorem primeVariance_eq_odd_add_even (f : ℝ → ℂ) (N : ℕ) :
    primeVariance f N = oddPrimeVariance f N + evenPrimeVariance f N := by
  classical
  simp only [primeVariance, oddPrimeVariance, evenPrimeVariance]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 N) Odd]
  congr 2
  ext n
  simp [Nat.not_odd_iff_even]

/-- **Windowed mean value law when off-diagonal pairs either vanish in coefficient or are
`2r`-separated.** -/
theorem integral_normSq_mul_normSq_expSum_of_coeff_or_separated {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ι → ℂ) (ν : ι → ℝ)
    (hsep : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → c j = 0 ∨ c k = 0 ∨ 2 * r ≤ |ν j - ν k|) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖expSum s c ν ξ‖ ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * ∑ j ∈ s, ‖c j‖ ^ 2 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  rw [integral_normSq_mul_normSq_expSum_eq_diag_add hη hηc]
  have hzero : ∑ j ∈ s, ∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (ν j - ν k) = 0 := by
    refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hkj, hks⟩ := Finset.mem_erase.mp hk
    rcases hsep j hj k hks hkj.symm with hcj | hck | hfar
    · rw [hcj, zero_mul, zero_mul]
    · rw [hck, map_zero, mul_zero, zero_mul]
    · rw [weilTest_self_eq_zero_of_le hη hηs hfar, mul_zero]
  rw [hzero, Complex.zero_re, add_zero]

/-- An even integer `n` with `Λ(n) ≠ 0` is a positive power of `2`. -/
private theorem exists_two_pow_of_even_of_vonMangoldt_ne_zero {n : ℕ} (he : Even n)
    (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) : ∃ a : ℕ, 1 ≤ a ∧ n = 2 ^ a := by
  have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  obtain ⟨q, a, hq, ha, hqa⟩ := (isPrimePow_nat_iff n).mp hpp
  have hdvd : 2 ∣ n := even_iff_two_dvd.mp he
  have h2q : 2 = q :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp (Nat.prime_two.dvd_of_dvd_pow (hqa ▸ hdvd))
  exact ⟨a, ha, by rw [h2q, hqa]⟩

/-- **Even prime-power frequencies are `log 2`-separated at every cutoff `N`.** Any two distinct
indices `j ≠ k` in the even sector either have a vanishing `primeCoeff` (when the integer is not a
power of `2`) or are separated by at least `log 2`. -/
theorem even_primeFreq_coeff_or_separated (f : ℝ → ℂ) (N : ℕ) {r : ℝ} (hr2 : 2 * r ≤ Real.log 2)
    (ξ₀ : ℝ) :
    ∀ j ∈ ((Finset.Icc 2 N).filter Even) ×ˢ (Finset.univ : Finset Bool),
      ∀ k ∈ ((Finset.Icc 2 N).filter Even) ×ˢ (Finset.univ : Finset Bool),
        j ≠ k →
          primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j) = 0 ∨
          primeCoeff f k * cexp (2 * π * I * ξ₀ * primeFreq k) = 0 ∨
          2 * r ≤ |primeFreq j - primeFreq k| := by
  rintro ⟨n, b⟩ hj ⟨m, b'⟩ hk hne
  by_cases hΛn : ArithmeticFunction.vonMangoldt n = 0
  · left; simp [primeCoeff, hΛn]
  by_cases hΛm : ArithmeticFunction.vonMangoldt m = 0
  · right; left; simp [primeCoeff, hΛm]
  right; right
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc, Finset.mem_univ, and_true] at hj hk
  obtain ⟨a, ha1, rfl⟩ := exists_two_pow_of_even_of_vonMangoldt_ne_zero hj.2 hΛn
  obtain ⟨a', ha'1, rfl⟩ := exists_two_pow_of_even_of_vonMangoldt_ne_zero hk.2 hΛm
  have hlog_a : Real.log ((2 ^ a : ℕ) : ℝ) = (a : ℝ) * Real.log 2 := by push_cast; rw [Real.log_pow]
  have hlog_a' : Real.log ((2 ^ a' : ℕ) : ℝ) = (a' : ℝ) * Real.log 2 := by push_cast; rw [Real.log_pow]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiff : ∀ {u v : ℕ}, u ≠ v → 1 ≤ |(u : ℝ) - (v : ℝ)| := fun {u v} huv => by
    rcases lt_or_gt_of_ne huv with h | h
    · have : (u : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : (v : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have ha_ne : b = b' → a ≠ a' := fun hbb haa => hne (by rw [haa, hbb])
  cases b <;> cases b' <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true, hlog_a, hlog_a']
  · rw [show -((a : ℝ) * Real.log 2) - -((a' : ℝ) * Real.log 2) =
        -(((a : ℝ) - (a' : ℝ)) * Real.log 2) by ring, abs_neg, abs_mul, abs_of_pos hl2]
    nlinarith [hdiff (ha_ne rfl)]
  · have hsum : (1 : ℝ) ≤ (a : ℝ) + (a' : ℝ) := by
      have : 2 ≤ a + a' := by omega
      exact_mod_cast le_trans (by norm_num : 1 ≤ 2) this
    rw [show -((a : ℝ) * Real.log 2) - (a' : ℝ) * Real.log 2 =
        -(((a : ℝ) + (a' : ℝ)) * Real.log 2) by ring, abs_neg,
        abs_of_nonneg (mul_nonneg (by linarith) hl2.le)]
    nlinarith
  · have hsum : (1 : ℝ) ≤ (a : ℝ) + (a' : ℝ) := by
      have : 2 ≤ a + a' := by omega
      exact_mod_cast le_trans (by norm_num : 1 ≤ 2) this
    rw [show (a : ℝ) * Real.log 2 - -((a' : ℝ) * Real.log 2) =
        ((a : ℝ) + (a' : ℝ)) * Real.log 2 by ring,
        abs_of_nonneg (mul_nonneg (by linarith) hl2.le)]
    nlinarith
  · rw [show (a : ℝ) * Real.log 2 - (a' : ℝ) * Real.log 2 =
        ((a : ℝ) - (a' : ℝ)) * Real.log 2 by ring, abs_mul, abs_of_pos hl2]
    nlinarith [hdiff (ha_ne rfl)]

/-- **Global exact diagonalization of the even prime-power sector at all bandwidths.** For any
window supported in `[-r, r]` with `2r ≤ log 2` and **every** cutoff `N ∈ ℕ` (with no restriction
on `rN`), `∫ |h_η(−2πξ)|² |Π_f^even(ξ + ξ₀)|² dξ = ‖η‖² V_f^even(N)`. -/
theorem integral_normSq_mul_normSq_evenPrimePolynomial_eq {r : ℝ} {f η : ℝ → ℂ}
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r) (hr2 : 2 * r ≤ Real.log 2)
    (N : ℕ) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖evenPrimePolynomial f N (ξ + ξ₀)‖ ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * evenPrimeVariance f N := by
  simp_rw [evenPrimePolynomial, expSum_add]
  rw [integral_normSq_mul_normSq_expSum_of_coeff_or_separated hη hηs _ _ _
    (even_primeFreq_coeff_or_separated f N hr2 ξ₀)]
  congr 1
  rw [evenPrimeVariance, Finset.sum_product]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Fintype.sum_bool]
  simp only [primeCoeff, primeFreq, ↓reduceIte, Bool.false_eq_true, norm_mul,
    norm_cexp_two_pi_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    div_pow, Real.sq_sqrt hn0]
  ring

/-! ### 4. `2`-adic parity doubling of the exact diagonalization threshold on the odd sector -/

/-- Two distinct odd integers `1 ≤ n < m ≤ X` have `log m − log n ≥ 2 / X`. -/
theorem two_div_le_log_sub_log_of_odd {n m : ℕ} {X : ℝ} (hn : 1 ≤ n) (hno : Odd n) (hmo : Odd m)
    (hnm : n < m) (hmX : (m : ℝ) ≤ X) :
    2 / X ≤ Real.log m - Real.log n := by
  obtain ⟨i, rfl⟩ := hno
  obtain ⟨j, rfl⟩ := hmo
  have hdiff2 : (2 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) - ((2 * i + 1 : ℕ) : ℝ) := by
    have : (2 * i + 1) + 2 ≤ 2 * j + 1 := by omega
    have hcast : ((2 * i + 1 : ℕ) : ℝ) + 2 ≤ ((2 * j + 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hn0 : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hm0 hn0)
  rw [Real.log_div hm0.ne' hn0.ne', inv_div] at hlog
  have h1 : 2 / X ≤ 2 / ((2 * j + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hm0 hmX
  have h2 : 2 / ((2 * j + 1 : ℕ) : ℝ) ≤ 1 - ((2 * i + 1 : ℕ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ) := by
    rw [one_sub_div hm0.ne', div_le_div_iff_of_pos_right hm0]
    linarith
  linarith

/-- **Odd prime frequencies up to `X` are `2r`-separated when `rX ≤ 1` (`2rX ≤ 2`) and
`2r ≤ log 2`.** -/
theorem odd_primeFreq_separated {r X : ℝ} (hX1 : 1 ≤ X) (hrX : r * X ≤ 1)
    (hr2 : 2 * r ≤ Real.log 2) :
    ∀ j ∈ ((Finset.Icc 2 ⌊X⌋₊).filter Odd) ×ˢ (Finset.univ : Finset Bool),
      ∀ k ∈ ((Finset.Icc 2 ⌊X⌋₊).filter Odd) ×ˢ (Finset.univ : Finset Bool),
        j ≠ k → 2 * r ≤ |primeFreq j - primeFreq k| := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX0 : 0 < X := by linarith
  have h2r : 2 * r ≤ 2 / X := by rw [le_div_iff₀ hX0]; linarith
  rintro ⟨n, b⟩ hj ⟨m, b'⟩ hk hne
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc, Finset.mem_univ, and_true] at hj hk
  have hnX : (n : ℝ) ≤ X := le_trans (by exact_mod_cast hj.1.2) (Nat.floor_le hX0.le)
  have hmX : (m : ℝ) ≤ X := le_trans (by exact_mod_cast hk.1.2) (Nat.floor_le hX0.le)
  have hn2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hj.1.1)
  have hm2 : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hk.1.1)
  have hsame : n ≠ m → 2 / X ≤ |Real.log n - Real.log m| := by
    intro hnm
    rcases lt_or_gt_of_ne hnm with h | h
    · have := two_div_le_log_sub_log_of_odd (by omega) hj.2 hk.2 h hmX
      rw [abs_sub_comm]
      exact this.trans (le_abs_self _)
    · have := two_div_le_log_sub_log_of_odd (by omega) hk.2 hj.2 h hnX
      exact this.trans (le_abs_self _)
  cases b <;> cases b' <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true]
  · have hnm : n ≠ m := fun h => hne (by rw [h])
    rw [show -Real.log n - -Real.log m = -(Real.log n - Real.log m) by ring, abs_neg]
    linarith [hsame hnm]
  · rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
      abs_of_nonneg (by linarith)]
    linarith
  · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
      abs_of_nonneg (by linarith)]
    linarith
  · have hnm : n ≠ m := fun h => hne (by rw [h])
    linarith [hsame hnm]

/-- **Exact diagonalization of the odd prime polynomial up to the doubled cutoff `rX ≤ 1`
(`2rX ≤ 2`).** -/
theorem integral_normSq_mul_normSq_oddPrimePolynomial_eq {r X : ℝ} (hX1 : 1 ≤ X) {f η : ℝ → ℂ}
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r) (hrX : r * X ≤ 1)
    (hr2 : 2 * r ≤ Real.log 2) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖oddPrimePolynomial f ⌊X⌋₊ (ξ + ξ₀)‖ ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * oddPrimeVariance f ⌊X⌋₊ := by
  simp_rw [oddPrimePolynomial, expSum_add]
  rw [integral_normSq_mul_normSq_expSum_of_separated hη hηs _ _ _
    (odd_primeFreq_separated hX1 hrX hr2)]
  congr 1
  rw [oddPrimeVariance, Finset.sum_product]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Fintype.sum_bool]
  simp only [primeCoeff, primeFreq, ↓reduceIte, Bool.false_eq_true, norm_mul,
    norm_cexp_two_pi_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    div_pow, Real.sq_sqrt hn0]
  ring

/-- Pointwise parallelogram bound relating the windowed mean square of `Π_f` to its odd and even
parts. -/
theorem integral_normSq_mul_normSq_primePolynomial_le_two_mul_odd_add_even {r : ℝ} {f η : ℝ → ℂ}
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r) (N : ℕ) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖primePolynomial f N (ξ + ξ₀)‖ ^ 2 ≤
      2 * (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖oddPrimePolynomial f N (ξ + ξ₀)‖ ^ 2) +
        2 * (∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖evenPrimePolynomial f N (ξ + ξ₀)‖ ^ 2) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  have hPi : Integrable P := by
    refine (integrable_pairTransform hη hηc).re.congr (Eventually.of_forall fun ξ => ?_)
    simp only [pairTransform_ofReal hη hηc ξ, RCLike.re_to_complex, Complex.ofReal_re, hP]
  have hPc : Continuous P := by
    have h := Complex.continuous_re.comp ((differentiable_pairTransform hη hηc).continuous.comp
      Complex.continuous_ofReal)
    exact h.congr fun ξ => by simp only [Function.comp_apply, pairTransform_ofReal hη hηc ξ,
      Complex.ofReal_re, hP]
  have hint_exp {s : Finset (ℕ × Bool)} :
      Integrable fun ξ : ℝ => P ξ * ‖expSum s (primeCoeff f) primeFreq (ξ + ξ₀)‖ ^ 2 := by
    set C := ∑ j ∈ s, ‖primeCoeff f j‖
    have hQc : Continuous fun ξ => expSum s (primeCoeff f) primeFreq (ξ + ξ₀) :=
      (continuous_expSum _ _ _).comp (continuous_id.add continuous_const)
    refine (hPi.mul_const (C ^ 2)).mono' (hPc.mul (hQc.norm.pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_expSum_le _ _ _ _) 2)
      (sq_nonneg _)
  have h1 : Integrable fun ξ : ℝ => P ξ * ‖oddPrimePolynomial f N (ξ + ξ₀)‖ ^ 2 := hint_exp
  have h2 : Integrable fun ξ : ℝ => P ξ * ‖evenPrimePolynomial f N (ξ + ξ₀)‖ ^ 2 := hint_exp
  have h0 : Integrable fun ξ : ℝ => P ξ * ‖primePolynomial f N (ξ + ξ₀)‖ ^ 2 := hint_exp
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul 2) (h2.const_mul 2)]
  refine integral_mono h0 ((h1.const_mul 2).add (h2.const_mul 2)) fun ξ => ?_
  dsimp only
  rw [primePolynomial_eq_odd_add_even]
  set u := oddPrimePolynomial f N (ξ + ξ₀)
  set v := evenPrimePolynomial f N (ξ + ξ₀)
  have htri : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    have h := norm_add_le u v
    nlinarith [norm_nonneg (u + v), norm_nonneg u, norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]
  have hP0 : 0 ≤ P ξ := sq_nonneg _
  calc P ξ * ‖u + v‖ ^ 2 ≤ P ξ * (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left htri hP0
    _ = 2 * (P ξ * ‖u‖ ^ 2) + 2 * (P ξ * ‖v‖ ^ 2) := by ring

/-- **Windowed variance bound across the doubled threshold `r e^{2a} ≤ 1` (`2rX ≤ 2`).** Because
the odd sector diagonalizes up to `rX ≤ 1` and the even sector diagonalizes globally for
`2r ≤ log 2`, the windowed mean square of `W_ζ − A_f` is at most `2 ‖η‖² V_f` throughout the
trans-threshold octave `X ≤ 1/r`. -/
theorem integral_windowed_sq_deviation_le_of_doubled_threshold {a r : ℝ} (ha : 0 ≤ a)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) (hrX : r * Real.exp (2 * a) ≤ 1) (hr2 : 2 * r ≤ Real.log 2)
    (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
          archPart f (ξ + ξ₀)‖ ^ 2 ≤
      2 * (∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ := by
  have hX1 : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
      archPart f (ξ + ξ₀)‖ = ‖primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)‖ := by
    intro ξ
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
  simp_rw [hdev]
  refine (integral_normSq_mul_normSq_primePolynomial_le_two_mul_odd_add_even hη hηs _ ξ₀).trans ?_
  rw [integral_normSq_mul_normSq_oddPrimePolynomial_eq hX1 hη hηs hrX hr2 ξ₀,
    integral_normSq_mul_normSq_evenPrimePolynomial_eq hη hηs hr2 _ ξ₀,
    primeVariance_eq_odd_add_even]
  linarith

/-- **Chebyshev bound for negative localized forms across the doubled threshold `r e^{2a} ≤ 1`.**
Extends `lintegral_bad_heights_le` from `2rX ≤ 1` to `rX ≤ 1` (`2rX ≤ 2`) with factor `2`. -/
theorem lintegral_bad_heights_le_of_doubled_threshold {a r : ℝ} (ha : 0 ≤ a) {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) (hrX : r * Real.exp (2 * a) ≤ 1) (hr2 : 2 * r ≤ Real.log 2)
    (ξ₀ : ℝ) {U : Set ℝ} {A₀ : ℝ} (hA₀ : 0 < A₀)
    (hU : ∀ ξ ∈ U, A₀ ≤ (archPart f (ξ + ξ₀)).re) :
    ∫⁻ ξ, (U ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
        (heightShift (ξ + ξ₀) f)).re < 0}).indicator
        (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
      ENNReal.ofReal (2 * (∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ / A₀ ^ 2) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set N := ⌊Real.exp (2 * a)⌋₊
  set Q : ℝ → ℂ := fun ξ => primePolynomial f N (ξ + ξ₀) with hQ
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  have hPi : Integrable P := by
    refine (integrable_pairTransform hη hηc).re.congr (Eventually.of_forall fun ξ => ?_)
    simp only [pairTransform_ofReal hη hηc ξ, RCLike.re_to_complex, Complex.ofReal_re, hP]
  have hPc : Continuous P := by
    have h := Complex.continuous_re.comp ((differentiable_pairTransform hη hηc).continuous.comp
      Complex.continuous_ofReal)
    exact h.congr fun ξ => by simp only [Function.comp_apply, pairTransform_ofReal hη hηc ξ,
      Complex.ofReal_re, hP]
  have hQc : Continuous Q :=
    (continuous_expSum _ _ _).comp (continuous_id.add continuous_const)
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖
  set G : ℝ → ℝ := fun ξ => P ξ * ‖Q ξ‖ ^ 2 / A₀ ^ 2 with hG
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => by positivity
  have hGi : Integrable G := by
    refine (hPi.mul_const (C ^ 2 / A₀ ^ 2)).mono'
      ((hPc.mul (hQc.norm.pow 2)).div_const _).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (hG0 ξ)]
    show P ξ * ‖Q ξ‖ ^ 2 / A₀ ^ 2 ≤ P ξ * (C ^ 2 / A₀ ^ 2)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_expSum_le _ _ _ _) 2)
        (by positivity)) (sq_nonneg _)
  have hGint : ∫ ξ, G ξ ≤ 2 * (∫ t, ‖η t‖ ^ 2) * primeVariance f N / A₀ ^ 2 := by
    have hvar := integral_windowed_sq_deviation_le_of_doubled_threshold ha hf hfs hη hηs hrX hr2 ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := fun ξ => by
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    simp only [hG, integral_div]
    exact div_le_div_of_nonneg_right hvar (by positivity)
  refine (lintegral_mono fun ξ => ?_).trans
    ((ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hG0)).symm.le.trans
      (ENNReal.ofReal_le_ofReal hGint))
  by_cases hξ : ξ ∈ U ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
      (heightShift (ξ + ξ₀) f)).re < 0}
  · rw [Set.indicator_of_mem hξ]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨hU', hneg⟩ := hξ
    simp only [Set.mem_setOf_eq] at hneg
    have hA := hU ξ hU'
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at hneg
    have hQn : A₀ ≤ ‖Q ξ‖ := (show A₀ ≤ (Q ξ).re by simp only [hQ]; linarith).trans (Complex.re_le_norm _)
    have hratio : 1 ≤ ‖Q ξ‖ ^ 2 / A₀ ^ 2 :=
      (le_div_iff₀ (by positivity)).mpr (by rw [one_mul]; exact pow_le_pow_left₀ hA₀.le hQn 2)
    calc ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 = P ξ * 1 := by rw [mul_one]
      _ ≤ P ξ * (‖Q ξ‖ ^ 2 / A₀ ^ 2) := mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
      _ = G ξ := by rw [hG]; ring
  · rw [Set.indicator_of_notMem hξ]; exact bot_le

/-! ### 5. Half-density odd neighbour bound and parity-split trans-threshold Chebyshev law -/

/-- **Odd-sector sub-threshold core silence.** For any cutoff `N` and `2r ≤ log 2`, every odd index
`(n, b)` with `r(n + 2) ≤ 1` has no close odd neighbours in `([2, N].filter Odd) × Bool`. -/
theorem odd_closeSet_primeFreq_eq_empty_of_le (N : ℕ) {r : ℝ} (hr2 : 2 * r ≤ Real.log 2) {n : ℕ}
    (hn2 : 2 ≤ n) (hno : Odd n) (hnr : r * ((n : ℝ) + 2) ≤ 1) (b : Bool) :
    closeSet (((Finset.Icc 2 N).filter Odd) ×ˢ (Finset.univ : Finset Bool)) primeFreq r (n, b) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨m, b₀⟩ hx
  simp only [closeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ,
    and_true, ne_eq, Prod.mk.injEq, not_and] at hx
  obtain ⟨⟨hmN, hmo⟩, hne, hclose⟩ := hx
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h2r : 2 * r ≤ 2 / ((n : ℝ) + 2) := by rw [le_div_iff₀ hn1]; linarith
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hmN.1)
  have hb : b₀ = b := by
    by_contra hbb
    cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
    · exact hbb rfl
    · rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
        abs_of_nonneg (by linarith)] at hclose; linarith
    · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
        abs_of_nonneg (by linarith)] at hclose; linarith
    · exact hbb rfl
  subst b₀
  have hmn : m ≠ n := fun h => hne h rfl
  have hlog_close : |Real.log n - Real.log m| < 2 * r := by
    cases b <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
    · rwa [show -Real.log n - -Real.log m = -(Real.log n - Real.log m) by ring, abs_neg] at hclose
    · exact hclose
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hsep := two_div_le_log_sub_log_of_odd (show 1 ≤ m by omega) hmo hno hlt
      (show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)
    rw [abs_of_nonneg (by linarith [div_pos two_pos hn1])] at hlog_close
    linarith
  · obtain ⟨i, hi⟩ := hno
    obtain ⟨j, hj⟩ := hmo
    have hsucc2 : n + 2 ≤ m := by omega
    have hn2_odd : Odd (n + 2) := ⟨i + 1, by omega⟩
    have hsep1 := two_div_le_log_sub_log_of_odd (show 1 ≤ n by omega) ⟨i, hi⟩ hn2_odd
      (by omega : n < n + 2) (show ((n + 2 : ℕ) : ℝ) ≤ (n : ℝ) + 2 by push_cast; rfl)
    have hsep2 : Real.log ((n + 2 : ℕ) : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hsucc2)
    rw [abs_sub_comm, abs_of_nonneg (by linarith [div_pos two_pos hn1])] at hlog_close
    linarith

/-- **Half-density neighbour count for odd integers.** For an odd integer `n ≥ 1` and `r ≥ 0`, at
most `(n/2)(e^{2r} − e^{−2r})` odd integers `m ∈ [2, N]`, `m ≠ n`, satisfy
`|log n − log m| < 2r`. -/
theorem card_odd_close_log_le {N n : ℕ} {r : ℝ} (hr : 0 ≤ r) (hn : 1 ≤ n) (hno : Odd n) :
    (((Finset.Icc 2 N).filter fun m => Odd m ∧ m ≠ n ∧ |Real.log n - Real.log m| < 2 * r).card : ℝ) ≤
      (n : ℝ) / 2 * (Real.exp (2 * r) - Real.exp (-(2 * r))) := by
  obtain ⟨i, rfl⟩ := hno
  set k₀ : ℕ := i + 1 with hk₀
  set A : ℝ := (((2 * i + 1 : ℕ) : ℝ) * Real.exp (-(2 * r)) + 1) / 2 with hA
  set B : ℝ := (((2 * i + 1 : ℕ) : ℝ) * Real.exp (2 * r) + 1) / 2 with hB
  have hn0 : (0 : ℝ) < ((2 * i + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hk₀_real : (k₀ : ℝ) = (((2 * i + 1 : ℕ) : ℝ) + 1) / 2 := by
    rw [hk₀]; push_cast; ring
  have hAk₀ : A ≤ (k₀ : ℝ) := by
    rw [hA, hk₀_real]
    have hexp : Real.exp (-(2 * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith [mul_le_of_le_one_right hn0.le hexp]
  have hk₀B : (k₀ : ℝ) ≤ B := by
    rw [hB, hk₀_real]
    have hexp : 1 ≤ Real.exp (2 * r) := Real.one_le_exp (by linarith)
    linarith [le_mul_of_one_le_right hn0.le hexp]
  set S := (Finset.Icc 2 N).filter fun m => Odd m ∧ m ≠ 2 * i + 1 ∧
      |Real.log ((2 * i + 1 : ℕ) : ℝ) - Real.log m| < 2 * r
  have hinj : Set.InjOn (fun m : ℕ => (m + 1) / 2) (S : Set ℕ) := by
    intro m₁ hm₁ m₂ hm₂ heq
    change (m₁ + 1) / 2 = (m₂ + 1) / 2 at heq
    have ho₁ : Odd m₁ := (Finset.mem_filter.mp hm₁).2.1
    have ho₂ : Odd m₂ := (Finset.mem_filter.mp hm₂).2.1
    obtain ⟨j₁, rfl⟩ := ho₁
    obtain ⟨j₂, rfl⟩ := ho₂
    omega
  have hmaps : ∀ m ∈ S, (m + 1) / 2 ∈ (Finset.Icc ⌈A⌉₊ ⌊B⌋₊).erase k₀ := by
    intro m hm
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm2, -⟩, ⟨j, rfl⟩, hmn, hlog⟩ := hm
    have hm_div : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [hm_div]
    have hj_ne : j + 1 ≠ k₀ := fun h => hmn (by omega)
    have hm0 : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
    rw [abs_lt] at hlog
    have hup : ((2 * j + 1 : ℕ) : ℝ) < ((2 * i + 1 : ℕ) : ℝ) * Real.exp (2 * r) := by
      have h1 : Real.log ((2 * j + 1 : ℕ) : ℝ) < Real.log ((2 * i + 1 : ℕ) : ℝ) + 2 * r := by
        linarith [hlog.1]
      rw [← Real.exp_log hm0, ← Real.exp_log hn0, ← Real.exp_add]
      exact Real.exp_lt_exp.mpr h1
    have hlow : ((2 * i + 1 : ℕ) : ℝ) * Real.exp (-(2 * r)) < ((2 * j + 1 : ℕ) : ℝ) := by
      have h1 : Real.log ((2 * i + 1 : ℕ) : ℝ) + -(2 * r) < Real.log ((2 * j + 1 : ℕ) : ℝ) := by
        linarith [hlog.2]
      rw [← Real.exp_log hm0, ← Real.exp_log hn0, ← Real.exp_add]
      exact Real.exp_lt_exp.mpr h1
    have hj_real : ((j + 1 : ℕ) : ℝ) = (((2 * j + 1 : ℕ) : ℝ) + 1) / 2 := by push_cast; ring
    refine Finset.mem_erase.mpr ⟨hj_ne, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact Nat.ceil_le.mpr (by rw [hj_real, hA]; linarith)
    · exact Nat.le_floor (by rw [hj_real, hB]; linarith)
  have hk₀mem : k₀ ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊ :=
    Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hAk₀, Nat.le_floor hk₀B⟩
  have hcard := Finset.card_le_card_of_injOn (fun m => (m + 1) / 2) hmaps hinj
  rw [Finset.card_erase_of_mem hk₀mem, Nat.card_Icc] at hcard
  have hle : ⌈A⌉₊ ≤ ⌊B⌋₊ := le_trans (Nat.ceil_le.mpr hAk₀) (Nat.le_floor hk₀B)
  have hcast : ((⌊B⌋₊ + 1 - ⌈A⌉₊ - 1 : ℕ) : ℝ) = (⌊B⌋₊ : ℝ) - ⌈A⌉₊ := by
    rw [show ⌊B⌋₊ + 1 - ⌈A⌉₊ - 1 = ⌊B⌋₊ - ⌈A⌉₊ by omega, Nat.cast_sub hle]
  calc (S.card : ℝ) ≤ ((⌊B⌋₊ + 1 - ⌈A⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (⌊B⌋₊ : ℝ) - ⌈A⌉₊ := hcast
    _ ≤ B - A := by linarith [Nat.floor_le hB0, Nat.le_ceil A]
    _ = ((2 * i + 1 : ℕ) : ℝ) / 2 * (Real.exp (2 * r) - Real.exp (-(2 * r))) := by
        rw [hA, hB]; ring

/-- Per-index odd neighbour bound: `|(closeSet_odd (n, b))| ≤ (n/2)(e^{2r} − e^{−2r})`. -/
theorem card_odd_closeSet_primeFreq_le_self (N : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2)
    {n : ℕ} (hn2 : 2 ≤ n) (hno : Odd n) (b : Bool) :
    ((closeSet (((Finset.Icc 2 N).filter Odd) ×ˢ (Finset.univ : Finset Bool))
        primeFreq r (n, b)).card : ℝ) ≤
      (n : ℝ) / 2 * (Real.exp (2 * r) - Real.exp (-(2 * r))) := by
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  set s := ((Finset.Icc 2 N).filter Odd) ×ˢ (Finset.univ : Finset Bool)
  have hinj : Set.InjOn Prod.fst ((closeSet s primeFreq r (n, b) : Finset (ℕ × Bool)) : Set (ℕ × Bool)) := by
    rintro ⟨m, b₁⟩ hm ⟨m', b₂⟩ hm' hmm
    change m = m' at hmm
    simp only [s, closeSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
      Finset.mem_filter, Finset.mem_Icc, Finset.mem_univ, and_true] at hm hm'
    have hb : ∀ {m₀ : ℕ} {b₀ : Bool}, 2 ≤ m₀ → |primeFreq (n, b) - primeFreq (m₀, b₀)| < 2 * r →
        b₀ = b := by
      intro m₀ b₀ hm₀ hclose
      by_contra hne
      have hlm : Real.log 2 ≤ Real.log m₀ := Real.log_le_log (by norm_num) (by exact_mod_cast hm₀)
      cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
      · exact hne rfl
      · rw [show -Real.log n - Real.log m₀ = -(Real.log n + Real.log m₀) by ring, abs_neg,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · rw [show Real.log n - -Real.log m₀ = Real.log n + Real.log m₀ by ring,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · exact hne rfl
    rw [hb hm.1.1.1 hm.2.2, hb hm'.1.1.1 hm'.2.2, hmm]
  have hmaps : ∀ x ∈ closeSet s primeFreq r (n, b),
      x.1 ∈ (Finset.Icc 2 N).filter fun m => Odd m ∧ m ≠ n ∧ |Real.log n - Real.log m| < 2 * r := by
    rintro ⟨m, b₀⟩ hx
    simp only [s, closeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ,
      and_true, ne_eq, Prod.mk.injEq, not_and] at hx
    obtain ⟨⟨hmN, hmo⟩, hne, hclose⟩ := hx
    have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hmN.1)
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨hmN, hmo, ?_, ?_⟩
    · intro hmn
      cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
      · exact hne hmn rfl
      · rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · exact hne hmn rfl
    · cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
      · rwa [show -Real.log n - -Real.log m = -(Real.log n - Real.log m) by ring, abs_neg] at hclose
      · rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
          abs_of_nonneg (by linarith)] at hclose; linarith
      · exact hclose
  have hcard := Finset.card_le_card_of_injOn Prod.fst hmaps hinj
  exact (Nat.cast_le.mpr hcard).trans (card_odd_close_log_le hr (by omega) hno)

/-- **Half-density degree-weight cancellation on the odd sector.** -/
theorem sum_card_odd_closeSet_primeFreq_mul_norm_sq_le (f : ℝ → ℂ) (N : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr2 : 2 * r ≤ Real.log 2) (ξ₀ : ℝ) :
    ∑ j ∈ ((Finset.Icc 2 N).filter Odd) ×ˢ (Finset.univ : Finset Bool),
        ((closeSet (((Finset.Icc 2 N).filter Odd) ×ˢ (Finset.univ : Finset Bool))
            primeFreq r j).card : ℝ) *
          ‖primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)‖ ^ 2 ≤
      (Real.exp (2 * r) - Real.exp (-(2 * r))) / 2 *
        ∑ n ∈ (Finset.Icc 2 N).filter Odd,
          if 1 < r * ((n : ℝ) + 2) then
            (ArithmeticFunction.vonMangoldt n) ^ 2 *
              (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)
          else 0 := by
  have hr2' : r ≤ Real.log 2 := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  set s := ((Finset.Icc 2 N).filter Odd) ×ˢ (Finset.univ : Finset Bool)
  rw [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hnI, hno⟩ := Finset.mem_filter.mp hn
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hnI).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Fintype.sum_bool]
  have hnorm (b : Bool) : ‖primeCoeff f (n, b) * cexp (2 * π * I * ξ₀ * primeFreq (n, b))‖ ^ 2 =
      (ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) * ‖EF.weilTest f f (primeFreq (n, b))‖ ^ 2 := by
    simp only [primeCoeff, norm_mul, norm_cexp_two_pi_I_mul, mul_one, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, div_pow, Real.sq_sqrt hn0.le]
  rw [hnorm true, hnorm false]
  split_ifs with htrans
  · have h1 := card_odd_closeSet_primeFreq_le_self N hr hr2' hn2 hno true
    have h2 := card_odd_closeSet_primeFreq_le_self N hr hr2' hn2 hno false
    have hpos1 : 0 ≤ (ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
        ‖EF.weilTest f f (primeFreq (n, true))‖ ^ 2 := by positivity
    have hpos2 : 0 ≤ (ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
        ‖EF.weilTest f f (primeFreq (n, false))‖ ^ 2 := by positivity
    calc ((closeSet s primeFreq r (n, true)).card : ℝ) *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
              ‖EF.weilTest f f (primeFreq (n, true))‖ ^ 2) +
          ((closeSet s primeFreq r (n, false)).card : ℝ) *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
              ‖EF.weilTest f f (primeFreq (n, false))‖ ^ 2)
        ≤ (n : ℝ) / 2 * (Real.exp (2 * r) - Real.exp (-(2 * r))) *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
              ‖EF.weilTest f f (Real.log n)‖ ^ 2) +
          (n : ℝ) / 2 * (Real.exp (2 * r) - Real.exp (-(2 * r))) *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 / (n : ℝ) *
              ‖EF.weilTest f f (-Real.log n)‖ ^ 2) := by
          exact add_le_add (mul_le_mul_of_nonneg_right h1 hpos1)
            (mul_le_mul_of_nonneg_right h2 hpos2)
      _ = (Real.exp (2 * r) - Real.exp (-(2 * r))) / 2 *
            ((ArithmeticFunction.vonMangoldt n) ^ 2 *
              (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)) := by
          have hne : (n : ℝ) ≠ 0 := hn0.ne'
          field_simp
  · have hle : r * ((n : ℝ) + 2) ≤ 1 := not_lt.mp htrans
    rw [odd_closeSet_primeFreq_eq_empty_of_le N hr2 hn2 hno hle true,
      odd_closeSet_primeFreq_eq_empty_of_le N hr2 hn2 hno hle false]
    simp

theorem sum_norm_sq_oddPrimeCoeff_shift_eq (f : ℝ → ℂ) (N : ℕ) (ξ₀ : ℝ) :
    ∑ j ∈ ((Finset.Icc 2 N).filter Odd) ×ˢ (Finset.univ : Finset Bool),
        ‖primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)‖ ^ 2 = oddPrimeVariance f N := by
  rw [oddPrimeVariance, Finset.sum_product]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Fintype.sum_bool]
  simp only [primeCoeff, primeFreq, ↓reduceIte, Bool.false_eq_true, norm_mul,
    norm_cexp_two_pi_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    div_pow, Real.sq_sqrt hn0]
  ring

/-- **Odd-sector trans-threshold Chebyshev variance bound.** -/
theorem integral_normSq_mul_normSq_oddPrimePolynomial_le_transThreshold_chebyshev {r : ℝ}
    {f η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hr : 0 ≤ r) (hr2 : 2 * r ≤ Real.log 2)
    (hηs : tsupport η ⊆ Icc (-r) r) (N : ℕ) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖oddPrimePolynomial f N (ξ + ξ₀)‖ ^ 2 ≤
      (∫ t, ‖η t‖ ^ 2) *
        (oddPrimeVariance f N +
          (Real.exp (2 * r) - Real.exp (-(2 * r))) / 2 *
            ∑ n ∈ (Finset.Icc 2 N).filter Odd,
              if 1 < r * ((n : ℝ) + 2) then
                (ArithmeticFunction.vonMangoldt n) ^ 2 *
                  (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)
              else 0) := by
  simp_rw [oddPrimePolynomial, expSum_add]
  set s := ((Finset.Icc 2 N).filter Odd) ×ˢ (Finset.univ : Finset Bool)
  have h1 := integral_normSq_mul_normSq_expSum_le_sum_card hη hηs s
    (fun j => primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)) primeFreq
  have hsplit : ∑ j ∈ s, (1 + ((closeSet s primeFreq r j).card : ℝ)) *
        ‖primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)‖ ^ 2 =
      oddPrimeVariance f N +
        ∑ j ∈ s, ((closeSet s primeFreq r j).card : ℝ) *
          ‖primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)‖ ^ 2 := by
    rw [← sum_norm_sq_oddPrimeCoeff_shift_eq f N ξ₀, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit] at h1
  have hN0 : 0 ≤ ∫ t, ‖η t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsum := sum_card_odd_closeSet_primeFreq_mul_norm_sq_le f N hr hr2 ξ₀
  exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) hN0)

/-- **Parity-split trans-threshold Chebyshev variance law for `ζ`.** Combines global exact
diagonalization of the even sector `Π_f^even` with half-density degree cancellation on the odd
sector `Π_f^odd`: only odd integers `n > 1/r − 2` enter the trans-threshold off-diagonal. -/
theorem integral_windowed_sq_deviation_parity_chebyshev_le {a r : ℝ} {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hη : ContDiff ℝ 2 η)
    (hr : 0 ≤ r) (hr2 : 2 * r ≤ Real.log 2) (hηs : tsupport η ⊆ Icc (-r) r) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
          archPart f (ξ + ξ₀)‖ ^ 2 ≤
      2 * (∫ t, ‖η t‖ ^ 2) *
        (primeVariance f ⌊Real.exp (2 * a)⌋₊ +
          (Real.exp (2 * r) - Real.exp (-(2 * r))) / 2 *
            ∑ n ∈ (Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊).filter Odd,
              if 1 < r * ((n : ℝ) + 2) then
                (ArithmeticFunction.vonMangoldt n) ^ 2 *
                  (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)
              else 0) := by
  have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
      archPart f (ξ + ξ₀)‖ = ‖primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)‖ := fun ξ => by
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
  simp_rw [hdev]
  refine (integral_normSq_mul_normSq_primePolynomial_le_two_mul_odd_add_even hη hηs _ ξ₀).trans ?_
  have hodd := integral_normSq_mul_normSq_oddPrimePolynomial_le_transThreshold_chebyshev
    (f := f) hη hr hr2 hηs ⌊Real.exp (2 * a)⌋₊ ξ₀
  have heven := integral_normSq_mul_normSq_evenPrimePolynomial_eq
    (f := f) hη hηs hr2 ⌊Real.exp (2 * a)⌋₊ ξ₀
  rw [heven, primeVariance_eq_odd_add_even]
  linarith

end GaloisForLFunctions.SquareRootThreshold
