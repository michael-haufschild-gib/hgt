import GaloisForLFunctions.SquareRootThreshold.WindowedOffDiagonalBeyondThreshold

/-!
# Product moments are diagonal below the threshold, for every product order

Let `D(ξ) = Σ_{n ∈ s} c_n e^{2πiξ log n}` with `s ⊆ [1, X]`, and let `η ∈ C²` be a window supported
in `[−r, r]`. The `k`-th power of `D` is again an integer-frequency polynomial,
`D^k = Σ_N c^{*k}(N) e^{2πiξ log N}` with `c^{*k}(N) = Σ_{n_1 ⋯ n_k = N} Π_i c_{n_i}` supported on
`N ≤ X^k` (`expSum_pow_eq_powSum`). So the windowed `2k`-th moment `∫ |ĥ_η|² |D|^{2k}` is the
windowed mean square of a polynomial of length `X^k`.

* **Below the threshold** (`integral_pairTransform_mul_normSq_pow_eq_diag`). If `2rX^k ≤ 1`, distinct
  products are `2r`-separated in logarithm, so the windowed `2k`-th moment is exactly its
  multiplicative diagonal `‖η‖² Σ_N |c^{*k}(N)|²`. The only coincidences it sees are equalities
  `n_1 ⋯ n_k = m_1 ⋯ m_k`: unique factorization.
* **Beyond the threshold** (`integral_normSq_pow_eq_diag_add_offDiag_nonneg`). For real nonnegative
  coefficients and a real nonnegative window, the windowed `2k`-th moment is the diagonal plus a
  nonnegative off-diagonal over near-coincident products. Size information alone cannot do better.

The free region of a product of order `k` therefore ends at total length `X^k = 1/(2r)`, the
square-root threshold, for every `k`. This is the moment form of the tensor-power trick over the
archimedean family `t ↦ D(σ + it)`: the base cost is the length of the window, and below the
threshold the moments carry only unique factorization.
-/

open MeasureTheory Complex Set
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticKunnethTheory

open Zeta23 SquareRootThreshold _root_.RHTower _root_.RHTower.WeilRegular

/-- The integers `n_1 ⋯ n_k` with every `n_i ∈ s`. -/
def powSupport (s : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Fintype.piFinset fun _ : Fin k => s).image fun t => ∏ i, t i

/-- The coefficient `c^{*k}(N) = Σ_{n_1 ⋯ n_k = N, n_i ∈ s} Π_i c_{n_i}` of `D^k`. -/
def powCoeff (s : Finset ℕ) (c : ℕ → ℂ) (k N : ℕ) : ℂ :=
  ∑ t ∈ (Fintype.piFinset fun _ : Fin k => s).filter (fun t => ∏ i, t i = N), ∏ i, c (t i)

/-- The logarithmic frequency `log n` of an integer. -/
def logFreq (n : ℕ) : ℝ := Real.log n

/-- **The `k`-th power of an integer-frequency polynomial** is the integer-frequency polynomial with
coefficients `c^{*k}` on the products `n_1 ⋯ n_k`. -/
theorem expSum_pow_eq_powSum {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (c : ℕ → ℂ) (k : ℕ) (ξ : ℝ) :
    expSum s c logFreq ξ ^ k = expSum (powSupport s k) (powCoeff s c k) logFreq ξ := by
  have hprod : ∀ t ∈ Fintype.piFinset (fun _ : Fin k => s),
      ∏ i, (c (t i) * cexp (2 * π * I * ξ * logFreq (t i))) =
        (∏ i, c (t i)) * cexp (2 * π * I * ξ * logFreq (∏ i, t i)) := by
    intro t ht
    rw [Fintype.mem_piFinset] at ht
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 2
    have hne : ∀ i ∈ (Finset.univ : Finset (Fin k)), ((t i : ℕ) : ℝ) ≠ 0 := fun i _ =>
      Nat.cast_ne_zero.mpr (by have := hs _ (ht i); omega)
    rw [logFreq, Nat.cast_prod, Real.log_prod hne, Complex.ofReal_sum, Finset.mul_sum]
    rfl
  rw [expSum, ← Fin.prod_const, Finset.prod_univ_sum, Finset.sum_congr rfl hprod, expSum]
  rw [← Finset.sum_fiberwise_of_maps_to (t := powSupport s k) (g := fun t => ∏ i, t i)
    (fun t ht => Finset.mem_image.mpr ⟨t, ht, rfl⟩)]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [powCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_filter.mp ht).2]

/-- Products of members of `s ⊆ [1, X]` lie in `[1, X^k]`. -/
theorem mem_powSupport_bounds {s : Finset ℕ} {X : ℕ} (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ X) {k N : ℕ}
    (hN : N ∈ powSupport s k) : 1 ≤ N ∧ N ≤ X ^ k := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hN
  rw [Fintype.mem_piFinset] at ht
  refine ⟨Finset.one_le_prod' fun i _ => (hs _ (ht i)).1, ?_⟩
  rw [← Fin.prod_const]
  exact Finset.prod_le_prod' fun i _ => (hs _ (ht i)).2

/-- Distinct integers in `[1, Y]` are `1/Y`-separated in logarithm. -/
theorem inv_le_abs_logFreq_sub {M N Y : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hMY : M ≤ Y) (hNY : N ≤ Y)
    (hne : M ≠ N) : ((Y : ℝ))⁻¹ ≤ |logFreq N - logFreq M| := by
  wlog hlt : M < N generalizing M N
  · rw [abs_sub_comm]
    exact this hN hM hNY hMY hne.symm (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hYN : (N : ℝ) ≤ Y := by exact_mod_cast hNY
  have hlog : 1 - ((N : ℝ) / M)⁻¹ ≤ Real.log ((N : ℝ) / M) :=
    Real.one_sub_inv_le_log_of_pos (div_pos hNpos hMpos)
  rw [inv_div, Real.log_div hNpos.ne' hMpos.ne'] at hlog
  have hgap : ((N : ℝ))⁻¹ ≤ 1 - (M : ℝ) / N := by
    rw [le_sub_iff_add_le, inv_eq_one_div, ← add_div, div_le_one hNpos]
    have : (M : ℝ) + 1 ≤ N := by exact_mod_cast hlt
    linarith
  calc ((Y : ℝ))⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hNpos hYN
    _ ≤ Real.log N - Real.log M := hgap.trans hlog
    _ ≤ |logFreq N - logFreq M| := le_abs_self _

/-- **Below the threshold every product moment is diagonal.** If `s ⊆ [1, X]` and the window is
supported in `[−r, r]` with `2rX^k ≤ 1`, the windowed `2k`-th moment of `D` is exactly
`‖η‖² Σ_N |c^{*k}(N)|²`, the multiplicative diagonal of `D^k`. -/
theorem integral_pairTransform_mul_normSq_pow_eq_diag {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) {s : Finset ℕ} {X : ℕ} (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ X)
    (c : ℕ → ℂ) {k : ℕ} (hthr : 2 * r * ((X : ℝ) ^ k) ≤ 1) :
    ∫ ξ : ℝ, pairTransform η ξ * (expSum s c logFreq ξ * conj (expSum s c logFreq ξ)) ^ k =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) *
        ∑ N ∈ powSupport s k, ((‖powCoeff s c k N‖ ^ 2 : ℝ) : ℂ) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hs1 : ∀ n ∈ s, 1 ≤ n := fun n hn => (hs n hn).1
  have hpow : ∀ ξ : ℝ, (expSum s c logFreq ξ * conj (expSum s c logFreq ξ)) ^ k =
      expSum (powSupport s k) (powCoeff s c k) logFreq ξ *
        conj (expSum (powSupport s k) (powCoeff s c k) logFreq ξ) := by
    intro ξ
    rw [mul_pow, ← map_pow, expSum_pow_eq_powSum hs1]
  simp_rw [hpow]
  rw [integral_pairTransform_mul_normSq_expSum_eq_diag_add hη hηc, add_eq_left]
  refine Finset.sum_eq_zero fun N hN => Finset.sum_eq_zero fun M hM => ?_
  obtain ⟨hMne, hM⟩ := Finset.mem_erase.mp hM
  have hNb := mem_powSupport_bounds hs hN
  have hMb := mem_powSupport_bounds hs hM
  have hXk : (0 : ℝ) < (X : ℝ) ^ k := by
    have : (0 : ℝ) < ((X ^ k : ℕ) : ℝ) := by exact_mod_cast (hMb.1.trans hMb.2)
    rwa [Nat.cast_pow] at this
  have hsep := inv_le_abs_logFreq_sub hMb.1 hNb.1 hMb.2 hNb.2 hMne
  have h2r : 2 * r ≤ |logFreq N - logFreq M| := by
    refine le_trans ?_ hsep
    rw [Nat.cast_pow, ← one_div]
    exact (le_div_iff₀ hXk).mpr hthr
  rw [weilTest_self_eq_zero_of_le hη hηs h2r, mul_zero]

/-- The real coefficient `c^{*k}(N)` for real data. -/
def powCoeffReal (s : Finset ℕ) (c : ℕ → ℝ) (k N : ℕ) : ℝ :=
  ∑ t ∈ (Fintype.piFinset fun _ : Fin k => s).filter (fun t => ∏ i, t i = N), ∏ i, c (t i)

theorem powCoeff_ofReal (s : Finset ℕ) (c : ℕ → ℝ) (k N : ℕ) :
    powCoeff s (fun n => (c n : ℂ)) k N = (powCoeffReal s c k N : ℂ) := by
  simp only [powCoeff, powCoeffReal, Complex.ofReal_sum, Complex.ofReal_prod]

theorem powCoeffReal_nonneg {s : Finset ℕ} {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (k N : ℕ) :
    0 ≤ powCoeffReal s c k N :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => hc _

/-- **Beyond the threshold the size bound is the truth for every product order.** For real
nonnegative coefficients and a real nonnegative window, the windowed `2k`-th moment of `D` is the
multiplicative diagonal of `D^k` plus a nonnegative sum over near-coincident products. -/
theorem integral_normSq_pow_eq_diag_add_offDiag_nonneg {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 (fun u => (w u : ℂ))) (hwc : HasCompactSupport (fun u => (w u : ℂ)))
    (hw0 : ∀ u, 0 ≤ w u) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n)
    (k : ℕ) :
    (∫ t, ‖(w t : ℂ)‖ ^ 2) * ∑ N ∈ powSupport s k, powCoeffReal s c k N ^ 2 +
        ∑ N ∈ powSupport s k, ∑ M ∈ (powSupport s k).erase N,
          powCoeffReal s c k N * powCoeffReal s c k M *
            ∫ t, w t * w (t - (logFreq N - logFreq M)) =
      ∫ ξ : ℝ, ‖paperFT (fun u => (w u : ℂ)) (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖expSum s (fun n => (c n : ℂ)) logFreq ξ‖ ^ (2 * k) ∧
    0 ≤ ∑ N ∈ powSupport s k, ∑ M ∈ (powSupport s k).erase N,
          powCoeffReal s c k N * powCoeffReal s c k M *
            ∫ t, w t * w (t - (logFreq N - logFreq M)) := by
  obtain ⟨hid, hoff⟩ := le_integral_normSq_mul_normSq_expSum_of_nonneg hw hwc hw0
    (powSupport s k) (powCoeffReal s c k) (powCoeffReal_nonneg hc k) logFreq
  refine ⟨?_, hoff⟩
  rw [hid]
  congr 1
  ext ξ
  congr 1
  rw [show ‖expSum s (fun n => (c n : ℂ)) logFreq ξ‖ ^ (2 * k) =
      ‖expSum s (fun n => (c n : ℂ)) logFreq ξ ^ k‖ ^ 2 by rw [norm_pow, ← pow_mul, mul_comm],
    expSum_pow_eq_powSum hs, show powCoeff s (fun n => (c n : ℂ)) k =
      fun N => ((powCoeffReal s c k N : ℝ) : ℂ) from funext (powCoeff_ofReal s c k)]

end GaloisForLFunctions.ArithmeticKunnethTheory
