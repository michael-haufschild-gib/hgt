import GaloisForLFunctions.SquareRootThreshold.ZetaLocalizedFormWindowedVarianceLaw

/-!
# Beyond the square-root threshold: the off-diagonal of windowed mean squares

For a window `η` supported in `[-r, r]` and `Q(ξ) = Σ_j c_j e^{2πiξν_j}`, the windowed Gram identity
splits exactly into a diagonal and an off-diagonal part
(`integral_pairTransform_mul_normSq_expSum_eq_diag_add`):

`∫ |h_η(−2πξ)|² |Q(ξ)|² dξ = ‖η‖² Σ_j |c_j|² + Σ_{j ≠ k} c_j c̄_k k_η(ν_j − ν_k)`.

Only pairs with `|ν_j − ν_k| < 2r` enter the off-diagonal.

* **Size bound at every length** (`integral_normSq_mul_normSq_expSum_le`). If every frequency has
  at most `M` neighbours within `2r`, then the windowed mean square is at most
  `‖η‖² (1 + M) Σ_j |c_j|²`. For logarithms of integers up to `X`, `M ≤ X(e^{2r} − e^{−2r})`
  (`card_close_log_le`). This is the mean value theorem `T + O(X)` in windowed form.
* **The size bound is the true size for aligned phases**
  (`le_integral_normSq_mul_normSq_expSum_of_nonneg`). For real nonnegative coefficients and a
  real nonnegative window, every off-diagonal term is nonnegative. So any argument that uses only
  the sizes `|c_j|` cannot do better than the bound above.
* **For `ζ`** (`integral_windowed_sq_deviation_le`). At every prime length `X = e^{2a}` and every
  window of aperture `r ≤ log 2`, the windowed mean square of the deviation `W_ζ − A_f` is at most
  `‖η‖² V_f (1 + X(e^{2r} − e^{−2r}))`. The excess over the exact diagonal of
  `integral_windowed_sq_deviation_eq` is the sum over prime-power pairs `n ≠ m` with
  `|log(m/n)| < 2r`.
* **Height averages** (`integral_pairTransform_mul_integral_windowed_eq`). Averaging the windowed
  mean square over heights with a second window `ω` multiplies each pair by `k_ω(ν_j − ν_k)`. With
  `ω` of aperture `ρ`, only pairs with `|log(m/n)| < 2 min(r, ρ)` survive. Beyond the threshold, the
  height-averaged variance is therefore exactly the diagonal plus a weighted correlation of prime
  pairs `(n, n + h)` with `h ≲ 2ρn`.

Controlling that correlation sum asymptotically is a statement about pairs of primes at
multiplicative distance `< 2ρ`. Through the explicit formula it is equivalent to the pair
correlation of zeros at `α = log X/log T > 1`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-! ### Diagonal and off-diagonal -/

/-- **Exact diagonal/off-diagonal split of the windowed Gram identity.** -/
theorem integral_pairTransform_mul_normSq_expSum_eq_diag_add {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (ν : ι → ℝ) :
    ∫ ξ : ℝ, pairTransform η ξ * (expSum s c ν ξ * conj (expSum s c ν ξ)) =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ∑ j ∈ s, ((‖c j‖ ^ 2 : ℝ) : ℂ) +
        ∑ j ∈ s, ∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (ν j - ν k) := by
  rw [integral_pairTransform_mul_normSq_expSum hη hηc, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.add_sum_erase s _ hj, sub_self, weilTest_self_zero, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- The close neighbours of `j`: the indices `k ≠ j` with `|ν_j − ν_k| < 2r`. -/
def closeSet {ι : Type*} [DecidableEq ι] (s : Finset ι) (ν : ι → ℝ) (r : ℝ) (j : ι) :
    Finset ι :=
  s.filter fun k => k ≠ j ∧ |ν j - ν k| < 2 * r

theorem mem_closeSet_comm {ι : Type*} [DecidableEq ι] {s : Finset ι} {ν : ι → ℝ} {r : ℝ}
    {j k : ι} (hj : j ∈ s) (hk : k ∈ s) : k ∈ closeSet s ν r j ↔ j ∈ closeSet s ν r k := by
  simp only [closeSet, Finset.mem_filter, hj, hk, true_and]
  rw [abs_sub_comm]
  exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

/-- **The off-diagonal energy.** If every index has at most `M` close neighbours, then
`Σ_j Σ_{k close to j} |c_j| |c_k| ≤ M Σ_j |c_j|²`. -/
theorem sum_closeSet_norm_mul_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (ν : ι → ℝ) {r M : ℝ} (hM : ∀ j ∈ s, ((closeSet s ν r j).card : ℝ) ≤ M) :
    ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ * ‖c k‖ ≤ M * ∑ j ∈ s, ‖c j‖ ^ 2 := by
  have hamgm : ∀ j k, ‖c j‖ * ‖c k‖ ≤ (‖c j‖ ^ 2 + ‖c k‖ ^ 2) / 2 := fun j k => by
    nlinarith [two_mul_le_add_sq ‖c j‖ ‖c k‖]
  have hswap : ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c k‖ ^ 2 =
      ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ ^ 2 := by
    have h1 : ∀ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c k‖ ^ 2 =
        ∑ k ∈ s, if k ∈ closeSet s ν r j then ‖c k‖ ^ 2 else 0 := by
      intro j _
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp only [closeSet, Finset.mem_filter]
      tauto
    have h2 : ∀ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ ^ 2 =
        ∑ k ∈ s, if j ∈ closeSet s ν r k then ‖c j‖ ^ 2 else 0 := by
      intro j hj
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [Finset.mem_filter]
      constructor
      · intro hk
        have hks : k ∈ s := (Finset.mem_filter.mp hk).1
        exact ⟨hks, (mem_closeSet_comm hj hks).mp hk⟩
      · rintro ⟨hks, hk⟩
        exact (mem_closeSet_comm hj hks).mpr hk
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  calc ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ * ‖c k‖
      ≤ ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, (‖c j‖ ^ 2 + ‖c k‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hamgm j k
    _ = (∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c j‖ ^ 2 +
          ∑ j ∈ s, ∑ k ∈ closeSet s ν r j, ‖c k‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ j ∈ s, ((closeSet s ν r j).card : ℝ) * ‖c j‖ ^ 2 := by
        rw [hswap, add_self_div_two]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ s, M * ‖c j‖ ^ 2 :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hM j hj) (sq_nonneg _)
    _ = M * ∑ j ∈ s, ‖c j‖ ^ 2 := by rw [Finset.mul_sum]

/-- **Size of the off-diagonal.** For a window supported in `[-r, r]`, the off-diagonal part is
at most `‖η‖² M Σ_j |c_j|²`. -/
theorem norm_offDiag_le {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (ν : ι → ℝ) {M : ℝ} (hM : ∀ j ∈ s, ((closeSet s ν r j).card : ℝ) ≤ M) :
    ‖∑ j ∈ s, ∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (ν j - ν k)‖ ≤
      (∫ t, ‖η t‖ ^ 2) * (M * ∑ j ∈ s, ‖c j‖ ^ 2) := by
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
    _ ≤ (∫ t, ‖η t‖ ^ 2) * (M * ∑ j ∈ s, ‖c j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_closeSet_norm_mul_le s c ν hM) hN0

/-- The windowed mean square, real form of the split. -/
theorem integral_normSq_mul_normSq_expSum_eq_diag_add {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (ν : ι → ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖expSum s c ν ξ‖ ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * ∑ j ∈ s, ‖c j‖ ^ 2 +
        (∑ j ∈ s, ∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (ν j - ν k)).re := by
  have h := integral_pairTransform_mul_normSq_expSum_eq_diag_add hη hηc s c ν
  have hfun : (fun ξ : ℝ => pairTransform η ξ * (expSum s c ν ξ * conj (expSum s c ν ξ))) =
      fun ξ : ℝ => ((‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖expSum s c ν ξ‖ ^ 2 : ℝ) : ℂ) := by
    funext ξ
    rw [pairTransform_ofReal hη hηc ξ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hfun, integral_complex_ofReal] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.add_re] at hre
  rw [hre]
  congr 1
  simp only [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **The windowed mean value bound at every length.** If every frequency has at most `M`
neighbours within `2r`, then `∫ |h_η(−2πξ)|² |Q(ξ)|² dξ ≤ ‖η‖² (1 + M) Σ_j |c_j|²`. -/
theorem integral_normSq_mul_normSq_expSum_le {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (ν : ι → ℝ) {M : ℝ} (hM : ∀ j ∈ s, ((closeSet s ν r j).card : ℝ) ≤ M) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖expSum s c ν ξ‖ ^ 2 ≤
      (∫ t, ‖η t‖ ^ 2) * (1 + M) * ∑ j ∈ s, ‖c j‖ ^ 2 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  rw [integral_normSq_mul_normSq_expSum_eq_diag_add hη hηc]
  have hoff := (Complex.re_le_norm _).trans (norm_offDiag_le hη hηs s c ν hM)
  linarith

/-- Logarithms of integers in `[2, N]` close to `log n`: at most `n(e^{2r} − e^{−2r})` of them. -/
theorem card_close_log_le {N n : ℕ} {r : ℝ} (hr : 0 ≤ r) (hn : 1 ≤ n) :
    (((Finset.Icc 2 N).filter fun m => m ≠ n ∧ |Real.log n - Real.log m| < 2 * r).card : ℝ) ≤
      n * (Real.exp (2 * r) - Real.exp (-(2 * r))) := by
  set A : ℝ := n * Real.exp (-(2 * r)) with hA
  set B : ℝ := n * Real.exp (2 * r) with hB
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hA0 : 0 ≤ A := by positivity
  have hAn : A ≤ n := by
    rw [hA]
    exact mul_le_of_le_one_right hn0.le (Real.exp_le_one_iff.mpr (by linarith))
  have hnB : (n : ℝ) ≤ B := by
    rw [hB]
    exact le_mul_of_one_le_right hn0.le (Real.one_le_exp (by linarith))
  have hsub : (Finset.Icc 2 N).filter (fun m => m ≠ n ∧ |Real.log n - Real.log m| < 2 * r) ⊆
      (Finset.Icc ⌈A⌉₊ ⌊B⌋₊).erase n := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm2, -⟩, hmn, hlog⟩ := hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [abs_lt] at hlog
    have hup : (m : ℝ) < B := by
      have : Real.log m < Real.log n + 2 * r := by linarith
      rw [hB, ← Real.exp_log hm0, ← Real.exp_log hn0, ← Real.exp_add]
      exact Real.exp_lt_exp.mpr this
    have hlow : A < m := by
      have : Real.log n - 2 * r < Real.log m := by linarith
      rw [hA, ← Real.exp_log hm0, ← Real.exp_log hn0, ← Real.exp_add]
      exact Real.exp_lt_exp.mpr (by linarith)
    refine Finset.mem_erase.mpr ⟨hmn, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact Nat.ceil_le.mpr hlow.le
    · exact Nat.le_floor hup.le
  have hnmem : n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊ :=
    Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hAn, Nat.le_floor hnB⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hnmem, Nat.card_Icc] at hcard
  have hle : ⌈A⌉₊ ≤ ⌊B⌋₊ := le_trans (Nat.ceil_le.mpr hAn) (Nat.le_floor hnB)
  have hcast : ((⌊B⌋₊ + 1 - ⌈A⌉₊ - 1 : ℕ) : ℝ) = (⌊B⌋₊ : ℝ) - ⌈A⌉₊ := by
    rw [show ⌊B⌋₊ + 1 - ⌈A⌉₊ - 1 = ⌊B⌋₊ - ⌈A⌉₊ by omega, Nat.cast_sub hle]
  have h1 : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (by positivity)
  have h2 : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  calc (((Finset.Icc 2 N).filter fun m => m ≠ n ∧ |Real.log n - Real.log m| < 2 * r).card : ℝ)
      ≤ ((⌊B⌋₊ + 1 - ⌈A⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (⌊B⌋₊ : ℝ) - ⌈A⌉₊ := hcast
    _ ≤ B - A := by linarith
    _ = n * (Real.exp (2 * r) - Real.exp (-(2 * r))) := by rw [hA, hB]; ring

/-! ### The windowed variance of `ζ` beyond the threshold -/

/-- The prime-index neighbours of `(n, b)`: only same-sign indices can be close when `r ≤ log 2`. -/
theorem card_closeSet_primeFreq_le {N : ℕ} {X r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2)
    (hNX : (N : ℝ) ≤ X) {j : ℕ × Bool} (hj : j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool)) :
    ((closeSet (Finset.Icc 2 N ×ˢ Finset.univ) primeFreq r j).card : ℝ) ≤
      X * (Real.exp (2 * r) - Real.exp (-(2 * r))) := by
  obtain ⟨n, b⟩ := j
  simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true] at hj
  have hn1 : 1 ≤ n := by omega
  have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hj.1)
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
      have hlm : Real.log 2 ≤ Real.log m₀ :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hm₀)
      cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
      · exact hne rfl
      · rw [show -Real.log n - Real.log m₀ = -(Real.log n + Real.log m₀) by ring, abs_neg,
          abs_of_nonneg (by linarith)] at hclose
        linarith
      · rw [show Real.log n - -Real.log m₀ = Real.log n + Real.log m₀ by ring,
          abs_of_nonneg (by linarith)] at hclose
        linarith
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
          abs_of_nonneg (by linarith)] at hclose
        linarith
      · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
          abs_of_nonneg (by linarith)] at hclose
        linarith
      · exact hne hmn rfl
    · cases b <;> cases b₀ <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true] at hclose
      · rw [show -Real.log n - -Real.log m = -(Real.log n - Real.log m) by ring, abs_neg] at hclose
        exact hclose
      · rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
          abs_of_nonneg (by linarith)] at hclose
        linarith
      · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
          abs_of_nonneg (by linarith)] at hclose
        linarith
      · exact hclose
  have hcard := Finset.card_le_card_of_injOn Prod.fst hmaps hinj
  have hX0 : 0 ≤ Real.exp (2 * r) - Real.exp (-(2 * r)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hnX : (n : ℝ) ≤ X := le_trans (by exact_mod_cast hj.2) hNX
  calc ((closeSet (Finset.Icc 2 N ×ˢ Finset.univ) primeFreq r (n, b)).card : ℝ)
      ≤ (((Finset.Icc 2 N).filter fun m => m ≠ n ∧ |Real.log n - Real.log m| < 2 * r).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ n * (Real.exp (2 * r) - Real.exp (-(2 * r))) := card_close_log_le hr hn1
    _ ≤ X * (Real.exp (2 * r) - Real.exp (-(2 * r))) := mul_le_mul_of_nonneg_right hnX hX0

theorem sum_norm_sq_primeCoeff_shift_eq (f : ℝ → ℂ) (N : ℕ) (ξ₀ : ℝ) :
    ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool),
        ‖primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)‖ ^ 2 = primeVariance f N := by
  rw [primeVariance, Finset.sum_product]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Fintype.sum_bool]
  simp only [primeCoeff, primeFreq, ↓reduceIte, Bool.false_eq_true, norm_mul,
    norm_cexp_two_pi_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    div_pow, Real.sq_sqrt hn0]
  ring

/-- **The windowed variance of `ζ` at every prime length.** For a window supported in `[-r, r]`
with `r ≤ log 2` and a profile of aperture `a`, `X = e^{2a}`:
`∫ |h_η(−2πξ)|² |W_ζ(S_{ξ+ξ₀} f) − A_f(ξ + ξ₀)|² dξ ≤ ‖η‖² V_f (1 + X(e^{2r} − e^{−2r}))`. -/
theorem integral_windowed_sq_deviation_le {a r : ℝ} {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hη : ContDiff ℝ 2 η) (hr : 0 ≤ r) (hr2 : r ≤ Real.log 2)
    (hηs : tsupport η ⊆ Icc (-r) r) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
          archPart f (ξ + ξ₀)‖ ^ 2 ≤
      (∫ t, ‖η t‖ ^ 2) * (1 + Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r)))) *
        primeVariance f ⌊Real.exp (2 * a)⌋₊ := by
  classical
  have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
      archPart f (ξ + ξ₀)‖ = ‖primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)‖ := by
    intro ξ
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
  simp_rw [hdev, primePolynomial, expSum_add]
  have hNX : ((⌊Real.exp (2 * a)⌋₊ : ℕ) : ℝ) ≤ Real.exp (2 * a) :=
    Nat.floor_le (Real.exp_pos _).le
  have hM := fun j hj => card_closeSet_primeFreq_le (j := j) hr hr2 hNX hj
  have h := integral_normSq_mul_normSq_expSum_le hη hηs _
    (fun j => primeCoeff f j * cexp (2 * π * I * ξ₀ * primeFreq j)) primeFreq
    (M := Real.exp (2 * a) * (Real.exp (2 * r) - Real.exp (-(2 * r))))
    (fun j hj => hM j hj)
  rw [sum_norm_sq_primeCoeff_shift_eq] at h
  exact h

/-! ### Nonnegative data: the size bound is attained -/

/-- For a real nonnegative window, the Weil kernel is real and nonnegative. -/
theorem weilTest_ofReal_nonneg {w : ℝ → ℝ} (hw : ∀ u, 0 ≤ w u) (v : ℝ) :
    EF.weilTest (fun u => (w u : ℂ)) (fun u => (w u : ℂ)) v =
      ((∫ t, w t * w (t - v) : ℝ) : ℂ) ∧ 0 ≤ ∫ t, w t * w (t - v) := by
  refine ⟨?_, integral_nonneg fun t => mul_nonneg (hw t) (hw (t - v))⟩
  rw [weilTest_apply, ← integral_complex_ofReal]
  congr 1 with t
  rw [Complex.conj_ofReal]
  push_cast
  ring

/-- **Aligned phases.** For real nonnegative coefficients and a real nonnegative window, every
off-diagonal term of the windowed mean square is nonnegative, so the windowed mean square is at
least the diagonal plus `Σ_{close j ≠ k} c_j c_k k_η(ν_j − ν_k)`. -/
theorem le_integral_normSq_mul_normSq_expSum_of_nonneg {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 (fun u => (w u : ℂ))) (hwc : HasCompactSupport (fun u => (w u : ℂ)))
    (hw0 : ∀ u, 0 ≤ w u) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ν : ι → ℝ) :
    (∫ t, ‖(w t : ℂ)‖ ^ 2) * ∑ j ∈ s, c j ^ 2 +
        ∑ j ∈ s, ∑ k ∈ s.erase j, c j * c k * ∫ t, w t * w (t - (ν j - ν k)) =
      ∫ ξ : ℝ, ‖paperFT (fun u => (w u : ℂ)) (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖expSum s (fun j => (c j : ℂ)) ν ξ‖ ^ 2 ∧
    0 ≤ ∑ j ∈ s, ∑ k ∈ s.erase j, c j * c k * ∫ t, w t * w (t - (ν j - ν k)) := by
  refine ⟨?_, Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (hc j) (hc k)) (weilTest_ofReal_nonneg hw0 _).2⟩
  rw [integral_normSq_mul_normSq_expSum_eq_diag_add hw hwc]
  have hcn : ∀ j, ‖(c j : ℂ)‖ ^ 2 = c j ^ 2 := fun j => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hcn]
  congr 1
  have hterm : ∀ j k, (c j : ℂ) * conj (c k : ℂ) *
      EF.weilTest (fun u => (w u : ℂ)) (fun u => (w u : ℂ)) (ν j - ν k) =
      ((c j * c k * ∫ t, w t * w (t - (ν j - ν k)) : ℝ) : ℂ) := fun j k => by
    rw [(weilTest_ofReal_nonneg hw0 _).1, Complex.conj_ofReal]
    push_cast
    ring
  simp only [hterm, ← Complex.ofReal_sum, Complex.ofReal_re]

/-! ### Height averages -/

/-- **Height-averaged windowed mean square.** Averaging over centres `ξ₀` with the weight
`|h_ω(−2πξ₀)|²` multiplies each pair by `k_ω(ν_j − ν_k)`. -/
theorem integral_pairTransform_mul_integral_windowed_eq {η ω : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) (hω : ContDiff ℝ 2 ω) (hωc : HasCompactSupport ω) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) :
    ∫ ξ₀ : ℝ, pairTransform ω ξ₀ *
        ∫ ξ : ℝ, pairTransform η ξ * (expSum s c ν (ξ + ξ₀) * conj (expSum s c ν (ξ + ξ₀))) =
      ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
        EF.weilTest ω ω (ν j - ν k) := by
  obtain ⟨ρ, -, hsω⟩ := exists_radius_bound hωc
  have he : ∀ ξ₀ : ℝ, ∀ j k : ι, cexp (2 * π * I * ξ₀ * ν j) * conj (cexp (2 * π * I * ξ₀ * ν k)) =
      cexp (2 * π * I * ξ₀ * ((ν j - ν k : ℝ) : ℂ)) := by
    intro ξ₀ j k
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  have hinner : ∀ ξ₀ : ℝ, ∫ ξ : ℝ, pairTransform η ξ *
      (expSum s c ν (ξ + ξ₀) * conj (expSum s c ν (ξ + ξ₀))) =
      ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
        cexp (2 * π * I * ξ₀ * ((ν j - ν k : ℝ) : ℂ)) := by
    intro ξ₀
    simp_rw [expSum_add]
    rw [integral_pairTransform_mul_normSq_expSum hη hηc]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← he ξ₀ j k]
    ring
  have hPωc : Continuous fun ξ : ℝ => pairTransform ω ξ :=
    (differentiable_pairTransform hω hωc).continuous.comp Complex.continuous_ofReal
  have hPωi := integrable_pairTransform hω hωc
  have hint : ∀ j k : ι, Integrable fun ξ₀ : ℝ => pairTransform ω ξ₀ *
      (c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
        cexp (2 * π * I * ξ₀ * ((ν j - ν k : ℝ) : ℂ))) := by
    intro j k
    refine (hPωi.norm.const_mul ‖c j * conj (c k) * EF.weilTest η η (ν j - ν k)‖).mono'
      (hPωc.mul (continuous_const.mul (by fun_prop))).aestronglyMeasurable
      (Eventually.of_forall fun ξ₀ => ?_)
    rw [norm_mul, norm_mul (c j * conj (c k) * EF.weilTest η η (ν j - ν k)),
      norm_cexp_two_pi_I_mul, mul_one, mul_comm]
  simp_rw [hinner, Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hω' := weilTest_eq_integral hω hωc hsω (ν j - ν k)
  calc ∫ ξ₀ : ℝ, pairTransform ω ξ₀ * (c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
          cexp (2 * π * I * ξ₀ * ((ν j - ν k : ℝ) : ℂ)))
      = c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
          ∫ ξ₀ : ℝ, pairTransform ω ξ₀ * cexp (2 * π * I * ξ₀ * ((ν j - ν k : ℝ) : ℂ)) := by
        rw [← integral_const_mul]
        congr 1 with ξ₀
        ring
    _ = c j * conj (c k) * EF.weilTest η η (ν j - ν k) * EF.weilTest ω ω (ν j - ν k) := by
        rw [hω']

end GaloisForLFunctions.SquareRootThreshold
