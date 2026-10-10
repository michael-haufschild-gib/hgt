import GaloisForLFunctions.RHTower.XiCosineShiftNonrealZeroCount
import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointConfinement

/-!
# Degenerate zeros of the cosine producer are power-sparse

Call a zero of `A_h = cos(hD)Ξ` *degenerate* if it is non-real or a multiple real zero (an
exceptional point). By the exceptional-point criterion, RH says that `A_h` has no degenerate zero for
any `h > 0`. This module proves the unconditional counterpart.

* `exists_xiZeroCopy_of_cosineShift_multiple`: a multiple real zero `x` of `A_h` violates the local
  phase law. So `ξ` has a zero `ρ` with `Re ρ ≥ ½ + h` and `|Im ρ − x| < ½`.
* `exists_card_cosineShift_degenerateZeros_le`: for `0 < h ≤ ½` the zero copies of `A_h` with real
  part in `[T + ½, 2T − ½]` that are non-real or multiple number at most
  `D (1 + log T)^{B+1} T^{(A(½+h)+ε)(½−h)}`. Here `A` is the Ingham–Huxley exponent.

Each degenerate zero lies within `½` of a zero of `ξ` of depth at least `h`. Each such zero carries
`O(log T)` zeros of `A_h` within `½` of its ordinate. The Ingham–Huxley density estimate counts the
deep zeros.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower

noncomputable section

/-- A multiple real zero of `cos(hD)Ξ` lies within `½` of a zero of `ξ` of depth at least `h`. -/
theorem exists_xiZeroCopy_of_cosineShift_multiple {h x : ℝ} (hh : 0 < h)
    (hzero : (XiC ((x : ℂ) + h * I) + XiC ((x : ℂ) - h * I)) / 2 = 0)
    (hd : deriv (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) x = 0) :
    ∃ q : XiZeroCopy, 1 / 2 + h ≤ (q.1 : ℂ).re ∧ |(q.1 : ℂ).im - x| < 1 / 2 := by
  obtain ⟨w, hw, hloc⟩ : ∃ w, XiC w = 0 ∧ (x - w.re) ^ 2 + h ^ 2 ≤ w.im ^ 2 := by
    by_contra hall
    push Not at hall
    exact deriv_cosineShiftXi_ne_zero_of_local hh (fun w hw => hall w hw) hzero hd
  have hxi : xi (1 / 2 + w * I) = 0 := by rw [← hw, XiC]
  have hwim : |w.im| < 1 / 2 := by
    obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hxi
    have hre : (1 / 2 + w * I).re = 1 / 2 - w.im := by simp; ring
    rw [hre] at h0 h1
    rw [abs_lt]; constructor <;> linarith
  have hw2 : w.im ^ 2 < 1 / 4 := by
    have := sq_lt_sq' (by linarith [(abs_lt.mp hwim).1]) (abs_lt.mp hwim).2
    linarith
  have hclose : |w.re - x| < 1 / 2 := by
    have h1 : (w.re - x) ^ 2 < (1 / 2) ^ 2 := by nlinarith
    have := sq_lt_sq.mp h1
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  have hdeep : h ≤ |w.im| := by
    have h1 : h ^ 2 ≤ w.im ^ 2 := by nlinarith [sq_nonneg (x - w.re)]
    have := sq_le_sq.mp h1
    rwa [abs_of_pos hh] at this
  rcases le_or_gt 0 w.im with hpos | hneg
  · -- reflect: `1 − conj(½ + iw)` has real part `½ + Im w`
    have hxi' : xi (1 - (starRingEnd ℂ) (1 / 2 + w * I)) = 0 := by
      rw [xi_one_sub, xi_conj, hxi, map_zero]
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi'
    refine ⟨q, ?_, ?_⟩
    · rw [hq, abs_of_nonneg hpos] at *; simp; linarith
    · rw [hq]; simpa using hclose
  · obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    refine ⟨q, ?_, ?_⟩
    · rw [hq]; rw [abs_of_neg hneg] at hdeep; simp; linarith
    · rw [hq]; simpa using hclose

/-- **Degenerate zeros are power-sparse.** For `0 < h ≤ ½` and `0 < ε ≤ 1`, the zero copies of
`cos(hD)Ξ` with real part in `[T + ½, 2T − ½]` that are non-real or multiple number at most
`D (1 + log T)^{B+1} T^{(A(½+h)+ε)(½−h)}`. -/
theorem exists_card_cosineShift_degenerateZeros_le {h ε : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ P : Finset (ZeroCopy (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2)),
        (∀ p ∈ P, ((zeroCopyPoint _ p).im ≠ 0 ∨
            deriv (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) (zeroCopyPoint _ p) = 0) ∧
          T + 1 / 2 ≤ (zeroCopyPoint _ p).re ∧ (zeroCopyPoint _ p).re ≤ 2 * T - 1 / 2) →
        (P.card : ℝ) ≤ D * (1 + Real.log T) ^ (B + 1) *
          T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h)) := by
  classical
  set f : ℂ → ℂ := fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2 with hfdef
  have hg := DeBruijn.riemannKernel_mul_cosh_superExp h
  have hF : DeBruijn.cosTransform (fun x => riemannKernelReal x * Real.cosh (h * x)) = f :=
    funext (DeBruijn.cosTransform_riemannKernel_mul_cosh h)
  obtain ⟨C₀, hC₀0, hC₀⟩ := hg.exists_envelope
  have hfan : AnalyticOnNhd ℂ f univ := by
    rw [← hF]; exact hg.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hf0 : f 0 ≠ 0 := by rw [← hF]; exact hg.cosTransform_zero_ne
  have heven : ∀ z, f (-z) = f z := by rw [← hF]; exact hg.cosTransform_neg
  have hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C₀ * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    rw [← hF]; exact hC₀
  have hstrip0 : ∀ w, f w = 0 → |w.im| ≤ 1 / 2 := by
    intro w hw
    have h1 := DeBruijn.cosineShift_zeros_im_sq_le hh hw
    have h2 : max (1 / 4 - h ^ 2) 0 ≤ (1 / 2) ^ 2 := max_le (by nlinarith) (by norm_num)
    have := sq_le_sq.mp (h1.trans h2)
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  obtain ⟨D₁, hD₁, B, T₁, hT₁, hIH⟩ :=
    exists_zeroHeightBox_ncard_le_ingham_huxley (σ := 1 / 2 + h) (by linarith) (by linarith) hε hε1
  obtain ⟨C, hC, hev⟩ := exists_norm_logDeriv_cosineShift_le hh hh2
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev
  refine ⟨29 * C * D₁, by positivity, B, max T₁ (max X₀ 2), le_trans hT₁ (le_max_left _ _),
    fun T hT P hP => ?_⟩
  have hTT₁ : T₁ ≤ T := le_trans (le_max_left _ _) hT
  have hTX : X₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT2 : 2 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hfin := zeroHeightBox_finite (1 / 2 + h) T
  set Z := hfin.toFinset with hZ
  set Fq : XiZeroCopy → Finset (ZeroCopy f) := fun q =>
    P.filter (fun p => |(zeroCopyPoint f p).re - (q.1 : ℂ).im| < 1 / 2) with hFq
  have hcover : P ⊆ Z.biUnion Fq := by
    intro p hp
    obtain ⟨hdeg, hplo, hphi⟩ := hP p hp
    have hzero : (XiC (zeroCopyPoint f p + h * I) + XiC (zeroCopyPoint f p - h * I)) / 2 = 0 :=
      DeBruijn.apply_zeroCopyPoint hfan p
    obtain ⟨q, hqre, hqim⟩ : ∃ q : XiZeroCopy, 1 / 2 + h ≤ (q.1 : ℂ).re ∧
        |(q.1 : ℂ).im - (zeroCopyPoint f p).re| < 1 / 2 := by
      by_cases hpim : (zeroCopyPoint f p).im = 0
      · have hpt : zeroCopyPoint f p = (((zeroCopyPoint f p).re : ℝ) : ℂ) :=
          Complex.ext (by simp) (by simp [hpim])
        have hd : deriv f (zeroCopyPoint f p) = 0 := hdeg.resolve_left (not_not.mpr hpim)
        rw [hpt] at hzero hd
        exact exists_xiZeroCopy_of_cosineShift_multiple hh hzero hd
      · obtain ⟨q, hqre, hqim⟩ := exists_xiZeroCopy_of_cosineShift_nonreal hh hpim hzero
        exact ⟨q, hqre.le, hqim⟩
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hqim
    refine Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩
    · rw [hZ, Set.Finite.mem_toFinset]
      exact ⟨hqre, by linarith, by linarith⟩
    · rw [hFq, Finset.mem_filter]
      refine ⟨hp, ?_⟩
      rw [abs_sub_comm]; exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hfibre : ∀ q ∈ Z, ((Fq q).card : ℝ) ≤ 29 * C * (1 + Real.log T) := by
    intro q hq
    rw [hZ, Set.Finite.mem_toFinset] at hq
    obtain ⟨-, hqlo, hqhi⟩ := hq
    have hcount := card_le_of_even_strip hC₀0 hfan hf0 heven hbound hstrip0
      (x₀ := (q.1 : ℂ).im) (Y := 3 / 2 + h) (by linarith) (by linarith) (Fq q) (by
        intro p hp
        rw [hFq, Finset.mem_filter] at hp
        exact hp.2.le.trans (by norm_num))
    have hlogd := hX₀ ((q.1 : ℂ).im) (by linarith)
    have hlogT : Real.log ((q.1 : ℂ).im) ≤ 1 + Real.log T := by
      have hqpos : 0 < (q.1 : ℂ).im := by linarith
      have h1 : Real.log ((q.1 : ℂ).im) ≤ Real.log (2 * T) := Real.log_le_log hqpos hqhi
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have h2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    calc ((Fq q).card : ℝ) ≤ 29 * ‖logDeriv f (((q.1 : ℂ).im : ℂ) -
          ((3 / 2 + h : ℝ) : ℂ) * I)‖ := hcount
      _ ≤ 29 * (C * Real.log ((q.1 : ℂ).im)) := by gcongr
      _ ≤ 29 * C * (1 + Real.log T) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hlogT (by positivity)
  have hZcard : (Z.card : ℝ) ≤ D₁ * (1 + Real.log T) ^ B *
      T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h)) := by
    have := hIH T hTT₁
    rw [show (1 : ℝ) - (1 / 2 + h) = 1 / 2 - h by ring] at this
    rw [hZ, ← Set.ncard_eq_toFinset_card _ hfin]
    exact this
  have hlog1 : 0 ≤ 1 + Real.log T := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T); linarith
  calc (P.card : ℝ) ≤ ((Z.biUnion Fq).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ q ∈ Z, ((Fq q).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ q ∈ Z, 29 * C * (1 + Real.log T) := Finset.sum_le_sum hfibre
    _ = (Z.card : ℝ) * (29 * C * (1 + Real.log T)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D₁ * (1 + Real.log T) ^ B *
          T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h))) *
          (29 * C * (1 + Real.log T)) :=
        mul_le_mul_of_nonneg_right hZcard (by positivity)
    _ = 29 * C * D₁ * (1 + Real.log T) ^ (B + 1) *
          T ^ ((inghamHuxleyExponent (1 / 2 + h) + ε) * (1 / 2 - h)) := by
        rw [pow_succ]; ring

end

end RHTower
