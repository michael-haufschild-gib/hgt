import GaloisForLFunctions.RHTower.Sieve.KthDerivativeTest
import GaloisForLFunctions.RHTower.GaussSpikeMass

namespace RHTower.Sieve

open Real

noncomputable section

theorem sum_Icc_sqrt_le_mul_sqrt (H : ℕ) :
    ∑ h ∈ Finset.Icc 1 (H - 1), Real.sqrt h ≤ (H : ℝ) * Real.sqrt H := by
  have hpt : ∀ h ∈ Finset.Icc 1 (H - 1), Real.sqrt h ≤ Real.sqrt H := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    exact Real.sqrt_le_sqrt (by exact_mod_cast (le_trans hh.2 (Nat.sub_le H 1)))
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc 1 (H - 1)).card : ℝ) ≤ (H : ℝ) := by
    rw [Nat.card_Icc]
    exact_mod_cast (Nat.sub_le H 1)
  exact mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg _)

theorem sum_Icc_inv_sqrt_le_three_sqrt (H : ℕ) (hH : 1 ≤ H) :
    ∑ h ∈ Finset.Icc 1 (H - 1), (Real.sqrt h)⁻¹ ≤ 3 * Real.sqrt H := by
  have heq : ∀ h ∈ Finset.Icc 1 (H - 1),
      (Real.sqrt h)⁻¹ = ((h : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    intro h hh
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity)]
  rw [Finset.sum_congr rfl heq]
  have hhead := RHTower.sum_rpow_neg_head_le (c := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (H - 1)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt H := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hH)
  have hsub : Real.sqrt (((H - 1 : ℕ) : ℝ)) ≤ Real.sqrt (H : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le H 1)
  have hrpow : (((H - 1 : ℕ) : ℝ)) ^ (1 - (1 / 2 : ℝ)) =
      Real.sqrt (((H - 1 : ℕ) : ℝ)) := by
    rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [hrpow] at hhead
  norm_num at hhead
  nlinarith

set_option maxHeartbeats 1600000 in
theorem third_derivative_test_window (G : ℕ → ℝ → ℝ) (x₀ : ℝ) (N H : ℕ)
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N)
    {lam hgrow : ℝ} (hlam0 : 0 < lam) (hgrow1 : 1 ≤ hgrow)
    (hHlam : ((H - 1 : ℕ) : ℝ) * lam ≤ 1)
    (hchain : ∀ i < 3, ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)),
      HasDerivAt (G i) (G (i + 1) x) x)
    (hlo : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), lam ≤ G 3 x)
    (hhi : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), G 3 x ≤ hgrow * lam) :
    (H : ℝ) * ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ ^ 2
      ≤ 4 * (N : ℝ) * ((N : ℝ)
        + 8 * (N : ℝ) * hgrow * Real.sqrt lam * ((H : ℝ) * Real.sqrt H)
        + 36 * (Real.sqrt lam)⁻¹ * Real.sqrt H) := by
  set a : ℕ → ℂ := fun n =>
    Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I) with hadef
  have hanorm : ∀ n, ‖a n‖ ≤ 1 := fun n => le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hW := weyl_vdc a hanorm N H hH hHN
  have hcorr : ∀ h ∈ Finset.Icc 1 (H - 1),
      ‖weylCorr a N h‖ ≤
        8 * (N : ℝ) * hgrow * Real.sqrt lam * Real.sqrt h
          + 12 * (Real.sqrt lam)⁻¹ * (Real.sqrt h)⁻¹ := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    have hh1 : 1 ≤ h := hh.1
    have hhH : h < H := by omega
    have hhN : h < N := lt_of_lt_of_le hhH hHN
    have hN' : 1 ≤ N - h := by omega
    have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh1
    have hlamh0 : 0 < (h : ℝ) * lam := mul_pos hh0 hlam0
    have hlamh1 : (h : ℝ) * lam ≤ 1 := by
      have hhcast : (h : ℝ) ≤ ((H - 1 : ℕ) : ℝ) := by exact_mod_cast hh.2
      exact le_trans (mul_le_mul_of_nonneg_right hhcast hlam0.le) hHlam
    have hcast : ((N - h - 1 : ℕ) : ℝ) + (h : ℝ) = ((N - 1 : ℕ) : ℝ) := by
      have hn : (N - h - 1) + h = N - 1 := by omega
      exact_mod_cast hn
    have hspan : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - h - 1 : ℕ) : ℝ)),
        x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) ∧
          x + (h : ℝ) ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) := by
      intro x hx
      constructor <;> constructor <;> linarith [hx.1, hx.2, hcast]
    set Gd : ℕ → ℝ → ℝ := fun i x => G i (x + (h : ℝ)) - G i x with hGddef
    have hchain' : ∀ i < 2, ∀ x ∈ Set.Icc x₀ (x₀ + ((N - h - 1 : ℕ) : ℝ)),
        HasDerivAt (Gd i) (Gd (i + 1) x) x := by
      intro i hi x hx
      obtain ⟨hx1, hx2⟩ := hspan x hx
      have hd1 := hchain i (by omega) (x + (h : ℝ)) hx2
      have hd2 := hchain i (by omega) x hx1
      have hs := HasDerivAt.comp_add_const x (h : ℝ) hd1
      change HasDerivAt (fun y => G i (y + (h : ℝ)) - G i y)
        (G (i + 1) (x + (h : ℝ)) - G (i + 1) x) x
      exact hs.sub hd2
    have hslope : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - h - 1 : ℕ) : ℝ)),
        (h : ℝ) * lam ≤ Gd 2 x ∧ Gd 2 x ≤ hgrow * ((h : ℝ) * lam) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hspan x hx
      have hlt : x < x + (h : ℝ) := by linarith
      have hsub : Set.Icc x (x + (h : ℝ)) ⊆
          Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) :=
        Set.Icc_subset_Icc hx1.1 hx2.2
      have hcont : ContinuousOn (G 2) (Set.Icc x (x + (h : ℝ))) := fun y hy =>
        (hchain 2 (by omega) y (hsub hy)).continuousAt.continuousWithinAt
      have hd : ∀ y ∈ Set.Ioo x (x + (h : ℝ)), HasDerivAt (G 2) (G 3 y) y :=
        fun y hy => hchain 2 (by omega) y (hsub (Set.mem_Icc_of_Ioo hy))
      obtain ⟨ξ, hξ, hval⟩ := exists_hasDerivAt_eq_slope (G 2) (G 3) hlt hcont hd
      have hξspan := hsub (Set.mem_Icc_of_Ioo hξ)
      have hden : (x + (h : ℝ)) - x ≠ 0 := by positivity
      rw [eq_div_iff hden] at hval
      have hdiff : (x + (h : ℝ)) - x = (h : ℝ) := by ring
      rw [hdiff] at hval
      constructor
      · simp only [hGddef]
        calc
          (h : ℝ) * lam = lam * (h : ℝ) := by ring
          _ ≤ G 3 ξ * (h : ℝ) := mul_le_mul_of_nonneg_right (hlo ξ hξspan) hh0.le
          _ = G 2 (x + (h : ℝ)) - G 2 x := hval
      · simp only [hGddef]
        calc
          G 2 (x + (h : ℝ)) - G 2 x = G 3 ξ * (h : ℝ) := hval.symm
          _ ≤ hgrow * lam * (h : ℝ) :=
            mul_le_mul_of_nonneg_right (hhi ξ hξspan) hh0.le
          _ = hgrow * ((h : ℝ) * lam) := by ring
    have htest := second_derivative_test' (Gd 0) (Gd 1) (Gd 2) x₀ (N - h) hN'
      hlamh0 hlamh1
      (fun x hx => hchain' 0 (by omega) x hx)
      (fun x hx => hchain' 1 (by omega) x hx)
      (fun x hx => (hslope x hx).1) (fun x hx => (hslope x hx).2)
    have hcorrEq : weylCorr a N h = ∑ n ∈ Finset.range (N - h),
        Complex.exp (((2 * Real.pi * Gd 0 (x₀ + n) : ℝ) : ℂ) * Complex.I) := by
      rw [hadef, weylCorr_phase]
    rw [hcorrEq]
    have hsqrtMul : Real.sqrt ((h : ℝ) * lam) = Real.sqrt h * Real.sqrt lam :=
      Real.sqrt_mul (Nat.cast_nonneg h) lam
    rw [hsqrtMul, div_eq_mul_inv, mul_inv_rev] at htest
    have hNh : ((N - h : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N h
    have hfac : 0 ≤ 8 * hgrow * (Real.sqrt h * Real.sqrt lam) := by positivity
    calc
      ‖∑ n ∈ Finset.range (N - h),
          Complex.exp (((2 * Real.pi * Gd 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
          ≤ 8 * (((N - h : ℕ) : ℝ)) * hgrow * (Real.sqrt h * Real.sqrt lam)
              + 12 * ((Real.sqrt lam)⁻¹ * (Real.sqrt h)⁻¹) := htest
      _ ≤ 8 * (N : ℝ) * hgrow * Real.sqrt lam * Real.sqrt h
              + 12 * (Real.sqrt lam)⁻¹ * (Real.sqrt h)⁻¹ := by
            have := mul_le_mul_of_nonneg_right hNh hfac
            nlinarith
  have hsum : ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖
      ≤ 8 * (N : ℝ) * hgrow * Real.sqrt lam * ((H : ℝ) * Real.sqrt H)
        + 36 * (Real.sqrt lam)⁻¹ * Real.sqrt H := by
    refine (Finset.sum_le_sum hcorr).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hsqrt := sum_Icc_sqrt_le_mul_sqrt H
    have hinv := sum_Icc_inv_sqrt_le_three_sqrt H hH
    have hfac1 : 0 ≤ 8 * (N : ℝ) * hgrow * Real.sqrt lam := by positivity
    have hfac2 : 0 ≤ 12 * (Real.sqrt lam)⁻¹ := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsqrt hfac1
    have h2 := mul_le_mul_of_nonneg_left hinv hfac2
    nlinarith
  have hsum0 : 0 ≤ ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hfacN : 0 ≤ 4 * (N : ℝ) := by positivity
  have hinside : (N : ℝ) + ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖ ≤
      (N : ℝ) + (8 * (N : ℝ) * hgrow * Real.sqrt lam * ((H : ℝ) * Real.sqrt H)
        + 36 * (Real.sqrt lam)⁻¹ * Real.sqrt H) := add_le_add_right hsum _
  have hscaled := mul_le_mul_of_nonneg_left hinside hfacN
  simpa only [hadef, add_assoc] using hW.trans hscaled

set_option maxHeartbeats 1600000 in
/-- Sharp order-three derivative test, retaining the summable `h⁻¹ᵗ²` correlation branch. -/
theorem third_derivative_test_sharp (G : ℕ → ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    {lam hgrow : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hgrow1 : 1 ≤ hgrow)
    (hchain : ∀ i < 3, ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)),
      HasDerivAt (G i) (G (i + 1) x) x)
    (hlo : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), lam ≤ G 3 x)
    (hhi : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), G 3 x ≤ hgrow * lam) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ 16 * hgrow * ((N : ℝ) * lam ^ (1 / 6 : ℝ)
        + Real.sqrt N * lam ^ (-(1 / 6 : ℝ))) := by
  have hgrow0 : 0 < hgrow := lt_of_lt_of_le one_pos hgrow1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlamnn : 0 ≤ lam := hlam0.le
  have hsqrtlam : Real.sqrt lam = lam ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow lam
  set H₀ : ℝ := lam ^ (-(1 / 3 : ℝ)) with hH₀def
  have hH₀pos : 0 < H₀ := by rw [hH₀def]; positivity
  have hH₀one : 1 ≤ H₀ := by
    rw [hH₀def]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam0 hlam1 (by norm_num)
  have hsqrtH₀ : Real.sqrt H₀ = lam ^ (-(1 / 6 : ℝ)) := by
    rw [hH₀def, Real.sqrt_eq_rpow, ← Real.rpow_mul hlamnn]
    congr 1
    norm_num
  have hH₀lam : H₀ * lam = lam ^ (2 / 3 : ℝ) := by
    calc
      H₀ * lam = lam ^ (-(1 / 3 : ℝ)) * lam ^ (1 : ℝ) := by
        rw [hH₀def, Real.rpow_one]
      _ = lam ^ (-(1 / 3 : ℝ) + 1) := (Real.rpow_add hlam0 _ _).symm
      _ = lam ^ (2 / 3 : ℝ) := by norm_num
  have hlamTwoThirds : lam ^ (2 / 3 : ℝ) ≤ 1 :=
    Real.rpow_le_one hlamnn hlam1 (by norm_num)
  by_cases hshort : (N : ℝ) ≤ H₀
  · have hsqN : Real.sqrt N ≤ Real.sqrt H₀ := Real.sqrt_le_sqrt hshort
    rw [hsqrtH₀] at hsqN
    have hsqrtN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hsqrtN2 : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hN0.le
    have hNV : (N : ℝ) ≤ Real.sqrt N * lam ^ (-(1 / 6 : ℝ)) := by
      nlinarith [mul_nonneg hsqrtN0
        (Real.rpow_nonneg hlamnn (-(1 / 6 : ℝ)))]
    have htriv := norm_phase_sum_le_card (G 0) x₀ N
    have hU0 : 0 ≤ (N : ℝ) * lam ^ (1 / 6 : ℝ) := by positivity
    have hV0 : 0 ≤ Real.sqrt N * lam ^ (-(1 / 6 : ℝ)) := by positivity
    calc
      ‖∑ n ∈ Finset.range N,
          Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
          ≤ (N : ℝ) := htriv
      _ ≤ Real.sqrt N * lam ^ (-(1 / 6 : ℝ)) := hNV
      _ ≤ 16 * hgrow * ((N : ℝ) * lam ^ (1 / 6 : ℝ)
          + Real.sqrt N * lam ^ (-(1 / 6 : ℝ))) := by nlinarith
  · have hH₀N : H₀ < (N : ℝ) := lt_of_not_ge hshort
    set H : ℕ := ⌈H₀⌉₊ with hHdef
    have hH1 : 1 ≤ H := Nat.one_le_ceil_iff.mpr hH₀pos
    have hHN : H ≤ N := by
      rw [hHdef, Nat.ceil_le]
      exact hH₀N.le
    have hH₀H : H₀ ≤ (H : ℝ) := by
      rw [hHdef]
      exact Nat.le_ceil H₀
    have hHH₀ : (H : ℝ) < H₀ + 1 := by
      rw [hHdef]
      exact Nat.ceil_lt_add_one hH₀pos.le
    have hHle : (H : ℝ) ≤ 2 * H₀ := by linarith
    have hHsub : (((H - 1 : ℕ) : ℝ)) < H₀ := by
      rw [hHdef]
      exact (Nat.lt_ceil).mp (by omega : ⌈H₀⌉₊ - 1 < ⌈H₀⌉₊)
    have hHlam : (((H - 1 : ℕ) : ℝ)) * lam ≤ 1 := by
      have hmul : (((H - 1 : ℕ) : ℝ)) * lam ≤ H₀ * lam :=
        mul_le_mul_of_nonneg_right hHsub.le hlamnn
      rw [hH₀lam] at hmul
      exact hmul.trans hlamTwoThirds
    have hwindow := third_derivative_test_window G x₀ N H hN hH1 hHN hlam0
      hgrow1 hHlam hchain hlo hhi
    have hrootLower : lam ^ (-(1 / 6 : ℝ)) ≤ Real.sqrt H := by
      rw [← hsqrtH₀]
      exact Real.sqrt_le_sqrt hH₀H
    have hsqrtHle : Real.sqrt H ≤ 2 * lam ^ (-(1 / 6 : ℝ)) := by
      have hsq := Real.sqrt_le_sqrt hHle
      have hsqrtTwo : Real.sqrt (2 * H₀) = Real.sqrt 2 * Real.sqrt H₀ :=
        Real.sqrt_mul (by norm_num) H₀
      rw [hsqrtTwo, hsqrtH₀] at hsq
      have hsqrtTwoLe : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact hsq.trans (mul_le_mul_of_nonneg_right hsqrtTwoLe (Real.rpow_nonneg hlamnn _))
    have hlamPowAdd : lam ^ (1 / 2 : ℝ) * lam ^ (-(1 / 6 : ℝ)) =
        lam ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hlam0]
      congr 1
      norm_num
    have hA : (1 : ℝ) ≤ (H : ℝ) * lam ^ (1 / 3 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hH₀H (Real.rpow_nonneg hlamnn (1 / 3 : ℝ))
      have hid : H₀ * lam ^ (1 / 3 : ℝ) = 1 := by
        rw [hH₀def, ← Real.rpow_add hlam0]
        norm_num
      rwa [hid] at hmul
    have hB : Real.sqrt lam * Real.sqrt H ≤ 2 * lam ^ (1 / 3 : ℝ) := by
      rw [hsqrtlam]
      calc
        lam ^ (1 / 2 : ℝ) * Real.sqrt H
            ≤ lam ^ (1 / 2 : ℝ) * (2 * lam ^ (-(1 / 6 : ℝ))) :=
          mul_le_mul_of_nonneg_left hsqrtHle (Real.rpow_nonneg hlamnn _)
        _ = 2 * lam ^ (1 / 3 : ℝ) := by rw [← hlamPowAdd]; ring
    have hinvSqrt : (Real.sqrt lam)⁻¹ = lam ^ (-(1 / 2 : ℝ)) := by
      rw [hsqrtlam, ← Real.rpow_neg hlamnn]
    have hpowNeg : lam ^ (-(1 / 3 : ℝ)) * lam ^ (-(1 / 6 : ℝ)) =
        lam ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hlam0]
      congr 1
      norm_num
    have hC : (Real.sqrt lam)⁻¹ * Real.sqrt H ≤
        (H : ℝ) * lam ^ (-(1 / 3 : ℝ)) := by
      rw [hinvSqrt, ← hpowNeg]
      have hsqrtH0 : 0 ≤ Real.sqrt H := Real.sqrt_nonneg _
      have hpow0 : 0 ≤ lam ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hlamnn _
      calc
        (lam ^ (-(1 / 3 : ℝ)) * lam ^ (-(1 / 6 : ℝ))) * Real.sqrt H
            ≤ (lam ^ (-(1 / 3 : ℝ)) * Real.sqrt H) * Real.sqrt H := by
          gcongr
        _ = lam ^ (-(1 / 3 : ℝ)) * (H : ℝ) := by
          rw [mul_assoc, Real.mul_self_sqrt (by positivity)]
        _ = (H : ℝ) * lam ^ (-(1 / 3 : ℝ)) := by ring
    set U : ℝ := (N : ℝ) * lam ^ (1 / 6 : ℝ) with hUdef
    set V : ℝ := Real.sqrt N * lam ^ (-(1 / 6 : ℝ)) with hVdef
    have hU0 : 0 ≤ U := by rw [hUdef]; positivity
    have hV0 : 0 ≤ V := by rw [hVdef]; positivity
    have hpowU : (lam ^ (1 / 6 : ℝ)) ^ 2 = lam ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlamnn]
      congr 1
      norm_num
    have hpowV : (lam ^ (-(1 / 6 : ℝ))) ^ 2 = lam ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlamnn]
      congr 1
      norm_num
    have hU2 : U ^ 2 = (N : ℝ) ^ 2 * lam ^ (1 / 3 : ℝ) := by
      rw [hUdef, mul_pow, hpowU]
    have hV2 : V ^ 2 = (N : ℝ) * lam ^ (-(1 / 3 : ℝ)) := by
      rw [hVdef, mul_pow, Real.sq_sqrt hN0.le, hpowV]
    have hRhs : 4 * (N : ℝ) * ((N : ℝ)
          + 8 * (N : ℝ) * hgrow * Real.sqrt lam * ((H : ℝ) * Real.sqrt H)
          + 36 * (Real.sqrt lam)⁻¹ * Real.sqrt H)
        ≤ (H : ℝ) * (16 * hgrow * (U + V)) ^ 2 := by
      have hNterm : 4 * (N : ℝ) ^ 2 ≤ 4 * (H : ℝ) * U ^ 2 := by
        rw [hU2]
        nlinarith [mul_nonneg (Nat.cast_nonneg H) (Real.rpow_nonneg hlamnn (1 / 3 : ℝ))]
      have hFirst : 32 * (N : ℝ) ^ 2 * hgrow * Real.sqrt lam *
            ((H : ℝ) * Real.sqrt H) ≤ 64 * (H : ℝ) * hgrow ^ 2 * U ^ 2 := by
        rw [hU2]
        have hg : hgrow ≤ hgrow ^ 2 := by nlinarith
        calc
          32 * (N : ℝ) ^ 2 * hgrow * Real.sqrt lam * ((H : ℝ) * Real.sqrt H)
              = 32 * (N : ℝ) ^ 2 * (H : ℝ) * hgrow *
                  (Real.sqrt lam * Real.sqrt H) := by ring
          _ ≤ 32 * (N : ℝ) ^ 2 * (H : ℝ) * hgrow *
                  (2 * lam ^ (1 / 3 : ℝ)) := by gcongr
          _ ≤ 32 * (N : ℝ) ^ 2 * (H : ℝ) * hgrow ^ 2 *
                  (2 * lam ^ (1 / 3 : ℝ)) := by gcongr
          _ = 64 * (H : ℝ) * hgrow ^ 2 *
                  ((N : ℝ) ^ 2 * lam ^ (1 / 3 : ℝ)) := by ring
      have hSecond : 144 * (N : ℝ) * (Real.sqrt lam)⁻¹ * Real.sqrt H ≤
            144 * (H : ℝ) * hgrow ^ 2 * V ^ 2 := by
        rw [hV2]
        have hg2 : 1 ≤ hgrow ^ 2 := by nlinarith
        have hbase0 : 0 ≤ (H : ℝ) * lam ^ (-(1 / 3 : ℝ)) := by positivity
        have hbase : (H : ℝ) * lam ^ (-(1 / 3 : ℝ)) ≤
            hgrow ^ 2 * ((H : ℝ) * lam ^ (-(1 / 3 : ℝ))) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hg2 hbase0
        calc
          144 * (N : ℝ) * (Real.sqrt lam)⁻¹ * Real.sqrt H
              = 144 * (N : ℝ) * ((Real.sqrt lam)⁻¹ * Real.sqrt H) := by ring
          _ ≤ 144 * (N : ℝ) * ((H : ℝ) * lam ^ (-(1 / 3 : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hC (by positivity)
          _ ≤ 144 * (N : ℝ) *
                  (hgrow ^ 2 * ((H : ℝ) * lam ^ (-(1 / 3 : ℝ)))) := by
            exact mul_le_mul_of_nonneg_left hbase (by positivity)
          _ = 144 * (H : ℝ) * hgrow ^ 2 *
                  ((N : ℝ) * lam ^ (-(1 / 3 : ℝ))) := by ring
      have hsq : U ^ 2 + V ^ 2 ≤ (U + V) ^ 2 := by nlinarith
      have hH0cast : 0 ≤ (H : ℝ) := Nat.cast_nonneg H
      have hg20 : 0 ≤ hgrow ^ 2 := sq_nonneg hgrow
      have hg2 : 1 ≤ hgrow ^ 2 := by nlinarith
      have hUscale : U ^ 2 ≤ hgrow ^ 2 * U ^ 2 :=
        by simpa only [one_mul] using mul_le_mul_of_nonneg_right hg2 (sq_nonneg U)
      have hNterm' : 4 * (H : ℝ) * U ^ 2 ≤
          4 * (H : ℝ) * hgrow ^ 2 * U ^ 2 := by
        calc
          4 * (H : ℝ) * U ^ 2 ≤ 4 * (H : ℝ) * (hgrow ^ 2 * U ^ 2) :=
            mul_le_mul_of_nonneg_left hUscale (by positivity)
          _ = 4 * (H : ℝ) * hgrow ^ 2 * U ^ 2 := by ring
      have hsqScaled : 144 * (H : ℝ) * hgrow ^ 2 * (U ^ 2 + V ^ 2) ≤
          144 * (H : ℝ) * hgrow ^ 2 * (U + V) ^ 2 := by gcongr
      calc
        4 * (N : ℝ) * ((N : ℝ)
              + 8 * (N : ℝ) * hgrow * Real.sqrt lam * ((H : ℝ) * Real.sqrt H)
              + 36 * (Real.sqrt lam)⁻¹ * Real.sqrt H)
            = 4 * (N : ℝ) ^ 2
              + 32 * (N : ℝ) ^ 2 * hgrow * Real.sqrt lam * ((H : ℝ) * Real.sqrt H)
              + 144 * (N : ℝ) * (Real.sqrt lam)⁻¹ * Real.sqrt H := by ring
        _ ≤ 4 * (H : ℝ) * U ^ 2
              + 64 * (H : ℝ) * hgrow ^ 2 * U ^ 2
              + 144 * (H : ℝ) * hgrow ^ 2 * V ^ 2 := by linarith
        _ ≤ 144 * (H : ℝ) * hgrow ^ 2 * (U ^ 2 + V ^ 2) := by
              nlinarith [hNterm']
        _ ≤ 144 * (H : ℝ) * hgrow ^ 2 * (U + V) ^ 2 := hsqScaled
        _ ≤ (H : ℝ) * (16 * hgrow * (U + V)) ^ 2 := by
              have hcoeff : (144 : ℝ) ≤ 256 := by norm_num
              ring_nf
              have htUV : 0 ≤ (H : ℝ) * hgrow ^ 2 * U * V := by positivity
              have htU : 0 ≤ (H : ℝ) * hgrow ^ 2 * U ^ 2 := by positivity
              have htV : 0 ≤ (H : ℝ) * hgrow ^ 2 * V ^ 2 := by positivity
              nlinarith
    have hsqBound :
        ‖∑ n ∈ Finset.range N,
            Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ ^ 2
          ≤ (16 * hgrow * (U + V)) ^ 2 := by
      have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
      have hmul := hwindow.trans hRhs
      nlinarith
    have htarget0 : 0 ≤ 16 * hgrow * (U + V) := by positivity
    have hnorm0 := norm_nonneg (∑ n ∈ Finset.range N,
      Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I))
    have hres : ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * G 0 (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
        ≤ 16 * hgrow * (U + V) := (sq_le_sq₀ hnorm0 htarget0).mp hsqBound
    simpa only [hUdef, hVdef] using hres

end

end RHTower.Sieve
