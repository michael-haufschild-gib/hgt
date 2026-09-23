import GaloisForLFunctions.RHTower.Sieve.RouteTZetaAsymptotics

/-!
# Power saving from the Route-T Möbius contour

The four exact contour edges are reduced to one power-saving monomial.  Smoothing width
`H = N^(1-s/3)` balances the sharp-comparison error with the left-edge smoothing loss, where `s`
is the actual Route-T contour shift.  High edges are paid by `U >= N^(4 : ℕ)`.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

def routeTMoebiusPowerWidth (A δ S N : ℝ) : ℝ :=
  N ^ (1 - routeTContourShift A δ S / 3)

def routeTMoebiusPowerConstant (C C' : ℝ) : ℝ :=
  1000 * (1 + C + C')

theorem routeTMoebiusPowerConstant_pos {C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') :
    0 < routeTMoebiusPowerConstant C C' := by
  unfold routeTMoebiusPowerConstant
  positivity

private theorem routeT_rpow_width_sq
    {N s : ℝ} (hN : 0 < N) :
    (N ^ (1 - s / 3)) ^ (2 : ℕ) = N ^ (2 - 2 * s / 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  congr 1
  ring

private theorem routeT_rpow_left_quotient
    {N s : ℝ} (hN : 0 < N) :
    N ^ (2 : ℕ) * N ^ (1 - s) / (N ^ (1 - s / 3)) ^ (2 : ℕ) =
      N ^ (1 - s / 3) := by
  rw [routeT_rpow_width_sq hN, ← Real.rpow_natCast,
    ← Real.rpow_add hN, ← Real.rpow_sub hN]
  congr 1
  ring

set_option maxHeartbeats 1000000 in
/-- **Exact four-edge reduction.**  Every term in the sharp Route-T majorant is bounded by a
single `N^(1-s/3)` monomial. -/
theorem routeTMoebiusSharpBound_le_power
    {A C C' δ x N τ U : ℝ}
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hδ : 0 < δ)
    (hN : 2 ≤ N) (hx0 : 0 < x) (hx : x ≤ 2 * N)
    (hU : N ^ (4 : ℕ) ≤ U) :
    routeTMoebiusSharpBound A C C' δ x
        (routeTMoebiusPowerWidth A δ (|τ| + U) N) τ U ≤
      routeTMoebiusPowerConstant C C' *
        routeTContourEdgeBound A (|τ| + U) *
        N ^ (1 - routeTContourShift A δ (|τ| + U) / 3) := by
  let S : ℝ := |τ| + U
  let s : ℝ := routeTContourShift A δ S
  let d : ℝ := routeTInverseDelta A S
  let left : ℝ := routeTContourLeft A δ S
  let right : ℝ := routeTContourRight A S
  let H : ℝ := N ^ (1 - s / 3)
  let B : ℝ := x + H + 1
  let Mh : ℝ := routeTContourEdgeBound A S
  let Md : ℝ := routeTContourRightBound A S
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hs0 : 0 < s := by
    dsimp only [s, S]
    exact routeTContourShift_pos hδ
  have hd0 : 0 < d := by
    dsimp only [d, S]
    exact routeTInverseDelta_pos A S
  have hd16 : d ≤ 1 / 16 := by
    dsimp only [d, S]
    exact routeTInverseDelta_le_sixteenth A S
  have hsD : s ≤ d / 20 := by
    dsimp only [s, d, S]
    exact routeTContourShift_le_delta_twentieth A δ S
  have hs320 : s ≤ 1 / 320 := by linarith
  have ha0 : 0 ≤ 1 - s / 3 := by linarith
  have ha1 : 1 - s / 3 ≤ 1 := by linarith
  have hl0 : 0 < left := by
    dsimp only [left, S]
    exact routeTContourLeft_pos
  have hlhalf : 1 / 2 ≤ left := by
    dsimp only [left, routeTContourLeft]
    linarith
  have hlone : left ≤ 1 := by
    dsimp only [left, S]
    exact routeTContourLeft_le_one hδ
  have hr0 : 0 < right := by
    dsimp only [right, S]
    linarith [routeTContourRight_gt_one A S]
  have hr2 : right ≤ 2 := by
    dsimp only [right, routeTContourRight, d]
    linarith
  have hH0 : 0 < H := by
    dsimp only [H]
    exact Real.rpow_pos_of_pos hN0 _
  have hH1 : 1 ≤ H := by
    dsimp only [H]
    exact Real.one_le_rpow hN1 ha0
  have hHN : H ≤ N := by
    dsimp only [H]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 ha1
  have hB1 : 1 ≤ B := by
    dsimp only [B]
    linarith
  have hB4 : B ≤ 4 * N := by
    dsimp only [B]
    linarith
  have hBsq : B ^ (2 : ℕ) ≤ 16 * N ^ (2 : ℕ) := by
    calc
      B ^ (2 : ℕ) ≤ (4 * N) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by linarith : 0 ≤ B) hB4 2
      _ = 16 * N ^ (2 : ℕ) := by ring
  have hU0 : 0 < U := by
    have hNpow : 0 < N ^ (4 : ℕ) := pow_pos hN0 4
    exact hNpow.trans_le hU
  have hMdMh : Md ≤ Mh := by
    dsimp only [Md, Mh, S]
    exact routeTContourRightBound_le_edgeBound A S
  have hMd0 : 0 ≤ Md := by
    dsimp only [Md, S, routeTContourRightBound]
    positivity
  have hMh1 : 1 ≤ Mh := by
    dsimp only [Mh, S, routeTContourEdgeBound]
    exact Real.one_le_exp (by positivity)
  have hBleft : B ^ left ≤ 4 * N ^ left := by
    have hmono := Real.rpow_le_rpow (by linarith : 0 ≤ B) hB4 hl0.le
    have hmul : (4 * N) ^ left = 4 ^ left * N ^ left := by
      rw [Real.mul_rpow (by norm_num) hN0.le]
    have hfour : (4 : ℝ) ^ left ≤ 4 :=
      Real.rpow_le_self_of_one_le (by norm_num) hlone
    rw [hmul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hN0.le _))
  have hBright : B ^ right ≤ 16 * N ^ (2 : ℕ) := by
    have hmono := Real.rpow_le_rpow_of_exponent_le hB1 hr2
    have hBsq : B ^ (2 : ℝ) = B ^ (2 : ℕ) := by norm_num [Real.rpow_natCast]
    rw [hBsq] at hmono
    calc
      B ^ right ≤ B ^ (2 : ℕ) := hmono
      _ ≤ (4 * N) ^ (2 : ℕ) := pow_le_pow_left₀ (by linarith : 0 ≤ B) hB4 2
      _ = 16 * N ^ (2 : ℕ) := by ring
  have hleftPower : N ^ left ≤ N ^ (1 - s / 3) := by
    have hexp : left ≤ 1 - s / 3 := by
      dsimp only [left, routeTContourLeft, s]
      linarith
    exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have hwidthSq : H ^ (2 : ℕ) = N ^ (2 - 2 * s / 3) := by
    dsimp only [H]
    exact routeT_rpow_width_sq hN0
  have hquot : N ^ (2 : ℕ) * N ^ left / H ^ (2 : ℕ) = N ^ (1 - s / 3) := by
    dsimp only [left, routeTContourLeft]
    dsimp only [H]
    exact routeT_rpow_left_quotient hN0
  have hdirect : 2 * ((x + H) ^ left / left) ≤ 16 * N ^ (1 - s / 3) := by
    have hxH0 : 0 ≤ x + H := by linarith
    have hxHB : x + H ≤ B := by dsimp only [B]; linarith
    have hxHpow : (x + H) ^ left ≤ B ^ left :=
      Real.rpow_le_rpow hxH0 hxHB hl0.le
    have hdiv : (x + H) ^ left / left ≤ 2 * (x + H) ^ left := by
      rw [div_le_iff₀ hl0]
      have hp0 : 0 ≤ (x + H) ^ left := Real.rpow_nonneg hxH0 left
      nlinarith
    calc
      2 * ((x + H) ^ left / left) ≤ 4 * (x + H) ^ left := by nlinarith
      _ ≤ 4 * B ^ left :=
        mul_le_mul_of_nonneg_left hxHpow (by norm_num : (0 : ℝ) ≤ 4)
      _ ≤ 4 * (4 * N ^ left) :=
        mul_le_mul_of_nonneg_left hBleft (by norm_num : (0 : ℝ) ≤ 4)
      _ = 16 * N ^ left := by ring
      _ ≤ 16 * N ^ (1 - s / 3) :=
        mul_le_mul_of_nonneg_left hleftPower (by norm_num : (0 : ℝ) ≤ 16)
  have hsmoothLeft :
      2 * (C / H ^ (2 : ℕ) * B ^ (2 : ℕ) * B ^ left) ≤
        128 * C * N ^ (1 - s / 3) := by
    have hcore : C / H ^ (2 : ℕ) * B ^ (2 : ℕ) * B ^ left ≤
        64 * C * (N ^ (2 : ℕ) * N ^ left / H ^ (2 : ℕ)) := by
      calc
        C / H ^ (2 : ℕ) * B ^ (2 : ℕ) * B ^ left ≤
            C / H ^ (2 : ℕ) * (16 * N ^ (2 : ℕ)) * (4 * N ^ left) := by
          gcongr
        _ = 64 * C * (N ^ (2 : ℕ) * N ^ left / H ^ (2 : ℕ)) := by ring
    rw [hquot] at hcore
    nlinarith
  have hverticalCore :
      C / H ^ (2 : ℕ) * B ^ (2 : ℕ) * B ^ right / U ≤ 256 * C := by
    have hHsq1 : 1 ≤ H ^ (2 : ℕ) := one_le_pow₀ hH1
    calc
      C / H ^ (2 : ℕ) * B ^ (2 : ℕ) * B ^ right / U ≤
          C / H ^ (2 : ℕ) * (16 * N ^ (2 : ℕ)) *
            (16 * N ^ (2 : ℕ)) / (N ^ (4 : ℕ)) := by
        gcongr
      _ = 256 * C / H ^ (2 : ℕ) := by
        field_simp [ne_of_gt hN0]
        ring
      _ ≤ 256 * C := by
        rw [div_le_iff₀ (pow_pos hH0 2)]
        nlinarith
  have hhorizontalCore :
      C' / H ^ (1 : ℕ) * B ^ (1 : ℕ) * B ^ right / U ≤ 64 * C' := by
    have hHN1 : 1 ≤ H * N := by nlinarith
    calc
      C' / H ^ (1 : ℕ) * B ^ (1 : ℕ) * B ^ right / U ≤
          C' / H * (4 * N) * (16 * N ^ (2 : ℕ)) / (N ^ (4 : ℕ)) := by
        norm_num
        gcongr
      _ = 64 * C' / (H * N) := by
        field_simp [ne_of_gt hN0, ne_of_gt hH0]
        ring
      _ ≤ 64 * C' := by
        rw [div_le_iff₀ (mul_pos hH0 hN0)]
        nlinarith
  have hspan : right - left ≤ 1 := by
    dsimp only [right, left, routeTContourRight, routeTContourLeft, d, s]
    linarith
  have hspan0 : 0 ≤ right - left := by
    dsimp only [right, left, S]
    exact sub_nonneg.mpr (routeTContourLeft_le_right hδ)
  have hNpower1 : 1 ≤ N ^ (1 - s / 3) := Real.one_le_rpow hN1 ha0
  have hvertical :
      2 * (Md * (C / H ^ 2 * B ^ 2 * B ^ right)) / U ≤
        512 * C * Mh * N ^ (1 - s / 3) := by
    have hcore := hverticalCore
    have hterm0 : 0 ≤ C / H ^ (2 : ℕ) * B ^ (2 : ℕ) * B ^ right / U := by
      positivity
    have hMh0 : 0 ≤ Mh := by linarith
    calc
      2 * (Md * (C / H ^ 2 * B ^ 2 * B ^ right)) / U =
          2 * Md * (C / H ^ 2 * B ^ 2 * B ^ right / U) := by ring
      _ ≤ 2 * Mh * (256 * C) := by
        have hfirst : Md * (C / H ^ 2 * B ^ 2 * B ^ right / U) ≤
            Mh * (C / H ^ 2 * B ^ 2 * B ^ right / U) :=
          mul_le_mul_of_nonneg_right hMdMh hterm0
        have hsecond : Mh * (C / H ^ 2 * B ^ 2 * B ^ right / U) ≤
            Mh * (256 * C) := mul_le_mul_of_nonneg_left hcore hMh0
        have hh := mul_le_mul_of_nonneg_left (hfirst.trans hsecond)
          (by norm_num : (0 : ℝ) ≤ 2)
        simpa only [mul_assoc] using hh
      _ = (512 * C * Mh) := by ring
      _ ≤ (512 * C * Mh) * N ^ (1 - s / 3) := by
        have hcoef0 : 0 ≤ 512 * C * Mh := by positivity
        have hh := mul_le_mul_of_nonneg_left hNpower1 hcoef0
        simpa only [mul_one] using hh
      _ = 512 * C * Mh * N ^ (1 - s / 3) := by ring
  have hhorizontal :
      Mh * (C' / H ^ 1 * B ^ 1 * B ^ right) / U ^ (0 + 1) * (right - left) ≤
        64 * C' * Mh * N ^ (1 - s / 3) := by
    have hcore := hhorizontalCore
    have hcore0 : 0 ≤ C' / H ^ (1 : ℕ) * B ^ (1 : ℕ) * B ^ right / U := by positivity
    have hMh0 : 0 ≤ Mh := by linarith
    have hbound0 : 0 ≤ Mh * (64 * C') := by positivity
    norm_num at hcore0 hcore ⊢
    calc
      Mh * (C' / H * B * B ^ right) / U * (right - left) =
          Mh * (C' / H * B * B ^ right / U) * (right - left) := by ring
      _ ≤ Mh * (64 * C') * (right - left) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcore hMh0) hspan0
      _ ≤ Mh * (64 * C') * 1 := mul_le_mul_of_nonneg_left hspan hbound0
      _ = 64 * C' * Mh := by ring
      _ ≤ (64 * C' * Mh) * N ^ (1 - s / 3) := by
        have hcoef0 : 0 ≤ 64 * C' * Mh := by positivity
        have hh := mul_le_mul_of_nonneg_left hNpower1 hcoef0
        simpa only [mul_one] using hh
      _ = 64 * C' * Mh * N ^ (1 - s / 3) := by ring
  have hleftTerm :
      Mh * (2 * ((x + H) ^ left / left) +
        2 * (C / H ^ 2 * B ^ 2 * B ^ left)) ≤
        (16 + 128 * C) * Mh * N ^ (1 - s / 3) := by
    have hsum : 2 * ((x + H) ^ left / left) +
        2 * (C / H ^ 2 * B ^ 2 * B ^ left) ≤
        (16 + 128 * C) * N ^ (1 - s / 3) := by
      calc
        2 * ((x + H) ^ left / left) +
            2 * (C / H ^ 2 * B ^ 2 * B ^ left) ≤
          16 * N ^ (1 - s / 3) + 128 * C * N ^ (1 - s / 3) :=
            add_le_add hdirect hsmoothLeft
        _ = (16 + 128 * C) * N ^ (1 - s / 3) := by ring
    have hsum0 : 0 ≤ 2 * ((x + H) ^ left / left) +
        2 * (C / H ^ 2 * B ^ 2 * B ^ left) := by positivity
    calc
      Mh * (2 * ((x + H) ^ left / left) + 2 * (C / H ^ 2 * B ^ 2 * B ^ left)) ≤
          Mh * ((16 + 128 * C) * N ^ (1 - s / 3)) :=
        mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ Mh)
      _ = (16 + 128 * C) * Mh * N ^ (1 - s / 3) := by ring
  have hsmoothTotal :
      routeTMoebiusSmoothBound A C C' δ x H τ U ≤
        (16 + 640 * C + 128 * C') * Mh * N ^ (1 - s / 3) := by
    unfold routeTMoebiusSmoothBound
    change
      2 * (Md * (C / H ^ 2 * B ^ 2 * B ^ right)) / U +
          Mh * (C' / H ^ 1 * B ^ 1 * B ^ right) / U ^ (0 + 1) * (right - left) +
        Mh * (C' / H ^ 1 * B ^ 1 * B ^ right) / U ^ (0 + 1) * (right - left) +
      Mh * (2 * ((x + H) ^ left / left) +
        2 * (C / H ^ 2 * B ^ 2 * B ^ left)) ≤ _
    calc
      2 * (Md * (C / H ^ 2 * B ^ 2 * B ^ right)) / U +
            Mh * (C' / H ^ 1 * B ^ 1 * B ^ right) / U ^ (0 + 1) * (right - left) +
          Mh * (C' / H ^ 1 * B ^ 1 * B ^ right) / U ^ (0 + 1) * (right - left) +
        Mh * (2 * ((x + H) ^ left / left) +
          2 * (C / H ^ 2 * B ^ 2 * B ^ left)) ≤
        512 * C * Mh * N ^ (1 - s / 3) +
            64 * C' * Mh * N ^ (1 - s / 3) +
          64 * C' * Mh * N ^ (1 - s / 3) +
        (16 + 128 * C) * Mh * N ^ (1 - s / 3) :=
          add_le_add (add_le_add (add_le_add hvertical hhorizontal) hhorizontal) hleftTerm
      _ = (16 + 640 * C + 128 * C') * Mh * N ^ (1 - s / 3) := by ring
  have hsmooth0 : 0 ≤ routeTMoebiusSmoothBound A C C' δ x H τ U := by
    unfold routeTMoebiusSmoothBound
    have hspan0 : 0 ≤ routeTContourRight A S - routeTContourLeft A δ S :=
      sub_nonneg.mpr (routeTContourLeft_le_right hδ)
    positivity
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hsharp : routeTMoebiusSharpBound A C C' δ x H τ U ≤
      (18 + 640 * C + 128 * C') * Mh * N ^ (1 - s / 3) := by
    unfold routeTMoebiusSharpBound
    have hdiv : routeTMoebiusSmoothBound A C C' δ x H τ U / (2 * Real.pi) ≤
        routeTMoebiusSmoothBound A C C' δ x H τ U := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi)]
      nlinarith
    have hH : H + 1 ≤ 2 * N ^ (1 - s / 3) := by
      dsimp only [H]
      nlinarith
    have hMhPow : N ^ (1 - s / 3) ≤ Mh * N ^ (1 - s / 3) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hMh1 (Real.rpow_nonneg hN0.le _)
    calc
      routeTMoebiusSmoothBound A C C' δ x H τ U / (2 * Real.pi) + (H + 1) ≤
          routeTMoebiusSmoothBound A C C' δ x H τ U + 2 * N ^ (1 - s / 3) :=
        add_le_add hdiv hH
      _ ≤ (16 + 640 * C + 128 * C') * Mh * N ^ (1 - s / 3) +
          2 * (Mh * N ^ (1 - s / 3)) := add_le_add hsmoothTotal
            (mul_le_mul_of_nonneg_left hMhPow (by norm_num))
      _ = (18 + 640 * C + 128 * C') * Mh * N ^ (1 - s / 3) := by ring
  have hconstant : 18 + 640 * C + 128 * C' ≤ routeTMoebiusPowerConstant C C' := by
    unfold routeTMoebiusPowerConstant
    linarith
  dsimp only [routeTMoebiusPowerWidth]
  dsimp only [S, s, H, Mh] at hsharp ⊢
  exact hsharp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hconstant (by positivity)) (by positivity))

/-- **Literal truncated Möbius atom with Route-T power saving.** -/
theorem exists_norm_LSeries_truncatedMoebius_dyadic_le_routeTPower :
    ∃ (A C C' δ : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < δ ∧
      ∀ (L q : ℕ) (c τ U : ℝ), 1 ≤ q → 2 ^ q ≤ L → 0 ≤ c →
      (((2 ^ q : ℕ) : ℝ)) ^ (4 : ℕ) ≤ U →
      routeTInverseBaseHeight + U ≤ |τ| →
      ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
          ((c : ℂ) + (τ : ℝ) * Complex.I)‖ ≤
        2 * routeTMoebiusPowerConstant C C' *
          routeTContourEdgeBound A (|τ| + U) *
          (((2 ^ q : ℕ) : ℝ)) ^
            (1 - c - routeTContourShift A δ (|τ| + U) / 3) := by
  obtain ⟨A, C, C', δ, hC, hC', hδ, hmain⟩ :=
    exists_norm_LSeries_truncatedMoebius_dyadic_le_routeT
  refine ⟨A, C, C', δ, hC, hC', hδ, ?_⟩
  intro L q c τ U hq hNL hc hU hsep
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let M : ℕ := min (2 ^ (q + 1)) (L + 1)
  let x : ℝ := (M : ℝ) - 1
  let S : ℝ := |τ| + U
  let s : ℝ := routeTContourShift A δ S
  let H : ℝ := routeTMoebiusPowerWidth A δ S N
  have hNnat : 2 ≤ 2 ^ q := by
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
  have hN : 2 ≤ N := by
    dsimp only [N]
    exact_mod_cast hNnat
  have hN0 : 0 < N := by linarith
  have hMN : 2 ^ q ≤ M := by
    dsimp only [M]
    apply le_min
    · rw [pow_succ]
      omega
    · omega
  have hM2 : 2 ≤ M := hNnat.trans hMN
  have hx0 : 0 < x := by
    dsimp only [x]
    have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    linarith
  have hMupper : M ≤ 2 * 2 ^ q := by
    calc
      M ≤ 2 ^ (q + 1) := min_le_left _ _
      _ = 2 * 2 ^ q := by rw [pow_succ]; ring
  have hxN : x ≤ 2 * N := by
    dsimp only [x, N]
    have hMr : (M : ℝ) ≤ ((2 * 2 ^ q : ℕ) : ℝ) := by exact_mod_cast hMupper
    push_cast at hMr ⊢
    linarith
  have hH0 : 0 < H := by
    dsimp only [H, routeTMoebiusPowerWidth]
    positivity
  have hU1 : 1 ≤ U := by
    have hNpow : 16 ≤ N ^ (4 : ℕ) := by nlinarith [sq_nonneg (N ^ 2 - 4)]
    linarith
  have hraw := hmain L q c τ H U hq hNL hc hH0 hU1 hsep
  have hsharp := routeTMoebiusSharpBound_le_power
    (A := A) (C := C) (C' := C') (δ := δ) (x := x) (N := N) (τ := τ) (U := U)
      hC hC' hδ hN hx0 hxN hU
  have hweight0 : 0 ≤ N ^ (-c) := Real.rpow_nonneg hN0.le _
  have hcompose :
      2 * routeTMoebiusSharpBound A C C' δ x H τ U * N ^ (-c) ≤
        2 * (routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S *
          N ^ (1 - s / 3)) * N ^ (-c) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa only [x, H, S, s] using hsharp)
        (by norm_num)) hweight0
  have hpow : N ^ (1 - s / 3) * N ^ (-c) = N ^ (1 - c - s / 3) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  calc
    ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
        ((c : ℂ) + (τ : ℝ) * Complex.I)‖ ≤
      2 * routeTMoebiusSharpBound A C C' δ x H τ U * N ^ (-c) := by
        simpa only [M, x, H, N] using hraw
    _ ≤ 2 * (routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S *
        N ^ (1 - s / 3)) * N ^ (-c) := hcompose
    _ = (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) *
        (N ^ (1 - s / 3) * N ^ (-c)) := by ring
    _ = 2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S *
        N ^ (1 - c - s / 3) := by rw [hpow]
    _ = 2 * routeTMoebiusPowerConstant C C' *
          routeTContourEdgeBound A (|τ| + U) *
          (((2 ^ q : ℕ) : ℝ)) ^
            (1 - c - routeTContourShift A δ (|τ| + U) / 3) := by rfl

end

end RHTower.Sieve
