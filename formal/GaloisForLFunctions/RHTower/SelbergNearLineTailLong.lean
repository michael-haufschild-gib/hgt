import GaloisForLFunctions.RHTower.SelbergNearLineTailLength
import GaloisForLFunctions.RHTower.ZetaMollifiedWindowGateLong

/-!
# The mollified tail right of the line for lengths in `[U^{21/100}/2, U^{21/50}]`

Let `Ψ_N` be the Barban–Vehov mollifier, `P_N` its von Mangoldt head and `f_N = ζΨ_N − 1 − P_N`.
For `N = ⌊U^θ⌋`, `21/100 ≤ θ ≤ 21/50`, there is `C` such that for all large `U`, every `a > 0` with
`2a + 2 ≤ log U` and every `U/4 ≤ T₁ ≤ T₂ ≤ U/2`,

`∫_{T₁}^{T₂} ‖f_N(1/2 + a/log U + it)‖² dt ≤ C e^{−(2a+1)/14} (T₂ − T₁ + 2U^{99/100})`
(`exists_eventually_integral_hbMollifiedTail_rightShift_le_long`).

The three-lines argument of `SelbergNearLineTailLength` with three changes: the left line is
`Re s = 1/2 − 1/(2 log U)`, where `N^{1/log U} ≤ e^{21/50} ≤ 2` keeps the von Mangoldt head
bounded and the long Barban–Vehov gate (`exists_bv_window_bound_long`, `R = 1/2`) controls `ζΨ_N`;
the far windows use `N² ≤ U`; and the right line `‖f_N‖ ≤ 2/N` now gives `16/N² ≤ U^{−2/5}`, so
the interpolation weight `λ = (a + 1/2)/(log U (5/2 + 1/(2 log U)))` yields the saving
`e^{−(2a+1)/14}` in place of `e^{−(a+1)/600}`.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- The interpolated window bound with the right line `16/N² ≤ e^{−2L/5}`. -/
theorem rpow_window_interp_le_long {C₁ H N L r lam : ℝ} (hC₁ : 1 ≤ C₁) (hH : 0 < H)
    (hN : 0 < N) (hlam0 : 0 ≤ lam)
    (hNL : 16 / N ^ 2 ≤ Real.exp (-(2 * L / 5))) (hlamL : r ≤ lam * (2 * L / 5)) :
    (C₁ * H) ^ (1 - lam) * (16 * H / N ^ 2) ^ lam ≤ C₁ * H * Real.exp (-r) := by
  have hC0 : 0 ≤ C₁ := by linarith
  have h16 : (16 * H / N ^ 2) = (16 / N ^ 2) * H := by ring
  rw [h16, Real.mul_rpow hC0 hH.le, Real.mul_rpow (by positivity) hH.le]
  have hHH : H ^ (1 - lam) * H ^ lam = H := by
    rw [← Real.rpow_add hH, sub_add_cancel, Real.rpow_one]
  have hC : C₁ ^ (1 - lam) ≤ C₁ := by
    calc C₁ ^ (1 - lam) ≤ C₁ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hC₁ (by linarith)
      _ = C₁ := Real.rpow_one C₁
  have hE : (16 / N ^ 2) ^ lam ≤ Real.exp (-r) := by
    calc (16 / N ^ 2) ^ lam ≤ (Real.exp (-(2 * L / 5))) ^ lam :=
          Real.rpow_le_rpow (by positivity) hNL hlam0
      _ = Real.exp (-(2 * L / 5) * lam) := by rw [← Real.exp_mul]
      _ ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by linarith)
  calc C₁ ^ (1 - lam) * H ^ (1 - lam) * ((16 / N ^ 2) ^ lam * H ^ lam)
      = C₁ ^ (1 - lam) * (16 / N ^ 2) ^ lam * (H ^ (1 - lam) * H ^ lam) := by ring
    _ = C₁ ^ (1 - lam) * (16 / N ^ 2) ^ lam * H := by rw [hHH]
    _ ≤ C₁ * Real.exp (-r) * H := by gcongr
    _ = C₁ * H * Real.exp (-r) := by ring

theorem exp_twentyOne_fiftieths_le_two : Real.exp (21 / 50) ≤ 2 := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have := Real.log_two_gt_d9
  linarith

/-- The scale facts for lengths `e^{21L/100}/2 ≤ N ≤ e^{21L/50}`, `L ≥ 1000`. -/
theorem nearLine_length_facts_long {N : ℕ} {L : ℝ} (hL : 1000 ≤ L)
    (hNle : (N : ℝ) ≤ Real.exp (21 * L / 50)) (hNlo : Real.exp (21 * L / 100) / 2 ≤ N) :
    2 ≤ N ∧ 1 ≤ Real.log N ∧ 8 * N * (1 + Real.log N) ≤ Real.exp (99 / 100 * L) ∧
      (N : ℝ) ^ (2 * (1 / (2 * L))) ≤ 2 ∧ (N : ℝ) ^ 2 ≤ Real.exp L ∧
      16 / (N : ℝ) ^ 2 ≤ Real.exp (-(2 * L / 5)) := by
  have he5 := hundred_le_exp_five
  have hE5 : Real.exp 5 ≤ Real.exp (21 * L / 100) := Real.exp_le_exp.mpr (by linarith)
  have hL0 : 0 < L := by linarith
  have hN50 : (50 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN_le : Real.log N ≤ 21 * L / 50 := by
    have := Real.log_le_log hNpos hNle
    rwa [Real.log_exp] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  · have h1 : Real.exp 1 ≤ N := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  · have h1 : 8 * (N : ℝ) * (1 + Real.log N) ≤ 8 * Real.exp (21 * L / 50) * (1 + 21 * L / 50) := by
      have : 0 ≤ 1 + Real.log (N : ℝ) := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ N)
        linarith
      gcongr
    refine h1.trans ?_
    have h2 : Real.exp (99 / 100 * L) = Real.exp (21 * L / 50) * Real.exp (57 / 100 * L) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : 8 * (1 + 21 * L / 50) ≤ Real.exp (57 / 100 * L) := by
      have h := Real.add_one_le_exp (57 / 100 * L)
      have h' := Real.pow_div_factorial_le_exp (x := 57 / 100 * L) (by positivity) 2
      simp only [Nat.factorial] at h'
      norm_num at h'
      nlinarith
    rw [h2]
    nlinarith [Real.exp_pos (21 * L / 50)]
  · calc (N : ℝ) ^ (2 * (1 / (2 * L))) ≤ Real.exp (21 * L / 50) ^ (2 * (1 / (2 * L))) :=
          Real.rpow_le_rpow hNpos.le hNle (by positivity)
      _ = Real.exp (21 / 50) := by
          rw [← Real.exp_mul]
          congr 1
          field_simp
      _ ≤ 2 := exp_twentyOne_fiftieths_le_two
  · calc (N : ℝ) ^ 2 ≤ Real.exp (21 * L / 50) ^ 2 := pow_le_pow_left₀ hNpos.le hNle 2
      _ = Real.exp (21 * L / 25) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
  · have hN2 : Real.exp (21 * L / 50) / 4 ≤ (N : ℝ) ^ 2 := by
      have h2 : (Real.exp (21 * L / 100) / 2) ^ 2 = Real.exp (21 * L / 50) / 4 := by
        rw [div_pow, ← Real.exp_nat_mul]; ring_nf
      rw [← h2]
      exact pow_le_pow_left₀ (by positivity) hNlo 2
    have h64 : (64 : ℝ) ≤ Real.exp (L / 50) := by
      have : Real.exp 5 ≤ Real.exp (L / 50) := Real.exp_le_exp.mpr (by linarith)
      linarith
    rw [div_le_iff₀ (by positivity)]
    have hsplit : Real.exp (-(2 * L / 5)) * (Real.exp (21 * L / 50) / 4)
        = Real.exp (L / 50) / 4 := by
      rw [mul_div_assoc', ← Real.exp_add]; ring_nf
    have h1 : Real.exp (-(2 * L / 5)) * (Real.exp (21 * L / 50) / 4)
        ≤ Real.exp (-(2 * L / 5)) * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hN2 (Real.exp_pos _).le
    linarith

/-- The size bound `16 CW² e^{5L} e^{−e^{L/50}/256} ≤ 1`. -/
theorem sixteen_mul_exp_five_mul_exp_neg_le_one {CW L : ℝ} (hCW : 0 < CW)
    (hL : 1280000 * (5 + max 0 (Real.log (16 * CW ^ 2))) ≤ L) :
    16 * CW ^ 2 * Real.exp (5 * L) * Real.exp (-(Real.exp (L / 50) / 256)) ≤ 1 := by
  set K : ℝ := max 0 (Real.log (16 * CW ^ 2)) with hK
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKle : Real.log (16 * CW ^ 2) ≤ K := le_max_right _ _
  have hL1 : 1 ≤ L := by nlinarith
  have hsq : (L / 50) ^ 2 / 2 ≤ Real.exp (L / 50) := by
    have := Real.pow_div_factorial_le_exp (x := L / 50) (by linarith) 2
    simpa using this
  have hgrow : Real.log (16 * CW ^ 2) + 5 * L ≤ Real.exp (L / 50) / 256 := by
    have h1 : (5 + K) * L ≤ L ^ 2 / 1280000 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    have h2 : K + 5 * L ≤ (5 + K) * L := by nlinarith
    have h3 : (L / 50) ^ 2 / 2 / 256 = L ^ 2 / 1280000 := by ring
    linarith
  have hCW2 : 0 < 16 * CW ^ 2 := by positivity
  calc 16 * CW ^ 2 * Real.exp (5 * L) * Real.exp (-(Real.exp (L / 50) / 256))
      = Real.exp (Real.log (16 * CW ^ 2) + 5 * L - Real.exp (L / 50) / 256) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hCW2, Real.exp_neg]
        field_simp
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- The far-window key for `N² ≤ e^L`. -/
theorem nearLine_far_key_long {N : ℕ} {L CW τ : ℝ} (hCW : 0 < CW)
    (hLK : 1280000 * (5 + max 0 (Real.log (16 * CW ^ 2))) ≤ L)
    (hN2 : (N : ℝ) ^ 2 ≤ Real.exp L) (hτ : 1 + |τ| ≤ Real.exp L) :
    16 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2 *
      Real.exp (-((Real.exp L / 16) ^ 2 / Real.exp (99 / 100 * L) ^ 2)) ≤ 1 := by
  have hH2 : Real.exp (99 / 100 * L) ^ 2 = Real.exp (99 / 50 * L) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hDH : (Real.exp L / 16) ^ 2 / Real.exp (99 / 100 * L) ^ 2 = Real.exp (L / 50) / 256 := by
    have hL2 : Real.exp L ^ 2 = Real.exp (L / 50) * Real.exp (99 / 50 * L) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hH2, div_pow, hL2]
    field_simp
    ring
  have hprod : (N : ℝ) ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2 ≤ Real.exp (5 * L) := by
    have h1 : (1 + |τ|) ^ 2 ≤ Real.exp (2 * L) := by
      calc (1 + |τ|) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ (by positivity) hτ 2
        _ = Real.exp (2 * L) := by rw [← Real.exp_nat_mul]; ring_nf
    calc (N : ℝ) ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2 ≤
          Real.exp L * Real.exp (2 * L) * Real.exp (99 / 50 * L) := by
          rw [hH2]
          gcongr
      _ = Real.exp (249 / 50 * L) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (5 * L) := by
          have : 0 ≤ L := by nlinarith [le_max_left 0 (Real.log (16 * CW ^ 2))]
          exact Real.exp_le_exp.mpr (by linarith)
  have hsize := sixteen_mul_exp_five_mul_exp_neg_le_one hCW hLK
  rw [hDH]
  have hE := Real.exp_pos (-(Real.exp (L / 50) / 256))
  calc 16 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2 *
        Real.exp (-(Real.exp (L / 50) / 256))
      = 16 * CW ^ 2 * ((N : ℝ) ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2) *
        Real.exp (-(Real.exp (L / 50) / 256)) := by ring
    _ ≤ 16 * CW ^ 2 * Real.exp (5 * L) * Real.exp (-(Real.exp (L / 50) / 256)) := by gcongr
    _ ≤ 1 := hsize

/-- The gate hypothesis of the long left line: `d = 1/(2L)`, blocks above `e^{49L/50}`. -/
def LongLeftGate (N : ℕ) (L c₀ : ℝ) : Prop :=
  ∀ a' v : ℝ, 20 ≤ a' → Real.exp (49 / 50 * L) ≤ a' → a' ≤ v → v ≤ 2 * a' → v ≤ Real.exp L →
    (∫ τ in a'..v, ‖riemannZeta (displacedLinePt (1 / (2 * L)) τ) *
      edPoly (hbCoeff N) (Finset.Icc 1 N) (displacedLinePt (1 / (2 * L)) τ)‖ ^ 2) ≤
        (c₀ + 1) * (v - a' + 2 * a' ^ ((19 : ℝ) / 20))

/-- **Left windows on `Re s = 1/2 − 1/(2L)`** for the long lengths. -/
theorem nearLine_left_window_le_long {N : ℕ} {L c₀ CW CM τ : ℝ} (hc₀ : 0 ≤ c₀) (hCW : 0 < CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hCM : ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log N * (Real.log N + CM))
    (hL1000 : 1000 ≤ L) (hLK : 1280000 * (5 + max 0 (Real.log (16 * CW ^ 2))) ≤ L)
    (hNle : (N : ℝ) ≤ Real.exp (21 * L / 50)) (hNlo : Real.exp (21 * L / 100) / 2 ≤ N)
    (hgU : LongLeftGate N L c₀)
    (hτ1 : Real.exp L / 4 ≤ τ) (hτ2 : τ ≤ Real.exp L / 2 + Real.exp (99 / 100 * L)) (y : ℝ) :
    ∫ t in (τ - Real.exp (99 / 100 * L))..(τ + Real.exp (99 / 100 * L)),
      ‖nearLineWindowField N (Real.exp (99 / 100 * L)) τ
        (((1 / 2 - 1 / (2 * L) : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
        (18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1) * Real.exp (99 / 100 * L) := by
  have hL500 : 500 ≤ L := by linarith
  obtain ⟨hH6, hHU, hU95, -, hU160, -⟩ := nearLine_scale_facts hL500
  obtain ⟨hN2, hlogN1, hMVT, hNd, hN2U, -⟩ := nearLine_length_facts_long hL1000 hNle hNlo
  have h49 : Real.exp (49 / 50 * L) ≤ Real.exp L / 16 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    have h1 : Real.exp (49 / 50 * L) * Real.exp (L / 50) = Real.exp L := by
      rw [← Real.exp_add]; ring_nf
    have h2 : (16 : ℝ) ≤ Real.exp (L / 50) := by
      have := hundred_le_exp_five
      have : Real.exp 5 ≤ Real.exp (L / 50) := Real.exp_le_exp.mpr (by linarith)
      linarith
    nlinarith [Real.exp_pos (49 / 50 * L)]
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = Real.exp (99 / 100 * L) := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = Real.exp L := ⟨_, rfl⟩
  rw [← hHdef] at hH6 hHU hU95 hMVT hτ2 ⊢
  rw [← hUdef] at hHU hU95 hU160 hτ1 hτ2 h49
  unfold LongLeftGate at hgU
  rw [← hUdef] at hgU
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := by linarith
  have hsubst := intervalIntegral.integral_comp_add_left
    (fun u : ℝ => ‖nearLineWindowField N H τ
      (((1 / 2 - 1 / (2 * L) : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2) y
    (a := τ - H) (b := τ + H)
  rw [hsubst, show y + (τ + H) = (y + (τ - H)) + 2 * H by ring]
  have hC₁ : 0 ≤ 18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) := by positivity
  have h2L : 1 / (2 * L) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h2L0 : 0 < 1 / (2 * L) := by positivity
  rcases le_or_gt |y| (U / 8) with hy | hy
  · have hyabs := abs_le.mp hy
    have hα2 : y + (τ - H) + 2 * H ≤ U := by linarith
    have hgateα := hgU (y + (τ - H)) (y + (τ - H) + 2 * H) (by linarith) (by linarith)
      (by linarith) (by linarith) hα2
    have hα95 : 2 * (y + (τ - H)) ^ ((95 : ℝ) / 100) ≤ H := by
      have : (y + (τ - H)) ^ ((95 : ℝ) / 100) ≤ U ^ ((95 : ℝ) / 100) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      linarith
    have hNd' : (N : ℝ) ^ (2 * (1 / 2 - (1 / 2 - 1 / (2 * L)))) ≤ 2 := by
      rw [show 2 * (1 / 2 - (1 / 2 - 1 / (2 * L))) = 2 * (1 / (2 * L)) by ring]
      exact hNd
    have hE := sum_hbVonMangoldtCoeff_displaced_le (by omega) (by linarith) hNd' hlogN1 hCM
    have hgate' : ∫ u in (y + (τ - H))..(y + (τ - H) + 2 * H),
        ‖riemannZeta (((1 / 2 - 1 / (2 * L) : ℝ) : ℂ) + (u : ℂ) * I) *
          edPoly (hbCoeff N) (Finset.Icc 1 N)
            (((1 / 2 - 1 / (2 * L) : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          (c₀ + 1) * (y + (τ - H) + 2 * H - (y + (τ - H)) +
            2 * (y + (τ - H)) ^ ((95 : ℝ) / 100)) := by
      rw [show ((95 : ℝ) / 100) = (19 : ℝ) / 20 by norm_num]
      exact hgateα
    have h := integral_nearLineWindowField_left_gate_le (τ := τ) (by linarith)
      (σL := 1 / 2 - 1 / (2 * L)) (by linarith) (by linarith) (by linarith) hc₀ hgate' hα95
      hMVT hE
    refine h.trans ?_
    linarith
  · have hτU : 1 + |τ| ≤ Real.exp L := by
      rw [abs_of_pos (by linarith), ← hUdef]; linarith
    have hkey := nearLine_far_key_long hCW hLK hN2U hτU
    rw [← hHdef, ← hUdef] at hkey
    have h := integral_nearLineWindowField_left_far_le (τ := τ) (y := y)
      (σL := 1 / 2 - 1 / (2 * L)) (D := U / 16) (by linarith) hCW.le hW (by linarith)
      (by linarith) (by linarith) (by linarith) hkey
    refine h.trans ?_
    nlinarith

/-- **One window** for the long lengths. -/
theorem nearLine_window_le_long {N : ℕ} {L a c₀ CW CM τ : ℝ} (ha : 0 < a) (hc₀ : 0 ≤ c₀)
    (hCW : 0 < CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hCM : ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log N * (Real.log N + CM))
    (hL1000 : 1000 ≤ L) (hLa : 2 * a + 2 ≤ L)
    (hLK : 1280000 * (5 + max 0 (Real.log (16 * CW ^ 2))) ≤ L)
    (hNle : (N : ℝ) ≤ Real.exp (21 * L / 50)) (hNlo : Real.exp (21 * L / 100) / 2 ≤ N)
    (hgU : LongLeftGate N L c₀)
    (hτ1 : Real.exp L / 4 + Real.exp (99 / 100 * L) ≤ τ)
    (hτ2 : τ ≤ Real.exp L / 2 + Real.exp (99 / 100 * L)) :
    ∫ t in (τ - Real.exp (99 / 100 * L))..(τ + Real.exp (99 / 100 * L)),
      ‖hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        2 * Real.exp 2 * ((18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1) *
          Real.exp (99 / 100 * L) * Real.exp (-((2 * a + 1) / 14))) := by
  have hL500 : 500 ≤ L := by linarith
  obtain ⟨hH6, -, -, -, hU160, -⟩ := nearLine_scale_facts hL500
  obtain ⟨hN2, -, -, -, -, h16⟩ := nearLine_length_facts_long hL1000 hNle hNlo
  have hL0 : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have haL : a / L ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0]; linarith
  have haL0 : 0 < a / L := div_pos ha hL0
  have h2L0 : 0 < 1 / (2 * L) := by positivity
  have h2L : 1 / (2 * L) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hleft := nearLine_left_window_le_long hc₀ hCW hW hCM hL1000 hLK hNle hNlo hgU
    (τ := τ) (by linarith) hτ2
  have h := integral_hbMollifiedTail_window_le hN2 hH6 hCW.le hW (σL := 1 / 2 - 1 / (2 * L))
    (σ₀ := 1 / 2 + a / L) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by positivity) hleft
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hden : 3 - (1 / 2 - 1 / (2 * L)) = 5 / 2 + 1 / (2 * L) := by ring
  have hnum : 1 / 2 + a / L - (1 / 2 - 1 / (2 * L)) = (2 * a + 1) / (2 * L) := by
    field_simp; ring
  rw [hden, hnum]
  have hC₁ : 1 ≤ 18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1 := by
    have : 0 ≤ 18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) := by positivity
    linarith
  refine rpow_window_interp_le_long (L := L) hC₁ (by linarith) hNpos (by positivity) h16 ?_
  rw [div_div, show (2 * a + 1) / (2 * L * (5 / 2 + 1 / (2 * L))) * (2 * L / 5) =
    (2 * a + 1) / (5 * (5 / 2 + 1 / (2 * L))) by field_simp]
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have : 5 * (5 / 2 + 1 / (2 * L)) ≤ 14 := by linarith
  nlinarith

/-- **Core estimate** at one scale `U = e^L` for the long lengths. -/
theorem integral_hbMollifiedTail_rightShift_le_core_long {N : ℕ} {L a c₀ CW CM T₁ T₂ : ℝ}
    (ha : 0 < a) (hc₀ : 0 ≤ c₀) (hCW : 0 < CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hCM : ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log N * (Real.log N + CM))
    (hL1000 : 1000 ≤ L) (hLa : 2 * a + 2 ≤ L)
    (hLK : 1280000 * (5 + max 0 (Real.log (16 * CW ^ 2))) ≤ L)
    (hNle : (N : ℝ) ≤ Real.exp (21 * L / 50)) (hNlo : Real.exp (21 * L / 100) / 2 ≤ N)
    (hgU : LongLeftGate N L c₀)
    (hT₁ : Real.exp L / 4 ≤ T₁) (hT₁₂ : T₁ ≤ T₂) (hT₂ : T₂ ≤ Real.exp L / 2) :
    ∫ t in T₁..T₂, ‖hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Real.exp 2 * (18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1) *
        Real.exp (-((2 * a + 1) / 14)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)) := by
  have hL500 : 500 ≤ L := by linarith
  obtain ⟨hH6, -, -, -, hU160, -⟩ := nearLine_scale_facts hL500
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = Real.exp (99 / 100 * L) := ⟨_, rfl⟩
  have hH0 : 0 < H := by rw [hHdef]; exact Real.exp_pos _
  have hwin := fun τ (h1 : Real.exp L / 4 + Real.exp (99 / 100 * L) ≤ τ)
      (h2 : τ ≤ Real.exp L / 2 + Real.exp (99 / 100 * L)) =>
    nearLine_window_le_long (τ := τ) ha hc₀ hCW hW hCM hL1000 hLa hLK hNle hNlo hgU h1 h2
  rw [← hHdef] at hwin ⊢
  set C₁ : ℝ := 18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1 with hC₁def
  have hgc : ContinuousOn (fun t : ℝ =>
      ‖hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) (Ici T₁) := by
    have hT0 : 0 < T₁ := by linarith [Real.exp_pos L]
    intro t ht
    have hne : (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [ht.out]
    have hct : ContinuousAt (fun t : ℝ =>
        hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)) t :=
      ContinuousAt.comp (g := hbMollifiedTail N)
        (f := fun t : ℝ => (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I))
        (continuousAt_hbMollifiedTail hne) (by fun_prop)
    exact (hct.norm.pow 2).continuousWithinAt
  have hW0 : (0 : ℝ) ≤ 2 * Real.exp 2 * (C₁ * H * Real.exp (-((2 * a + 1) / 14))) := by
    have : 0 ≤ C₁ := by rw [hC₁def]; positivity
    positivity
  have hcover := integral_le_of_windows (g := fun t : ℝ =>
      ‖hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) hH0 hT₁₂
    (fun t => by positivity) hgc hW0
    (fun j hj => by
      have hj0 : (0 : ℝ) ≤ 2 * j * H := by positivity
      have h := hwin (T₁ + (2 * j + 1) * H) (by linarith) (by linarith)
      have e1 : T₁ + (2 * j + 1) * H - H = T₁ + 2 * j * H := by ring
      have e2 : T₁ + (2 * j + 1) * H + H = T₁ + 2 * ((j + 1 : ℕ) : ℝ) * H := by push_cast; ring
      rw [e1, e2] at h
      exact h)
  refine hcover.trans (le_of_eq ?_)
  field_simp

/-- **The mollified tail right of the critical line for the long length `⌊U^θ⌋`,
`21/100 ≤ θ ≤ 21/50`, uniformly in the displacement.** -/
theorem exists_eventually_integral_hbMollifiedTail_rightShift_le_long {θ : ℝ}
    (hθ0 : 21 / 100 ≤ θ) (hθ1 : θ ≤ 21 / 50) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U in Filter.atTop, ∀ a : ℝ, 0 < a → 2 * a + 2 ≤ Real.log U →
      ∀ T₁ T₂ : ℝ, U / 4 ≤ T₁ → T₁ ≤ T₂ → T₂ ≤ U / 2 →
      ∫ t in T₁..T₂, ‖hbMollifiedTail (ZetaGateProductAFE.bvLen θ U)
          (((1 / 2 + a / Real.log U : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C * Real.exp (-((2 * a + 1) / 14)) * (T₂ - T₁ + 2 * U ^ ((99 : ℝ) / 100)) := by
  have hθ5 : 1 / 5 ≤ θ := by linarith
  set c₀ : ℝ := ZetaGateProductAFE.bvLongStar (1 / 2) with hc₀def
  have hc₀ : 0 ≤ c₀ := ZetaGateProductAFE.bvLongStar_nonneg (by norm_num)
  have hgate := ZetaGateProductAFE.exists_bv_window_bound_long (R := 1 / 2) (by norm_num)
    hθ5 hθ1 1 one_pos
  obtain ⟨CW, hCW, hW⟩ := exists_norm_nearLineField_le
  obtain ⟨CM, hCM⟩ := exists_sum_vonMangoldt_sq_div_le
  refine ⟨Real.exp 2 * (18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1), by positivity, ?_⟩
  filter_upwards [hgate, Filter.eventually_ge_atTop (Real.exp
      (max 1000 (1280000 * (5 + max 0 (Real.log (16 * CW ^ 2))))))]
    with U hgU hUL₀
  intro a ha hLa T₁ T₂ hT₁ hT₁₂ hT₂
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hUL₀
  have hL := Real.log_le_log (Real.exp_pos _) hUL₀
  rw [Real.log_exp] at hL
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  have hUexp : U = Real.exp L := by rw [hLdef, Real.exp_log hU0]
  rw [← hLdef] at hL hLa
  subst hUexp
  simp only [Real.log_exp] at hgU ⊢
  have hL1000 : 1000 ≤ L := le_trans (le_max_left _ _) hL
  have hLK : 1280000 * (5 + max 0 (Real.log (16 * CW ^ 2))) ≤ L :=
    le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hUθ : Real.exp L ^ θ = Real.exp (θ * L) := by rw [← Real.exp_mul]; ring_nf
  have hU99 : Real.exp L ^ ((99 : ℝ) / 100) = Real.exp (99 / 100 * L) := by
    rw [← Real.exp_mul]; ring_nf
  have hNle : (ZetaGateProductAFE.bvLen θ (Real.exp L) : ℝ) ≤ Real.exp (21 * L / 50) := by
    refine (ZetaGateProductAFE.bvLen_le (Real.exp_pos L).le).trans ?_
    rw [hUθ]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hNlo : Real.exp (21 * L / 100) / 2 ≤ (ZetaGateProductAFE.bvLen θ (Real.exp L) : ℝ) := by
    have h2 : (2 : ℝ) ≤ Real.exp L ^ θ := by
      rw [hUθ]
      have : Real.exp 5 ≤ Real.exp (θ * L) := Real.exp_le_exp.mpr (by nlinarith)
      have := hundred_le_exp_five
      linarith
    refine le_trans ?_ (ZetaGateProductAFE.half_rpow_le_bvLen h2)
    rw [hUθ]
    have : Real.exp (21 * L / 100) ≤ Real.exp (θ * L) := Real.exp_le_exp.mpr (by nlinarith)
    linarith
  obtain ⟨hN2, -⟩ := nearLine_length_facts_long hL1000 hNle hNlo
  have hgN : LongLeftGate (ZetaGateProductAFE.bvLen θ (Real.exp L)) L c₀ := by
    intro a' v ha' haU hav hv2 hvU
    have hd8 : 1 / (2 * L) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hRd : 1 / 2 ≤ 1 / (2 * L) * L := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    have hdU1 : 1 / (2 * L) * Real.log (Real.exp L - 1) ≤ 1 / 2 := by
      have hlog : Real.log (Real.exp L - 1) ≤ L := by
        have := Real.log_le_log (by nlinarith [Real.add_one_le_exp L])
          (show Real.exp L - 1 ≤ Real.exp L by linarith)
        rwa [Real.log_exp] at this
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h49 : Real.exp L ^ ((49 : ℝ) / 50) ≤ a' := by
      rw [← Real.exp_mul]
      refine le_trans (le_of_eq ?_) haU
      ring_nf
    exact hgU (1 / (2 * L)) (by positivity) hd8 hRd hdU1 a' v ha' h49 hav hv2 hvU
  rw [hU99]
  exact integral_hbMollifiedTail_rightShift_le_core_long ha hc₀ hCW (hW _ hN2)
    (hCM _ (by omega)) hL1000 hLa hLK hNle hNlo hgN hT₁ hT₁₂ hT₂

end RHTower
