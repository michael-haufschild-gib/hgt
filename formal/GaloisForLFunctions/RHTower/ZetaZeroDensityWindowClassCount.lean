import GaloisForLFunctions.RHTower.ZetaZeroDensityHypothesisClassCount

/-!
# The detector class count for a general ratio-`3/2` window

Parameters: a window exponent `0 < a ≤ 1`, the smoothing exponent `y = 3a/4`, a mollifier exponent
`0 < δ ≤ 1` and a power bound `M ≥ max(2, 2a/δ)`.  A Type I block `2^j ∈ [T^{δ/2}, T^y (log T)²]`
has a power `ℓ ≤ M` in `[T^a, T^{3a/2}(log T)⁴]` (`exists_pow_mem_window`).  For a fixed `σ` and an
exponent `E` with

* `(3a + κ)(1 - σ) ≤ E` for some `κ > 0` (the diagonal term with its logarithms), and
* either `1 + a(1 - 2σ) ≤ E` (mean value range) or `1 + a(4 - 6σ) ≤ E` with `a(3/2 - 2σ) < 0`
  (Huxley range with its threshold),

every class count is `≤ C (1 + log T)^B T^E` for large `T` (`exists_window_class_card_le`).
-/

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve

/-- **The power window.**  If `T^{δ/2} ≤ K ≤ T^{3a/4}(log T)²`, `M ≥ max(2, 2a/δ)` and
`log T ≥ 1`, some power `K^ℓ`, `1 ≤ ℓ ≤ M`, lies in `[T^a, T^{3a/2}(log T)⁴]`. -/
theorem exists_pow_mem_window {a δ T : ℝ} {M : ℕ} (ha0 : 0 < a) (hδ : 0 < δ)
    (hM : 2 * a / δ ≤ M) (hM2 : 2 ≤ M) (hT : 1 < T) (hlog1 : 1 ≤ Real.log T) {K : ℕ}
    (hK1 : T ^ (δ / 2) ≤ K) (hK2 : (K : ℝ) ≤ T ^ (3 * a / 4) * Real.log T ^ 2) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ M ∧ T ^ a ≤ (K : ℝ) ^ ℓ ∧
      (K : ℝ) ^ ℓ ≤ T ^ (3 * a / 2) * Real.log T ^ 4 := by
  classical
  have hT0 : 0 < T := by linarith
  have hK0 : 0 < (K : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 _) hK1
  by_cases hbig : T ^ (a / 2) ≤ K
  · refine ⟨2, by norm_num, hM2, ?_, ?_⟩
    · calc T ^ a = (T ^ (a / 2)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
        _ ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hbig 2
    · calc (K : ℝ) ^ 2 ≤ (T ^ (3 * a / 4) * Real.log T ^ 2) ^ 2 := pow_le_pow_left₀ hK0.le hK2 2
        _ = T ^ (3 * a / 2) * Real.log T ^ 4 := by
            rw [mul_pow, ← Real.rpow_natCast (T ^ (3 * a / 4)), ← Real.rpow_mul hT0.le, ← pow_mul]
            ring_nf
  · push Not at hbig
    have hMpow : T ^ a ≤ (K : ℝ) ^ M := by
      calc T ^ a ≤ T ^ (δ / 2 * M) := by
            apply Real.rpow_le_rpow_of_exponent_le hT.le
            have := mul_le_mul_of_nonneg_left hM (show (0 : ℝ) ≤ δ / 2 by positivity)
            rw [show δ / 2 * (2 * a / δ) = a by field_simp] at this
            exact this
        _ = (T ^ (δ / 2)) ^ M := by rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        _ ≤ (K : ℝ) ^ M := pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hK1 _
    have hex : ∃ ℓ, T ^ a ≤ (K : ℝ) ^ ℓ := ⟨_, hMpow⟩
    set ℓ := Nat.find hex with hℓ
    have hspec : T ^ a ≤ (K : ℝ) ^ ℓ := Nat.find_spec hex
    have hle : ℓ ≤ M := Nat.find_min' hex hMpow
    have hone : 1 < T ^ a := Real.one_lt_rpow hT ha0
    have hℓ1 : 1 ≤ ℓ := by
      by_contra h
      have h0 : ℓ = 0 := by omega
      rw [h0, pow_zero] at hspec
      linarith
    refine ⟨ℓ, hℓ1, hle, hspec, ?_⟩
    have hmin : ¬ T ^ a ≤ (K : ℝ) ^ (ℓ - 1) := Nat.find_min hex (by omega)
    push Not at hmin
    have hsplit : (K : ℝ) ^ ℓ = (K : ℝ) ^ (ℓ - 1) * K := by
      rw [← pow_succ]
      congr 1
      omega
    calc (K : ℝ) ^ ℓ = (K : ℝ) ^ (ℓ - 1) * K := hsplit
      _ ≤ T ^ a * T ^ (a / 2) := mul_le_mul hmin.le hbig.le hK0.le (Real.rpow_nonneg hT0.le _)
      _ = T ^ (3 * a / 2) := by rw [← Real.rpow_add hT0]; ring_nf
      _ ≤ T ^ (3 * a / 2) * Real.log T ^ 4 :=
          le_mul_of_one_le_right (Real.rpow_nonneg hT0.le _) (one_le_pow₀ hlog1)

/-- `T^{δ/2} ≤ 2^j` whenever `⌊T^δ⌋ < 2·2^j` and `T^{δ/2} ≥ 2`. -/
theorem rpow_half_le_of_moll_lt {δ T : ℝ} (hT1 : 1 ≤ T) (h2 : 2 ≤ T ^ (δ / 2)) {j : ℕ}
    (hj : pDetMoll δ T < 2 * 2 ^ j) : T ^ (δ / 2) ≤ ((2 ^ j : ℕ) : ℝ) := by
  have hT0 : 0 < T := by linarith
  have h1 : (pDetMoll δ T : ℝ) + 1 ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (show pDetMoll δ T + 1 ≤ 2 * 2 ^ j by omega)
  have h2' : T ^ δ < (pDetMoll δ T : ℝ) + 1 := by
    unfold pDetMoll
    exact Nat.lt_floor_add_one _
  have h4 : T ^ δ = T ^ (δ / 2) * T ^ (δ / 2) := by
    rw [← Real.rpow_add hT0]
    ring_nf
  have h5 : 2 * T ^ (δ / 2) ≤ T ^ δ := by
    rw [h4]
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hT0.le _)
  linarith

/-- The logarithmic exponent `6M + 3·2^{4M} + 1` of a window class count. -/
def windowLogExponent (M : ℕ) : ℕ := 6 * M + 3 * 2 ^ (4 * M) + 1

/-- The constant of a window class count. -/
def windowCountConstant (M : ℕ) : ℝ :=
  (2 ^ (M + 1) * (2 + 2 ^ (M + 2)) + classHuxleyConstantOf M)
    * ((M : ℝ) + 100) ^ windowLogExponent M

theorem windowCountConstant_nonneg (M : ℕ) : 0 ≤ windowCountConstant M := by
  unfold windowCountConstant
  have := classHuxleyConstantOf_nonneg M
  positivity

/-- **The class count for a ratio-`3/2` window at a fixed `σ`.** -/
theorem exists_window_class_card_le {a δ σ E κ : ℝ} {M : ℕ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hδ0 : 0 < δ) (hM : 2 * a / δ ≤ M) (hM2 : 2 ≤ M) (hκ : 0 < κ) (hσ0 : 1 / 2 ≤ σ)
    (hσ1 : σ ≤ 1) (hdiag : (3 * a + κ) * (1 - σ) ≤ E)
    (hreg : 1 + a * (1 - 2 * σ) ≤ E ∨ (1 + a * (4 - 6 * σ) ≤ E ∧ a * (3 / 2 - 2 * σ) < 0)) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (j i : ℕ) (σ' : ℝ), σ ≤ σ' → ∀ W : Finset ℝ,
        (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) →
        (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
        (∀ t ∈ W, 1 / (48 * (gDetBlockCount (pDetCut (3 * a / 4) T) : ℝ)) ≤
          ‖abscissaTaylorPoly (gDetBlock (pDetCut (3 * a / 4) T) j)
            (fun k => ((gDetCoeff (pDetMoll δ T) (pDetSmooth (3 * a / 4) T) k : ℝ) : ℂ))
            (gDetLog (pDetCut (3 * a / 4) T)) i σ' t‖) →
        (W.card : ℝ) ≤ windowCountConstant M * (1 + Real.log T) ^ windowLogExponent M * T ^ E := by
  set y : ℝ := 3 * a / 4 with hydef
  have hy0 : 0 < y := by rw [hydef]; positivity
  have hy1 : y ≤ 3 / 4 := by rw [hydef]; linarith
  set ν : ℝ := -(a * (3 / 2 - 2 * σ)) with hν
  obtain ⟨TH, hTH⟩ : ∃ TH : ℝ, ∀ T : ℝ, TH ≤ T → (0 < ν →
      3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M)
        * ((((M : ℝ) + 100) * (1 + Real.log T)) ^ (2 * M)
          * (((M : ℝ) + 100) * (1 + Real.log T)) ^ (2 ^ (4 * M))) ≤ T ^ ν) := by
    by_cases hν0 : 0 < ν
    · obtain ⟨TH, hTH⟩ := eventually_atTop.mp
        (eventually_const_mul_polylog_le_rpow (2 * M + 2 ^ (4 * M)) (c := ν) hν0
          (3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M) * ((M : ℝ) + 100) ^ (2 * M + 2 ^ (4 * M))))
      refine ⟨TH, fun T hT _ => ?_⟩
      have h := hTH T hT
      rw [← pow_add, mul_pow]
      calc 3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M)
            * (((M : ℝ) + 100) ^ (2 * M + 2 ^ (4 * M)) * (1 + Real.log T) ^ (2 * M + 2 ^ (4 * M)))
          = 3 * (M : ℝ) ^ 2 * 1537 * 2 ^ (2 * M) * ((M : ℝ) + 100) ^ (2 * M + 2 ^ (4 * M))
              * (1 + Real.log T) ^ (2 * M + 2 ^ (4 * M)) := by ring
        _ ≤ T ^ ν := h
    · exact ⟨0, fun T _ h => absurd h hν0⟩
  obtain ⟨TA, hTA⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 2 (c := 1 / 4) (by norm_num) 1)
  obtain ⟨TB, hTB⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 4 (c := 1 / 2) (by norm_num) 1)
  obtain ⟨TC, hTC⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 8 (c := κ) hκ 1)
  obtain ⟨TD, hTD⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0 : ℝ) < δ / 2 by positivity)).eventually_ge_atTop 2)
  refine ⟨max (max (max (Real.exp 1) 4) TH) (max TA (max TB (max TC TD))), ?_⟩
  intro T hT j i σ' hσσ' W hW hsep hbig
  have hTe : Real.exp 1 ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hT
  have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_right (Real.exp 1) 4)
    (le_trans (le_max_left _ TH) (le_trans (le_max_left _ _) hT))
  have hTTH : TH ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTTA : TA ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTTB : TB ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hT
  have hTTC : TC ≤ T := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hT
  have hTTD : TD ≤ T := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    exact hTe
  have hT2 : (2 : ℝ) ≤ T := by linarith
  have hA := hTA T hTTA
  have hB := hTB T hTTB
  have hC := hTC T hTTC
  simp only [one_mul] at hA hB hC
  have hlogsq : Real.log T ^ 2 ≤ T ^ (1 / 4 : ℝ) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 2) hA
  have hlog4 : Real.log T ^ 4 ≤ T ^ (1 / 2 : ℝ) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 4) hB
  have hlog8 : Real.log T ^ 8 ≤ T ^ κ :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 8) hC
  have hZT : T ^ y * Real.log T ^ 2 ≤ T := by
    calc T ^ y * Real.log T ^ 2 ≤ T ^ (3 / 4 : ℝ) * T ^ (1 / 4 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 hy1) hlogsq (by positivity)
            (Real.rpow_nonneg hT0.le _)
      _ = T := by rw [← Real.rpow_add hT0]; norm_num
  have hwin2 : T ^ (3 * a / 2) * Real.log T ^ 4 ≤ T ^ (2 : ℝ) := by
    calc T ^ (3 * a / 2) * Real.log T ^ 4 ≤ T ^ (3 / 2 : ℝ) * T ^ (1 / 2 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hlog4 (by positivity)
            (Real.rpow_nonneg hT0.le _)
      _ = T ^ (2 : ℝ) := by rw [← Real.rpow_add hT0]; norm_num
  set Zc := pDetCut y T with hZc
  have hZle : (Zc : ℝ) ≤ T ^ y * Real.log T ^ 2 := Nat.floor_le (by positivity)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = ((M : ℝ) + 100) * (1 + Real.log T) := ⟨_, rfl⟩
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hl1 : 1 ≤ 1 + Real.log T := by linarith only [hlog0]
  have hQM3 : ((M : ℝ) + 3) * (1 + Real.log T) ≤ Q := by
    rw [hQdef]; exact mul_le_mul_of_nonneg_right (by linarith only) (by linarith only [hl1])
  have hQlow : 36 * (1 + Real.log T) ≤ Q := by
    rw [hQdef]; exact mul_le_mul_of_nonneg_right (by linarith only [hM0]) (by linarith only [hl1])
  have hQ1 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ 36 * (1 + Real.log T) := by linarith only [hl1]
    linarith only [this, hQlow]
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ1
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Q ^ (2 ^ (4 * M)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPdef]; exact pow_nonneg hQ0.le _
  set R : ℝ := Q ^ (4 * M + 3 * 2 ^ (4 * M)) with hRdef
  have hcube : Q ^ (4 * M) * P ^ 3 ≤ R := by
    rw [hPdef, ← pow_mul, ← pow_add, hRdef, mul_comm (2 ^ (4 * M)) 3]
  have hsingle : P ≤ R := by
    rw [hPdef, hRdef]
    exact pow_le_pow_right₀ hQ1 (by omega)
  have hfinal : ∀ K : ℝ, 0 ≤ K →
      K ≤ 2 ^ (M + 1) * (2 + 2 ^ (M + 2)) + classHuxleyConstantOf M →
      ∀ e : ℕ, e ≤ windowLogExponent M →
      K * Q ^ e * T ^ E
        ≤ windowCountConstant M * (1 + Real.log T) ^ windowLogExponent M * T ^ E := by
    intro K hK0 hK e he
    have hQe : Q ^ e ≤ Q ^ windowLogExponent M := pow_le_pow_right₀ hQ1 he
    have hTE : 0 ≤ T ^ E := Real.rpow_nonneg hT0.le _
    have hKc : 0 ≤ 2 ^ (M + 1) * (2 + 2 ^ (M + 2)) + classHuxleyConstantOf M := by
      have := classHuxleyConstantOf_nonneg M
      positivity
    calc K * Q ^ e * T ^ E ≤ (2 ^ (M + 1) * (2 + 2 ^ (M + 2)) + classHuxleyConstantOf M)
          * Q ^ windowLogExponent M * T ^ E :=
          mul_le_mul_of_nonneg_right (mul_le_mul hK hQe (pow_nonneg hQ0.le _) hKc) hTE
      _ = windowCountConstant M * (1 + Real.log T) ^ windowLogExponent M * T ^ E := by
          rw [hQdef, mul_pow, windowCountConstant]
          ring
  rcases W.eq_empty_or_nonempty with hWe | ⟨t₀, ht₀⟩
  · rw [hWe, card_empty, Nat.cast_zero]
    have := windowCountConstant_nonneg M
    positivity
  set J := gDetBlockCount Zc with hJdef
  set V : ℝ := 1 / (48 * (J : ℝ)) with hVdef
  have hJpos : (0 : ℝ) < J := by
    rw [hJdef, gDetBlockCount]
    positivity
  have hV0 : 0 < V := by positivity
  obtain ⟨hjX, hjZ⟩ := gDetBlock_bounds_of_large hV0 (hbig t₀ ht₀)
  have hZ2 : 2 ≤ Zc := by
    have hTy : (2 : ℝ) ≤ T ^ y * Real.log T ^ 2 := by
      have hK1 := rpow_half_le_of_moll_lt hT1 (hTD T hTTD) hjX
      have hK2 : ((2 ^ j : ℕ) : ℝ) ≤ T ^ y * Real.log T ^ 2 :=
        le_trans (by exact_mod_cast hjZ) hZle
      linarith [hTD T hTTD]
    rw [hZc, pDetCut]
    exact Nat.le_floor (by exact_mod_cast hTy)
  have hJQ : 48 * (J : ℝ) ≤ Q := by
    have hZTR : (Zc : ℝ) ≤ T := le_trans hZle hZT
    have hJ2 := gDetBlockCount_le_log hZ2 hZTR
    rw [hQdef]
    calc 48 * (J : ℝ) ≤ 48 * (2 * (1 + Real.log T)) := by linarith only [hJ2]
      _ = 96 * (1 + Real.log T) := by ring
      _ ≤ ((M : ℝ) + 100) * (1 + Real.log T) :=
          mul_le_mul_of_nonneg_right (by linarith only [hM0]) (by linarith only [hlog0])
  have hVQ : 1 / Q ≤ V := by
    rw [hVdef]
    exact one_div_le_one_div_of_le (by positivity) hJQ
  set Λ := gDetLog Zc with hΛ
  set B := gDetBlock Zc j with hBdef
  set Xm := pDetMoll δ T with hXm
  set Ys := pDetSmooth y T with hYs
  have hXm1 : 1 ≤ Xm := one_le_pDetMoll hδ0.le hT1
  have hYs0 : 0 < Ys := lt_of_lt_of_le one_pos (one_le_pDetSmooth hy0.le hT1)
  have hB1 : ∀ k ∈ B, 1 ≤ k := fun k hk => (mem_gDetBlock_bounds hk).1
  have hBb : ∀ k ∈ B, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1 := fun k hk =>
    ⟨(mem_gDetBlock_bounds hk).2.2.1, (mem_gDetBlock_bounds hk).2.2.2⟩
  have hBΛ : ∀ k ∈ B, Real.log k ≤ Λ := by
    intro k hk
    have hk := mem_gDetBlock_bounds hk
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk.2.1)
  have hcoef : ∀ k ∈ B, |gDetCoeff Xm Ys k| ≤ k.divisors.card :=
    fun k _ => abs_gDetCoeff_le hXm1 hYs0 k
  have hbig' : ∀ t ∈ W, V ≤ ‖dpoly (genClassCoeff (gDetCoeff Xm Ys) Λ i σ') B t‖ := by
    intro t ht
    rw [← abscissaTaylorPoly_ofReal_eq_dpoly hB1]
    exact hbig t ht
  have hK1 := rpow_half_le_of_moll_lt hT1 (hTD T hTTD) hjX
  have hK2 : ((2 ^ j : ℕ) : ℝ) ≤ T ^ y * Real.log T ^ 2 :=
    le_trans (by exact_mod_cast hjZ) hZle
  obtain ⟨ℓ, hℓ1, hℓM, hX1, hX2⟩ := exists_pow_mem_window ha0 hδ0 hM hM2
    (lt_of_lt_of_le one_lt_two hT2) hlog1 hK1 hK2
  have hX2' : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ T ^ (2 : ℝ) := le_trans hX2 hwin2
  set X : ℝ := (((2 ^ j : ℕ) : ℝ)) ^ ℓ with hXdef
  have hXge1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast Nat.one_le_two_pow)
  have hσ0' : (0 : ℝ) ≤ σ := le_trans (by norm_num) hσ0
  have hmass₀ := classPowerMass_le_of_le (σ := σ) hT1 hℓM hX2'
  rw [← hXdef] at hmass₀
  have hPP : (((M : ℝ) + 3) * (1 + Real.log T)) ^ (2 ^ (4 * M)) ≤ P := by
    rw [hPdef]
    exact pow_le_pow_left₀ (by positivity) hQM3 _
  have hmass : classPowerMass j ℓ σ ≤ 2 ^ M * X ^ (1 - 2 * σ) * P :=
    le_trans hmass₀ (mul_le_mul_of_nonneg_left hPP (by positivity))
  have hLcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * X := by
    rw [hXdef]
    push_cast
    ring
  have hLM : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ 2 ^ M * X := by
    rw [hLcast]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hℓM) (by linarith)
  have hL1 : (1 : ℝ) ≤ (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by positivity)
  have hlogL : 1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ Q :=
    le_trans (one_add_log_raised_le_of_le hT1 hℓM hX2') hQM3
  have hVl : 1 / Q ^ M ≤ V ^ ℓ := by
    calc 1 / Q ^ M ≤ 1 / Q ^ ℓ := one_div_le_one_div_of_le (pow_pos hQ0 _)
          (pow_le_pow_right₀ hQ1 hℓM)
      _ = (1 / Q) ^ ℓ := by rw [one_div_pow]
      _ ≤ V ^ ℓ := pow_le_pow_left₀ (by positivity) hVQ ℓ
  have hG0 : 0 ≤ classPowerMass j ℓ σ := by unfold classPowerMass; positivity
  -- the diagonal term
  have hdiagX : X ^ (2 - 2 * σ) ≤ T ^ E := by
    have h1 : X ^ (2 - 2 * σ) ≤ (T ^ (3 * a / 2) * Real.log T ^ 4) ^ (2 - 2 * σ) :=
      Real.rpow_le_rpow (by linarith) hX2 (by linarith)
    have h2 : (T ^ (3 * a / 2) * Real.log T ^ 4) ^ (2 - 2 * σ) =
        T ^ (3 * a * (1 - σ)) * (Real.log T ^ 8) ^ (1 - σ) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hT0.le _) (by positivity), ← Real.rpow_mul hT0.le]
      congr 1
      · ring_nf
      · rw [← Real.rpow_natCast (Real.log T) 4, ← Real.rpow_natCast (Real.log T) 8,
          ← Real.rpow_mul hlog0, ← Real.rpow_mul hlog0]
        ring_nf
    have h3 : (Real.log T ^ 8) ^ (1 - σ) ≤ (T ^ κ) ^ (1 - σ) :=
      Real.rpow_le_rpow (by positivity) hlog8 (by linarith)
    have h4 : T ^ (3 * a * (1 - σ)) * (T ^ κ) ^ (1 - σ) = T ^ ((3 * a + κ) * (1 - σ)) := by
      rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
      ring_nf
    calc X ^ (2 - 2 * σ) ≤ T ^ (3 * a * (1 - σ)) * (Real.log T ^ 8) ^ (1 - σ) := h2 ▸ h1
      _ ≤ T ^ (3 * a * (1 - σ)) * (T ^ κ) ^ (1 - σ) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hT0.le _)
      _ = T ^ ((3 * a + κ) * (1 - σ)) := h4
      _ ≤ T ^ E := Real.rpow_le_rpow_of_exponent_le hT1 hdiag
  have hXlow : ∀ e : ℝ, e ≤ 0 → T * X ^ e ≤ T ^ (1 + a * e) := by
    intro e he
    calc T * X ^ e ≤ T * (T ^ a) ^ e :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hX1 he) hT0.le
      _ = T ^ (1 + a * e) := by rw [← Real.rpow_mul hT0.le, Real.rpow_add hT0, Real.rpow_one]
  rcases hreg with hmvtE | ⟨hhuxE, hthr⟩
  · -- the mean value range
    have hTa : T * X ^ (1 - 2 * σ) ≤ T ^ E :=
      le_trans (hXlow _ (by linarith)) (Real.rpow_le_rpow_of_exponent_le hT1 hmvtE)
    have hmvt := card_mul_pow_le_genClass_mvt (B := B) (c := gDetCoeff Xm Ys) (Λ := Λ) (i := i)
      hℓ1 hBb hBΛ hcoef hσ0' hσσ' hT0.le hV0.le hW hsep hbig'
    have hc := class_count_mvt_arith_of_le hT1 hXge1 hTa hdiagX hQ1 hP0 hL1 hLM hlogL hG0 hmass hVl
      (Nat.cast_nonneg _) hmvt
    refine le_trans hc ?_
    have hQP : Q ^ (2 * M) * Q * Q * P = Q ^ (2 * M + 2 + 2 ^ (4 * M)) := by
      rw [hPdef, ← pow_succ, ← pow_succ, ← pow_add]
    rw [hQP]
    refine hfinal _ (by positivity) ?_ _ ?_
    · have := classHuxleyConstantOf_nonneg M
      linarith
    · unfold windowLogExponent
      have := Nat.one_le_two_pow (n := 4 * M)
      omega
  · -- the Huxley range
    have hν0 : 0 < ν := by rw [hν]; linarith
    have h32 : (3 : ℝ) / 2 - 2 * σ < 0 := by
      by_contra h
      push Not at h
      have := mul_nonneg ha0.le h
      linarith
    have hXd : X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ T ^ (-ν) := by
      calc X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ (T ^ a) ^ ((3 : ℝ) / 2 - 2 * σ) :=
            Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hX1 h32.le
        _ = T ^ (-ν) := by rw [← Real.rpow_mul hT0.le, hν]; ring_nf
    have hX46 : T * X ^ (4 - 6 * σ) ≤ T ^ E :=
      le_trans (hXlow _ (by linarith)) (Real.rpow_le_rpow_of_exponent_le hT1 hhuxE)
    have hVlpos : 0 < V ^ ℓ := pow_pos hV0 ℓ
    have hℓRM : (ℓ : ℝ) ≤ M := by exact_mod_cast hℓM
    obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = ℓ / V ^ ℓ := ⟨_, rfl⟩
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
    have hU0 : 0 < U := by rw [hUdef]; positivity
    have hU : U ≤ M * Q ^ M := by
      rw [hUdef, div_le_iff₀ hVlpos]
      have h1 : 1 ≤ Q ^ M * V ^ ℓ := by
        have := mul_le_mul_of_nonneg_left hVl (pow_nonneg hQ0.le M)
        rwa [mul_one_div_cancel (pow_pos hQ0 _).ne'] at this
      calc (ℓ : ℝ) ≤ M * 1 := by linarith only [hℓRM]
        _ ≤ M * (Q ^ M * V ^ ℓ) := mul_le_mul_of_nonneg_left h1 hM0
        _ = M * Q ^ M * V ^ ℓ := by ring
    have hVU : V ^ ℓ / ℓ = 1 / U := by rw [hUdef, one_div_div]
    have hthr' := class_huxley_threshold_arith_of_le hT1 hXge1 hXd hQ1 hP0 hL1 hLM hmass hU0 hU
      (by rw [hPdef, hQdef]; exact hTH T hTTH hν0)
    rw [← hVU] at hthr'
    have hhux := card_mul_pow_le_genClass_huxley (B := B) (c := gDetCoeff Xm Ys) (Λ := Λ)
      (i := i) hℓ1 hBb hBΛ hcoef hσ0' hσσ' hT0.le hV0 hW hsep hbig' hthr'
    rw [hVU] at hhux
    have hc := class_count_huxley_arith_of_le hT1 hXge1 hX46 hdiagX hQ1 hQlow hP0 hcube
      hsingle hL1 hLM hG0 hmass hU0 hU hℓRM hhux
    refine le_trans hc ?_
    have hQB : Q ^ (2 * M) * R * Q = Q ^ windowLogExponent M := by
      rw [hRdef, ← pow_add, ← pow_succ, windowLogExponent]
      congr 1
      ring
    rw [hQB]
    refine hfinal _ (classHuxleyConstantOf_nonneg M) ?_ _ le_rfl
    have : (0 : ℝ) ≤ 2 ^ (M + 1) * (2 + 2 ^ (M + 2)) := by positivity
    linarith

end RHTower

end
