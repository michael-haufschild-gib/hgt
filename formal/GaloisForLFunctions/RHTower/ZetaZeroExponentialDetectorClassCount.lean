import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorClasses
import GaloisForLFunctions.RHTower.ZetaZeroDensityEdgeRanges

/-!
# The count of an exponential-detector class: exponent `12/5 + ε`

Let `0 < ε ≤ 1`.  For all large `T`, every `σ ∈ [1/2, 1]` and every Type I class `(j, i, σ')` with
`σ ≤ σ'`, a `1`-separated set `W ⊆ [T, 2T]` on which the class polynomial is at least `1/(48J)` has

`#W ≤ C (1 + log T)^E T^{(12/5 + ε)(1 - σ)}`.

The block `2^j` lies in `[T^{1/35}, T^{3/5}(log T)²]` (its coefficients vanish up to
`X = ⌊T^{1/30}⌋`), so a power `ℓ ≤ 34` puts `X' = (2^j)^ℓ` in `[T^{4/5}, T^{6/5}(log T)⁴]`
(`ℓ = 2` above `T^{2/5}`, the first power past `T^{4/5}` below).  Then:

* `X'^{2-2σ} ≤ T^{(12/5)(1-σ)} (log T)^{8(1-σ)} ≤ T^{(12/5+ε)(1-σ)}`;
* for `σ ≤ 3/4 + ε/8`, the mean value term `T X'^{1-2σ} ≤ T^{(9-8σ)/5} ≤ T^{(12/5+ε)(1-σ)}`;
* for `σ ≥ 3/4 + ε/8`, Huxley's threshold holds (`X'^{3/2-2σ} ≤ T^{-ε/5}`) and the Huxley term is
  `T X'^{4-6σ} ≤ T^{(21-24σ)/5} ≤ T^{(12/5)(1-σ)}`.

The arithmetic is that of `ZetaZeroDensityEdgeRanges` with an abstract exponent; the logarithmic
unit is `Q = 100(1 + log T)`, which dominates `48J`.
-/

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve

/-- The logarithmic exponent of the detector class count. -/
def expDetCountLogExponent : ℕ := 3 * 2 ^ 136 + 300

/-- The constant of the detector class count. -/
def expDetCountConstant : ℝ := 2 ^ 300 * 100 ^ expDetCountLogExponent

/-- The huge-exponent facts for `Q = 100(1 + log T)`, `P = Q^{2^{136}}`. -/
structure ExpDetBigFacts (Q P T δ : ℝ) : Prop where
  threshold : 3 * 34 ^ 2 * 1537 * 2 ^ 51 * (Q ^ 68 * P) ≤ T ^ δ
  meanValue : Q ^ 68 * Q * Q * P ≤ Q ^ expDetCountLogExponent
  cube : Q ^ 136 * P ^ 3 ≤ Q ^ (136 + 3 * 2 ^ 136)
  single : P ≤ Q ^ (136 + 3 * 2 ^ 136)
  huxley : Q ^ 68 * Q ^ (136 + 3 * 2 ^ 136) * Q ≤ Q ^ expDetCountLogExponent
  split : Q ^ expDetCountLogExponent
    = 100 ^ expDetCountLogExponent * (1 + Real.log T) ^ expDetCountLogExponent

theorem exists_expDetBigFacts {δ : ℝ} (hδ : 0 < δ) :
    ∃ TH : ℝ, ∀ T : ℝ, TH ≤ T → 1 ≤ T →
      ExpDetBigFacts (100 * (1 + Real.log T)) ((100 * (1 + Real.log T)) ^ (2 ^ 136)) T δ := by
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℕ, e₀ = 68 + 2 ^ 136 := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 3 * 34 ^ 2 * 1537 * 2 ^ 51 * 100 ^ e₀ := ⟨_, rfl⟩
  obtain ⟨TH, hTH⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow e₀ (c := δ) hδ c₀)
  refine ⟨TH, fun T hT hT1 => ?_⟩
  have hQ1 : 1 ≤ 100 * (1 + Real.log T) := by
    have := Real.log_nonneg hT1
    linarith
  have hQpow : ∀ a b : ℕ, a ≤ b → (100 * (1 + Real.log T)) ^ a ≤ (100 * (1 + Real.log T)) ^ b :=
    fun a b hab => pow_le_pow_right₀ hQ1 hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← pow_add, ← he₀, mul_pow, ← mul_assoc, ← hc₀]
    exact hTH T hT
  · rw [← pow_succ, ← pow_succ, ← pow_add]
    exact hQpow _ _ (by unfold expDetCountLogExponent; omega)
  · rw [← pow_mul, ← pow_add, mul_comm (2 ^ 136) 3]
  · exact hQpow _ _ (by omega)
  · rw [← pow_add, ← pow_succ]
    exact hQpow _ _ (by unfold expDetCountLogExponent; omega)
  · rw [mul_pow]

/-- The cutoff is at most `T^{3/5} (log T)²`. -/
theorem expDetCut_le {T : ℝ} (hT : 1 ≤ T) :
    (expDetCut T : ℝ) ≤ T ^ (3 / 5 : ℝ) * Real.log T ^ 2 :=
  Nat.floor_le (by have := Real.log_nonneg hT; positivity)

/-- `J ≤ 2(1 + log T)` once `T^{3/5}(log T)² ≤ T`. -/
theorem expDetBlockCount_le_log {T : ℝ} (hT4 : 4 ≤ T)
    (hZT : T ^ (3 / 5 : ℝ) * Real.log T ^ 2 ≤ T) :
    (expDetBlockCount T : ℝ) ≤ 2 * (1 + Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hZ := two_le_expDetCut hT4
  set m := expDetCut T with hm
  have hm0 : m ≠ 0 := by omega
  have hpow : ((2 : ℝ) ^ Nat.log 2 m) ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 hm0
  have hlog2 : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
    have := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at this
  have hmT : (m : ℝ) ≤ T := le_trans (expDetCut_le (by linarith)) hZT
  have hlogm : Real.log m ≤ Real.log T :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hm0) hmT
  have hl2 : (0.69 : ℝ) < Real.log 2 := Real.log_two_gt_d9.trans' (by norm_num)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hN : (Nat.log 2 m : ℝ) ≤ 2 * Real.log T := by
    have h2 : (Nat.log 2 m : ℝ) * 0.69 ≤ (Nat.log 2 m : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
    nlinarith
  unfold expDetBlockCount
  push_cast
  linarith

/-- **The power window.**  If `T^{1/35} ≤ K ≤ T^{3/5}(log T)²` and `log T ≥ 1`, then some power
`K^ℓ`, `1 ≤ ℓ ≤ 34`, lies in `[T^{4/5}, T^{6/5}(log T)⁴]`. -/
theorem exists_pow_mem_expDet_window {T : ℝ} (hT : 1 < T) (hlog1 : 1 ≤ Real.log T) {K : ℕ}
    (hK1 : T ^ (1 / 35 : ℝ) ≤ K) (hK2 : (K : ℝ) ≤ T ^ (3 / 5 : ℝ) * Real.log T ^ 2) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ 34 ∧ T ^ (4 / 5 : ℝ) ≤ (K : ℝ) ^ ℓ ∧
      (K : ℝ) ^ ℓ ≤ T ^ (6 / 5 : ℝ) * Real.log T ^ 4 := by
  classical
  have hT0 : 0 < T := by linarith
  have hK0 : 0 < (K : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 _) hK1
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT.le
  by_cases hbig : T ^ (2 / 5 : ℝ) ≤ K
  · refine ⟨2, by norm_num, by norm_num, ?_, ?_⟩
    · calc T ^ (4 / 5 : ℝ) = (T ^ (2 / 5 : ℝ)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
        _ ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hbig 2
    · calc (K : ℝ) ^ 2 ≤ (T ^ (3 / 5 : ℝ) * Real.log T ^ 2) ^ 2 :=
            pow_le_pow_left₀ hK0.le hK2 2
        _ = T ^ (6 / 5 : ℝ) * Real.log T ^ 4 := by
            rw [mul_pow, ← Real.rpow_natCast (T ^ (3 / 5 : ℝ)), ← Real.rpow_mul hT0.le, ← pow_mul]
            norm_num
  · push Not at hbig
    have h34 : T ^ (4 / 5 : ℝ) ≤ (K : ℝ) ^ (28 : ℕ) := by
      calc T ^ (4 / 5 : ℝ) = (T ^ (1 / 35 : ℝ)) ^ (28 : ℕ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
        _ ≤ (K : ℝ) ^ (28 : ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hK1 _
    have hex : ∃ ℓ, T ^ (4 / 5 : ℝ) ≤ (K : ℝ) ^ ℓ := ⟨28, h34⟩
    set ℓ := Nat.find hex with hℓ
    have hspec : T ^ (4 / 5 : ℝ) ≤ (K : ℝ) ^ ℓ := Nat.find_spec hex
    have hle : ℓ ≤ 28 := Nat.find_min' hex h34
    have hone : 1 < T ^ (4 / 5 : ℝ) := Real.one_lt_rpow hT (by norm_num)
    have hℓ1 : 1 ≤ ℓ := by
      by_contra h
      have h0 : ℓ = 0 := by omega
      rw [h0, pow_zero] at hspec
      linarith
    refine ⟨ℓ, hℓ1, by omega, hspec, ?_⟩
    have hmin : ¬ T ^ (4 / 5 : ℝ) ≤ (K : ℝ) ^ (ℓ - 1) := Nat.find_min hex (by omega)
    push Not at hmin
    have hsplit : (K : ℝ) ^ ℓ = (K : ℝ) ^ (ℓ - 1) * K := by
      rw [← pow_succ]
      congr 1
      omega
    calc (K : ℝ) ^ ℓ = (K : ℝ) ^ (ℓ - 1) * K := hsplit
      _ ≤ T ^ (4 / 5 : ℝ) * T ^ (2 / 5 : ℝ) :=
          mul_le_mul hmin.le hbig.le hK0.le (Real.rpow_nonneg hT0.le _)
      _ = T ^ (6 / 5 : ℝ) := by rw [← Real.rpow_add hT0]; norm_num
      _ ≤ T ^ (6 / 5 : ℝ) * Real.log T ^ 4 :=
          le_mul_of_one_le_right (Real.rpow_nonneg hT0.le _) (one_le_pow₀ hlog1)

/-! ## Exponent comparisons in the window `[T^{4/5}, T^{6/5}(log T)⁴]` -/

/-- `X^{2-2σ} ≤ T^{(12/5+ε)(1-σ)}` for `X ≤ T^{6/5}(log T)⁴` once `(log T)⁸ ≤ T^ε`. -/
theorem expDet_window_diagonal_le {T X σ ε : ℝ} (hT : 1 ≤ T) (hX0 : 0 ≤ X)
    (hX2 : X ≤ T ^ (6 / 5 : ℝ) * Real.log T ^ 4) (hσ : σ ≤ 1)
    (hlogε : Real.log T ^ 8 ≤ T ^ ε) :
    X ^ (2 - 2 * σ) ≤ T ^ ((12 / 5 + ε) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  have hl0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have h1 : X ^ (2 - 2 * σ) ≤ (T ^ (6 / 5 : ℝ) * Real.log T ^ 4) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow hX0 hX2 (by linarith)
  have h2 : (T ^ (6 / 5 : ℝ) * Real.log T ^ 4) ^ (2 - 2 * σ) =
      T ^ ((12 / 5) * (1 - σ)) * (Real.log T ^ 8) ^ (1 - σ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hT0.le _) (by positivity), ← Real.rpow_mul hT0.le]
    congr 1
    · ring_nf
    · rw [← Real.rpow_natCast (Real.log T) 4, ← Real.rpow_natCast (Real.log T) 8,
        ← Real.rpow_mul hl0, ← Real.rpow_mul hl0]
      ring_nf
  have h3 : (Real.log T ^ 8) ^ (1 - σ) ≤ (T ^ ε) ^ (1 - σ) :=
    Real.rpow_le_rpow (by positivity) hlogε (by linarith)
  have h4 : T ^ ((12 / 5) * (1 - σ)) * (T ^ ε) ^ (1 - σ) = T ^ ((12 / 5 + ε) * (1 - σ)) := by
    rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
    ring_nf
  calc X ^ (2 - 2 * σ) ≤ T ^ ((12 / 5) * (1 - σ)) * (Real.log T ^ 8) ^ (1 - σ) := h2 ▸ h1
    _ ≤ T ^ ((12 / 5) * (1 - σ)) * (T ^ ε) ^ (1 - σ) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hT0.le _)
    _ = T ^ ((12 / 5 + ε) * (1 - σ)) := h4

theorem expDet_rpow_window_lower {T X a : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (4 / 5 : ℝ) ≤ X)
    (ha : a ≤ 0) : X ^ a ≤ T ^ ((4 / 5) * a) := by
  have hT0 : 0 < T := by linarith
  calc X ^ a ≤ (T ^ (4 / 5 : ℝ)) ^ a :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hX1 ha
    _ = T ^ ((4 / 5) * a) := by rw [← Real.rpow_mul hT0.le]

/-- The mean value term for `1/2 ≤ σ ≤ 3/4 + ε/8`. -/
theorem expDet_mvt_term_le {T X σ ε : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (4 / 5 : ℝ) ≤ X)
    (hσ0 : 1 / 2 ≤ σ) (hσ : σ ≤ 3 / 4 + ε / 8) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    T * X ^ (1 - 2 * σ) ≤ T ^ ((12 / 5 + ε) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  calc T * X ^ (1 - 2 * σ) ≤ T * T ^ ((4 / 5) * (1 - 2 * σ)) :=
        mul_le_mul_of_nonneg_left (expDet_rpow_window_lower hT hX1 (by linarith)) hT0.le
    _ = T ^ (1 + (4 / 5) * (1 - 2 * σ)) := by rw [Real.rpow_add hT0, Real.rpow_one]
    _ ≤ T ^ ((12 / 5 + ε) * (1 - σ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hT
        nlinarith

/-- The Huxley term for `σ ≥ 3/4`. -/
theorem expDet_huxley_term_le {T X σ ε : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (4 / 5 : ℝ) ≤ X)
    (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hε : 0 ≤ ε) :
    T * X ^ (4 - 6 * σ) ≤ T ^ ((12 / 5 + ε) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  calc T * X ^ (4 - 6 * σ) ≤ T * T ^ ((4 / 5) * (4 - 6 * σ)) :=
        mul_le_mul_of_nonneg_left (expDet_rpow_window_lower hT hX1 (by linarith)) hT0.le
    _ = T ^ (1 + (4 / 5) * (4 - 6 * σ)) := by rw [Real.rpow_add hT0, Real.rpow_one]
    _ ≤ T ^ ((12 / 5 + ε) * (1 - σ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hT
        nlinarith

/-- Huxley's threshold decay for `σ ≥ 3/4 + ε/8`. -/
theorem expDet_huxley_decay_le {T X σ ε : ℝ} (hT : 1 ≤ T) (hX1 : T ^ (4 / 5 : ℝ) ≤ X)
    (hXge : 1 ≤ X) (hε : 0 ≤ ε) (hσ : 3 / 4 + ε / 8 ≤ σ) :
    X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ T ^ (-(ε / 5)) := by
  calc X ^ ((3 : ℝ) / 2 - 2 * σ) ≤ X ^ (-(ε / 4)) :=
        Real.rpow_le_rpow_of_exponent_le hXge (by linarith)
    _ ≤ T ^ ((4 / 5) * (-(ε / 4))) := expDet_rpow_window_lower hT hX1 (by linarith)
    _ = T ^ (-(ε / 5)) := by ring_nf

/-! ## The class count -/

/-- A block with a large class value has a nonzero coefficient, so `X < 2·2^j ≤ 2Z`. -/
theorem expDetBlock_bounds_of_large {T : ℝ} {j i : ℕ} {Λ σ' t V : ℝ} (hV : 0 < V)
    (hbig : V ≤ ‖abscissaTaylorPoly (expDetBlock T j) (fun k => ((expDetCoeff T k : ℝ) : ℂ))
      Λ i σ' t‖) :
    expDetMoll T < 2 * 2 ^ j ∧ 2 ^ j ≤ expDetCut T := by
  have hne : ∃ k ∈ expDetBlock T j, expDetCoeff T k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : abscissaTaylorPoly (expDetBlock T j) (fun k => ((expDetCoeff T k : ℝ) : ℂ))
        Λ i σ' t = 0 := by
      unfold abscissaTaylorPoly
      refine Finset.sum_eq_zero fun k hk => ?_
      simp [hcon k hk]
    rw [hzero, norm_zero] at hbig
    linarith
  obtain ⟨k, hk, hkne⟩ := hne
  have hb := mem_expDetBlock_bounds hk
  exact ⟨expDetMoll_lt_of_coeff_ne_zero hk hkne, le_trans hb.2.2.1 hb.2.1⟩

/-- `T^{1/35} ≤ 2^j` whenever `X < 2·2^j` and `T ≥ 2^{210}`. -/
theorem rpow_one_div_thirtyFive_le_of_moll_lt {T : ℝ} (hT : (2 : ℝ) ^ (210 : ℕ) ≤ T) {j : ℕ}
    (hj : expDetMoll T < 2 * 2 ^ j) : T ^ (1 / 35 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hT1 : 1 ≤ T := le_trans (one_le_pow₀ (by norm_num)) hT
  have h1 : (expDetMoll T : ℝ) + 1 ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (show expDetMoll T + 1 ≤ 2 * 2 ^ j by omega)
  have h2 : T ^ (1 / 30 : ℝ) < (expDetMoll T : ℝ) + 1 := by
    unfold expDetMoll
    exact Nat.lt_floor_add_one _
  have h3 : 2 ≤ T ^ (1 / 210 : ℝ) := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (210 : ℕ)) ^ (1 / 210 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ T ^ (1 / 210 : ℝ) := Real.rpow_le_rpow (by positivity) hT (by norm_num)
  have h4 : T ^ (1 / 30 : ℝ) = T ^ (1 / 210 : ℝ) * T ^ (1 / 35 : ℝ) := by
    rw [← Real.rpow_add hT0]
    norm_num
  have h5 : 2 * T ^ (1 / 35 : ℝ) ≤ T ^ (1 / 30 : ℝ) := by
    rw [h4]
    exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hT0.le _)
  linarith

/-- **The detector class count with exponent `12/5 + ε`.** -/
theorem exists_expDet_class_card_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ (j i : ℕ) (σ' : ℝ), σ ≤ σ' → ∀ W : Finset ℝ,
        (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) →
        (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
        (∀ t ∈ W, 1 / (48 * (expDetBlockCount T : ℝ)) ≤
          ‖abscissaTaylorPoly (expDetBlock T j) (fun k => ((expDetCoeff T k : ℝ) : ℂ))
            (expDetLog T) i σ' t‖) →
        (W.card : ℝ) ≤ expDetCountConstant * (1 + Real.log T) ^ expDetCountLogExponent
          * T ^ ((12 / 5 + ε) * (1 - σ)) := by
  obtain ⟨TH, hTH⟩ := exists_expDetBigFacts (show (0 : ℝ) < ε / 5 by positivity)
  obtain ⟨TA, hTA⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 2 (c := 2 / 5) (by norm_num) 1)
  obtain ⟨TB, hTB⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 4 (c := 2 / 15) (by norm_num) 1)
  obtain ⟨TC, hTC⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow 8 (c := ε) hε 1)
  refine ⟨max (max ((2 : ℝ) ^ (210 : ℕ)) TH) (max TA (max TB TC)), ?_⟩
  intro T hT σ hσ1 hσ2 j i σ' hσσ' W hW hsep hbig
  have hT210 : (2 : ℝ) ^ (210 : ℕ) ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTTH : TH ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTTA : TA ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTTB : TB ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hT
  have hTTC : TC ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hT
  have hT4 : (4 : ℝ) ≤ T := le_trans (by norm_num) hT210
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  -- the polylogarithmic comparisons
  have hA := hTA T hTTA
  have hB := hTB T hTTB
  have hC := hTC T hTTC
  simp only [one_mul] at hA hB hC
  have hlogsq : Real.log T ^ 2 ≤ T ^ (2 / 5 : ℝ) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 2) hA
  have hlog4 : Real.log T ^ 4 ≤ T ^ (2 / 15 : ℝ) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 4) hB
  have hlog8 : Real.log T ^ 8 ≤ T ^ ε :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 8) hC
  have hZT : T ^ (3 / 5 : ℝ) * Real.log T ^ 2 ≤ T := by
    calc T ^ (3 / 5 : ℝ) * Real.log T ^ 2 ≤ T ^ (3 / 5 : ℝ) * T ^ (2 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_left hlogsq (Real.rpow_nonneg hT0.le _)
      _ = T := by rw [← Real.rpow_add hT0]; norm_num
  have hwin43 : T ^ (6 / 5 : ℝ) * Real.log T ^ 4 ≤ T ^ (4 / 3 : ℝ) := by
    calc T ^ (6 / 5 : ℝ) * Real.log T ^ 4 ≤ T ^ (6 / 5 : ℝ) * T ^ (2 / 15 : ℝ) :=
          mul_le_mul_of_nonneg_left hlog4 (Real.rpow_nonneg hT0.le _)
      _ = T ^ (4 / 3 : ℝ) := by rw [← Real.rpow_add hT0]; norm_num
  have hBig := hTH T hTTH hT1
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 100 * (1 + Real.log T) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Q ^ (2 ^ 136) := ⟨_, rfl⟩
  rw [← hQdef, ← hPdef] at hBig
  have hQlow : 36 * (1 + Real.log T) ≤ Q := by rw [hQdef]; linarith
  have hQ1 : 1 ≤ Q := by rw [hQdef]; linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ1
  have hP0 : 0 ≤ P := by rw [hPdef]; exact pow_nonneg hQ0.le _
  set J := expDetBlockCount T with hJdef
  have hJpos : (0 : ℝ) < J := by
    rw [hJdef, expDetBlockCount]
    positivity
  have hJQ : 48 * (J : ℝ) ≤ Q := by
    have := expDetBlockCount_le_log hT4 hZT
    rw [hQdef]
    linarith
  set V : ℝ := 1 / (48 * (J : ℝ)) with hVdef
  have hV0 : 0 < V := by positivity
  have hVQ : 1 / Q ≤ V := by
    rw [hVdef]
    exact one_div_le_one_div_of_le (by positivity) hJQ
  rcases W.eq_empty_or_nonempty with hWe | ⟨t₀, ht₀⟩
  · rw [hWe, card_empty, Nat.cast_zero]
    unfold expDetCountConstant
    have hl : 0 ≤ 1 + Real.log T := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
      (pow_nonneg hl _)) (Real.rpow_nonneg hT0.le _)
  set Λ := expDetLog T with hΛ
  set B := expDetBlock T j with hBdef
  have hB1 : ∀ k ∈ B, 1 ≤ k := fun k hk => (mem_expDetBlock_bounds hk).1
  have hBb : ∀ k ∈ B, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1 := fun k hk =>
    ⟨(mem_expDetBlock_bounds hk).2.2.1, (mem_expDetBlock_bounds hk).2.2.2⟩
  have hBΛ : ∀ k ∈ B, Real.log k ≤ Λ := by
    intro k hk
    have hk := mem_expDetBlock_bounds hk
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk.2.1)
  have hcoef : ∀ k ∈ B, |expDetCoeff T k| ≤ k.divisors.card := fun k _ => abs_expDetCoeff_le hT1 k
  have hbig' : ∀ t ∈ W, V ≤ ‖dpoly (genClassCoeff (expDetCoeff T) Λ i σ') B t‖ := by
    intro t ht
    rw [← abscissaTaylorPoly_ofReal_eq_dpoly hB1]
    exact hbig t ht
  obtain ⟨hjX, hjZ⟩ := expDetBlock_bounds_of_large hV0 (hbig t₀ ht₀)
  have hK1 := rpow_one_div_thirtyFive_le_of_moll_lt hT210 hjX
  have hK2 : ((2 ^ j : ℕ) : ℝ) ≤ T ^ (3 / 5 : ℝ) * Real.log T ^ 2 :=
    le_trans (by exact_mod_cast hjZ) (expDetCut_le hT1)
  obtain ⟨ℓ, hℓ1, hℓ34, hX1, hX2⟩ := exists_pow_mem_expDet_window
    (lt_of_lt_of_le one_lt_two (by linarith : (2 : ℝ) ≤ T)) hlog1 hK1 hK2
  have hX2' : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ T ^ (4 / 3 : ℝ) := le_trans hX2 hwin43
  set X : ℝ := (((2 ^ j : ℕ) : ℝ)) ^ ℓ with hXdef
  have hXge1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast Nat.one_le_two_pow)
  have hσ0 : (0 : ℝ) ≤ σ := le_trans (by norm_num) hσ1
  have hmass₀ := classPowerMass_le (σ := σ) hT1 hℓ1 hℓ34 hX2'
  rw [← hXdef] at hmass₀
  have hPP : (36 * (1 + Real.log T)) ^ (2 ^ 136) ≤ P := by
    rw [hPdef]
    exact pow_le_pow_left₀ (by linarith) hQlow _
  have hmass : classPowerMass j ℓ σ ≤ 2 ^ 34 * X ^ (1 - 2 * σ) * P :=
    le_trans hmass₀ (mul_le_mul_of_nonneg_left hPP (by positivity))
  have hLcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * X := by
    rw [hXdef]
    push_cast
    ring
  have hL34 : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ 2 ^ 34 * X := by
    rw [hLcast]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hℓ34) (by linarith)
  have hL1 : (1 : ℝ) ≤ (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by positivity)
  have hlogL : 1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ Q :=
    le_trans (one_add_log_raised_le hT1 hℓ34 hX2') hQlow
  have hVl : 1 / Q ^ 34 ≤ V ^ ℓ := by
    calc 1 / Q ^ 34 ≤ 1 / Q ^ ℓ := one_div_le_one_div_of_le (pow_pos hQ0 _)
          (pow_le_pow_right₀ hQ1 hℓ34)
      _ = (1 / Q) ^ ℓ := by rw [one_div_pow]
      _ ≤ V ^ ℓ := pow_le_pow_left₀ (by positivity) hVQ ℓ
  have hG0 : 0 ≤ classPowerMass j ℓ σ := by unfold classPowerMass; positivity
  have hdiag := expDet_window_diagonal_le hT1 (by linarith) hX2 hσ2 hlog8
  clear_value J V X Λ B
  clear hQdef hPdef
  have hl : 0 ≤ 1 + Real.log T := by linarith
  have hfinal : ∀ K : ℝ, 0 ≤ K → K ≤ 2 ^ 300 →
      K * Q ^ expDetCountLogExponent * T ^ ((12 / 5 + ε) * (1 - σ))
        ≤ expDetCountConstant * (1 + Real.log T) ^ expDetCountLogExponent
          * T ^ ((12 / 5 + ε) * (1 - σ)) := by
    intro K hK0 hK
    rw [hBig.split]
    unfold expDetCountConstant
    have e : K * (100 ^ expDetCountLogExponent * (1 + Real.log T) ^ expDetCountLogExponent)
        * T ^ ((12 / 5 + ε) * (1 - σ)) = K * 100 ^ expDetCountLogExponent
          * (1 + Real.log T) ^ expDetCountLogExponent * T ^ ((12 / 5 + ε) * (1 - σ)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (pow_nonneg (by norm_num) _)) (pow_nonneg hl _))
      (Real.rpow_nonneg hT0.le _)
  by_cases hcase : σ ≤ 3 / 4 + ε / 8
  · have hmvt := card_mul_pow_le_genClass_mvt (B := B) (c := expDetCoeff T) (Λ := Λ) (i := i)
      hℓ1 hBb hBΛ hcoef hσ0 hσσ' hT0.le hV0.le hW hsep hbig'
    have hc := class_count_mvt_arith_of_exponent hT1 hXge1
      (expDet_mvt_term_le hT1 hX1 hσ1 hcase hε hε1) hdiag hQ1 hP0 hL1 hL34 hlogL hG0 hmass hVl
      (Nat.cast_nonneg _) hmvt
    refine le_trans hc (le_trans ?_ (hfinal _ (by norm_num) classMvtConstant_le))
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0.le _)
    exact mul_le_mul_of_nonneg_left hBig.meanValue (by norm_num)
  · push Not at hcase
    have hVlpos : 0 < V ^ ℓ := pow_pos hV0 ℓ
    have hℓR34 : (ℓ : ℝ) ≤ 34 := by exact_mod_cast hℓ34
    obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = ℓ / V ^ ℓ := ⟨_, rfl⟩
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
    have hU0 : 0 < U := by rw [hUdef]; positivity
    have hU : U ≤ 34 * Q ^ 34 := by
      rw [hUdef, div_le_iff₀ hVlpos]
      have h1 : 1 ≤ Q ^ 34 * V ^ ℓ := by
        have := mul_le_mul_of_nonneg_left hVl (pow_nonneg hQ0.le 34)
        rwa [mul_one_div_cancel (pow_pos hQ0 _).ne'] at this
      calc (ℓ : ℝ) ≤ 34 * 1 := by linarith only [hℓR34]
        _ ≤ 34 * (Q ^ 34 * V ^ ℓ) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 34 * Q ^ 34 * V ^ ℓ := by ring
    have hVU : V ^ ℓ / ℓ = 1 / U := by rw [hUdef, one_div_div]
    have hthr' := class_huxley_threshold_arith_of_decay hT1 hXge1
      (expDet_huxley_decay_le hT1 hX1 hXge1 hε.le hcase.le) hQ1 hP0 hL1 hL34 hmass hU0 hU
      hBig.threshold
    rw [← hVU] at hthr'
    have hhux := card_mul_pow_le_genClass_huxley (B := B) (c := expDetCoeff T) (Λ := Λ)
      (i := i) hℓ1 hBb hBΛ hcoef hσ0 hσσ' hT0.le hV0 hW hsep hbig' hthr'
    rw [hVU] at hhux
    have hc := class_count_huxley_arith_of_exponent hT1 hXge1
      (expDet_huxley_term_le hT1 hX1 (by linarith) hσ2 hε.le) hdiag hQ1 hQlow hP0 hBig.cube
      hBig.single hL1 hL34 hG0 hmass hU0 hU hℓR34 hhux
    have hHC0 : 0 ≤ classHuxleyConstant := by unfold classHuxleyConstant; norm_num
    refine le_trans hc (le_trans ?_ (hfinal _ hHC0 classHuxleyConstant_le))
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0.le _)
    exact mul_le_mul_of_nonneg_left hBig.huxley hHC0

end RHTower
