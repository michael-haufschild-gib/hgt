import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorTypeTwo
import GaloisForLFunctions.RHTower.ZetaZeroGenericBlockCounts
import GaloisForLFunctions.RHTower.ZetaZeroDensityEightThirds

/-!
# Zeros of a height box become separated classes of the exponential detector

The Type I polynomial of the exponential detector is `Σ_{k ≤ Z} c(k) k^{-s}` with the real
coefficients `c(k) = D(k) e^{-k/Y}`, `|c(k)| ≤ d(k)`.  Split it into the dyadic blocks
`B_j = {k ≤ Z : ⌊log₂ k⌋ = j}`, `j < J = ⌊log₂ Z⌋ + 1`.  A Type I zero `β + iγ` has a block of
modulus `≥ 1/(8J)`, and with `Λ = log Z` and the slab `m = ⌊(β - σ)Λ⌋` the Taylor transfer
(`exists_abscissaTaylorPoly_large`) gives a class `(j, i, m)`, `i < J + 8`, whose companion
polynomial is `≥ 1/(48J)` on the line `σ + m/Λ` at height `γ`.  A Type II zero carries the
critical-line integral.

The most populated of the `J(J+8)(⌊Λ⌋+1) + 1` classes (one of them the Type II class), thinned to a
`1`-separated set of ordinates, carries the box count up to the class count times the local
zero-count capacity (`exists_separated_expDet_class`).
-/

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve

/-- The support `[1, Z]` of the Type I polynomial. -/
def expDetSupport (T : ℝ) : Finset ℕ := Finset.Icc 1 (expDetCut T)

/-- The `j`-th dyadic block of the Type I polynomial. -/
def expDetBlock (T : ℝ) (j : ℕ) : Finset ℕ :=
  (expDetSupport T).filter (fun k => Nat.log 2 k = j)

/-- The number of dyadic blocks. -/
def expDetBlockCount (T : ℝ) : ℕ := Nat.log 2 (expDetCut T) + 1

/-- The logarithmic length `log Z`. -/
def expDetLog (T : ℝ) : ℝ := Real.log (expDetCut T)

/-- The real coefficients `D(k) e^{-k/Y}` of the Type I polynomial. -/
def expDetCoeff (T : ℝ) (k : ℕ) : ℝ :=
  moebiusZetaDefect (expDetMoll T) k * Real.exp (-((k : ℝ) / expDetSmooth T))

theorem mem_expDetBlock_bounds {T : ℝ} {j k : ℕ} (hk : k ∈ expDetBlock T j) :
    1 ≤ k ∧ k ≤ expDetCut T ∧ 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1 := by
  unfold expDetBlock expDetSupport at hk
  rw [Finset.mem_filter, Finset.mem_Icc] at hk
  obtain ⟨⟨hk1, hkZ⟩, hlog⟩ := hk
  have h1 : 2 ^ j ≤ k := by rw [← hlog]; exact Nat.pow_log_le_self 2 (by omega)
  have h2 : k < 2 ^ (j + 1) := by rw [← hlog]; exact Nat.lt_pow_succ_log_self (by norm_num) k
  rw [pow_succ] at h2
  exact ⟨hk1, hkZ, h1, by omega⟩

theorem abs_expDetCoeff_le {T : ℝ} (hT : 1 ≤ T) (k : ℕ) :
    |expDetCoeff T k| ≤ k.divisors.card := by
  have hX := one_le_expDetMoll hT
  have hD := norm_moebiusZetaDefect_le_card_divisors hX k
  rw [Real.norm_eq_abs] at hD
  unfold expDetCoeff
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-((k : ℝ) / expDetSmooth T)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact div_nonneg (Nat.cast_nonneg k) (by linarith [one_le_expDetSmooth hT])
  calc |moebiusZetaDefect (expDetMoll T) k| * Real.exp (-((k : ℝ) / expDetSmooth T))
      ≤ (k.divisors.card : ℝ) * 1 :=
        mul_le_mul hD he (Real.exp_pos _).le (Nat.cast_nonneg _)
    _ = k.divisors.card := mul_one _

/-- A block with a nonzero coefficient starts above the mollifier length: `X < 2^{j+1}`. -/
theorem expDetMoll_lt_of_coeff_ne_zero {T : ℝ} {j k : ℕ} (hk : k ∈ expDetBlock T j)
    (hc : expDetCoeff T k ≠ 0) : expDetMoll T < 2 * 2 ^ j := by
  obtain ⟨hk1, -, -, hk2⟩ := mem_expDetBlock_bounds hk
  by_contra hcon
  push Not at hcon
  apply hc
  unfold expDetCoeff
  have hz : moebiusZetaDefect (expDetMoll T) k = 0 :=
    (moebiusZetaDefect_vanishesBelow (expDetMoll T)) k (by omega)
  rw [hz, zero_mul]

/-- The Type I polynomial of the detector is the Dirichlet value of `c` on `[1, Z]`. -/
theorem sum_range_expDetTerm_eq {T : ℝ} (ρ : ℂ) :
    ∑ n ∈ Finset.range (expDetCut T + 1), expDetTerm (expDetMoll T) ρ (expDetSmooth T) n =
      abscissaDirichletValue (expDetSupport T) (fun k => ((expDetCoeff T k : ℝ) : ℂ))
        ρ.re ρ.im := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h0 : expDetTerm (expDetMoll T) ρ (expDetSmooth T) 0 = 0 := by simp [expDetTerm]
  rw [h0, zero_add]
  unfold abscissaDirichletValue expDetSupport
  rw [show Finset.Icc 1 (expDetCut T) = Finset.Ico 1 (expDetCut T + 1) by
    ext n; simp [Finset.mem_Icc, Finset.mem_Ico]]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hρ : ((ρ.re : ℂ) + (ρ.im : ℂ) * I) = ρ := Complex.re_add_im ρ
  rw [hρ]
  unfold expDetTerm expDetCoeff
  push_cast
  simp only [complexCoeff_apply, div_eq_mul_inv]
  ring

/-- The Dirichlet value on `[1, Z]` is the sum of its dyadic blocks. -/
theorem abscissaDirichletValue_expDetSupport_eq_sum_blocks (T σ γ : ℝ) :
    abscissaDirichletValue (expDetSupport T) (fun k => ((expDetCoeff T k : ℝ) : ℂ)) σ γ =
      ∑ j ∈ range (expDetBlockCount T),
        abscissaDirichletValue (expDetBlock T j) (fun k => ((expDetCoeff T k : ℝ) : ℂ)) σ γ := by
  unfold abscissaDirichletValue expDetBlock
  have hmaps : ∀ k ∈ expDetSupport T, Nat.log 2 k ∈ range (expDetBlockCount T) := by
    intro k hk
    rw [mem_range, expDetBlockCount, Nat.lt_succ_iff]
    unfold expDetSupport at hk
    exact Nat.log_mono_right (Finset.mem_Icc.mp hk).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]

/-- **From a Type I zero to a dyadic block on a fixed line.** -/
theorem exists_expDetBlock_taylor_large {T : ℝ} (hT : 1 ≤ T) (hZ : 2 ≤ expDetCut T)
    {σ₀ δ γ : ℝ} (hσ₀ : 0 ≤ σ₀) (hδ0 : 0 ≤ δ) (hδΛ : δ * expDetLog T ≤ 1)
    (hdet : 1 / 8 ≤ ‖abscissaDirichletValue (expDetSupport T)
      (fun k => ((expDetCoeff T k : ℝ) : ℂ)) (σ₀ + δ) γ‖) :
    ∃ j < expDetBlockCount T, ∃ i < expDetBlockCount T + 8,
      1 / (48 * expDetBlockCount T) ≤
        ‖abscissaTaylorPoly (expDetBlock T j) (fun k => ((expDetCoeff T k : ℝ) : ℂ))
          (expDetLog T) i σ₀ γ‖ := by
  set J := expDetBlockCount T with hJdef
  have hJ : 1 ≤ J := by rw [hJdef, expDetBlockCount]; omega
  rw [abscissaDirichletValue_expDetSupport_eq_sum_blocks] at hdet
  obtain ⟨j, hj, hblock⟩ := exists_range_norm_ge_div hJ _ hdet
  have hΛ0 : 0 < expDetLog T := Real.log_pos (by exact_mod_cast (by omega : 1 < expDetCut T))
  have hS : ∀ k ∈ expDetBlock T j, 1 ≤ k := fun k hk => (mem_expDetBlock_bounds hk).1
  have hΛ : ∀ k ∈ expDetBlock T j, Real.log k ≤ expDetLog T := by
    intro k hk
    have hk := mem_expDetBlock_bounds hk
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk.2.1)
  -- the Taylor tail
  have hcard : ((expDetBlock T j).card : ℝ) ≤ 2 ^ j := by
    have hsub : expDetBlock T j ⊆ Finset.Ico (2 ^ j) (2 * 2 ^ j) := by
      intro k hk
      have := mem_expDetBlock_bounds hk
      rw [Finset.mem_Ico]
      omega
    have h := Finset.card_le_card hsub
    rw [Nat.card_Ico, show 2 * 2 ^ j - 2 ^ j = 2 ^ j by omega] at h
    exact_mod_cast h
  have hsum : ∑ k ∈ expDetBlock T j, ‖((expDetCoeff T k : ℝ) : ℂ)‖ * (k : ℝ) ^ (-σ₀) ≤
      2 * 4 ^ j := by
    have hterm : ∀ k ∈ expDetBlock T j,
        ‖((expDetCoeff T k : ℝ) : ℂ)‖ * (k : ℝ) ^ (-σ₀) ≤ 2 * 2 ^ j := by
      intro k hk
      have hb := mem_expDetBlock_bounds hk
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hb.1
      have hc := abs_expDetCoeff_le hT k
      have hdiv : (k.divisors.card : ℝ) ≤ k := by exact_mod_cast Nat.card_divisors_le_self k
      have hpow : (k : ℝ) ^ (-σ₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hkR (by linarith)
      have hk2 : (k : ℝ) ≤ 2 * 2 ^ j := by
        have : k ≤ 2 * 2 ^ j := by omega
        exact_mod_cast this
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |expDetCoeff T k| * (k : ℝ) ^ (-σ₀) ≤ (k : ℝ) * 1 :=
            mul_le_mul (le_trans hc hdiv) hpow (Real.rpow_nonneg (by linarith) _)
              (Nat.cast_nonneg k)
        _ ≤ 2 * 2 ^ j := by linarith
    calc ∑ k ∈ expDetBlock T j, ‖((expDetCoeff T k : ℝ) : ℂ)‖ * (k : ℝ) ^ (-σ₀)
        ≤ ∑ _k ∈ expDetBlock T j, (2 * 2 ^ j : ℝ) := Finset.sum_le_sum hterm
      _ = (expDetBlock T j).card * (2 * 2 ^ j) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ j * (2 * 2 ^ j) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * 4 ^ j := by rw [show (4 : ℝ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]; ring
  have h4j : (2 : ℝ) * 4 ^ j ≤ (1 / 4) * (2 * 4 ^ J) := by
    have hjJ : j + 1 ≤ J := hj
    have : (4 : ℝ) ^ (j + 1) ≤ 4 ^ J := pow_le_pow_right₀ (by norm_num) hjJ
    rw [pow_succ] at this
    linarith
  have htail : 2 / ((J + 8).factorial : ℝ) *
      ∑ k ∈ expDetBlock T j, ‖((expDetCoeff T k : ℝ) : ℂ)‖ * (k : ℝ) ^ (-σ₀) ≤
        1 / 8 / J / 2 := by
    have h2 := taylor_tail_factorial_bound hJ
    have hpos : (0 : ℝ) ≤ 2 / ((J + 8).factorial : ℝ) := by positivity
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
    calc _ ≤ 2 / ((J + 8).factorial : ℝ) * ((1 / 4) * (2 * 4 ^ J)) :=
          mul_le_mul_of_nonneg_left (le_trans hsum h4j) hpos
      _ = (1 / 4) * (2 / ((J + 8).factorial : ℝ) * (2 * 4 ^ J)) := by ring
      _ ≤ (1 / 4) * (1 / (2 * J) / 2) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 1 / 8 / J / 2 := by field_simp; ring
  obtain ⟨i, hi, hlarge⟩ := exists_abscissaTaylorPoly_large hS _ hδ0 hΛ0 hΛ hδΛ
    (by omega : 1 ≤ J + 8) hblock htail
  refine ⟨j, hj, i, hi, le_trans (le_of_eq ?_) hlarge⟩
  field_simp
  ring

theorem two_le_expDetCut {T : ℝ} (hT : 4 ≤ T) : 2 ≤ expDetCut T := by
  have hT0 : 0 < T := by linarith
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hpow : 2 ≤ T ^ (3 / 5 : ℝ) := by
    calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hT (by norm_num)
      _ ≤ T ^ (3 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h : (2 : ℝ) ≤ T ^ (3 / 5 : ℝ) * Real.log T ^ 2 := by
    have : 1 ≤ Real.log T ^ 2 := one_le_pow₀ hlog
    nlinarith
  unfold expDetCut
  exact Nat.le_floor (by exact_mod_cast h)

/-- **Every zero copy of a height box has a detector class.**  Either its ordinate carries the
Type II integral, or it has a Type I class `(j, i, m)`. -/
theorem exists_expDet_class_of_mem_zeroHeightBox {K₀ c₀ T₁ : ℝ}
    (hdich : ∀ T : ℝ, T₁ ≤ T → ∀ ρ : ℂ,
      riemannZeta ρ = 0 → 7 / 12 ≤ ρ.re → ρ.re < 1 → T ≤ ρ.im → ρ.im ≤ 2 * T →
      1 / 8 ≤ ‖∑ n ∈ Finset.range (expDetCut T + 1),
          expDetTerm (expDetMoll T) ρ (expDetSmooth T) n‖ ∨
      c₀ * expDetSmooth T ^ (ρ.re - 1 / 2) / expDetMoll T ≤
        ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ.im + y : ℝ) : ℂ) * I)‖)
    (hc₀ : 0 < c₀) {σ T : ℝ} (hT₁ : T₁ ≤ T) (hT4 : 4 ≤ T) (hσ : 7 / 12 ≤ σ)
    {q : XiZeroCopy} (hq : q ∈ zeroHeightBox σ T) :
    (c₀ * expDetSmooth T ^ (σ - 1 / 2) / expDetMoll T ≤
        ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (((q.1 : ℂ).im + y : ℝ) : ℂ) * I)‖) ∨
    ∃ j < expDetBlockCount T, ∃ i < expDetBlockCount T + 8, ∃ m < ⌊expDetLog T⌋₊ + 1,
      1 / (48 * expDetBlockCount T) ≤
        ‖abscissaTaylorPoly (expDetBlock T j) (fun k => ((expDetCoeff T k : ℝ) : ℂ))
          (expDetLog T) i (σ + m / expDetLog T) (q.1 : ℂ).im‖ := by
  have hT1 : 1 ≤ T := by linarith
  have hζ := riemannZeta_eq_zero_of_xiZeroCopy q
  have hβ1 := xiZeroCopy_re_lt_one q
  obtain ⟨hβσ, hγ1, hγ2⟩ := hq
  rcases hdich T hT₁ (q.1 : ℂ) hζ (by linarith) hβ1 hγ1 hγ2 with hI | hII
  · right
    rw [sum_range_expDetTerm_eq] at hI
    have hZ := two_le_expDetCut hT4
    set Λ := expDetLog T with hΛ
    have hΛ0 : 0 < Λ := Real.log_pos (by exact_mod_cast (by omega : 1 < expDetCut T))
    set x : ℝ := ((q.1 : ℂ).re - σ) * Λ with hx
    have hx0 : 0 ≤ x := mul_nonneg (by linarith) hΛ0.le
    set m : ℕ := ⌊x⌋₊ with hm
    have hmx : (m : ℝ) ≤ x := Nat.floor_le hx0
    have hxm : x < m + 1 := Nat.lt_floor_add_one x
    have hmM : m < ⌊Λ⌋₊ + 1 := by
      have hxΛ : x ≤ Λ := by
        rw [hx]
        have : (q.1 : ℂ).re - σ ≤ 1 := by linarith
        nlinarith
      exact Nat.lt_succ_of_le (Nat.floor_le_floor hxΛ)
    set δ : ℝ := (q.1 : ℂ).re - (σ + m / Λ) with hδ
    have hδ0 : 0 ≤ δ := by
      rw [hδ]
      have : (m : ℝ) / Λ ≤ (q.1 : ℂ).re - σ := by
        rw [div_le_iff₀ hΛ0]
        linarith
      linarith
    have hδΛ : δ * Λ ≤ 1 := by
      rw [hδ, sub_mul, add_mul, div_mul_cancel₀ _ hΛ0.ne']
      linarith
    have hσm : 0 ≤ σ + m / Λ := by positivity
    have hpt : (q.1 : ℂ).re = σ + m / Λ + δ := by rw [hδ]; ring
    rw [hpt] at hI
    obtain ⟨j, hj, i, hi, hlarge⟩ := exists_expDetBlock_taylor_large hT1 hZ hσm hδ0 hδΛ hI
    exact ⟨j, hj, i, hi, m, hmM, hlarge⟩
  · left
    refine le_trans ?_ hII
    have hX0 : (0 : ℝ) < expDetMoll T := by exact_mod_cast one_le_expDetMoll hT1
    have hY1 := one_le_expDetSmooth hT1
    have hpow : expDetSmooth T ^ (σ - 1 / 2) ≤ expDetSmooth T ^ ((q.1 : ℂ).re - 1 / 2) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    gcongr

/-- **The separated detector class.**  For `T ≥ max(T₁, 4)` and `σ ≥ 7/12` there are a
`1`-separated set `W ⊆ [T, 2T]` of ordinates, all of Type II or all in one Type I class, such that
the box count is at most `(J(J+8)(⌊Λ⌋+1) + 1) · 16(|C| + log(2T+5)) · #W`. -/
theorem exists_separated_expDet_class {K₀ c₀ T₁ : ℝ}
    (hdich : ∀ T : ℝ, T₁ ≤ T → ∀ ρ : ℂ,
      riemannZeta ρ = 0 → 7 / 12 ≤ ρ.re → ρ.re < 1 → T ≤ ρ.im → ρ.im ≤ 2 * T →
      1 / 8 ≤ ‖∑ n ∈ Finset.range (expDetCut T + 1),
          expDetTerm (expDetMoll T) ρ (expDetSmooth T) n‖ ∨
      c₀ * expDetSmooth T ^ (ρ.re - 1 / 2) / expDetMoll T ≤
        ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ.im + y : ℝ) : ℂ) * I)‖)
    (hc₀ : 0 < c₀) {σ T : ℝ} (hT₁ : T₁ ≤ T) (hT4 : 4 ≤ T) (hσ : 7 / 12 ≤ σ) :
    ∃ W : Finset ℝ, (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) ∧
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) ∧
      ((∀ t ∈ W, c₀ * expDetSmooth T ^ (σ - 1 / 2) / expDetMoll T ≤
          ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
            ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖) ∨
        ∃ j < expDetBlockCount T, ∃ i < expDetBlockCount T + 8, ∃ m < ⌊expDetLog T⌋₊ + 1,
          ∀ t ∈ W, 1 / (48 * expDetBlockCount T) ≤
            ‖abscissaTaylorPoly (expDetBlock T j) (fun k => ((expDetCoeff T k : ℝ) : ℂ))
              (expDetLog T) i (σ + m / expDetLog T) t‖) ∧
      ((zeroHeightBox σ T).ncard : ℝ) ≤
        ((expDetBlockCount T * (expDetBlockCount T + 8) * (⌊expDetLog T⌋₊ + 1) + 1 : ℕ) : ℝ) *
          densityWindowCapacity T * W.card := by
  classical
  set J := expDetBlockCount T with hJ
  set Λ := expDetLog T with hΛ
  set M := ⌊Λ⌋₊ + 1 with hM
  have hT0 : 0 < T := by linarith
  set Z : Finset XiZeroCopy := (zeroHeightBox_finite σ T).toFinset with hZ
  set C₀ : Finset (ℕ × ℕ × ℕ) := range J ×ˢ range (J + 8) ×ˢ range M with hC₀
  set C : Finset (Option (ℕ × ℕ × ℕ)) := insert none (C₀.map Function.Embedding.some) with hC
  let typeTwo : ℝ → Prop := fun t =>
    c₀ * expDetSmooth T ^ (σ - 1 / 2) / expDetMoll T ≤
      ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖
  let typeOne : ℝ → ℕ × ℕ × ℕ → Prop := fun t c =>
    1 / (48 * J) ≤ ‖abscissaTaylorPoly (expDetBlock T c.1) (fun k => ((expDetCoeff T k : ℝ) : ℂ))
      Λ c.2.1 (σ + c.2.2 / Λ) t‖
  let good : XiZeroCopy → Option (ℕ × ℕ × ℕ) → Prop := fun q o =>
    o ∈ C ∧ Option.elim o (typeTwo (q.1 : ℂ).im) (typeOne (q.1 : ℂ).im)
  have hex : ∀ q ∈ Z, ∃ o, good q o := by
    intro q hqZ
    rw [hZ, Set.Finite.mem_toFinset] at hqZ
    rcases exists_expDet_class_of_mem_zeroHeightBox hdich hc₀ hT₁ hT4 hσ hqZ with h2 | h1
    · exact ⟨none, by simp [hC], h2⟩
    · obtain ⟨j, hj, i, hi, m, hm, hlarge⟩ := h1
      refine ⟨some (j, i, m), ?_, hlarge⟩
      rw [hC, Finset.mem_insert, Finset.mem_map]
      right
      exact ⟨(j, i, m), by simp only [hC₀, mem_product, mem_range]; exact ⟨hj, hi, hm⟩, rfl⟩
  let cls : XiZeroCopy → Option (ℕ × ℕ × ℕ) := fun q =>
    if h : q ∈ Z then Classical.choose (hex q h) else none
  have hcls : ∀ q ∈ Z, good q (cls q) := by
    intro q hq
    simp only [cls, dif_pos hq]
    exact Classical.choose_spec (hex q hq)
  have hCne : C.Nonempty := ⟨none, by simp [hC]⟩
  obtain ⟨o, hoC, hfib⟩ := exists_fiber_card_ge Z C cls (fun q hq => (hcls q hq).1) hCne
  set Zc := Z.filter (fun q => cls q = o) with hZc
  have hcap : ∀ t : ℝ, ((Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)).card : ℝ)
      ≤ densityWindowCapacity T := by
    intro t
    by_cases hne : (Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)).Nonempty
    · obtain ⟨q, hq⟩ := hne
      rw [mem_filter, hZc, mem_filter, hZ, Set.Finite.mem_toFinset] at hq
      have ht : |t| ≤ 2 * T + 1 := by
        have h1 := hq.2
        rw [abs_le] at h1 ⊢
        constructor <;> linarith [hq.1.1.2.1, hq.1.1.2.2]
      have hsub : ((Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)) : Set XiZeroCopy)
          ⊆ xiOrdinateWindow 1 t := by
        intro z hz
        rw [mem_coe, mem_filter] at hz
        exact hz.2
      have hle := Set.ncard_le_ncard hsub (finite_xiOrdinateWindow 1 t)
      rw [Set.ncard_coe_finset] at hle
      have hwin := ncard_xiOrdinateWindow_one_le_log t
      have hlog : Real.log (|t| + 4) ≤ Real.log (2 * T + 5) :=
        Real.log_le_log (by positivity) (by linarith)
      unfold densityWindowCapacity
      have habsC := le_abs_self xiLineTwoLogDerivConstant
      calc ((Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)).card : ℝ)
          ≤ ((xiOrdinateWindow 1 t).ncard : ℝ) := by exact_mod_cast hle
        _ ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := hwin
        _ ≤ 16 * (|xiLineTwoLogDerivConstant| + Real.log (2 * T + 5)) := by linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, card_empty, Nat.cast_zero]
      unfold densityWindowCapacity
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T + 5 by linarith)
      positivity
  obtain ⟨S, hSZ, hSsep, hScard⟩ :=
    exists_separated_subset_card_le Zc (fun q => (q.1 : ℂ).im) hcap
  have hgoodS : ∀ q ∈ S, Option.elim o (typeTwo (q.1 : ℂ).im) (typeOne (q.1 : ℂ).im) := by
    intro q hq
    have hq' := hSZ hq
    rw [hZc, mem_filter] at hq'
    have hg := (hcls q hq'.1).2
    rwa [hq'.2] at hg
  refine ⟨S.image (fun q => (q.1 : ℂ).im), ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    have hq' := hSZ hq
    rw [hZc, mem_filter, hZ, Set.Finite.mem_toFinset] at hq'
    exact ⟨hq'.1.2.1, hq'.1.2.2⟩
  · intro t ht t' ht' htt'
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    obtain ⟨q', hq', rfl⟩ := mem_image.mp ht'
    have hqq : q ≠ q' := fun h => htt' (by rw [h])
    exact hSsep q hq q' hq' hqq
  · rcases o with _ | c
    · left
      intro t ht
      obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
      exact hgoodS q hq
    · right
      have hcC : c ∈ C₀ := by
        rw [hC, Finset.mem_insert, Finset.mem_map] at hoC
        rcases hoC with h | ⟨c', hc', hcc'⟩
        · exact absurd h (by simp)
        · simp only [Function.Embedding.some_apply, Option.some.injEq] at hcc'
          rwa [← hcc']
      simp only [hC₀, mem_product, mem_range] at hcC
      refine ⟨c.1, hcC.1, c.2.1, hcC.2.1, c.2.2, hcC.2.2, fun t ht => ?_⟩
      obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
      exact hgoodS q hq
  · have hinj : Set.InjOn (fun q : XiZeroCopy => (q.1 : ℂ).im) S := by
      intro a ha b hb hab
      by_contra hne
      have h := hSsep a ha b hb hne
      simp only at hab
      rw [hab, sub_self, abs_zero] at h
      linarith
    rw [card_image_of_injOn hinj]
    have hbox : (zeroHeightBox σ T).ncard = Z.card := by
      rw [hZ, Set.ncard_eq_toFinset_card _ (zeroHeightBox_finite σ T)]
    have hCcard : (C.card : ℝ) = ((J * (J + 8) * M + 1 : ℕ) : ℝ) := by
      rw [hC, Finset.card_insert_of_notMem (by simp), Finset.card_map, hC₀]
      simp [card_product]
      ring
    rw [hbox]
    calc (Z.card : ℝ) ≤ C.card * (Z.filter (fun a => cls a = o)).card := hfib
      _ = C.card * (Zc.card : ℝ) := by rw [hZc]
      _ ≤ C.card * (densityWindowCapacity T * S.card) :=
          mul_le_mul_of_nonneg_left hScard (Nat.cast_nonneg _)
      _ = ((J * (J + 8) * M + 1 : ℕ) : ℝ) * densityWindowCapacity T * S.card := by
          rw [hCcard]
          ring

end RHTower
