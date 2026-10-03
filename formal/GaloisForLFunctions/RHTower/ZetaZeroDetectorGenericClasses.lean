import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorTypeTwo
import GaloisForLFunctions.RHTower.ZetaZeroGenericBlockCounts
import GaloisForLFunctions.RHTower.ZetaZeroDensityEightThirds

/-!
# Zeros of a height box as separated detector classes, for general lengths

The class extraction of `ZetaZeroExponentialDetectorClasses` with the mollifier length `X`, the
smoothing length `Y` and the cutoff `Z` as free parameters (`1 ≤ X`, `1 ≤ Y`, `2 ≤ Z`).  The
Type I polynomial `Σ_{k ≤ Z} c(k) k^{-s}`, `c(k) = D(k) e^{-k/Y}`, splits into the dyadic blocks
`B_j = {k ≤ Z : ⌊log₂ k⌋ = j}`, `j < J = ⌊log₂ Z⌋ + 1`; a Type I zero has a class `(j, i, m)`
whose companion polynomial is `≥ 1/(48J)` on the line `σ + m/log Z`, and a Type II zero carries
the critical-line integral.  The most populated of the `J(J+8)(⌊log Z⌋+1) + 1` classes, thinned to
a `1`-separated set of ordinates, carries the box count up to the class count times the local
zero-count capacity (`exists_separated_gDet_class`).
-/

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve

/-- The support `[1, Z]` of the Type I polynomial. -/
def gDetSupport (Z : ℕ) : Finset ℕ := Finset.Icc 1 Z

/-- The `j`-th dyadic block of the Type I polynomial. -/
def gDetBlock (Z j : ℕ) : Finset ℕ :=
  (gDetSupport Z).filter (fun k => Nat.log 2 k = j)

/-- The number of dyadic blocks. -/
def gDetBlockCount (Z : ℕ) : ℕ := Nat.log 2 Z + 1

/-- The logarithmic length `log Z`. -/
def gDetLog (Z : ℕ) : ℝ := Real.log Z

/-- The real coefficients `D(k) e^{-k/Y}` of the Type I polynomial. -/
def gDetCoeff (X : ℕ) (Y : ℝ) (k : ℕ) : ℝ :=
  moebiusZetaDefect X k * Real.exp (-((k : ℝ) / Y))

theorem mem_gDetBlock_bounds {Z j k : ℕ} (hk : k ∈ gDetBlock Z j) :
    1 ≤ k ∧ k ≤ Z ∧ 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1 := by
  unfold gDetBlock gDetSupport at hk
  rw [Finset.mem_filter, Finset.mem_Icc] at hk
  obtain ⟨⟨hk1, hkZ⟩, hlog⟩ := hk
  have h1 : 2 ^ j ≤ k := by rw [← hlog]; exact Nat.pow_log_le_self 2 (by omega)
  have h2 : k < 2 ^ (j + 1) := by rw [← hlog]; exact Nat.lt_pow_succ_log_self (by norm_num) k
  rw [pow_succ] at h2
  exact ⟨hk1, hkZ, h1, by omega⟩

theorem abs_gDetCoeff_le {X : ℕ} {Y : ℝ} (hX : 1 ≤ X) (hY : 0 < Y) (k : ℕ) :
    |gDetCoeff X Y k| ≤ k.divisors.card := by
  have hD := norm_moebiusZetaDefect_le_card_divisors hX k
  rw [Real.norm_eq_abs] at hD
  unfold gDetCoeff
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-((k : ℝ) / Y)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact div_nonneg (Nat.cast_nonneg k) hY.le
  calc |moebiusZetaDefect X k| * Real.exp (-((k : ℝ) / Y))
      ≤ (k.divisors.card : ℝ) * 1 :=
        mul_le_mul hD he (Real.exp_pos _).le (Nat.cast_nonneg _)
    _ = k.divisors.card := mul_one _

/-- A block with a nonzero coefficient starts above the mollifier length: `X < 2^{j+1}`. -/
theorem gDetMoll_lt_of_coeff_ne_zero {X Z j k : ℕ} {Y : ℝ} (hk : k ∈ gDetBlock Z j)
    (hc : gDetCoeff X Y k ≠ 0) : X < 2 * 2 ^ j := by
  obtain ⟨hk1, -, -, hk2⟩ := mem_gDetBlock_bounds hk
  by_contra hcon
  push Not at hcon
  apply hc
  unfold gDetCoeff
  have hz : moebiusZetaDefect X k = 0 :=
    (moebiusZetaDefect_vanishesBelow X) k (by omega)
  rw [hz, zero_mul]

/-- The Type I polynomial of the detector is the Dirichlet value of `c` on `[1, Z]`. -/
theorem sum_range_gDetTerm_eq (X Z : ℕ) (Y : ℝ) (ρ : ℂ) :
    ∑ n ∈ Finset.range (Z + 1), expDetTerm X ρ Y n =
      abscissaDirichletValue (gDetSupport Z) (fun k => ((gDetCoeff X Y k : ℝ) : ℂ))
        ρ.re ρ.im := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h0 : expDetTerm X ρ Y 0 = 0 := by simp [expDetTerm]
  rw [h0, zero_add]
  unfold abscissaDirichletValue gDetSupport
  rw [show Finset.Icc 1 Z = Finset.Ico 1 (Z + 1) by
    ext n; simp [Finset.mem_Icc, Finset.mem_Ico]]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hρ : ((ρ.re : ℂ) + (ρ.im : ℂ) * I) = ρ := Complex.re_add_im ρ
  rw [hρ]
  unfold expDetTerm gDetCoeff
  push_cast
  simp only [complexCoeff_apply, div_eq_mul_inv]
  ring

/-- The Dirichlet value on `[1, Z]` is the sum of its dyadic blocks. -/
theorem abscissaDirichletValue_gDetSupport_eq_sum_blocks (X Z : ℕ) (Y σ γ : ℝ) :
    abscissaDirichletValue (gDetSupport Z) (fun k => ((gDetCoeff X Y k : ℝ) : ℂ)) σ γ =
      ∑ j ∈ range (gDetBlockCount Z),
        abscissaDirichletValue (gDetBlock Z j) (fun k => ((gDetCoeff X Y k : ℝ) : ℂ)) σ γ := by
  unfold abscissaDirichletValue gDetBlock
  have hmaps : ∀ k ∈ gDetSupport Z, Nat.log 2 k ∈ range (gDetBlockCount Z) := by
    intro k hk
    rw [mem_range, gDetBlockCount, Nat.lt_succ_iff]
    unfold gDetSupport at hk
    exact Nat.log_mono_right (Finset.mem_Icc.mp hk).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]

/-- **From a Type I zero to a dyadic block on a fixed line.** -/
theorem exists_gDetBlock_taylor_large {X Z : ℕ} {Y : ℝ} (hX : 1 ≤ X) (hY : 0 < Y) (hZ : 2 ≤ Z)
    {σ₀ δ γ : ℝ} (hσ₀ : 0 ≤ σ₀) (hδ0 : 0 ≤ δ) (hδΛ : δ * gDetLog Z ≤ 1)
    (hdet : 1 / 8 ≤ ‖abscissaDirichletValue (gDetSupport Z)
      (fun k => ((gDetCoeff X Y k : ℝ) : ℂ)) (σ₀ + δ) γ‖) :
    ∃ j < gDetBlockCount Z, ∃ i < gDetBlockCount Z + 8,
      1 / (48 * gDetBlockCount Z) ≤
        ‖abscissaTaylorPoly (gDetBlock Z j) (fun k => ((gDetCoeff X Y k : ℝ) : ℂ))
          (gDetLog Z) i σ₀ γ‖ := by
  set J := gDetBlockCount Z with hJdef
  have hJ : 1 ≤ J := by rw [hJdef, gDetBlockCount]; omega
  rw [abscissaDirichletValue_gDetSupport_eq_sum_blocks] at hdet
  obtain ⟨j, hj, hblock⟩ := exists_range_norm_ge_div hJ _ hdet
  have hΛ0 : 0 < gDetLog Z := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  have hS : ∀ k ∈ gDetBlock Z j, 1 ≤ k := fun k hk => (mem_gDetBlock_bounds hk).1
  have hΛ : ∀ k ∈ gDetBlock Z j, Real.log k ≤ gDetLog Z := by
    intro k hk
    have hk := mem_gDetBlock_bounds hk
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk.2.1)
  -- the Taylor tail
  have hcard : ((gDetBlock Z j).card : ℝ) ≤ 2 ^ j := by
    have hsub : gDetBlock Z j ⊆ Finset.Ico (2 ^ j) (2 * 2 ^ j) := by
      intro k hk
      have := mem_gDetBlock_bounds hk
      rw [Finset.mem_Ico]
      omega
    have h := Finset.card_le_card hsub
    rw [Nat.card_Ico, show 2 * 2 ^ j - 2 ^ j = 2 ^ j by omega] at h
    exact_mod_cast h
  have hsum : ∑ k ∈ gDetBlock Z j, ‖((gDetCoeff X Y k : ℝ) : ℂ)‖ * (k : ℝ) ^ (-σ₀) ≤
      2 * 4 ^ j := by
    have hterm : ∀ k ∈ gDetBlock Z j,
        ‖((gDetCoeff X Y k : ℝ) : ℂ)‖ * (k : ℝ) ^ (-σ₀) ≤ 2 * 2 ^ j := by
      intro k hk
      have hb := mem_gDetBlock_bounds hk
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hb.1
      have hc := abs_gDetCoeff_le hX hY k
      have hdiv : (k.divisors.card : ℝ) ≤ k := by exact_mod_cast Nat.card_divisors_le_self k
      have hpow : (k : ℝ) ^ (-σ₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hkR (by linarith)
      have hk2 : (k : ℝ) ≤ 2 * 2 ^ j := by
        have : k ≤ 2 * 2 ^ j := by omega
        exact_mod_cast this
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |gDetCoeff X Y k| * (k : ℝ) ^ (-σ₀) ≤ (k : ℝ) * 1 :=
            mul_le_mul (le_trans hc hdiv) hpow (Real.rpow_nonneg (by linarith) _)
              (Nat.cast_nonneg k)
        _ ≤ 2 * 2 ^ j := by linarith
    calc ∑ k ∈ gDetBlock Z j, ‖((gDetCoeff X Y k : ℝ) : ℂ)‖ * (k : ℝ) ^ (-σ₀)
        ≤ ∑ _k ∈ gDetBlock Z j, (2 * 2 ^ j : ℝ) := Finset.sum_le_sum hterm
      _ = (gDetBlock Z j).card * (2 * 2 ^ j) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ j * (2 * 2 ^ j) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * 4 ^ j := by rw [show (4 : ℝ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]; ring
  have h4j : (2 : ℝ) * 4 ^ j ≤ (1 / 4) * (2 * 4 ^ J) := by
    have hjJ : j + 1 ≤ J := hj
    have : (4 : ℝ) ^ (j + 1) ≤ 4 ^ J := pow_le_pow_right₀ (by norm_num) hjJ
    rw [pow_succ] at this
    linarith
  have htail : 2 / ((J + 8).factorial : ℝ) *
      ∑ k ∈ gDetBlock Z j, ‖((gDetCoeff X Y k : ℝ) : ℂ)‖ * (k : ℝ) ^ (-σ₀) ≤
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

/-- **Every zero copy of a height box has a detector class.**  Either its ordinate carries the
Type II integral, or it has a Type I class `(j, i, m)`. -/
theorem exists_gDet_class_of_mem_zeroHeightBox {K₀ c₀ σ₁ T Y : ℝ} {X Z : ℕ}
    (hdich : ∀ ρ : ℂ,
      riemannZeta ρ = 0 → σ₁ ≤ ρ.re → ρ.re < 1 → T ≤ ρ.im → ρ.im ≤ 2 * T →
      1 / 8 ≤ ‖∑ n ∈ Finset.range (Z + 1), expDetTerm X ρ Y n‖ ∨
      c₀ * Y ^ (ρ.re - 1 / 2) / X ≤
        ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ.im + y : ℝ) : ℂ) * I)‖)
    (hc₀ : 0 < c₀) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hZ : 2 ≤ Z) {σ : ℝ} (hσ : σ₁ ≤ σ)
    (hσ0 : 0 ≤ σ) {q : XiZeroCopy} (hq : q ∈ zeroHeightBox σ T) :
    (c₀ * Y ^ (σ - 1 / 2) / X ≤
        ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (((q.1 : ℂ).im + y : ℝ) : ℂ) * I)‖) ∨
    ∃ j < gDetBlockCount Z, ∃ i < gDetBlockCount Z + 8, ∃ m < ⌊gDetLog Z⌋₊ + 1,
      1 / (48 * gDetBlockCount Z) ≤
        ‖abscissaTaylorPoly (gDetBlock Z j) (fun k => ((gDetCoeff X Y k : ℝ) : ℂ))
          (gDetLog Z) i (σ + m / gDetLog Z) (q.1 : ℂ).im‖ := by
  have hζ := riemannZeta_eq_zero_of_xiZeroCopy q
  have hβ1 := xiZeroCopy_re_lt_one q
  obtain ⟨hβσ, hγ1, hγ2⟩ := hq
  rcases hdich (q.1 : ℂ) hζ (by linarith) hβ1 hγ1 hγ2 with hI | hII
  · right
    rw [sum_range_gDetTerm_eq] at hI
    set Λ := gDetLog Z with hΛ
    have hΛ0 : 0 < Λ := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
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
    obtain ⟨j, hj, i, hi, hlarge⟩ :=
      exists_gDetBlock_taylor_large hX (by linarith) hZ hσm hδ0 hδΛ hI
    exact ⟨j, hj, i, hi, m, hmM, hlarge⟩
  · left
    refine le_trans ?_ hII
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
    have hY1 := hY
    have hpow : Y ^ (σ - 1 / 2) ≤ Y ^ ((q.1 : ℂ).re - 1 / 2) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    gcongr

/-- **The separated detector class.**  For `T ≥ max(T₁, 4)` and `σ ≥ 7/12` there are a
`1`-separated set `W ⊆ [T, 2T]` of ordinates, all of Type II or all in one Type I class, such that
the box count is at most `(J(J+8)(⌊Λ⌋+1) + 1) · 16(|C| + log(2T+5)) · #W`. -/
theorem exists_separated_gDet_class {K₀ c₀ σ₁ T Y : ℝ} {X Z : ℕ}
    (hdich : ∀ ρ : ℂ,
      riemannZeta ρ = 0 → σ₁ ≤ ρ.re → ρ.re < 1 → T ≤ ρ.im → ρ.im ≤ 2 * T →
      1 / 8 ≤ ‖∑ n ∈ Finset.range (Z + 1), expDetTerm X ρ Y n‖ ∨
      c₀ * Y ^ (ρ.re - 1 / 2) / X ≤
        ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((ρ.im + y : ℝ) : ℂ) * I)‖)
    (hc₀ : 0 < c₀) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hZ : 2 ≤ Z) (hT0 : 0 < T) {σ : ℝ}
    (hσ : σ₁ ≤ σ) (hσ0 : 0 ≤ σ) :
    ∃ W : Finset ℝ, (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) ∧
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) ∧
      ((∀ t ∈ W, c₀ * Y ^ (σ - 1 / 2) / X ≤
          ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
            ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖) ∨
        ∃ j < gDetBlockCount Z, ∃ i < gDetBlockCount Z + 8, ∃ m < ⌊gDetLog Z⌋₊ + 1,
          ∀ t ∈ W, 1 / (48 * gDetBlockCount Z) ≤
            ‖abscissaTaylorPoly (gDetBlock Z j) (fun k => ((gDetCoeff X Y k : ℝ) : ℂ))
              (gDetLog Z) i (σ + m / gDetLog Z) t‖) ∧
      ((zeroHeightBox σ T).ncard : ℝ) ≤
        ((gDetBlockCount Z * (gDetBlockCount Z + 8) * (⌊gDetLog Z⌋₊ + 1) + 1 : ℕ) : ℝ) *
          densityWindowCapacity T * W.card := by
  classical
  set J := gDetBlockCount Z with hJ
  set Λ := gDetLog Z with hΛ
  set M := ⌊Λ⌋₊ + 1 with hM
  set Zs : Finset XiZeroCopy := (zeroHeightBox_finite σ T).toFinset with hZs
  set C₀ : Finset (ℕ × ℕ × ℕ) := range J ×ˢ range (J + 8) ×ˢ range M with hC₀
  set C : Finset (Option (ℕ × ℕ × ℕ)) := insert none (C₀.map Function.Embedding.some) with hC
  let typeTwo : ℝ → Prop := fun t =>
    c₀ * Y ^ (σ - 1 / 2) / X ≤
      ∫ y in (-(K₀ * Real.log T))..(K₀ * Real.log T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I)‖
  let typeOne : ℝ → ℕ × ℕ × ℕ → Prop := fun t c =>
    1 / (48 * J) ≤ ‖abscissaTaylorPoly (gDetBlock Z c.1) (fun k => ((gDetCoeff X Y k : ℝ) : ℂ))
      Λ c.2.1 (σ + c.2.2 / Λ) t‖
  let good : XiZeroCopy → Option (ℕ × ℕ × ℕ) → Prop := fun q o =>
    o ∈ C ∧ Option.elim o (typeTwo (q.1 : ℂ).im) (typeOne (q.1 : ℂ).im)
  have hex : ∀ q ∈ Zs, ∃ o, good q o := by
    intro q hqZ
    rw [hZs, Set.Finite.mem_toFinset] at hqZ
    rcases exists_gDet_class_of_mem_zeroHeightBox hdich hc₀ hX hY hZ hσ hσ0 hqZ with h2 | h1
    · exact ⟨none, by simp [hC], h2⟩
    · obtain ⟨j, hj, i, hi, m, hm, hlarge⟩ := h1
      refine ⟨some (j, i, m), ?_, hlarge⟩
      rw [hC, Finset.mem_insert, Finset.mem_map]
      right
      exact ⟨(j, i, m), by simp only [hC₀, mem_product, mem_range]; exact ⟨hj, hi, hm⟩, rfl⟩
  let cls : XiZeroCopy → Option (ℕ × ℕ × ℕ) := fun q =>
    if h : q ∈ Zs then Classical.choose (hex q h) else none
  have hcls : ∀ q ∈ Zs, good q (cls q) := by
    intro q hq
    simp only [cls, dif_pos hq]
    exact Classical.choose_spec (hex q hq)
  have hCne : C.Nonempty := ⟨none, by simp [hC]⟩
  obtain ⟨o, hoC, hfib⟩ := exists_fiber_card_ge Zs C cls (fun q hq => (hcls q hq).1) hCne
  set Zc := Zs.filter (fun q => cls q = o) with hZc
  have hcap : ∀ t : ℝ, ((Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)).card : ℝ)
      ≤ densityWindowCapacity T := by
    intro t
    by_cases hne : (Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)).Nonempty
    · obtain ⟨q, hq⟩ := hne
      rw [mem_filter, hZc, mem_filter, hZs, Set.Finite.mem_toFinset] at hq
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
    rw [hZc, mem_filter, hZs, Set.Finite.mem_toFinset] at hq'
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
    have hbox : (zeroHeightBox σ T).ncard = Zs.card := by
      rw [hZs, Set.ncard_eq_toFinset_card _ (zeroHeightBox_finite σ T)]
    have hCcard : (C.card : ℝ) = ((J * (J + 8) * M + 1 : ℕ) : ℝ) := by
      rw [hC, Finset.card_insert_of_notMem (by simp), Finset.card_map, hC₀]
      simp [card_product]
      ring
    rw [hbox]
    calc (Zs.card : ℝ) ≤ C.card * (Zs.filter (fun a => cls a = o)).card := hfib
      _ = C.card * (Zc.card : ℝ) := by rw [hZc]
      _ ≤ C.card * (densityWindowCapacity T * S.card) :=
          mul_le_mul_of_nonneg_left hScard (Nat.cast_nonneg _)
      _ = ((J * (J + 8) * M + 1 : ℕ) : ℝ) * densityWindowCapacity T * S.card := by
          rw [hCcard]
          ring

end RHTower
