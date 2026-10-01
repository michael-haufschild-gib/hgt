import GaloisForLFunctions.RHTower.SpeiserShadowAreaDensity
import GaloisForLFunctions.RHTower.XiHadamardSignDensity

/-!
# The Hadamard sign fails on area `O(T / log T)`

RH is equivalent to `ξ(s) ≠ 0`, `Re(ξ'/ξ)(s) ≥ 0` for every `s` with `Re s > 1/2`. A failure at
`s` lies in the rectangle `1/2 < Re s ≤ Re ρ`, `|Im s − Im ρ| ≤ Re ρ − 1/2` of an off-line zero
`ρ`, of area `2(Re ρ − 1/2)²` (`DeBruijn.exists_boxZero_of_hadamard_fail`).

**Theorem** (`exists_hadamardFail_area_le_div_log`). There is `C` such that for all large `U`
admissible heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` exist with

`vol{s : Re s > 1/2, T₁ + 1/2 ≤ Im s ≤ T₂ − 1/2, Hadamard sign fails at s} ≤ C (T₂ − T₁)/log U`.

This is the natural critical-scale order: `≍ T log T` zeros, each displaced by `≍ 1/log T` under
the exponential near-line density, give total rectangle area `≍ T/log T`.

**Proof.**
- Failures within `2/L` of the line (`L = log U`) cover area `≤ (4/L)(T₂ − T₁)`.
- The remaining failures lie in rectangles of zeros with `b = Re ρ − 1/2 ≥ 2/L`.
- For these, `b² ≤ (4/L) Σ_{1 ≤ k ≤ M} [b ≥ 2k/L] b` (`sq_le_four_div_mul_sum_indicator`).
- So `Σ m b² ≤ (4/L) Σ_k (tail moment at 2k/L)`, and the exponential layer bound
  (`sum_mul_sub_half_le_of_layer_bound`) sums to `≪ (T₂ − T₁)/L + L²`.
-/

open Complex Set MeasureTheory Filter

namespace RHTower

noncomputable section

/-- For `2/L ≤ b < 1/2`, `b² ≤ (4/L) Σ_{1 ≤ k ≤ M} [2k/L ≤ b] b` once `M > L/4`. -/
theorem sq_le_four_div_mul_sum_indicator {L b : ℝ} (hL : 0 < L) (hb : 2 / L ≤ b) (hb1 : b < 1 / 2)
    {M : ℕ} (hM : L / 4 < M) :
    b ^ 2 ≤ 4 / L * ∑ k ∈ Finset.Icc 1 M, if 2 * (k : ℝ) / L ≤ b then b else 0 := by
  classical
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  set j : ℕ := ⌊L * b / 2⌋₊ with hj
  have hLb : 1 ≤ L * b / 2 := by
    rw [div_le_iff₀ hL] at hb; linarith
  have hj1 : 1 ≤ j := Nat.le_floor (by exact_mod_cast hLb)
  have hjle : (j : ℝ) ≤ L * b / 2 := Nat.floor_le (by positivity)
  have hjlt : L * b / 2 < j + 1 := Nat.lt_floor_add_one _
  have hjM : j ≤ M := by
    have : (j : ℝ) < M := by
      have : L * b / 2 < L / 4 := by nlinarith
      linarith
    exact_mod_cast this.le
  -- `b ≤ 4j/L`
  have hbj : b ≤ 4 * j / L := by
    rw [le_div_iff₀ hL]
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    nlinarith
  -- the indicator sum dominates `j b`
  have hsum : (j : ℝ) * b ≤ ∑ k ∈ Finset.Icc 1 M, if 2 * (k : ℝ) / L ≤ b then b else 0 := by
    have h1 : (j : ℝ) * b = ∑ k ∈ Finset.Icc 1 j, if 2 * (k : ℝ) / L ≤ b then b else 0 := by
      have : ∀ k ∈ Finset.Icc 1 j, (if 2 * (k : ℝ) / L ≤ b then b else 0) = b := by
        intro k hk
        have hkj : (k : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hk).2
        rw [if_pos]
        rw [div_le_iff₀ hL]; nlinarith
      rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp
    rw [h1]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hjM)
    intro k _ _
    split_ifs <;> linarith
  calc b ^ 2 = b * b := sq b
    _ ≤ 4 * j / L * b := mul_le_mul_of_nonneg_right hbj hb0.le
    _ = 4 / L * (j * b) := by ring
    _ ≤ 4 / L * ∑ k ∈ Finset.Icc 1 M, if 2 * (k : ℝ) / L ≤ b then b else 0 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **Squared moment from tail moments.** -/
theorem sum_mul_sq_le_of_tail {Z : Finset ℂ} {m : ℂ → ℝ} (hm : ∀ w, 0 ≤ m w) {L : ℝ}
    (hL : 0 < L) (hre : ∀ w ∈ Z, w.re < 1) {M : ℕ} (hM : L / 4 < M) {B : ℕ → ℝ}
    (htail : ∀ k ∈ Finset.Icc 1 M,
      ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * (k : ℝ) / L ≤ w.re), m w * (w.re - 1 / 2) ≤ B k) :
    ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 / L ≤ w.re), m w * (w.re - 1 / 2) ^ 2 ≤
      4 / L * ∑ k ∈ Finset.Icc 1 M, B k := by
  classical
  set F := Z.filter (fun w => 1 / 2 + 2 / L ≤ w.re) with hF
  have hpt : ∀ w ∈ F, m w * (w.re - 1 / 2) ^ 2 ≤ 4 / L * ∑ k ∈ Finset.Icc 1 M,
      if 2 * (k : ℝ) / L ≤ w.re - 1 / 2 then m w * (w.re - 1 / 2) else 0 := by
    intro w hw
    obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
    have h := sq_le_four_div_mul_sum_indicator hL (b := w.re - 1 / 2) (by linarith)
      (by linarith [hre w hwZ]) hM
    have e : ∑ k ∈ Finset.Icc 1 M,
        (if 2 * (k : ℝ) / L ≤ w.re - 1 / 2 then m w * (w.re - 1 / 2) else 0) =
        m w * ∑ k ∈ Finset.Icc 1 M, if 2 * (k : ℝ) / L ≤ w.re - 1 / 2 then w.re - 1 / 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
    rw [e]
    calc m w * (w.re - 1 / 2) ^ 2 ≤ m w * (4 / L * ∑ k ∈ Finset.Icc 1 M,
          if 2 * (k : ℝ) / L ≤ w.re - 1 / 2 then w.re - 1 / 2 else 0) :=
          mul_le_mul_of_nonneg_left h (hm w)
      _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro k hk
  refine le_trans (le_of_eq ?_) (htail k hk)
  rw [← Finset.sum_filter, hF, Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext w
  simp only [Finset.mem_filter]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have h2 : 2 / L ≤ 2 * (k : ℝ) / L := div_le_div_of_nonneg_right (by linarith) hL.le
  constructor
  · rintro ⟨hw, -, h⟩; exact ⟨hw, by linarith⟩
  · rintro ⟨hw, h⟩; exact ⟨hw, by linarith, by linarith⟩

/-- **The Hadamard failure set in a window, split at distance `2/L`.** -/
theorem volume_hadamardFail_window_le {T₁ T₂ L : ℝ} (hL : 0 < L) (h20 : 20 ≤ T₁) (hT : T₁ < T₂)
    {Z : Finset ℂ}
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) :
    volume {s : ℂ | 1 / 2 < s.re ∧ T₁ + 1 / 2 ≤ s.im ∧ s.im ≤ T₂ - 1 / 2 ∧
        ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)} ≤
      ENNReal.ofReal (4 / L * (T₂ - T₁) + 2 * ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 / L ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) ^ 2) := by
  classical
  set F := Z.filter (fun w => 1 / 2 + 2 / L ≤ w.re) with hF
  have hsub : {s : ℂ | 1 / 2 < s.re ∧ T₁ + 1 / 2 ≤ s.im ∧ s.im ≤ T₂ - 1 / 2 ∧
      ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)} ⊆
      {s : ℂ | |s.re - 1 / 2| < 2 / L ∧ T₁ + 1 / 2 ≤ s.im ∧ s.im ≤ T₂ - 1 / 2} ∪
        ⋃ w ∈ F, DeBruijn.hadamardRect w := by
    rintro s ⟨hs, h1, h2, hfail⟩
    by_cases hnear : s.re - 1 / 2 < 2 / L
    · exact Or.inl ⟨by rw [abs_of_pos (by linarith)]; exact hnear, h1, h2⟩
    · right
      push Not at hnear
      obtain ⟨ρ, hρ, hsρ⟩ := DeBruijn.exists_boxZero_of_hadamard_fail (V := T₂ - 1 / 2) hs
        (by linarith) h2 hfail
      rw [mem_boxFinsetLe] at hρ
      obtain ⟨hρ1, hρ2, -, -, hρ0⟩ := hρ
      simp only [DeBruijn.hadamardRect, mem_preimage, Complex.measurableEquivRealProd_apply,
        mem_prod, mem_Ioc, mem_Icc] at hsρ
      obtain ⟨⟨-, hsre⟩, hi1, hi2⟩ := hsρ
      have hρne : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hρ2; linarith
      have hζ : riemannZeta ρ = 0 := (xi_eq_zero_iff (by linarith) hρne).mp hρ0
      refine Set.mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨(hZ ρ).mpr ⟨?_, hζ⟩, by linarith⟩, ?_⟩
      · rw [Complex.mem_reProdIm, uIcc_of_le (by norm_num), uIcc_of_le hT.le]
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      · simp only [DeBruijn.hadamardRect, mem_preimage, Complex.measurableEquivRealProd_apply,
          mem_prod, mem_Ioc, mem_Icc]
        exact ⟨⟨hs, hsre⟩, hi1, hi2⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hnear := volume_nearLine_le (T₁ := T₁) (T₂ := T₂) (r := 2 / L) (by positivity)
  have hfar : volume (⋃ w ∈ F, DeBruijn.hadamardRect w) ≤
      ENNReal.ofReal (2 * ∑ w ∈ F,
        ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) ^ 2) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ w ∈ F, volume (DeBruijn.hadamardRect w) ≤
        ENNReal.ofReal (2 * (((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) ^ 2)) := by
      intro w hw
      obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
      obtain ⟨-, hζw⟩ := (hZ w).mp hwZ
      have hr0 : 0 ≤ w.re - 1 / 2 := by have := div_pos two_pos hL; linarith
      have hw1 : w ≠ 1 := fun h => by rw [h] at hζw; exact riemannZeta_one_ne_zero hζw
      have hm := one_le_toNat_analyticOrderAt_riemannZeta hw1 hζw
      have hm' : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := by exact_mod_cast hm
      rw [DeBruijn.volume_hadamardRect, ← ENNReal.ofReal_mul hr0]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_nonneg (w.re - 1 / 2)]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w hw => by
      have hwre := (Finset.mem_filter.mp hw).2
      have hr0 : 0 ≤ w.re - 1 / 2 := by have := div_pos two_pos hL; linarith
      positivity), Finset.mul_sum]
  refine (add_le_add hnear hfar).trans ?_
  rw [← ENNReal.ofReal_add (by nlinarith [div_pos two_pos hL]) (by
    apply mul_nonneg two_pos.le
    apply Finset.sum_nonneg
    intro w hw
    have hwre := (Finset.mem_filter.mp hw).2
    have hr0 : 0 ≤ w.re - 1 / 2 := by have := div_pos two_pos hL; linarith
    positivity)]
  apply ENNReal.ofReal_le_ofReal
  have : 2 * (2 / L) * (T₂ - T₁) = 4 / L * (T₂ - T₁) := by ring
  nlinarith [div_pos two_pos hL]


/-- The exponential factor at the clipped layer `min(2k, L/2 − 2)`. -/
private theorem exp_clip_le {L : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ L / 4 + 1) :
    Real.exp (-(min (2 * (k : ℝ)) (L / 2 - 2) / 2400)) ≤ 2 * Real.exp (-((k : ℝ) / 1200)) := by
  have h1 : 2 * (k : ℝ) - 4 ≤ min (2 * (k : ℝ)) (L / 2 - 2) := le_min (by linarith) (by linarith)
  calc Real.exp (-(min (2 * (k : ℝ)) (L / 2 - 2) / 2400))
      ≤ Real.exp (1 / 600 + -((k : ℝ) / 1200)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (1 / 600) * Real.exp (-((k : ℝ) / 1200)) := Real.exp_add _ _
    _ ≤ 2 * Real.exp (-((k : ℝ) / 1200)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        calc Real.exp (1 / 600) ≤ Real.exp (Real.log 2) :=
              Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
          _ = 2 := Real.exp_log two_pos

/-- `Σ_{1 ≤ k ≤ M} e^{−k/1200} ≤ 1201`. -/
private theorem sum_Icc_exp_neg_div_le (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, Real.exp (-((k : ℝ) / 1200)) ≤ 1201 := by
  refine le_trans ?_ (sum_exp_neg_div_le (M + 1))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2
  · intro _ _ _; exact (Real.exp_pos _).le

/-- **The Hadamard sign fails on area `O(T/log T)`.** -/
theorem exists_hadamardFail_area_le_div_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        volume {s : ℂ | 1 / 2 < s.re ∧ T₁ + 1 / 2 ≤ s.im ∧ s.im ≤ T₂ - 1 / 2 ∧
            ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)} ≤
          ENNReal.ofReal (C * (T₂ - T₁) / Real.log U) := by
  classical
  obtain ⟨A, K, hA, hK, hev⟩ := exists_selberg_exponential_nearLine_zeroDensity
  have hπ : 0 < Real.pi := Real.pi_pos
  refine ⟨5 + 16 / Real.pi * (2402 * 1201 * A), by positivity, ?_⟩
  have hratio : Tendsto (fun U : ℝ => Real.log U ^ 3 / U) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero
  filter_upwards [hev, Real.tendsto_log_atTop.eventually_ge_atTop (8 : ℝ),
    hratio.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (32 * (K + 1)) by positivity)),
    eventually_ge_atTop (100 : ℝ)] with U hU hL8 hL3 hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, ?_⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  rw [← hLdef] at hL8 hL3 hbound ⊢
  have hL0 : 0 < L := by linarith
  have hT : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hΔ : U / 8 ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset (T₁ := T₁) (T₂ := T₂)
    (by linarith [hT₁.1]) hT
  have hre : ∀ w ∈ Z, w.re < 1 := by
    intro w hw
    obtain ⟨-, hζ⟩ := (hZ w).mp hw
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hζ
  set m : ℂ → ℝ := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ) with hm
  have hm0 : ∀ w, 0 ≤ m w := fun w => Nat.cast_nonneg _
  set D := (T₂ - T₁) * A with hD
  have hD0 : 0 ≤ D := by rw [hD]; nlinarith
  set E := K * L with hE
  have hE0 : 0 ≤ E := by positivity
  set M : ℕ := ⌊L / 4⌋₊ + 1 with hMdef
  have hM : L / 4 < M := by rw [hMdef]; push_cast; exact Nat.lt_floor_add_one _
  have hMle : (M : ℝ) ≤ L / 4 + 1 := by
    rw [hMdef]; push_cast; linarith [Nat.floor_le (show 0 ≤ L / 4 by positivity)]
  set B : ℕ → ℝ := fun k =>
    2 / Real.pi * (1201 * D * (2 * Real.exp (-((k : ℝ) / 1200))) + (L / 4 + 1) * E) with hB
  -- the tail at every layer
  have htail : ∀ k ∈ Finset.Icc 1 M,
      ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * (k : ℝ) / L ≤ w.re), m w * (w.re - 1 / 2) ≤ B k := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hkM : (k : ℝ) ≤ L / 4 + 1 :=
      le_trans (by exact_mod_cast (Finset.mem_Icc.mp hk).2) hMle
    set κ := min (2 * (k : ℝ)) (L / 2 - 2) with hκ
    have hκ2 : 2 ≤ κ := le_min (by linarith) (by linarith)
    have hκL : κ ≤ L / 2 - 2 := min_le_right _ _
    have hlayer := sum_mul_sub_half_le_of_layer_bound (Z := Z) (m := m) hm0
      (L := L) (κ := κ) (D := D) (E := E) (by linarith) hκ2 hκL hre hD0 hE0
      (fun a ha1 ha2 => by
        have := hbound a ha1 ha2 Z hZ
        calc 2 * Real.pi * (a / L * ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re), m w)
            ≤ (T₂ - T₁) * (A * Real.exp (-(a / 1200))) + K * L := this
          _ = D * Real.exp (-(a / 1200)) + E := by rw [hD, hE]; ring)
    have hsub : Z.filter (fun w => 1 / 2 + 2 * (k : ℝ) / L ≤ w.re) ⊆
        Z.filter (fun w => 1 / 2 + κ / L ≤ w.re) := by
      intro w hw
      obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_filter.mpr ⟨hwZ, ?_⟩
      have : κ / L ≤ 2 * (k : ℝ) / L := div_le_div_of_nonneg_right (min_le_left _ _) hL0.le
      linarith
    have hmono : ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * (k : ℝ) / L ≤ w.re), m w * (w.re - 1 / 2) ≤
        ∑ w ∈ Z.filter (fun w => 1 / 2 + κ / L ≤ w.re), m w * (w.re - 1 / 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro w hw _
      have hwre := (Finset.mem_filter.mp hw).2
      have : 0 ≤ κ / L := by positivity
      exact mul_nonneg (hm0 w) (by linarith)
    refine hmono.trans (hlayer.trans ?_)
    have hexp := exp_clip_le (L := L) hkM
    rw [← hκ] at hexp
    rw [hB]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 1201 * D)
    linarith
  have hsq := sum_mul_sq_le_of_tail hm0 hL0 hre hM htail
  have hwin := volume_hadamardFail_window_le hL0 (by linarith [hT₁.1]) hT hZ
  refine hwin.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the layer sum
  have hBsum : ∑ k ∈ Finset.Icc 1 M, B k ≤
      2 / Real.pi * (2402 * 1201 * D + (L / 4 + 1) ^ 2 * E) := by
    have e : ∑ k ∈ Finset.Icc 1 M, B k = 2 / Real.pi * (2402 * D *
        ∑ k ∈ Finset.Icc 1 M, Real.exp (-((k : ℝ) / 1200)) + M * ((L / 4 + 1) * E)) := by
      rw [hB]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
        nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 := mul_le_mul_of_nonneg_left (sum_Icc_exp_neg_div_le M)
      (by positivity : (0 : ℝ) ≤ 2402 * D)
    have h2 : (M : ℝ) * ((L / 4 + 1) * E) ≤ (L / 4 + 1) * ((L / 4 + 1) * E) :=
      mul_le_mul_of_nonneg_right hMle (by positivity)
    nlinarith
  -- `L³` is negligible against `T₂ − T₁`
  have hU0 : 0 < U := by linarith
  have hL3' : 32 * (K + 1) * L ^ 3 ≤ U := by
    have := hL3; rw [div_lt_iff₀ hU0] at this
    have e : 1 / (32 * (K + 1)) * U * (32 * (K + 1)) = U := by field_simp
    have hK1 : (0 : ℝ) < 32 * (K + 1) := by positivity
    nlinarith
  have hquart : (L / 4 + 1) ^ 2 ≤ L ^ 2 / 4 := by nlinarith
  have hsmall : 16 / Real.pi * ((L / 4 + 1) ^ 2 * E) ≤ T₂ - T₁ := by
    have hπ3 : 3 < Real.pi := Real.pi_gt_three
    have h1 : (L / 4 + 1) ^ 2 * E ≤ L ^ 2 / 4 * (K * L) := by
      rw [hE]; exact mul_le_mul_of_nonneg_right hquart (by positivity)
    have h2 : 16 / Real.pi ≤ 16 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ3.le
    have h3 : 16 / Real.pi * ((L / 4 + 1) ^ 2 * E) ≤ 16 / 3 * (L ^ 2 / 4 * (K * L)) :=
      mul_le_mul h2 h1 (by positivity) (by norm_num)
    have h4 : 16 / 3 * (L ^ 2 / 4 * (K * L)) ≤ U / 8 := by
      have : 0 ≤ L ^ 3 := by positivity
      nlinarith
    linarith
  -- assemble
  have hsumnn : 0 ≤ ∑ k ∈ Finset.Icc 1 M, B k := by
    apply Finset.sum_nonneg; intro k _; rw [hB]; positivity
  calc 4 / L * (T₂ - T₁) + 2 * ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 / L ≤ w.re),
        m w * (w.re - 1 / 2) ^ 2
      ≤ 4 / L * (T₂ - T₁) + 2 * (4 / L * (2 / Real.pi * (2402 * 1201 * D +
          (L / 4 + 1) ^ 2 * E))) := by
        have := hsq.trans (mul_le_mul_of_nonneg_left hBsum (by positivity))
        linarith
    _ = (4 * (T₂ - T₁) + 16 / Real.pi * (2402 * 1201 * A) * (T₂ - T₁) +
          16 / Real.pi * ((L / 4 + 1) ^ 2 * E)) / L := by
        rw [hD]; field_simp; ring
    _ ≤ (5 + 16 / Real.pi * (2402 * 1201 * A)) * (T₂ - T₁) / L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        nlinarith

end

end RHTower
