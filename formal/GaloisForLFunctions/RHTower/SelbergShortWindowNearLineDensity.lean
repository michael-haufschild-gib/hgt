import GaloisForLFunctions.RHTower.ZetaRightZeroWeightedCount

/-!
# Selberg's near-line zero density on short windows

The two-length mollified mean square of `SelbergExponentialNearLineDensity` holds on every
window `[T₁, T₂] ⊂ [U/4, U/2]` of length at least `U^{99/100}`; only the final choice of admissible
heights there is dyadic. Choosing the admissible heights inside `(B, B + 1)` and
`(B + W − 1, B + W)` gives, for all large `U`, every window `[B, B + W] ⊂ [U/4, U/2]` with
`W ≥ U^{99/100} + 2` and every `1 ≤ a` with `2a + 2 ≤ L = log U`,

`2π (a/L) · #{ρ : Re ρ ≥ ½ + 2a/L, T₁ ≤ Im ρ ≤ T₂} ≤ (T₂ − T₁) A e^{−a/1200} + K L`

(`exists_selberg_shortWindow_nearLine_zeroDensity`). Summing over dyadic shells in the depth
gives the weighted count
`Σ_{Re w > ½ + v₀} m_w e^{λ(Re w − ½)L} ≤ (W' A/(π v₀))(1 + 4800/(v₀L)) e^{−v₀L/4800} + L (KL/(πv₀)) e^{λL}`,
`W' = T₂ − T₁` (`exists_shortWindowZeros_weighted_le`): the proportion of zeros at depth `v₀`
decays like `e^{−v₀L/4800}` on every window of length `U^{99/100}`, not only on dyadic ones.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- **Short-window exponential zero density.** For all large `U`, with `L = log U`, every window
`[B, B + W] ⊂ [U/4, U/2]` of length `W ≥ U^{99/100} + 2` has admissible heights
`T₁ ∈ (B, B + 1)`, `T₂ ∈ (B + W − 1, B + W)` such that for every `1 ≤ a` with `2a + 2 ≤ L` the zeros
with `Re ρ ≥ 1/2 + 2a/L` between them satisfy
`2π (a/L) · #zeros ≤ (T₂ − T₁) A e^{−a/1200} + K L`. -/
theorem exists_selberg_shortWindow_nearLine_zeroDensity :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop, ∀ B W : ℝ, U / 4 ≤ B → B + W ≤ U / 2 →
      Real.exp (99 / 100 * Real.log U) + 2 ≤ W →
      ∃ T₁ ∈ Ioo B (B + 1), ∃ T₂ ∈ Ioo (B + W - 1) (B + W),
        ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ Real.log U →
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          2 * Real.pi * ((a / Real.log U) *
            ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
            (T₂ - T₁) * (A * Real.exp (-(a / 1200))) + K * Real.log U := by
  obtain ⟨C, K₀, hC, hK₀, hcons⟩ := exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide
  obtain ⟨Cf, hCf, htail⟩ := exists_eventually_integral_hbMollifiedTail_rightShift_le_len
  obtain ⟨CM, hCM⟩ := exists_sum_vonMangoldt_sq_div_le
  have hA₀0 : 0 < 128 + 120 * Cf := by positivity
  refine ⟨(3 * Real.sqrt (128 + 120 * Cf) + 2 * (128 + 120 * Cf)) / 2, C + 2 * K₀, by positivity,
    by positivity, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (Real.exp (max 1000 (100 * |CM|)))]
    with U htailU hUL₀
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hUL₀
  have hL := Real.log_le_log (Real.exp_pos _) hUL₀
  rw [Real.log_exp] at hL
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  have hUexp : U = Real.exp L := by rw [hLdef, Real.exp_log hU0]
  rw [← hLdef] at hL
  subst hUexp
  simp only [Real.log_exp] at htailU ⊢
  intro B W hB hBW hW
  have hL1000 : 1000 ≤ L := le_trans (le_max_left _ _) hL
  have hLCM : 100 * |CM| ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hU100 : Real.exp L ^ ((1 : ℝ) / 100) = Real.exp (L / 100) := by
    rw [← Real.exp_mul]; ring_nf
  have hU200 : Real.exp L ^ ((1 : ℝ) / 200) = Real.exp (L / 200) := by
    rw [← Real.exp_mul]; ring_nf
  have hU99 : Real.exp L ^ ((99 : ℝ) / 100) = Real.exp (99 / 100 * L) := by
    rw [← Real.exp_mul]; ring_nf
  set X : ℕ := ZetaGateProductAFE.mollN (Real.exp L) with hXdef
  set Y : ℕ := ⌊Real.exp (L / 200)⌋₊ with hYdef
  have hXle : (X : ℝ) ≤ Real.exp (L / 100) := by
    rw [← hU100]; exact ZetaGateProductAFE.mollN_le (Real.exp_pos L).le
  have hXgt : Real.exp (L / 100) - 1 < X := by
    rw [← hU100]; exact ZetaGateProductAFE.mollN_gt (Real.exp L)
  have hYle : (Y : ℝ) ≤ Real.exp (L / 200) := Nat.floor_le (Real.exp_pos _).le
  have hYgt : Real.exp (L / 200) - 1 < Y := by
    have := Nat.lt_floor_add_one (Real.exp (L / 200))
    linarith
  obtain ⟨hY2, hYX, hYhalf, hXhalf, -, -, -, -⟩ := twoLength_scale_facts hL1000 hXle hXgt hYle hYgt
  obtain ⟨h6, -, -, -, hU160, -⟩ := nearLine_scale_facts (by linarith : (500 : ℝ) ≤ L)
  have hbn : ∀ n ∈ Finset.Icc 1 X, ‖twoLengthCoeff X Y n‖ ≤ 1 :=
    fun n hn => norm_twoLengthCoeff_le (by omega) hYX hn
  obtain ⟨T₁, hT₁, T₂, hT₂, hE1, hE2⟩ := exists_admissible_heights_of_mollifier
    (b := twoLengthCoeff X Y) (N := X) (by omega) (twoLengthCoeff_one (by omega) hYX) hbn
    (A₁ := B) (B₁ := B + 1) (A₂ := B + W - 1) (B₂ := B + W) (by linarith) (by linarith)
    (by linarith) (by linarith)
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha haL Z hZ => ?_⟩
  have hT₁₂ : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hfX := htailU X (by rw [hU100]; exact hXle) (by rw [hU200]; exact hXhalf) a (by linarith)
    haL T₁ T₂ (by linarith [hT₁.1]) hT₁₂ (by linarith [hT₂.2])
  have hexp12 : Real.exp (L / 200) ≤ Real.exp (L / 100) := Real.exp_le_exp.mpr (by linarith)
  have hfY := htailU Y (by rw [hU100]; linarith) (by rw [hU200]; exact hYhalf) a (by linarith)
    haL T₁ T₂ (by linarith [hT₁.1]) hT₁₂ (by linarith [hT₂.2])
  rw [hU99] at hfX hfY
  have hMsq := integral_normSq_zetaTwoLength_rightShift_le hL1000 hLCM hCf hXle hXgt hYle hYgt
    (hCM X (by omega)) (by linarith) (by linarith) (by linarith [hT₁.1]) hT₁₂ hlen hfX hfY
  have hσ₀a : 1 / 4 ≤ 1 / 2 + a / L := by
    have : 0 < a / L := div_pos (by linarith) hL0
    linarith
  have hσ₀b : 1 / 2 + a / L < 2 := by
    have : a / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hmem : ∀ x ∈ Icc (1 / 2 + a / L) (15 / 2 : ℝ), x ∈ Icc (1 / 4 : ℝ) (15 / 2) :=
    fun x hx => ⟨le_trans hσ₀a hx.1, hx.2⟩
  have hXX : (1 : ℝ) ≤ (X : ℝ) ^ (5 : ℕ) :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ X))
  have hmain := hcons (twoLengthCoeff X Y) X (by omega) (twoLengthCoeff_one (by omega) hYX) hbn
    (fun n _ => conj_twoLengthCoeff X Y n) _ hXX
    (sum_norm_twoLengthCoeff_mul_rpow_le (by omega) hYX) (1 / 2 + a / L) T₁ T₂ _
    hσ₀a hσ₀b (by linarith [hT₁.1]) hT12
    (fun x hx => (hE1 x (hmem x hx)).1) (fun x hx => (hE2 x (hmem x hx)).1)
    (fun x hx => (hE1 x (hmem x hx)).2) (fun x hx => (hE2 x (hmem x hx)).2)
    hMsq Z hZ (a / L) (div_pos (by linarith) hL0).le
  have hfilter : Z.filter (fun w => 1 / 2 + a / L + a / L ≤ w.re) =
      Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re) := by
    refine Finset.filter_congr fun w _ => ?_
    rw [show 1 / 2 + a / L + a / L = 1 / 2 + 2 * a / L by ring]
  rw [hfilter] at hmain
  have hlogT₂ : Real.log T₂ ≤ L := by
    have h1 : T₂ ≤ Real.exp L := le_trans hT₂.2.le (by linarith [Real.exp_pos L])
    have := Real.log_le_log (by linarith [hT₁.1, hT₁.2, hT₂.1]) h1
    rwa [Real.log_exp] at this
  have hlogMb : Real.log ((X : ℝ) ^ (5 : ℕ)) ≤ L := by
    rw [Real.log_pow]
    have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < X)) hXle
    rw [Real.log_exp] at h1
    push_cast
    linarith
  exact twoLength_final_count (by linarith) hC.le hK₀.le hA₀0.le (by linarith) hT12 hlogT₂
    hlogMb hmain

/-- **Short-window count.** On every admissible window of length `≥ U^{99/100} + 2` in
`[U/4, U/2]`, the zeros at depth `≥ v` number at most
`((T₂ − T₁) A e^{−vL/2400} + K L)/(π v)`. -/
theorem exists_shortWindowZeros_count_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop, ∀ B W : ℝ, U / 4 ≤ B → B + W ≤ U / 2 →
      Real.exp (99 / 100 * Real.log U) + 2 ≤ W →
      ∃ T₁ ∈ Ioo B (B + 1), ∃ T₂ ∈ Ioo (B + W - 1) (B + W),
        ∀ v : ℝ, 2 / Real.log U ≤ v → v ≤ 1 - 2 / Real.log U →
          ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re), zeroMult w ≤
            ((T₂ - T₁) * A * Real.exp (-(v * Real.log U / 2400)) + K * Real.log U) /
              (Real.pi * v) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_selberg_shortWindow_nearLine_zeroDensity
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (Real.exp 4), eventually_ge_atTop 8] with U hU hUe hU8
  intro B W hB hBW hW
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hU B W hB hBW hW
  refine ⟨T₁, hT₁, T₂, hT₂, fun v hv1 hv2 => ?_⟩
  have hL : 4 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 4) hUe; rwa [Real.log_exp] at this
  have hL0 : 0 < Real.log U := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv1
  have hT₁pos : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1, hW, Real.exp_pos (99 / 100 * Real.log U)]
  set a : ℝ := v * Real.log U / 2 with ha
  have ha1 : 1 ≤ a := by
    rw [ha, le_div_iff₀ (by norm_num)]
    have := (div_le_iff₀ hL0).mp hv1
    linarith
  have ha2 : 2 * a + 2 ≤ Real.log U := by
    rw [ha]
    have := (le_sub_iff_add_le.mp hv2)
    have h2 : 2 / Real.log U * Real.log U = 2 := by field_simp
    nlinarith
  have hZ := hcount a ha1 ha2 (windowZeros T₁ T₂) (mem_windowZeros_iff hT₁pos hT12)
  have hfilt : (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re) =
      (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re) := by
    refine Finset.filter_congr fun w _ => ?_
    rw [show 2 * a / Real.log U = v by rw [ha]; field_simp]
  rw [hfilt] at hZ
  have hsum : ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re), zeroMult w =
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    refine Finset.sum_congr rfl fun w hw => ?_
    have hwmem := (mem_windowZeros_iff hT₁pos hT12 w).1 (Finset.mem_filter.mp hw).1
    have hz1 : w ≠ 1 := by
      intro h
      have := (Complex.mem_reProdIm.mp hwmem.1).2
      rw [h, uIcc_of_le hT12] at this
      simp at this
      linarith [this.1]
    exact zeroMult_eq_zeta_order hz1
  rw [hsum]
  have hav : a / Real.log U = v / 2 := by rw [ha]; field_simp
  rw [hav] at hZ
  rw [le_div_iff₀ (by positivity)]
  have hexp : Real.exp (-(a / 1200)) = Real.exp (-(v * Real.log U / 2400)) := by
    rw [ha]; ring_nf
  rw [hexp] at hZ
  nlinarith

/-- **Short-window weighted count.** For `0 ≤ λ` with `2λ ≤ 1/4800` and `2/L ≤ v₀ ≤ 1/4`, on every
admissible window `[T₁, T₂]` of length `≥ U^{99/100}` in `[U/4, U/2]`,
`Σ_{Re w > ½ + v₀} m_w e^{λ(Re w − ½)L} ≤ ((T₂ − T₁) A/(π v₀))(1 + 4800/(v₀L)) e^{−v₀L/4800}
  + L (KL/(πv₀)) e^{λL}`. -/
theorem exists_shortWindowZeros_weighted_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop, ∀ B W : ℝ, U / 4 ≤ B → B + W ≤ U / 2 →
      Real.exp (99 / 100 * Real.log U) + 2 ≤ W →
      ∃ T₁ ∈ Ioo B (B + 1), ∃ T₂ ∈ Ioo (B + W - 1) (B + W),
        ∀ lam v₀ : ℝ, 0 ≤ lam → 2 * lam ≤ 1 / 4800 → 2 / Real.log U ≤ v₀ → v₀ ≤ 1 / 4 →
          ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re),
              zeroMult w * Real.exp (lam * (w.re - 1 / 2) * Real.log U) ≤
            (T₂ - T₁) * A / (Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log U)) *
                Real.exp (-(v₀ * Real.log U / 4800)) +
              Real.log U * (K * Real.log U / (Real.pi * v₀) * Real.exp (lam * Real.log U)) := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_shortWindowZeros_count_le
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (Real.exp 4), eventually_ge_atTop 8] with U hU hUe hU8
  intro B W hB hBW hW
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hU B W hB hBW hW
  refine ⟨T₁, hT₁, T₂, hT₂, fun lam v₀ hlam hlam2 hv1 hv2 => ?_⟩
  set L := Real.log U with hLdef
  have hL : 4 ≤ L := by
    have := Real.log_le_log (Real.exp_pos 4) hUe; rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  have hv0 : 0 < v₀ := lt_of_lt_of_le (by positivity) hv1
  have hT₁pos : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1, hW, Real.exp_pos (99 / 100 * L)]
  set V : ℝ := 4 * (T₂ - T₁) with hV
  have hV0 : 0 ≤ V := by rw [hV]; linarith
  set J : ℕ := ⌊L⌋₊ with hJ
  have hJL : (J : ℝ) ≤ L := Nat.floor_le hL0.le
  have hJpow : L < 2 ^ J := by
    have h1 := Nat.lt_floor_add_one L
    have h2 : ((J + 1 : ℕ) : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt Nat.lt_two_pow_self
    push_cast at h2
    rw [← hJ] at h1
    linarith
  have hcover : ∀ w ∈ windowZeros T₁ T₂, w.re - 1 / 2 ≤ 2 ^ J * v₀ := by
    intro w hw
    have h1 := windowZeros_re_lt_one hT₁pos hT12 hw
    have h2 : 2 ≤ 2 ^ J * v₀ := by
      have := (div_le_iff₀ hL0).mp hv1
      nlinarith
    linarith
  have hfm : Monotone (fun b : ℝ => Real.exp (lam * b * L)) := by
    intro a b hab
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hab hlam
    nlinarith
  have hsh := sum_mult_weight_le_shells (windowZeros T₁ T₂) (f := fun b => Real.exp (lam * b * L))
    (fun _ => (Real.exp_pos _).le) hfm hv0 J hcover
  refine hsh.trans ?_
  set c : ℝ := v₀ * L / 4800 with hc
  have hc0 : 0 < c := by positivity
  have hterm : ∀ j ∈ Finset.range J, Real.exp (lam * (2 ^ (j + 1) * v₀) * L) *
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 2 ^ j * v₀ ≤ w.re), zeroMult w ≤
      V * A / (4 * Real.pi * v₀) * Real.exp (-(2 ^ j * c)) +
        K * L / (Real.pi * v₀) * Real.exp (lam * L) := by
    intro j _
    have hrhs0 : 0 ≤ V * A / (4 * Real.pi * v₀) * Real.exp (-(2 ^ j * c)) +
        K * L / (Real.pi * v₀) * Real.exp (lam * L) := by positivity
    have hexpc : -(2 ^ j * c) = -(2 ^ j * v₀ * L / 4800) := by rw [hc]; ring
    by_cases hjv : 2 ^ j * v₀ ≤ 1 / 2
    · have hj1 : 2 ^ (j + 1) * v₀ ≤ 1 := by rw [pow_succ]; linarith
      have hvle : 2 ^ j * v₀ ≤ 1 - 2 / L := by
        have : 2 / L ≤ 1 / 2 := by rw [div_le_iff₀ hL0]; linarith
        linarith
      have hvge : 2 / L ≤ 2 ^ j * v₀ := by
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        nlinarith
      have hN := hcount (2 ^ j * v₀) hvge hvle
      have hN' : ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 2 ^ j * v₀ ≤ w.re),
          zeroMult w ≤ ((V / 4) * A * Real.exp (-(2 ^ j * v₀ * L / 2400)) + K * L) /
            (Real.pi * (2 ^ j * v₀)) := by
        rw [show V / 4 = T₂ - T₁ by rw [hV]; ring]
        exact hN
      rw [hexpc]
      exact shell_term_le j hV0 hA.le hK hL0.le hlam hlam2 hv0 hj1 hN'
    · push Not at hjv
      have hempty : (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 2 ^ j * v₀ ≤ w.re) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun w hw hle => ?_
        have := windowZeros_re_lt_one hT₁pos hT12 hw
        linarith
      rw [hempty, Finset.sum_empty, mul_zero]
      exact hrhs0
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgeo := sum_exp_neg_two_pow_le hc0 J
  have h1c : 1 + 1 / c = 1 + 4800 / (v₀ * L) := by rw [hc]; field_simp
  rw [h1c] at hgeo
  have hpos : 0 ≤ V * A / (4 * Real.pi * v₀) := by positivity
  have hsecond : 0 ≤ K * L / (Real.pi * v₀) * Real.exp (lam * L) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hgeo hpos
  have h2 := mul_le_mul_of_nonneg_right hJL hsecond
  have hVA : V * A / (4 * Real.pi * v₀) = (T₂ - T₁) * A / (Real.pi * v₀) := by
    rw [hV]; field_simp
  rw [hVA] at h1 ⊢
  rw [hc] at h1
  nlinarith

end RHTower
