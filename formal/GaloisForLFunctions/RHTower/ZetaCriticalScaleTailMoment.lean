import GaloisForLFunctions.RHTower.ZetaFixedSigmaDensity

/-!
# The off-line first moment beyond the critical scale

Write `L = log U`.  The Selberg-type count of zeros with `Re ρ ≥ ½ + a/L + δ` on a Littlewood window
(`exists_zeroCount_fixedShift_le`) holds with one window for all shifts `1 ≤ a ≤ L/2 − 1` and all
`δ ≥ 0` at once (`exists_zeroCount_shift_le_uniform`): the only dependence of the mollified tail
estimate on `a` is the condition `2a + 2 ≤ L`.  With `a = δL = 2^{j−1}c` the zeros of the dyadic
shell `2^j c/L ≤ Re ρ − ½ < 2^{j+1}c/L` number `≪ (T₂−T₁) L r_A(2^{j−1}c)/2^j c`, and
`r_A(a) ≤ D_A/a`, so summing the shells gives

  `Σ_{Re ρ − ½ ≥ c/L} m_ρ (Re ρ − ½) ≤ (D/c)(T₂ − T₁) + K L²`   for all `c ≥ 2`
  (`exists_offLineTailMoment_window_le`).

Two receivers localise at an off-line zero within its shadow `|t − Im ρ| ≤ Re ρ − ½`:
* the Hadamard sign `Re (ξ'/ξ)(σ + it) ≥ 0` on the line `σ = ½ + c/L` fails only at heights within
  the shadow of a zero with `Re ρ ≥ σ` (`exists_volume_hadamardFail_criticalScale_le`);
* vertical monotonicity of `y ↦ |Ξ(x + iy)|` on `y ≥ c/L` fails only at abscissae within the
  shadow of a zero with `Re ρ > ½ + c/L` (`exists_volume_monotoneFail_criticalScale_le`).

Each failure set therefore has measure at most `2(D/c)(T₂ − T₁) + O(L²)`: at the zero-spacing
scale `c/log T` both receivers hold on a proportion `≥ 1 − O(1/c)` of the window.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-- **The mollified tail on right-shifted lines, uniformly in the shift.** -/
theorem exists_eventually_integral_hbMollifiedTail_rightShift_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U in atTop, ∀ a : ℝ, 0 < a → 2 * a + 2 ≤ Real.log U →
      ∀ T₁ T₂ : ℝ, U / 4 ≤ T₁ → T₁ ≤ T₂ → T₂ ≤ U / 2 →
      ∫ t in T₁..T₂, ‖hbMollifiedTail (ZetaGateProductAFE.mollN U)
          (((1 / 2 + a / Real.log U : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C * Real.exp (-((a + 1) / 300)) * (T₂ - T₁ + 2 * U ^ ((99 : ℝ) / 100)) := by
  obtain ⟨c₀, hc₀, hgate⟩ :=
    ZetaGateProductAFE.exists_highBlock_window_bound_productAFE (R := 1) one_pos
  obtain ⟨CW, hCW, hW⟩ := exists_norm_nearLineField_le
  obtain ⟨CM, hCM⟩ := exists_sum_vonMangoldt_sq_div_le
  refine ⟨Real.exp 2 * (18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1), by positivity, ?_⟩
  filter_upwards [hgate 1 one_pos, Filter.eventually_ge_atTop (Real.exp
      (max 500 (1280000 * (4 + max 0 (Real.log (16 * CW ^ 2))))))]
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
  have hL500 : 500 ≤ L := le_trans (le_max_left _ _) hL
  have hLK : 1280000 * (4 + max 0 (Real.log (16 * CW ^ 2))) ≤ L := le_trans (le_max_right _ _) hL
  have hU100 : Real.exp L ^ ((1 : ℝ) / 100) = Real.exp (L / 100) := by
    rw [← Real.exp_mul]; ring_nf
  have hU99 : Real.exp L ^ ((99 : ℝ) / 100) = Real.exp (99 / 100 * L) := by
    rw [← Real.exp_mul]; ring_nf
  have hNle := ZetaGateProductAFE.mollN_le (Real.exp_pos L).le
  have hNgt := ZetaGateProductAFE.mollN_gt (Real.exp L)
  rw [hU100] at hNle hNgt
  obtain ⟨hN2, -⟩ := nearLine_length_facts hL500 hNle hNgt
  rw [hU99]
  exact integral_hbMollifiedTail_rightShift_le_core ha hc₀ hCW (hW _ hN2)
    (hCM _ (by omega)) hL500 hLa hLK hNle hNgt hgU hT₁ hT₁₂ hT₂

/-- **The Littlewood count with a horizontal shift, one window for all shifts.** -/
theorem exists_zeroCount_shift_le_uniform :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ Real.log U → ∀ δ : ℝ, 0 ≤ δ →
          2 * Real.pi * (δ *
            ∑ w ∈ Z.filter (fun w => 1 / 2 + a / Real.log U + δ ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
            (T₂ - T₁) / 2 * selbergNearLineRate A a + K * Real.log U := by
  obtain ⟨C, K₀, hC, hK₀, hcons⟩ := exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide
  obtain ⟨Cf, hCf, htail⟩ := exists_eventually_integral_hbMollifiedTail_rightShift_le_uniform
  refine ⟨max 400000 (3 * Cf), C + 2 * K₀, by positivity, by positivity, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (Real.exp 500)] with U htailU hUL₀
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hUL₀
  have hL := Real.log_le_log (Real.exp_pos _) hUL₀
  rw [Real.log_exp] at hL
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  have hUexp : U = Real.exp L := by rw [hLdef, Real.exp_log hU0]
  rw [← hLdef] at hL
  subst hUexp
  simp only [Real.log_exp] at htailU ⊢
  have hL500 : 500 ≤ L := hL
  obtain ⟨-, hHU, -, -, hU160, -⟩ := nearLine_scale_facts hL500
  have hU100 : Real.exp L ^ ((1 : ℝ) / 100) = Real.exp (L / 100) := by
    rw [← Real.exp_mul]; ring_nf
  have hU99 : Real.exp L ^ ((99 : ℝ) / 100) = Real.exp (99 / 100 * L) := by
    rw [← Real.exp_mul]; ring_nf
  have hNle := ZetaGateProductAFE.mollN_le (Real.exp_pos L).le
  have hNgt := ZetaGateProductAFE.mollN_gt (Real.exp L)
  rw [hU100] at hNle hNgt
  obtain ⟨hN2, -, -, -, -, -⟩ := nearLine_length_facts hL500 hNle hNgt
  have hlogN_le : Real.log (ZetaGateProductAFE.mollN (Real.exp L) : ℝ) ≤ L / 100 := by
    have := Real.log_le_log (by exact_mod_cast (by omega : 0 < ZetaGateProductAFE.mollN
      (Real.exp L))) hNle
    rwa [Real.log_exp] at this
  obtain ⟨T₁, hT₁, T₂, hT₂, hE1, hE2⟩ := exists_admissible_heights_hbMollifier hN2
    (A₁ := Real.exp L / 4) (B₁ := Real.exp L / 4 + 1) (A₂ := Real.exp L / 2 - 1)
    (B₂ := Real.exp L / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨T₁, hT₁, T₂, hT₂, fun Z hZ a ha hLa δ hδ => ?_⟩
  have hT₁₂ : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hf := htailU a (by linarith) hLa T₁ T₂ hT₁.1.le hT₁₂ hT₂.2.le
  rw [hU99] at hf
  have hMsq := integral_normSq_zetaHb_rightShift_le ha hCf hL500 hLa hNle hNgt
    (by linarith [hT₁.1]) hT₁₂ hlen hf
  have hL0 : 0 < L := by linarith
  have hσ₀a : 1 / 4 ≤ 1 / 2 + a / L := by
    have : 0 < a / L := div_pos (by linarith) hL0
    linarith
  have hσ₀b : 1 / 2 + a / L < 2 := by
    have : a / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hmem : ∀ x ∈ Icc (1 / 2 + a / L) (15 / 2 : ℝ), x ∈ Icc (1 / 4 : ℝ) (15 / 2) :=
    fun x hx => ⟨le_trans hσ₀a hx.1, hx.2⟩
  have hNN : (1 : ℝ) ≤ ((ZetaGateProductAFE.mollN (Real.exp L) : ℕ) : ℝ) ^ (5 : ℕ) :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ ZetaGateProductAFE.mollN (Real.exp L)))
  have hmain := hcons (hbCoeff (ZetaGateProductAFE.mollN (Real.exp L)))
    (ZetaGateProductAFE.mollN (Real.exp L)) (by omega) (hbCoeff_one hN2)
    (fun n hn => norm_hbCoeff_le hN2 hn) (fun n _ => conj_hbCoeff _ n) _ hNN
    (sum_norm_hbCoeff_mul_rpow_le hN2) (1 / 2 + a / L) T₁ T₂ _
    hσ₀a hσ₀b (by linarith [hT₁.1]) hT12
    (fun x hx => (hE1 x (hmem x hx)).1) (fun x hx => (hE2 x (hmem x hx)).1)
    (fun x hx => (hE1 x (hmem x hx)).2) (fun x hx => (hE2 x (hmem x hx)).2)
    hMsq Z hZ δ hδ
  exact fixedShift_count_le_of_meanSquare (by positivity) hK₀.le (by linarith) hN2 hT12
    (by linarith [hT₂.2, Real.exp_pos L]) (by linarith [hT₁.1]) hmain hC.le hlogN_le

/-- **The near-line rate decays like `1/a`.** -/
theorem selbergNearLineRate_le_div {A a : ℝ} (hA : 0 ≤ A) (ha : 1 ≤ a) :
    selbergNearLineRate A a ≤ (3 * Real.sqrt (180001 * A) + 360002 * A) / a := by
  have ha0 : 0 < a := by linarith
  have hexp : Real.exp (-(a / 300)) ≤ 180000 / a ^ 2 := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ a / 300 by positivity)
    have hsq : a ^ 2 ≤ 180000 * Real.exp (a / 300) := by nlinarith
    rw [Real.exp_neg, le_div_iff₀ (by positivity)]
    calc (Real.exp (a / 300))⁻¹ * a ^ 2 ≤ (Real.exp (a / 300))⁻¹ * (180000 * Real.exp (a / 300)) :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (Real.exp_pos _).le)
      _ = 180000 := by field_simp
  have hη : A * (1 / a ^ 2 + Real.exp (-(a / 300))) ≤ 180001 * A / a ^ 2 := by
    have h1 : 1 / a ^ 2 + Real.exp (-(a / 300)) ≤ 180001 / a ^ 2 := by
      have : 1 / a ^ 2 + 180000 / a ^ 2 = 180001 / a ^ 2 := by ring
      linarith
    calc A * (1 / a ^ 2 + Real.exp (-(a / 300))) ≤ A * (180001 / a ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hA
      _ = 180001 * A / a ^ 2 := by ring
  have hsqrt : Real.sqrt (A * (1 / a ^ 2 + Real.exp (-(a / 300)))) ≤
      Real.sqrt (180001 * A) / a := by
    calc Real.sqrt (A * (1 / a ^ 2 + Real.exp (-(a / 300)))) ≤ Real.sqrt (180001 * A / a ^ 2) :=
          Real.sqrt_le_sqrt hη
      _ = Real.sqrt (180001 * A) / a := by
          rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq ha0.le]
  have hlin : 180001 * A / a ^ 2 ≤ 180001 * A / a := by
    apply div_le_div_of_nonneg_left (by positivity) ha0
    nlinarith
  unfold selbergNearLineRate
  have e : (3 * Real.sqrt (180001 * A) + 360002 * A) / a =
      3 * (Real.sqrt (180001 * A) / a) + 2 * (180001 * A / a) := by ring
  rw [e]
  linarith

/-- **The dyadic level of a displacement.** Every `u ≥ c/L` lies in a dyadic shell
`2^j c/L ≤ u < 2·2^j c/L`. -/
theorem exists_dyadic_level {u c L : ℝ} (hc : 0 < c) (hL : 0 < L) (hu : c / L ≤ u) :
    ∃ j : ℕ, 2 ^ j * c / L ≤ u ∧ u < 2 * (2 ^ j * c / L) := by
  have hx1 : 1 ≤ u * L / c := by
    rw [le_div_iff₀ hc, one_mul]
    rw [div_le_iff₀ hL] at hu
    linarith
  set x := u * L / c with hxdef
  set m := Nat.log 2 ⌊x⌋₊
  have hfl : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr hx1).ne'
  have h1 : (2 : ℝ) ^ m ≤ x := by
    have := Nat.pow_log_le_self 2 hfl
    calc (2 : ℝ) ^ m = ((2 ^ m : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ x := Nat.floor_le (by linarith)
  have h2 : x < 2 * 2 ^ m := by
    have h3 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊x⌋₊
    have h4 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have h5 : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at h5
    rw [pow_succ] at h5
    linarith
  refine ⟨m, ?_, ?_⟩
  · rw [div_le_iff₀ hL]
    rw [hxdef, le_div_iff₀ hc] at h1
    linarith
  · rw [hxdef, div_lt_iff₀ hc] at h2
    rw [mul_div_assoc', lt_div_iff₀ hL]
    linarith

/-- **The off-line first moment beyond the critical scale.** For all large `U` there is one
Littlewood window on which, for every `c ≥ 2`, the zeros with `Re ρ − ½ ≥ c/log U` carry off-line
first moment at most `(D/c)(T₂ − T₁) + K log² U`. -/
theorem exists_offLineTailMoment_window_le :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          ∀ c : ℝ, 2 ≤ c →
          ∑ w ∈ Z.filter (fun w => 1 / 2 + c / Real.log U ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) ≤
            D / c * (T₂ - T₁) + K * Real.log U ^ 2 := by
  classical
  obtain ⟨A, K, hA, hK, hcount⟩ := exists_zeroCount_shift_le_uniform
  set DA := 3 * Real.sqrt (180001 * A) + 360002 * A with hDA
  have hDA0 : 0 ≤ DA := by positivity
  refine ⟨4 * DA / Real.pi, 2 * K, by positivity, by positivity, ?_⟩
  filter_upwards [hcount, eventually_ge_atTop (Real.exp 4), eventually_ge_atTop (100 : ℝ)]
    with U hU hU4 hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun Z hZ c hc2 => ?_⟩
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hU4
  set L := Real.log U with hLdef
  have hL4 : 4 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hU4
    rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hlen0 : 0 ≤ T₂ - T₁ := by linarith
  set m : ℂ → ℝ := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ) with hmdef
  have hm0 : ∀ w, 0 ≤ m w := fun w => Nat.cast_nonneg _
  set Zc := Z.filter (fun w => 1 / 2 + c / L ≤ w.re)
  set J := ⌊L⌋₊ + 1
  -- every zero of `Z` has real part `< 1`
  have hre1 : ∀ w ∈ Z, w.re < 1 := by
    intro w hw
    obtain ⟨-, hw0⟩ := (hZ w).mp hw
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hw0
  -- the shell sums
  set S : ℕ → ℝ := fun j => ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 ^ j * c / L ≤ w.re), m w
    with hSdef
  have hshell : ∀ j ∈ Finset.range J, 2 ^ j * c / L * S j ≤
      ((T₂ - T₁) / 2 * (DA / (2 ^ j * c / 2)) + K * L) / Real.pi := by
    intro j _
    have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    set a := 2 ^ j * c / 2 with hadef
    have ha1 : 1 ≤ a := by rw [hadef]; nlinarith
    have hrhs0 : 0 ≤ ((T₂ - T₁) / 2 * (DA / a) + K * L) / Real.pi := by
      have : 0 ≤ DA / a := div_nonneg hDA0 (by linarith)
      positivity
    by_cases hbig : 2 * a + 2 ≤ L
    · have hδ0 : 0 ≤ a / L := div_nonneg (by linarith) hL0.le
      have h := hc Z hZ a ha1 hbig (a / L) hδ0
      have hfilt : Z.filter (fun w => 1 / 2 + a / L + a / L ≤ w.re) =
          Z.filter (fun w => 1 / 2 + 2 ^ j * c / L ≤ w.re) := by
        refine Finset.filter_congr fun w _ => ?_
        have : 1 / 2 + a / L + a / L = 1 / 2 + 2 ^ j * c / L := by rw [hadef]; ring
        rw [this]
      rw [hfilt] at h
      have hrate := selbergNearLineRate_le_div hA.le ha1
      have hr : (T₂ - T₁) / 2 * selbergNearLineRate A a ≤ (T₂ - T₁) / 2 * (DA / a) :=
        mul_le_mul_of_nonneg_left hrate (by linarith)
      have e : 2 ^ j * c / L * S j = (2 * Real.pi * (a / L * S j)) / Real.pi := by
        rw [hadef]; field_simp
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
    · have hempty : S j = 0 := by
        refine Finset.sum_eq_zero fun w hw => ?_
        obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
        exfalso
        have h1 := hre1 w hwZ
        have h2 : 1 / 2 ≤ 2 ^ j * c / L := by
          rw [le_div_iff₀ hL0]
          rw [not_le] at hbig
          rw [hadef] at hbig
          linarith
        linarith
      rw [hempty, mul_zero]
      exact hrhs0
  -- each zero of `Zc` lies in its dyadic shell
  have hlevel : ∀ w ∈ Zc, w.re - 1 / 2 ≤
      2 * ∑ j ∈ (Finset.range J).filter (fun j => 2 ^ j * c / L ≤ w.re - 1 / 2),
        2 ^ j * c / L := by
    intro w hw
    obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
    obtain ⟨j, hj1, hj2⟩ := exists_dyadic_level (u := w.re - 1 / 2) hc0 hL0 (by linarith)
    have hjJ : j ∈ Finset.range J := by
      rw [Finset.mem_range]
      have h1 := hre1 w hwZ
      have hj : (2 : ℝ) ^ j * c < L := by
        rw [div_le_iff₀ hL0] at hj1
        nlinarith
      have hjl : (j : ℝ) < 2 ^ j := by
        have := Nat.lt_two_pow_self (n := j)
        exact_mod_cast this
      have hjL : (j : ℝ) < L := by nlinarith
      have : j ≤ ⌊L⌋₊ := Nat.le_floor hjL.le
      omega
    have hmem : j ∈ (Finset.range J).filter (fun j => 2 ^ j * c / L ≤ w.re - 1 / 2) :=
      Finset.mem_filter.mpr ⟨hjJ, hj1⟩
    have hsingle := Finset.single_le_sum (f := fun j : ℕ => 2 ^ j * c / L)
      (fun i _ => by positivity) hmem
    linarith
  -- swap the sums
  have hswap : ∑ w ∈ Zc, m w * (w.re - 1 / 2) ≤
      2 * ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j := by
    calc ∑ w ∈ Zc, m w * (w.re - 1 / 2)
        ≤ ∑ w ∈ Zc, m w * (2 * ∑ j ∈ (Finset.range J).filter
            (fun j => 2 ^ j * c / L ≤ w.re - 1 / 2), 2 ^ j * c / L) :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hlevel w hw) (hm0 w)
      _ = 2 * ∑ j ∈ Finset.range J, ∑ w ∈ Zc.filter (fun w => 2 ^ j * c / L ≤ w.re - 1 / 2),
            m w * (2 ^ j * c / L) := by
          have hcomm : ∑ w ∈ Zc, m w * ∑ j ∈ (Finset.range J).filter
              (fun j => 2 ^ j * c / L ≤ w.re - 1 / 2), 2 ^ j * c / L =
              ∑ j ∈ Finset.range J, ∑ w ∈ Zc.filter (fun w => 2 ^ j * c / L ≤ w.re - 1 / 2),
                m w * (2 ^ j * c / L) := by
            simp_rw [Finset.mul_sum, Finset.sum_filter]
            exact Finset.sum_comm
          rw [← hcomm, Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ 2 * ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by norm_num)
          rw [hSdef]
          simp only
          rw [Finset.mul_sum]
          calc ∑ w ∈ Zc.filter (fun w => 2 ^ j * c / L ≤ w.re - 1 / 2), m w * (2 ^ j * c / L)
              ≤ ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 ^ j * c / L ≤ w.re), m w * (2 ^ j * c / L) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ =>
                  mul_nonneg (hm0 w) (by positivity)
                intro w hw
                obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
                exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw1).1, by linarith⟩
            _ = ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 ^ j * c / L ≤ w.re), 2 ^ j * c / L * m w := by
                refine Finset.sum_congr rfl fun w _ => by ring
  -- sum the shells
  have hgeo : ∑ j ∈ Finset.range J, DA / (2 ^ j * c / 2) ≤ 4 * DA / c := by
    have e : ∀ j : ℕ, DA / (2 ^ j * c / 2) = (2 * DA / c) * (1 / 2) ^ j := by
      intro j
      rw [one_div_pow]
      field_simp
    simp_rw [e]
    rw [← Finset.mul_sum]
    have := sum_geometric_two_le J
    calc 2 * DA / c * ∑ i ∈ Finset.range J, (1 / 2 : ℝ) ^ i ≤ 2 * DA / c * 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 4 * DA / c := by ring
  have hJ : (J : ℝ) ≤ L + 1 := by
    have := Nat.floor_le hL0.le
    push_cast [J]
    linarith
  have htot : ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j ≤
      ((T₂ - T₁) / 2 * (4 * DA / c) + (L + 1) * (K * L)) / Real.pi := by
    calc ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j
        ≤ ∑ j ∈ Finset.range J, ((T₂ - T₁) / 2 * (DA / (2 ^ j * c / 2)) + K * L) / Real.pi :=
          Finset.sum_le_sum hshell
      _ = ((T₂ - T₁) / 2 * ∑ j ∈ Finset.range J, DA / (2 ^ j * c / 2) + J * (K * L)) /
            Real.pi := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
      _ ≤ ((T₂ - T₁) / 2 * (4 * DA / c) + (L + 1) * (K * L)) / Real.pi := by
          refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
          have h1 := mul_le_mul_of_nonneg_left hgeo (show 0 ≤ (T₂ - T₁) / 2 by linarith)
          have h2 := mul_le_mul_of_nonneg_right hJ (show 0 ≤ K * L by positivity)
          linarith
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hfin : 2 * (((T₂ - T₁) / 2 * (4 * DA / c) + (L + 1) * (K * L)) / Real.pi) ≤
      4 * DA / Real.pi / c * (T₂ - T₁) + 2 * K * L ^ 2 := by
    have e : 2 * (((T₂ - T₁) / 2 * (4 * DA / c) + (L + 1) * (K * L)) / Real.pi) =
        4 * DA / Real.pi / c * (T₂ - T₁) + 2 * ((L + 1) * (K * L)) / Real.pi := by
      field_simp
    rw [e]
    have h1 : 2 * ((L + 1) * (K * L)) / Real.pi ≤ 2 * K * L ^ 2 := by
      rw [div_le_iff₀ Real.pi_pos]
      have h := mul_le_mul_of_nonneg_right (show L + 1 ≤ Real.pi * L by nlinarith)
        (show 0 ≤ 2 * (K * L) by positivity)
      linarith
    linarith
  calc ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)
      = ∑ w ∈ Zc, m w * (w.re - 1 / 2) := rfl
    _ ≤ 2 * ∑ j ∈ Finset.range J, 2 ^ j * c / L * S j := hswap
    _ ≤ 2 * (((T₂ - T₁) / 2 * (4 * DA / c) + (L + 1) * (K * L)) / Real.pi) :=
        mul_le_mul_of_nonneg_left htot (by norm_num)
    _ ≤ 4 * DA / Real.pi / c * (T₂ - T₁) + 2 * K * L ^ 2 := hfin

/-- **Three-scale decomposition of the off-line first moment.** On the window of
`exists_offLineTailMoment_window_le`, for `0 < ε` and `c ≥ 2`, the off-line first moment is at most
`ε/L` times the off-line count, plus `c/L` times the count beyond `ε/L`, plus the tail
`(D/c)(T₂ − T₁) + K L²`.  Hence `Σ (Re ρ − ½)⁺ = o(T₂ − T₁)` as soon as, for every `ε > 0`, the zeros
with `Re ρ − ½ ≥ ε/L` are `o((T₂ − T₁) L)`. -/
theorem exists_offLineMoment_window_three_scale_le :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          ∀ ε c : ℝ, 0 < ε → 2 ≤ c →
          ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) ≤
            ε / Real.log U * ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re),
                ((analyticOrderAt riemannZeta w).toNat : ℝ) +
              c / Real.log U * ∑ w ∈ Z.filter (fun w => 1 / 2 + ε / Real.log U ≤ w.re),
                ((analyticOrderAt riemannZeta w).toNat : ℝ) +
              (D / c * (T₂ - T₁) + K * Real.log U ^ 2) := by
  classical
  obtain ⟨D, K, hD, hK, htail⟩ := exists_offLineTailMoment_window_le
  refine ⟨D, K, hD, hK, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (3 : ℝ)] with U hU hU3
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun Z hZ ε c hε hc2 => ?_⟩
  have hL : 0 < Real.log U := Real.log_pos (by linarith)
  set L := Real.log U
  set m : ℂ → ℝ := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ)
  have hm0 : ∀ w, 0 ≤ m w := fun w => Nat.cast_nonneg _
  have hεL : 0 < ε / L := div_pos hε hL
  have hcL : 0 < c / L := div_pos (by linarith) hL
  have hpt : ∀ w ∈ Z.filter (fun w => 1 / 2 < w.re), m w * (w.re - 1 / 2) ≤
      ε / L * m w + (if 1 / 2 + ε / L ≤ w.re then c / L * m w else 0) +
        (if 1 / 2 + c / L ≤ w.re then m w * (w.re - 1 / 2) else 0) := by
    intro w hw
    have hw1 := (Finset.mem_filter.mp hw).2
    have hmw := hm0 w
    have h1 := mul_nonneg hεL.le hmw
    have h2 := mul_nonneg hcL.le hmw
    split_ifs with ha hb hb
    · linarith
    · have := mul_le_mul_of_nonneg_left (show w.re - 1 / 2 ≤ c / L by linarith) hmw
      linarith
    · linarith
    · have := mul_le_mul_of_nonneg_left (show w.re - 1 / 2 ≤ ε / L by linarith) hmw
      linarith
  have hsub1 : (Z.filter (fun w => 1 / 2 < w.re)).filter (fun w => 1 / 2 + ε / L ≤ w.re) =
      Z.filter (fun w => 1 / 2 + ε / L ≤ w.re) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun w _ => ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩
  have hsub2 : (Z.filter (fun w => 1 / 2 < w.re)).filter (fun w => 1 / 2 + c / L ≤ w.re) =
      Z.filter (fun w => 1 / 2 + c / L ≤ w.re) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun w _ => ⟨fun h => h.2, fun h => ⟨by linarith, h⟩⟩
  calc ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re), m w * (w.re - 1 / 2)
      ≤ ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re), (ε / L * m w +
          (if 1 / 2 + ε / L ≤ w.re then c / L * m w else 0) +
          (if 1 / 2 + c / L ≤ w.re then m w * (w.re - 1 / 2) else 0)) :=
        Finset.sum_le_sum hpt
    _ = ε / L * ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re), m w +
          c / L * ∑ w ∈ Z.filter (fun w => 1 / 2 + ε / L ≤ w.re), m w +
          ∑ w ∈ Z.filter (fun w => 1 / 2 + c / L ≤ w.re), m w * (w.re - 1 / 2) := by
        have e1 : ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re), ε / L * m w =
            ε / L * ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re), m w := (Finset.mul_sum _ _ _).symm
        have e2 : ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re),
            (if 1 / 2 + ε / L ≤ w.re then c / L * m w else 0) =
            c / L * ∑ w ∈ Z.filter (fun w => 1 / 2 + ε / L ≤ w.re), m w := by
          rw [← Finset.sum_filter, hsub1, Finset.mul_sum]
        have e3 : ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re),
            (if 1 / 2 + c / L ≤ w.re then m w * (w.re - 1 / 2) else 0) =
            ∑ w ∈ Z.filter (fun w => 1 / 2 + c / L ≤ w.re), m w * (w.re - 1 / 2) := by
          rw [← Finset.sum_filter, hsub2]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3]
    _ ≤ ε / L * ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re), m w +
          c / L * ∑ w ∈ Z.filter (fun w => 1 / 2 + ε / L ≤ w.re), m w +
          (D / c * (T₂ - T₁) + K * L ^ 2) := by
        have := hc Z hZ c hc2
        linarith

/-- **Covering by shadows.** A set of heights covered by the shadows
`[Im w − (Re w − ½), Im w + (Re w − ½)]` of the zeros `w` of a finite family, each of weight at
least one and real part at least `½`, has measure at most twice the weighted first moment. -/
theorem volume_le_of_subset_shadows {S : Set ℝ} {Z : Finset ℂ} {m : ℂ → ℝ}
    (hS : S ⊆ ⋃ w ∈ Z, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)))
    (hZ : ∀ w ∈ Z, 1 / 2 ≤ w.re ∧ 1 ≤ m w) :
    volume S ≤ ENNReal.ofReal (2 * ∑ w ∈ Z, m w * (w.re - 1 / 2)) := by
  calc volume S ≤ volume (⋃ w ∈ Z, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))) :=
        measure_mono hS
    _ ≤ ∑ w ∈ Z, volume (Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))) :=
        measure_biUnion_finset_le _ _
    _ = ∑ w ∈ Z, ENNReal.ofReal (2 * (w.re - 1 / 2)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Real.volume_Icc]
        congr 1
        ring
    _ = ENNReal.ofReal (∑ w ∈ Z, 2 * (w.re - 1 / 2)) :=
        (ENNReal.ofReal_sum_of_nonneg fun w hw => by linarith [(hZ w hw).1]).symm
    _ ≤ ENNReal.ofReal (2 * ∑ w ∈ Z, m w * (w.re - 1 / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun w hw => ?_
        have h1 := hZ w hw
        nlinarith

/-- **The Hadamard sign at the critical scale.** For all large `U` there is one Littlewood window
on which, for every `c ≥ 2`, the heights `t ∈ [T₁ + 1, T₂ − 1]` where `ξ(σ + it) = 0` or
`Re (ξ'/ξ)(σ + it) < 0` on the line `σ = ½ + c/log U` have measure at most
`2((D/c)(T₂ − T₁) + K log² U)`. -/
theorem exists_volume_hadamardFail_criticalScale_le :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2), ∀ c : ℝ, 2 ≤ c →
        volume {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧
          ¬ (xi (((1 / 2 + c / Real.log U : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 ∧
            0 ≤ (logDeriv xi (((1 / 2 + c / Real.log U : ℝ) : ℂ) + (t : ℂ) * I)).re)}
          ≤ ENNReal.ofReal (2 * (D / c * (T₂ - T₁) + K * Real.log U ^ 2)) := by
  classical
  obtain ⟨D, K, hD, hK, htail⟩ := exists_offLineTailMoment_window_le
  refine ⟨D, K, hD, hK, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (100 : ℝ)] with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun c hc2 => ?_⟩
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  have hL0 : 0 < Real.log U := Real.log_pos (by linarith)
  set σ := 1 / 2 + c / Real.log U with hσdef
  have hσ : 1 / 2 < σ := by
    have : 0 < c / Real.log U := div_pos (by linarith) hL0
    linarith
  set Zc := Z.filter (fun w => σ ≤ w.re)
  have hsub : {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧
      ¬ (xi ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧ 0 ≤ (logDeriv xi ((σ : ℂ) + (t : ℂ) * I)).re)} ⊆
      ⋃ w ∈ Zc, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    intro t ⟨ht, hfail⟩
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    have ht0 : 0 ≤ t := by linarith [ht.1]
    obtain ⟨ρ, hρ, hρs⟩ := DeBruijn.exists_boxZero_of_hadamard_fail (V := t)
      (by rw [hsre]; exact hσ) (by rw [hsim]; exact ht0) (by rw [hsim]) hfail
    rw [mem_boxFinsetLe] at hρ
    obtain ⟨hρ1, hρ2, -, -, hρ0⟩ := hρ
    simp only [DeBruijn.hadamardRect, mem_preimage, Complex.measurableEquivRealProd_apply,
      mem_prod, mem_Ioc, mem_Icc] at hρs
    rw [hsre, hsim] at hρs
    obtain ⟨⟨-, hσρ⟩, hlo, hhi⟩ := hρs
    have hζ : riemannZeta ρ = 0 := by
      have hne : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
      exact (xi_eq_zero_iff (by linarith) hne).mp hρ0
    have hZρ : ρ ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩, hζ⟩
    exact mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hZρ, hσρ⟩, ⟨by linarith, by linarith⟩⟩
  refine (volume_le_of_subset_shadows (m := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ))
    hsub fun w hw => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨hwZ, hwσ⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact ⟨by linarith, by exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0⟩
  · have := hc Z hZ c hc2
    linarith

/-- **Vertical monotonicity at the critical scale.** For all large `U` there is one Littlewood
window on which, for every `c ≥ 2`, the abscissae `x ∈ [T₁ + 1, T₂ − 1]` at which
`y ↦ |Ξ(x + iy)|` fails to be nondecreasing on `y ≥ c/log U` have measure at most
`2((D/c)(T₂ − T₁) + K log² U)`. -/
theorem exists_volume_monotoneFail_criticalScale_le :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2), ∀ c : ℝ, 2 ≤ c →
        volume {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
          ¬ MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖)
            (Ici (c / Real.log U))}
          ≤ ENNReal.ofReal (2 * (D / c * (T₂ - T₁) + K * Real.log U ^ 2)) := by
  classical
  obtain ⟨D, K, hD, hK, htail⟩ := exists_offLineTailMoment_window_le
  refine ⟨D, K, hD, hK, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (100 : ℝ)] with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun c hc2 => ?_⟩
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  have hL0 : 0 < Real.log U := Real.log_pos (by linarith)
  set y₀ := c / Real.log U with hy₀def
  have hy₀ : 0 < y₀ := div_pos (by linarith) hL0
  set Zc := Z.filter (fun w => 1 / 2 + y₀ ≤ w.re)
  have hsub : {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
      ¬ MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici y₀)} ⊆
      ⋃ w ∈ Zc, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    intro x ⟨hx, hfail⟩
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hbad : ∃ ζ, DeBruijn.riemannHeat 0 ζ = 0 ∧ y₀ ^ 2 < ζ.im ^ 2 ∧
        (ζ.re - x) ^ 2 < ζ.im ^ 2 := by
      by_contra hno
      apply hfail
      refine DeBruijn.monotoneOn_norm_xi_vertical_Ici hy₀.le fun ζ hζ => ?_
      by_contra hc'
      rw [not_or, not_le, not_le] at hc'
      exact hno ⟨ζ, hζ, hc'.1, hc'.2⟩
    obtain ⟨ζ, hζ, hy, hlt⟩ := hbad
    obtain ⟨ρ, hρ0, hρ1, hρ2, hρx⟩ := DeBruijn.exists_xiZero_of_obstruct hx0 hζ hy hlt hy₀.le
    have hζρ : riemannZeta ρ = 0 := by
      have hne : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
      exact (xi_eq_zero_iff (by linarith) hne).mp hρ0
    have hρx' := abs_lt.mp hρx
    have hZρ : ρ ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩, hζρ⟩
    exact mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hZρ, hρ1.le⟩, ⟨by linarith, by linarith⟩⟩
  refine (volume_le_of_subset_shadows (m := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ))
    hsub fun w hw => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨hwZ, hwσ⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact ⟨by linarith, by exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0⟩
  · have := hc Z hZ c hc2
    linarith

end

end RHTower
