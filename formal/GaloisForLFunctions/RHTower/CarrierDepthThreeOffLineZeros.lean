import GaloisForLFunctions.RHTower.EulerExponentialCarrierCriticalLine
import GaloisForLFunctions.RHTower.PerturbationZero

/-!
# The depth-three additive carrier has zeros off the critical line at every height

`g₃(s) = D₃(s) + χ(s) D₃(1-s)`, `D₃(s) = 1 + 2^{-s} + 3^{-s}`, satisfies ζ's functional equation
(`gN 3`). It has zeros with `1/2 < Re s < 1` above every height (`exists_offLine_zero_gN_three`).

Mechanism.
* At `σ₀ = 3/5`, `a = 2^{-σ₀}` and `b = 3^{-σ₀}` satisfy `a, b < 1 < a + b`, so there are unit
  complex numbers `W₂ = e^{iφ}`, `W₃` with `1 + a W₂ + b W₃ = 0` (intermediate values of
  `φ ↦ |1 + a e^{iφ}|` on `[0, π]`). The model `M(z) = 1 + 2^{-z} W₂ + 3^{-z} W₃` vanishes at `σ₀`,
  is not identically zero, and so is bounded below by some `m > 0` on a small circle around `σ₀`.
* `log 3 / log 2` is irrational. Along heights `τₖ = (2πk - φ)/log 2` one has `2^{-iτₖ} = W₂`
  exactly, and Dirichlet approximation makes `3^{-iτₖ}` as close to `W₃` as needed with `k`
  arbitrarily large.
* In the right half-strip `|χ(s)| ≤ ((t/2π)/e)^{-(σ-1/2)}` (`norm_zetaChi_le_right_line_exp`) and
  `|D₃(1-s)| ≤ 3`, so the reflected term is small at large height.
* Hence `g₃(z + iτₖ) - M(z)` is below `m/3` on the circle, and sphere domination
  (`exists_zero_of_sphere_domination`) places a zero of `g₃` near `σ₀ + iτₖ`.

The carrier `1 + 2^{-s}` is critical-line rigid at large height (`CarrierDepthTwoRigidity`), and
symmetrized Euler exponentials are rigid at every depth above an explicit height
(`EulerExponentialCarrierCriticalLine`). Depth three is the first additive depth where rigidity
fails: the additive truncation has zeros of its own in the right half-strip, which an Euler
exponential never has.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

namespace CarrierDepthThree

/-- The depth-three Dirichlet polynomial. -/
theorem dirichletPoly_three (s : ℂ) :
    dirichletPoly 3 s = 1 + (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s) := by
  unfold dirichletPoly
  rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
  simp [Finset.sum_insert, Complex.one_cpow]
  ring

theorem norm_two_cpow_neg_le {z : ℂ} (hz : 0 ≤ z.re) : ‖(2 : ℂ) ^ (-z)‖ ≤ 1 := by
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.norm_natCast_cpow_of_pos (by norm_num)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp; linarith)

theorem norm_three_cpow_neg_le {z : ℂ} (hz : 0 ≤ z.re) : ‖(3 : ℂ) ^ (-z)‖ ≤ 1 := by
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.norm_natCast_cpow_of_pos (by norm_num)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp; linarith)

/-- The reflected Dirichlet part is at most `3` in modulus when `Re s ≤ 1`. -/
theorem norm_dirichletPoly_three_one_sub_le {s : ℂ} (h1 : s.re ≤ 1) :
    ‖dirichletPoly 3 (1 - s)‖ ≤ 3 := by
  rw [dirichletPoly_three]
  have hre : 0 ≤ (1 - s).re := by simp; linarith
  calc ‖1 + (2 : ℂ) ^ (-(1 - s)) + (3 : ℂ) ^ (-(1 - s))‖
      ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (-(1 - s))‖ + ‖(3 : ℂ) ^ (-(1 - s))‖ := norm_add₃_le
    _ ≤ 1 + 1 + 1 := by
        gcongr
        · simp
        · exact norm_two_cpow_neg_le hre
        · exact norm_three_cpow_neg_le hre
    _ = 3 := by norm_num

/-! ## The torus triangle -/

/-- Three lengths `1, a, b` with `a, b < 1 < a + b` close up into a triangle of unit directions. -/
theorem exists_unit_triangle {a b : ℝ} (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hab : 1 < a + b) :
    ∃ φ : ℝ, ∃ W₃ : ℂ, ‖W₃‖ = 1 ∧
      1 + (a : ℂ) * Complex.exp ((φ : ℂ) * I) + (b : ℂ) * W₃ = 0 := by
  set f : ℝ → ℝ := fun φ => ‖(1 : ℂ) + (a : ℂ) * Complex.exp ((φ : ℂ) * I)‖ with hf
  have hcont : ContinuousOn f (Icc 0 Real.pi) := by
    apply Continuous.continuousOn
    fun_prop
  have hf0 : f 0 = 1 + a := by
    simp only [hf, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [show (1 : ℂ) + (a : ℂ) = ((1 + a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hfπ : f Real.pi = 1 - a := by
    simp only [hf, Complex.exp_pi_mul_I, mul_neg, mul_one]
    rw [show (1 : ℂ) + -(a : ℂ) = ((1 - a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hb : b ∈ Icc (f Real.pi) (f 0) := by
    rw [hf0, hfπ]
    constructor <;> linarith
  obtain ⟨φ, -, hφ⟩ := intermediate_value_Icc' Real.pi_pos.le hcont hb
  refine ⟨φ, -((1 : ℂ) + (a : ℂ) * Complex.exp ((φ : ℂ) * I)) / (b : ℂ), ?_, ?_⟩
  · rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
    change f φ / b = 1
    rw [hφ, div_self hb0.ne']
  · have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
    field_simp
    ring

/-! ## Irrational rotation -/

/-- `log 3 / log 2` is irrational. -/
theorem irrational_log_three_div_log_two : Irrational (Real.log 3 / Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [irrational_iff_ne_rational]
  intro p q hq heq
  have hpos : 0 < Real.log 3 / Real.log 2 := div_pos (Real.log_pos (by norm_num)) h2
  -- `q log 3 = p log 2` forces `3^|q| = 2^|p|`
  have hkey : (q : ℝ) * Real.log 3 = (p : ℝ) * Real.log 2 := by
    have := heq
    field_simp at this
    linarith
  rcases lt_trichotomy q 0 with hq' | hq' | hq'
  · -- replace by the negatives
    have hp' : p < 0 := by
      have : (p : ℝ) / q > 0 := heq ▸ hpos
      rcases lt_trichotomy p 0 with h | h | h
      · exact h
      · simp [h] at this
      · exfalso
        have : (p : ℝ) / q < 0 := div_neg_of_pos_of_neg (by exact_mod_cast h) (by exact_mod_cast hq')
        linarith
    have hkey' : ((-q : ℤ) : ℝ) * Real.log 3 = ((-p : ℤ) : ℝ) * Real.log 2 := by
      push_cast; linarith
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (-q : ℤ) = m := ⟨(-q).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (-p : ℤ) = n := ⟨(-p).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hm, hn] at hkey'
    push_cast at hkey'
    have hpow : ((3 : ℝ) ^ m) = (2 : ℝ) ^ n := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 3 ^ m),
        ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ n), Real.log_pow, Real.log_pow, hkey']
    have hnat : (3 : ℕ) ^ m = 2 ^ n := by exact_mod_cast hpow
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hodd : Odd ((3 : ℕ) ^ m) := Odd.pow (by decide)
    have heven : Even ((2 : ℕ) ^ n) := (Nat.even_pow.mpr ⟨even_two, hn0⟩)
    rw [hnat] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  · exact hq hq'
  · have hp' : 0 < p := by
      have : (p : ℝ) / q > 0 := heq ▸ hpos
      rcases lt_trichotomy p 0 with h | h | h
      · exfalso
        have : (p : ℝ) / q < 0 := div_neg_of_neg_of_pos (by exact_mod_cast h) (by exact_mod_cast hq')
        linarith
      · simp [h] at this
      · exact h
    obtain ⟨m, hm⟩ : ∃ m : ℕ, q = m := ⟨q.toNat, (Int.toNat_of_nonneg hq'.le).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, (Int.toNat_of_nonneg hp'.le).symm⟩
    rw [hm, hn] at hkey
    push_cast at hkey
    have hpow : ((3 : ℝ) ^ m) = (2 : ℝ) ^ n := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 3 ^ m),
        ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ n), Real.log_pow, Real.log_pow, hkey]
    have hnat : (3 : ℕ) ^ m = 2 ^ n := by exact_mod_cast hpow
    have hn0 : n ≠ 0 := by omega
    have hodd : Odd ((3 : ℕ) ^ m) := Odd.pow (by decide)
    have heven : Even ((2 : ℕ) ^ n) := (Nat.even_pow.mpr ⟨even_two, hn0⟩)
    rw [hnat] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- Forward orbits of an irrational rotation are dense: every residue is approximated by `k α`
with `k` as large as required. -/
theorem exists_nat_mul_near {α : ℝ} (hα : Irrational α) (y : ℝ) {ε : ℝ} (hε : 0 < ε)
    (M₀ : ℕ) : ∃ k : ℕ, M₀ ≤ k ∧ ∃ J : ℤ, |(k : ℝ) * α - y - J| < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  obtain ⟨j, k₀, hk₀, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α hn0
  set δ := (k₀ : ℝ) * α - j with hδ
  have hδε : |δ| < ε := by
    refine lt_of_le_of_lt hjk ?_
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hε).mp hn
    linarith
  have hδ0 : δ ≠ 0 := by
    intro h0
    have : α = (j : ℝ) / k₀ := by
      have hk : (k₀ : ℝ) ≠ 0 := by exact_mod_cast hk₀.ne'
      field_simp
      linarith
    exact hα ⟨(j : ℚ) / k₀, by push_cast [this]; ring⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (K : ℤ) = k₀ := ⟨k₀.toNat, Int.toNat_of_nonneg hk₀.le⟩
  have hKpos : 0 < K := by omega
  -- find `m ≥ M₀` with `m δ ≡ y` up to `|δ|`
  obtain ⟨m, hm, N₀, hmN⟩ : ∃ m : ℕ, M₀ ≤ m ∧ ∃ N₀ : ℤ, |(m : ℝ) * δ - y - N₀| < ε := by
    rcases lt_or_gt_of_ne hδ0 with hneg | hpos
    · set N₀ : ℤ := ⌈y - (M₀ : ℝ) * δ⌉ + 1 with hN₀
      have hN₀y : y - N₀ < (M₀ : ℝ) * δ := by
        have := Int.le_ceil (y - (M₀ : ℝ) * δ)
        rw [hN₀]; push_cast; linarith
      set x := (y - N₀) / δ with hx
      have hxM : (M₀ : ℝ) < x := by
        rw [hx, lt_div_iff_of_neg hneg]
        linarith
      refine ⟨⌈x⌉₊, ?_, -N₀, ?_⟩
      · exact_mod_cast (lt_of_lt_of_le hxM (Nat.le_ceil x)).le
      · have h1 := Nat.le_ceil x
        have h2 := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x)
        have e1 : (⌈x⌉₊ : ℝ) * δ ≤ y - N₀ := by
          have := mul_le_mul_of_nonpos_right h1 hneg.le
          rwa [hx, div_mul_cancel₀ _ hneg.ne] at this
        have e2 : y - N₀ < (⌈x⌉₊ : ℝ) * δ - δ := by
          have := mul_lt_mul_of_neg_right h2 hneg
          rw [add_mul, one_mul, hx, div_mul_cancel₀ _ hneg.ne] at this
          linarith
        rw [abs_lt]
        push_cast
        have := abs_of_neg hneg
        constructor <;> linarith
    · set N₀ : ℤ := ⌈(M₀ : ℝ) * δ - y⌉ + 1 with hN₀
      have hN₀y : (M₀ : ℝ) * δ < y + N₀ := by
        have := Int.le_ceil ((M₀ : ℝ) * δ - y)
        rw [hN₀]; push_cast; linarith
      set x := (y + N₀) / δ with hx
      have hxM : (M₀ : ℝ) < x := by
        rw [hx, lt_div_iff₀ hpos]
        linarith
      refine ⟨⌈x⌉₊, ?_, N₀, ?_⟩
      · exact_mod_cast (lt_of_lt_of_le hxM (Nat.le_ceil x)).le
      · have h1 := Nat.le_ceil x
        have h2 := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x)
        have e1 : y + N₀ ≤ (⌈x⌉₊ : ℝ) * δ := by
          have := mul_le_mul_of_nonneg_right h1 hpos.le
          rwa [hx, div_mul_cancel₀ _ hpos.ne'] at this
        have e2 : (⌈x⌉₊ : ℝ) * δ < y + N₀ + δ := by
          have := mul_lt_mul_of_pos_right h2 hpos
          rw [add_mul, one_mul, hx, div_mul_cancel₀ _ hpos.ne'] at this
          exact this
        rw [abs_lt]
        have := abs_of_pos hpos
        constructor <;> linarith
  refine ⟨m * K, le_trans hm (Nat.le_mul_of_pos_right m hKpos), (m : ℤ) * j + N₀, ?_⟩
  have hkα : ((m * K : ℕ) : ℝ) * α = (m : ℝ) * j + (m : ℝ) * δ := by
    rw [hδ]
    have hKR : (K : ℝ) = k₀ := by exact_mod_cast hK
    push_cast
    rw [hKR]
    ring
  rw [hkα]
  push_cast
  convert hmN using 2
  ring

/-! ## The model and its isolated zero -/

/-- The torus model `M(z) = 1 + 2^{-z} W₂ + 3^{-z} W₃`. -/
def model (W₂ W₃ : ℂ) (z : ℂ) : ℂ := 1 + (2 : ℂ) ^ (-z) * W₂ + (3 : ℂ) ^ (-z) * W₃

theorem differentiable_model (W₂ W₃ : ℂ) : Differentiable ℂ (model W₂ W₃) := by
  intro z
  unfold model
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (-z)) z :=
    (differentiableAt_id.neg).const_cpow (Or.inl two_ne_zero)
  have h3 : DifferentiableAt ℂ (fun z : ℂ => (3 : ℂ) ^ (-z)) z :=
    (differentiableAt_id.neg).const_cpow (Or.inl three_ne_zero)
  fun_prop

theorem model_two_ne_zero {W₂ W₃ : ℂ} (h₂ : ‖W₂‖ = 1) (h₃ : ‖W₃‖ = 1) :
    model W₂ W₃ 2 ≠ 0 := by
  intro h
  unfold model at h
  have e2 : (2 : ℂ) ^ (-(2 : ℂ)) = 1 / 4 := by
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    norm_num
  have e3 : (3 : ℂ) ^ (-(2 : ℂ)) = 1 / 9 := by
    rw [Complex.cpow_neg, show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num,
      show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    norm_num
  rw [e2, e3] at h
  have hsum : (1 / 4 : ℂ) * W₂ + (1 / 9 : ℂ) * W₃ = -1 := by linear_combination h
  have hn := norm_add_le ((1 / 4 : ℂ) * W₂) ((1 / 9 : ℂ) * W₃)
  rw [hsum, norm_neg, norm_one, norm_mul, norm_mul, h₂, h₃] at hn
  norm_num at hn

/-- A circle around a zero of the model on which the model stays away from zero. -/
theorem exists_sphere_model_floor {W₂ W₃ : ℂ} (h₂ : ‖W₂‖ = 1) (h₃ : ‖W₃‖ = 1) (z₀ : ℂ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 20 ∧ ∃ m : ℝ, 0 < m ∧
      ∀ z ∈ sphere z₀ r, m ≤ ‖model W₂ W₃ z‖ := by
  have han : AnalyticOnNhd ℂ (model W₂ W₃) univ :=
    (differentiable_model W₂ W₃).differentiableOn.analyticOnNhd isOpen_univ
  rcases (han z₀ (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hEq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ z₀) hzero
    exact model_two_ne_zero h₂ h₃ (hEq (mem_univ 2))
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
    obtain ⟨ε, hε, hball⟩ := hne
    set r := min (ε / 2) (1 / 20) with hr
    have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
    have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsne : (sphere z₀ r).Nonempty := (NormedSpace.sphere_nonempty (x := z₀)).mpr hr0.le
    obtain ⟨zm, hzm, hmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn hsne
      (((differentiable_model W₂ W₃).continuous.norm).continuousOn)
    have hzm_ne : model W₂ W₃ zm ≠ 0 := by
      apply hball
      · rw [mem_sphere] at hzm; rw [hzm]; exact hrε
      · intro h
        rw [mem_sphere, h, dist_self] at hzm
        exact hr0.ne' hzm.symm
    refine ⟨r, hr0, min_le_right _ _, ‖model W₂ W₃ zm‖, norm_pos_iff.mpr hzm_ne, ?_⟩
    intro z hz
    exact hmin hz

/-! ## Numerical side conditions at `σ₀ = 3/5` -/

theorem rpow_neg_three_fifths_pow_five {x : ℝ} (hx : 0 < x) :
    (x ^ (-(3 / 5 : ℝ))) ^ 5 = (x ^ 3)⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le,
    show -(3 / 5 : ℝ) * ((5 : ℕ) : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast,
    zpow_neg, zpow_ofNat]

theorem three_fifths_side_conditions :
    0 < (2 : ℝ) ^ (-(3 / 5 : ℝ)) ∧ (2 : ℝ) ^ (-(3 / 5 : ℝ)) < 1 ∧
      0 < (3 : ℝ) ^ (-(3 / 5 : ℝ)) ∧ (3 : ℝ) ^ (-(3 / 5 : ℝ)) < 1 ∧
      1 < (2 : ℝ) ^ (-(3 / 5 : ℝ)) + (3 : ℝ) ^ (-(3 / 5 : ℝ)) := by
  set a := (2 : ℝ) ^ (-(3 / 5 : ℝ)) with ha
  set b := (3 : ℝ) ^ (-(3 / 5 : ℝ)) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hb0 : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have ha5 : a ^ 5 = 1 / 8 := by rw [ha, rpow_neg_three_fifths_pow_five (by norm_num)]; norm_num
  have hb5 : b ^ 5 = 1 / 27 := by rw [hb, rpow_neg_three_fifths_pow_five (by norm_num)]; norm_num
  have ha' : 13 / 20 < a := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ ha0.le h 5
    rw [ha5] at this
    norm_num at this
  have hb' : 1 / 2 < b := by
    by_contra h
    push Not at h
    have := pow_le_pow_left₀ hb0.le h 5
    rw [hb5] at this
    norm_num at this
  exact ⟨ha0, ha1, hb0, hb1, by linarith⟩

theorem natCast_cpow_ofReal_neg (n : ℕ) (x : ℝ) :
    (n : ℂ) ^ (-(x : ℂ)) = (((n : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg]

/-- `n^{-iτ}` is `exp(-i τ log n)`. -/
theorem natCast_cpow_neg_I_mul {n : ℕ} (hn : 0 < n) (τ : ℝ) :
    (n : ℂ) ^ (-((τ : ℂ) * I)) = Complex.exp (((-(Real.log n * τ) : ℝ) : ℂ) * I) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 1
  push_cast
  ring

/-- Distance between unit exponentials is at most the distance of the angles. -/
theorem norm_exp_mul_I_sub_exp_mul_I_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * I) - Complex.exp ((y : ℂ) * I)‖ ≤ |x - y| := by
  have hsplit : Complex.exp ((x : ℂ) * I) - Complex.exp ((y : ℂ) * I) =
      Complex.exp ((y : ℂ) * I) * (Complex.exp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-! ## The off-line zeros -/

/-- **Depth three breaks critical-line rigidity.** The carrier
`1 + 2^{-s} + 3^{-s} + χ(s)(1 + 2^{s-1} + 3^{s-1})` has a zero with `1/2 < Re s < 1` above every
height. -/
theorem exists_offLine_zero_gN_three (T : ℝ) :
    ∃ s : ℂ, gN 3 s = 0 ∧ 1 / 2 < s.re ∧ s.re < 1 ∧ T ≤ s.im := by
  obtain ⟨ha0, ha1, hb0, hb1, hab⟩ := three_fifths_side_conditions
  set a := (2 : ℝ) ^ (-(3 / 5 : ℝ)) with ha
  set b := (3 : ℝ) ^ (-(3 / 5 : ℝ)) with hb
  obtain ⟨φ, W₃, hW₃, htri⟩ := exists_unit_triangle ha1 hb0 hb1 hab
  set W₂ : ℂ := Complex.exp ((φ : ℂ) * I) with hW₂def
  have hW₂ : ‖W₂‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
  set σ₀ : ℂ := ((3 / 5 : ℝ) : ℂ) with hσ₀
  have hM0 : model W₂ W₃ σ₀ = 0 := by
    unfold model
    have e2 : (2 : ℂ) ^ (-σ₀) = (a : ℂ) := by
      rw [hσ₀, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, natCast_cpow_ofReal_neg]
      push_cast
      rfl
    have e3 : (3 : ℂ) ^ (-σ₀) = (b : ℂ) := by
      rw [hσ₀, show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, natCast_cpow_ofReal_neg]
      push_cast
      rfl
    rw [e2, e3]
    linear_combination htri
  obtain ⟨r, hr0, hr20, m, hm0, hmM⟩ := exists_sphere_model_floor hW₂ hW₃ σ₀
  -- the height threshold
  set L : ℝ := 1 + 20 * |Real.log (18 / m)| with hL
  set τmin : ℝ := max (T + 1) (max 9 (2 * Real.pi * Real.exp L + 1)) with hτmin
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set α : ℝ := Real.log 3 / Real.log 2 with hα
  set y : ℝ := (φ * α - Complex.arg W₃) / (2 * Real.pi) with hy
  set M₀ : ℕ := ⌈(τmin * Real.log 2 + |φ|) / (2 * Real.pi)⌉₊ with hM₀
  have hε : 0 < m / (12 * Real.pi) := by positivity
  obtain ⟨k, hk, J, hkJ⟩ :=
    exists_nat_mul_near irrational_log_three_div_log_two y hε M₀
  set τ : ℝ := (2 * Real.pi * k - φ) / Real.log 2 with hτ
  have hτge : τmin ≤ τ := by
    rw [hτ, le_div_iff₀ hlog2]
    have h1 := (Nat.le_ceil ((τmin * Real.log 2 + |φ|) / (2 * Real.pi))).trans
      (Nat.cast_le.mpr hk)
    rw [div_le_iff₀ (by positivity)] at h1
    have := le_abs_self φ
    linarith
  have hτT : T + 1 ≤ τ := le_trans (le_max_left _ _) hτge
  have hτ9 : 9 ≤ τ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hτge
  have hτL : 2 * Real.pi * Real.exp L + 1 ≤ τ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hτge
  -- the two prime phases at height τ
  have h2τ : (2 : ℂ) ^ (-((τ : ℂ) * I)) = W₂ := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, natCast_cpow_neg_I_mul (by norm_num)]
    have hlt : Real.log ((2 : ℕ) : ℝ) * τ = 2 * Real.pi * k - φ := by
      rw [hτ]; push_cast; field_simp
    rw [hlt, hW₂def]
    have hk2 : (((-(2 * Real.pi * k - φ)) : ℝ) : ℂ) * I =
        (φ : ℂ) * I + ((-(k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast; ring
    rw [hk2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h3τ : ‖(3 : ℂ) ^ (-((τ : ℂ) * I)) - W₃‖ ≤ m / 6 := by
    rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, natCast_cpow_neg_I_mul (by norm_num)]
    have hW₃e : W₃ = Complex.exp ((Complex.arg W₃ : ℂ) * I) := by
      have := Complex.norm_mul_exp_arg_mul_I W₃
      rw [hW₃, Complex.ofReal_one, one_mul] at this
      exact this.symm
    have hshift : Complex.exp ((Complex.arg W₃ : ℂ) * I) =
        Complex.exp (((Complex.arg W₃ - 2 * Real.pi * J : ℝ) : ℂ) * I) := by
      have : (((Complex.arg W₃ - 2 * Real.pi * J : ℝ) : ℂ) * I) =
          (Complex.arg W₃ : ℂ) * I + ((-J : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hW₃e, hshift]
    refine (norm_exp_mul_I_sub_exp_mul_I_le _ _).trans ?_
    have hangle : -(Real.log ((3 : ℕ) : ℝ) * τ) - (Complex.arg W₃ - 2 * Real.pi * J) =
        -(2 * Real.pi) * ((k : ℝ) * α - y - J) := by
      rw [hτ, hy, hα]
      push_cast
      field_simp
      ring
    rw [hangle, abs_mul, abs_neg, abs_of_pos (by positivity)]
    calc 2 * Real.pi * |(k : ℝ) * α - y - J| ≤ 2 * Real.pi * (m / (12 * Real.pi)) := by
          gcongr
      _ = m / 6 := by field_simp; ring
  -- the perturbation
  set pert : ℂ → ℂ := fun z => gN 3 (z + (τ : ℂ) * I) - model W₂ W₃ z with hpert
  have hre_ball : ∀ z ∈ closedBall σ₀ r, 11 / 20 ≤ z.re ∧ z.re ≤ 13 / 20 ∧ |z.im| ≤ 1 / 20 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - σ₀)
    have h2 := Complex.abs_im_le_norm (z - σ₀)
    simp only [hσ₀, Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at h1 h2
    refine ⟨?_, ?_, ?_⟩
    · have := (abs_le.mp (h1.trans (hz.trans hr20))).1; linarith
    · have := (abs_le.mp (h1.trans (hz.trans hr20))).2; linarith
    · exact h2.trans (hz.trans hr20)
  have hchi : ∀ z ∈ closedBall σ₀ r, ‖zetaChi (z + (τ : ℂ) * I)‖ ≤ m / 18 := by
    intro z hz
    obtain ⟨hre1, hre2, him⟩ := hre_ball z hz
    set t : ℝ := z.im + τ with ht
    have ht8 : 8 ≤ t := by have := (abs_le.mp him).1; linarith
    have ht0 : 0 < t := by linarith
    have hzt : z + (τ : ℂ) * I = (z.re : ℂ) + (t : ℂ) * I := by
      rw [ht]; push_cast
      conv_lhs => rw [← Complex.re_add_im z]
      ring
    rw [hzt]
    refine (norm_zetaChi_le_right_line_exp (by linarith) (by linarith) ht0).trans ?_
    have hE := EulerExponentialCarrier.chi_correction_lt_one ht8
    have htL : L ≤ Real.log (t / (2 * Real.pi)) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
      have := (abs_le.mp him).1
      nlinarith
    have hlog : Real.log Real.pi - Real.log (t / 2) = -Real.log (t / (2 * Real.pi)) := by
      rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
        Real.log_div (by positivity) Real.pi_ne_zero]
      ring
    have hL1 : 1 ≤ L := by rw [hL]; have := abs_nonneg (Real.log (18 / m)); linarith
    have hexp : (z.re - 1 / 2) * (Real.log Real.pi - Real.log (t / 2) +
        (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2)))) ≤ -|Real.log (18 / m)| := by
      rw [hlog]
      have hneg : -Real.log (t / (2 * Real.pi)) + (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2)))
          ≤ 1 - L := by linarith
      have hneg' : 1 - L ≤ 0 := by linarith
      calc (z.re - 1 / 2) * (-Real.log (t / (2 * Real.pi)) +
            (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))))
          ≤ (1 / 20) * (1 - L) := by
            have h20 : 1 / 20 ≤ z.re - 1 / 2 := by linarith
            nlinarith
        _ = -|Real.log (18 / m)| := by rw [hL]; ring
    calc Real.exp ((z.re - 1 / 2) * (Real.log Real.pi - Real.log (t / 2) +
          (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2)))))
        ≤ Real.exp (-|Real.log (18 / m)|) := Real.exp_le_exp.mpr hexp
      _ ≤ Real.exp (-Real.log (18 / m)) := Real.exp_le_exp.mpr (by
          have := le_abs_self (Real.log (18 / m)); linarith)
      _ = m / 18 := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hpert_le : ∀ z ∈ closedBall σ₀ r, ‖pert z‖ ≤ m / 3 := by
    intro z hz
    obtain ⟨hre1, hre2, him⟩ := hre_ball z hz
    have hzre : 0 ≤ z.re := by linarith
    have hsplit : pert z = (2 : ℂ) ^ (-z) * ((2 : ℂ) ^ (-((τ : ℂ) * I)) - W₂) +
        (3 : ℂ) ^ (-z) * ((3 : ℂ) ^ (-((τ : ℂ) * I)) - W₃) +
        zetaChi (z + (τ : ℂ) * I) * dirichletPoly 3 (1 - (z + (τ : ℂ) * I)) := by
      simp only [hpert, gN, chiSymmetrize, dirichletPoly_three, model]
      rw [show -(z + (τ : ℂ) * I) = -z + -((τ : ℂ) * I) by ring,
        Complex.cpow_add _ _ two_ne_zero, Complex.cpow_add _ _ three_ne_zero]
      ring
    rw [hsplit, h2τ, sub_self, mul_zero, zero_add]
    have hre1' : (1 - (z + (τ : ℂ) * I)).re ≤ 1 := by simp; linarith
    have hD := norm_dirichletPoly_three_one_sub_le (s := z + (τ : ℂ) * I) (by simp; linarith)
    calc ‖(3 : ℂ) ^ (-z) * ((3 : ℂ) ^ (-((τ : ℂ) * I)) - W₃) +
          zetaChi (z + (τ : ℂ) * I) * dirichletPoly 3 (1 - (z + (τ : ℂ) * I))‖
        ≤ ‖(3 : ℂ) ^ (-z)‖ * ‖(3 : ℂ) ^ (-((τ : ℂ) * I)) - W₃‖ +
            ‖zetaChi (z + (τ : ℂ) * I)‖ * ‖dirichletPoly 3 (1 - (z + (τ : ℂ) * I))‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
      _ ≤ 1 * (m / 6) + (m / 18) * 3 := by
          gcongr
          · exact norm_three_cpow_neg_le hzre
          · exact hchi z hz
      _ = m / 3 := by ring
  -- analyticity of the carrier on the closed ball
  have hgN_diff : DifferentiableOn ℂ (fun z => gN 3 (z + (τ : ℂ) * I)) (closedBall σ₀ r) := by
    intro z hz
    obtain ⟨hre1, hre2, -⟩ := hre_ball z hz
    have hG : Complex.Gammaℝ (1 - (z + (τ : ℂ) * I)) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    exact ((gN_analyticAt hG).differentiableAt.comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hpert_diff : DiffContOnCl ℂ pert (ball σ₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball σ₀ hr0.ne']
    exact hgN_diff.sub (differentiable_model W₂ W₃).differentiableOn
  have hmodel_diff : DiffContOnCl ℂ (model W₂ W₃) (ball σ₀ r) :=
    (differentiable_model W₂ W₃).diffContOnCl
  -- plant the zero
  obtain ⟨z, hz, hzero⟩ : ∃ z ∈ closedBall σ₀ r, gN 3 (z + (τ : ℂ) * I) = 0 := by
    by_cases hc : pert σ₀ = 0
    · refine ⟨σ₀, mem_closedBall_self hr0.le, ?_⟩
      have : gN 3 (σ₀ + (τ : ℂ) * I) = pert σ₀ + model W₂ W₃ σ₀ := by
        simp only [hpert]; ring
      rw [this, hc, hM0, add_zero]
    · obtain ⟨z, hz, hsum⟩ := exists_zero_of_sphere_domination hr0 hpert_diff hmodel_diff
        hM0 hc (fun z hz => by
          have h1 := hpert_le z (sphere_subset_closedBall hz)
          have h2 := hmM z hz
          linarith)
      refine ⟨z, hz, ?_⟩
      have : gN 3 (z + (τ : ℂ) * I) = pert z + model W₂ W₃ z := by
        simp only [hpert]; ring
      rw [this, hsum]
  obtain ⟨hre1, hre2, him⟩ := hre_ball z hz
  refine ⟨z + (τ : ℂ) * I, hzero, ?_, ?_, ?_⟩
  · simp; linarith
  · simp; linarith
  · simp
    have := (abs_le.mp him).1
    linarith

/-- The depth-three carrier is not critical-line rigid at large height: no height threshold
confines its strip zeros to the critical line. -/
theorem not_eventually_critical_gN_three :
    ¬ ∃ T : ℝ, ∀ s : ℂ, 0 < s.re → s.re < 1 → T ≤ s.im → gN 3 s = 0 → s.re = 1 / 2 := by
  rintro ⟨T, hT⟩
  obtain ⟨s, hs, h1, h2, h3⟩ := exists_offLine_zero_gN_three T
  have := hT s (by linarith) h2 h3 hs
  linarith

end CarrierDepthThree

end

end RHTower
