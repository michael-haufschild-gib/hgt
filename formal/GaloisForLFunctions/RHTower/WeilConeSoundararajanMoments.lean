import GaloisForLFunctions.RHTower.WeilConeSoundararajanLargeValues

/-!
# Moments on the Weil cone

Let `lam` be full-cone Weil-positive with `|lam(n)| ≤ κ log n` and summable rest weight
`A_c = Σ_{n ∉ {p, p²}} |lam(n)|/(√n log n)`.  Write `log F_lam(σ + it)` for `producerLogZeta`, the
logarithm continued from `Re s = 2` along horizontal lines.

**Theorem** (`exists_setIntegral_exp_mul_le`).  For every `k > 0` and `0 < ε ≤ 1/8` there are
`C` and `T₀` with

`∫_T^{2T} exp(2k Re log F_lam(½ + 1/log T + it)) dt ≤ C T (log T)^{k² e^ε κ²/(1−4ε)² + ε}`
for `T ≥ T₀`.

For `ζ` under RH this is Soundararajan's moment bound just right of the line.  On this part of the
Weil cone it holds unconditionally, with Weil positivity in place of RH.  The case `k = 1` is
`exists_setIntegral_exp_two_mul_le`.

**Proof.**
* Layer cake over integer levels (`setIntegral_exp_mul_le_sum`).  Littlewood's bound on the
  cone caps the levels at `C log T/log log T`.
* At level `V`, the split Soundararajan inequality with `L = log T/(εV)` reduces `log|F| ≥ V` to
  three prime-polynomial events (`measureReal_level_le`).  The prime part below `z = e^{L/ℓ}`,
  `ℓ = log log T`, has variance `≤ κ²(ℓ + B)` and moments up to `εVℓ/4`; this gives the Gaussian
  tail `e^{−e^{−ε}(1−4ε)²V²/(κ²(ℓ+B)+1)}`.  The other two events have variance `O(log ℓ)` and
  `O(1)` and moments up to `εV/4`, so their tails are `≪ e^{−(2k+1)V}` above a level of order
  `log ℓ` (`measureReal_level_le_explicit`).
* Summing `e^{2kV}` against these tails gives `O(ℓ) (log T)^{k² e^ε κ²/(1−4ε)²}`.  The levels
  below the threshold contribute `T e^{O(log ℓ)}`.  Both extra factors are `≤ (log T)^ε` for
  large `T`.
-/

open Complex Set Filter MeasureTheory Topology

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz WeilConeMoments

/-! ### Continuity in the height -/

theorem continuous_LSeries_lamLogC_two {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Continuous fun t : ℝ => LSeries (lamLogC lam) ((2 : ℂ) + t * I) := by
  have hd := LSeries_differentiableOn (lamLogC lam)
  have hab := abscissaOfAbsConv_lamLogC_le hW
  refine (hd.continuousOn.comp_continuous (by fun_prop) fun t => ?_)
  show LSeries.abscissaOfAbsConv (lamLogC lam) < ((2 : ℂ) + t * I).re
  simp only [Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
  calc LSeries.abscissaOfAbsConv (lamLogC lam) ≤ 1 := hab
    _ < 2 := by exact_mod_cast (by norm_num : (1 : ℝ) < 2)

/-- `t ↦ log F_lam(σ + it)` is continuous on `t > 0`. -/
theorem continuousOn_producerLogZeta {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ2 : σ ≤ 2) :
    ContinuousOn (fun t => producerLogZeta hW σ t) (Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  unfold producerLogZeta
  refine ((continuous_LSeries_lamLogC_two hW).comp continuous_subtype_val).add ?_
  set f : Ioi (0 : ℝ) → ℝ → ℂ := fun t u =>
    producerA hW (((max σ (min u 2) : ℝ) : ℂ) + (t : ℝ) * I) with hf
  have hfc : Continuous f.uncurry := by
    have hmap : Continuous fun p : Ioi (0 : ℝ) × ℝ =>
        (((max σ (min p.2 2) : ℝ) : ℂ) + ((p.1 : ℝ) : ℂ) * I) := by fun_prop
    refine (continuousOn_producerA hW).comp_continuous hmap fun p => ?_
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      exact lt_of_lt_of_le hσ (le_max_left _ _)
    · intro h
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at this
      have hp : (0 : ℝ) < p.1 := p.1.2
      linarith
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hfc σ 2
  refine hcont.congr fun t => ?_
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hσ2] at hu
  simp only [hf]
  rw [min_eq_left hu.2, max_eq_right hu.1]

/-! ### The layer cake over integer levels -/

/-- Pointwise: `e^{cx} ≤ e^{cJ₀} + Σ_{J₀ ≤ j ≤ J₁} e^{cj+c} 1_{x ≥ j}` when `x ≤ J₁`, `c ≥ 0`. -/
theorem exp_mul_le_sum {c x : ℝ} (hc : 0 ≤ c) {J₀ J₁ : ℕ} (hx : x ≤ J₁) :
    Real.exp (c * x) ≤ Real.exp (c * J₀) + ∑ j ∈ Finset.Icc J₀ J₁,
      Real.exp (c * j + c) * (if (j : ℝ) ≤ x then 1 else 0) := by
  have hsum0 : 0 ≤ ∑ j ∈ Finset.Icc J₀ J₁,
      Real.exp (c * j + c) * (if (j : ℝ) ≤ x then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Real.exp_pos _).le (by split_ifs <;> norm_num)
  by_cases hx0 : x < J₀
  · have : Real.exp (c * x) ≤ Real.exp (c * J₀) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx0.le hc)
    linarith
  push Not at hx0
  have hxnn : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx0
  set j : ℕ := ⌊x⌋₊ with hj
  have hj0 : J₀ ≤ j := Nat.le_floor hx0
  have hj1 : j ≤ J₁ := by
    have := Nat.floor_le_floor (show x ≤ (J₁ : ℝ) from hx)
    rwa [Nat.floor_natCast] at this
  have hjx : (j : ℝ) ≤ x := Nat.floor_le hxnn
  have hxj : x < j + 1 := Nat.lt_floor_add_one x
  have hmem : j ∈ Finset.Icc J₀ J₁ := Finset.mem_Icc.mpr ⟨hj0, hj1⟩
  have hterm : Real.exp (c * x) ≤ Real.exp (c * j + c) * (if (j : ℝ) ≤ x then 1 else 0) := by
    rw [if_pos hjx, mul_one]
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hxj.le hc
    linarith
  have hle := Finset.single_le_sum (f := fun j : ℕ =>
    Real.exp (c * j + c) * (if (j : ℝ) ≤ x then (1 : ℝ) else 0))
    (fun j _ => mul_nonneg (Real.exp_pos _).le (by split_ifs <;> norm_num)) hmem
  have := Real.exp_pos (c * J₀)
  linarith

/-- **Layer cake.**  For `f` a.e.-measurable on `(a, b]` with `f ≤ J₁` there and `c ≥ 0`,
`∫_{(a,b]} e^{cf} ≤ (b − a) e^{cJ₀} + Σ_{J₀ ≤ j ≤ J₁} e^{cj+c} |{f ≥ j}|`. -/
theorem setIntegral_exp_mul_le_sum {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfm : AEMeasurable f (volume.restrict (Ioc a b))) {J₀ J₁ : ℕ}
    (hf : ∀ t ∈ Ioc a b, f t ≤ J₁) :
    ∫ t in Ioc a b, Real.exp (c * f t) ≤ (b - a) * Real.exp (c * J₀) +
      ∑ j ∈ Finset.Icc J₀ J₁, Real.exp (c * j + c) *
        (volume.restrict (Ioc a b)).real {t | (j : ℝ) ≤ f t} := by
  set μ := volume.restrict (Ioc a b)
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hnull : ∀ j : ℕ, NullMeasurableSet {t | (j : ℝ) ≤ f t} μ := fun j =>
    nullMeasurableSet_le aemeasurable_const hfm
  set g : ℝ → ℝ := fun t => Real.exp (c * J₀) + ∑ j ∈ Finset.Icc J₀ J₁,
    Real.exp (c * j + c) * ({t | (j : ℝ) ≤ f t}.indicator (fun _ => (1 : ℝ)) t) with hg
  have hind : ∀ j : ℕ, Integrable ({t | (j : ℝ) ≤ f t}.indicator (fun _ => (1 : ℝ))) μ := fun j =>
    (integrable_const (1 : ℝ)).indicator₀ (hnull j)
  have hgint : Integrable g μ :=
    (integrable_const _).add (integrable_finsetSum _ fun j _ => (hind j).const_mul _)
  have hpt : ∀ᵐ t ∂μ, Real.exp (c * f t) ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := exp_mul_le_sum hc (J₀ := J₀) (hf t ht)
    refine h.trans (le_of_eq ?_)
    simp only [hg]
    congr 1
  have hle := integral_mono_of_nonneg (Eventually.of_forall fun t => (Real.exp_pos _).le) hgint hpt
  refine hle.trans (le_of_eq ?_)
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => (hind j).const_mul _),
    integral_const, integral_finsetSum _ fun j _ => (hind j).const_mul _]
  congr 1
  · rw [smul_eq_mul, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_indicator₀ (hnull j), setIntegral_const, smul_eq_mul, mul_one]

/-! ### Two sums -/

/-- `Σ_{J₀ ≤ j ≤ J₁} e^{−j} ≤ 2`. -/
theorem sum_exp_neg_le_two (J₀ J₁ : ℕ) :
    ∑ j ∈ Finset.Icc J₀ J₁, Real.exp (-(j : ℝ)) ≤ 2 := by
  have hsub : Finset.Icc J₀ J₁ ⊆ Finset.range (J₁ + 1) := fun j hj => by
    rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (Real.exp_pos _).le)).trans ?_
  have hgeo : ∀ j : ℕ, Real.exp (-(j : ℝ)) = (Real.exp (-1)) ^ j := by
    intro j; rw [← Real.exp_nat_mul]; ring_nf
  simp_rw [hgeo]
  have hr : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hr0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hhalf : Real.exp (-1) ≤ 1 / 2 := by
    have h := Real.add_one_le_exp 1
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  rw [geom_sum_eq hr.ne]
  rw [div_le_iff_of_neg (by linarith)]
  have hpow : 0 ≤ Real.exp (-1) ^ (J₁ + 1) := pow_nonneg hr0 _
  nlinarith

/-- `Σ_{J₀ ≤ j ≤ J₁} e^{cj − a j²} ≤ ((2c+2)/a + 1) e^{c²/(4a)} + 2` for `a > 0`, `c ≥ 0`. -/
theorem sum_exp_mul_sub_sq_le {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (J₀ J₁ : ℕ) :
    ∑ j ∈ Finset.Icc J₀ J₁, Real.exp (c * j - a * j ^ 2) ≤
      ((2 * c + 2) / a + 1) * Real.exp (c ^ 2 / (4 * a)) + 2 := by
  set S := Finset.Icc J₀ J₁
  set B : ℝ := (2 * c + 2) / a with hB
  have hB0 : 0 ≤ B := by positivity
  rw [← Finset.sum_filter_add_sum_filter_not S (fun j : ℕ => (j : ℝ) < B)]
  have hlow : ∑ j ∈ S.filter (fun j : ℕ => (j : ℝ) < B), Real.exp (c * j - a * j ^ 2) ≤
      (B + 1) * Real.exp (c ^ 2 / (4 * a)) := by
    have hterm : ∀ j : ℕ, Real.exp (c * j - a * j ^ 2) ≤ Real.exp (c ^ 2 / (4 * a)) := by
      intro j
      apply Real.exp_le_exp.mpr
      have : c * (j : ℝ) - a * j ^ 2 = c ^ 2 / (4 * a) - a * (j - c / (2 * a)) ^ 2 := by
        field_simp; ring
      rw [this]
      nlinarith [sq_nonneg ((j : ℝ) - c / (2 * a))]
    have hcard : ((S.filter (fun j : ℕ => (j : ℝ) < B)).card : ℝ) ≤ B + 1 := by
      have hsub : S.filter (fun j : ℕ => (j : ℝ) < B) ⊆ Finset.range (⌊B⌋₊ + 1) := by
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_range, Nat.lt_succ_iff]
        exact Nat.le_floor hj.2.le
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_range] at h1
      have h2 : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ B + 1 := by
        push_cast; linarith [Nat.floor_le hB0]
      exact (Nat.cast_le.mpr h1).trans h2
    calc _ ≤ ∑ j ∈ S.filter (fun j : ℕ => (j : ℝ) < B), Real.exp (c ^ 2 / (4 * a)) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = (S.filter (fun j : ℕ => (j : ℝ) < B)).card * Real.exp (c ^ 2 / (4 * a)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (B + 1) * Real.exp (c ^ 2 / (4 * a)) := by gcongr
  have hhigh : ∑ j ∈ S.filter (fun j : ℕ => ¬ (j : ℝ) < B), Real.exp (c * j - a * j ^ 2) ≤ 2 := by
    have hterm : ∀ j ∈ S.filter (fun j : ℕ => ¬ (j : ℝ) < B),
        Real.exp (c * j - a * j ^ 2) ≤ Real.exp (-(j : ℝ)) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have hjB : B ≤ j := not_lt.mp hj.2
      apply Real.exp_le_exp.mpr
      have h1 : 2 * c + 2 ≤ a * j := by rw [hB, div_le_iff₀ ha] at hjB; linarith
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have h2 := mul_le_mul_of_nonneg_left h1 hj0
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => (Real.exp_pos _).le)).trans ?_
    exact sum_exp_neg_le_two J₀ J₁
  linarith

/-! ### Mertens and length bounds for the parameters -/

theorem mertensS_nonneg (N : ℕ) : 0 ≤ Sieve.mertensS N :=
  Finset.sum_nonneg fun p _ => by positivity

theorem mertensS_eq_zero_of_lt {N : ℕ} (hN : N < 2) : Sieve.mertensS N = 0 := by
  unfold Sieve.mertensS
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Nat.primesLE, Nat.mem_primesBelow] at hp
  have := hp.2.two_le
  omega

/-- `Σ_{p ≤ z} 1/p ≤ log log T + |B₊|` for `z ≤ T`, `T ≥ e`. -/
theorem mertensS_le_logLog {z : ℕ} {T : ℝ} (hzT : (z : ℝ) ≤ T) (hT : Real.exp 1 ≤ T) :
    Sieve.mertensS z ≤ Real.log (Real.log T) + |Sieve.mertensSecondUpperConst| := by
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hlogT1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]; exact hT
  have hll0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlogT1
  rcases lt_or_ge z 2 with hz | hz
  · rw [mertensS_eq_zero_of_lt hz]; positivity
  · refine (Sieve.mertensS_le hz).trans ?_
    have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
    have hlz : 0 < Real.log z := Real.log_pos (by linarith)
    have h1 : Sieve.logLog z ≤ Real.log (Real.log T) := by
      unfold Sieve.logLog
      exact Real.log_le_log hlz (Real.log_le_log (by linarith) hzT)
    have h2 := le_abs_self Sieve.mertensSecondUpperConst
    linarith

theorem polyLength_le_exp_add_one {L : ℝ} (hL : 0 ≤ L) :
    (polyLength L : ℝ) ≤ Real.exp (L + 1) := by
  unfold polyLength
  have h1 := Nat.ceil_lt_add_one (Real.exp_pos L).le
  have h2 : Real.exp L + 1 ≤ Real.exp (L + 1) := by
    rw [Real.exp_add]
    have he := Real.add_one_le_exp 1
    have hL1 : 1 ≤ Real.exp L := Real.one_le_exp hL
    nlinarith
  linarith

theorem two_le_polyLength {L : ℝ} (hL : 1 ≤ L) : 2 ≤ polyLength L := by
  unfold polyLength
  have h : (2 : ℝ) < Real.exp L := by
    have := Real.add_one_le_exp L
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    exact lt_of_lt_of_le h2 (Real.exp_le_exp.mpr hL)
  have := Nat.le_ceil (Real.exp L)
  exact_mod_cast (show (2 : ℝ) ≤ ⌈Real.exp L⌉₊ by
    have : (2 : ℝ) < ⌈Real.exp L⌉₊ := lt_of_lt_of_le h this
    linarith)

/-- **The middle range has variance `O(log ℓ)`**: with `z = ⌊e^{L/ℓ}⌋`, `N = ⌈e^L⌉`,
`Σ_{z < p ≤ N} 1/p ≤ log(4ℓ) + |B₊| + |B₋|`. -/
theorem mertensS_sub_le {L ℓ : ℝ} (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ) :
    Sieve.mertensS (polyLength L) - Sieve.mertensS ⌊Real.exp (L / ℓ)⌋₊ ≤
      Real.log (4 * ℓ) + |Sieve.mertensSecondUpperConst| + |Sieve.mertensSecondLowerConst| := by
  set z : ℕ := ⌊Real.exp (L / ℓ)⌋₊ with hz
  set N : ℕ := polyLength L with hN
  have hN2 := two_le_polyLength hL
  have hNr : (N : ℝ) ≤ Real.exp (L + 1) := polyLength_le_exp_add_one (by linarith)
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlogN : Real.log N ≤ L + 1 := by
    rw [← Real.log_exp (L + 1)]; exact Real.log_le_log (by linarith) hNr
  have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hup := Sieve.mertensS_le hN2
  have hMp := le_abs_self Sieve.mertensSecondUpperConst
  have hMm := neg_abs_le Sieve.mertensSecondLowerConst
  have hMm' := le_abs_self Sieve.mertensSecondLowerConst
  have hMp0 := abs_nonneg Sieve.mertensSecondUpperConst
  have hMm0 := abs_nonneg Sieve.mertensSecondLowerConst
  by_cases hcase : 2 * Real.log 2 ≤ L / ℓ
  · -- `z ≥ 4` and `log z ≥ L/(2ℓ)`
    have he4 : 4 ≤ Real.exp (L / ℓ) := by
      have : Real.exp (2 * Real.log 2) = 4 := by
        rw [show 2 * Real.log 2 = Real.log (2 ^ 2) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by norm_num)]; norm_num
      rw [← this]; exact Real.exp_le_exp.mpr hcase
    have hz4 : 4 ≤ z := by
      rw [hz]; exact Nat.le_floor (by exact_mod_cast he4)
    have hzr : Real.exp (L / ℓ) / 2 ≤ z := by
      have := Nat.lt_floor_add_one (Real.exp (L / ℓ))
      rw [← hz] at this
      linarith
    have hlogz : L / (2 * ℓ) ≤ Real.log z := by
      have h1 : Real.log (Real.exp (L / ℓ) / 2) ≤ Real.log z :=
        Real.log_le_log (by positivity) hzr
      rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
      have h2 : L / (2 * ℓ) = L / ℓ - L / (2 * ℓ) := by field_simp; ring
      have h3 : Real.log 2 ≤ L / (2 * ℓ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ℓ)]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < ℓ)] at hcase
        linarith
      linarith
    have hlogzpos : 0 < Real.log z := lt_of_lt_of_le (by positivity) hlogz
    have hlow := Sieve.le_mertensS (show 2 ≤ z by omega)
    have hratio : Real.log N / Real.log z ≤ 4 * ℓ := by
      rw [div_le_iff₀ hlogzpos]
      have : L + 1 ≤ 4 * ℓ * (L / (2 * ℓ)) := by
        have e : 4 * ℓ * (L / (2 * ℓ)) = 2 * L := by field_simp; ring
        rw [e]; linarith
      nlinarith
    have hll : Sieve.logLog N - Sieve.logLog z ≤ Real.log (4 * ℓ) := by
      unfold Sieve.logLog
      rw [← Real.log_div hlogNpos.ne' hlogzpos.ne']
      exact Real.log_le_log (div_pos hlogNpos hlogzpos) hratio
    linarith
  · -- `L < 2ℓ log 2`: the whole sum up to `N`
    push Not at hcase
    have hL4 : L + 1 ≤ 4 * ℓ := by
      have h2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ℓ)] at hcase
      nlinarith
    have hll : Sieve.logLog N ≤ Real.log (4 * ℓ) := by
      unfold Sieve.logLog
      exact Real.log_le_log hlogNpos (hlogN.trans hL4)
    have hz0 := mertensS_nonneg z
    linarith


theorem nat_pow_le_exp {x : ℕ} {y : ℝ} (hx : (x : ℝ) ≤ Real.exp y) (k : ℕ) :
    ((x ^ k : ℕ) : ℝ) ≤ Real.exp (k * y) := by
  push_cast
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg x) hx k

theorem length_le {m : ℕ} {X : ℝ} (hm : (m : ℝ) ≤ Real.exp X) (hX : 0 ≤ X) :
    8 * (m : ℝ) * (1 + Real.log m) ≤ 8 * Real.exp X * (1 + X) := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp; positivity
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
    have hlog : Real.log m ≤ X := by
      rw [← Real.log_exp X]; exact Real.log_le_log (by linarith) hm
    have hl0 : 0 ≤ Real.log m := Real.log_nonneg hm1
    have : (m : ℝ) * (1 + Real.log m) ≤ Real.exp X * (1 + X) :=
      mul_le_mul hm (by linarith) (by linarith) (Real.exp_pos _).le
    linarith

theorem length_pow_le {x k : ℕ} {y T : ℝ} (hx : (x : ℝ) ≤ Real.exp y)
    (hky : k * y ≤ 3 * Real.log T / 8) (hT : 0 ≤ Real.log T)
    (hlen : 8 * Real.exp (3 * Real.log T / 8) * (1 + 3 * Real.log T / 8) ≤ T) :
    8 * ((x ^ k : ℕ) : ℝ) * (1 + Real.log (x ^ k : ℕ)) ≤ T :=
  (length_le ((nat_pow_le_exp hx k).trans (Real.exp_le_exp.mpr hky)) (by positivity)).trans hlen

theorem exp_mul_le_of_le_div {δ X W M k : ℝ} (hW : 0 < W) (hM : M ≤ W) (hk0 : 0 ≤ k)
    (hk : k ≤ Real.exp (-δ) * X / W) : Real.exp δ * k * M ≤ X := by
  have h1 : k * W ≤ Real.exp (-δ) * X := by rwa [le_div_iff₀ hW] at hk
  have h2 : Real.exp δ * Real.exp (-δ) = 1 := by rw [← Real.exp_add]; simp
  have hek : 0 ≤ Real.exp δ * k := mul_nonneg (Real.exp_pos δ).le hk0
  calc Real.exp δ * k * M ≤ Real.exp δ * k * W := mul_le_mul_of_nonneg_left hM hek
    _ = Real.exp δ * (k * W) := by ring
    _ ≤ Real.exp δ * (Real.exp (-δ) * X) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos δ).le
    _ = X := by rw [← mul_assoc, h2, one_mul]

theorem exp_mul_le_of_le {δ W M k c X : ℝ} (hM : M ≤ W) (hk0 : 0 ≤ k) (hkc : k ≤ c)
    (hW0 : 0 ≤ W) (h : Real.exp δ * W * c ≤ X) : Real.exp δ * k * M ≤ X := by
  have hek : 0 ≤ Real.exp δ * k := mul_nonneg (Real.exp_pos δ).le hk0
  calc Real.exp δ * k * M ≤ Real.exp δ * k * W := mul_le_mul_of_nonneg_left hM hek
    _ = Real.exp δ * W * k := by ring
    _ ≤ Real.exp δ * W * c :=
        mul_le_mul_of_nonneg_left hkc (mul_nonneg (Real.exp_pos δ).le hW0)
    _ ≤ X := h

/-- Order `min ⌊a⌋ ⌊b⌋` with `b ≥ mV`: `e^{−k} ≤ e (e^{−a} + e^{−mV})`. -/
theorem exp_neg_min_floor_le {a b m V : ℝ} (hbV : m * V ≤ b) :
    Real.exp (-((min ⌊a⌋₊ ⌊b⌋₊ : ℕ) : ℝ)) ≤
      Real.exp 1 * (Real.exp (-a) + Real.exp (-(m * V))) := by
  have hk : min a b - 1 ≤ ((min ⌊a⌋₊ ⌊b⌋₊ : ℕ) : ℝ) := by
    have h1 : a - 1 ≤ (⌊a⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one a]
    have h2 : b - 1 ≤ (⌊b⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one b]
    rw [Nat.cast_min]
    rcases min_cases (⌊a⌋₊ : ℝ) (⌊b⌋₊ : ℝ) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · linarith [min_le_left a b]
    · linarith [min_le_right a b]
  have he : Real.exp (-((min ⌊a⌋₊ ⌊b⌋₊ : ℕ) : ℝ)) ≤ Real.exp 1 * Real.exp (-(min a b)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  refine he.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le)
  rcases min_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · have := (Real.exp_pos (-(m * V))).le; linarith
  · have : Real.exp (-b) ≤ Real.exp (-(m * V)) := Real.exp_le_exp.mpr (by linarith)
    have := (Real.exp_pos (-a)).le; linarith

/-- `(e^{−4m/ε}/e)^{⌊εV/4⌋} ≤ e^{4m/ε+1} e^{−mV}`. -/
theorem pow_floor_le {ε m V : ℝ} (hε : 0 < ε) (hm : 0 ≤ m) (hV : 0 ≤ V) :
    (Real.exp (-(4 * m / ε)) / Real.exp 1) ^ ⌊ε * V / 4⌋₊ ≤
      Real.exp (4 * m / ε + 1) * Real.exp (-(m * V)) := by
  have hqe : Real.exp (-(4 * m / ε)) / Real.exp 1 = Real.exp (-(4 * m / ε) - 1) := by
    rw [Real.exp_sub]
  rw [hqe, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, ⌊ε * V / 4⌋₊ = k := ⟨_, rfl⟩
  rw [hkdef]
  have hk : ε * V / 4 - 1 ≤ k := by
    have := Nat.lt_floor_add_one (ε * V / 4); rw [hkdef] at this; linarith
  have hc : 0 ≤ 4 * m / ε := by positivity
  have h1 : (k : ℝ) * (-(4 * m / ε) - 1) ≤ (ε * V / 4 - 1) * (-(4 * m / ε) - 1) :=
    mul_le_mul_of_nonpos_right hk (by linarith)
  have e : (ε * V / 4 - 1) * (-(4 * m / ε) - 1) = -(m * V) - ε * V / 4 + (4 * m / ε + 1) := by
    field_simp; ring
  have : 0 ≤ ε * V / 4 := by positivity
  linarith

theorem two_le_log_four_mul {ℓ : ℝ} (hℓ : 2 ≤ ℓ) : 2 ≤ Real.log (4 * ℓ) := by
  have h8 : Real.log 8 ≤ Real.log (4 * ℓ) := Real.log_le_log (by norm_num) (by linarith)
  have : (2 : ℝ) ≤ Real.log 8 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  linarith

/-- **The bound at one level.**  For `V = j` in the admissible range, with `ℓ = log log T`,
`W₁ = κ²(ℓ + |B₊|) + 1`, `W₂ = κ²(log 4ℓ + |B₊| + |B₋|) + 1` and `q = e^{−4m/ε}`:
`|{t ∈ (T, 2T] : log|F| ≥ j}| ≤ (e²/ε) T (e·e^{−e^{−ε}((1−4ε)j)²/W₁} + (e + 2e^{4m/ε+1}) e^{−mj})`.
The orders are `k₁ = min(⌊e^{−ε}((1−4ε)j)²/W₁⌋, ⌊εjℓ/4⌋)` and `k₂ = k₃ = ⌊εj/4⌋`, with
`L = log T/(εj)` and `z = ⌊e^{L/ℓ}⌋`. -/
theorem measureReal_level_le_explicit {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {T ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8)
    {m : ℝ} (hm : 0 < m) (j : ℕ) (hT4 : 4 ≤ T) (hlogT : Real.log 2 + 6 ≤ Real.log T)
    (hℓ12 : 4 * m / ε ≤ Real.log (Real.log T)) (hℓ2 : 2 ≤ Real.log (Real.log T))
    (hlen : 8 * Real.exp (3 * Real.log T / 8) * (1 + 3 * Real.log T / 8) ≤ T)
    (hjA : 1 ≤ ε * j)
    (hjB : (∑' n, restWeight lam n) + ((∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) + 2) ≤ ε * j)
    (hjC : Real.exp ε * (κ ^ 2 * (Real.log (4 * Real.log (Real.log T)) +
      |Sieve.mertensSecondUpperConst| + |Sieve.mertensSecondLowerConst|) + 1) /
        (Real.exp (-(4 * m / ε)) * ε) ≤ j)
    (hjD : (j : ℝ) ≤ Real.log T / (2 * ε)) :
    (volume.restrict (Ioc T (2 * T))).real
        {t | (j : ℝ) ≤ (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re} ≤
      Real.exp 2 / ε * T * (Real.exp 1 * Real.exp (-(Real.exp (-ε) * ((1 - 4 * ε) * j) ^ 2 /
        (κ ^ 2 * (Real.log (Real.log T) + |Sieve.mertensSecondUpperConst|) + 1))) +
        (Real.exp 1 + 2 * Real.exp (4 * m / ε + 1)) * Real.exp (-(m * j))) := by
  have hT0 : 0 < T := by linarith only [hT4]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTpos : 0 < Real.log T := by linarith only [hlog2, hlogT]
  have hj0 : (0 : ℝ) < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; norm_num at hjA
    · exact_mod_cast h
  have hεj : 0 < ε * j := mul_pos hε hj0
  have heT : Real.exp 1 ≤ T := by
    calc Real.exp 1 ≤ Real.exp (Real.log T) := Real.exp_le_exp.mpr (by linarith only [hlog2, hlogT])
      _ = T := Real.exp_log hT0
  have hεjT : ε * j ≤ Real.log T / 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε)] at hjD
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith only [hjD]
  generalize hℓdef : Real.log (Real.log T) = ℓ at hℓ12 hℓ2 hjC ⊢
  have hℓ1 : 1 ≤ ℓ := by linarith only [hℓ2]
  have hℓ0 : ℓ ≠ 0 := (by linarith only [hℓ2] : (0 : ℝ) < ℓ).ne'
  have hε0 : ε ≠ 0 := hε.ne'
  have hj0' : (j : ℝ) ≠ 0 := hj0.ne'
  obtain ⟨L, hL⟩ : ∃ L, Real.log T / (ε * j) = L := ⟨_, rfl⟩
  have hL2 : 2 ≤ L := by
    rw [← hL, le_div_iff₀ hεj]; linarith only [hεjT]
  have hLT : L ≤ Real.log T := by
    rw [← hL, div_le_iff₀ hεj]; exact le_mul_of_one_le_right hlogTpos.le hjA
  have hLℓ : L / ℓ ≤ L := div_le_self (by linarith only [hL2]) hℓ1
  obtain ⟨z, hz⟩ : ∃ z : ℕ, ⌊Real.exp (L / ℓ)⌋₊ = z := ⟨_, rfl⟩
  have hzr : (z : ℝ) ≤ Real.exp (L / ℓ) := by rw [← hz]; exact Nat.floor_le (Real.exp_pos _).le
  obtain ⟨N, hN⟩ : ∃ N : ℕ, polyLength L = N := ⟨_, rfl⟩
  have hzN : z ≤ N := by
    have h1 : (z : ℝ) ≤ Real.exp L := hzr.trans (Real.exp_le_exp.mpr hLℓ)
    have h2 : Real.exp L ≤ (N : ℝ) := by rw [← hN]; exact Nat.le_ceil _
    exact_mod_cast h1.trans h2
  have hzT : (z : ℝ) ≤ T := by
    calc (z : ℝ) ≤ Real.exp (L / ℓ) := hzr
      _ ≤ Real.exp (Real.log T) := Real.exp_le_exp.mpr (hLℓ.trans hLT)
      _ = T := Real.exp_log hT0
  -- the variances
  generalize hW₁def : κ ^ 2 * (ℓ + |Sieve.mertensSecondUpperConst|) + 1 = W₁
  have hBp := abs_nonneg Sieve.mertensSecondUpperConst
  have hBm := abs_nonneg Sieve.mertensSecondLowerConst
  have hW₁pos : 0 < W₁ := by
    rw [← hW₁def]
    have := mul_nonneg (sq_nonneg κ) (show 0 ≤ ℓ + |Sieve.mertensSecondUpperConst| by
      linarith only [hℓ1, hBp])
    linarith only [this]
  have hMz : κ ^ 2 * Sieve.mertensS z ≤ W₁ := by
    have h := mertensS_le_logLog hzT heT
    rw [hℓdef] at h
    have := mul_le_mul_of_nonneg_left h (sq_nonneg κ)
    rw [← hW₁def]; linarith only [this]
  generalize hW₂def : κ ^ 2 * (Real.log (4 * ℓ) + |Sieve.mertensSecondUpperConst| +
    |Sieve.mertensSecondLowerConst|) + 1 = W₂ at hjC
  have hlog4ℓ := two_le_log_four_mul hℓ2
  have hMid : κ ^ 2 * (Sieve.mertensS N - Sieve.mertensS z) ≤ W₂ := by
    have h := mertensS_sub_le (L := L) (ℓ := ℓ) (by linarith only [hL2]) hℓ1
    rw [hN, hz] at h
    have := mul_le_mul_of_nonneg_left h (sq_nonneg κ)
    rw [← hW₂def]; linarith only [this]
  have h2κ : 2 * κ ^ 2 ≤ W₂ := by
    rw [← hW₂def]
    have := mul_nonneg (sq_nonneg κ) (show 0 ≤ Real.log (4 * ℓ) +
      |Sieve.mertensSecondUpperConst| + |Sieve.mertensSecondLowerConst| - 2 by
        linarith only [hlog4ℓ, hBp, hBm])
    linarith only [this]
  have hW₂0 : 0 ≤ W₂ := by linarith only [h2κ, sq_nonneg κ]
  generalize hqdef : Real.exp (-(4 * m / ε)) = q at hjC
  have hq0 : 0 < q := by rw [← hqdef]; exact Real.exp_pos _
  have hqj : Real.exp ε * W₂ * (ε * j / 4) ≤ q * (ε * j / 2) ^ 2 := by
    rw [div_le_iff₀ (mul_pos hq0 hε)] at hjC
    have h1 : Real.exp ε * W₂ ≤ q * ε * j := by linarith only [hjC]
    have e : q * (ε * j / 2) ^ 2 = (q * ε * j) * (ε * j / 4) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  -- the orders
  obtain ⟨k₁, hk₁⟩ : ∃ k : ℕ,
      min ⌊Real.exp (-ε) * ((1 - 4 * ε) * j) ^ 2 / W₁⌋₊ ⌊ε * j * ℓ / 4⌋₊ = k := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k : ℕ, ⌊ε * j / 4⌋₊ = k := ⟨_, rfl⟩
  have ha0 : 0 ≤ Real.exp (-ε) * ((1 - 4 * ε) * j) ^ 2 / W₁ :=
    div_nonneg (by positivity) hW₁pos.le
  have hb0 : 0 ≤ ε * j * ℓ / 4 :=
    div_nonneg (mul_nonneg hεj.le (by linarith only [hℓ1])) (by norm_num)
  have hk₁a : (k₁ : ℝ) ≤ Real.exp (-ε) * ((1 - 4 * ε) * j) ^ 2 / W₁ := by
    rw [← hk₁]; exact (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le ha0)
  have hk₁b : (k₁ : ℝ) ≤ ε * j * ℓ / 4 := by
    rw [← hk₁]; exact (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le hb0)
  have hk₂a : (k₂ : ℝ) ≤ ε * j / 4 := by
    rw [← hk₂]; exact Nat.floor_le (by positivity)
  have hK₁ : Real.exp ε * k₁ * (κ ^ 2 * Sieve.mertensS z) ≤ ((1 - 4 * ε) * j) ^ 2 :=
    exp_mul_le_of_le_div hW₁pos hMz (Nat.cast_nonneg _) hk₁a
  have hK₂ : Real.exp ε * k₂ * (κ ^ 2 * (Sieve.mertensS N - Sieve.mertensS z)) ≤
      q * (ε * j / 2) ^ 2 :=
    exp_mul_le_of_le hMid (Nat.cast_nonneg _) hk₂a hW₂0 hqj
  have hK₃ : Real.exp ε * k₂ * (2 * κ ^ 2) ≤ q * (ε * j / 2) ^ 2 :=
    exp_mul_le_of_le h2κ (Nat.cast_nonneg _) hk₂a hW₂0 hqj
  -- the lengths
  have hN₁ : 8 * ((z ^ k₁ : ℕ) : ℝ) * (1 + Real.log (z ^ k₁ : ℕ)) ≤ T := by
    refine length_pow_le hzr ?_ hlogTpos.le hlen
    have h1 : (k₁ : ℝ) * (L / ℓ) ≤ ε * j * ℓ / 4 * (L / ℓ) :=
      mul_le_mul_of_nonneg_right hk₁b (div_nonneg (by linarith only [hL2])
        (by linarith only [hℓ1]))
    have h2 : ε * j * ℓ / 4 * (L / ℓ) = Real.log T / 4 := by
      rw [← hL]; field_simp
    linarith only [h1, h2, hlogTpos]
  have hNe : (N : ℝ) ≤ Real.exp (L + 1) := by
    rw [← hN]; exact polyLength_le_exp_add_one (by linarith only [hL2])
  have hN₂ : 8 * ((N ^ k₂ : ℕ) : ℝ) * (1 + Real.log (N ^ k₂ : ℕ)) ≤ T := by
    refine length_pow_le hNe ?_ hlogTpos.le hlen
    have h1 : (k₂ : ℝ) * (L + 1) ≤ ε * j / 4 * (L + 1) :=
      mul_le_mul_of_nonneg_right hk₂a (by linarith only [hL2])
    have h2 : ε * j / 4 * L = Real.log T / 4 := by
      rw [← hL]; field_simp
    have h3 : ε * j / 4 * (L + 1) = Real.log T / 4 + ε * j / 4 := by rw [mul_add, h2, mul_one]
    linarith only [h1, h3, hεjT]
  have hN₃ : 8 * ((N ^ k₂ : ℕ) : ℝ) * (1 + Real.log (N ^ k₂ : ℕ)) ≤ 2 * T := by
    linarith only [hN₂, hT0]
  -- the tails
  have hT1 : Real.exp (-(k₁ : ℝ)) ≤ Real.exp 1 * (Real.exp (-(Real.exp (-ε) *
      ((1 - 4 * ε) * j) ^ 2 / W₁)) + Real.exp (-(m * j))) := by
    have h12 : 4 * m ≤ ε * ℓ := by rw [div_le_iff₀ hε] at hℓ12; linarith only [hℓ12]
    have hb3 : m * (j : ℝ) ≤ ε * j * ℓ / 4 := by
      linarith only [mul_le_mul_of_nonneg_right h12 hj0.le]
    rw [← hk₁]
    exact exp_neg_min_floor_le hb3
  have hT2 : (q / Real.exp 1) ^ k₂ ≤ Real.exp (4 * m / ε + 1) * Real.exp (-(m * j)) := by
    rw [← hk₂, ← hqdef]; exact pow_floor_le hε hm.le hj0.le
  have hpos : 0 ≤ Real.exp 2 / ε * T := mul_nonneg (div_nonneg (Real.exp_pos 2).le hε.le) hT0.le
  have hfin : Real.exp 2 / ε * T * (Real.exp (-(k₁ : ℝ)) + (q / Real.exp 1) ^ k₂ +
      (q / Real.exp 1) ^ k₂) ≤ Real.exp 2 / ε * T * (Real.exp 1 * Real.exp (-(Real.exp (-ε) *
        ((1 - 4 * ε) * j) ^ 2 / W₁)) +
        (Real.exp 1 + 2 * Real.exp (4 * m / ε + 1)) * Real.exp (-(m * j))) := by
    refine mul_le_mul_of_nonneg_left ?_ hpos
    linarith only [hT1, hT2]
  subst hN
  subst hL
  have hε4 : ε < 1 / 4 := by linarith only [hε8]
  have hε1 : ε ≤ 1 := by linarith only [hε8]
  have hlev := measureReal_level_le hW hA hκ hlam (T := T) (ε := ε) (V := (j : ℝ)) (δ := ε)
    (q := q) z k₁ k₂ k₂ hT4 hlogT hε hε4 hjA hL2 hjB hε hε1 hq0 hzN hK₁ hN₁ hK₂ hN₂ hK₃ hN₃
  exact hlev.trans hfin


/-! ### Summing the levels -/

theorem sum_levels_le {c : ℝ} (hc : 0 ≤ c) {J₀ J₁ : ℕ} {ms : ℕ → ℝ} {D a K : ℝ} (hD : 0 ≤ D)
    (ha : 0 < a) (hK : 0 ≤ K) (hm : ∀ j ∈ Finset.Icc J₀ J₁, ms j ≤
      D * (Real.exp 1 * Real.exp (-(a * j ^ 2)) + K * Real.exp (-((c + 1) * j)))) :
    ∑ j ∈ Finset.Icc J₀ J₁, Real.exp (c * j + c) * ms j ≤
      D * (Real.exp (c + 1) * (((2 * c + 2) / a + 1) * Real.exp (c ^ 2 / (4 * a)) + 2) +
        2 * K * Real.exp c) := by
  have hterm : ∀ j ∈ Finset.Icc J₀ J₁, Real.exp (c * j + c) * ms j ≤
      D * (Real.exp (c + 1) * Real.exp (c * j - a * j ^ 2) +
        K * Real.exp c * Real.exp (-(j : ℝ))) := by
    intro j hj
    have h := mul_le_mul_of_nonneg_left (hm j hj) (Real.exp_pos (c * j + c)).le
    refine h.trans (le_of_eq ?_)
    have e1 : Real.exp (c * j + c) * Real.exp 1 * Real.exp (-(a * j ^ 2)) =
        Real.exp (c + 1) * Real.exp (c * j - a * j ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (c * j + c) * Real.exp (-((c + 1) * j)) =
        Real.exp c * Real.exp (-(j : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (c * j + c) * (D * (Real.exp 1 * Real.exp (-(a * j ^ 2)) +
          K * Real.exp (-((c + 1) * j))))
        = D * (Real.exp (c * j + c) * Real.exp 1 * Real.exp (-(a * j ^ 2)) +
          K * (Real.exp (c * j + c) * Real.exp (-((c + 1) * j)))) := by ring
      _ = _ := by rw [e1, e2]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hD
  have h1 := mul_le_mul_of_nonneg_left (sum_exp_mul_sub_sq_le ha hc J₀ J₁)
    (Real.exp_pos (c + 1)).le
  have h2 := mul_le_mul_of_nonneg_left (sum_exp_neg_le_two J₀ J₁)
    (mul_nonneg hK (Real.exp_pos c).le)
  linarith only [h1, h2]

/-! ### Large parameters -/

/-- `c₀ + c₁ log x ≤ ε x` for all large `x`. -/
theorem eventually_add_mul_log_le (c₀ c₁ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, c₀ + c₁ * Real.log x ≤ ε * x := by
  have hc : 0 < |c₁| + 1 := by positivity
  have hδ : 0 < ε / (2 * (|c₁| + 1)) := by positivity
  filter_upwards [Real.isLittleO_log_id_atTop.bound hδ, eventually_ge_atTop (2 * |c₀| / ε),
    eventually_ge_atTop (0 : ℝ)] with x hx hx0 hxnn
  simp only [Real.norm_eq_abs, id, abs_of_nonneg hxnn] at hx
  have h1 : c₁ * Real.log x ≤ |c₁| * |Real.log x| := by
    rw [← abs_mul]; exact le_abs_self _
  have h2 : |c₁| * |Real.log x| ≤ |c₁| * (ε / (2 * (|c₁| + 1)) * x) :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have h3 : |c₁| * (ε / (2 * (|c₁| + 1)) * x) ≤ ε * x / 2 := by
    have hr : |c₁| / (|c₁| + 1) ≤ 1 := by
      rw [div_le_one hc]; linarith only
    have e : |c₁| * (ε / (2 * (|c₁| + 1)) * x) = |c₁| / (|c₁| + 1) * (ε * x / 2) := by
      field_simp
    rw [e]
    calc |c₁| / (|c₁| + 1) * (ε * x / 2) ≤ 1 * (ε * x / 2) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
      _ = ε * x / 2 := one_mul _
  have h4 : c₀ ≤ ε * x / 2 := by
    rw [div_le_iff₀ hε] at hx0
    linarith only [hx0, le_abs_self c₀]
  linarith only [h1, h2, h3, h4]

/-- `8 e^{3y/8} (1 + 3y/8) ≤ e^y` for all large `y`. -/
theorem eventually_length_le :
    ∀ᶠ y in atTop, 8 * Real.exp (3 * y / 8) * (1 + 3 * y / 8) ≤ Real.exp y := by
  filter_upwards [eventually_add_mul_log_le (Real.log 8) 1 (show (0 : ℝ) < 5 / 8 by norm_num),
    eventually_ge_atTop (8 / 5 : ℝ)] with y hy hy1
  have hy0 : 0 < y := by linarith only [hy1]
  have h1 : 8 * (1 + 3 * y / 8) ≤ Real.exp (5 / 8 * y) := by
    calc 8 * (1 + 3 * y / 8) ≤ 8 * y := by linarith only [hy1]
      _ = Real.exp (Real.log 8 + 1 * Real.log y) := by
        rw [one_mul, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hy0]
      _ ≤ Real.exp (5 / 8 * y) := Real.exp_le_exp.mpr hy
  calc 8 * Real.exp (3 * y / 8) * (1 + 3 * y / 8) =
        Real.exp (3 * y / 8) * (8 * (1 + 3 * y / 8)) := by ring
    _ ≤ Real.exp (3 * y / 8) * Real.exp (5 / 8 * y) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp y := by rw [← Real.exp_add]; congr 1; ring

/-- `u + v ℓ ≤ e^{εℓ}` for all large `ℓ`, when `u, v ≥ 0`. -/
theorem eventually_affine_le_exp {u v ε : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hε : 0 < ε) :
    ∀ᶠ ℓ in atTop, u + v * ℓ ≤ Real.exp (ε * ℓ) := by
  filter_upwards [eventually_add_mul_log_le (Real.log (u + v + 1)) 1 hε,
    eventually_ge_atTop (1 : ℝ)] with ℓ h h1
  have hℓ0 : 0 < ℓ := by linarith only [h1]
  calc u + v * ℓ ≤ (u + v + 1) * ℓ := by nlinarith
    _ = Real.exp (Real.log (u + v + 1) + 1 * Real.log ℓ) := by
      rw [one_mul, Real.exp_add, Real.exp_log (by positivity), Real.exp_log hℓ0]
    _ ≤ Real.exp (ε * ℓ) := Real.exp_le_exp.mpr h


/-- The lowest level used: above it the three parameter conditions of
`measureReal_level_le_explicit` hold. -/
def levelFloor (ε m A M κ ℓ : ℝ) : ℝ :=
  max (max (1 / ε) ((A + (M + 2)) / ε)) (Real.exp ε * (κ ^ 2 * (Real.log (4 * ℓ) +
    |Sieve.mertensSecondUpperConst| + |Sieve.mertensSecondLowerConst|) + 1) /
      (Real.exp (-(4 * m / ε)) * ε))

theorem levelFloor_conditions {ε m A M κ ℓ : ℝ} (hε : 0 < ε) {j : ℕ}
    (hj : ⌈levelFloor ε m A M κ ℓ⌉₊ ≤ j) :
    1 ≤ ε * j ∧ A + (M + 2) ≤ ε * j ∧
      Real.exp ε * (κ ^ 2 * (Real.log (4 * ℓ) + |Sieve.mertensSecondUpperConst| +
        |Sieve.mertensSecondLowerConst|) + 1) / (Real.exp (-(4 * m / ε)) * ε) ≤ j := by
  have h : levelFloor ε m A M κ ℓ ≤ j := (Nat.le_ceil _).trans (Nat.cast_le.mpr hj)
  unfold levelFloor at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := max_le_iff.mp h |>.imp_left max_le_iff.mp
  refine ⟨?_, ?_, h3⟩
  · rw [div_le_iff₀ hε] at h1; linarith only [h1]
  · rw [div_le_iff₀ hε] at h2; linarith only [h2]

theorem one_div_le_levelFloor {ε m A M κ ℓ : ℝ} : 1 / ε ≤ levelFloor ε m A M κ ℓ :=
  (le_max_left _ _).trans (le_max_left _ _)

/-- All parameter conditions hold for large `T`. -/
theorem exists_large_parameters {ε : ℝ} (hε : 0 < ε) {c : ℝ} (hc : 0 ≤ c) (m A M κ C TL : ℝ)
    (hC : 0 ≤ C) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      TL ≤ T ∧ 4 ≤ T ∧ Real.log 2 + 6 ≤ Real.log T ∧
      4 * m / ε ≤ Real.log (Real.log T) ∧ 2 ≤ Real.log (Real.log T) ∧
      8 * Real.exp (3 * Real.log T / 8) * (1 + 3 * Real.log T / 8) ≤ T ∧
      2 * C * Real.log T / Real.log (Real.log T) + 1 ≤ Real.log T / (2 * ε) ∧
      c * (levelFloor ε m A M κ (Real.log (Real.log T)) + 1) ≤ ε * Real.log (Real.log T) ∧
      (2 * c + 2) * Real.exp ε * (κ ^ 2 * (Real.log (Real.log T) +
        |Sieve.mertensSecondUpperConst|) + 1) / (1 - 4 * ε) ^ 2 + 1 ≤
          Real.exp (ε * Real.log (Real.log T)) := by
  have hy := Real.tendsto_log_atTop
  have hℓ := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hBp := abs_nonneg Sieve.mertensSecondUpperConst
  have hBm := abs_nonneg Sieve.mertensSecondLowerConst
  have h4 : ∀ᶠ T in atTop, 8 * Real.exp (3 * Real.log T / 8) * (1 + 3 * Real.log T / 8) ≤ T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hy.eventually eventually_length_le] with T hT h
    rwa [Real.exp_log hT] at h
  have h5y : ∀ᶠ y in atTop, 2 * C * y / Real.log y + 1 ≤ y / (2 * ε) := by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (8 * C * ε + 1)),
      eventually_ge_atTop (4 * ε), eventually_gt_atTop (0 : ℝ)] with y hl hy4 hy0
    have h8 : 0 ≤ 8 * C * ε := by positivity
    have hlpos : 0 < Real.log y := by linarith only [hl, h8]
    have h1 : 2 * C * y / Real.log y ≤ y / (4 * ε) := by
      rw [div_le_div_iff₀ hlpos (by positivity)]
      have e : 2 * C * y * (4 * ε) = y * (8 * C * ε) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith only [hl]) hy0.le
    have h2 : 1 ≤ y / (4 * ε) := by
      rw [le_div_iff₀ (by positivity)]; linarith only [hy4]
    have e : y / (2 * ε) = y / (4 * ε) + y / (4 * ε) := by ring
    linarith only [h1, h2, e]
  have h6ℓ : ∀ᶠ ℓ in atTop, c * (levelFloor ε m A M κ ℓ + 1) ≤ ε * ℓ := by
    filter_upwards [eventually_add_mul_log_le
      (c * (|1 / ε| + |(A + (M + 2)) / ε| + Real.exp ε * (κ ^ 2 * (Real.log 4 +
        |Sieve.mertensSecondUpperConst| + |Sieve.mertensSecondLowerConst|) + 1) /
          (Real.exp (-(4 * m / ε)) * ε) + 1))
      (c * (Real.exp ε * κ ^ 2 / (Real.exp (-(4 * m / ε)) * ε))) hε,
      eventually_ge_atTop (1 : ℝ)] with ℓ h hℓ1
    have hℓ0 : 0 < ℓ := by linarith only [hℓ1]
    have hlog4 : Real.log (4 * ℓ) = Real.log 4 + Real.log ℓ :=
      Real.log_mul (by norm_num) hℓ0.ne'
    have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
    have hlog4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hc' : Real.exp ε * (κ ^ 2 * (Real.log (4 * ℓ) + |Sieve.mertensSecondUpperConst| +
        |Sieve.mertensSecondLowerConst|) + 1) / (Real.exp (-(4 * m / ε)) * ε) =
        Real.exp ε * (κ ^ 2 * (Real.log 4 + |Sieve.mertensSecondUpperConst| +
          |Sieve.mertensSecondLowerConst|) + 1) / (Real.exp (-(4 * m / ε)) * ε) +
        Real.exp ε * κ ^ 2 / (Real.exp (-(4 * m / ε)) * ε) * Real.log ℓ := by
      rw [hlog4]; ring
    have hin : 0 ≤ κ ^ 2 * (Real.log (4 * ℓ) + |Sieve.mertensSecondUpperConst| +
        |Sieve.mertensSecondLowerConst|) + 1 := by
      have := mul_nonneg (sq_nonneg κ) (show 0 ≤ Real.log (4 * ℓ) +
        |Sieve.mertensSecondUpperConst| + |Sieve.mertensSecondLowerConst| by
          rw [hlog4]; linarith only [hlogℓ, hlog4', hBp, hBm])
      linarith only [this]
    have hthird : 0 ≤ Real.exp ε * (κ ^ 2 * (Real.log (4 * ℓ) + |Sieve.mertensSecondUpperConst| +
        |Sieve.mertensSecondLowerConst|) + 1) / (Real.exp (-(4 * m / ε)) * ε) :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le hin) (by positivity)
    have hfl : levelFloor ε m A M κ ℓ ≤ |1 / ε| + |(A + (M + 2)) / ε| +
        Real.exp ε * (κ ^ 2 * (Real.log (4 * ℓ) + |Sieve.mertensSecondUpperConst| +
          |Sieve.mertensSecondLowerConst|) + 1) / (Real.exp (-(4 * m / ε)) * ε) := by
      have ha1 := le_abs_self (1 / ε)
      have ha2 := le_abs_self ((A + (M + 2)) / ε)
      have hb1 := abs_nonneg (1 / ε)
      have hb2 := abs_nonneg ((A + (M + 2)) / ε)
      unfold levelFloor
      refine max_le (max_le ?_ ?_) ?_
      · linarith only [ha1, hb2, hthird]
      · linarith only [ha2, hb1, hthird]
      · linarith only [hb1, hb2]
    rw [hc'] at hfl
    have hfl1 : levelFloor ε m A M κ ℓ + 1 ≤ |1 / ε| + |(A + (M + 2)) / ε| +
        (Real.exp ε * (κ ^ 2 * (Real.log 4 + |Sieve.mertensSecondUpperConst| +
          |Sieve.mertensSecondLowerConst|) + 1) / (Real.exp (-(4 * m / ε)) * ε) +
        Real.exp ε * κ ^ 2 / (Real.exp (-(4 * m / ε)) * ε) * Real.log ℓ) + 1 := by
      linarith only [hfl]
    have hfl' := mul_le_mul_of_nonneg_left hfl1 hc
    refine hfl'.trans (le_of_eq_of_le ?_ h)
    ring
  have h7ℓ : ∀ᶠ ℓ in atTop, (2 * c + 2) * Real.exp ε * (κ ^ 2 * (ℓ +
      |Sieve.mertensSecondUpperConst|) + 1) / (1 - 4 * ε) ^ 2 + 1 ≤ Real.exp (ε * ℓ) := by
    have hu : 0 ≤ (2 * c + 2) * Real.exp ε * (κ ^ 2 * |Sieve.mertensSecondUpperConst| + 1) /
        (1 - 4 * ε) ^ 2 + 1 := by positivity
    have hv : 0 ≤ (2 * c + 2) * Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2 := by positivity
    filter_upwards [eventually_affine_le_exp hu hv hε] with ℓ h
    have e : (2 * c + 2) * Real.exp ε * (κ ^ 2 * (ℓ + |Sieve.mertensSecondUpperConst|) + 1) /
        (1 - 4 * ε) ^ 2 + 1 = ((2 * c + 2) * Real.exp ε * (κ ^ 2 * |Sieve.mertensSecondUpperConst| +
          1) / (1 - 4 * ε) ^ 2 + 1) + (2 * c + 2) * Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2 * ℓ := by
      ring
    rw [e]; exact h
  have hall := (eventually_ge_atTop TL).and ((eventually_ge_atTop (4 : ℝ)).and
    ((hy.eventually (eventually_ge_atTop (Real.log 2 + 6))).and
    ((hℓ.eventually (eventually_ge_atTop (4 * m / ε))).and
    ((hℓ.eventually (eventually_ge_atTop (2 : ℝ))).and (h4.and ((hy.eventually h5y).and
    ((hℓ.eventually h6ℓ).and (hℓ.eventually h7ℓ))))))))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hall
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

/-- Littlewood's bound caps `log|F|` on `(T, 2T]` at `2C log T/log log T`. -/
theorem re_producerLogZeta_le_cap {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {CL TL : ℝ}
    (hLw : ∀ σ t : ℝ, TL ≤ |t| → 1 / 2 < σ → σ ≤ 2 →
      (producerLogZeta hW σ t).re ≤ CL * Real.log |t| / Real.log (Real.log |t|))
    {T σ t : ℝ} (hTL : TL ≤ T) (hT2 : 2 ≤ T) (hℓ : 0 < Real.log (Real.log T))
    (ht : t ∈ Ioc T (2 * T)) (hσ : 1 / 2 < σ) (hσ2 : σ ≤ 2) :
    (producerLogZeta hW σ t).re ≤ 2 * max CL 0 * Real.log T / Real.log (Real.log T) := by
  have hT0 : 0 < T := by linarith only [hT2]
  have ht0 : 0 < t := hT0.trans ht.1
  have h := hLw σ t (by rw [abs_of_pos ht0]; exact hTL.trans ht.1.le) hσ hσ2
  rw [abs_of_pos ht0] at h
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith only [hT2])
  have hlogt : Real.log T ≤ Real.log t := Real.log_le_log hT0 ht.1.le
  have hℓt : Real.log (Real.log T) ≤ Real.log (Real.log t) := Real.log_le_log hlogT hlogt
  have hlog2T : Real.log t ≤ 2 * Real.log T := by
    have h1 : Real.log t ≤ Real.log (2 * T) := Real.log_le_log ht0 ht.2
    rw [Real.log_mul (by norm_num) hT0.ne'] at h1
    have h2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
    linarith only [h1, h2]
  have hC := le_max_left CL 0
  have hC0 := le_max_right CL 0
  have hq0 : 0 ≤ Real.log t / Real.log (Real.log t) :=
    div_nonneg (hlogT.le.trans hlogt) (hℓ.le.trans hℓt)
  calc (producerLogZeta hW σ t).re ≤ CL * Real.log t / Real.log (Real.log t) := h
    _ = CL * (Real.log t / Real.log (Real.log t)) := by ring
    _ ≤ max CL 0 * (Real.log t / Real.log (Real.log t)) := mul_le_mul_of_nonneg_right hC hq0
    _ ≤ max CL 0 * (2 * Real.log T / Real.log (Real.log T)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        exact div_le_div₀ (by positivity) hlog2T hℓ hℓt
    _ = 2 * max CL 0 * Real.log T / Real.log (Real.log T) := by ring

theorem final_bound {c I T d x y z E K P : ℝ} (hT : 0 < T) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hI : I ≤ T * x + d * T * (Real.exp (c + 1) * (y * z + 2) + 2 * K * Real.exp c))
    (hx : x ≤ P) (hyz : y * z ≤ E * P) (hP : 1 ≤ P) :
    I ≤ (1 + d * (Real.exp (c + 1) * (E + 2) + 2 * K * Real.exp c)) * T * P := by
  have h1 : T * x ≤ T * P := mul_le_mul_of_nonneg_left hx hT.le
  have he3 := (Real.exp_pos (c + 1)).le
  have h2 : Real.exp (c + 1) * (y * z + 2) + 2 * K * Real.exp c ≤
      P * (Real.exp (c + 1) * (E + 2) + 2 * K * Real.exp c) := by
    have a1 : Real.exp (c + 1) * (y * z) ≤ Real.exp (c + 1) * (E * P) :=
      mul_le_mul_of_nonneg_left hyz he3
    have a2 : Real.exp (c + 1) * 2 ≤ Real.exp (c + 1) * (2 * P) :=
      mul_le_mul_of_nonneg_left (by linarith only [hP]) he3
    have a3 : 2 * K * Real.exp c * 1 ≤ 2 * K * Real.exp c * P :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    have e : P * (Real.exp (c + 1) * (E + 2) + 2 * K * Real.exp c) =
        Real.exp (c + 1) * (E * P) + Real.exp (c + 1) * (2 * P) + 2 * K * Real.exp c * P := by
      ring
    rw [e]; linarith only [a1, a2, a3]
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hd hT.le)
  have e : (1 + d * (Real.exp (c + 1) * (E + 2) + 2 * K * Real.exp c)) * T * P =
      T * P + d * T * (P * (Real.exp (c + 1) * (E + 2) + 2 * K * Real.exp c)) := by ring
  rw [e]; linarith only [hI, h1, h3]

/-- The exponential factors in the final sum: with `1/a = e^ε W₁/(1−4ε)²`,
`y e^{k²/a} ≤ E · (log T)^{k²e^εκ²/(1−4ε)² + ε}` once `y ≤ (log T)^ε`. -/
theorem quadratic_factor_le {k ε κ ℓ B y : ℝ} (hyle : y ≤ Real.exp (ε * ℓ)) :
    y * Real.exp (k ^ 2 * (Real.exp ε * (κ ^ 2 * (ℓ + B) + 1) / (1 - 4 * ε) ^ 2)) ≤
      Real.exp (k ^ 2 * (Real.exp ε * (κ ^ 2 * B + 1) / (1 - 4 * ε) ^ 2)) *
        Real.exp (ℓ * (k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε)) := by
  have e : Real.exp (k ^ 2 * (Real.exp ε * (κ ^ 2 * B + 1) / (1 - 4 * ε) ^ 2)) *
      Real.exp (ℓ * (k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε)) =
      Real.exp (ε * ℓ) *
        Real.exp (k ^ 2 * (Real.exp ε * (κ ^ 2 * (ℓ + B) + 1) / (1 - 4 * ε) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hyle (Real.exp_pos _).le

/-! ### The moments -/

/-- **Moments on the Weil cone.**  If `lam` is full-cone Weil-positive, `|lam(n)| ≤ κ log n` and
the rest weight is summable, then for every `k > 0` and `0 < ε ≤ 1/8`

`∫_T^{2T} exp(2k Re log F_lam(½ + 1/log T + it)) dt ≤ C T (log T)^{k² e^ε κ²/(1−4ε)² + ε}`

for all large `T`.  For `lam = Λ` (`κ = 1`) this is Soundararajan's bound `≪ T(log T)^{k²+ε}`
just right of the line, which there needs RH. -/
theorem exists_setIntegral_exp_mul_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {k : ℝ} (hk : 0 < k) {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in Ioc T (2 * T),
          Real.exp (2 * k * (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re) ≤
        C * T * Real.log T ^ (k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε) := by
  have hc : 0 ≤ 2 * k := by positivity
  have hm : 0 < 2 * k + 1 := by positivity
  obtain ⟨CL, TL, hLw⟩ := exists_re_producerLogZeta_le_littlewood hW hκ hlam
  obtain ⟨T₀, hT₀⟩ := exists_large_parameters hε hc (2 * k + 1) (∑' n, restWeight lam n)
    (∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) κ (max CL 0) TL (le_max_right _ _)
  refine ⟨1 + Real.exp 2 / ε * (Real.exp (2 * k + 1) * (Real.exp (k ^ 2 * (Real.exp ε *
      (κ ^ 2 * |Sieve.mertensSecondUpperConst| + 1) / (1 - 4 * ε) ^ 2)) + 2) +
      2 * (Real.exp 1 + 2 * Real.exp (4 * (2 * k + 1) / ε + 1)) * Real.exp (2 * k)), T₀,
      fun T hT => ?_⟩
  obtain ⟨hTL, hT4, hlogT, hℓ12, hℓ2, hlen, hJ₁, hJ₀, hexpa⟩ := hT₀ T hT
  have hT0 : 0 < T := by linarith only [hT4]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTpos : 0 < Real.log T := by linarith only [hlog2, hlogT]
  have hσ : 1 / 2 < 1 / 2 + 1 / Real.log T := by
    have := one_div_pos.mpr hlogTpos; linarith only [this]
  have hσ2 : 1 / 2 + 1 / Real.log T ≤ 2 := by
    have : 1 / Real.log T ≤ 1 := by rw [div_le_one hlogTpos]; linarith only [hlog2, hlogT]
    linarith only [this]
  have hℓ0 : 0 < Real.log (Real.log T) := by linarith only [hℓ2]
  -- the layer cake
  have hfm : AEMeasurable (fun t => (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re)
      (volume.restrict (Ioc T (2 * T))) := by
    have hcont := (continuousOn_producerLogZeta hW hσ hσ2).mono
      (show Ioc T (2 * T) ⊆ Ioi 0 from fun t ht => hT0.trans ht.1)
    exact (Complex.continuous_re.comp_continuousOn hcont).aemeasurable measurableSet_Ioc
  obtain ⟨J₁, hJ₁def⟩ : ∃ J : ℕ,
      ⌈2 * max CL 0 * Real.log T / Real.log (Real.log T)⌉₊ = J := ⟨_, rfl⟩
  obtain ⟨J₀, hJ₀def⟩ : ∃ J : ℕ, ⌈levelFloor ε (2 * k + 1) (∑' n, restWeight lam n)
      (∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) κ (Real.log (Real.log T))⌉₊ = J := ⟨_, rfl⟩
  have hcap : ∀ t ∈ Ioc T (2 * T),
      (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re ≤ J₁ := fun t ht => by
    rw [← hJ₁def]
    exact (re_producerLogZeta_le_cap hW hLw hTL (by linarith only [hT4]) hℓ0 ht hσ
      hσ2).trans (Nat.le_ceil _)
  have hlayer := setIntegral_exp_mul_le_sum hc (by linarith only [hT0] : T ≤ 2 * T) hfm
    (J₀ := J₀) hcap
  -- the levels
  obtain ⟨W₁, hW₁⟩ : ∃ W : ℝ,
      κ ^ 2 * (Real.log (Real.log T) + |Sieve.mertensSecondUpperConst|) + 1 = W := ⟨_, rfl⟩
  have hW₁pos : 0 < W₁ := by
    rw [← hW₁]
    have := mul_nonneg (sq_nonneg κ) (show 0 ≤ Real.log (Real.log T) +
      |Sieve.mertensSecondUpperConst| by
        linarith only [hℓ0, abs_nonneg Sieve.mertensSecondUpperConst])
    linarith only [this]
  have h14 : 0 < 1 - 4 * ε := by linarith only [hε8]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, Real.exp (-ε) * (1 - 4 * ε) ^ 2 / W₁ = a := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [← ha]; exact div_pos (mul_pos (Real.exp_pos _) (pow_pos h14 2)) hW₁pos
  obtain ⟨K, hK⟩ : ∃ K : ℝ, Real.exp 1 + 2 * Real.exp (4 * (2 * k + 1) / ε + 1) = K :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [← hK]; positivity
  have hm' : ∀ j ∈ Finset.Icc J₀ J₁, (volume.restrict (Ioc T (2 * T))).real
      {t | (j : ℝ) ≤ (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re} ≤
        Real.exp 2 / ε * T * (Real.exp 1 * Real.exp (-(a * j ^ 2)) +
          K * Real.exp (-((2 * k + 1) * j))) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨hjA, hjB, hjC⟩ := levelFloor_conditions hε (hJ₀def ▸ hj.1)
    have hjD : (j : ℝ) ≤ Real.log T / (2 * ε) := by
      have h1 : (j : ℝ) ≤ J₁ := Nat.cast_le.mpr hj.2
      have h2 : (J₁ : ℝ) < 2 * max CL 0 * Real.log T / Real.log (Real.log T) + 1 := by
        rw [← hJ₁def]
        exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          (le_max_right _ _)) hlogTpos.le) hℓ0.le)
      linarith only [h1, h2, hJ₁]
    have h := measureReal_level_le_explicit hW hA hκ hlam hε hε8 hm j hT4 hlogT hℓ12 hℓ2 hlen
      hjA hjB hjC hjD
    have e : Real.exp (-ε) * ((1 - 4 * ε) * j) ^ 2 /
        (κ ^ 2 * (Real.log (Real.log T) + |Sieve.mertensSecondUpperConst|) + 1) = a * j ^ 2 := by
      rw [hW₁, ← ha]; ring
    rw [e, hK] at h
    exact h
  have hsum := sum_levels_le hc (D := Real.exp 2 / ε * T) (by positivity) ha0 hK0 hm'
  -- the exponential factors
  have hW₁' := hW₁pos.ne'
  have h14' := h14.ne'
  have hya : (2 * (2 * k) + 2) / a + 1 = (2 * (2 * k) + 2) * Real.exp ε *
      (κ ^ 2 * (Real.log (Real.log T) + |Sieve.mertensSecondUpperConst|) + 1) /
        (1 - 4 * ε) ^ 2 + 1 := by
    rw [hW₁, ← ha, Real.exp_neg]; field_simp
  have hia : (2 * k) ^ 2 / (4 * a) = k ^ 2 * (Real.exp ε * (κ ^ 2 * (Real.log (Real.log T) +
      |Sieve.mertensSecondUpperConst|) + 1) / (1 - 4 * ε) ^ 2) := by
    rw [hW₁, ← ha, Real.exp_neg]; field_simp; ring
  rw [hya, hia] at hsum
  have hyz := quadratic_factor_le (k := k) (κ := κ) (B := |Sieve.mertensSecondUpperConst|) hexpa
  have hP : Real.log T ^ (k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε) =
      Real.exp (Real.log (Real.log T) * (k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε)) :=
    Real.rpow_def_of_pos hlogTpos _
  have hβ : 0 ≤ k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) := by positivity
  have hJ₀le : Real.exp (2 * k * (J₀ : ℝ)) ≤
      Real.log T ^ (k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε) := by
    rw [hP]
    apply Real.exp_le_exp.mpr
    have hfl0 := le_trans (le_of_lt (one_div_pos.mpr hε)) (one_div_le_levelFloor (m := 2 * k + 1)
      (A := ∑' n, restWeight lam n) (M := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) (κ := κ)
      (ℓ := Real.log (Real.log T)))
    have h1 := Nat.ceil_lt_add_one hfl0
    rw [hJ₀def] at h1
    have h1' := mul_le_mul_of_nonneg_left h1.le hc
    have h2 := mul_nonneg hℓ0.le hβ
    linarith only [h1', hJ₀, h2]
  have hP1 : 1 ≤ Real.log T ^ (k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε) := by
    rw [hP]; exact Real.one_le_exp (mul_nonneg hℓ0.le (by positivity))
  rw [← hP] at hyz
  have hI : ∫ t in Ioc T (2 * T), Real.exp (2 * k * (producerLogZeta hW
      (1 / 2 + 1 / Real.log T) t).re) ≤ T * Real.exp (2 * k * (J₀ : ℝ)) + Real.exp 2 / ε * T *
        (Real.exp (2 * k + 1) * (((2 * (2 * k) + 2) * Real.exp ε * (κ ^ 2 * (Real.log
          (Real.log T) + |Sieve.mertensSecondUpperConst|) + 1) / (1 - 4 * ε) ^ 2 + 1) *
          Real.exp (k ^ 2 * (Real.exp ε * (κ ^ 2 * (Real.log (Real.log T) +
            |Sieve.mertensSecondUpperConst|) + 1) / (1 - 4 * ε) ^ 2)) + 2) +
          2 * K * Real.exp (2 * k)) := by
    have e : (2 * T - T) * Real.exp (2 * k * (J₀ : ℝ)) = T * Real.exp (2 * k * (J₀ : ℝ)) := by
      ring
    linarith only [hlayer, hsum, e]
  rw [hK]
  exact final_bound hT0 (by positivity) hK0 hI hJ₀le hyz hP1

/-- **The mean square on the Weil cone** (`k = 1`):
`∫_T^{2T} exp(2 Re log F_lam(½ + 1/log T + it)) dt ≤ C T (log T)^{e^ε κ²/(1−4ε)² + ε}`. -/
theorem exists_setIntegral_exp_two_mul_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in Ioc T (2 * T), Real.exp (2 * (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re) ≤
        C * T * Real.log T ^ (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2 + ε) := by
  obtain ⟨C, T₀, h⟩ := exists_setIntegral_exp_mul_le hW hA hκ hlam one_pos hε hε8
  refine ⟨C, T₀, fun T hT => ?_⟩
  have := h T hT
  simpa only [mul_one, one_pow, one_mul] using this

end RHTower.WeilSpectral
