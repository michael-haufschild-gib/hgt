import GaloisForLFunctions.ArithmeticPositiveDuality.ADiscreteBeurlingOneOff

/-!
# Quantile discretization of a prime density

A prime density is a measurable function `w ≥ 0` of the logarithmic coordinate `u = log p`,
zero below a cut `c > 0` and bounded below by a positive constant from the cut on, with a
Laplace transform right of `Re s = 1`. It is the density of a continuous system of primes; its
zeta function is `exp ∫ e^{−su} w(u) du`.

Let `W(x) = ∫_{(0,x]} w` and let `t_k` be the point with `W(t_k) = k + 1`. The discrete primes
`p_k = e^{t_k}` follow the continuous ones to within one: `#{k : t_k ≤ x} = ⌊W(x)⌋`. Hence, for
`Re s > 1`,

`Σ_k −log(1 − p_k^{−s}) = ∫ e^{−su} w(u) du + sΛ(s) + R(s)`,

with `Λ` the Laplace transform of the bounded function `N − W`, holomorphic on `Re s > 0`, and
`R` the prime-power remainder, holomorphic on `Re s > ½`. The Euler product of the discrete
primes is the zeta function of the density times a factor that is holomorphic and without zeros
on `Re s > ½`: discretization keeps every zero and pole right of the critical line.

The statements are those of the discrete Beurling one-off of `ArithmeticPositiveDuality`, for an
arbitrary density.

* `PrimeDensity`: the data.
* `PrimeDensity.atomCount_eq`, `PrimeDensity.abs_discrepancy_le`: the counting law.
* `PrimeDensity.discreteZeta_eq_tprod`: the Euler product.
* `PrimeDensity.discreteZeta_eq`, `PrimeDensity.differentiableOn_correction`: the comparison
  with the continuous zeta function.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

/-- A prime density in the logarithmic coordinate: zero below a cut, at least a positive
constant from the cut on, with a Laplace transform right of `Re s = 1`. -/
structure PrimeDensity where
  /-- The density. -/
  w : ℝ → ℝ
  /-- The cut below which there are no primes. -/
  cut : ℝ
  /-- A lower bound of the density from the cut on. -/
  floor : ℝ
  cut_pos : 0 < cut
  floor_pos : 0 < floor
  measurable_w : Measurable w
  zero_of_lt : ∀ u, u < cut → w u = 0
  floor_le : ∀ u, cut ≤ u → floor ≤ w u
  integrable : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun u => Real.exp (-(σ * u)) * w u) (Ioi 0)

namespace PrimeDensity

variable (P : PrimeDensity)

theorem pos_of_le (u : ℝ) (hu : P.cut ≤ u) : 0 < P.w u := P.floor_pos.trans_le (P.floor_le u hu)

theorem w_nonneg (u : ℝ) : 0 ≤ P.w u := by
  rcases lt_or_ge u P.cut with h | h
  · rw [P.zero_of_lt u h]
  · exact (P.pos_of_le u h).le

/-! ### The distribution function -/

/-- The distribution function `W(x) = ∫_{(0,x]} w` of the continuous primes. -/
def W (x : ℝ) : ℝ := distribution P.w x

/-- `w` on `(0, ∞)`, zero elsewhere. -/
def wt : ℝ → ℝ := (Ioi (0 : ℝ)).indicator P.w

theorem wt_nonneg (u : ℝ) : 0 ≤ P.wt u := Set.indicator_nonneg (fun u _ => P.w_nonneg u) u

theorem integrableOn_w_Ioc (b : ℝ) : IntegrableOn P.w (Ioc 0 b) := by
  have h := (P.integrable 2 (by norm_num)).mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) b ⊆ Ioi 0)
  have hIcc : IntegrableOn (fun u => Real.exp (-(2 * u)) * P.w u) (Icc 0 b) :=
    Iff.mpr integrableOn_Icc_iff_integrableOn_Ioc h
  have hc : ContinuousOn (fun u : ℝ => Real.exp (2 * u)) (Icc 0 b) := by fun_prop
  have h2 := (hIcc.mul_continuousOn hc isCompact_Icc).mono_set Ioc_subset_Icc_self
  refine h2.congr_fun (fun u _ => ?_) measurableSet_Ioc
  show Real.exp (-(2 * u)) * P.w u * Real.exp (2 * u) = P.w u
  rw [mul_right_comm, ← Real.exp_add]
  simp

theorem integrableOn_wt_Icc (b : ℝ) : IntegrableOn P.wt (Icc 0 b) := by
  refine Iff.mpr integrableOn_Icc_iff_integrableOn_Ioc ?_
  refine (P.integrableOn_w_Ioc b).congr_fun (fun u hu => ?_) measurableSet_Ioc
  simp [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu.1)]

theorem W_eq_intervalIntegral {x : ℝ} (hx : 0 ≤ x) : P.W x = ∫ u in (0 : ℝ)..x, P.wt u := by
  rw [intervalIntegral.integral_of_le hx, W, distribution]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  simp [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu.1)]

theorem W_of_nonpos {x : ℝ} (hx : x ≤ 0) : P.W x = 0 := by
  rw [W, distribution, Ioc_eq_empty (not_lt.mpr hx)]
  simp

theorem W_nonneg (x : ℝ) : 0 ≤ P.W x :=
  setIntegral_nonneg measurableSet_Ioc fun u _ => P.w_nonneg u

theorem intervalIntegrable_wt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable P.wt volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    ((P.integrableOn_wt_Icc b).mono_set (Icc_subset_Icc_left ha))

theorem continuousOn_W {M : ℝ} (hM : 0 ≤ M) : ContinuousOn P.W (Icc 0 M) := by
  have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := M)
    (f := P.wt) (by rw [uIcc_of_le hM]; exact P.integrableOn_wt_Icc M)
  rw [uIcc_of_le hM] at h
  exact h.congr fun x hx => P.W_eq_intervalIntegral hx.1

/-- The increment of `W` over an interval. -/
theorem W_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : P.W b - P.W a = ∫ u in a..b, P.wt u := by
  rw [P.W_eq_intervalIntegral ha, P.W_eq_intervalIntegral (ha.trans hab)]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (P.intervalIntegrable_wt le_rfl ha) (P.intervalIntegrable_wt ha hab)
  linarith only [hadd]

theorem W_le_W {a b : ℝ} (hab : a ≤ b) : P.W a ≤ P.W b := by
  rcases le_or_gt a 0 with ha | ha
  · rw [P.W_of_nonpos ha]
    exact P.W_nonneg b
  · have h := P.W_sub ha.le hab
    have hnn : 0 ≤ ∫ u in a..b, P.wt u :=
      intervalIntegral.integral_nonneg hab fun u _ => P.wt_nonneg u
    linarith only [h, hnn]

/-- `W` is strictly increasing from the cut on. -/
theorem W_lt {a b : ℝ} (ha : P.cut ≤ a) (hab : a < b) : P.W a < P.W b := by
  have ha0 : 0 ≤ a := P.cut_pos.le.trans ha
  have h := P.W_sub ha0 hab.le
  have hpos : 0 < ∫ u in a..b, P.wt u := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (P.intervalIntegrable_wt ha0 hab.le)
      (fun u hu => ?_) hab
    have hu0 : 0 < u := lt_of_le_of_lt ha0 hu.1
    simp only [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu0)]
    exact P.pos_of_le u (ha.trans hu.1.le)
  linarith only [h, hpos]

/-- There is no mass below the cut. -/
theorem W_of_le_cut {x : ℝ} (hx : x ≤ P.cut) : P.W x = 0 := by
  have hcut : P.W P.cut = 0 := by
    rw [W, distribution, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_eq_zero_of_forall_eq_zero fun u hu => P.zero_of_lt u hu.2
  exact le_antisymm (hcut ▸ P.W_le_W hx) (P.W_nonneg x)

theorem cut_lt_of_W_pos {x : ℝ} (hx : 0 < P.W x) : P.cut < x := by
  by_contra h
  rw [P.W_of_le_cut (not_lt.mp h)] at hx
  exact lt_irrefl _ hx

theorem W_le_exp {b : ℝ} (hb : 1 < b) (x : ℝ) :
    P.W x ≤ Real.exp (b * x) * ∫ u in Ioi (0 : ℝ), Real.exp (-(b * u)) * P.w u := by
  have hint := P.integrable b hb
  have hstep : P.W x ≤ ∫ u in Ioc 0 x, Real.exp (b * x) * (Real.exp (-(b * u)) * P.w u) := by
    refine setIntegral_mono_on (P.integrableOn_w_Ioc x)
      ((hint.mono_set Ioc_subset_Ioi_self).const_mul _) measurableSet_Ioc fun u hu => ?_
    have hw := P.w_nonneg u
    have he : 1 ≤ Real.exp (b * x) * Real.exp (-(b * u)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [hu.2])
    nlinarith
  rw [integral_const_mul] at hstep
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  refine setIntegral_mono_set hint ?_ (Eventually.of_forall Ioc_subset_Ioi_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
  exact mul_nonneg (Real.exp_pos _).le (P.w_nonneg u)

/-! ### The discrete primes -/

/-- The mass grows at least linearly beyond the cut. -/
theorem floor_mul_le_W {x : ℝ} (hx : P.cut ≤ x) : P.floor * (x - P.cut) ≤ P.W x := by
  have h := P.W_sub P.cut_pos.le hx
  rw [P.W_of_le_cut le_rfl, sub_zero] at h
  rw [h]
  have hmono := intervalIntegral.integral_mono_on hx
    (intervalIntegrable_const (c := P.floor) (μ := volume))
    (P.intervalIntegrable_wt P.cut_pos.le hx) fun u hu => by
      have hu0 : 0 < u := P.cut_pos.trans_le hu.1
      simp only [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu0)]
      exact P.floor_le u hu.1
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at hmono
  exact hmono

/-- The total mass is infinite. -/
theorem exists_le_W (B : ℝ) : ∃ x : ℝ, B ≤ P.W x := by
  refine ⟨P.cut + |B| / P.floor, ?_⟩
  have hx : P.cut ≤ P.cut + |B| / P.floor :=
    le_add_of_nonneg_right (div_nonneg (abs_nonneg B) P.floor_pos.le)
  have h := P.floor_mul_le_W hx
  rw [add_sub_cancel_left, mul_div_cancel₀ _ P.floor_pos.ne'] at h
  exact (le_abs_self B).trans h

theorem exists_atom (k : ℕ) : ∃ x, P.cut < x ∧ P.W x = k + 1 := by
  obtain ⟨M, hWM⟩ := P.exists_le_W ((k : ℝ) + 1)
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hM : 0 ≤ M := by
    by_contra h
    have h0 : P.W M = 0 := P.W_of_nonpos (not_le.mp h).le
    have h1 : (k : ℝ) + 1 ≤ P.W M := hWM
    rw [h0] at h1
    linarith only [h1, hk]
  obtain ⟨x, _, hWx⟩ := intermediate_value_Icc hM (P.continuousOn_W hM)
    ⟨by rw [P.W_of_nonpos le_rfl]; exact hk.le, hWM⟩
  exact ⟨x, P.cut_lt_of_W_pos (by rw [hWx]; exact hk), hWx⟩

/-- The `k`-th discrete prime in the logarithmic coordinate: `W(t_k) = k + 1`. -/
def atom (k : ℕ) : ℝ := (P.exists_atom k).choose

theorem cut_lt_atom (k : ℕ) : P.cut < P.atom k := (P.exists_atom k).choose_spec.1

theorem atom_pos (k : ℕ) : 0 < P.atom k := P.cut_pos.trans (P.cut_lt_atom k)

theorem W_atom (k : ℕ) : P.W (P.atom k) = k + 1 := (P.exists_atom k).choose_spec.2

theorem atom_le_iff (k : ℕ) (x : ℝ) : P.atom k ≤ x ↔ (k : ℝ) + 1 ≤ P.W x := by
  constructor
  · intro h
    rw [← P.W_atom k]
    exact P.W_le_W h
  · intro h
    by_contra hlt
    push Not at hlt
    have hpos : 0 < P.W x := lt_of_lt_of_le (by positivity) h
    have hlt' := P.W_lt (P.cut_lt_of_W_pos hpos).le hlt
    rw [P.W_atom] at hlt'
    linarith only [h, hlt']

theorem atom_strictMono : StrictMono P.atom := by
  intro j k hjk
  by_contra hle
  push Not at hle
  have h := P.W_le_W hle
  rw [P.W_atom, P.W_atom] at h
  have hjk' : (j : ℝ) < k := by exact_mod_cast hjk
  linarith only [h, hjk']

theorem atom_zero_le (k : ℕ) : P.atom 0 ≤ P.atom k := P.atom_strictMono.monotone (Nat.zero_le k)

theorem atom_le_iff_lt_floor (k : ℕ) (x : ℝ) : P.atom k ≤ x ↔ k < ⌊P.W x⌋₊ := by
  rw [P.atom_le_iff k x, Nat.lt_iff_add_one_le, Nat.le_floor_iff (P.W_nonneg x)]
  push_cast
  rfl

/-- **The discrete primes follow the continuous ones**: `#{k : t_k ≤ x} = ⌊W(x)⌋`. -/
theorem atomCount_eq (x : ℝ) : atomCount P.atom x = (⌊P.W x⌋₊ : ℝ) := by
  have hiff : ∀ k : ℕ, P.atom k ≤ x ↔ k < ⌊P.W x⌋₊ := fun k => P.atom_le_iff_lt_floor k x
  rw [atomCount, tsum_eq_sum (s := Finset.range ⌊P.W x⌋₊) fun k hk => by
    rw [if_neg (by rw [hiff]; simpa using hk)]]
  rw [Finset.sum_congr rfl fun k hk => if_pos ((hiff k).mpr (Finset.mem_range.mp hk))]
  simp

/-- `|N(x) − W(x)| ≤ 1`. -/
theorem abs_atomCount_sub_W_le (x : ℝ) : |atomCount P.atom x - P.W x| ≤ 1 := by
  rw [P.atomCount_eq, abs_le]
  have h1 := Nat.floor_le (P.W_nonneg x)
  have h2 := Nat.lt_floor_add_one (P.W x)
  constructor <;> linarith

/-- The discrete prime sum `Σ_k e^{-a t_k}` converges for `a > 1`. -/
theorem summable_exp_atom {a : ℝ} (ha : 1 < a) :
    Summable fun k => Real.exp (-(a * P.atom k)) := by
  set b := (1 + a) / 2 with hb
  have hb1 : 1 < b := by rw [hb]; linarith
  have hab : 1 < a / b := by rw [lt_div_iff₀ (by linarith)]; linarith
  set C := ∫ u in Ioi (0 : ℝ), Real.exp (-(b * u)) * P.w u with hC
  have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_Ioi fun u _ =>
    mul_nonneg (Real.exp_pos _).le (P.w_nonneg u)
  have hk : ∀ k : ℕ, Real.exp (-(b * P.atom k)) ≤ C / ((k : ℝ) + 1) := by
    intro k
    have h := P.W_le_exp hb1 (P.atom k)
    rw [P.W_atom] at h
    rw [le_div_iff₀ (by positivity)]
    have he : Real.exp (-(b * P.atom k)) * Real.exp (b * P.atom k) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(b * P.atom k))]
  have hsum : Summable fun k : ℕ => C ^ (a / b) * ((k : ℝ) + 1) ^ (-(a / b)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by linarith : -(a / b) < -1))
    refine (h.mul_left (C ^ (a / b))).congr fun k => ?_
    push_cast
    rfl
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hsum
  have hexp : Real.exp (-(a * P.atom k)) = Real.exp (-(b * P.atom k)) ^ (a / b) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [hexp]
  calc Real.exp (-(b * P.atom k)) ^ (a / b) ≤ (C / ((k : ℝ) + 1)) ^ (a / b) :=
        Real.rpow_le_rpow (Real.exp_pos _).le (hk k) (by positivity)
    _ = C ^ (a / b) * ((k : ℝ) + 1) ^ (-(a / b)) := by
        rw [Real.div_rpow hC0 (by positivity), Real.rpow_neg (by positivity), div_eq_mul_inv]

/-- The discrepancy `N − W` between the discrete and the continuous prime counts. -/
def discrepancy (x : ℝ) : ℝ := atomCount P.atom x - P.W x

theorem measurable_discrepancy : Measurable P.discrepancy := by
  have hW : Monotone P.W := fun a b h => P.W_le_W h
  have hF : Monotone fun x => (⌊P.W x⌋₊ : ℝ) := fun a b h =>
    Nat.cast_le.mpr (Nat.floor_le_floor (P.W_le_W h))
  have heq : P.discrepancy = fun x => (⌊P.W x⌋₊ : ℝ) - P.W x := by
    funext x
    rw [discrepancy, P.atomCount_eq]
  rw [heq]
  exact hF.measurable.sub hW.measurable

theorem abs_discrepancy_le (x : ℝ) : |P.discrepancy x| ≤ 1 := P.abs_atomCount_sub_W_le x

/-! ### The Euler product and its comparison with the continuous zeta function -/

/-- The Euler logarithm `Σ_k −log(1 − p_k^{-s})` of the discrete primes `p_k = e^{t_k}`. -/
def eulerLog (s : ℂ) : ℂ := ∑' k, -Complex.log (1 - cexp (-(s * P.atom k)))

/-- The zeta function of the discrete primes, `exp` of the Euler logarithm. -/
def discreteZeta (s : ℂ) : ℂ := cexp (P.eulerLog s)

/-- **It is the Euler product** `Π_k (1 − p_k^{-s})^{-1}` on `Re s > 1`. -/
theorem discreteZeta_eq_tprod {s : ℂ} (hs : 1 < s.re) :
    P.discreteZeta s = ∏' k, (1 - cexp (-(s * P.atom k)))⁻¹ := by
  have hre : ∀ k, 0 < (1 - cexp (-(s * P.atom k))).re := by
    intro k
    have h1 : (cexp (-(s * P.atom k))).re ≤ ‖cexp (-(s * P.atom k))‖ := Complex.re_le_norm _
    have h2 : ‖cexp (-(s * P.atom k))‖ < 1 := by
      rw [norm_cexp_neg_mul, Real.exp_lt_one_iff]
      have := P.atom_pos k
      nlinarith
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hlog : ∀ k, Complex.log (1 - cexp (-(s * P.atom k)))⁻¹ =
      -Complex.log (1 - cexp (-(s * P.atom k))) := by
    intro k
    refine Complex.log_inv _ fun h => ?_
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith [hre k]
  have hne : ∀ k, (1 - cexp (-(s * P.atom k)))⁻¹ ≠ 0 := by
    intro k
    refine inv_ne_zero fun h => ?_
    have := hre k
    rw [h] at this
    simp at this
  obtain ⟨h1, h2⟩ := summable_neg_log P.atom_pos P.atom_zero_le
    (fun a ha => P.summable_exp_atom ha) hs
  have hsum : Summable fun k => Complex.log (1 - cexp (-(s * P.atom k)))⁻¹ := by
    simp_rw [hlog]
    exact (h1.add h2).congr fun k => by ring
  rw [discreteZeta, eulerLog, ← Complex.cexp_tsum_eq_tprod hne hsum]
  simp_rw [hlog]

/-- The correction between the discrete and the continuous zeta function: `sΛ(s) + R(s)`,
with `Λ` the Laplace transform of `N − W` and `R` the prime-power remainder. -/
def correction (s : ℂ) : ℂ :=
  s * boundedLaplace P.discrepancy s + primePowerRemainder P.atom s

/-- **The correction is holomorphic on `Re s > ½`.** -/
theorem differentiableOn_correction :
    DifferentiableOn ℂ P.correction {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hs' : 1 / 2 < s.re := hs
  have hΛ : DifferentiableAt ℂ (boundedLaplace P.discrepancy) s :=
    (differentiableOn_boundedLaplace P.measurable_discrepancy
      P.abs_discrepancy_le).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by show 0 < s.re; linarith only [hs']))
  have hR : DifferentiableAt ℂ (primePowerRemainder P.atom) s :=
    (differentiableOn_primePowerRemainder P.atom_pos P.atom_zero_le
      (fun a ha => P.summable_exp_atom ha)).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs')
  exact ((differentiableAt_id.mul hΛ).add hR).differentiableWithinAt

/-- **The Euler logarithm of the discrete primes** is the Laplace transform of the density plus
the correction, on `Re s > 1`. -/
theorem eulerLog_eq {s : ℂ} (hs : 1 < s.re) :
    P.eulerLog s = (∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (P.w u : ℂ)) + P.correction s := by
  have hs0 : 0 < s.re := by linarith only [hs]
  have hsplit := tsum_neg_log_eq P.atom_pos P.atom_zero_le (fun a ha => P.summable_exp_atom ha) hs
  have hdisc := tsum_cexp_atoms P.atom_pos hs0 (P.summable_exp_atom hs)
  have hint : IntegrableOn (fun u => Real.exp (-(s.re * u)) * P.w u) (Ioi 0) :=
    P.integrable s.re hs
  obtain ⟨hWint, hcont⟩ := integral_cexp_density P.measurable_w (fun u _ => P.w_nonneg u)
    hs0 hint
  have hEint : IntegrableOn (fun x : ℝ => cexp (-(s * x)) * (P.discrepancy x : ℂ)) (Ioi 0) := by
    have hb : IntegrableOn (fun x : ℝ => Real.exp (-s.re * x)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine hb.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((by fun_prop : Continuous fun x : ℝ => cexp (-(s * x))).measurable.mul
        (Complex.measurable_ofReal.comp P.measurable_discrepancy)).aestronglyMeasurable
    · rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs]
      have := P.abs_discrepancy_le x
      have he := Real.exp_pos (-(s.re * x))
      rw [show -s.re * x = -(s.re * x) by ring]
      nlinarith
  have hN : ∫ x in Ioi (0 : ℝ), cexp (-(s * x)) * (atomCount P.atom x : ℂ) =
      boundedLaplace P.discrepancy s +
        ∫ x in Ioi (0 : ℝ), cexp (-(s * x)) * (distribution P.w x : ℂ) := by
    rw [boundedLaplace, ← integral_add hEint hWint]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [discrepancy, W]
    push_cast
    ring
  rw [eulerLog, hsplit, hdisc, hN, hcont, correction]
  ring

/-- **The discrete zeta function is the continuous one times `exp` of the correction.** -/
theorem discreteZeta_eq {s : ℂ} (hs : 1 < s.re) :
    P.discreteZeta s =
      cexp (∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (P.w u : ℂ)) * cexp (P.correction s) := by
  rw [discreteZeta, P.eulerLog_eq hs, Complex.exp_add]

end PrimeDensity

end GaloisForLFunctions.FloorFreeArithmetic
