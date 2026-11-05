import GaloisForLFunctions.ArithmeticProduction.TheMollifierDefectIsASawtoothForm
import GaloisForLFunctions.ArithmeticProduction.TypeIInformationIsParityBlind
import GaloisForLFunctions.BiScaleUncertainty.BandSpectrumZeroWidthLaw
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# The linear Möbius mollifier is the Chebyshev error

On `1 ≤ x ≤ y` the sawtooth function of a mollifier supported on `[1, y]` is computed by the hyperbola identity
`Σ_d a_d ⌊x/d⌋ = Σ_{n ≤ x} Σ_{d ∣ n} a_d` (`sum_mul_nat_div`).

* **Sharp Möbius mollifier** `a_d = μ(d)`.  The inner sum is `1_{n = 1}`, so `F(x) = x m(y)` with `m(y) = Σ_{d ≤ y} μ(d)/d`
  (`sawtoothDefect_sharp`), and `y m(y)² ≤ defect` (`mul_sq_le_sharpDefect`).  Because `M(x) = Ω(√x)`, this quantity does not tend to `0`
  (`exists_frequently_le_sharpDefect`): sharp truncation of `1/ζ` never closes the defect, under any hypothesis on the zeros.
* **Linear Möbius mollifier** `a_d = μ(d)(1 − log d/log y)`.  The inner sum is `1_{n = 1} + Λ(n)/log y`
  (`sum_divisors_linearCoeff`), so `F(x) = x D(1) − ψ(x)/log y` (`sawtoothDefect_linear`).  With
  `κ_y = D(1) log y − 1` and `Ẽ(u) = e^{−u/2}(ψ(e^u) − e^u)`,

    `∫_0^{log y} (Ẽ(u) − κ_y e^{u/2})² du ≤ (log y)² · defect`
    (`integral_linearBand_le`).

  So the Cauchy-weighted mollified second moment contains Cramér's integral divided by `log²y`, up to the one number `κ_y`.
* **From the mollifier to the zeros.**  Dyadic comparison eliminates `κ_y` (`band_of_dyadic`, which uses only the prime number
  theorem), so a defect growth rate `y^{2β}`, `β < ½`, confines every zero to `Re ρ ≤ ½ + β`
  (`xiZeroHalfPlaneBound_of_linearDefectRate`).  A bounded linear defect already gives RH
  (`riemannHypothesis_of_linearDefect_bounded`), which is stronger than the classical `d_N → 0`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace GaloisForLFunctions.ArithmeticProduction

open BiScaleUncertainty.ChebyshevGauge BiScaleUncertainty.SignedPrimePolar

/-! ### The hyperbola identity -/

/-- **Hyperbola identity.**  For `X ≤ y`, `Σ_{d ≤ y} a_d ⌊X/d⌋ = Σ_{n ≤ X} Σ_{d ∣ n} a_d`. -/
theorem sum_mul_nat_div (a : ℕ → ℝ) {X y : ℕ} (hXy : X ≤ y) :
    ∑ d ∈ Finset.Icc 1 y, a d * ((X / d : ℕ) : ℝ) =
      ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, a d := by
  have h1 : ∀ d ∈ Finset.Icc 1 y, ((X / d : ℕ) : ℝ) =
      ∑ n ∈ Finset.Icc 1 X, (if d ∣ n then (1 : ℝ) else 0) := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    rw [sum_Icc_ite_dvd hd0 X (fun _ => 1)]
    simp
  rw [Finset.sum_congr rfl fun d hd => by rw [h1 d hd]]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
  have hfil : (Finset.Icc 1 y).filter (· ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
    · rintro ⟨hd, -⟩
      have hle := Nat.le_of_dvd hn1 hd
      have hpos := Nat.pos_of_dvd_of_pos hd hn1
      exact ⟨⟨hpos, by omega⟩, hd⟩
  rw [← hfil, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

/-- The fractional sum is the linear term minus the hyperbola sum. -/
theorem sum_mul_fract_eq (a : ℕ → ℝ) (y : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∑ d ∈ Finset.Icc 1 y, a d * Int.fract (x / d) =
      x * valueAtOne (Finset.Icc 1 y) a -
        ∑ d ∈ Finset.Icc 1 y, a d * ((⌊x⌋₊ / d : ℕ) : ℝ) := by
  unfold valueAtOne
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hfloor : ((⌊x / d⌋ : ℤ) : ℝ) = ((⌊x⌋₊ / d : ℕ) : ℝ) := by
    rw [← natCast_floor_eq_intCast_floor (div_nonneg hx hd0), Nat.floor_div_natCast]
  rw [Int.fract, hfloor]
  ring

/-- The sawtooth function on `[1, y]`. -/
theorem sawtoothDefect_band (a : ℕ → ℝ) {y : ℕ} {x : ℝ} (hx1 : 1 ≤ x) (hxy : x ≤ y) :
    sawtoothDefect (Finset.Icc 1 y) a x =
      1 + x * valueAtOne (Finset.Icc 1 y) a -
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ d ∈ n.divisors, a d := by
  unfold sawtoothDefect
  rw [if_pos hx1, sum_mul_fract_eq a y (by linarith),
    sum_mul_nat_div a (Nat.floor_le_of_le hxy)]
  ring

/-! ### The sharp Möbius mollifier -/

/-- The sharp Möbius coefficients. -/
def sharpCoeff (d : ℕ) : ℝ := ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- `m(y) = Σ_{d ≤ y} μ(d)/d`. -/
def harmonicMoebius (y : ℕ) : ℝ := valueAtOne (Finset.Icc 1 y) sharpCoeff

theorem sum_divisors_sharpCoeff (n : ℕ) :
    ∑ d ∈ n.divisors, sharpCoeff d = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← h]
  rfl

theorem sum_Icc_ite_eq_one {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ Finset.Icc 1 X, (if n = 1 then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_ite_eq']
  simp [hX]

/-- **`F(x) = x m(y)` on `[1, y]`.** -/
theorem sawtoothDefect_sharp {y : ℕ} {x : ℝ} (hx1 : 1 ≤ x) (hxy : x ≤ y) :
    sawtoothDefect (Finset.Icc 1 y) sharpCoeff x = x * harmonicMoebius y := by
  rw [sawtoothDefect_band _ hx1 hxy]
  simp_rw [sum_divisors_sharpCoeff]
  rw [sum_Icc_ite_eq_one (Nat.one_le_floor_iff x |>.mpr hx1)]
  simp only [harmonicMoebius]
  ring

private theorem integral_exp_Icc {a b : ℝ} (hab : a ≤ b) :
    ∫ u in Icc a b, Real.exp u = Real.exp b - Real.exp a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_exp]

/-- **The sharp mollifier pays `y m(y)²`.** -/
theorem mul_sq_le_sharpDefect {y : ℕ} (hy : 1 ≤ y) :
    (y : ℝ) * harmonicMoebius y ^ 2 ≤ mollifierDefect (Finset.Icc 1 y) sharpCoeff := by
  have hS : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hband := mollifierDefect_ge_band hS sharpCoeff (L := Real.log y)
    (f := fun u => Real.exp u * harmonicMoebius y) (fun u hu => by
      refine sawtoothDefect_sharp (Real.one_le_exp hu.1) ?_
      calc Real.exp u ≤ Real.exp (Real.log y) := Real.exp_le_exp.mpr hu.2
        _ = y := Real.exp_log hy0)
  have hint : ∫ u in Icc 0 (Real.log y), Real.exp (-u) * (Real.exp u * harmonicMoebius y) ^ 2 =
      harmonicMoebius y ^ 2 * ((y : ℝ) - 1) := by
    have hpt : ∀ u ∈ Icc 0 (Real.log y),
        Real.exp (-u) * (Real.exp u * harmonicMoebius y) ^ 2 =
          harmonicMoebius y ^ 2 * Real.exp u := by
      intro u _
      have h1 : Real.exp (-u) * Real.exp u = 1 := by
        rw [← Real.exp_add]
        simp
      calc Real.exp (-u) * (Real.exp u * harmonicMoebius y) ^ 2
          = (Real.exp (-u) * Real.exp u) * (Real.exp u * harmonicMoebius y ^ 2) := by ring
        _ = _ := by rw [h1]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hpt, integral_const_mul,
      integral_exp_Icc (Real.log_nonneg hy1), Real.exp_log hy0, Real.exp_zero]
  rw [hint] at hband
  have hval : valueAtOne (Finset.Icc 1 y) sharpCoeff = harmonicMoebius y := rfl
  rw [hval] at hband
  nlinarith

/-- Abel summation: `M(N) = N m(N) − Σ_{k < N} m(k)`. -/
theorem mertens_eq_abel (N : ℕ) :
    _root_.RHTower.mertensFunctionReal N =
      (N : ℝ) * harmonicMoebius N - ∑ k ∈ Finset.range N, harmonicMoebius k := by
  induction N with
  | zero => simp [_root_.RHTower.mertensFunctionReal, harmonicMoebius, valueAtOne]
  | succ N ih =>
    have hM : _root_.RHTower.mertensFunctionReal ((N + 1 : ℕ) : ℝ) =
        _root_.RHTower.mertensFunctionReal (N : ℝ) + sharpCoeff (N + 1) := by
      simp only [_root_.RHTower.mertensFunctionReal, Nat.floor_natCast]
      rw [Finset.sum_Icc_succ_top (by omega)]
      rfl
    have hm : harmonicMoebius (N + 1) = harmonicMoebius N + sharpCoeff (N + 1) / ((N + 1 : ℕ) : ℝ) := by
      simp only [harmonicMoebius, valueAtOne]
      rw [Finset.sum_Icc_succ_top (by omega)]
    have hne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hc : ((N + 1 : ℕ) : ℝ) * (sharpCoeff (N + 1) / ((N + 1 : ℕ) : ℝ)) = sharpCoeff (N + 1) :=
      mul_div_cancel₀ _ hne
    rw [hM, ih, Finset.sum_range_succ, hm, mul_add, hc]
    push_cast
    ring

/-- **The sharp mollifier never closes.**  There is `c > 0` with `c ≤ y m(y)²` for arbitrarily large `y`: the sharp Möbius
truncation has defect `≥ c` infinitely often, whatever the zeros do. -/
theorem exists_frequently_le_sharpDefect :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ y : ℕ in atTop,
      c ≤ (y : ℝ) * harmonicMoebius y ^ 2 ∧
        c ≤ mollifierDefect (Finset.Icc 1 y) sharpCoeff := by
  obtain ⟨c₀, hc₀, hup, -⟩ := _root_.RHTower.mertens_omega_pm_sqrt
  set ε : ℝ := c₀ / 8 with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨ε ^ 2, by positivity, ?_⟩
  by_contra hcon
  rw [not_frequently] at hcon
  have hsmall : ∀ᶠ y : ℕ in atTop, (y : ℝ) * harmonicMoebius y ^ 2 < ε ^ 2 := by
    filter_upwards [hcon, eventually_ge_atTop 1] with y hy hy1
    by_contra hge
    exact hy ⟨not_lt.mp hge, (not_lt.mp hge).trans (mul_sq_le_sharpDefect hy1)⟩
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp (hsmall.and (eventually_ge_atTop 1))
  have hm : ∀ k : ℕ, y₀ ≤ k → |harmonicMoebius k| ≤ ε * (1 / √(k : ℝ)) := by
    intro k hk
    obtain ⟨h1, h2⟩ := hy₀ k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast h2
    have hs : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk0
    have h3 : (√(k : ℝ) * |harmonicMoebius k|) ^ 2 < ε ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hk0.le, sq_abs]
      exact h1
    have h4 : √(k : ℝ) * |harmonicMoebius k| ≤ ε := (abs_lt_of_sq_lt_sq' h3 hε0.le).2.le
    rw [mul_one_div, le_div_iff₀ hs]
    linarith
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = ∑ k ∈ Finset.range y₀, |harmonicMoebius k| := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : ∀ N : ℕ, y₀ ≤ N → |_root_.RHTower.mertensFunctionReal N| ≤ 3 * ε * √(N : ℝ) + C₀ := by
    intro N hN
    rw [mertens_eq_abel]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h1 : (N : ℝ) * |harmonicMoebius N| ≤ ε * √(N : ℝ) := by
      rcases Nat.eq_zero_or_pos N with rfl | hNpos
      · simp
      have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hs : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hNp
      have h2 := hm N hN
      calc (N : ℝ) * |harmonicMoebius N| ≤ N * (ε * (1 / √(N : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 hN0
        _ = ε * √(N : ℝ) := by
          have : (N : ℝ) = √(N : ℝ) * √(N : ℝ) := (Real.mul_self_sqrt hN0).symm
          rw [this]
          field_simp
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hN0]
    have hsplit : Finset.range N = Finset.range y₀ ∪ Finset.Ico y₀ N := by
      ext k
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range y₀) (Finset.Ico y₀ N) := by
      rw [Finset.disjoint_left]
      intro k h1 h2
      have := Finset.mem_range.mp h1
      have := (Finset.mem_Ico.mp h2).1
      omega
    have h2 : ∑ k ∈ Finset.Ico y₀ N, |harmonicMoebius k| ≤ ε * (2 * √(N : ℝ)) := by
      refine (Finset.sum_le_sum fun k hk => hm k (Finset.mem_Ico.mp hk).1).trans ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hε0.le
      refine le_trans ?_ (ArithmeticOfSquareRootPrecision.sum_inv_sqrt_le N)
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro k hk
      obtain ⟨h3, h4⟩ := Finset.mem_Ico.mp hk
      have hy1 := (hy₀ y₀ le_rfl).2
      exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    have h3 : |∑ k ∈ Finset.range N, harmonicMoebius k| ≤ C₀ + ε * (2 * √(N : ℝ)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hsplit, Finset.sum_union hdisj, ← hC₀]
      linarith
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hN0]
    linarith
  -- contradiction with `M(x) > c₀ √x`
  have hevent : ∀ᶠ x : ℝ in atTop, (y₀ : ℝ) ≤ x ∧ C₀ < (c₀ / 2) * √x := by
    refine (eventually_ge_atTop (y₀ : ℝ)).and ?_
    have hT : Tendsto (fun x : ℝ => (c₀ / 2) * √x) atTop atTop :=
      Real.tendsto_sqrt_atTop.const_mul_atTop (by positivity)
    exact hT.eventually_gt_atTop C₀
  obtain ⟨x, hx1, hx2, hx3⟩ := (hup.and_eventually hevent).exists
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx2
  have hfl : y₀ ≤ ⌊x⌋₊ := Nat.le_floor hx2
  have hMx : _root_.RHTower.mertensFunctionReal x =
      _root_.RHTower.mertensFunctionReal (⌊x⌋₊ : ℝ) := by
    simp [_root_.RHTower.mertensFunctionReal]
  have hbound := hM _ hfl
  rw [← hMx] at hbound
  have hsqrt : √((⌊x⌋₊ : ℝ)) ≤ √x := Real.sqrt_le_sqrt (Nat.floor_le hx0)
  have h1 := le_abs_self (_root_.RHTower.mertensFunctionReal x)
  have hsq0 := Real.sqrt_nonneg x
  rw [hε] at hbound
  nlinarith

/-! ### The linear Möbius mollifier -/

/-- The linear Möbius coefficients `μ(d)(1 − log d/log y)`. -/
def linearCoeff (y d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (1 - Real.log d / Real.log y)

/-- **The coefficients of `ζM` below `y`.** -/
theorem sum_divisors_linearCoeff (y n : ℕ) :
    ∑ d ∈ n.divisors, linearCoeff y d =
      (if n = 1 then 1 else 0) + (vonMangoldt n : ℝ) / Real.log y := by
  unfold linearCoeff
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  have h1 := sum_divisors_sharpCoeff n
  have h2 := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  have h3 : ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (Real.log d / Real.log y) = -(vonMangoldt n : ℝ) / Real.log y := by
    rw [← h2, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ArithmeticFunction.log_apply]
    ring
  rw [h3]
  have h4 : ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) =
      if n = 1 then 1 else 0 := h1
  rw [h4]
  ring

/-- `Σ_{n ≤ x} Λ(n) = ψ(x)`. -/
theorem sum_Icc_vonMangoldt_eq_psi (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (vonMangoldt n : ℝ) = Chebyshev.psi x := by
  have hIoc : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [Chebyshev.psi, hIoc]

/-- **`F(x) = x D(1) − ψ(x)/log y` on `[1, y]`.** -/
theorem sawtoothDefect_linear {y : ℕ} {x : ℝ} (hx1 : 1 ≤ x) (hxy : x ≤ y) :
    sawtoothDefect (Finset.Icc 1 y) (linearCoeff y) x =
      x * valueAtOne (Finset.Icc 1 y) (linearCoeff y) - Chebyshev.psi x / Real.log y := by
  rw [sawtoothDefect_band _ hx1 hxy]
  simp_rw [sum_divisors_linearCoeff]
  rw [Finset.sum_add_distrib, sum_Icc_ite_eq_one (Nat.one_le_floor_iff x |>.mpr hx1),
    ← Finset.sum_div, sum_Icc_vonMangoldt_eq_psi]
  ring

/-- The defect of the linear Möbius mollifier of length `y`. -/
def linearDefect (y : ℕ) : ℝ := mollifierDefect (Finset.Icc 1 y) (linearCoeff y)

/-- The one number separating the band from the Chebyshev error: `κ_y = D(1) log y − 1`. -/
def linearOffset (y : ℕ) : ℝ := valueAtOne (Finset.Icc 1 y) (linearCoeff y) * Real.log y - 1

/-- **The Cramér integral inside the defect.** -/
theorem integral_linearBand_le {y : ℕ} (hy : 2 ≤ y) :
    ∫ u in Icc 0 (Real.log y), (normalizedLogError u - linearOffset y * Real.exp (u / 2)) ^ 2 ≤
      Real.log y ^ 2 * linearDefect y := by
  have hS : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hy0 : (0 : ℝ) < y := by
    have : 0 < y := by omega
    exact_mod_cast this
  have hlog : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hband := mollifierDefect_ge_band hS (linearCoeff y) (L := Real.log y)
    (f := fun u => Real.exp u * valueAtOne (Finset.Icc 1 y) (linearCoeff y) -
      Chebyshev.psi (Real.exp u) / Real.log y) (fun u hu => by
      refine sawtoothDefect_linear (Real.one_le_exp hu.1) ?_
      calc Real.exp u ≤ Real.exp (Real.log y) := Real.exp_le_exp.mpr hu.2
        _ = y := Real.exp_log hy0)
  have hpt : ∀ u : ℝ, Real.exp (-u) * (Real.exp u * valueAtOne (Finset.Icc 1 y) (linearCoeff y) -
      Chebyshev.psi (Real.exp u) / Real.log y) ^ 2 =
      (Real.log y ^ 2)⁻¹ * (normalizedLogError u - linearOffset y * Real.exp (u / 2)) ^ 2 := by
    intro u
    have hE : Real.exp (-u) = Real.exp (-u / 2) * Real.exp (-u / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hE2 : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hinner : Real.exp (-u / 2) * (Real.exp u * valueAtOne (Finset.Icc 1 y) (linearCoeff y) -
        Chebyshev.psi (Real.exp u) / Real.log y) =
        -(Real.log y)⁻¹ * (normalizedLogError u - linearOffset y * Real.exp (u / 2)) := by
      have hne := hlog.ne'
      rw [← hE2]
      unfold normalizedLogError logError linearOffset
      field_simp
      ring
    calc Real.exp (-u) * (Real.exp u * valueAtOne (Finset.Icc 1 y) (linearCoeff y) -
          Chebyshev.psi (Real.exp u) / Real.log y) ^ 2
        = (Real.exp (-u / 2) * (Real.exp u * valueAtOne (Finset.Icc 1 y) (linearCoeff y) -
            Chebyshev.psi (Real.exp u) / Real.log y)) ^ 2 := by rw [hE]; ring
      _ = _ := by
        rw [hinner, mul_pow, neg_sq, inv_pow]
  have hint : ∫ u in Icc 0 (Real.log y), Real.exp (-u) *
      (Real.exp u * valueAtOne (Finset.Icc 1 y) (linearCoeff y) -
        Chebyshev.psi (Real.exp u) / Real.log y) ^ 2 =
      (Real.log y ^ 2)⁻¹ *
        ∫ u in Icc 0 (Real.log y), (normalizedLogError u - linearOffset y * Real.exp (u / 2)) ^ 2 := by
    simp_rw [hpt]
    rw [integral_const_mul]
  rw [hint] at hband
  have hval : mollifierDefect (Finset.Icc 1 y) (linearCoeff y) = linearDefect y := rfl
  rw [hval] at hband
  have hsq : 0 ≤ valueAtOne (Finset.Icc 1 y) (linearCoeff y) ^ 2 := sq_nonneg _
  have hlog2 : 0 < Real.log y ^ 2 := by positivity
  have h1 : (Real.log y ^ 2)⁻¹ *
      ∫ u in Icc 0 (Real.log y), (normalizedLogError u - linearOffset y * Real.exp (u / 2)) ^ 2 ≤
      linearDefect y := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hlog2.le
  rwa [← mul_assoc, mul_inv_cancel₀ hlog2.ne', one_mul] at h2

/-! ### Dyadic elimination of the offset -/

/-- **Dyadic elimination.**  If `E(u) = o(e^{u/2})` and for each `k` the error `E − κ_k e^{u/2}` has mean square `≤ C q^k` on
`[0, k log 2]`, `1 ≤ q < 2`, then `κ_k` is geometrically small and `E` itself has mean square `≤ C' q^k`. -/
theorem band_of_dyadic {E : ℝ → ℝ} (hEm : Measurable E)
    (hEi : ∀ L : ℝ, IntegrableOn (fun u => E u ^ 2) (Icc 0 L))
    (hPNT : ∀ ε : ℝ, 0 < ε → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → |E u| ≤ ε * Real.exp (u / 2))
    {κ : ℕ → ℝ} {C q : ℝ} (hC : 0 ≤ C) (hq1 : 1 ≤ q) (hq2 : q < 2)
    (hI : ∀ k : ℕ, 1 ≤ k →
      ∫ u in Icc 0 ((k : ℝ) * Real.log 2), (E u - κ k * Real.exp (u / 2)) ^ 2 ≤ C * q ^ k) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ k : ℕ, 1 ≤ k →
      ∫ u in Icc 0 ((k : ℝ) * Real.log 2), E u ^ 2 ≤ C' * q ^ k := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexpk : ∀ k : ℕ, Real.exp ((k : ℝ) * Real.log 2) = 2 ^ k := by
    intro k
    rw [mul_comm, Real.exp_mul, Real.exp_log two_pos, Real.rpow_natCast]
  have hexpint : ∀ L : ℝ, IntegrableOn (fun u => Real.exp u) (Icc 0 L) := fun L =>
    Real.continuous_exp.continuousOn.integrableOn_compact isCompact_Icc
  have hAint : ∀ (c L : ℝ), IntegrableOn (fun u => (E u - c * Real.exp (u / 2)) ^ 2) (Icc 0 L) := by
    intro c L
    have hm : AEStronglyMeasurable (fun u => (E u - c * Real.exp (u / 2)) ^ 2)
        (volume.restrict (Icc 0 L)) := by
      have : Measurable fun u => (E u - c * Real.exp (u / 2)) ^ 2 := by fun_prop
      exact this.aestronglyMeasurable
    refine Integrable.mono' (((hEi L).const_mul 2).add ((hexpint L).const_mul (2 * c ^ 2))) hm
      (Filter.Eventually.of_forall fun u => ?_)
    have hexp2 : Real.exp (u / 2) ^ 2 = Real.exp u := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    show (E u - c * Real.exp (u / 2)) ^ 2 ≤ 2 * E u ^ 2 + 2 * c ^ 2 * Real.exp u
    rw [← hexp2]
    nlinarith [sq_nonneg (E u + c * Real.exp (u / 2))]
  have hIinner : ∀ k : ℕ, ∫ u in Icc 0 ((k : ℝ) * Real.log 2), Real.exp u = (2 : ℝ) ^ k - 1 := by
    intro k
    rw [integral_exp_Icc (by positivity), hexpk, Real.exp_zero]
  have h2k : ∀ k : ℕ, 1 ≤ k → (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k - 1 := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]
    linarith
  set r : ℝ := √(q / 2) with hr
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr1 : r < 1 := by
    rw [hr, Real.sqrt_lt' one_pos]
    norm_num
    linarith
  have hr2 : r ^ 2 = q / 2 := Real.sq_sqrt (by positivity)
  -- Step 1: consecutive offsets
  have hstep : ∀ k : ℕ, 1 ≤ k → (κ (k + 1) - κ k) ^ 2 ≤ 12 * C * (q / 2) ^ k := by
    intro k hk
    set Δ := κ (k + 1) - κ k with hΔ
    have hmono : ∫ u in Icc 0 ((k : ℝ) * Real.log 2), (E u - κ (k + 1) * Real.exp (u / 2)) ^ 2 ≤
        ∫ u in Icc 0 (((k + 1 : ℕ) : ℝ) * Real.log 2),
          (E u - κ (k + 1) * Real.exp (u / 2)) ^ 2 := by
      refine setIntegral_mono_set (hAint _ _) (Filter.Eventually.of_forall fun u => sq_nonneg _) ?_
      refine (Icc_subset_Icc_right ?_).eventuallyLE
      push_cast
      nlinarith
    have hpt : ∀ u ∈ Icc 0 ((k : ℝ) * Real.log 2), Δ ^ 2 * Real.exp u ≤
        2 * (E u - κ k * Real.exp (u / 2)) ^ 2 + 2 * (E u - κ (k + 1) * Real.exp (u / 2)) ^ 2 := by
      intro u _
      have hexp2 : Real.exp (u / 2) ^ 2 = Real.exp u := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [← hexp2, hΔ]
      nlinarith [sq_nonneg ((E u - κ k * Real.exp (u / 2)) + (E u - κ (k + 1) * Real.exp (u / 2)))]
    have hmain : ∫ u in Icc 0 ((k : ℝ) * Real.log 2), Δ ^ 2 * Real.exp u ≤
        ∫ u in Icc 0 ((k : ℝ) * Real.log 2), (2 * (E u - κ k * Real.exp (u / 2)) ^ 2 +
          2 * (E u - κ (k + 1) * Real.exp (u / 2)) ^ 2) :=
      setIntegral_mono_on ((hexpint _).const_mul (Δ ^ 2))
        (((hAint (κ k) _).const_mul 2).add ((hAint (κ (k + 1)) _).const_mul 2))
        measurableSet_Icc hpt
    rw [integral_const_mul, hIinner, integral_add ((hAint _ _).const_mul 2) ((hAint _ _).const_mul 2),
      integral_const_mul, integral_const_mul] at hmain
    have h1 := hI k hk
    have h2 := hI (k + 1) (by omega)
    have h3 := h2k k hk
    have hqk : 0 ≤ q ^ k := by positivity
    have hsucc : q ^ (k + 1) ≤ 2 * q ^ k := by
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_right hq2.le hqk
    have hsucc' := mul_le_mul_of_nonneg_left hsucc hC
    have hbound : Δ ^ 2 * ((2 : ℝ) ^ k - 1) ≤ 6 * C * q ^ k := by
      linarith
    have h4 : Δ ^ 2 * (2 : ℝ) ^ (k - 1) ≤ 6 * C * q ^ k :=
      (mul_le_mul_of_nonneg_left h3 (sq_nonneg _)).trans hbound
    have h2pos : (0 : ℝ) < 2 ^ k := by positivity
    have h2rel : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      ring
    rw [div_pow, mul_div_assoc', le_div_iff₀ h2pos, h2rel]
    linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = √(12 * C) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hK2 : K ^ 2 = 12 * C := by
    rw [hKdef]
    exact Real.sq_sqrt (by positivity)
  have hdist : ∀ n : ℕ, dist (κ (n + 1)) (κ (n + 1 + 1)) ≤ K * r ^ n := by
    intro n
    rw [Real.dist_eq, abs_sub_comm]
    have h1 := hstep (n + 1) (by omega)
    have h2 : (q / 2) ^ (n + 1) = (r ^ (n + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, hr2]
    have h3 : (κ (n + 1 + 1) - κ (n + 1)) ^ 2 ≤ (K * r ^ (n + 1)) ^ 2 := by
      rw [mul_pow, hK2, ← h2]
      exact h1
    have h4 : |κ (n + 1 + 1) - κ (n + 1)| ≤ K * r ^ (n + 1) :=
      abs_le_of_sq_le_sq h3 (by positivity)
    refine h4.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) hr1.le
  have hcauchy : CauchySeq fun n => κ (n + 1) := cauchySeq_of_le_geometric r K hr1 hdist
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- Step 2: the limit is zero
  have hbound2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      κ (n + 1) ^ 2 ≤ 4 * C * (q / 2) ^ (n + 1) + 2 * ε ^ 2 := by
    intro ε hε
    obtain ⟨u₀, hu₀⟩ := hPNT ε hε
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge (u₀ / Real.log 2)
    refine ⟨n₀, fun n hn => ?_⟩
    set k := n + 1 with hk
    have hlow : u₀ ≤ (n : ℝ) * Real.log 2 := by
      have h1 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
      have h2 := (div_le_iff₀ hlog2).mp hn₀
      nlinarith
    set J : Set ℝ := Icc ((n : ℝ) * Real.log 2) ((k : ℝ) * Real.log 2) with hJ
    have hJsub : J ⊆ Icc 0 ((k : ℝ) * Real.log 2) := by
      refine Icc_subset_Icc_left (by positivity)
    have hpt : ∀ u ∈ J, κ k ^ 2 * Real.exp u ≤
        2 * (E u - κ k * Real.exp (u / 2)) ^ 2 + 2 * ε ^ 2 * Real.exp u := by
      intro u hu
      have hexp2 : Real.exp (u / 2) ^ 2 = Real.exp u := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have hE := hu₀ u (hlow.trans hu.1)
      have hE2 : E u ^ 2 ≤ ε ^ 2 * Real.exp u := by
        rw [← hexp2, ← mul_pow, ← sq_abs (E u)]
        exact pow_le_pow_left₀ (abs_nonneg _) hE 2
      rw [← hexp2] at hE2 ⊢
      nlinarith [sq_nonneg (κ k * Real.exp (u / 2) - 2 * E u), hE2]
    have hmain : ∫ u in J, κ k ^ 2 * Real.exp u ≤
        ∫ u in J, (2 * (E u - κ k * Real.exp (u / 2)) ^ 2 + 2 * ε ^ 2 * Real.exp u) :=
      setIntegral_mono_on
        (((hexpint _).mono_set hJsub).const_mul (κ k ^ 2))
        ((((hAint (κ k) _).mono_set hJsub).const_mul 2).add
          (((hexpint _).mono_set hJsub).const_mul (2 * ε ^ 2)))
        measurableSet_Icc hpt
    have hnk : (n : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by rw [hk]; push_cast; linarith) hlog2.le
    have hJexp : ∫ u in J, Real.exp u = (2 : ℝ) ^ n := by
      rw [hJ, integral_exp_Icc hnk, hexpk, hexpk, hk, pow_succ]
      ring
    rw [integral_const_mul, hJexp, integral_add (((hAint _ _).mono_set hJsub).const_mul 2)
      (((hexpint _).mono_set hJsub).const_mul _), integral_const_mul, integral_const_mul, hJexp] at hmain
    have hsub : ∫ u in J, (E u - κ k * Real.exp (u / 2)) ^ 2 ≤
        ∫ u in Icc 0 ((k : ℝ) * Real.log 2), (E u - κ k * Real.exp (u / 2)) ^ 2 :=
      setIntegral_mono_set (hAint _ _) (Filter.Eventually.of_forall fun u => sq_nonneg _)
        hJsub.eventuallyLE
    have h1 := hI k (by omega)
    have h2 : κ k ^ 2 * (2 : ℝ) ^ n ≤ 2 * (C * q ^ k) + 2 * ε ^ 2 * 2 ^ n := by linarith
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hgoal : 4 * C * (q / 2) ^ k * 2 ^ n = 2 * (C * q ^ k) := by
      rw [div_pow, hk, pow_succ (2 : ℝ) n]
      field_simp
      ring
    have h3 : κ k ^ 2 * (2 : ℝ) ^ n ≤ (4 * C * (q / 2) ^ k + 2 * ε ^ 2) * 2 ^ n := by
      rw [add_mul, hgoal]
      linarith
    exact le_of_mul_le_mul_right h3 h2n
  have hgeo : Tendsto (fun n : ℕ => (q / 2) ^ (n + 1)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := q / 2) (by positivity) (by linarith)
    exact h.comp (tendsto_add_atTop_nat 1)
  have ha0 : a = 0 := by
    by_contra hne
    have hpos : 0 < |a| := abs_pos.mpr hne
    obtain ⟨n₀, hn₀⟩ := hbound2 (|a| / 2) (by positivity)
    have hlim1 : Tendsto (fun n => κ (n + 1) ^ 2) atTop (𝓝 (a ^ 2)) := ha.pow 2
    have hlim2 : Tendsto (fun n : ℕ => 4 * C * (q / 2) ^ (n + 1) + 2 * (|a| / 2) ^ 2) atTop
        (𝓝 (4 * C * 0 + 2 * (|a| / 2) ^ 2)) := (hgeo.const_mul _).add_const _
    have hle := le_of_tendsto_of_tendsto hlim1 hlim2
      (eventually_atTop.mpr ⟨n₀, fun n hn => hn₀ n hn⟩)
    have hsq : (|a| / 2) ^ 2 = a ^ 2 / 4 := by
      rw [div_pow, sq_abs]
      norm_num
    rw [hsq] at hle
    have ha2 : 0 < a ^ 2 := by positivity
    nlinarith
  subst ha0
  -- Step 3: the offsets are geometrically small
  have hgeom : ∀ n : ℕ, |κ (n + 1)| ≤ K * r ^ n / (1 - r) := by
    intro n
    have h := dist_le_of_le_geometric_of_tendsto r K hr1 hdist ha n
    rwa [Real.dist_eq, sub_zero] at h
  have h1r : 0 < 1 - r := by linarith
  -- Step 4: remove the offset
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = K ^ 2 / (1 - r) ^ 2 := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  refine ⟨2 * C + 4 * K₂, by positivity, fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hpt : ∀ u ∈ Icc 0 (((n + 1 : ℕ) : ℝ) * Real.log 2), E u ^ 2 ≤
      2 * (E u - κ (n + 1) * Real.exp (u / 2)) ^ 2 + 2 * κ (n + 1) ^ 2 * Real.exp u := by
    intro u _
    have hexp2 : Real.exp (u / 2) ^ 2 = Real.exp u := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [← hexp2]
    nlinarith [sq_nonneg (E u - 2 * (κ (n + 1) * Real.exp (u / 2)))]
  have hmain : ∫ u in Icc 0 (((n + 1 : ℕ) : ℝ) * Real.log 2), E u ^ 2 ≤
      ∫ u in Icc 0 (((n + 1 : ℕ) : ℝ) * Real.log 2), (2 * (E u - κ (n + 1) * Real.exp (u / 2)) ^ 2 +
        2 * κ (n + 1) ^ 2 * Real.exp u) :=
    setIntegral_mono_on (hEi _)
      (((hAint (κ (n + 1)) _).const_mul 2).add ((hexpint _).const_mul (2 * κ (n + 1) ^ 2)))
      measurableSet_Icc hpt
  rw [integral_add ((hAint _ _).const_mul 2) ((hexpint _).const_mul _), integral_const_mul,
    integral_const_mul, hIinner] at hmain
  have hκ2 : κ (n + 1) ^ 2 ≤ K₂ * (q / 2) ^ n := by
    have h := hgeom n
    have h2 : κ (n + 1) ^ 2 ≤ (K * r ^ n / (1 - r)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    refine h2.trans (le_of_eq ?_)
    rw [hK₂, div_pow, mul_pow, ← pow_mul, mul_comm n 2, pow_mul, hr2]
    ring
  have h2pow : (2 : ℝ) ^ (n + 1) - 1 ≤ 2 * 2 ^ n := by
    rw [pow_succ]
    linarith
  have hqn : (q / 2) ^ n * (2 * 2 ^ n) = 2 * q ^ n := by
    rw [div_pow]
    field_simp
  have hterm : 2 * κ (n + 1) ^ 2 * ((2 : ℝ) ^ (n + 1) - 1) ≤ 4 * K₂ * q ^ (n + 1) := by
    have hqmono : q ^ n ≤ q ^ (n + 1) := pow_le_pow_right₀ hq1 (Nat.le_succ n)
    have h2n1 : (0 : ℝ) ≤ (2 : ℝ) ^ (n + 1) - 1 := by
      have : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      linarith
    calc 2 * κ (n + 1) ^ 2 * ((2 : ℝ) ^ (n + 1) - 1)
        ≤ 2 * (K₂ * (q / 2) ^ n) * (2 * 2 ^ n) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hκ2 (by norm_num)) h2pow h2n1 (by positivity)
      _ = 2 * K₂ * ((q / 2) ^ n * (2 * 2 ^ n)) := by ring
      _ = 4 * K₂ * q ^ n := by rw [hqn]; ring
      _ ≤ 4 * K₂ * q ^ (n + 1) := mul_le_mul_of_nonneg_left hqmono (by positivity)
  have h1 := hI (n + 1) (by omega)
  calc ∫ u in Icc 0 (((n + 1 : ℕ) : ℝ) * Real.log 2), E u ^ 2
      ≤ 2 * (∫ u in Icc 0 (((n + 1 : ℕ) : ℝ) * Real.log 2),
          (E u - κ (n + 1) * Real.exp (u / 2)) ^ 2) + 2 * κ (n + 1) ^ 2 * ((2 : ℝ) ^ (n + 1) - 1) := hmain
    _ ≤ 2 * (C * q ^ (n + 1)) + 4 * K₂ * q ^ (n + 1) := by linarith
    _ = (2 * C + 4 * K₂) * q ^ (n + 1) := by ring

/-! ### From the mollifier to the zeros -/

/-- The prime number theorem for the normalized error: `Ẽ(u) = o(e^{u/2})`. -/
theorem normalizedLogError_littleO {ε : ℝ} (hε : 0 < ε) :
    ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → |normalizedLogError u| ≤ ε * Real.exp (u / 2) := by
  have h := Real.tendsto_exp_atTop.eventually (ArithmeticOfSquareRootPrecision.eventually_abs_psi_sub_le hε)
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp h
  refine ⟨u₀, fun u hu => ?_⟩
  have h1 := hu₀ u hu
  unfold normalizedLogError logError
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hE : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-u / 2) * |Chebyshev.psi (Real.exp u) - Real.exp u|
      ≤ Real.exp (-u / 2) * (ε * Real.exp u) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = ε * (Real.exp (-u / 2) * Real.exp u) := by ring
    _ = ε * Real.exp (u / 2) := by rw [hE]

/-- A growth rate `y^{2β}` for the linear mollifier defect on dyadic lengths. -/
def LinearDefectRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → linearDefect (2 ^ k) ≤ C * ((2 : ℝ) ^ (2 * β)) ^ k

/-- A linear mollifier defect rate `β' < β < ½` is a mean-square band rate `β`. -/
theorem meanSquareBandRate_of_linearDefectRate {β' β : ℝ} (hβ'0 : 0 ≤ β') (hβ' : β' < β)
    (hβ : β < 1 / 2) (h : LinearDefectRate β') : MeanSquareBandRate β := by
  obtain ⟨C, hC, hD⟩ := h
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set q₀ : ℝ := (2 : ℝ) ^ (2 * β') with hq₀
  set q : ℝ := (2 : ℝ) ^ (2 * β) with hq
  have hq₀1 : 1 ≤ q₀ := Real.one_le_rpow (by norm_num) (by positivity)
  have hqq : q₀ < q := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hq1 : 1 ≤ q := by linarith
  have hq2 : q < 2 := by
    have h1 : q < (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rwa [Real.rpow_one] at h1
  have hq0 : 0 < q := by linarith
  -- the polynomial factor is absorbed
  have hρ : |q₀ / q| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hq0]
    exact hqq
  obtain ⟨B, hB⟩ := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hρ).bddAbove_range
  have hB' : ∀ k : ℕ, (k : ℝ) ^ 2 * (q₀ / q) ^ k ≤ B := fun k => hB ⟨k, rfl⟩
  have hB0 : 0 ≤ B := by simpa using hB' 0
  have hIk : ∀ k : ℕ, 1 ≤ k →
      ∫ u in Icc 0 ((k : ℝ) * Real.log 2),
        (normalizedLogError u - linearOffset (2 ^ k) * Real.exp (u / 2)) ^ 2 ≤
        (Real.log 2 ^ 2 * C * B) * q ^ k := by
    intro k hk
    have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h1 := integral_linearBand_le h2k
    have hlogk : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
      push_cast
      rw [Real.log_pow]
    rw [hlogk] at h1
    refine h1.trans ?_
    have hk2 := hB' k
    have hqk : 0 < q ^ k := by positivity
    have hbound : (k : ℝ) ^ 2 * q₀ ^ k ≤ B * q ^ k := by
      rw [div_pow, mul_div_assoc', div_le_iff₀ hqk] at hk2
      exact hk2
    have hDk := hD k hk
    have hcomp : ((k : ℝ) * Real.log 2) ^ 2 * linearDefect (2 ^ k) ≤
        ((k : ℝ) * Real.log 2) ^ 2 * (C * q₀ ^ k) :=
      mul_le_mul_of_nonneg_left hDk (by positivity)
    refine hcomp.trans ?_
    calc ((k : ℝ) * Real.log 2) ^ 2 * (C * q₀ ^ k)
        = Real.log 2 ^ 2 * C * ((k : ℝ) ^ 2 * q₀ ^ k) := by ring
      _ ≤ Real.log 2 ^ 2 * C * (B * q ^ k) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = _ := by ring
  obtain ⟨C', hC', hband⟩ := band_of_dyadic measurable_normalizedLogError
    integrableOn_normalizedLogError_sq (fun ε hε => normalizedLogError_littleO hε)
    (by positivity) hq1 hq2 hIk
  -- from dyadic to all lengths
  refine ⟨C' * Real.exp (2 * β * (2 * Real.log 2)), by positivity, fun L hL => ?_⟩
  set k₀ := ⌈L / Real.log 2⌉₊ with hk₀
  set k := k₀ + 1 with hk
  have hL0 : 0 ≤ L / Real.log 2 := by positivity
  have hLk₀ : L / Real.log 2 ≤ k₀ := Nat.le_ceil _
  have hk₀up : (k₀ : ℝ) < L / Real.log 2 + 1 := Nat.ceil_lt_add_one hL0
  have hLk : L ≤ (k : ℝ) * Real.log 2 := by
    have h1 := (div_le_iff₀ hlog2).mp hLk₀
    rw [hk]
    push_cast
    nlinarith
  have hkup : (k : ℝ) * Real.log 2 ≤ L + 2 * Real.log 2 := by
    have h1 : (k₀ : ℝ) * Real.log 2 ≤ (L / Real.log 2 + 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hk₀up.le hlog2.le
    have h2 : (L / Real.log 2 + 1) * Real.log 2 = L + Real.log 2 := by
      field_simp
    rw [hk]
    push_cast
    nlinarith
  have hβ0 : 0 ≤ β := by linarith
  have hqk : q ^ k = Real.exp (2 * β * ((k : ℝ) * Real.log 2)) := by
    rw [hq, Real.rpow_def_of_pos two_pos, ← Real.exp_nat_mul]
    congr 1
    ring
  have hmono := integral_normalizedLogError_sq_mono hLk
  have hmain := hband k (by omega)
  calc ∫ t in Icc 0 L, normalizedLogError t ^ 2
      ≤ ∫ t in Icc 0 ((k : ℝ) * Real.log 2), normalizedLogError t ^ 2 := hmono
    _ ≤ C' * q ^ k := hmain
    _ = C' * Real.exp (2 * β * ((k : ℝ) * Real.log 2)) := by rw [hqk]
    _ ≤ C' * Real.exp (2 * β * (L + 2 * Real.log 2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hkup (by positivity))) hC'
    _ = C' * Real.exp (2 * β * (2 * Real.log 2)) * Real.exp (2 * β * L) := by
      have hsplit : Real.exp (2 * β * (L + 2 * Real.log 2)) =
          Real.exp (2 * β * (2 * Real.log 2)) * Real.exp (2 * β * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      ring

/-- Band rates are monotone in the exponent. -/
theorem meanSquareBandRate_mono {β₁ β₂ : ℝ} (h : MeanSquareBandRate β₁) (hβ : β₁ ≤ β₂) :
    MeanSquareBandRate β₂ := by
  obtain ⟨C, hC, hband⟩ := h
  refine ⟨C, hC, fun L hL => (hband L hL).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hL)

/-- **A defect rate confines the zeros.**  If the linear mollifier defect grows at most like `y^{2β}`, `0 ≤ β < ½`, every zero has
`Re ρ ≤ ½ + β`. -/
theorem xiZeroHalfPlaneBound_of_linearDefectRate {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1 / 2)
    (h : LinearDefectRate β) : _root_.RHTower.XiZeroHalfPlaneBound β := by
  refine (xiZeroHalfPlaneBound_iff_meanSquareBandRate hβ0 hβ).mpr fun β₁ hβ₁ => ?_
  by_cases hβ₁2 : β₁ < 1 / 2
  · exact meanSquareBandRate_of_linearDefectRate hβ0 hβ₁ hβ₁2 h
  · have hmid : β < (β + 1 / 2) / 2 := by linarith
    have hmid2 : (β + 1 / 2) / 2 < 1 / 2 := by linarith
    exact meanSquareBandRate_mono (meanSquareBandRate_of_linearDefectRate hβ0 hmid hmid2 h)
      (by linarith)

/-- **A bounded linear defect gives RH.**  This is stronger than the classical `d_N → 0`: boundedness along dyadic lengths suffices. -/
theorem riemannHypothesis_of_linearDefect_bounded
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → linearDefect (2 ^ k) ≤ C) : RiemannHypothesis := by
  obtain ⟨C, hC, hD⟩ := h
  refine _root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr
    (xiZeroHalfPlaneBound_of_linearDefectRate le_rfl (by norm_num) ⟨C, hC, fun k hk => ?_⟩)
  simpa using hD k hk

/-- **Subpolynomial defect gives RH.** -/
theorem riemannHypothesis_of_linearDefect_subpolynomial
    (h : ∀ β : ℝ, 0 < β → LinearDefectRate β) : RiemannHypothesis := by
  refine _root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set β := min ε (1 / 4) with hβdef
  have hβ0 : 0 < β := lt_min hε (by norm_num)
  have hβ1 : β < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h1 := xiZeroHalfPlaneBound_of_linearDefectRate hβ0.le hβ1 (h β hβ0) ρ hρ
  have h2 : β ≤ ε := min_le_left _ _
  linarith

end GaloisForLFunctions.ArithmeticProduction
