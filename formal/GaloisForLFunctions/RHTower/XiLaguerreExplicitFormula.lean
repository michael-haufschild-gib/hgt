import GaloisForLFunctions.RHTower.LagExplicitFormula
import GaloisForLFunctions.HTGeometry.PerronDoubleSimplePole
import GaloisForLFunctions.RHTower.XiLaguerreZeroSumIdentity
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.XiLaguerreOffLineNeighbourhood
import GaloisForLFunctions.RHTower.XiEdgeLogDerivativeBlindness

/-!
# The Cesàro explicit formula at a point of the strip

For `Y > 1` and a point `s₀` with `0 < Re s₀ < 1` that is not a zero of `ξ`, the Perron integral
`(1/2π) ∫_{Re z = 2} (−ζ'/ζ)(z) Y^z/(z − s₀)² dt` is evaluated twice.

* **Dirichlet side** (`laguerre_dirichlet_side`): `Σ_{n ≤ Y} Λ(n) (Y/n)^{s₀} log(Y/n)`, from the
  double-pole Perron kernel.
* **Mittag-Leffler side** (`laguerre_mittagLeffler_side`): the expansion
  `−ζ'/ζ = 1/(z−1) + c + ½Σ_k (1/(k+2) − 2/(z+2k+2)) − Σ_ρ [1/(ρ−½) + 1/(z−ρ)]`
  integrated term by term with the double-plus-simple pole kernel
  `(1/2π)∫ Y^z/((z−s₀)²(z−b)) = (Y^b − Y^{s₀})/(b−s₀)² − Y^{s₀} log Y/(b − s₀)`.

**Theorem** (`laguerre_explicit_formula_raw`).  The two sides agree:

  `Σ_{n ≤ Y} Λ(n)(Y/n)^{s₀} log(Y/n) = D(1) + c Y^{s₀} log Y`
  `    + ½ Σ_k [Y^{s₀} log Y/(k+2) − 2 D(−2k−2)] − Σ_ρ [Y^{s₀} log Y/(ρ − ½) + D(ρ)]`,

with `D(b) = (Y^b − Y^{s₀})/(b−s₀)² − Y^{s₀} log Y/(b − s₀)` and `c = ½ − ½ log π − γ/2`.
Dividing by `Y^{s₀}`, the zero terms are `(Y^{ρ−s₀} − 1)/(ρ−s₀)²` plus logarithmic-derivative
terms.  At `s₀ = ½ + it` the untwisted part `−Σ_ρ 1/(ρ−s₀)²` is the order-one horizontal slice
coefficient `c₂(t)/Ξ(t)²`, so the formula compares the slice coefficient with an all-prime Cesàro
sum.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## The kernel `Y^z/(z − s₀)²` on the line `Re z = 2` -/

/-- The Perron kernel `Y^z/(z − s₀)²` on the line `Re z = 2`. -/
def cesaroLaguerreKernel (Y : ℝ) (s₀ : ℂ) (t : ℝ) : ℂ := (Y : ℂ) ^ lineTwo t / (lineTwo t - s₀) ^ 2

/-- The double-plus-simple pole value `(Y^b − Y^a)/(b−a)² − Y^a log Y/(b−a)`. -/
def laguerreDS (Y : ℝ) (a b : ℂ) : ℂ :=
  ((Y : ℂ) ^ b - (Y : ℂ) ^ a) / (b - a) ^ 2 - (Y : ℂ) ^ a * Complex.log Y / (b - a)

/-- The constant of the kernel bound. -/
def laguerreConst (s₀ : ℂ) : ℝ := 2 * (1 + s₀.im ^ 2)

theorem laguerreConst_pos (s₀ : ℂ) : 0 < laguerreConst s₀ := by unfold laguerreConst; positivity

theorem one_add_sq_le_laguerre (s₀ : ℂ) (t : ℝ) :
    1 + t ^ 2 ≤ laguerreConst s₀ * (1 + (t - s₀.im) ^ 2) := by
  unfold laguerreConst
  nlinarith [sq_nonneg (t - 2 * s₀.im), sq_nonneg (s₀.im * (t - s₀.im)), sq_nonneg s₀.im]

theorem norm_lineTwo_sub_sq_ge {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) (t : ℝ) :
    1 + (t - s₀.im) ^ 2 ≤ ‖lineTwo t - s₀‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [lineTwo, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  nlinarith

theorem lineTwo_sub_ne_zero_of_re_le {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) (t : ℝ) : lineTwo t - s₀ ≠ 0 :=
  lineTwo_sub_ne_zero (by linarith) t

/-- `‖Y^z/(z − s₀)²‖ ≤ C(s₀) Y²/(1 + t²)`. -/
theorem norm_laguerreKernel_le {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) (t : ℝ) :
    ‖cesaroLaguerreKernel Y s₀ t‖ ≤ laguerreConst s₀ * (Y ^ 2 / (1 + t ^ 2)) := by
  unfold cesaroLaguerreKernel
  rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hY, lineTwo_re,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 := norm_lineTwo_sub_sq_ge hs₀ t
  have h2 := one_add_sq_le_laguerre s₀ t
  have hC := laguerreConst_pos s₀
  rw [div_le_iff₀ (pow_pos (norm_pos_iff.mpr (lineTwo_sub_ne_zero_of_re_le hs₀ t)) 2)]
  have hYsq : 0 ≤ Y ^ 2 := by positivity
  calc Y ^ 2 = laguerreConst s₀ * (Y ^ 2 / (1 + t ^ 2)) * ((1 + t ^ 2) / laguerreConst s₀) := by
        field_simp
    _ ≤ laguerreConst s₀ * (Y ^ 2 / (1 + t ^ 2)) * ‖lineTwo t - s₀‖ ^ 2 := by
        gcongr
        rw [div_le_iff₀ hC]
        nlinarith

theorem continuous_laguerreKernel {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) :
    Continuous (cesaroLaguerreKernel Y s₀) := by
  unfold cesaroLaguerreKernel
  have hcp : Continuous (fun t : ℝ => (Y : ℂ) ^ lineTwo t) :=
    (by unfold lineTwo; fun_prop : Continuous lineTwo).const_cpow
      (Or.inl (by exact_mod_cast hY.ne'))
  refine hcp.div ?_ fun t => pow_ne_zero 2 (lineTwo_sub_ne_zero_of_re_le hs₀ t)
  unfold lineTwo; fun_prop

theorem integrable_laguerreKernel {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) :
    Integrable (cesaroLaguerreKernel Y s₀) :=
  integrable_cpow_div_doublePole (σ := 2) (by linarith) hY

/-! ## Perron evaluations on the line `Re z = 2` -/

theorem integrable_lineTwo_double {a : ℂ} (ha : a.re < 2) {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => (X : ℂ) ^ lineTwo t / (lineTwo t - a) ^ 2) :=
  integrable_cpow_div_doublePole (σ := 2) ha hX

theorem perron_lineTwo_double {a : ℂ} (ha : a.re < 2) {X : ℝ} (hX : 0 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (X : ℂ) ^ lineTwo t / (lineTwo t - a) ^ 2 =
      if 1 < X then (X : ℂ) ^ a * Complex.log X else 0 := by
  split_ifs with h
  · exact perron_doublePole (σ := 2) ha h
  · exact perron_doublePole_of_le_one (σ := 2) ha hX (not_lt.mp h)

theorem integrable_lineTwo_doubleSimple {a b : ℂ} (ha : a.re < 2) (hb : b.re < 2) (hab : a ≠ b)
    {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => (X : ℂ) ^ lineTwo t / ((lineTwo t - a) ^ 2 * (lineTwo t - b))) :=
  integrable_cpow_div_doubleSimple (σ := 2) ha hb hab hX

theorem perron_lineTwo_doubleSimple {a b : ℂ} (ha : a.re < 2) (hb : b.re < 2) (hab : a ≠ b)
    {X : ℝ} (hX : 1 < X) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (X : ℂ) ^ lineTwo t / ((lineTwo t - a) ^ 2 * (lineTwo t - b))
      = laguerreDS X a b :=
  perron_doubleSimple (σ := 2) ha hb hab hX

/-! ## The Dirichlet side -/

/-- The `n`-th Dirichlet term of the Perron integrand. -/
def laguerreDirTerm (Y : ℝ) (s₀ : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) (lineTwo t) n * cesaroLaguerreKernel Y s₀ t

theorem laguerreDirTerm_eq {Y : ℝ} (hY : 0 < Y) (s₀ : ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    laguerreDirTerm Y s₀ n t =
      ((vonMangoldt n : ℝ) : ℂ) * (((Y / n : ℝ) : ℂ) ^ lineTwo t / (lineTwo t - s₀) ^ 2) := by
  unfold laguerreDirTerm cesaroLaguerreKernel
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hcp : (((Y / n : ℝ) : ℂ) ^ lineTwo t) = (Y : ℂ) ^ lineTwo t / (n : ℂ) ^ lineTwo t := by
    rw [show (Y / n : ℝ) = Y * (n : ℝ)⁻¹ by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hY.le (by positivity), Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by
        rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hn0.le]
        exact Real.pi_pos.ne'.symm)]
    exact (div_eq_mul_inv _ _).symm
  rw [hcp]
  ring

theorem laguerreDirTerm_zero (Y : ℝ) (s₀ : ℂ) (t : ℝ) : laguerreDirTerm Y s₀ 0 t = 0 := by
  unfold laguerreDirTerm; rw [LSeries.term_zero, zero_mul]

theorem integrable_laguerreDirTerm {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) (n : ℕ) :
    Integrable (laguerreDirTerm Y s₀ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : laguerreDirTerm Y s₀ 0 = fun _ => 0 := funext (laguerreDirTerm_zero Y s₀)
    rw [h0]; exact integrable_zero _ _ _
  · have hYn : (0 : ℝ) < Y / n := by positivity
    have := (integrable_lineTwo_double (a := s₀) (by linarith) hYn).const_mul
      ((vonMangoldt n : ℝ) : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    rw [laguerreDirTerm_eq hY s₀ hn.ne']

theorem integral_norm_laguerreDirTerm {Y : ℝ} (hY : 0 < Y) (s₀ : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∫ t : ℝ, ‖laguerreDirTerm Y s₀ n t‖ =
      vonMangoldt n * (Y / n) ^ 2 * ∫ t : ℝ, ‖(1 : ℂ) / (lineTwo t - s₀) ^ 2‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hYn : (0 : ℝ) < Y / n := by positivity
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [laguerreDirTerm_eq hY s₀ hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, div_eq_mul_one_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hYn, lineTwo_re,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

theorem summable_integral_norm_laguerreDirTerm {Y : ℝ} (hY : 0 < Y) (s₀ : ℂ) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖laguerreDirTerm Y s₀ n t‖) := by
  set C : ℝ := ∫ t : ℝ, ‖(1 : ℂ) / (lineTwo t - s₀) ^ 2‖
  have hbase : Summable (fun n : ℕ => (Y ^ 2 * C) * (vonMangoldt n / (n : ℝ) ^ 2)) :=
    summable_vonMangoldt_div_sq.mul_left _
  refine hbase.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [laguerreDirTerm_zero]
  · rw [integral_norm_laguerreDirTerm hY s₀ hn.ne']
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring

/-- **The Dirichlet side.**  `(1/2π)∫ (Σ Λ(n) n^{−z}) Y^z/(z−s₀)² dt = Σ_{n≤Y} Λ(n)(Y/n)^{s₀} log(Y/n)`. -/
theorem laguerre_dirichlet_side {Y : ℝ} (hY : 1 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) *
        cesaroLaguerreKernel Y s₀ t
      = ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ((vonMangoldt n : ℝ) : ℂ) *
          (((Y / n : ℝ) : ℂ) ^ s₀ * Complex.log ((Y / n : ℝ) : ℂ)) := by
  have hY0 : 0 < Y := by linarith
  have hint : (fun t : ℝ => LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) *
      cesaroLaguerreKernel Y s₀ t) = fun t : ℝ => ∑' n : ℕ, laguerreDirTerm Y s₀ n t := by
    funext t
    unfold LSeries laguerreDirTerm
    rw [tsum_mul_right]
  rw [hint, ← integral_tsum_of_summable_integral_norm (integrable_laguerreDirTerm hY0 hs₀)
    (summable_integral_norm_laguerreDirTerm hY0 s₀)]
  have hterm : ∀ n : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, laguerreDirTerm Y s₀ n t =
      ((vonMangoldt n : ℝ) : ℂ) * (if 1 < Y / n then
        ((Y / n : ℝ) : ℂ) ^ s₀ * Complex.log ((Y / n : ℝ) : ℂ) else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [laguerreDirTerm_zero]
    · have hYn : (0 : ℝ) < Y / n := by positivity
      have h := perron_lineTwo_double (a := s₀) (by linarith) hYn
      have hI : ∫ t : ℝ, laguerreDirTerm Y s₀ n t = ((vonMangoldt n : ℝ) : ℂ) *
          ∫ t : ℝ, ((Y / n : ℝ) : ℂ) ^ lineTwo t / (lineTwo t - s₀) ^ 2 := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
          laguerreDirTerm_eq hY0 s₀ hn.ne' t)
      rw [hI, ← h, Complex.real_smul, Complex.real_smul]
      ring
  rw [smul_tsum_eq]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Y⌋₊)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hnY : (n : ℝ) ≤ Y := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le hY0.le)
    by_cases h : 1 < Y / n
    · rw [if_pos h]
    · rw [if_neg h]
      have heq : Y / n = 1 := le_antisymm (not_lt.mp h) (by rw [le_div_iff₀ hn0]; linarith)
      rw [heq]; simp
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · have hgt : ¬ (1 < Y / n) := by
        intro h1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
        rw [one_lt_div hn0] at h1
        exact hn ⟨hnpos, Nat.le_floor h1.le⟩
      rw [if_neg hgt, mul_zero]

/-! ## The Mittag-Leffler side: termwise bounds -/

/-- The `k`-th digamma term times the kernel. -/
def laguerreKTerm (Y : ℝ) (s₀ : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (1 / ((k : ℂ) + 2) - 2 / (lineTwo t + 2 * ((k : ℂ) + 1))) * cesaroLaguerreKernel Y s₀ t

/-- The zero term times the kernel. -/
def laguerreZTerm (Y : ℝ) (s₀ : ℂ) (q : XiZeroCopy) (t : ℝ) : ℂ :=
  (((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo t - (q.1 : ℂ))⁻¹) * cesaroLaguerreKernel Y s₀ t

theorem norm_laguerreKTerm_le {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) (k : ℕ) (t : ℝ) :
    ‖laguerreKTerm Y s₀ k t‖ ≤ laguerreConst s₀ * ((Y ^ 2 / 2) *
      (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)))) * (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) := by
  unfold laguerreKTerm
  rw [norm_mul]
  have h1 := norm_kFactor_le k t
  have h2 := norm_laguerreKernel_le hY hs₀ t
  have h3 := sqrt_abs_le_rpow_quarter t
  have hC := laguerreConst_pos s₀
  calc ‖1 / ((k : ℂ) + 2) - 2 / (lineTwo t + 2 * ((k : ℂ) + 1))‖ * ‖cesaroLaguerreKernel Y s₀ t‖
      ≤ (Real.sqrt |t| / (2 * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) *
          (laguerreConst s₀ * (Y ^ 2 / (1 + t ^ 2))) := by gcongr
    _ ≤ ((1 + t ^ 2) ^ (1 / 4 : ℝ) / (2 * ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2))) *
          (laguerreConst s₀ * (Y ^ 2 / (1 + t ^ 2))) := by gcongr
    _ = laguerreConst s₀ * ((Y ^ 2 / 2) * (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)))) *
          ((1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2)) := by
        have hk2pos : 0 < Real.sqrt ((k : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
        have h1t : 0 < 1 + t ^ 2 := by positivity
        field_simp
    _ = _ := by rw [rpow_quarter_div_eq]

theorem continuous_laguerreKTerm {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) (k : ℕ) :
    Continuous (laguerreKTerm Y s₀ k) := by
  unfold laguerreKTerm
  refine Continuous.mul (Continuous.sub continuous_const ?_) (continuous_laguerreKernel hY hs₀)
  exact continuous_const.div (by unfold lineTwo; fun_prop) (lineTwo_add_ne_zero k)

theorem integrable_laguerreKTerm {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) (k : ℕ) :
    Integrable (laguerreKTerm Y s₀ k) :=
  (integrable_one_add_sq_rpow_neg_three_quarters.const_mul _).mono'
    (continuous_laguerreKTerm hY hs₀ k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => norm_laguerreKTerm_le hY hs₀ k t)

theorem summable_integral_norm_laguerreKTerm {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) :
    Summable (fun k : ℕ => ∫ t : ℝ, ‖laguerreKTerm Y s₀ k t‖) := by
  have hb : Summable (fun k : ℕ => laguerreConst s₀ * ((Y ^ 2 / 2) *
      (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2)))) * majorantMass) :=
    ((summable_inv_mul_sqrt_shift.mul_left (Y ^ 2 / 2)).mul_left _).mul_right majorantMass
  refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) (fun k => ?_) hb
  unfold majorantMass
  rw [← integral_const_mul]
  exact integral_mono (integrable_laguerreKTerm hY hs₀ k).norm
    (integrable_one_add_sq_rpow_neg_three_quarters.const_mul _) (norm_laguerreKTerm_le hY hs₀ k)

theorem norm_laguerreZTerm_le_majorant {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1)
    (q : XiZeroCopy) (t : ℝ) :
    ‖laguerreZTerm Y s₀ q t‖ ≤ laguerreConst s₀ *
      (8 * Y ^ 2 * Real.sqrt 2 / (‖(q.1 : ℂ) - 1 / 2‖ * Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖)) *
      ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ))) := by
  have hC := laguerreConst_pos s₀
  unfold laguerreZTerm
  rw [norm_mul]
  have hK := norm_laguerreKernel_le hY hs₀ t
  have hz := norm_zFactor_le q t
  have hqn : 0 < ‖(q.1 : ℂ) - 1 / 2‖ := norm_pos_iff.mpr (xiZeroCopy_sub_half_ne_zero q)
  have h3 : Y ^ 2 / (1 + t ^ 2) ≤ 2 * Y ^ 2 / (1 + |t|) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (1 - |t|), sq_nonneg Y]
  have hmaj := two_centre_majorant ((q.1 : ℂ)).im t
  have hle : ‖(q.1 : ℂ) - 1 / 2‖ ≤ 1 + |((q.1 : ℂ)).im| := by
    have := Complex.norm_le_abs_re_add_abs_im ((q.1 : ℂ) - 1 / 2)
    have hre0 := xiZeroCopy_re_pos q
    have hre1 := xiZeroCopy_re_lt_one q
    have habs : |((q.1 : ℂ) - 1 / 2).re| ≤ 1 := by
      rw [Complex.sub_re]; simp only [Complex.div_ofNat_re, Complex.one_re]
      rw [abs_le]; constructor <;> linarith
    have him : ((q.1 : ℂ) - 1 / 2).im = ((q.1 : ℂ)).im := by simp
    rw [him] at this
    linarith
  have hrp : (1 + |((q.1 : ℂ)).im|) ^ (-(1 / 2 : ℝ)) ≤ 1 / Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    exact inv_anti₀ (Real.sqrt_pos.mpr hqn) (Real.sqrt_le_sqrt hle)
  have hsq := Real.sqrt_pos.mpr hqn
  calc ‖((q.1 : ℂ) - 1 / 2)⁻¹ + (lineTwo t - (q.1 : ℂ))⁻¹‖ * ‖cesaroLaguerreKernel Y s₀ t‖
      ≤ (4 * (1 + |t|) / (‖(q.1 : ℂ) - 1 / 2‖ * (1 + |t - ((q.1 : ℂ)).im|))) *
          (laguerreConst s₀ * (2 * Y ^ 2 / (1 + |t|) ^ 2)) :=
        mul_le_mul hz (hK.trans (mul_le_mul_of_nonneg_left h3 hC.le)) (norm_nonneg _)
          (by positivity)
    _ = laguerreConst s₀ * (8 * Y ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) *
          (1 / ((1 + |t - ((q.1 : ℂ)).im|) * (1 + |t|))) := by
        have : (0 : ℝ) < 1 + |t| := by positivity
        field_simp
        ring
    _ ≤ laguerreConst s₀ * (8 * Y ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) *
          (Real.sqrt 2 * (1 + |((q.1 : ℂ)).im|) ^ (-(1 / 2 : ℝ)) *
          ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ)))) := by
        gcongr
    _ ≤ laguerreConst s₀ * (8 * Y ^ 2 / ‖(q.1 : ℂ) - 1 / 2‖) *
          (Real.sqrt 2 * (1 / Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖) *
          ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ)))) := by
        gcongr
    _ = _ := by
        field_simp

theorem continuous_laguerreZTerm {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1)
    (q : XiZeroCopy) : Continuous (laguerreZTerm Y s₀ q) := by
  unfold laguerreZTerm
  have hre := xiZeroCopy_re_lt_one q
  refine Continuous.mul (Continuous.add continuous_const ?_) (continuous_laguerreKernel hY hs₀)
  exact Continuous.inv₀ (by unfold lineTwo; fun_prop) (fun t => lineTwo_sub_ne_zero (by linarith) t)

theorem integrable_laguerreZTerm {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1)
    (q : XiZeroCopy) : Integrable (laguerreZTerm Y s₀ q) :=
  ((integrable_majorant_shift ((q.1 : ℂ)).im).const_mul _).mono'
    (continuous_laguerreZTerm hY hs₀ q).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => norm_laguerreZTerm_le_majorant hY hs₀ q t)

theorem summable_integral_norm_laguerreZTerm {Y : ℝ} (hY : 0 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) :
    Summable (fun q : XiZeroCopy => ∫ t : ℝ, ‖laguerreZTerm Y s₀ q t‖) := by
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun q => ?_)
    (xiSpectralPoint_inv_three_halves_summable.mul_left
      (laguerreConst s₀ * (16 * Y ^ 2 * Real.sqrt 2 * majorantMass)))
  have hnorm : ‖xiSpectralPoint q‖ = ‖(q.1 : ℂ) - 1 / 2‖ := by
    rw [xiSpectralPoint, norm_mul, norm_neg, Complex.norm_I, mul_one]
  rw [hnorm]
  calc ∫ t : ℝ, ‖laguerreZTerm Y s₀ q t‖
      ≤ ∫ t : ℝ, laguerreConst s₀ *
          (8 * Y ^ 2 * Real.sqrt 2 / (‖(q.1 : ℂ) - 1 / 2‖ * Real.sqrt ‖(q.1 : ℂ) - 1 / 2‖)) *
          ((1 + t ^ 2) ^ (-(3 / 4 : ℝ)) + (1 + (t - ((q.1 : ℂ)).im) ^ 2) ^ (-(3 / 4 : ℝ))) :=
        integral_mono (integrable_laguerreZTerm hY hs₀ q).norm
          ((integrable_majorant_shift _).const_mul _) (norm_laguerreZTerm_le_majorant hY hs₀ q)
    _ = _ := by
        rw [integral_const_mul, integral_majorant_shift]
        ring

/-! ## Termwise integrals -/

theorem integral_laguerreKernel {Y : ℝ} (hY : 1 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, cesaroLaguerreKernel Y s₀ t = (Y : ℂ) ^ s₀ * Complex.log Y := by
  have h := perron_lineTwo_double (a := s₀) (by linarith) (by linarith : (0 : ℝ) < Y)
  rw [if_pos hY] at h
  exact h

/-- `(1/(z−b)) · Y^z/(z−s₀)²` integrates to `D(b)`. -/
theorem integral_laguerre_pole {Y : ℝ} (hY : 1 < Y) {s₀ b : ℂ} (hs₀ : s₀.re ≤ 1) (hb : b.re < 2)
    (hb0 : s₀ ≠ b) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, (lineTwo t - b)⁻¹ * cesaroLaguerreKernel Y s₀ t =
      laguerreDS Y s₀ b := by
  have h := perron_lineTwo_doubleSimple (a := s₀) (b := b) (by linarith) hb hb0 hY
  rw [← h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  unfold cesaroLaguerreKernel
  have h1 := lineTwo_sub_ne_zero_of_re_le hs₀ t
  have h2 := lineTwo_sub_ne_zero hb t
  field_simp

theorem integrable_laguerre_pole {Y : ℝ} (hY : 0 < Y) {s₀ b : ℂ} (hs₀ : s₀.re ≤ 1)
    (hb : b.re < 2) (hb0 : s₀ ≠ b) :
    Integrable (fun t : ℝ => (lineTwo t - b)⁻¹ * cesaroLaguerreKernel Y s₀ t) := by
  refine (integrable_lineTwo_doubleSimple (a := s₀) (b := b) (by linarith) hb hb0 hY).congr
    (Filter.Eventually.of_forall fun t => ?_)
  unfold cesaroLaguerreKernel
  have h1 := lineTwo_sub_ne_zero_of_re_le hs₀ t
  have h2 := lineTwo_sub_ne_zero hb t
  field_simp

/-- The trivial-zero abscissae `−2(k+1)`. -/
def trivialAbscissa (k : ℕ) : ℂ := -(2 * ((k : ℂ) + 1))

theorem trivialAbscissa_re (k : ℕ) : (trivialAbscissa k).re = -(2 * ((k : ℝ) + 1)) := by
  simp [trivialAbscissa]

theorem s₀_ne_trivialAbscissa {s₀ : ℂ} (hs₀ : 0 < s₀.re) (k : ℕ) : s₀ ≠ trivialAbscissa k := by
  intro h
  have := congrArg Complex.re h
  rw [trivialAbscissa_re] at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem integral_laguerreKTerm {Y : ℝ} (hY : 1 < Y) {s₀ : ℂ} (hs₀0 : 0 < s₀.re) (hs₀ : s₀.re ≤ 1)
    (k : ℕ) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, laguerreKTerm Y s₀ k t =
      (1 / ((k : ℂ) + 2)) * ((Y : ℂ) ^ s₀ * Complex.log Y) - 2 * laguerreDS Y s₀ (trivialAbscissa k) := by
  have hY0 : 0 < Y := by linarith
  have hb : (trivialAbscissa k).re < 2 := by
    rw [trivialAbscissa_re]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hne := s₀_ne_trivialAbscissa hs₀0 k
  have hsplit : ∀ t : ℝ, laguerreKTerm Y s₀ k t = (1 / ((k : ℂ) + 2)) * cesaroLaguerreKernel Y s₀ t -
      2 * ((lineTwo t - trivialAbscissa k)⁻¹ * cesaroLaguerreKernel Y s₀ t) := by
    intro t
    unfold laguerreKTerm trivialAbscissa
    rw [show lineTwo t - -(2 * ((k : ℂ) + 1)) = lineTwo t + 2 * ((k : ℂ) + 1) by ring]
    ring
  simp_rw [hsplit]
  rw [integral_sub ((integrable_laguerreKernel hY0 hs₀).const_mul _)
      ((integrable_laguerre_pole hY0 hs₀ hb hne).const_mul _), integral_const_mul,
    integral_const_mul, smul_sub, ← mul_smul_comm, ← mul_smul_comm,
    integral_laguerreKernel hY hs₀, integral_laguerre_pole hY hs₀ hb hne]

theorem integral_laguerreZTerm {Y : ℝ} (hY : 1 < Y) {s₀ : ℂ} (hs₀ : s₀.re ≤ 1)
    (q : XiZeroCopy) (hq : s₀ ≠ (q.1 : ℂ)) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, laguerreZTerm Y s₀ q t =
      ((q.1 : ℂ) - 1 / 2)⁻¹ * ((Y : ℂ) ^ s₀ * Complex.log Y) + laguerreDS Y s₀ (q.1 : ℂ) := by
  have hY0 : 0 < Y := by linarith
  have hb : ((q.1 : ℂ)).re < 2 := by linarith [xiZeroCopy_re_lt_one q]
  have hsplit : ∀ t : ℝ, laguerreZTerm Y s₀ q t =
      ((q.1 : ℂ) - 1 / 2)⁻¹ * cesaroLaguerreKernel Y s₀ t +
        (lineTwo t - (q.1 : ℂ))⁻¹ * cesaroLaguerreKernel Y s₀ t := by
    intro t; unfold laguerreZTerm; ring
  simp_rw [hsplit]
  rw [integral_add ((integrable_laguerreKernel hY0 hs₀).const_mul _)
      (integrable_laguerre_pole hY0 hs₀ hb hq), integral_const_mul, smul_add, ← mul_smul_comm,
    integral_laguerreKernel hY hs₀, integral_laguerre_pole hY hs₀ hb hq]

/-! ## Assembly -/

/-- **The Mittag-Leffler side.** -/
theorem laguerre_mittagLeffler_side {Y : ℝ} (hY : 1 < Y) {s₀ : ℂ} (hs₀0 : 0 < s₀.re)
    (hs₀ : s₀.re < 1) :
    (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) *
        cesaroLaguerreKernel Y s₀ t
      = laguerreDS Y s₀ 1 +
        ((1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2) *
          ((Y : ℂ) ^ s₀ * Complex.log Y) +
        (1 / 2 : ℂ) * (∑' k : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, laguerreKTerm Y s₀ k t) -
        ∑' q : XiZeroCopy, (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, laguerreZTerm Y s₀ q t := by
  have hY0 : 0 < Y := by linarith
  have hs₀' : s₀.re ≤ 1 := hs₀.le
  have hs₁ : s₀ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hs₀; exact lt_irrefl 1 hs₀
  set c₁ : ℂ := (1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2
    with hc₁
  have hpt : ∀ t : ℝ, LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo t) *
      cesaroLaguerreKernel Y s₀ t =
      ((lineTwo t - 1)⁻¹ * cesaroLaguerreKernel Y s₀ t + c₁ * cesaroLaguerreKernel Y s₀ t) +
        (1 / 2 : ℂ) * (∑' k : ℕ, laguerreKTerm Y s₀ k t) -
        ∑' q : XiZeroCopy, laguerreZTerm Y s₀ q t := by
    intro t
    rw [lseries_vonMangoldt_lineTwo t]
    unfold laguerreKTerm laguerreZTerm
    rw [tsum_mul_right, tsum_mul_right]
    ring
  simp_rw [hpt]
  have hb1 : (1 : ℂ).re < 2 := by simp
  have hA1 := integrable_laguerre_pole hY0 hs₀' hb1 hs₁
  have hA2 := (integrable_laguerreKernel hY0 hs₀').const_mul c₁
  have hTk : Integrable (fun t : ℝ => ∑' k : ℕ, laguerreKTerm Y s₀ k t) :=
    integrable_tsum_of_summable_integral_norm'
      (fun k => (continuous_laguerreKTerm hY0 hs₀' k).measurable)
      (integrable_laguerreKTerm hY0 hs₀') (summable_integral_norm_laguerreKTerm hY0 hs₀')
  have hTq : Integrable (fun t : ℝ => ∑' q : XiZeroCopy, laguerreZTerm Y s₀ q t) :=
    integrable_tsum_of_summable_integral_norm'
      (fun q => (continuous_laguerreZTerm hY0 hs₀' q).measurable)
      (integrable_laguerreZTerm hY0 hs₀') (summable_integral_norm_laguerreZTerm hY0 hs₀')
  have hS1 : Integrable (fun t : ℝ => (lineTwo t - 1)⁻¹ * cesaroLaguerreKernel Y s₀ t +
      c₁ * cesaroLaguerreKernel Y s₀ t) := hA1.add hA2
  have hS2 : Integrable (fun t : ℝ => (lineTwo t - 1)⁻¹ * cesaroLaguerreKernel Y s₀ t +
      c₁ * cesaroLaguerreKernel Y s₀ t + (1 / 2 : ℂ) * ∑' k : ℕ, laguerreKTerm Y s₀ k t) :=
    hS1.add (hTk.const_mul (1 / 2 : ℂ))
  rw [integral_sub hS2 hTq, integral_add hS1 (hTk.const_mul _), integral_add hA1 hA2,
    integral_const_mul, integral_const_mul,
    ← integral_tsum_of_summable_integral_norm (integrable_laguerreKTerm hY0 hs₀')
      (summable_integral_norm_laguerreKTerm hY0 hs₀'),
    ← integral_tsum_of_summable_integral_norm (integrable_laguerreZTerm hY0 hs₀')
      (summable_integral_norm_laguerreZTerm hY0 hs₀')]
  rw [smul_sub, smul_add, smul_add, ← mul_smul_comm, ← mul_smul_comm,
    integral_laguerre_pole hY hs₀' hb1 hs₁, integral_laguerreKernel hY hs₀', smul_tsum_eq,
    smul_tsum_eq]

/-- **The Cesàro explicit formula at a point of the strip.**  For `Y > 1` and `0 < Re s₀ < 1`
with `ξ(s₀) ≠ 0`,

`Σ_{n ≤ Y} Λ(n)(Y/n)^{s₀} log(Y/n) = D(1) + c Y^{s₀} log Y`
`    + ½ Σ_k [Y^{s₀} log Y/(k+2) − 2 D(−2k−2)] − Σ_ρ [Y^{s₀} log Y/(ρ−½) + D(ρ)]`,

with `D(b) = (Y^b − Y^{s₀})/(b−s₀)² − Y^{s₀} log Y/(b−s₀)` and `c = ½ − ½ log π − γ/2`. -/
theorem laguerre_explicit_formula_raw {Y : ℝ} (hY : 1 < Y) {s₀ : ℂ} (hs₀0 : 0 < s₀.re)
    (hs₀ : s₀.re < 1) (hξ : xi s₀ ≠ 0) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ((vonMangoldt n : ℝ) : ℂ) *
        (((Y / n : ℝ) : ℂ) ^ s₀ * Complex.log ((Y / n : ℝ) : ℂ)) =
      laguerreDS Y s₀ 1 +
        ((1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2) *
          ((Y : ℂ) ^ s₀ * Complex.log Y) +
        (1 / 2 : ℂ) * (∑' k : ℕ, ((1 / ((k : ℂ) + 2)) * ((Y : ℂ) ^ s₀ * Complex.log Y) -
          2 * laguerreDS Y s₀ (trivialAbscissa k))) -
        ∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ * ((Y : ℂ) ^ s₀ * Complex.log Y) +
          laguerreDS Y s₀ (q.1 : ℂ)) := by
  have hq : ∀ q : XiZeroCopy, s₀ ≠ (q.1 : ℂ) := by
    intro q h; apply hξ; rw [h]; exact xi_xiZeroCopy_eq_zero q
  rw [← laguerre_dirichlet_side hY hs₀.le, laguerre_mittagLeffler_side hY hs₀0 hs₀,
    tsum_congr fun k => integral_laguerreKTerm hY hs₀0 hs₀.le k,
    tsum_congr fun q => integral_laguerreZTerm hY hs₀.le q (hq q)]

/-! ## Regrouping: the archimedean and divisor parts -/

/-- The archimedean logarithmic derivative `1/s + 1/(s−1) + Γ_ℝ'/Γ_ℝ(s)`, so that
`−ζ'/ζ = archLogDeriv − ξ'/ξ`. -/
def archLogDeriv (s : ℂ) : ℂ := s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s

/-- The shifted digamma terms `1/(k+2) − 2/(s + 2k + 2)`. -/
def shiftedDigammaTerm (s : ℂ) (k : ℕ) : ℂ := 1 / ((k : ℂ) + 2) - 2 / (s + 2 * ((k : ℂ) + 1))

theorem summable_shiftedDigammaTerm {s : ℂ} (hs : 0 < s.re) : Summable (shiftedDigammaTerm s) := by
  have hs2 : 0 < (s / 2).re := by rw [Complex.div_re]; simp; linarith
  have h := (summable_nat_add_iff 1).mpr (summable_digammaSeriesTerm hs2)
  refine h.congr fun k => ?_
  unfold shiftedDigammaTerm
  push_cast
  rw [show (k : ℂ) + 1 + 1 = (k : ℂ) + 2 by ring,
    show s / 2 + ((k : ℂ) + 1) = (s + 2 * ((k : ℂ) + 1)) / 2 by ring, one_div_div]

/-- `1/(s−1) + c + ½ Σ_k (1/(k+2) − 2/(s+2k+2)) = 1/s + 1/(s−1) + Γ_ℝ'/Γ_ℝ(s)`. -/
theorem archLogDeriv_eq {s : ℂ} (hs : 0 < s.re) :
    (s - 1)⁻¹ + ((1 : ℂ) / 2 - (Real.log Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2) +
        (1 / 2 : ℂ) * ∑' k : ℕ, shiftedDigammaTerm s k = archLogDeriv s := by
  have hs2 : 0 < (s / 2).re := by rw [Complex.div_re]; simp; linarith
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  have hΓ := logDeriv_Gammaℝ_digamma hs
  have hdig := digamma_eq_tsum hs2
  have hsumm := summable_digammaSeriesTerm hs2
  rw [hsumm.tsum_eq_zero_add] at hdig
  have hshift : (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℂ) + 1) - 1 / (s / 2 + ((k + 1 : ℕ) : ℂ)))
      = shiftedDigammaTerm s := by
    funext k
    unfold shiftedDigammaTerm
    push_cast
    rw [show (k : ℂ) + 1 + 1 = (k : ℂ) + 2 by ring,
      show s / 2 + ((k : ℂ) + 1) = (s + 2 * ((k : ℂ) + 1)) / 2 by ring, one_div_div]
  rw [hshift] at hdig
  have h0 : (1 : ℂ) / (((0 : ℕ) : ℂ) + 1) - 1 / (s / 2 + ((0 : ℕ) : ℂ)) = 1 - 2 / s := by
    push_cast
    rw [add_zero, zero_add, div_one, one_div_div]
  rw [h0] at hdig
  unfold archLogDeriv
  rw [hΓ, hdig]
  field_simp
  ring

/-- The trivial-zero powers `(Y^{−2k−2} − Y^{s₀})/(−2k−2−s₀)²` are summable. -/
theorem summable_trivialAbscissa_pow {Y : ℝ} (hY : 1 < Y) {s₀ : ℂ} (hs₀0 : 0 < s₀.re) :
    Summable (fun k : ℕ => ((Y : ℂ) ^ trivialAbscissa k - (Y : ℂ) ^ s₀) /
      (trivialAbscissa k - s₀) ^ 2) := by
  have hY0 : 0 < Y := by linarith
  set M : ℝ := 1 + Y ^ s₀.re with hM
  have hbase : Summable (fun k : ℕ => (M / 4) * (1 / ((k : ℝ) + 1) ^ 2)) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact (this.congr fun k => by push_cast; ring).mul_left _
  refine Summable.of_norm_bounded hbase fun k => ?_
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnum : ‖(Y : ℂ) ^ trivialAbscissa k - (Y : ℂ) ^ s₀‖ ≤ M := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY0, Complex.norm_cpow_eq_rpow_re_of_pos hY0,
      trivialAbscissa_re, hM]
    have : Y ^ (-(2 * ((k : ℝ) + 1))) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY.le (by linarith)
    linarith
  have hden : 2 * ((k : ℝ) + 1) ≤ ‖trivialAbscissa k - s₀‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, trivialAbscissa_re, abs_of_neg (by linarith)]
    linarith
  rw [norm_div, norm_pow, div_le_iff₀ (pow_pos (lt_of_lt_of_le (by positivity) hden) 2)]
  calc ‖(Y : ℂ) ^ trivialAbscissa k - (Y : ℂ) ^ s₀‖ ≤ M := hnum
    _ = M / 4 * (1 / ((k : ℝ) + 1) ^ 2) * (2 * ((k : ℝ) + 1)) ^ 2 := by field_simp; ring
    _ ≤ M / 4 * (1 / ((k : ℝ) + 1) ^ 2) * ‖trivialAbscissa k - s₀‖ ^ 2 := by
        gcongr

/-- The centred coordinate `(s₀ − ½)(−i)` of a point. -/
def centredPoint (s₀ : ℂ) : ℂ := (s₀ - 1 / 2) * (-Complex.I)

theorem XiC_centredPoint (s₀ : ℂ) : XiC (centredPoint s₀) = xi s₀ :=
  (xi_eq_XiC_comp s₀).symm

/-- `ρ − s₀ = i (a_q − z₀)` in the centred coordinates. -/
theorem zero_sub_eq_centred (s₀ : ℂ) (q : XiZeroCopy) :
    (q.1 : ℂ) - s₀ = Complex.I * (xiSpectralPoint q - centredPoint s₀) := by
  rw [xiSpectralPoint_eq_support, xiSpectralPointSupport, centredPoint]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem inv_sq_zero_sub_eq (s₀ : ℂ) (q : XiZeroCopy) :
    ((q.1 : ℂ) - s₀) ^ 2 = -((centredPoint s₀ - xiSpectralPoint q) ^ 2) := by
  rw [zero_sub_eq_centred, mul_pow, Complex.I_sq]
  ring

/-- The zero powers `(Y^ρ − Y^{s₀})/(ρ − s₀)²` are summable. -/
theorem summable_zero_pow {Y : ℝ} (hY : 1 < Y) {s₀ : ℂ} (hξ : xi s₀ ≠ 0) :
    Summable (fun q : XiZeroCopy => ((Y : ℂ) ^ (q.1 : ℂ) - (Y : ℂ) ^ s₀) / ((q.1 : ℂ) - s₀) ^ 2) := by
  have hY0 : 0 < Y := by linarith
  have hz : XiC (centredPoint s₀) ≠ 0 := by rw [XiC_centredPoint]; exact hξ
  have hbase := (summable_inv_sq_sub_xiSpectralPoint hz).norm.mul_left (Y + ‖(Y : ℂ) ^ s₀‖)
  refine Summable.of_norm_bounded hbase fun q => ?_
  have hpow : ‖(Y : ℂ) ^ (q.1 : ℂ)‖ ≤ Y := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY0]
    calc Y ^ ((q.1 : ℂ)).re ≤ Y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hY.le (xiZeroCopy_re_lt_one q).le
      _ = Y := Real.rpow_one Y
  have hnum : ‖(Y : ℂ) ^ (q.1 : ℂ) - (Y : ℂ) ^ s₀‖ ≤ Y + ‖(Y : ℂ) ^ s₀‖ :=
    (norm_sub_le ((Y : ℂ) ^ (q.1 : ℂ)) ((Y : ℂ) ^ s₀)).trans (by linarith)
  rw [div_eq_mul_inv, norm_mul, inv_sq_zero_sub_eq, inv_neg, norm_neg]
  exact mul_le_mul_of_nonneg_right hnum (norm_nonneg _)

/-- **Regrouped Cesàro explicit formula.**  For `Y > 1`, `0 < Re s₀ < 1`, `ξ(s₀) ≠ 0`, with
`P = Y^{s₀}` and `L = log Y`,

`Σ_{n ≤ Y} Λ(n)(Y/n)^{s₀} log(Y/n) = P L (A(s₀) − ξ'/ξ(s₀)) + (Y − P)/(1−s₀)²`
`    − Σ_k (Y^{−2k−2} − P)/(−2k−2−s₀)² − Σ_ρ (Y^ρ − P)/(ρ−s₀)²`,

where `A = 1/s + 1/(s−1) + Γ_ℝ'/Γ_ℝ` is the archimedean logarithmic derivative. -/
theorem laguerre_explicit_formula_grouped {Y : ℝ} (hY : 1 < Y) {s₀ : ℂ} (hs₀0 : 0 < s₀.re)
    (hs₀ : s₀.re < 1) (hξ : xi s₀ ≠ 0) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ((vonMangoldt n : ℝ) : ℂ) *
        (((Y / n : ℝ) : ℂ) ^ s₀ * Complex.log ((Y / n : ℝ) : ℂ)) =
      (Y : ℂ) ^ s₀ * Complex.log Y * (archLogDeriv s₀ - logDeriv xi s₀) +
        ((Y : ℂ) - (Y : ℂ) ^ s₀) / (1 - s₀) ^ 2 -
        ∑' k : ℕ, ((Y : ℂ) ^ trivialAbscissa k - (Y : ℂ) ^ s₀) / (trivialAbscissa k - s₀) ^ 2 -
        ∑' q : XiZeroCopy, ((Y : ℂ) ^ (q.1 : ℂ) - (Y : ℂ) ^ s₀) / ((q.1 : ℂ) - s₀) ^ 2 := by
  have hs₁ : (1 : ℂ) - s₀ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hq : ∀ q : XiZeroCopy, (q.1 : ℂ) - s₀ ≠ 0 := by
    intro q h; apply hξ; rw [← sub_eq_zero.mp h]; exact xi_xiZeroCopy_eq_zero q
  have hk : ∀ k : ℕ, trivialAbscissa k - s₀ ≠ 0 := fun k =>
    sub_ne_zero.mpr (s₀_ne_trivialAbscissa hs₀0 k).symm
  set P : ℂ := (Y : ℂ) ^ s₀ with hP
  set L : ℂ := Complex.log Y with hL
  rw [laguerre_explicit_formula_raw hY hs₀0 hs₀ hξ]
  -- the digamma series
  have hksplit : ∀ k : ℕ, (1 / ((k : ℂ) + 2)) * (P * L) - 2 * laguerreDS Y s₀ (trivialAbscissa k) =
      P * L * shiftedDigammaTerm s₀ k -
        2 * (((Y : ℂ) ^ trivialAbscissa k - P) / (trivialAbscissa k - s₀) ^ 2) := by
    intro k
    unfold laguerreDS shiftedDigammaTerm
    have h1 : trivialAbscissa k - s₀ = -(s₀ + 2 * ((k : ℂ) + 1)) := by
      unfold trivialAbscissa; ring
    have h2 : s₀ + 2 * ((k : ℂ) + 1) ≠ 0 := by
      intro h; apply hk k; rw [h1, h, neg_zero]
    rw [← hP, ← hL, h1]
    field_simp
    ring
  have hksum : ∑' k : ℕ, ((1 / ((k : ℂ) + 2)) * (P * L) - 2 * laguerreDS Y s₀ (trivialAbscissa k)) =
      P * L * ∑' k : ℕ, shiftedDigammaTerm s₀ k -
        2 * ∑' k : ℕ, ((Y : ℂ) ^ trivialAbscissa k - P) / (trivialAbscissa k - s₀) ^ 2 := by
    simp_rw [hksplit]
    rw [Summable.tsum_sub ((summable_shiftedDigammaTerm hs₀0).mul_left _)
      ((summable_trivialAbscissa_pow hY hs₀0).mul_left _), tsum_mul_left, tsum_mul_left]
  -- the divisor series
  have hqsplit : ∀ q : XiZeroCopy, ((q.1 : ℂ) - 1 / 2)⁻¹ * (P * L) + laguerreDS Y s₀ (q.1 : ℂ) =
      P * L * (((q.1 : ℂ) - 1 / 2)⁻¹ + (s₀ - (q.1 : ℂ))⁻¹) +
        ((Y : ℂ) ^ (q.1 : ℂ) - P) / ((q.1 : ℂ) - s₀) ^ 2 := by
    intro q
    unfold laguerreDS
    have h1 := hq q
    have h2 : s₀ - (q.1 : ℂ) ≠ 0 := by intro h; apply h1; linear_combination -h
    rw [← hP, ← hL]
    field_simp
    ring
  have hqsum : ∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ * (P * L) + laguerreDS Y s₀ (q.1 : ℂ)) =
      P * L * logDeriv xi s₀ +
        ∑' q : XiZeroCopy, ((Y : ℂ) ^ (q.1 : ℂ) - P) / ((q.1 : ℂ) - s₀) ^ 2 := by
    simp_rw [hqsplit]
    rw [Summable.tsum_add ((summable_partialFractionTerm hξ).mul_left _) (summable_zero_pow hY hξ),
      tsum_mul_left, logDeriv_xi_eq_partialFraction hξ]
  rw [hksum, hqsum]
  have harch := archLogDeriv_eq hs₀0
  unfold laguerreDS
  rw [Complex.cpow_one, ← hP, ← hL, ← harch]
  have h1 : (1 : ℂ) - s₀ ≠ 0 := hs₁
  have h1' : s₀ - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
  field_simp
  ring

/-! ## The order-one slice coefficient against the all-prime Cesàro sum -/

/-- The point `½ + it` of the critical line. -/
def laguerreLinePoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)

theorem laguerreLinePoint_re (t : ℝ) : (laguerreLinePoint t).re = 1 / 2 := by simp [laguerreLinePoint]

theorem centredPoint_laguerreLinePoint (t : ℝ) : centredPoint (laguerreLinePoint t) = t := by
  unfold centredPoint laguerreLinePoint
  ring_nf
  rw [Complex.I_sq]
  ring

theorem xi_laguerreLinePoint (t : ℝ) : xi (laguerreLinePoint t) = XiC t := by
  rw [← XiC_centredPoint, centredPoint_laguerreLinePoint]

/-- The Cesàro prime sum `D_Y(s) = Σ_{n ≤ Y} Λ(n) n^{−s} log(Y/n)`. -/
def cesaroPrimeSum (Y : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ((vonMangoldt n : ℝ) : ℂ) * ((n : ℂ) ^ s)⁻¹ * (Real.log (Y / n) : ℂ)

/-- The archimedean and trivial-zero remainder `(Y^{1−s} − 1)/(1−s)² − Σ_k (Y^{−2k−2−s} − 1)/(s+2k+2)²`. -/
def laguerreRemainder (Y : ℝ) (s : ℂ) : ℂ :=
  ((Y : ℂ) ^ (1 - s) - 1) / (1 - s) ^ 2 -
    ∑' k : ℕ, ((Y : ℂ) ^ (trivialAbscissa k - s) - 1) / (trivialAbscissa k - s) ^ 2

/-- The twisted divisor sum `Σ_ρ Y^{ρ−s}/(ρ−s)²`. -/
def twistedDivisorSum (Y : ℝ) (s : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, (Y : ℂ) ^ ((q.1 : ℂ) - s) / ((q.1 : ℂ) - s) ^ 2

private theorem cpow_div_cpow {Y : ℝ} (hY : 0 < Y) (a b : ℂ) :
    (Y : ℂ) ^ a * ((Y : ℂ) ^ b)⁻¹ = (Y : ℂ) ^ (a - b) := by
  rw [Complex.cpow_sub _ _ (by exact_mod_cast hY.ne'), div_eq_mul_inv]

/-- **The Laguerre explicit formula.**  At a height `t` with `Ξ(t) ≠ 0` and for every `Y > 1`,
the order-one horizontal slice coefficient satisfies

`c₂(t)/Ξ(t)² = log Y · Re A(½+it) − Re D_Y(½+it) − Re Σ_ρ Y^{ρ−s}/(ρ−s)² + Re R_Y(½+it)`,

with `A` the archimedean logarithmic derivative, `D_Y` the Cesàro prime sum and `R_Y` the explicit
archimedean and trivial-zero remainder.  The `ξ'/ξ` term drops out because `ξ'/ξ` is purely
imaginary on the critical line. -/
theorem xiSliceCoeff_two_div_eq_cesaro (t : ℝ) (hΞ : XiC t ≠ 0) {Y : ℝ} (hY : 1 < Y) :
    (xiSliceCoeff t 2 / XiC t ^ 2).re =
      Real.log Y * (archLogDeriv (laguerreLinePoint t)).re - (cesaroPrimeSum Y (laguerreLinePoint t)).re -
        (twistedDivisorSum Y (laguerreLinePoint t)).re + (laguerreRemainder Y (laguerreLinePoint t)).re := by
  set s : ℂ := laguerreLinePoint t with hs
  have hY0 : 0 < Y := by linarith
  have hξ : xi s ≠ 0 := by rw [hs, xi_laguerreLinePoint]; exact hΞ
  have hsre : s.re = 1 / 2 := laguerreLinePoint_re t
  have hgroup := laguerre_explicit_formula_grouped hY (by rw [hsre]; norm_num)
    (by rw [hsre]; norm_num) hξ
  set P : ℂ := (Y : ℂ) ^ s with hP
  have hP0 : P ≠ 0 := by
    rw [hP]; exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hY0.ne'))
  have hq : ∀ q : XiZeroCopy, (q.1 : ℂ) - s ≠ 0 := by
    intro q h; apply hξ; rw [← sub_eq_zero.mp h]; exact xi_xiZeroCopy_eq_zero q
  -- divide the regrouped formula by `P`
  have hdir : (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ((vonMangoldt n : ℝ) : ℂ) *
      (((Y / n : ℝ) : ℂ) ^ s * Complex.log ((Y / n : ℝ) : ℂ))) * P⁻¹ = cesaroPrimeSum Y s := by
    unfold cesaroPrimeSum
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hcp : (((Y / n : ℝ) : ℂ) ^ s) = P * ((n : ℂ) ^ s)⁻¹ := by
      rw [show (Y / n : ℝ) = Y * (n : ℝ)⁻¹ by ring, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hY0.le (by positivity), Complex.ofReal_inv,
        Complex.ofReal_natCast, Complex.inv_cpow _ _ (by
          rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hn0.le]
          exact Real.pi_pos.ne'.symm)]
    rw [hcp, ← Complex.ofReal_log (by positivity)]
    field_simp
  have hk : ∀ k : ℕ, ((Y : ℂ) ^ trivialAbscissa k - P) / (trivialAbscissa k - s) ^ 2 * P⁻¹ =
      ((Y : ℂ) ^ (trivialAbscissa k - s) - 1) / (trivialAbscissa k - s) ^ 2 := by
    intro k
    rw [← cpow_div_cpow hY0, ← hP]
    field_simp
  have hzq : ∀ q : XiZeroCopy, ((Y : ℂ) ^ (q.1 : ℂ) - P) / ((q.1 : ℂ) - s) ^ 2 * P⁻¹ =
      (Y : ℂ) ^ ((q.1 : ℂ) - s) / ((q.1 : ℂ) - s) ^ 2 - (((q.1 : ℂ) - s) ^ 2)⁻¹ := by
    intro q
    rw [← cpow_div_cpow hY0, ← hP]
    have := hq q
    field_simp
  have hsumK := summable_trivialAbscissa_pow hY (s₀ := s) (by rw [hsre]; norm_num)
  have hsumQ := summable_zero_pow hY hξ
  have hz : XiC (centredPoint s) ≠ 0 := by rw [XiC_centredPoint]; exact hξ
  have hinvQ : Summable (fun q : XiZeroCopy => (((q.1 : ℂ) - s) ^ 2)⁻¹) := by
    refine ((summable_inv_sq_sub_xiSpectralPoint hz).neg).congr fun q => ?_
    rw [inv_sq_zero_sub_eq, inv_neg]
  have htwQ : Summable (fun q : XiZeroCopy => (Y : ℂ) ^ ((q.1 : ℂ) - s) / ((q.1 : ℂ) - s) ^ 2) := by
    refine ((hsumQ.mul_right P⁻¹).add hinvQ).congr fun q => ?_
    rw [hzq]; ring
  have hPL : P * Complex.log Y * (archLogDeriv s - logDeriv xi s) * P⁻¹ =
      Complex.log Y * (archLogDeriv s - logDeriv xi s) := by field_simp
  have hY1 : ((Y : ℂ) - P) / (1 - s) ^ 2 * P⁻¹ = ((Y : ℂ) ^ (1 - s) - 1) / (1 - s) ^ 2 := by
    rw [← cpow_div_cpow hY0, Complex.cpow_one, ← hP]
    field_simp
  have hSK : (∑' k : ℕ, ((Y : ℂ) ^ trivialAbscissa k - P) / (trivialAbscissa k - s) ^ 2) * P⁻¹ =
      ∑' k : ℕ, ((Y : ℂ) ^ (trivialAbscissa k - s) - 1) / (trivialAbscissa k - s) ^ 2 := by
    rw [← tsum_mul_right]; exact tsum_congr hk
  have hSQ : (∑' q : XiZeroCopy, ((Y : ℂ) ^ (q.1 : ℂ) - P) / ((q.1 : ℂ) - s) ^ 2) * P⁻¹ =
      (∑' q : XiZeroCopy, (Y : ℂ) ^ ((q.1 : ℂ) - s) / ((q.1 : ℂ) - s) ^ 2) -
        ∑' q : XiZeroCopy, (((q.1 : ℂ) - s) ^ 2)⁻¹ := by
    rw [← tsum_mul_right, ← Summable.tsum_sub htwQ hinvQ]; exact tsum_congr hzq
  have hmain : cesaroPrimeSum Y s = Complex.log Y * (archLogDeriv s - logDeriv xi s) +
      ((Y : ℂ) ^ (1 - s) - 1) / (1 - s) ^ 2 -
      (∑' k : ℕ, ((Y : ℂ) ^ (trivialAbscissa k - s) - 1) / (trivialAbscissa k - s) ^ 2) -
      ((∑' q : XiZeroCopy, (Y : ℂ) ^ ((q.1 : ℂ) - s) / ((q.1 : ℂ) - s) ^ 2) -
        ∑' q : XiZeroCopy, (((q.1 : ℂ) - s) ^ 2)⁻¹) := by
    rw [← hdir, hgroup, ← hPL, ← hY1, ← hSK, ← hSQ]
    ring
  -- the inverse-square divisor sum is the Laguerre quantity
  have hlag : xiSliceCoeff t 2 / XiC t ^ 2 = -∑' q : XiZeroCopy, (((q.1 : ℂ) - s) ^ 2)⁻¹ := by
    rw [xiSliceCoeff_two_eq_laguerre, laguerre_XiC_eq_tsum_inv_sq hΞ]
    have hcent : centredPoint s = (t : ℂ) := by rw [hs, centredPoint_laguerreLinePoint]
    have hfun : (fun q : XiZeroCopy => (((q.1 : ℂ) - s) ^ 2)⁻¹) =
        fun q => -(((t : ℂ) - xiSpectralPoint q) ^ (2 : ℕ))⁻¹ := by
      funext q; rw [inv_sq_zero_sub_eq, hcent, inv_neg]
    rw [hfun, tsum_neg, neg_neg]
    field_simp
  have hre : (logDeriv xi s).re = 0 := by
    rw [logDeriv_apply, hs]
    exact re_logDeriv_xi_criticalLine t
  rw [hlag]
  unfold laguerreRemainder twistedDivisorSum
  have hlogY : Complex.log Y = (Real.log Y : ℂ) := (Complex.ofReal_log hY0.le).symm
  rw [hlogY] at hmain
  have hmre := congrArg Complex.re hmain
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.re_ofReal_mul, hre] at hmre ⊢
  linarith

/-! ## The phase velocity of the Cesàro Euler stage -/

/-- The Cesàro-weighted truncated logarithm of the Euler product,
`Σ_{n ≤ Y} Λ(n) log(Y/n) n^{−s} / (log Y · log n)`. -/
def cesaroStageLog (Y : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ((vonMangoldt n * Real.log (Y / n) / (Real.log Y * Real.log n) : ℝ) : ℂ) *
    (n : ℂ) ^ (-s)

/-- The Cesàro Euler stage half `Γ_ℝ(s) exp(cesaroStageLog Y s)`. -/
def cesaroStageHalf (Y : ℝ) (s : ℂ) : ℂ := Complex.Gammaℝ s * Complex.exp (cesaroStageLog Y s)

theorem hasDerivAt_cesaroStageLog {Y : ℝ} (hY : 1 < Y) (s : ℂ) :
    HasDerivAt (cesaroStageLog Y) (-(cesaroPrimeSum Y s / Real.log Y)) s := by
  have hL : Real.log Y ≠ 0 := (Real.log_pos hY).ne'
  unfold cesaroStageLog cesaroPrimeSum
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h := ((hasDerivAt_neg s).const_cpow (c := (n : ℂ)) (Or.inl hn0)).const_mul
    ((vonMangoldt n * Real.log (Y / n) / (Real.log Y * Real.log n) : ℝ) : ℂ)
  refine h.congr_deriv ?_
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_log (Nat.cast_nonneg n)]
  have hln : Real.log n ≠ 0 ∨ n = 1 := by
    rcases eq_or_ne n 1 with h1 | h1
    · exact Or.inr h1
    · left
      have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      exact (Real.log_pos this).ne'
  rw [hlog, Complex.cpow_neg]
  rcases hln with hln | rfl
  · have hcl : ((Real.log n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hln
    have hYl : ((Real.log Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul]
    field_simp
  · simp

/-- **Phase velocity of the Cesàro Euler stage.**  On the critical line, for `Ξ(t) ≠ 0` and
`Y > 1`, `log Y · Re (A_Y'/A_Y)(½+it) = c₂(t)/Ξ(t)² + Re Σ_ρ Y^{ρ−s}/(ρ−s)² − Re R_Y(½+it)`.
Under RH the first two terms combine to the Fejér sum `Σ_γ (1 − cos((γ−t) log Y))/(γ−t)² ≥ 0`, so
the stage's phase velocity is the Fejér–Weil form at aperture `log Y`, read at height `t`. -/
theorem log_mul_re_logDeriv_cesaroStageHalf (t : ℝ) (hΞ : XiC t ≠ 0) {Y : ℝ} (hY : 1 < Y) :
    Real.log Y * (logDeriv (cesaroStageHalf Y) (laguerreLinePoint t)).re =
      (xiSliceCoeff t 2 / XiC t ^ 2).re + (twistedDivisorSum Y (laguerreLinePoint t)).re -
        (laguerreRemainder Y (laguerreLinePoint t)).re := by
  set s : ℂ := laguerreLinePoint t with hs
  have hsre : 0 < s.re := by rw [hs, laguerreLinePoint_re]; norm_num
  have hL : 0 < Real.log Y := Real.log_pos hY
  have hder : HasDerivAt (fun y => Complex.Gammaℝ y * Complex.exp (cesaroStageLog Y y)) _ s :=
    (hasDerivAt_Gammaℝ_of_re_pos hsre).mul (hasDerivAt_cesaroStageLog hY s).cexp
  have hne : cesaroStageHalf Y s ≠ 0 :=
    mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hsre) (Complex.exp_ne_zero _)
  have hfun : cesaroStageHalf Y = fun y => Complex.Gammaℝ y * Complex.exp (cesaroStageLog Y y) := rfl
  have hld : logDeriv (cesaroStageHalf Y) s =
      (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) - cesaroPrimeSum Y s / Real.log Y := by
    rw [logDeriv_apply, hfun, hder.deriv]
    have hG := Complex.Gammaℝ_ne_zero_of_re_pos hsre
    have hE := Complex.exp_ne_zero (cesaroStageLog Y s)
    have hYl : ((Real.log Y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp
    ring
  have hlag := xiSliceCoeff_two_div_eq_cesaro t hΞ hY
  rw [← hs] at hlag
  have harch : (archLogDeriv s).re =
      (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2).re := by
    unfold archLogDeriv
    rw [logDeriv_Gammaℝ_digamma hsre]
    have hpole : (s⁻¹ + (s - 1)⁻¹).re = 0 := by
      rw [hs, laguerreLinePoint]
      have h1 : (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this
      have h2 : (1 / 2 : ℂ) + Complex.I * (t : ℂ) - 1 ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; norm_num at this
      rw [inv_add_inv h1 h2, Complex.div_re]
      simp [Complex.normSq_apply]
      ring
    simp only [Complex.add_re] at hpole ⊢
    linarith
  rw [hld, Complex.sub_re, Complex.div_ofReal_re, ← harch]
  field_simp
  linarith

end

end RHTower
