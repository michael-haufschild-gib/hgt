import GaloisForLFunctions.RHTower.WeilHerglotzPhaseLockRigidity
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

/-!
# Infinitely many real spectral masses with a rapidly decaying tail force `Λ` and RH

Let `Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`, and suppose that on `Re s > 1`

`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s} = 2(s−½) Σ_j m_j/((s−½)² + t_j²)
  + Σ_k c_k · 2(s−½)/((s−½)² + u_k²)`,

with integer masses `m_j` at ordinates `t_j ≥ 1` (`Σ m_j/t_j² < ∞`) and real masses `c_k ≥ 0` at
ordinates `u_k ≥ 1`, `u_k → ∞`, with `Σ_k c_k u_k^K < ∞` for every `K`.

**Theorem** (`fractional_mass_tail_rigidity`).  Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the
Riemann hypothesis holds.  This extends `FractionalMassRigidity.fractional_mass_rigidity` from
finitely many real masses to infinitely many with a rapidly decaying mass tail.

**Proof.**
* The real atoms exponentiate to the infinite product `R = Π_k ((s−½+iu_k)/u_k)^{c_k}
  ((s−½−iu_k)/u_k)^{c_k}`.  Near the centre each factor equals `exp(c log(1 + (s−½)²/u²))`, so
  `|factor − 1| ≤ 4c|s−½|²/u²`, and every factor is holomorphic on `|Im s| < u`.  Hence the product
  converges locally uniformly, is holomorphic on `Re s > ½` with logarithmic derivative
  `Σ_k c_k·2(s−½)/((s−½)² + u_k²)`, and is continuous on `Re s ≥ ½` (split off the finitely many
  factors whose atoms are nearby).
* On the lower half of the critical line `conj R(½ − iy) = e^{2πiC(y)} R(½ − iy)` with
  `C(y) = Σ_{u_k < y} c_k`: factors above `y` are real, factors below `y` carry `e^{2πic_k}`.
* With `G = K·Q·R` (`Q` the integer-mass product) this gives `G(1 − s) = κ⁻¹G(s) + defect` on the
  lower half-line, `κ⁻¹ = e^{2πiC_∞}`, where the defect is `(e^{2πiC(y)} − e^{2πiC_∞})` times the
  polynomially bounded boundary value.  The mass tail `C_∞ − C(y) ≤ y^{−K}Σ c_k u_k^K` beats the
  polynomial, so the defect is Abel-sublinear and the lock-defect rigidity theorem
  (`PhaseLockRigidity.phase_lock_rigidity_of_defect`) applies.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace FractionalMassTailRigidity

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity

noncomputable section

/-! ### One real-mass factor near its centre -/

theorem fracBase_eq_I_mul {u : ℝ} (hu : 0 < u) (s : ℂ) :
    fracBase u u s = I * (1 - I * (s - 1 / 2) / u) := by
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold fracBase
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem fracBase_neg_eq_neg_I_mul {u : ℝ} (hu : 0 < u) (s : ℂ) :
    fracBase (-u) u s = -I * (1 + I * (s - 1 / 2) / u) := by
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold fracBase
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem abs_arg_lt_of_norm_sub_one_le {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) : |w.arg| < Real.pi / 2 := by
  refine Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ?_)
  have h := Complex.abs_re_le_norm (w - 1)
  rw [Complex.sub_re, Complex.one_re] at h
  have := (abs_le.mp (h.trans hw)).1
  linarith

theorem ne_zero_of_norm_sub_one_le {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) : w ≠ 0 := by
  rintro rfl
  norm_num at hw

/-- **Near its centre a real-mass factor is `exp(c log(1 + (s−½)²/u²))`.** -/
theorem fracPair_eq_exp {c u : ℝ} (hu : 0 < u) {s : ℂ} (hs : ‖s - 1 / 2‖ ≤ u / 2) :
    fracPair c u s = Complex.exp ((c : ℂ) * Complex.log (1 + (s - 1 / 2) ^ 2 / (u : ℂ) ^ 2)) := by
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  set a : ℂ := I * (s - 1 / 2) / u with ha
  have hna : ‖a‖ ≤ 1 / 2 := by
    rw [ha, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hu, div_le_iff₀ hu]
    linarith
  have h1 : ‖(1 - a) - 1‖ ≤ 1 / 2 := by rw [sub_sub_cancel_left, norm_neg]; exact hna
  have h2 : ‖(1 + a) - 1‖ ≤ 1 / 2 := by rw [add_sub_cancel_left]; exact hna
  have hA1 := abs_arg_lt_of_norm_sub_one_le h1
  have hA2 := abs_arg_lt_of_norm_sub_one_le h2
  have hn1 := ne_zero_of_norm_sub_one_le h1
  have hn2 := ne_zero_of_norm_sub_one_le h2
  have hI : (I : ℂ).arg = Real.pi / 2 := Complex.arg_I
  have hnI : (-I : ℂ).arg = -(Real.pi / 2) := Complex.arg_neg_I
  have hl1 : Complex.log (I * (1 - a)) = Complex.log I + Complex.log (1 - a) := by
    refine Complex.log_mul I_ne_zero hn1 ?_
    rw [hI]
    constructor <;> linarith [(abs_lt.mp hA1).1, (abs_lt.mp hA1).2, Real.pi_pos]
  have hl2 : Complex.log (-I * (1 + a)) = Complex.log (-I) + Complex.log (1 + a) := by
    refine Complex.log_mul (neg_ne_zero.mpr I_ne_zero) hn2 ?_
    rw [hnI]
    constructor <;> linarith [(abs_lt.mp hA2).1, (abs_lt.mp hA2).2, Real.pi_pos]
  have hl12 : Complex.log ((1 - a) * (1 + a)) = Complex.log (1 - a) + Complex.log (1 + a) := by
    refine Complex.log_mul hn1 hn2 ?_
    constructor <;> linarith [(abs_lt.mp hA1).1, (abs_lt.mp hA1).2, (abs_lt.mp hA2).1,
      (abs_lt.mp hA2).2, Real.pi_pos]
  have hprod : (1 - a) * (1 + a) = 1 + (s - 1 / 2) ^ 2 / (u : ℂ) ^ 2 := by
    rw [ha]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  unfold fracPair
  rw [fracBase_eq_I_mul hu, fracBase_neg_eq_neg_I_mul hu, ← ha,
    Complex.cpow_def_of_ne_zero (mul_ne_zero I_ne_zero hn1),
    Complex.cpow_def_of_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hn2), hl1, hl2,
    Complex.log_I, Complex.log_neg_I, ← Complex.exp_add, ← hprod, hl12]
  congr 1
  ring

/-- **A real-mass factor is close to `1` near its centre:**
`|R_{c,u}(s) − 1| ≤ 4c|s − ½|²/u²` for `|s − ½| ≤ u/2` and `c|s − ½|²/u² ≤ ½`, `c ≥ 0`. -/
theorem norm_fracPair_sub_one_le {c u : ℝ} (hc0 : 0 ≤ c) (hu : 0 < u) {s : ℂ}
    (hs : ‖s - 1 / 2‖ ≤ u / 2) (hcx : c * (‖s - 1 / 2‖ ^ 2 / u ^ 2) ≤ 1 / 2) :
    ‖fracPair c u s - 1‖ ≤ 4 * c * (‖s - 1 / 2‖ ^ 2 / u ^ 2) := by
  rw [fracPair_eq_exp hu hs]
  set x : ℂ := (s - 1 / 2) ^ 2 / (u : ℂ) ^ 2 with hx
  have hxn : ‖x‖ = ‖s - 1 / 2‖ ^ 2 / u ^ 2 := by
    rw [hx, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have hx4 : ‖x‖ ≤ 1 / 4 := by
    rw [hxn, div_le_iff₀ (by positivity)]
    have h0 := norm_nonneg (s - 1 / 2)
    nlinarith
  have hlog : ‖Complex.log (1 + x)‖ ≤ 2 * ‖x‖ := by
    have h := Complex.norm_log_one_add_le (z := x) (by linarith)
    have hx0 := norm_nonneg x
    have hinv : (1 - ‖x‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    have : ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 ≤ ‖x‖ := by
      have h2 : ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ ≤ ‖x‖ ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      nlinarith
    linarith
  have hcl : ‖(c : ℂ) * Complex.log (1 + x)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    calc c * ‖Complex.log (1 + x)‖ ≤ c * (2 * ‖x‖) := mul_le_mul_of_nonneg_left hlog hc0
      _ = 2 * (c * ‖x‖) := by ring
      _ ≤ 1 := by rw [hxn]; linarith
  calc ‖Complex.exp ((c : ℂ) * Complex.log (1 + x)) - 1‖
      ≤ 2 * ‖(c : ℂ) * Complex.log (1 + x)‖ := Complex.norm_exp_sub_one_le hcl
    _ ≤ 2 * (c * (2 * ‖x‖)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
        gcongr
    _ = 4 * c * (‖s - 1 / 2‖ ^ 2 / u ^ 2) := by rw [hxn]; ring

/-! ### Holomorphy of a factor away from its atoms -/

theorem fracBase_im (σ u : ℝ) (s : ℂ) : (fracBase σ u s).im = (s.im + σ) / u := by
  unfold fracBase
  rw [Complex.div_ofReal_im]
  simp

theorem fracBase_mem_slitPlane {σ u : ℝ} (hu : 0 < u) {s : ℂ} (h : s.im + σ ≠ 0) :
    fracBase σ u s ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  rw [fracBase_im]
  exact div_ne_zero h hu.ne'

/-- Every real-mass factor is holomorphic on the horizontal band `|Im s| < u`. -/
theorem hasDerivAt_fracPair_of_abs_im_lt {c u : ℝ} (hu : 0 < u) {s : ℂ} (hs : |s.im| < u) :
    DifferentiableAt ℂ (fracPair c u) s := by
  have h1 : s.im + u ≠ 0 := by have := (abs_lt.mp hs).1; linarith
  have h2 : s.im + -u ≠ 0 := by have := (abs_lt.mp hs).2; linarith
  have d1 := hasDerivAt_fracBase_cpow (c := c) hu (fracBase_mem_slitPlane hu h1)
  have d2 := hasDerivAt_fracBase_cpow (c := c) hu (fracBase_mem_slitPlane hu h2)
  exact (d1.mul d2).differentiableAt

theorem differentiableAt_fracPair_of_half_lt {c u : ℝ} (hu : 0 < u) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fracPair c u) s :=
  (hasDerivAt_fracPair (c := c) hu hs).differentiableAt

/-! ### The infinite product -/

/-- The infinite product of the real-mass factors. -/
def fracInfProd (c u : ℕ → ℝ) (s : ℂ) : ℂ := ∏' k, fracPair (c k) (u k) s

section Product

variable {c u : ℕ → ℝ}

theorem summable_div_sq_of_summable (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hcs : Summable c) : Summable fun k => c k / u k ^ 2 :=
  hcs.of_nonneg_of_le (fun k => div_nonneg (hc k) (by positivity))
    fun k => div_le_self (hc k) (one_le_pow₀ (hu1 k))

theorem eventually_lt_and_small (hut : Tendsto u atTop atTop)
    (hcs : Summable fun k => c k / u k ^ 2) (B ρ : ℝ) :
    ∀ᶠ k in atTop, B < u k ∧ c k / u k ^ 2 * ρ ^ 2 ≤ 1 / 2 := by
  have h := hcs.tendsto_atTop_zero.mul_const (ρ ^ 2)
  rw [zero_mul] at h
  exact (hut.eventually (eventually_gt_atTop B)).and (h.eventually (ge_mem_nhds (by norm_num)))

/-- The factor bound at an index `k` with `2ρ < u_k` and `c_k ρ²/u_k² ≤ ½`. -/
theorem norm_fracPair_sub_one_le_of_small {c' u' ρ : ℝ} (hc : 0 ≤ c') (hu : 0 < u')
    (hk : 2 * ρ < u' ∧ c' / u' ^ 2 * ρ ^ 2 ≤ 1 / 2) {s : ℂ} (hs : ‖s - 1 / 2‖ ≤ ρ) :
    ‖fracPair c' u' s - 1‖ ≤ 4 * ρ ^ 2 * (c' / u' ^ 2) := by
  have h2 : ‖s - 1 / 2‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  have hcu : 0 ≤ c' / u' ^ 2 := div_nonneg hc (by positivity)
  have e : c' * (‖s - 1 / 2‖ ^ 2 / u' ^ 2) = c' / u' ^ 2 * ‖s - 1 / 2‖ ^ 2 := by ring
  have hcx : c' * (‖s - 1 / 2‖ ^ 2 / u' ^ 2) ≤ 1 / 2 := by
    rw [e]; exact (mul_le_mul_of_nonneg_left h2 hcu).trans hk.2
  have h := norm_fracPair_sub_one_le hc hu (s := s) (by linarith [hk.1]) hcx
  calc ‖fracPair c' u' s - 1‖ ≤ 4 * c' * (‖s - 1 / 2‖ ^ 2 / u' ^ 2) := h
    _ = 4 * (c' / u' ^ 2) * ‖s - 1 / 2‖ ^ 2 := by ring
    _ ≤ 4 * (c' / u' ^ 2) * ρ ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 4 * ρ ^ 2 * (c' / u' ^ 2) := by ring

theorem eventually_norm_fracPair_sub_one_le (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) (ρ : ℝ) :
    ∀ᶠ k in atTop, ∀ s : ℂ, ‖s - 1 / 2‖ ≤ ρ →
      ‖fracPair (c k) (u k) s - 1‖ ≤ 4 * ρ ^ 2 * (c k / u k ^ 2) := by
  filter_upwards [eventually_lt_and_small hut hcs (2 * ρ) ρ] with k hk s hs
  exact norm_fracPair_sub_one_le_of_small (hc k) (lt_of_lt_of_le one_pos (hu1 k)) hk hs

theorem summable_fracPair_sub_one (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) (s : ℂ) :
    Summable fun k => fracPair (c k) (u k) s - 1 := by
  refine Summable.of_norm_bounded_eventually (hcs.mul_left (4 * ‖s - 1 / 2‖ ^ 2)) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_norm_fracPair_sub_one_le hc hu1 hut hcs ‖s - 1 / 2‖]
    with k hk
  exact hk s le_rfl

theorem multipliable_fracPair (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) (s : ℂ) :
    Multipliable fun k => fracPair (c k) (u k) s := by
  simpa using Complex.multipliable_one_add_of_summable
    (summable_fracPair_sub_one hc hu1 hut hcs s)

/-- The tail of the product past the first `N` factors. -/
def tailTerm (c u : ℕ → ℝ) (N k : ℕ) (s : ℂ) : ℂ :=
  if k < N then 0 else fracPair (c k) (u k) s - 1

/-- **Head–tail splitting** of the product. -/
theorem fracInfProd_eq_head_mul (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) (N : ℕ) (s : ℂ) :
    fracInfProd c u s = (∏ k ∈ Finset.range N, fracPair (c k) (u k) s) *
      ∏' k, (1 + tailTerm c u N k s) := by
  have hpt : (fun k => fracPair (c k) (u k) s) = fun k =>
      (if k < N then fracPair (c k) (u k) s else 1) * (1 + tailTerm c u N k s) := by
    funext k
    unfold tailTerm
    split_ifs <;> ring
  have hm1 : Multipliable fun k => (if k < N then fracPair (c k) (u k) s else 1) :=
    multipliable_of_ne_finset_one (s := Finset.range N) fun k hk => by
      rw [Finset.mem_range] at hk; rw [if_neg hk]
  have hm2 : Multipliable fun k => 1 + tailTerm c u N k s := by
    refine Complex.multipliable_one_add_of_summable ?_
    refine (summable_fracPair_sub_one hc hu1 hut hcs s).congr_cofinite ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with k hk
    unfold tailTerm
    rw [if_neg (not_lt.mpr hk)]
  unfold fracInfProd
  calc ∏' k, fracPair (c k) (u k) s
      = ∏' k, ((if k < N then fracPair (c k) (u k) s else 1) * (1 + tailTerm c u N k s)) :=
        tprod_congr fun k => congrFun hpt k
    _ = (∏' k, (if k < N then fracPair (c k) (u k) s else 1)) *
          ∏' k, (1 + tailTerm c u N k s) := hm1.tprod_mul hm2
    _ = _ := by
        rw [tprod_eq_prod (s := Finset.range N) fun k hk => by
          rw [Finset.mem_range] at hk; rw [if_neg hk]]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Finset.mem_range] at hk; rw [if_pos hk]

end Product

/-- `|c·2z/(z² + u²)| ≤ 3|z|·c/u²` for `|z| ≤ u/2`, `u > 0`. -/
theorem norm_fracTerm_le_div {c u : ℝ} (hc : 0 ≤ c) (hu0 : 0 < u) {s : ℂ}
    (hs : ‖s - 1 / 2‖ ≤ u / 2) : ‖fracTerm c u s‖ ≤ 3 * ‖s - 1 / 2‖ * (c / u ^ 2) := by
  set z := s - 1 / 2 with hz
  have hz0 := norm_nonneg z
  have hden : 3 / 4 * u ^ 2 ≤ ‖z ^ 2 + (u : ℂ) ^ 2‖ := by
    have h1 : ‖(u : ℂ) ^ 2‖ = u ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
    have h2 : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
    have h3 := norm_sub_norm_le ((u : ℂ) ^ 2) (-(z ^ 2))
    rw [norm_neg, sub_neg_eq_add, add_comm] at h3
    have h4 : ‖z‖ ^ 2 ≤ u ^ 2 / 4 := by nlinarith
    rw [h1, h2] at h3
    linarith
  have hpos : 0 < 3 / 4 * u ^ 2 := by positivity
  have hu2 : 0 < u ^ 2 := by positivity
  unfold fracTerm
  rw [← hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, norm_div, norm_mul,
    Complex.norm_two]
  have hq : 2 * ‖z‖ / ‖z ^ 2 + (u : ℂ) ^ 2‖ ≤ 3 * ‖z‖ / u ^ 2 := by
    rw [div_le_div_iff₀ (lt_of_lt_of_le hpos hden) hu2]
    nlinarith
  calc c * (2 * ‖z‖ / ‖z ^ 2 + (u : ℂ) ^ 2‖) ≤ c * (3 * ‖z‖ / u ^ 2) :=
        mul_le_mul_of_nonneg_left hq hc
    _ = 3 * ‖z‖ * (c / u ^ 2) := by ring

section Analytic

variable {c u : ℕ → ℝ}

/-- **Continuity of the tail product** near any point. -/
theorem exists_continuousAt_tail (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) (s₀ : ℂ) :
    ∃ N : ℕ, ContinuousAt (fun s => ∏' k, (1 + tailTerm c u N k s)) s₀ := by
  set ρ : ℝ := ‖s₀ - 1 / 2‖ + 1 with hρ
  set B : ℝ := 2 * ρ + |s₀.im| + 1 with hB
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_and_small hut hcs B ρ)
  refine ⟨N, ?_⟩
  set K := Metric.closedBall s₀ 1 with hKdef
  have hK : IsCompact K := isCompact_closedBall s₀ 1
  have hxK : ∀ x ∈ K, ‖x - 1 / 2‖ ≤ ρ ∧ |x.im| ≤ |s₀.im| + 1 := by
    intro x hx
    rw [hKdef, Metric.mem_closedBall, dist_eq_norm] at hx
    constructor
    · calc ‖x - 1 / 2‖ = ‖(x - s₀) + (s₀ - 1 / 2)‖ := by ring_nf
        _ ≤ ‖x - s₀‖ + ‖s₀ - 1 / 2‖ := norm_add_le _ _
        _ ≤ ρ := by rw [hρ]; linarith
    · have h1 := Complex.abs_im_le_norm (x - s₀)
      rw [Complex.sub_im] at h1
      have h2 := abs_sub_abs_le_abs_sub x.im s₀.im
      linarith
  have hu0 : ∀ k, 0 < u k := fun k => lt_of_lt_of_le one_pos (hu1 k)
  have hcont : ∀ k, ContinuousOn (tailTerm c u N k) K := by
    intro k
    by_cases hk : k < N
    · have : tailTerm c u N k = fun _ => 0 := funext fun s => by unfold tailTerm; rw [if_pos hk]
      rw [this]; exact continuousOn_const
    · have hk' := hN k (not_lt.mp hk)
      have : tailTerm c u N k = fun s => fracPair (c k) (u k) s - 1 :=
        funext fun s => by unfold tailTerm; rw [if_neg hk]
      rw [this]
      intro x hx
      have him : |x.im| < u k := by
        have := (hxK x hx).2
        have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
        linarith [hk'.1]
      exact ((hasDerivAt_fracPair_of_abs_im_lt (c := c k) (hu0 k) him).continuousAt.sub
        continuousAt_const).continuousWithinAt
  have hB2 : 2 * ρ ≤ B := by rw [hB]; linarith [abs_nonneg s₀.im]
  have hbound : ∀ k, ∀ x ∈ K, ‖tailTerm c u N k x‖ ≤ 4 * ρ ^ 2 * (c k / u k ^ 2) := by
    intro k x hx
    unfold tailTerm
    split_ifs with hk
    · rw [norm_zero]; exact mul_nonneg (by positivity) (div_nonneg (hc k) (by positivity))
    · have hk' := hN k (not_lt.mp hk)
      exact norm_fracPair_sub_one_le_of_small (hc k) (hu0 k) ⟨by linarith [hk'.1], hk'.2⟩
        (hxK x hx).1
  have hprod := Summable.hasProdUniformlyOn_one_add hK (hcs.mul_left (4 * ρ ^ 2))
    (Eventually.of_forall fun k x hx => hbound k x hx) hcont
  have hco : ContinuousOn (fun s => ∏' k, (1 + tailTerm c u N k s)) K := by
    rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at hprod
    refine hprod.continuousOn (Frequently.of_forall fun S => ?_)
    exact continuousOn_finsetProd S fun k _ => continuousOn_const.add (hcont k)
  exact hco.continuousAt (Metric.closedBall_mem_nhds s₀ one_pos)

/-- **The real-mass product is continuous on `Re s ≥ ½`.** -/
theorem continuousAt_fracInfProd (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) {s₀ : ℂ} (hs₀ : 1 / 2 ≤ s₀.re) :
    ContinuousAt (fracInfProd c u) s₀ := by
  obtain ⟨N, hN⟩ := exists_continuousAt_tail hc hu1 hut hcs s₀
  have heq : fracInfProd c u = fun s => (∏ k ∈ Finset.range N, fracPair (c k) (u k) s) *
      ∏' k, (1 + tailTerm c u N k s) :=
    funext (fracInfProd_eq_head_mul hc hu1 hut hcs N)
  rw [heq]
  refine ContinuousAt.mul ?_ hN
  exact tendsto_finsetProd _ fun k _ =>
    continuousAt_fracPair (hc k) (lt_of_lt_of_le one_pos (hu1 k)) hs₀

/-- Uniform convergence of the product on compact subsets of `Re s > ½`. -/
theorem hasProdUniformlyOn_fracPair (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) {S : Set ℂ} (hS : IsCompact S)
    (hSU : S ⊆ {s : ℂ | 1 / 2 < s.re}) :
    HasProdUniformlyOn (fun k s => fracPair (c k) (u k) s) (fracInfProd c u) S := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hS.isBounded
  set ρ : ℝ := R + 1 with hρ
  have hxS : ∀ x ∈ S, ‖x - 1 / 2‖ ≤ ρ := fun x hx => by
    calc ‖x - 1 / 2‖ ≤ ‖x‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ ρ := by rw [hρ]; have := hR x hx; norm_num; linarith
  have h := Summable.hasProdUniformlyOn_one_add hS (hcs.mul_left (4 * ρ ^ 2))
    (f := fun k s => fracPair (c k) (u k) s - 1) ?_ fun k x hx =>
      ((differentiableAt_fracPair_of_half_lt (c := c k) (lt_of_lt_of_le one_pos (hu1 k))
        (hSU hx)).continuousAt.sub continuousAt_const).continuousWithinAt
  · simp only [add_sub_cancel] at h
    exact h
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_norm_fracPair_sub_one_le hc hu1 hut hcs ρ] with k hk x hx
    exact hk x (hxS x hx)

theorem hasProdLocallyUniformlyOn_fracPair (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) :
    HasProdLocallyUniformlyOn (fun k s => fracPair (c k) (u k) s) (fracInfProd c u)
      {s : ℂ | 1 / 2 < s.re} :=
  hasProdLocallyUniformlyOn_of_forall_compact (isOpen_lt continuous_const Complex.continuous_re)
    fun _ hSU hS => hasProdUniformlyOn_fracPair hc hu1 hut hcs hS hSU

theorem differentiableOn_fracInfProd (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) :
    DifferentiableOn ℂ (fracInfProd c u) {s : ℂ | 1 / 2 < s.re} :=
  (hasProdLocallyUniformlyOn_fracPair hc hu1 hut hcs).differentiableOn
    (.of_forall fun S => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (u := S)
        (s := {s : ℂ | 1 / 2 < s.re}) fun k _ z hz =>
          (differentiableAt_fracPair_of_half_lt (c := c k)
            (lt_of_lt_of_le one_pos (hu1 k)) hz).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

theorem fracInfProd_ne_zero (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) {s : ℂ} (hs : 1 / 2 < s.re) :
    fracInfProd c u s ≠ 0 := by
  have hu0 : ∀ k, 0 < u k := fun k => lt_of_lt_of_le one_pos (hu1 k)
  set ρ := ‖s - 1 / 2‖ with hρ
  have hsmall : ∀ᶠ k in atTop, 4 * ρ ^ 2 * (c k / u k ^ 2) ≤ 1 / 2 := by
    have h := hcs.tendsto_atTop_zero.const_mul (4 * ρ ^ 2)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  have hlog : Summable fun k => Complex.log (fracPair (c k) (u k) s) := by
    refine Summable.of_norm_bounded_eventually (hcs.mul_left (8 * ρ ^ 2)) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_norm_fracPair_sub_one_le hc hu1 hut hcs ρ, hsmall] with k hk hk2
    have hz := (hk s le_rfl).trans hk2
    set z := fracPair (c k) (u k) s - 1 with hzdef
    have hz0 := norm_nonneg z
    have h := Complex.norm_log_one_add_le (z := z) (by linarith)
    rw [hzdef, add_sub_cancel] at h
    have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    have h2 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ := by
      have := mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖z‖)
      nlinarith
    calc ‖Complex.log (fracPair (c k) (u k) s)‖ ≤ 2 * ‖z‖ := by linarith
      _ ≤ 2 * (4 * ρ ^ 2 * (c k / u k ^ 2)) := by linarith [hk s le_rfl]
      _ = 8 * ρ ^ 2 * (c k / u k ^ 2) := by ring
  have h := Complex.cexp_tsum_eq_tprod (fun k => fracPair_ne_zero (c := c k) (hu0 k) hs) hlog
  unfold fracInfProd
  rw [← h]
  exact Complex.exp_ne_zero _

theorem logDeriv_fracPair {c' u' : ℝ} (hu : 0 < u') {s : ℂ} (hs : 1 / 2 < s.re) :
    logDeriv (fracPair c' u') s = fracTerm c' u' s := by
  rw [logDeriv_apply, (hasDerivAt_fracPair (c := c') hu hs).deriv,
    mul_div_cancel_left₀ _ (fracPair_ne_zero hu hs)]

theorem summable_fracTerm (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) (s : ℂ) :
    Summable fun k => fracTerm (c k) (u k) s := by
  refine Summable.of_norm_bounded_eventually (hcs.mul_left (3 * ‖s - 1 / 2‖)) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hut.eventually (eventually_ge_atTop (2 * ‖s - 1 / 2‖))] with k hk
  exact norm_fracTerm_le_div (hc k) (lt_of_lt_of_le one_pos (hu1 k)) (by linarith)

/-- **The logarithmic derivative of the real-mass product** on `Re s > ½`. -/
theorem hasDerivAt_fracInfProd (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (fracInfProd c u) (fracInfProd c u s * ∑' k, fracTerm (c k) (u k) s) s := by
  have hu0 : ∀ k, 0 < u k := fun k => lt_of_lt_of_le one_pos (hu1 k)
  have hU : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableAt ℂ (fracInfProd c u) s :=
    (differentiableOn_fracInfProd hc hu1 hut hcs).differentiableAt (hU.mem_nhds hs)
  have hne := fracInfProd_ne_zero hc hu1 hut hcs hs
  have hL : logDeriv (fracInfProd c u) s = ∑' k, fracTerm (c k) (u k) s := by
    have h := logDeriv_tprod_eq_tsum hU hs (f := fun k => fracPair (c k) (u k))
      (fun k => fracPair_ne_zero (hu0 k) hs)
      (fun k z hz => (differentiableAt_fracPair_of_half_lt (c := c k) (hu0 k)
        hz).differentiableWithinAt)
      (by simpa only [logDeriv_fracPair (hu0 _) hs] using summable_fracTerm hc hu1 hut hcs s)
      ⟨_, hasProdLocallyUniformlyOn_fracPair hc hu1 hut hcs⟩ hne
    rw [show fracInfProd c u = fun x => ∏' k, fracPair (c k) (u k) x from rfl, h]
    exact tsum_congr fun k => logDeriv_fracPair (hu0 k) hs
  rw [logDeriv_apply, div_eq_iff hne] at hL
  exact hd.hasDerivAt.congr_deriv (by rw [hL]; ring)

end Analytic

/-! ### Phases on the critical line -/

/-- `(−i b)^c = b^c e^{−iπc/2}` for `b > 0`. -/
theorem cpow_neg_I_mul_ofReal {b : ℝ} (hb : 0 < b) (c : ℝ) :
    (-I * (b : ℂ)) ^ (c : ℂ) =
      ((b ^ c : ℝ) : ℂ) * Complex.exp (((-(Real.pi * c / 2)) : ℝ) * I) := by
  have hne : -I * (b : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (by exact_mod_cast hb.ne')
  have hlog : Complex.log (-I * (b : ℂ)) = (Real.log b : ℂ) + ((-(Real.pi / 2)) : ℝ) * I := by
    apply Complex.ext
    · rw [Complex.log_re]; simp [abs_of_pos hb]
    · rw [Complex.log_im]
      have : (-I * (b : ℂ)).arg = -(Real.pi / 2) :=
        Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨by simp, by simp [hb]⟩
      rw [this]; simp
  rw [Complex.cpow_def_of_ne_zero hne, hlog, Real.rpow_def_of_pos hb, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- **Below its atom a real-mass factor is real on the line:** `conj R(½ + iy) = R(½ + iy)` for
`0 ≤ y ≤ u`. -/
theorem conj_fracPair_of_le {c u : ℝ} (hc : 0 ≤ c) (hu : 0 < u) {y : ℝ} (hy0 : 0 ≤ y)
    (hyu : y ≤ u) :
    starRingEnd ℂ (fracPair c u (1 / 2 + y * I)) = fracPair c u (1 / 2 + y * I) := by
  have hb1 : fracBase u u (1 / 2 + y * I) = I * (((y + u) / u : ℝ) : ℂ) := by
    unfold fracBase; push_cast; field_simp; ring
  have hp1 : 0 < (y + u) / u := div_pos (by linarith) hu
  rcases eq_or_lt_of_le hyu with hyu' | hyu'
  · have hb2 : fracBase (-u) u (1 / 2 + y * I) = 0 := by
      unfold fracBase; rw [hyu']; push_cast; ring
    unfold fracPair
    rw [hb2, hb1, cpow_I_mul_ofReal hp1]
    rcases eq_or_lt_of_le hc with hc0 | hc0
    · subst hc0
      simp
    · rw [Complex.zero_cpow (by exact_mod_cast hc0.ne'), mul_zero, map_zero]
  · have hb2 : fracBase (-u) u (1 / 2 + y * I) = -I * (((u - y) / u : ℝ) : ℂ) := by
      unfold fracBase; push_cast; field_simp; ring
    have hp2 : 0 < (u - y) / u := div_pos (by linarith) hu
    unfold fracPair
    rw [hb1, hb2, cpow_I_mul_ofReal hp1, cpow_neg_I_mul_ofReal hp2]
    set A : ℂ := ((((y + u) / u) ^ c : ℝ) : ℂ) with hA
    set B : ℂ := ((((u - y) / u) ^ c : ℝ) : ℂ) with hB
    have e : Complex.exp (((Real.pi * c / 2 : ℝ) : ℂ) * I) *
        Complex.exp (((-(Real.pi * c / 2)) : ℝ) * I) = 1 := by
      rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
    have hreal : A * Complex.exp (((Real.pi * c / 2 : ℝ) : ℂ) * I) *
        (B * Complex.exp (((-(Real.pi * c / 2)) : ℝ) * I)) =
        ((((y + u) / u) ^ c * ((u - y) / u) ^ c : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, ← hA, ← hB]
      linear_combination (A * B) * e
    rw [hreal, Complex.conj_ofReal]

/-- **The phase of one real-mass factor on the lower half-line.**  For `y > 0`,
`conj R(½ − iy) = e^{2πic} R(½ − iy)` if `u < y`, and `= R(½ − iy)` otherwise. -/
theorem conj_fracPair_lower {c u : ℝ} (hc : 0 ≤ c) (hu : 0 < u) {y : ℝ} (hy : 0 < y) :
    starRingEnd ℂ (fracPair c u (1 / 2 - y * I)) =
      (if u < y then Complex.exp (((2 * Real.pi * c : ℝ) : ℂ) * I) else 1) *
        fracPair c u (1 / 2 - y * I) := by
  have hs : (1 / 2 : ℝ) ≤ ((1 / 2 : ℂ) + y * I).re := by simp
  have hconj : (1 / 2 : ℂ) - y * I = starRingEnd ℂ ((1 / 2 : ℂ) + y * I) := by
    apply Complex.ext <;> simp
  rw [hconj, fracPair_conj hu hs, Complex.conj_conj]
  split_ifs with huy
  · have h := conj_fracPair_of_gt (c := c) hu huy
    rw [h, ← mul_assoc, ← Complex.exp_add]
    have : ((2 * Real.pi * c : ℝ) : ℂ) * I + -((2 * Real.pi * c : ℝ) : ℂ) * I = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
  · rw [conj_fracPair_of_le hc hu hy.le (not_lt.mp huy), one_mul]

section Phase

variable {c u : ℕ → ℝ}

/-- `R(s̄) = conj R(s)` on `Re s ≥ ½`. -/
theorem fracInfProd_conj (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    fracInfProd c u (starRingEnd ℂ s) = starRingEnd ℂ (fracInfProd c u s) := by
  unfold fracInfProd
  rw [(multipliable_fracPair hc hu1 hut hcs s).map_tprod (starRingEnd ℂ) Complex.continuous_conj]
  exact tprod_congr fun k => fracPair_conj (lt_of_lt_of_le one_pos (hu1 k)) hs

/-- The real mass below height `y`: `C(y) = Σ_{u_k < y} c_k`. -/
def phaseSum (c u : ℕ → ℝ) (y : ℝ) : ℝ := ∑' k, if u k < y then c k else 0

/-- Only finitely many atoms lie below any height. -/
theorem summable_phaseTerm (hut : Tendsto u atTop atTop) (y : ℝ) :
    Summable fun k => if u k < y then c k else 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hut.eventually (eventually_ge_atTop y))
  exact summable_of_ne_finset_zero (s := Finset.range N) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk; rw [if_neg (not_lt.mpr (hN k hk))]

theorem phaseSum_mono (hc : ∀ k, 0 ≤ c k) (hut : Tendsto u atTop atTop) :
    Monotone (phaseSum c u) :=
  fun y₁ y₂ h => (summable_phaseTerm hut y₁).tsum_le_tsum (fun k => by
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (lt_of_lt_of_le h1 h) h2
    · exact hc k
    · exact le_rfl) (summable_phaseTerm hut y₂)

/-- **The phase of the real-mass product on the lower half-line:**
`conj R(½ − iy) = e^{2πiC(y)} R(½ − iy)`. -/
theorem conj_fracInfProd_lower (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) {y : ℝ} (hy : 0 < y) :
    starRingEnd ℂ (fracInfProd c u (1 / 2 - y * I)) =
      Complex.exp (((2 * Real.pi * phaseSum c u y : ℝ) : ℂ) * I) *
        fracInfProd c u (1 / 2 - y * I) := by
  have hu0 : ∀ k, 0 < u k := fun k => lt_of_lt_of_le one_pos (hu1 k)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hut.eventually (eventually_ge_atTop y))
  set ω : ℕ → ℂ := fun k => if u k < y then Complex.exp (((2 * Real.pi * c k : ℝ) : ℂ) * I) else 1
    with hω
  have hω1 : ∀ k ∉ Finset.range N, ω k = 1 := fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    simp only [hω, if_neg (not_lt.mpr (hN k hk))]
  have hmω : Multipliable ω := multipliable_of_ne_finset_one hω1
  set s : ℂ := 1 / 2 - y * I
  have hmf := multipliable_fracPair hc hu1 hut hcs s
  have hsum : phaseSum c u y = ∑ k ∈ Finset.range N, if u k < y then c k else 0 :=
    tsum_eq_sum fun k hk => by
      rw [Finset.mem_range, not_lt] at hk; rw [if_neg (not_lt.mpr (hN k hk))]
  unfold fracInfProd
  rw [hmf.map_tprod (starRingEnd ℂ) Complex.continuous_conj]
  calc ∏' k, starRingEnd ℂ (fracPair (c k) (u k) s)
      = ∏' k, (ω k * fracPair (c k) (u k) s) :=
        tprod_congr fun k => conj_fracPair_lower (hc k) (hu0 k) hy
    _ = (∏' k, ω k) * ∏' k, fracPair (c k) (u k) s := hmω.tprod_mul hmf
    _ = _ := by
        rw [tprod_eq_prod hω1, hsum, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul,
          Complex.exp_sum]
        congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [hω]
        split_ifs
        · rfl
        · simp

/-- **The mass tail:** `0 ≤ C_∞ − C(y) ≤ y^{−K} Σ_k c_k u_k^K`. -/
theorem tsum_sub_phaseSum_le (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hcs : Summable c)
    {K : ℕ} (hcK : Summable fun k => c k * u k ^ K) {y : ℝ} (hy : 0 < y) :
    0 ≤ (∑' k, c k) - phaseSum c u y ∧
      (∑' k, c k) - phaseSum c u y ≤ (∑' k, c k * u k ^ K) / y ^ K := by
  have hsp : Summable fun k => if u k < y then c k else 0 :=
    hcs.of_nonneg_of_le (fun k => by split_ifs; exacts [hc k, le_rfl])
      fun k => by split_ifs; exacts [le_rfl, hc k]
  have hdiff : (∑' k, c k) - phaseSum c u y = ∑' k, if u k < y then 0 else c k := by
    unfold phaseSum
    rw [← hcs.tsum_sub hsp]
    exact tsum_congr fun k => by split_ifs <;> ring
  have hst : Summable fun k => if u k < y then (0 : ℝ) else c k :=
    hcs.of_nonneg_of_le (fun k => by split_ifs; exacts [le_rfl, hc k])
      fun k => by split_ifs; exacts [hc k, le_rfl]
  rw [hdiff]
  refine ⟨tsum_nonneg fun k => by split_ifs; exacts [le_rfl, hc k], ?_⟩
  rw [← tsum_div_const]
  refine hst.tsum_le_tsum (fun k => ?_) (hcK.div_const _)
  split_ifs with h
  · exact div_nonneg (mul_nonneg (hc k) (pow_nonneg (by linarith [hu1 k]) _)) (by positivity)
  · rw [le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy.le (not_lt.mp h) K) (hc k)

end Phase

/-- `|e^{ia} − e^{ib}| ≤ 2|a − b|`. -/
theorem norm_cexp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I)‖ ≤ 2 * |a - b| := by
  have hsplit : Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I) =
      Complex.exp ((b : ℂ) * I) * (Complex.exp (((a - b : ℝ) : ℂ) * I) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; push_cast; ring_nf
  rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  by_cases h : |a - b| ≤ 1
  · have h1 : ‖((a - b : ℝ) : ℂ) * I‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact h
    calc ‖Complex.exp (((a - b : ℝ) : ℂ) * I) - 1‖ ≤ 2 * ‖((a - b : ℝ) : ℂ) * I‖ :=
          Complex.norm_exp_sub_one_le h1
      _ = 2 * |a - b| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · push Not at h
    calc ‖Complex.exp (((a - b : ℝ) : ℂ) * I) - 1‖
        ≤ ‖Complex.exp (((a - b : ℝ) : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
      _ ≤ 2 * |a - b| := by linarith

/-! ### Abel sublinearity of a decaying defect -/

theorem integral_exp_neg_mul_abs_tail {δ : ℝ} (hδ : 0 < δ) :
    ∫ x : ℝ, Real.exp (-(δ * |x|)) = 2 / δ := by
  have h := integral_comp_abs (f := fun y : ℝ => Real.exp (-(δ * y)))
  rw [h]
  have h2 := integral_exp_mul_Ioi (a := -δ) (by linarith) 0
  have e : (fun x : ℝ => Real.exp (-(δ * x))) = fun x => Real.exp (-δ * x) := by
    funext x; ring_nf
  rw [e, h2]; simp; field_simp

/-- **A bounded defect decaying like `1/|t|` is Abel-sublinear.** -/
theorem tendsto_mul_abelMass_of_decay {g : ℝ → ℂ} {M A : ℝ} (hM : ∀ t, ‖g t‖ ≤ M) (hA : ∀ t, 1 ≤ |t| → ‖g t‖ ≤ A / |t|) :
    Tendsto (fun δ => δ * HamburgerStability.abelMass g δ) (𝓝[>] 0) (𝓝 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hA0 : 0 ≤ A := by
    have h := hA 1 (by norm_num)
    rw [abs_one, div_one] at h
    exact (norm_nonneg _).trans h
  -- `0 ≤ δ·abelMass ≤ 2(M + A)√δ` on `(0, 1)`
  have hbound : ∀ δ : ℝ, 0 < δ → δ < 1 →
      δ * HamburgerStability.abelMass g δ ≤ 2 * (M + A) * Real.sqrt δ := by
    intro δ hδ hδ1
    set T : ℝ := 1 / Real.sqrt δ with hT
    have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    have hsq1 : Real.sqrt δ < 1 := by
      rw [Real.sqrt_lt' one_pos]; simpa using hδ1
    have hT1 : 1 ≤ T := by rw [hT, le_div_iff₀ hsq, one_mul]; exact hsq1.le
    have hT0 : 0 < T := by linarith
    have hpt : ∀ t, ‖g t‖ * Real.exp (-(δ * |t|)) ≤
        M * (Icc (-T) T).indicator (fun _ => (1 : ℝ)) t + A / T * Real.exp (-(δ * |t|)) := by
      intro t
      have he0 : 0 ≤ Real.exp (-(δ * |t|)) := (Real.exp_pos _).le
      have he1 : Real.exp (-(δ * |t|)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := abs_nonneg t; nlinarith
      by_cases ht : |t| ≤ T
      · rw [indicator_of_mem (show t ∈ Icc (-T) T from abs_le.mp ht)]
        have : ‖g t‖ * Real.exp (-(δ * |t|)) ≤ M :=
          (mul_le_of_le_one_right (norm_nonneg _) he1).trans (hM t)
        have : 0 ≤ A / T * Real.exp (-(δ * |t|)) := mul_nonneg (div_nonneg hA0 hT0.le) he0
        linarith
      · push Not at ht
        rw [indicator_of_notMem (show t ∉ Icc (-T) T from fun h => absurd (abs_le.mpr h)
          (not_le.mpr ht)), mul_zero, zero_add]
        refine mul_le_mul_of_nonneg_right ?_ he0
        calc ‖g t‖ ≤ A / |t| := hA t (hT1.trans ht.le)
          _ ≤ A / T := div_le_div_of_nonneg_left hA0 hT0 ht.le
    have hint1 : Integrable fun t : ℝ => M * (Icc (-T) T).indicator (fun _ => (1 : ℝ)) t :=
      ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).const_mul M
    have hexp : Integrable fun t : ℝ => Real.exp (-(δ * |t|)) := by
      have := HamburgerStability.integrable_abelMass (g := fun _ : ℝ => (1 : ℂ)) (Cg := 1)
        (N := 0) aestronglyMeasurable_const (fun t => by simp) hδ
      simpa using this
    have hint2 : Integrable fun t : ℝ => A / T * Real.exp (-(δ * |t|)) := hexp.const_mul _
    have hnn : ∀ t, 0 ≤ ‖g t‖ * Real.exp (-(δ * |t|)) := fun t =>
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    have hle : HamburgerStability.abelMass g δ ≤ M * (2 * T) + A / T * (2 / δ) := by
      unfold HamburgerStability.abelMass
      calc ∫ t, ‖g t‖ * Real.exp (-(δ * |t|))
          ≤ ∫ t, (M * (Icc (-T) T).indicator (fun _ => (1 : ℝ)) t +
              A / T * Real.exp (-(δ * |t|))) :=
            integral_mono_of_nonneg (Eventually.of_forall hnn) (hint1.add hint2)
              (Eventually.of_forall hpt)
        _ = M * (2 * T) + A / T * (2 / δ) := by
            rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
              integral_indicator measurableSet_Icc, integral_exp_neg_mul_abs_tail hδ]
            simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
              Set.univ_inter, Real.volume_real_Icc, smul_eq_mul, mul_one]
            congr 1
            rw [max_eq_left (by linarith)]
            ring
    calc δ * HamburgerStability.abelMass g δ ≤ δ * (M * (2 * T) + A / T * (2 / δ)) :=
          mul_le_mul_of_nonneg_left hle hδ.le
      _ = 2 * (M + A) * Real.sqrt δ := by
          rw [hT]
          have hsqsq : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ.le
          field_simp
          nlinarith [hsqsq]
  have hlow : ∀ δ : ℝ, 0 < δ → 0 ≤ δ * HamburgerStability.abelMass g δ := fun δ hδ =>
    mul_nonneg hδ.le (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hup : Tendsto (fun δ : ℝ => 2 * (M + A) * Real.sqrt δ) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto 0).const_mul (2 * (M + A))).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ using hlow δ hδ
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    exact hbound δ hδ.1 hδ.2

/-! ### The completed function -/

/-- The total Herglotz series: integer atoms plus infinitely many real atoms. -/
def phiInf (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : ℕ → ℝ) (s : ℂ) : ℂ :=
  atomicPairSeries (fun j => Real.pi * m j) t s + ∑' k, fracTerm (c k) (u k) s

/-- `K = G(2)/(Q(2) R(2))`. -/
def kInf (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : ℕ → ℝ) : ℂ :=
  bigG lam 2 / (atomQ m t 2 * fracInfProd c u 2)

/-- `Ĝ = K Q R`. -/
def gInf (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : ℕ → ℝ) (s : ℂ) : ℂ :=
  kInf lam m t c u * (atomQ m t s * fracInfProd c u s)

section Completed

variable {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {c u : ℕ → ℝ}

theorem atomQ_mul_fracInfProd_ne_zero (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) {z : ℂ} (hz : 1 / 2 < z.re) :
    atomQ m t z * fracInfProd c u z ≠ 0 :=
  mul_ne_zero (atomQ_ne_zero hone hsum (ne_atomAt_of_half_lt hz))
    (fracInfProd_ne_zero hc hu1 hut hcs hz)

theorem hasDerivAt_gInf (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    HasDerivAt (gInf lam m t c u) (phiInf m t c u z * gInf lam m t c u z) z := by
  have hz1 : ∀ i : AtomIndex m, z ≠ atomAt t i := ne_atomAt_of_half_lt hz
  have hQd := (differentiable_atomQ hone hsum z).hasDerivAt
  have hL := logDeriv_atomQ hone hsum hz1
  rw [logDeriv_apply] at hL
  have hne := atomQ_ne_zero hone hsum hz1
  have e : deriv (atomQ m t) z = atomicPairSeries (fun j => Real.pi * m j) t z * atomQ m t z := by
    rw [← hL]; field_simp
  rw [e] at hQd
  have hR := hasDerivAt_fracInfProd hc hu1 hut hcs hz
  refine ((hQd.mul hR).const_mul (kInf lam m t c u)).congr_deriv ?_
  unfold phiInf gInf
  ring

theorem gInf_two (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) :
    gInf lam m t c u 2 = bigG lam 2 := by
  have h := atomQ_mul_fracInfProd_ne_zero (m := m) (t := t) hone hsum hc hu1 hut hcs
    (z := 2) (by norm_num)
  unfold gInf kInf
  exact div_mul_cancel₀ _ h

theorem gInf_ne_zero (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2)
    {z : ℂ} (hz : 1 / 2 < z.re) : gInf lam m t c u z ≠ 0 :=
  mul_ne_zero (div_ne_zero (bigG_ne_zero lam (by norm_num))
    (atomQ_mul_fracInfProd_ne_zero hone hsum hc hu1 hut hcs (z := 2) (by norm_num)))
    (atomQ_mul_fracInfProd_ne_zero hone hsum hc hu1 hut hcs hz)

theorem continuousAt_gInf (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2)
    {z : ℂ} (hz : 1 / 2 ≤ z.re) : ContinuousAt (gInf lam m t c u) z := by
  unfold gInf
  exact continuousAt_const.mul ((differentiable_atomQ hone hsum).continuous.continuousAt.mul
    (continuousAt_fracInfProd hc hu1 hut hcs hz))

theorem re_phiInf_nonneg (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) {z : ℂ} (hz : 1 / 2 < z.re) :
    0 ≤ (phiInf m t c u z).re := by
  unfold phiInf
  rw [Complex.add_re, Complex.re_tsum (summable_fracTerm hc hu1 hut hcs z)]
  refine add_nonneg (re_atomicPairSeries_nonneg m t hz) (tsum_nonneg fun k => ?_)
  unfold fracTerm
  rw [Complex.re_ofReal_mul]
  have hw : 0 < (z - 1 / 2).re := by simp; linarith
  exact mul_nonneg (hc k) (re_two_mul_div_nonneg hw (u k))

theorem differentiableOn_phiInf (lam : ℕ → ℝ) (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs : Summable fun k => c k / u k ^ 2) :
    DifferentiableOn ℂ (phiInf m t c u) {s : ℂ | 1 / 2 < s.re} := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGd : DifferentiableOn ℂ (gInf lam m t c u) {s : ℂ | 1 / 2 < s.re} := fun z hz =>
    (hasDerivAt_gInf hone hsum hc hu1 hut hcs hz).differentiableAt.differentiableWithinAt
  refine ((hGd.deriv hU).div hGd fun z hz => gInf_ne_zero hone hsum hc hu1 hut hcs hz).congr
    fun z hz => ?_
  rw [Pi.div_apply, (hasDerivAt_gInf hone hsum hc hu1 hut hcs hz).deriv,
    mul_div_cancel_right₀ _ (gInf_ne_zero hone hsum hc hu1 hut hcs hz)]

end Completed

/-! ### Infinitely many real masses with a rapidly decaying tail force `Λ` and RH -/

/-- **Infinitely many non-integer spectral masses with a rapidly decaying tail force `Λ` and the
Riemann hypothesis.**  Let `Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`.  Suppose that on `Re s > 1`
`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s}` equals the Herglotz series with integer masses `m_j` at
ordinates `t_j ≥ 1` (`Σ m_j/t_j² < ∞`) plus real masses `c_k ≥ 0` at ordinates `u_k ≥ 1`, with
`u_k → ∞` and `Σ_k c_k u_k^K < ∞` for every `K`.  Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the
Riemann hypothesis holds. -/
theorem fractional_mass_tail_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {c u : ℕ → ℝ}
    (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop)
    (hcK : ∀ K : ℕ, Summable fun k => c k * u k ^ K)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hcs : Summable c := by simpa using hcK 0
  have hcs2 := summable_div_sq_of_summable hc hu1 hcs
  set G := gInf lam m t c u with hGdef
  set Φ := phiInf m t c u with hΦdef
  have hid' : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s := fun s hs => (hid s hs).symm
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid'
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum hc hu1 hut hcs2
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs =>
    re_phiInf_nonneg hc hu1 hut hcs2 hs
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s := fun s hs =>
    hasDerivAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum hc hu1 hut hcs2
  obtain ⟨CB, N, hCB, hB⟩ := exists_poly_bound_lineG hsl hΦre hidT hGc hGd hG2
  set Cinf : ℝ := ∑' k, c k with hCinf
  set κ : ℂ := Complex.exp (-((2 * Real.pi * Cinf : ℝ) : ℂ) * I) with hκ
  have hκ0 : κ ≠ 0 := Complex.exp_ne_zero _
  have hκinv : κ⁻¹ = Complex.exp (((2 * Real.pi * Cinf : ℝ) : ℂ) * I) := by
    rw [hκ, ← Complex.exp_neg]; congr 1; ring
  set ω : ℝ → ℂ := fun τ => Complex.exp (((2 * Real.pi * phaseSum c u (-(2 * τ)) : ℝ) : ℂ) * I)
    with hω
  set e : ℝ → ℂ := fun τ => if τ < 0 then (ω τ - κ⁻¹) * phiG G τ else 0 with he
  -- the exact lock on the lower half-line
  have hlock : ∀ τ : ℝ, τ < -0 → G (1 - lineS τ) =
      κ⁻¹ * G (lineS τ) + lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) * e τ := by
    intro τ hτ
    have hτ0 : τ < 0 := by linarith
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    have hrefl : G (1 - lineS τ) = ω τ * G (lineS τ) := by
      simp only [hGdef, gInf, hω]
      rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracInfProd_conj hc hu1 hut hcs2 hre,
        hline, conj_fracInfProd_lower hc hu1 hut hcs2 hy]
      ring
    have hD : lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
        (Gammaℝ_lineS_ne_zero τ)
    simp only [he, if_pos hτ0]
    unfold phiG
    set D := lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) with hDdef
    have hcancel : D * ((ω τ - κ⁻¹) * (G (lineS τ) / D)) = (ω τ - κ⁻¹) * G (lineS τ) := by
      field_simp
    rw [hrefl, hcancel]
    ring
  -- the defect is bounded by the unimodular gap times the boundary value
  have hgap : ∀ τ, ‖ω τ - κ⁻¹‖ ≤ 2 := by
    intro τ
    rw [hκinv]
    calc ‖ω τ - Complex.exp (((2 * Real.pi * Cinf : ℝ) : ℂ) * I)‖
        ≤ ‖ω τ‖ + ‖Complex.exp (((2 * Real.pi * Cinf : ℝ) : ℂ) * I)‖ := norm_sub_le _ _
      _ = 2 := by rw [hω]; simp only [Complex.norm_exp_ofReal_mul_I]; norm_num
  have heb : ∀ τ, ‖e τ‖ ≤ (2 * CB) * (1 + |τ|) ^ N := by
    intro τ
    simp only [he]
    split_ifs
    · rw [norm_mul]
      calc ‖ω τ - κ⁻¹‖ * ‖phiG G τ‖ ≤ 2 * (CB * (1 + |τ|) ^ N) :=
            mul_le_mul (hgap τ) (hB τ).1 (norm_nonneg _) (by norm_num)
        _ = 2 * CB * (1 + |τ|) ^ N := by ring
    · rw [norm_zero]; positivity
  -- measurability
  have hph : Measurable fun τ : ℝ => phaseSum c u (-(2 * τ)) :=
    ((phaseSum_mono hc hut).comp_antitone (show Antitone fun τ : ℝ => -(2 * τ) from
      fun a b hab => by linarith)).measurable
  have hωm : Measurable ω :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul hph)).mul_const I)
  have hem : Measurable e :=
    Measurable.ite measurableSet_Iio ((hωm.sub_const _).mul (continuous_phiG hGc).measurable)
      measurable_const
  -- decay of the defect
  set S : ℝ := ∑' k, c k * u k ^ (N + 1) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => mul_nonneg (hc k) (pow_nonneg (by linarith [hu1 k]) _)
  set A : ℝ := 2 * Real.pi * S * CB with hA
  have hA0 : 0 ≤ A := by positivity
  have hdecay : ∀ τ, 1 ≤ |τ| → ‖e τ‖ ≤ A / |τ| := by
    intro τ hτ
    simp only [he]
    split_ifs with hτ0
    · have habs : |τ| = -τ := abs_of_neg hτ0
      set y : ℝ := -(2 * τ) with hy
      have hy0 : 0 < y := by rw [hy]; linarith
      have hy2 : y = 2 * |τ| := by rw [hy, habs]; ring
      obtain ⟨hlo, hhi⟩ := tsum_sub_phaseSum_le hc hu1 hcs (hcK (N + 1)) hy0
      have hω1 : ‖ω τ - κ⁻¹‖ ≤ 4 * Real.pi * (S / y ^ (N + 1)) := by
        rw [hκinv, hω]
        refine (norm_cexp_mul_I_sub_le _ _).trans ?_
        rw [show 2 * Real.pi * phaseSum c u y - 2 * Real.pi * Cinf =
          -(2 * Real.pi * (Cinf - phaseSum c u y)) by ring, abs_neg,
          abs_of_nonneg (by positivity)]
        have := mul_le_mul_of_nonneg_left hhi (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
        linarith
      have hpoly : ‖phiG G τ‖ ≤ CB * y ^ N := by
        refine (hB τ).1.trans (mul_le_mul_of_nonneg_left ?_ hCB)
        exact pow_le_pow_left₀ (by positivity) (by rw [hy2]; linarith) N
      rw [norm_mul]
      have hyN : 0 < y ^ N := pow_pos hy0 N
      calc ‖ω τ - κ⁻¹‖ * ‖phiG G τ‖ ≤ 4 * Real.pi * (S / y ^ (N + 1)) * (CB * y ^ N) :=
            mul_le_mul hω1 hpoly (norm_nonneg _) (by positivity)
        _ = A / |τ| := by
            rw [hA, hy2, pow_succ]
            have hτ' : 0 < |τ| := by linarith
            field_simp
            ring
    · rw [norm_zero]; positivity
  have hM : ∀ τ, ‖e τ‖ ≤ 2 * CB * 2 ^ N + A := by
    intro τ
    by_cases hτ : 1 ≤ |τ|
    · have h1 := hdecay τ hτ
      have h2 : A / |τ| ≤ A := div_le_self hA0 hτ
      have h3 : 0 ≤ 2 * CB * 2 ^ N := by positivity
      linarith
    · push Not at hτ
      have h1 := heb τ
      have h2 : (1 + |τ|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      have h3 : 2 * CB * (1 + |τ|) ^ N ≤ 2 * CB * 2 ^ N :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith
  have heA := tendsto_mul_abelMass_of_decay hM hdecay
  exact phase_lock_rigidity_of_defect hsl hΦd hΦre hid' hGc hGd hG2 hem heb heA le_rfl hκ0 hlock

end

end FractionalMassTailRigidity

end RHTower
