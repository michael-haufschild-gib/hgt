import GaloisForLFunctions.ArithmeticOrientationTheory.ATowerPoleObstructsAVerticalProgression
import GaloisForLFunctions.ArithmeticOrientationTheory.AKernelBoundedBelowOnTheHalfPlaneIsAUnit
import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenInequality

/-!
# Obstruction hulls are not confined to the half-plane

The half-plane `Re s ≥ ½` meets the Bohr polydisk only in the points `ω(p) = p^{½ − s}`, whose radii
are tied: `|ω(3)| = √3 (|ω(2)|/√2)^{log₂ 3}` (`tiedAtTwoThree_halfPlanePoint`), a closed condition.
The hulls computed so far (smooth powers, probes, translated zeros of the Möbius weight) are made of
such points.  This module shows that unpayability is genuinely located on the polydisk:

* **A whole hyperplane is obstructed** (`mem_obstructionHull_towerTwisted_of_two`): for the
  tower-twisted smooth power `c_a` (`2^{1−ε} < a < 2`) with no zero of `ζ` on its progression, every
  Bohr point with `ω(2) = √2/a` — whatever its other coordinates — is an obstruction point.
* **Some `a` qualifies** (`exists_good_tower`): the zeros of `ζ` are countable, the interval of `a`
  is not.
* **Hence an untied obstruction** (`exists_obstruction_not_tied`): the point `ω(2) = √2/a`,
  `ω(q) = 0` for odd `q` is in the hull of `c_a` and is not a limit of half-plane points.

Mechanism.  Repairing kernels vanish on the progression `s_n = log₂ a − 2πin/log 2`
(`mem_obstructionHull_towerTwisted`); their points `ω_n` have `ω_n(2) = √2/a` and run, by Kronecker,
densely through the torus `|ω(q)| = q^{½ − log₂ a}` (`exists_towerPoint_near`), so the hull contains
the torus (`bohrEval_eq_zero_of_onTowerTorus`).  On a circle `|z| = r < 1` in one coordinate the
Bohr transform is holomorphic in `z` on the unit disk, and vanishing on the circle forces vanishing
on the disk (`coordEval_eq_zero_of_sphere`): coordinates are untied one at a time, and a tail
argument reaches every point of the hyperplane.
-/

open Finset ArithmeticFunction LSeries Complex Filter Topology Metric

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-! ### Continuity of the Bohr evaluation along the primes -/

/-- If Bohr points converge at every prime, their evaluations converge. -/
theorem tendsto_bohrEval_of_tendsto_primes {σ : ℝ} {g : ArithmeticFunction ℂ}
    (hg : LSeriesSummable (⇑g) σ) {ωj : ℕ → BohrPoint} {ω : BohrPoint}
    (h : ∀ p, p.Prime → Tendsto (fun j => (ωj j).ω p) atTop (𝓝 (ω.ω p))) :
    Tendsto (fun j => bohrEval σ g (ωj j)) atTop (𝓝 (bohrEval σ g ω)) := by
  unfold bohrEval LSeries
  refine tendsto_tsum_of_dominated_convergence hg.norm (fun n => ?_)
    (Eventually.of_forall fun j n => norm_term_le _ (by
      simp only [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) ((ωj j).norm_le_one n)))
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero]; exact tendsto_const_nhds
  simp only [term_of_ne_zero hn]
  refine Tendsto.div_const (Tendsto.const_mul _ ?_) _
  have hl : Tendsto (fun j => (n.primeFactorsList.map (ωj j).ω).prod) atTop
      (𝓝 (n.primeFactorsList.map ω.ω).prod) := by
    have := tendsto_list_prod (l := n.primeFactorsList) (f := fun p j => (ωj j).ω p)
      (a := fun p => ω.ω p) (x := atTop) fun p hp => h p (Nat.prime_of_mem_primeFactorsList hp)
    simpa using this
  simpa [← (ωj _).apply_eq_prod hn, ← ω.apply_eq_prod hn] using hl

/-! ### Untying one coordinate -/

/-- **Vanishing on a circle forces vanishing on the disk**: if the Bohr transform with the `q`-th
value replaced by `z` vanishes on `|z| = r < 1`, it vanishes for every `|z| ≤ 1`. -/
theorem coordEval_eq_zero_of_sphere {σ : ℝ} {g : ArithmeticFunction ℂ}
    (hg : LSeriesSummable (⇑g) σ) (ω : BohrPoint) (q : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (h : ∀ z ∈ sphere (0 : ℂ) r, coordEval σ g ω q z = 0) {z₀ : ℂ}
    (hz₀ : z₀ ∈ closedBall (0 : ℂ) 1) : coordEval σ g ω q z₀ = 0 := by
  have ha : AnalyticOnNhd ℂ (coordEval σ g ω q) (ball 0 1) :=
    (differentiableOn_coordEval hg ω q).analyticOnNhd isOpen_ball
  have hr : ((r : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have hfreq : ∃ᶠ z in 𝓝[≠] ((r : ℝ) : ℂ), coordEval σ g ω q z = 0 := by
    rw [Filter.frequently_iff]
    intro V hV
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hV
    set θ := min (ρ / 2) 1
    have hθ : 0 < θ := lt_min (by linarith) one_pos
    have hnorm : ‖exp (I * (θ : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ
    refine ⟨(r : ℂ) * exp (I * θ), hball ⟨?_, ?_⟩, h _ ?_⟩
    · rw [mem_ball, dist_eq_norm, show (r : ℂ) * exp (I * θ) - r = r * (exp (I * θ) - 1) by ring,
        norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      calc r * ‖exp (I * θ) - 1‖ ≤ 1 * ‖(θ : ℝ)‖ :=
            mul_le_mul hr1.le Real.norm_exp_I_mul_ofReal_sub_one_le (norm_nonneg _) zero_le_one
        _ < ρ := by
            rw [one_mul, Real.norm_eq_abs, abs_of_pos hθ]
            exact (min_le_left _ _).trans_lt (by linarith)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro he
      have h1 : exp (I * θ) = 1 := by
        have hr0' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr0.ne'
        exact (mul_eq_left₀ hr0').1 he
      have h2 := Complex.norm_exp_I_mul_ofReal_sub_one θ
      rw [h1, sub_self, norm_zero, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs] at h2
      have hs : 0 < Real.sin (θ / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [min_le_right (ρ / 2) 1, Real.pi_gt_three])
      have : |(2 : ℝ)| * |Real.sin (θ / 2)| > 0 := by positivity
      linarith
    · rw [mem_sphere_zero_iff_norm, norm_mul, hnorm, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos hr0]
  have hzero := ha.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected hr hfreq
  have hcl : Set.EqOn (coordEval σ g ω q) 0 (closedBall 0 1) :=
    hzero.of_subset_closure (continuousOn_coordEval hg ω q) continuousOn_const
      ball_subset_closedBall (by rw [closure_ball _ one_ne_zero])
  exact hcl hz₀

/-! ### The progression and its points -/

/-- The `n`-th point `log₂ a − 2πin/log 2` of the tower progression. -/
def towerPoint (a : ℝ) (n : ℤ) : ℂ :=
  (Real.logb 2 a : ℂ) - ((2 * Real.pi * n / Real.log 2 : ℝ) : ℂ) * I

theorem towerPoint_re (a : ℝ) (n : ℤ) : (towerPoint a n).re = Real.logb 2 a := by
  simp only [towerPoint, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero]

theorem complex_log_two : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
  simp

theorem mul_two_cpow_neg_towerPoint {a : ℝ} (ha : 0 < a) (n : ℤ) :
    (a : ℂ) * (2 : ℂ) ^ (-towerPoint a n) = 1 := by
  have hl2 : (Real.log 2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.log_pos one_lt_two).ne'
  have e : Complex.log 2 * -towerPoint a n = -(Real.log a : ℂ) + (n : ℂ) * (2 * Real.pi * I) := by
    rw [complex_log_two]
    simp only [towerPoint, Real.logb]
    push_cast
    field_simp
    ring
  rw [cpow_def_of_ne_zero two_ne_zero, e, exp_add, exp_int_mul_two_pi_mul_I, mul_one,
    ← ofReal_neg, ← ofReal_exp, Real.exp_neg, Real.exp_log ha, ← ofReal_mul,
    mul_inv_cancel₀ ha.ne', ofReal_one]

variable {ε a : ℝ}

theorem half_le_re_towerPoint (hε2 : ε < 1 / 2) (ha1 : (2 : ℝ) ^ (1 - ε) < a) (ha2 : a < 2)
    (n : ℤ) : (1 / 2 : ℝ) ≤ (towerPoint a n).re := by
  rw [towerPoint_re]; linarith [(logb_bounds ha1 ha2).1]

/-- The value at `2` of a progression point. -/
theorem towerPoint_apply_two (ha : 0 < a) (n : ℤ) (h : (1 / 2 : ℝ) ≤ (towerPoint a n).re) :
    (halfPlanePoint (1 / 2) (towerPoint a n) h).ω 2 = (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) / a := by
  have hpt := mul_two_cpow_neg_towerPoint ha n
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 ha.ne'
  simp only [halfPlanePoint, two_ne_zero, if_false, Nat.cast_ofNat]
  rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero]
  field_simp
  linear_combination hpt

/-- The radius of the tied torus at `q`. -/
def towerRadius (a : ℝ) (q : ℕ) : ℝ := (q : ℝ) ^ (1 / 2 - Real.logb 2 a)

/-- The value at a prime `q` of a progression point: `q^{½ − log₂ a} q^{i t_n}`. -/
theorem towerPoint_apply (n : ℤ) (h : (1 / 2 : ℝ) ≤ (towerPoint a n).re) {q : ℕ} (hq : q.Prime) :
    (halfPlanePoint (1 / 2) (towerPoint a n) h).ω q = (towerRadius a q : ℂ) *
      (q : ℂ) ^ (((2 * Real.pi * n / Real.log 2 : ℝ) : ℂ) * I) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  simp only [halfPlanePoint, hq.ne_zero, if_false, towerRadius]
  rw [show ((1 / 2 : ℝ) : ℂ) - towerPoint a n = ((1 / 2 - Real.logb 2 a : ℝ) : ℂ) +
      ((2 * Real.pi * n / Real.log 2 : ℝ) : ℂ) * I by simp only [towerPoint]; push_cast; ring,
    cpow_add _ _ hq0, ofReal_cpow (Nat.cast_nonneg q), ofReal_natCast]

/-! ### Kronecker on the progression -/

theorem abs_le_of_norm_exp_sub_one {y : ℝ} (hy : |y| ≤ Real.pi) :
    |y| ≤ Real.pi / 2 * ‖exp (I * y) - 1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  have hpi := Real.pi_pos
  have key : ∀ z : ℝ, 0 ≤ z → z ≤ Real.pi / 2 → 2 / Real.pi * z ≤ |Real.sin z| := fun z hz hz' =>
    (Real.mul_le_sin hz hz').trans (le_abs_self _)
  rcases le_total 0 y with h0 | h0
  · have := key (y / 2) (by linarith) (by rw [abs_of_nonneg h0] at hy; linarith)
    rw [abs_of_nonneg h0]
    field_simp at this ⊢
    nlinarith
  · have := key (-y / 2) (by linarith) (by rw [abs_of_nonpos h0] at hy; linarith)
    rw [show -y / 2 = -(y / 2) by ring, Real.sin_neg, abs_neg] at this
    rw [abs_of_nonpos h0]
    field_simp at this ⊢
    nlinarith

/-- From `|e^{ix} − 1| < η`, `x` is within `πη/2` of `2πℤ`. -/
theorem exists_int_near_of_norm_exp_sub_one {x η : ℝ} (h : ‖exp (I * x) - 1‖ < η) :
    ∃ n : ℤ, |x - 2 * Real.pi * n| ≤ Real.pi / 2 * η := by
  have hpi := Real.pi_pos
  set n : ℤ := round (x / (2 * Real.pi))
  refine ⟨n, ?_⟩
  set y := x - 2 * Real.pi * n
  have hy : |y| ≤ Real.pi := by
    have h1 := abs_sub_round (x / (2 * Real.pi))
    have : y = 2 * Real.pi * (x / (2 * Real.pi) - n) := by simp only [y]; field_simp
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith
  have hexp : exp (I * x) = exp (I * y) := by
    have : (x : ℂ) = (y : ℂ) + (n : ℂ) * (2 * Real.pi) := by simp only [y]; push_cast; ring
    rw [this, mul_add, exp_add, show I * ((n : ℂ) * (2 * Real.pi)) = n * (2 * Real.pi * I) by ring,
      exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp] at h
  exact (abs_le_of_norm_exp_sub_one hy).trans (by nlinarith [norm_nonneg (exp (I * y) - 1)])

/-- On the tied torus: `ω(2) = √2/a` and `|ω(q)| = q^{½ − log₂ a}` at the odd primes. -/
def OnTowerTorus (a : ℝ) (ω : BohrPoint) : Prop :=
  ω.ω 2 = (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) / a ∧
    ∀ q, q.Prime → q ≠ 2 → ‖ω.ω q‖ = towerRadius a q

theorem towerRadius_le_one (hε2 : ε < 1 / 2) (ha1 : (2 : ℝ) ^ (1 - ε) < a) (ha2 : a < 2) {q : ℕ}
    (hq : q.Prime) : towerRadius a q ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq.one_le)
    (by linarith [(logb_bounds ha1 ha2).1])

theorem towerRadius_pos {q : ℕ} (hq : q.Prime) : 0 < towerRadius a q :=
  Real.rpow_pos_of_pos (by exact_mod_cast hq.pos) _

/-- **Kronecker on the progression**: the points `ω_n` approach any point of the tied torus at all
primes `q ≤ N`. -/
theorem exists_towerPoint_near (hε2 : ε < 1 / 2) (ha1 : (2 : ℝ) ^ (1 - ε) < a) (ha2 : a < 2)
    {ω : BohrPoint} (hω : OnTowerTorus a ω) (N : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ n : ℤ, ∀ q, q.Prime → q ≤ N →
      ‖(halfPlanePoint (1 / 2) (towerPoint a n) (half_le_re_towerPoint hε2 ha1 ha2 n)).ω q -
        ω.ω q‖ < η := by
  have ha0 : 0 < a := lt_trans (Real.rpow_pos_of_pos two_pos _) ha1
  by_cases hN : N < 2
  · exact ⟨0, fun q hq hqN => absurd hq.two_le (by omega)⟩
  push Not at hN
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpi := Real.pi_pos
  set C : ℝ := 1 + Real.pi / 2 * (Real.log (N + 1) / Real.log 2)
  have hlogN : 0 ≤ Real.log (N + 1) :=
    Real.log_nonneg (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  set η' := η / (2 * C)
  have hη' : 0 < η' := by positivity
  obtain ⟨t, ht⟩ := primeTorus_cpow_dense N
    (fun p => if ((p : Nat.Primes) : ℕ) = 2 then 0 else arg (ω.ω ((p : Nat.Primes) : ℕ))) hη'
  have hcpow : ∀ (p : ℕ), p ≠ 0 → ∀ x : ℝ, (p : ℂ) ^ ((x : ℂ) * I) =
      exp (I * ((x * Real.log p : ℝ) : ℂ)) := fun p hp x => by
    rw [cpow_def_of_ne_zero (by exact_mod_cast hp), ← ofReal_natCast,
      ← ofReal_log (Nat.cast_nonneg p)]
    push_cast; ring_nf
  have hunit : ∀ x : ℝ, ‖exp (I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  -- the prime `2` pins `t` near the progression
  obtain ⟨n, hn⟩ : ∃ n : ℤ, |t * Real.log 2 - 2 * Real.pi * n| ≤ Real.pi / 2 * η' := by
    have h := ht ⟨⟨2, Nat.prime_two⟩, (mem_primesLE N _).2 hN⟩
    simp only [if_true, ofReal_zero, zero_mul, Complex.exp_zero] at h
    rw [hcpow 2 two_ne_zero] at h
    exact exists_int_near_of_norm_exp_sub_one h
  refine ⟨n, fun q hq hqN => ?_⟩
  by_cases hq2 : q = 2
  · subst hq2
    rw [towerPoint_apply_two ha0, hω.1, sub_self, norm_zero]
    exact hη
  have hk : ‖(q : ℂ) ^ ((t : ℂ) * I) - exp ((arg (ω.ω q) : ℝ) * I)‖ < η' := by
    have := ht ⟨⟨q, hq⟩, (mem_primesLE N _).2 hqN⟩
    simpa [hq2] using this
  have hωq : ω.ω q = (towerRadius a q : ℂ) * exp ((arg (ω.ω q) : ℝ) * I) := by
    rw [← hω.2 q hq hq2]; exact (norm_mul_exp_arg_mul_I _).symm
  rw [towerPoint_apply n _ hq, hωq, ← mul_sub, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (towerRadius_pos hq)]
  set tn : ℝ := 2 * Real.pi * n / Real.log 2
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.one_le)
  have hdiff : ‖(q : ℂ) ^ ((tn : ℂ) * I) - (q : ℂ) ^ ((t : ℂ) * I)‖ ≤ |tn - t| * Real.log q := by
    rw [hcpow q hq.ne_zero, hcpow q hq.ne_zero,
      show exp (I * ((tn * Real.log q : ℝ) : ℂ)) - exp (I * ((t * Real.log q : ℝ) : ℂ)) =
        exp (I * ((t * Real.log q : ℝ) : ℂ)) * (exp (I * (((tn - t) * Real.log q : ℝ) : ℂ)) - 1) by
          rw [mul_sub, mul_one, ← exp_add]; congr 2; push_cast; ring,
      norm_mul, hunit, one_mul]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlogq]
  have htn : |tn - t| ≤ Real.pi / 2 * η' / Real.log 2 := by
    rw [show tn - t = -(t * Real.log 2 - 2 * Real.pi * n) / Real.log 2 by
        simp only [tn]; field_simp; ring, abs_div, abs_neg, abs_of_pos hl2]
    exact div_le_div_of_nonneg_right hn hl2.le
  have hlq : Real.log q ≤ Real.log (N + 1) :=
    Real.log_le_log (by exact_mod_cast hq.pos) (by exact_mod_cast (by omega : q ≤ N + 1))
  have hsplit := norm_sub_le_norm_sub_add_norm_sub ((q : ℂ) ^ ((tn : ℂ) * I))
    ((q : ℂ) ^ ((t : ℂ) * I)) (exp ((arg (ω.ω q) : ℝ) * I))
  have hr1 := towerRadius_le_one hε2 ha1 ha2 hq
  have hprod : |tn - t| * Real.log q ≤ Real.pi / 2 * η' / Real.log 2 * Real.log (N + 1) :=
    mul_le_mul htn hlq hlogq (by positivity)
  have hC' : η' + Real.pi / 2 * η' / Real.log 2 * Real.log (N + 1) = η' * C := by
    simp only [C]; field_simp
  have hη2 : η' * C = η / 2 := by simp only [η']; field_simp
  calc towerRadius a q * ‖(q : ℂ) ^ ((tn : ℂ) * I) - exp ((arg (ω.ω q) : ℝ) * I)‖
      ≤ 1 * (|tn - t| * Real.log q + η') :=
        mul_le_mul hr1 (hsplit.trans (add_le_add hdiff hk.le)) (norm_nonneg _) zero_le_one
    _ < η := by nlinarith

/-! ### The hull contains the tied torus -/

section Tower

variable (hε : 0 < ε) (hε2 : ε < 1 / 2) (ha1 : (2 : ℝ) ^ (1 - ε) < a) (ha2 : a < 2)
include hε hε2 ha1 ha2

omit hε2 in
/-- The summable mean of `c_a`, as a term. -/
theorem summable_abs_towerTwisted_div' : Summable fun d : ℕ => |towerTwistedPower ε a d / d| :=
  summable_abs_towerTwisted_div hε (lt_trans (Real.rpow_pos_of_pos two_pos _) ha1).le ha2

/-- **The tied torus is obstructed** when `ζ` has no zero on the progression. -/
theorem bohrEval_eq_zero_of_onTowerTorus (hgood : ∀ n : ℤ, riemannZeta (towerPoint a n) ≠ 0)
    {k : WienerAlgebraAt (1 / 2)}
    (hk : k ∈ paidIdeal (towerTwistedPower ε a) (summable_abs_towerTwisted_div' hε ha1 ha2))
    {ω : BohrPoint} (hω : OnTowerTorus a ω) : bohrEval (1 / 2) k.toFn ω = 0 := by
  have ha0 : 0 < a := lt_trans (Real.rpow_pos_of_pos two_pos _) ha1
  have hnear : ∀ j : ℕ, ∃ n : ℤ, ∀ q, q.Prime → q ≤ j →
      ‖(halfPlanePoint (1 / 2) (towerPoint a n) (half_le_re_towerPoint hε2 ha1 ha2 n)).ω q -
        ω.ω q‖ < 1 / ((j : ℝ) + 1) := fun j =>
    exists_towerPoint_near hε2 ha1 ha2 hω j (by positivity)
  choose n hn using hnear
  set ωj : ℕ → BohrPoint := fun j =>
    halfPlanePoint (1 / 2) (towerPoint a (n j)) (half_le_re_towerPoint hε2 ha1 ha2 (n j))
  have hzero : ∀ j, bohrEval (1 / 2) k.toFn (ωj j) = 0 := fun j =>
    mem_obstructionHull_towerTwisted hε hε2 ha1 ha2 (mul_two_cpow_neg_towerPoint ha0 (n j))
      (hgood (n j)) _ k hk
  have hlim := tendsto_bohrEval_of_tendsto_primes k.summable (ωj := ωj) (ω := ω) fun p hp => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop p).mono fun j hj => (hn j p hp hj).le) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun j => (hzero j).symm) hlim |>.symm

/-! ### Untying the coordinates -/

omit hε in
theorem towerRadius_lt_one {q : ℕ} (hq : q.Prime) : towerRadius a q < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq.one_lt)
    (by linarith [(logb_bounds ha1 ha2).1])

/-- **Untying finitely many coordinates**: a point with `ω(2) = √2/a`, on the torus at the odd
primes outside `S`, is obstructed. -/
theorem bohrEval_eq_zero_of_two_of_finset (hgood : ∀ n : ℤ, riemannZeta (towerPoint a n) ≠ 0)
    {k : WienerAlgebraAt (1 / 2)}
    (hk : k ∈ paidIdeal (towerTwistedPower ε a) (summable_abs_towerTwisted_div' hε ha1 ha2))
    (S : Finset ℕ) : ∀ ω : BohrPoint, ω.ω 2 = (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) / a →
      (∀ q, q.Prime → q ≠ 2 → q ∉ S → ‖ω.ω q‖ = towerRadius a q) →
      bohrEval (1 / 2) k.toFn ω = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    exact fun ω h2 hT => bohrEval_eq_zero_of_onTowerTorus hε hε2 ha1 ha2 hgood hk
      ⟨h2, fun q hq hq2 => hT q hq hq2 (Finset.notMem_empty q)⟩
  | @insert q S hqS ih =>
    intro ω h2 hT
    by_cases hq : q.Prime ∧ q ≠ 2
    swap
    · refine ih ω h2 fun p hp hp2 hpS => hT p hp hp2 ?_
      rw [mem_insert, not_or]
      exact ⟨fun h => hq (h ▸ ⟨hp, hp2⟩), hpS⟩
    have hr0 := towerRadius_pos (a := a) hq.1
    have hr1 := towerRadius_lt_one hε2 ha1 ha2 hq.1
    have hcirc : ∀ z ∈ sphere (0 : ℂ) (towerRadius a q), coordEval (1 / 2) k.toFn ω q z = 0 := by
      intro z hz
      have hz1 : ‖z‖ ≤ 1 := (mem_sphere_zero_iff_norm.1 hz).le.trans hr1.le
      rw [← bohrEval_replace (1 / 2) k.toFn ω q hz1]
      refine ih _ ?_ fun p hp hp2 hpS => ?_
      · rw [replace_apply_prime _ _ _ Nat.prime_two, Function.update_of_ne (Ne.symm hq.2)]
        exact h2
      · rw [replace_apply_prime _ _ _ hp]
        rcases eq_or_ne p q with rfl | hpq
        · simpa using mem_sphere_zero_iff_norm.1 hz
        · rw [Function.update_of_ne hpq]
          exact hT p hp hp2 (by rw [mem_insert, not_or]; exact ⟨hpq, hpS⟩)
    have := coordEval_eq_zero_of_sphere k.summable ω q hr0 hr1 hcirc
      (z₀ := ω.ω q) (mem_closedBall_zero_iff.2 (ω.norm_le_one q))
    rwa [coordEval_self] at this

/-- **The hyperplane is obstructed**: if `ζ` has no zero on the progression, every Bohr point with
`ω(2) = √2/a` lies in the hull of `c_a`, whatever its other coordinates. -/
theorem mem_obstructionHull_towerTwisted_of_two
    (hgood : ∀ n : ℤ, riemannZeta (towerPoint a n) ≠ 0) {ω : BohrPoint}
    (h2 : ω.ω 2 = (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) / a) :
    ω ∈ obstructionHull (towerTwistedPower ε a) (summable_abs_towerTwisted_div' hε ha1 ha2) := by
  intro k hk
  have ha0 : 0 < a := lt_trans (Real.rpow_pos_of_pos two_pos _) ha1
  set ω₀ := halfPlanePoint (1 / 2) (towerPoint a 0) (half_le_re_towerPoint hε2 ha1 ha2 0)
  have h0two : ω₀.ω 2 = (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) / a := towerPoint_apply_two ha0 0 _
  have h0q : ∀ q, q.Prime → ‖ω₀.ω q‖ = towerRadius a q := fun q hq => by
    rw [towerPoint_apply 0 _ hq, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos (towerRadius_pos hq), norm_natCast_cpow_of_pos hq.pos]
    simp
  have hv : ∀ N : ℕ, ∀ p, p.Prime → ‖(fun p => if p < N then ω.ω p else ω₀.ω p) p‖ ≤ 1 :=
    fun N p _ => by dsimp only; split_ifs; exacts [ω.norm_le_one p, ω₀.norm_le_one p]
  set ωN : ℕ → BohrPoint := fun N => BohrPoint.ofPrimes _ (hv N)
  have hzero : ∀ N, bohrEval (1 / 2) k.toFn (ωN N) = 0 := fun N => by
    refine bohrEval_eq_zero_of_two_of_finset hε hε2 ha1 ha2 hgood hk (range N) _ ?_ ?_
    · rw [BohrPoint.ofPrimes_apply_prime _ Nat.prime_two]
      split_ifs
      exacts [h2, h0two]
    · intro q hq _ hqN
      rw [BohrPoint.ofPrimes_apply_prime _ hq]
      rw [if_neg (fun h => hqN (mem_range.2 h))]
      exact h0q q hq
  have hlim := tendsto_bohrEval_of_tendsto_primes k.summable (ωj := ωN) (ω := ω) fun p hp => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop p] with N hN
    rw [BohrPoint.ofPrimes_apply_prime _ hp]
    rw [if_pos hN]
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun N => (hzero N).symm) hlim |>.symm

omit hε2 ha1 ha2 in
/-- **Good parameters exist**: some `a ∈ (2^{1−ε}, 2)` has no zero of `ζ` on its progression,
since the zeros of `ζ` are countable. -/
theorem exists_good_tower : ∃ a : ℝ, (2 : ℝ) ^ (1 - ε) < a ∧ a < 2 ∧
    ∀ n : ℤ, riemannZeta (towerPoint a n) ≠ 0 := by
  have hlt : (2 : ℝ) ^ (1 - ε) < 2 := by
    calc (2 : ℝ) ^ (1 - ε) < (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
      _ = 2 := Real.rpow_one 2
  set B : Set ℝ := (fun s : ℂ => (2 : ℝ) ^ s.re) '' {s : ℂ | RHTower.zetaEntire s = 0}
  have hB : B.Countable := RHTower.countable_setOf_zetaEntire_eq_zero.image _
  obtain ⟨a, haI, haB⟩ : (Set.Ioo ((2 : ℝ) ^ (1 - ε)) 2 \ B).Nonempty := by
    refine Set.sdiff_nonempty.2 fun hsub => ?_
    have : (Set.Ioo ((2 : ℝ) ^ (1 - ε)) 2).Countable := hB.mono hsub
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real hlt] at this
    exact this.not_gt Cardinal.aleph0_lt_continuum
  refine ⟨a, haI.1, haI.2, fun n hz => haB ⟨towerPoint a n, ?_, ?_⟩⟩
  · have hne : towerPoint a n ≠ 1 := fun h => by
      have := congrArg Complex.re h
      rw [towerPoint_re] at this
      simp at this
      linarith [(logb_bounds haI.1 haI.2).2]
    show RHTower.zetaEntire (towerPoint a n) = 0
    rw [RHTower.zetaEntire_eq hne, hz, mul_zero]
  · have ha0 : 0 < a := lt_trans (Real.rpow_pos_of_pos two_pos _) haI.1
    show (2 : ℝ) ^ (towerPoint a n).re = a
    rw [towerPoint_re, Real.rpow_logb two_pos (by norm_num) ha0]

end Tower

/-! ### Untied obstructions -/

/-- The radii at `2` and `3` are tied as at a half-plane point. -/
def TiedAtTwoThree (ω : BohrPoint) : Prop :=
  ‖ω.ω 3‖ = Real.sqrt 3 * (‖ω.ω 2‖ / Real.sqrt 2) ^ Real.logb 2 3

/-- **Half-plane points are tied.** -/
theorem tiedAtTwoThree_halfPlanePoint (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re) :
    TiedAtTwoThree (halfPlanePoint (1 / 2) s hs) := by
  unfold TiedAtTwoThree
  have hn : ∀ n : ℕ, n ≠ 0 → ‖(halfPlanePoint (1 / 2) s hs).ω n‖ = (n : ℝ) ^ (1 / 2 - s.re) :=
    fun n hn => by
      simp only [halfPlanePoint, hn, if_false]
      rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
  rw [hn 3 three_ne_zero, hn 2 two_ne_zero]
  have e1 : ((2 : ℕ) : ℝ) ^ (1 / 2 - s.re) / Real.sqrt 2 = (2 : ℝ) ^ (-s.re) := by
    rw [Real.sqrt_eq_rpow, Nat.cast_ofNat, ← Real.rpow_sub two_pos]; ring_nf
  have e2 : ((2 : ℝ) ^ (-s.re)) ^ Real.logb 2 3 = (3 : ℝ) ^ (-s.re) := by
    rw [← Real.rpow_mul zero_le_two, mul_comm, Real.rpow_mul zero_le_two,
      Real.rpow_logb two_pos (by norm_num) (by norm_num)]
  rw [e1, e2, Real.sqrt_eq_rpow, Nat.cast_ofNat, ← Real.rpow_add (by norm_num)]
  ring_nf

theorem norm_two_point_lt_one {ε a : ℝ} (hε2 : ε < 1 / 2) (ha1 : (2 : ℝ) ^ (1 - ε) < a) :
    ‖(2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) / a‖ < 1 := by
  have ha0 : 0 < a := lt_trans (Real.rpow_pos_of_pos two_pos _) ha1
  have h2 : ‖(2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ)‖ = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (two_pos : (0 : ℝ) < 2) (((1 / 2 : ℝ)) : ℂ)
    simpa using this
  rw [norm_div, h2, norm_real, Real.norm_eq_abs, abs_of_pos ha0, div_lt_one ha0]
  calc (2 : ℝ) ^ (1 / 2 : ℝ) < (2 : ℝ) ^ (1 - ε) :=
        Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
    _ < a := ha1

/-- **An untied obstruction**: for some tower-twisted smooth power, the Bohr point `ω(2) = √2/a`,
`ω(q) = 0` at the odd primes is an obstruction point, though it is not tied as every half-plane point
is. Unpayability is not confined to the half-plane. -/
theorem exists_obstruction_not_tied {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ a : ℝ, ∃ (ha1 : (2 : ℝ) ^ (1 - ε) < a) (ha2 : a < 2),
      ∃ ω ∈ obstructionHull (towerTwistedPower ε a) (summable_abs_towerTwisted_div' hε ha1 ha2),
        ¬ TiedAtTwoThree ω := by
  obtain ⟨a, ha1, ha2, hgood⟩ := exists_good_tower hε
  set w : ℂ := (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) / a
  have hw := norm_two_point_lt_one hε2 ha1
  have hv : ∀ p, p.Prime → ‖(fun p => if p = 2 then w else 0) p‖ ≤ 1 := fun p _ => by
    dsimp only; split_ifs
    · exact hw.le
    · simp
  set ω := BohrPoint.ofPrimes _ hv
  have h2 : ω.ω 2 = w := (BohrPoint.ofPrimes_apply_prime _ Nat.prime_two).trans (if_pos rfl)
  have h3 : ω.ω 3 = 0 :=
    (BohrPoint.ofPrimes_apply_prime _ Nat.prime_three).trans (if_neg (by norm_num))
  refine ⟨a, ha1, ha2, ω, mem_obstructionHull_towerTwisted_of_two hε hε2 ha1 ha2 hgood h2, ?_⟩
  unfold TiedAtTwoThree
  rw [h2, h3, norm_zero]
  have hwpos : 0 < ‖w‖ := by
    have ha0 : 0 < a := lt_trans (Real.rpow_pos_of_pos two_pos _) ha1
    refine norm_pos_iff.2 (div_ne_zero ?_ (ofReal_ne_zero.2 ha0.ne'))
    rw [Ne, cpow_eq_zero_iff]; norm_num
  have : 0 < Real.sqrt 3 * (‖w‖ / Real.sqrt 2) ^ Real.logb 2 3 := by positivity
  exact ne_of_lt this

end

end GaloisForLFunctions.ArithmeticOrientationTheory
