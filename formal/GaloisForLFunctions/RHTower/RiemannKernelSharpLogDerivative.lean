import GaloisForLFunctions.RHTower.RiemannKernelTailDecayRate

/-!
# The sharp logarithmic derivative of Riemann's kernel on the tail

On the tail `e^{2u} ≥ 3` Riemann's kernel satisfies

  `−2π(e^{2u} + 2) Φ(u) ≤ Φ'(u) ≤ (5 − 2πe^{2u}) Φ(u)`,

so `(log Φ)'(u) = −2πe^{2u} + O(1)`.  Termwise, with `Y = n²e^{2u}` and `R(Y) = 4π²Y² − 6πY`, the cusp
operator gives `DR(Y) + 2πY R(Y) = 18π²Y² − 15πY ∈ [0, 5R(Y)]` for `Y ≥ 3`.  The upper bound
follows from `Y ≥ e^{2u}`.  For the lower bound, the terms `n ≥ 2` carry the extra weight
`(n² − 1)e^{2u} ≤ e^{−(n−1)}/term₁ · term₁`, since `R(n²Y)/R(Y) ≤ 2n⁴` and
`2n⁴(n²−1) Y e^{−π(n²−1)Y} ≤ e^{−(n−1)}`.

Integrated forms (`riemannKernelReal_le_sharp`, `riemannKernelReal_ge_sharp`): for
`½ log 3 ≤ a ≤ b`,

  `Φ(a) e^{−π(e^{2b} − e^{2a}) − 4π(b − a)} ≤ Φ(b) ≤ Φ(a) e^{−π(e^{2b} − e^{2a}) + 5(b − a)}`.
-/

open Real Filter Topology Set Polynomial

namespace RHTower

noncomputable section

theorem cuspDeriv_riemannCuspPoly_add_eval (Y : ℝ) :
    (cuspDeriv riemannCuspPoly).eval Y + 2 * π * Y * riemannCuspPoly.eval Y =
      18 * π ^ 2 * Y ^ 2 - 15 * π * Y := by
  rw [cuspDeriv_riemannCuspPoly_eval, riemannCuspPoly_eval]
  ring

theorem riemannCuspPoly_eval_ge {Y : ℝ} (hY : 1 ≤ Y) :
    2 * π ^ 2 * Y ^ 2 ≤ riemannCuspPoly.eval Y := by
  rw [riemannCuspPoly_eval]
  have hπ := Real.pi_gt_three
  have h1 : 0 ≤ π * Y - 3 := by nlinarith
  have h2 : 0 ≤ π * Y := by positivity
  nlinarith [mul_nonneg h1 h2]

theorem riemannCuspPoly_eval_le (Y : ℝ) (hY : 0 ≤ Y) :
    riemannCuspPoly.eval Y ≤ 4 * π ^ 2 * Y ^ 2 := by
  rw [riemannCuspPoly_eval]
  nlinarith [Real.pi_pos]

theorem three_le_exp_two_mul {u : ℝ} (hu : Real.log 3 / 2 ≤ u) : 3 ≤ Real.exp (2 * u) := by
  have : Real.log 3 ≤ 2 * u := by linarith
  calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr this

/-- Termwise upper bound: `D(term) ≤ (5 − 2πe^{2u}) term` for `e^{2u} ≥ 3`. -/
theorem cuspTerm_cuspDeriv_riemannCuspPoly_le_sharp {n : ℕ} (hn : 1 ≤ n) {u : ℝ}
    (hu : Real.log 3 / 2 ≤ u) :
    cuspTerm (cuspDeriv riemannCuspPoly) n u ≤
      (5 - 2 * π * Real.exp (2 * u)) * cuspTerm riemannCuspPoly n u := by
  have hE := three_le_exp_two_mul hu
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  set Y : ℝ := (n : ℝ) ^ 2 * Real.exp (2 * u) with hYdef
  have hYE : Real.exp (2 * u) ≤ Y := by rw [hYdef]; nlinarith [Real.exp_pos (2 * u)]
  have hY3 : 3 ≤ Y := le_trans hE hYE
  have hR := riemannCuspPoly_eval_ge (show (1 : ℝ) ≤ Y by linarith)
  have hR0 : 0 ≤ riemannCuspPoly.eval Y := le_trans (by positivity) hR
  have hsum := cuspDeriv_riemannCuspPoly_add_eval Y
  have hπ := Real.pi_gt_three
  have hstep : (cuspDeriv riemannCuspPoly).eval Y ≤
      (5 - 2 * π * Real.exp (2 * u)) * riemannCuspPoly.eval Y := by
    have h1 : 18 * π ^ 2 * Y ^ 2 - 15 * π * Y ≤ 5 * riemannCuspPoly.eval Y := by
      rw [riemannCuspPoly_eval]
      have h1 : 0 ≤ 2 * π * Y - 15 := by nlinarith
      have h2 : 0 ≤ π * Y := by positivity
      nlinarith [mul_nonneg h1 h2]
    have h2 : 2 * π * Real.exp (2 * u) * riemannCuspPoly.eval Y ≤
        2 * π * Y * riemannCuspPoly.eval Y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYE (by positivity)) hR0
    nlinarith
  unfold cuspTerm
  rw [← hYdef]
  have hpos : 0 < Real.exp (u / 2) * Real.exp (-π * Y) := by positivity
  calc Real.exp (u / 2) * (cuspDeriv riemannCuspPoly).eval Y * Real.exp (-π * Y)
      = (Real.exp (u / 2) * Real.exp (-π * Y)) * (cuspDeriv riemannCuspPoly).eval Y := by ring
    _ ≤ (Real.exp (u / 2) * Real.exp (-π * Y)) *
        ((5 - 2 * π * Real.exp (2 * u)) * riemannCuspPoly.eval Y) :=
        mul_le_mul_of_nonneg_left hstep hpos.le
    _ = _ := by ring

/-- Termwise lower bound: `D(term) ≥ −2πn²e^{2u} term` for `e^{2u} ≥ 1`. -/
theorem cuspTerm_cuspDeriv_riemannCuspPoly_ge {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    -(2 * π) * cuspTerm (X * riemannCuspPoly) n u ≤ cuspTerm (cuspDeriv riemannCuspPoly) n u := by
  have hE : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  set Y : ℝ := (n : ℝ) ^ 2 * Real.exp (2 * u) with hYdef
  have hY1 : 1 ≤ Y := by rw [hYdef]; nlinarith
  have hsum := cuspDeriv_riemannCuspPoly_add_eval Y
  have hπ := Real.pi_gt_three
  have hstep : -(2 * π) * (Y * riemannCuspPoly.eval Y) ≤ (cuspDeriv riemannCuspPoly).eval Y := by
    have : 0 ≤ 18 * π ^ 2 * Y ^ 2 - 15 * π * Y := by
      have h1 : 0 ≤ 6 * π * Y - 5 := by nlinarith
      have h2 : 0 ≤ π * Y := by positivity
      nlinarith [mul_nonneg h1 h2]
    nlinarith
  unfold cuspTerm
  rw [← hYdef, eval_mul, eval_X]
  have hpos : 0 < Real.exp (u / 2) * Real.exp (-π * Y) := by positivity
  calc -(2 * π) * (Real.exp (u / 2) * (Y * riemannCuspPoly.eval Y) * Real.exp (-π * Y))
      = (Real.exp (u / 2) * Real.exp (-π * Y)) * (-(2 * π) * (Y * riemannCuspPoly.eval Y)) := by
        ring
    _ ≤ (Real.exp (u / 2) * Real.exp (-π * Y)) * (cuspDeriv riemannCuspPoly).eval Y :=
        mul_le_mul_of_nonneg_left hstep hpos.le
    _ = _ := by ring

theorem cuspTerm_X_mul (R : ℝ[X]) (n : ℕ) (u : ℝ) :
    cuspTerm (X * R) n u = (n : ℝ) ^ 2 * Real.exp (2 * u) * cuspTerm R n u := by
  unfold cuspTerm
  rw [eval_mul, eval_X]
  ring

/-- `2n⁴(n² − 1) Y e^{−π(n²−1)Y} ≤ e^{−(n−1)}` for `n ≥ 2`, `Y ≥ 1`. -/
theorem weight_exp_le {n : ℕ} (hn : 2 ≤ n) {Y : ℝ} (hY : 1 ≤ Y) :
    2 * (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 - 1) * Y * Real.exp (-(π * ((n : ℝ) ^ 2 - 1) * Y)) ≤
      Real.exp (-((n : ℝ) - 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) ^ 2 - 1 with hm
  have hm3 : 3 ≤ m := by rw [hm]; nlinarith
  have hπ := Real.pi_gt_three
  -- `Y e^{−πmY} ≤ e^{−πm}`
  have hY' : Y * Real.exp (-(π * m * Y)) ≤ Real.exp (-(π * m)) := by
    have h := Real.add_one_le_exp (π * m * (Y - 1))
    have hpm : 1 ≤ π * m := by nlinarith
    have hYle : Y ≤ Real.exp (π * m * (Y - 1)) := by nlinarith
    have e : Real.exp (-(π * m)) = Real.exp (π * m * (Y - 1)) * Real.exp (-(π * m * Y)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact mul_le_mul_of_nonneg_right hYle (Real.exp_pos _).le
  -- `n⁶ ≤ e^{6(n−1)}`
  have hn6 : (n : ℝ) ^ 6 ≤ Real.exp (6 * ((n : ℝ) - 1)) := by
    have h := Real.add_one_le_exp ((n : ℝ) - 1)
    rw [show ((n : ℝ) - 1) + 1 = n by ring] at h
    calc (n : ℝ) ^ 6 ≤ Real.exp ((n : ℝ) - 1) ^ 6 := pow_le_pow_left₀ (by positivity) h 6
      _ = Real.exp (6 * ((n : ℝ) - 1)) := by rw [← Real.exp_nat_mul]; norm_num
  have hpoly : 2 * (n : ℝ) ^ 4 * m ≤ Real.exp (1 + 6 * ((n : ℝ) - 1)) := by
    have h2 : 2 * (n : ℝ) ^ 4 * m ≤ 2 * (n : ℝ) ^ 6 := by rw [hm]; nlinarith [sq_nonneg (n : ℝ)]
    have h3 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.exp_add]
    nlinarith [Real.exp_pos (6 * ((n : ℝ) - 1))]
  have hexp : 1 + 6 * ((n : ℝ) - 1) - π * m ≤ -((n : ℝ) - 1) := by
    rw [hm]
    have : (3 : ℝ) * ((n : ℝ) ^ 2 - 1) ≤ π * ((n : ℝ) ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right hπ.le (by nlinarith)
    nlinarith
  calc 2 * (n : ℝ) ^ 4 * m * Y * Real.exp (-(π * m * Y))
      = 2 * (n : ℝ) ^ 4 * m * (Y * Real.exp (-(π * m * Y))) := by ring
    _ ≤ Real.exp (1 + 6 * ((n : ℝ) - 1)) * Real.exp (-(π * m)) :=
        mul_le_mul hpoly hY' (by positivity) (Real.exp_pos _).le
    _ = Real.exp (1 + 6 * ((n : ℝ) - 1) - π * m) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-((n : ℝ) - 1)) := Real.exp_le_exp.mpr hexp

/-- The weight of the term `n ≥ 2` against the first term. -/
theorem cuspTerm_weight_le {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    ((n : ℝ) ^ 2 - 1) * Real.exp (2 * u) * cuspTerm riemannCuspPoly n u ≤
      Real.exp (-((n : ℝ) - 1)) * cuspTerm riemannCuspPoly 1 u := by
  set Y₁ := Real.exp (2 * u) with hY₁
  have hY1 : 1 ≤ Y₁ := Real.one_le_exp (by linarith)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hRn := riemannCuspPoly_eval_le ((n : ℝ) ^ 2 * Y₁) (by positivity)
  have hR1 := riemannCuspPoly_eval_ge hY1
  have hw := weight_exp_le hn hY1
  unfold cuspTerm
  rw [← hY₁]
  simp only [Nat.cast_one, one_pow, one_mul]
  have hA : 0 < Real.exp (u / 2) := Real.exp_pos _
  have hm : 0 ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
  have hsplit : Real.exp (-π * ((n : ℝ) ^ 2 * Y₁)) =
      Real.exp (-(π * ((n : ℝ) ^ 2 - 1) * Y₁)) * Real.exp (-π * Y₁) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  calc ((n : ℝ) ^ 2 - 1) * Y₁ * (Real.exp (u / 2) * riemannCuspPoly.eval ((n : ℝ) ^ 2 * Y₁) *
        (Real.exp (-(π * ((n : ℝ) ^ 2 - 1) * Y₁)) * Real.exp (-π * Y₁)))
      ≤ ((n : ℝ) ^ 2 - 1) * Y₁ * (Real.exp (u / 2) * (4 * π ^ 2 * ((n : ℝ) ^ 2 * Y₁) ^ 2) *
        (Real.exp (-(π * ((n : ℝ) ^ 2 - 1) * Y₁)) * Real.exp (-π * Y₁))) := by
        gcongr
    _ = (2 * (n : ℝ) ^ 4 * ((n : ℝ) ^ 2 - 1) * Y₁ *
          Real.exp (-(π * ((n : ℝ) ^ 2 - 1) * Y₁))) *
        (Real.exp (u / 2) * (2 * π ^ 2 * Y₁ ^ 2) * Real.exp (-π * Y₁)) := by ring
    _ ≤ Real.exp (-((n : ℝ) - 1)) *
        (Real.exp (u / 2) * riemannCuspPoly.eval Y₁ * Real.exp (-π * Y₁)) := by
        refine mul_le_mul hw ?_ (by positivity) (Real.exp_pos _).le
        gcongr

/-- `Φ'(u) ≤ (5 − 2πe^{2u}) Φ(u)` for `e^{2u} ≥ 3`, in cusp-series form. -/
theorem cuspSeries_cuspDeriv_riemannCuspPoly_le_sharp {u : ℝ} (hu : Real.log 3 / 2 ≤ u) :
    cuspSeries (cuspDeriv riemannCuspPoly) u ≤
      (5 - 2 * π * Real.exp (2 * u)) * cuspSeries riemannCuspPoly u := by
  unfold cuspSeries
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun n => cuspTerm_cuspDeriv_riemannCuspPoly_le_sharp (Nat.succ_le_succ (Nat.zero_le n)) hu)
    (summable_cuspTerm _ u) ((summable_cuspTerm _ u).mul_left _)

/-- `Φ'(u) ≥ −2π(e^{2u} + 2) Φ(u)` for `u ≥ 0`, in cusp-series form. -/
theorem cuspSeries_cuspDeriv_riemannCuspPoly_ge_sharp {u : ℝ} (hu : 0 ≤ u) :
    -(2 * π * (Real.exp (2 * u) + 2)) * cuspSeries riemannCuspPoly u ≤
      cuspSeries (cuspDeriv riemannCuspPoly) u := by
  set Y₁ := Real.exp (2 * u) with hY₁
  set T₁ := cuspTerm riemannCuspPoly 1 u with hT₁
  have hsX := summable_cuspTerm (X * riemannCuspPoly) u
  have hsR := summable_cuspTerm riemannCuspPoly u
  have hT₁le : T₁ ≤ cuspSeries riemannCuspPoly u := by
    unfold cuspSeries
    have := hsR.le_tsum 0 (fun n _ => (cuspTerm_riemannCuspPoly_pos (Nat.succ_pos n) hu).le)
    simpa [hT₁] using this
  -- `Σ n² Y₁ term_n ≤ (Y₁ + 2) Φ`
  have hgeom : Summable fun k : ℕ => Real.exp (-(k : ℝ)) * T₁ :=
    (Real.summable_exp_neg_nat).mul_right _
  have hterm : ∀ k : ℕ, cuspTerm (X * riemannCuspPoly) (k + 1) u ≤
      Y₁ * cuspTerm riemannCuspPoly (k + 1) u + Real.exp (-(k : ℝ)) * T₁ := by
    intro k
    rw [cuspTerm_X_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Nat.zero_add, Nat.cast_one, one_pow, one_mul, Nat.cast_zero, neg_zero,
        Real.exp_zero]
      have := (cuspTerm_riemannCuspPoly_pos (n := 1) le_rfl hu).le
      rw [← hY₁]; linarith
    · have hw := cuspTerm_weight_le (n := k + 1) (by omega) hu
      push_cast at hw ⊢
      rw [show ((k : ℝ) + 1) - 1 = k by ring] at hw
      rw [← hY₁] at hw ⊢
      nlinarith
  have hXle : ∑' k, cuspTerm (X * riemannCuspPoly) (k + 1) u ≤
      Y₁ * cuspSeries riemannCuspPoly u + (∑' k : ℕ, Real.exp (-(k : ℝ))) * T₁ := by
    unfold cuspSeries
    rw [← tsum_mul_left, ← tsum_mul_right, ← Summable.tsum_add (hsR.mul_left _) hgeom]
    exact Summable.tsum_le_tsum hterm hsX ((hsR.mul_left _).add hgeom)
  have hgsum : ∑' k : ℕ, Real.exp (-(k : ℝ)) ≤ 2 := by
    have e : (fun k : ℕ => Real.exp (-(k : ℝ))) = fun k => (Real.exp (-1)) ^ k := by
      funext k; rw [← Real.exp_nat_mul]; ring_nf
    rw [e, tsum_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by norm_num))]
    have h := Real.add_one_le_exp (1 : ℝ)
    have hE1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-1)
    have hhalf : Real.exp (-1) ≤ 1 / 2 := by nlinarith
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hT₁0 : 0 ≤ T₁ := (cuspTerm_riemannCuspPoly_pos (n := 1) le_rfl hu).le
  have hlow : ∑' k, -(2 * π) * cuspTerm (X * riemannCuspPoly) (k + 1) u ≤
      cuspSeries (cuspDeriv riemannCuspPoly) u := by
    unfold cuspSeries
    exact Summable.tsum_le_tsum
      (fun k => cuspTerm_cuspDeriv_riemannCuspPoly_ge (Nat.succ_le_succ (Nat.zero_le k)) hu)
      (hsX.mul_left _) (summable_cuspTerm _ u)
  rw [tsum_mul_left] at hlow
  have hΦ0 : 0 ≤ cuspSeries riemannCuspPoly u := (cuspSeries_riemannCuspPoly_pos hu).le
  have hπ := Real.pi_pos
  have h2 : (∑' k : ℕ, Real.exp (-(k : ℝ))) * T₁ ≤ 2 * cuspSeries riemannCuspPoly u :=
    le_trans (mul_le_mul_of_nonneg_right hgsum hT₁0) (by linarith)
  nlinarith

/-! ## Integrated forms -/

private theorem hasDerivAt_riemannKernelReal_of_pos' {u : ℝ} (hu : 0 < u) :
    HasDerivAt riemannKernelReal (cuspSeries (cuspDeriv riemannCuspPoly) u) u := by
  have h := hasDerivAt_cuspSeries riemannCuspPoly u
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hu] with x hx
  exact riemannKernelReal_of_nonneg hx.le

/-- **Sharp upper tail.**  `Φ(b) ≤ Φ(a) e^{−π(e^{2b} − e^{2a}) + 5(b − a)}` for `½ log 3 ≤ a ≤ b`. -/
theorem riemannKernelReal_le_sharp {a b : ℝ} (ha : Real.log 3 / 2 ≤ a) (hab : a ≤ b) :
    riemannKernelReal b ≤
      riemannKernelReal a * Real.exp (-(π * (Real.exp (2 * b) - Real.exp (2 * a))) + 5 * (b - a)) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  set h : ℝ → ℝ := fun x => riemannKernelReal x * Real.exp (π * Real.exp (2 * x) - 5 * x) with hh
  have hderiv : ∀ x, 0 < x → HasDerivAt h
      (cuspSeries (cuspDeriv riemannCuspPoly) x * Real.exp (π * Real.exp (2 * x) - 5 * x) +
        riemannKernelReal x * (Real.exp (π * Real.exp (2 * x) - 5 * x) *
          (π * (Real.exp (2 * x) * 2) - 5))) x := by
    intro x hx
    have h1 := hasDerivAt_riemannKernelReal_of_pos' hx
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (π * Real.exp (2 * x) - 5 * x))
        (Real.exp (π * Real.exp (2 * x) - 5 * x) * (π * (Real.exp (2 * x) * 2) - 5)) x := by
      have hin : HasDerivAt (fun x : ℝ => π * Real.exp (2 * x) - 5 * x)
          (π * (Real.exp (2 * x) * 2) - 5) x := by
        have h1 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (Real.exp (2 * x) * 2) x :=
          (((hasDerivAt_id' x).const_mul 2).exp).congr_deriv (by ring)
        exact ((h1.const_mul π).sub ((hasDerivAt_id' x).const_mul 5)).congr_deriv (by ring)
      exact hin.exp
    exact h1.mul h2
  have hanti : AntitoneOn h (Ici a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici a)
    · exact fun x hx => (hderiv x (lt_of_lt_of_le ha0 hx)).continuousAt.continuousWithinAt
    · exact fun x hx => (hderiv x (lt_of_lt_of_le ha0 (interior_subset hx))).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : a < x := hx
      have hx0 : 0 < x := ha0.trans hx'
      rw [(hderiv x hx0).deriv]
      have hD := cuspSeries_cuspDeriv_riemannCuspPoly_le_sharp (le_trans ha hx'.le)
      rw [← riemannKernelReal_of_nonneg hx0.le] at hD
      have hE := Real.exp_pos (π * Real.exp (2 * x) - 5 * x)
      nlinarith
  have hle := hanti self_mem_Ici (show b ∈ Ici a from hab) hab
  simp only [hh] at hle
  have hEb := Real.exp_pos (π * Real.exp (2 * b) - 5 * b)
  have e : Real.exp (-(π * (Real.exp (2 * b) - Real.exp (2 * a))) + 5 * (b - a)) =
      Real.exp (π * Real.exp (2 * a) - 5 * a) / Real.exp (π * Real.exp (2 * b) - 5 * b) := by
    rw [← Real.exp_sub]; ring_nf
  rw [e, mul_div_assoc', le_div_iff₀ hEb]
  exact hle

/-- **Sharp lower tail.**  `Φ(a) e^{−π(e^{2b} − e^{2a}) − 4π(b − a)} ≤ Φ(b)` for `0 ≤ a ≤ b`. -/
theorem riemannKernelReal_ge_sharp {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    riemannKernelReal a * Real.exp (-(π * (Real.exp (2 * b) - Real.exp (2 * a))) - 4 * π * (b - a)) ≤
      riemannKernelReal b := by
  set h : ℝ → ℝ := fun x => riemannKernelReal x * Real.exp (π * Real.exp (2 * x) + 4 * π * x)
    with hh
  have hderiv : ∀ x, 0 < x → HasDerivAt h
      (cuspSeries (cuspDeriv riemannCuspPoly) x * Real.exp (π * Real.exp (2 * x) + 4 * π * x) +
        riemannKernelReal x * (Real.exp (π * Real.exp (2 * x) + 4 * π * x) *
          (π * (Real.exp (2 * x) * 2) + 4 * π))) x := by
    intro x hx
    have h1 := hasDerivAt_riemannKernelReal_of_pos' hx
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (π * Real.exp (2 * x) + 4 * π * x))
        (Real.exp (π * Real.exp (2 * x) + 4 * π * x) * (π * (Real.exp (2 * x) * 2) + 4 * π)) x := by
      have hin : HasDerivAt (fun x : ℝ => π * Real.exp (2 * x) + 4 * π * x)
          (π * (Real.exp (2 * x) * 2) + 4 * π) x := by
        have h1 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (Real.exp (2 * x) * 2) x :=
          (((hasDerivAt_id' x).const_mul 2).exp).congr_deriv (by ring)
        exact ((h1.const_mul π).add ((hasDerivAt_id' x).const_mul (4 * π))).congr_deriv (by ring)
      exact hin.exp
    exact h1.mul h2
  have hmono : MonotoneOn h (Ici a) := by
    have hcont : ContinuousOn h (Ici a) := by
      have := continuous_riemannKernelReal
      exact (this.mul (by fun_prop)).continuousOn
    apply monotoneOn_of_deriv_nonneg (convex_Ici a) hcont
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x (lt_of_le_of_lt ha hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := lt_of_le_of_lt ha hx
      rw [(hderiv x hx0).deriv]
      have hD := cuspSeries_cuspDeriv_riemannCuspPoly_ge_sharp hx0.le
      rw [← riemannKernelReal_of_nonneg hx0.le] at hD
      have hE := Real.exp_pos (π * Real.exp (2 * x) + 4 * π * x)
      nlinarith
  have hle := hmono self_mem_Ici (show b ∈ Ici a from hab) hab
  simp only [hh] at hle
  have hEb := Real.exp_pos (π * Real.exp (2 * b) + 4 * π * b)
  have e : Real.exp (-(π * (Real.exp (2 * b) - Real.exp (2 * a))) - 4 * π * (b - a)) =
      Real.exp (π * Real.exp (2 * a) + 4 * π * a) / Real.exp (π * Real.exp (2 * b) + 4 * π * b) := by
    rw [← Real.exp_sub]; ring_nf
  rw [e, mul_div_assoc', div_le_iff₀ hEb]
  exact hle

end

end RHTower
