/-
# The necessity half of the determinant-completion law, unconditionally

The plain determinant of a Schatten-`p` operator is its order-`p` regularized determinant times the
exponential of the polynomial of its first `p-1` power traces.  If the plain determinants of a
Schatten-converging family converge *locally uniformly* -- the compact-open topology the completion
law is stated in -- then the limit is holomorphic and equals `1` at the origin, so Weierstrass
convergence supplies the derivative limits and continuity supplies the nonvanishing that the graph
closure needs.  No hypothesis beyond membership in the closure survives.

Main results:
* `lowTracePoly` — the polynomial of the trace coordinates below the order.
* `opSchattenDet_one_eq_mul_exp_lowTracePoly` — **the plain determinant factors**.
* `differentiableOn_opSchattenDet_one`, `opSchattenDet_apply_zero` — it is holomorphic and unital.
* `exists_poly_of_tendstoLocallyUniformlyOn_opSchattenDet` — **the necessity half of `(DC)`,
  unconditionally**: a locally uniform limit of plain determinants of a Schatten-converging
  finite-rank family is `exp(Q)` times the order-`p` regularized determinant of the limit.
-/
import GaloisForLFunctions.HTGeometry.OperatorDeterminantSufficiency

open Filter Topology Metric ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-! ## The polynomial of the trace coordinates below the order -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The polynomial carrying the trace coordinates below the regularization order. -/
def lowTracePoly (p : ℕ) (S : H →L[ℂ] H) : Polynomial ℂ :=
  ∑ m ∈ Finset.Ico 1 p, Polynomial.C (-(opTrace (S ^ m) / (m : ℂ))) * Polynomial.X ^ m

theorem eval_lowTracePoly (p : ℕ) (S : H →L[ℂ] H) (z : ℂ) :
    Polynomial.eval z (lowTracePoly p S)
      = -∑ m ∈ Finset.Ico 1 p, tracePowerTerm (fun m => opTrace (S ^ m)) z m := by
  rw [lowTracePoly, Polynomial.eval_finsetSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    tracePowerTerm]
  ring

theorem natDegree_lowTracePoly_le (p : ℕ) (S : H →L[ℂ] H) :
    (lowTracePoly p S).natDegree ≤ p - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [Finset.mem_Ico] at hm
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have h1 : (Polynomial.C (-(opTrace (S ^ m) / (m : ℂ)))).natDegree = 0 :=
    Polynomial.natDegree_C _
  have h2 : ((Polynomial.X : Polynomial ℂ) ^ m).natDegree ≤ m := by
    simp
  omega

theorem coeff_zero_lowTracePoly (p : ℕ) (S : H →L[ℂ] H) : (lowTracePoly p S).coeff 0 = 0 := by
  rw [lowTracePoly, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mem_Ico] at hm
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

/-! ## The plain determinant factors, is holomorphic, and is unital -/

theorem opSchattenDet_apply_zero {q : ℕ} (hq : 0 < q) (S : H →L[ℂ] H) :
    opSchattenDet q S 0 = 1 := by
  rw [opSchattenDet_eq_tracePowerDet, tracePowerDet]
  have hexp : tracePowerDetExp q (fun m => opTrace (S ^ m)) (0 : ℂ) = 0 := by
    rw [tracePowerDetExp]
    have hzero : ∀ k : ℕ,
        (0 : ℂ) ^ (k + q) / ((k + q : ℕ) : ℂ) * opTrace (S ^ (k + q)) = 0 := by
      intro k
      rw [zero_pow (by omega : k + q ≠ 0)]
      simp
    rw [tsum_congr hzero, tsum_zero]
  rw [hexp, neg_zero, Complex.exp_zero]

/-! ## The plain determinant factors and is holomorphic -/

section Factor

variable {p : ℕ} {S : H →L[ℂ] H} {C : ℝ}

/-- **The plain determinant factors** as the order-`p` regularized determinant times the
exponential of the polynomial of the trace coordinates below the order. -/
theorem opSchattenDet_one_eq_mul_exp_lowTracePoly (hp : 0 < p)
    (hS : MemSchattenClass (p : ℝ) S) (hC1 : 1 ≤ C) (hC : schattenNorm (p : ℝ) S ≤ C)
    {z : ℂ} (hz : ‖z‖ * (2 * C) < 1) :
    opSchattenDet 1 S z
      = opSchattenDet p S z * Complex.exp (Polynomial.eval z (lowTracePoly p S)) := by
  have hB1 : (1 : ℝ) ≤ 2 * C := by linarith
  have hbound : ∀ k : ℕ, ‖(fun m => opTrace (S ^ m)) (k + p)‖
      ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
    fun k => norm_opTrace_pow_add_le hp hS hC1 hC k
  have hord :=
    tracePowerDet_order_shift (τ := fun m => opTrace (S ^ m)) hp hB1 hbound hz (q := 1) hp
  rw [opSchattenDet_eq_tracePowerDet, opSchattenDet_eq_tracePowerDet, hord, eval_lowTracePoly]

/-- The plain determinant is holomorphic on the disc of convergence. -/
theorem differentiableOn_opSchattenDet_one (hp : 0 < p)
    (hS : MemSchattenClass (p : ℝ) S) (hC1 : 1 ≤ C) (hC : schattenNorm (p : ℝ) S ≤ C)
    {r : ℝ} (hr : 0 < r) (hrB : r * (2 * C) < 1) :
    DifferentiableOn ℂ (fun z => opSchattenDet 1 S z) (ball (0 : ℂ) r) := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hB1 : (1 : ℝ) ≤ 2 * C := by linarith
  have hS0 : (0 : ℝ) ≤ (1 + (p : ℝ)) * C ^ (p : ℝ) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hC0.le _)
  have hbound : ∀ k : ℕ, ‖(fun m => opTrace (S ^ m)) (k + p)‖
      ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
    fun k => norm_opTrace_pow_add_le hp hS hC1 hC k
  have hsmall : ∀ z ∈ ball (0 : ℂ) r, ‖z‖ * (2 * C) < 1 := by
    intro z hz
    have hzr : ‖z‖ < r := by simpa using mem_ball_zero_iff.mp hz
    have : ‖z‖ * (2 * C) < r * (2 * C) :=
      mul_lt_mul_of_pos_right hzr (by linarith)
    linarith
  have hmain : DifferentiableOn ℂ
      (fun z => opSchattenDet p S z * Complex.exp (Polynomial.eval z (lowTracePoly p S)))
      (ball (0 : ℂ) r) := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 : DifferentiableAt ℂ (fun w => opSchattenDet p S w) z :=
      differentiableAt_tracePowerDet (τ := fun m => opTrace (S ^ m)) hp hB1 hS0 hbound hr hrB hz
    have h2 : DifferentiableAt ℂ
        (fun w : ℂ => Complex.exp (Polynomial.eval w (lowTracePoly p S))) z :=
      (Polynomial.differentiable (lowTracePoly p S)).differentiableAt.cexp
    exact h1.mul h2
  exact hmain.congr fun z hz =>
    opSchattenDet_one_eq_mul_exp_lowTracePoly hp hS hC1 hC (hsmall z hz)

end Factor

/-! ## The unconditional necessity half of `(DC)` -/

set_option maxHeartbeats 1000000 in
/-- **The necessity half of `(DC)`, unconditionally.**  If finite-rank -- or merely Schatten --
operators converge in the Schatten `p`-norm and their plain determinants converge locally uniformly
on a disc, then on a possibly smaller disc the limit is the order-`p` regularized determinant of the
limit operator times the exponential of a jet of degree below `p` with vanishing constant term. -/
theorem exists_poly_of_tendstoLocallyUniformlyOn_opSchattenDet {p : ℕ} (hp : 0 < p)
    {A : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : ∀ n, MemSchattenClass (p : ℝ) (A n)) (hT : MemSchattenClass (p : ℝ) T)
    (hD : ∀ n, MemSchattenClass (p : ℝ) (A n - T))
    {C : ℝ} (hC1 : 1 ≤ C) (hCA : ∀ n, schattenNorm (p : ℝ) (A n) ≤ C)
    (hCT : schattenNorm (p : ℝ) T ≤ C)
    (htend : Tendsto (fun n => schattenNorm (p : ℝ) (A n - T)) atTop (nhds 0))
    {r : ℝ} (hr : 0 < r) (hrB : r * (2 * C) < 1) {F : ℂ → ℂ}
    (hF : TendstoLocallyUniformlyOn (fun n z => opSchattenDet 1 (A n) z) F atTop
      (ball (0 : ℂ) r)) :
    ∃ (ρ : ℝ) (Q : Polynomial ℂ), 0 < ρ ∧ ρ ≤ r ∧ Q.natDegree ≤ p - 1 ∧ Q.coeff 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) ρ, F z = opSchattenDet p T z * Complex.exp (Polynomial.eval z Q) := by
  classical
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hsmall : ∀ z ∈ ball (0 : ℂ) r, ‖z‖ * (2 * C) < 1 := by
    intro z hz
    have hzr : ‖z‖ < r := by simpa using mem_ball_zero_iff.mp hz
    have : ‖z‖ * (2 * C) < r * (2 * C) := mul_lt_mul_of_pos_right hzr (by linarith)
    linarith
  rcases Nat.lt_or_ge p 2 with hp1 | hp2
  · -- order one: there is no polynomial factor at all
    have hpe : p = 1 := by omega
    subst hpe
    refine ⟨r, 0, hr, le_rfl, by simp, by simp, fun z hz => ?_⟩
    have h1 := hF.tendsto_at hz
    have h2 := tendsto_opSchattenDet_of_tendsto_schattenNorm hp hA hT hD hC1 hCA htend
      (z := z) (hsmall z hz)
    rw [Polynomial.eval_zero, Complex.exp_zero, mul_one]
    exact tendsto_nhds_unique h1 h2
  · -- order at least two
    have hdiffn : ∀ n, DifferentiableOn ℂ (fun z => opSchattenDet 1 (A n) z) (ball (0 : ℂ) r) :=
      fun n => differentiableOn_opSchattenDet_one hp (hA n) hC1 (hCA n) hr hrB
    have hFdiff : DifferentiableOn ℂ F (ball (0 : ℂ) r) :=
      hF.differentiableOn (Eventually.of_forall hdiffn) isOpen_ball
    have hF0 : F 0 = 1 := by
      have h := hF.tendsto_at (mem_ball_self hr)
      have hconst : Tendsto (fun n => opSchattenDet 1 (A n) (0 : ℂ)) atTop (nhds 1) := by
        have : (fun n => opSchattenDet 1 (A n) (0 : ℂ)) = fun _ => (1 : ℂ) :=
          funext fun n => opSchattenDet_apply_zero one_pos (A n)
        rw [this]
        exact tendsto_const_nhds
      exact tendsto_nhds_unique h hconst
    have hFcont : ContinuousAt F 0 :=
      hFdiff.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    have hne : ∀ᶠ z in nhds (0 : ℂ), F z ≠ 0 := hFcont.eventually_ne (by rw [hF0]; norm_num)
    obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ := Metric.eventually_nhds_iff.mp hne
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min ρ₀ r := ⟨_, rfl⟩
    have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hρ₀pos hr
    have hρr : ρ ≤ r := by rw [hρdef]; exact min_le_right _ _
    have hρ₀le : ρ ≤ ρ₀ := by rw [hρdef]; exact min_le_left _ _
    have hsub : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) r := ball_subset_ball hρr
    have hρB : ρ * (2 * C) < 1 := by nlinarith [hρr, hC0]
    -- the sample nodes
    obtain ⟨v, hvdef⟩ : ∃ v : Fin (p - 2 + 1) → ℂ,
        v = fun i : Fin (p - 2 + 1) =>
          ((ρ * (((i : ℕ) : ℝ) + 1) / (((p : ℕ) : ℝ) + 1) : ℝ) : ℂ) := ⟨_, rfl⟩
    have hden : (0 : ℝ) < ((p : ℕ) : ℝ) + 1 := by positivity
    have hv : Function.Injective v := by
      intro i j hij
      rw [hvdef] at hij
      have h1 : ρ * (((i : ℕ) : ℝ) + 1) / (((p : ℕ) : ℝ) + 1)
          = ρ * (((j : ℕ) : ℝ) + 1) / (((p : ℕ) : ℝ) + 1) := Complex.ofReal_inj.mp hij
      have hρne : ρ ≠ 0 := ne_of_gt hρpos
      field_simp at h1
      have h3 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith
      exact Fin.ext (by exact_mod_cast h3)
    have hvU : ∀ i, v i ∈ ball (0 : ℂ) ρ := by
      intro i
      rw [hvdef, mem_ball_zero_iff]
      have hilt : ((i : ℕ) : ℝ) + 1 < ((p : ℕ) : ℝ) + 1 := by
        have : (i : ℕ) < p := by have := i.isLt; omega
        have hc : ((i : ℕ) : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hpos : 0 ≤ ρ * (((i : ℕ) : ℝ) + 1) / (((p : ℕ) : ℝ) + 1) := by positivity
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos, div_lt_iff₀ hden]
      nlinarith
    have hvne : ∀ i, F (v i) ≠ 0 := by
      intro i
      refine hρ₀ ?_
      have := mem_ball_zero_iff.mp (hvU i)
      rw [dist_zero_right]
      linarith [this, hρ₀le]
    -- the factorisation of the plain determinants
    have hfact : ∀ (n : ℕ), ∀ z ∈ ball (0 : ℂ) r, opSchattenDet 1 (A n) z
        = opSchattenDet p (A n) z * Complex.exp (Polynomial.eval z (lowTracePoly p (A n))) :=
      fun n z hz => opSchattenDet_one_eq_mul_exp_lowTracePoly hp (hA n) hC1 (hCA n) (hsmall z hz)
    have hFval : ∀ z ∈ ball (0 : ℂ) ρ, Tendsto
        (fun n => opSchattenDet p (A n) z
          * Complex.exp (Polynomial.eval z (lowTracePoly p (A n)))) atTop (nhds (F z)) := by
      intro z hz
      have h := hF.tendsto_at (hsub hz)
      refine h.congr fun n => hfact n z (hsub hz)
    have hFder : ∀ i, Tendsto (fun n => deriv (fun w : ℂ =>
        opSchattenDet p (A n) w * Complex.exp (Polynomial.eval w (lowTracePoly p (A n)))) (v i))
        atTop (nhds (deriv F (v i))) := by
      intro i
      have hderiv := hF.deriv (Eventually.of_forall hdiffn) isOpen_ball
      have h := hderiv.tendsto_at (hsub (hvU i))
      refine h.congr fun n => ?_
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_ball.mem_nhds (hsub (hvU i))] with w hw
      exact hfact n w hw
    obtain ⟨Q, hQdeg, hQ0, -, hQval⟩ :=
      exists_poly_limit_of_tendsto_opSchattenDet (J := p - 2) hp hA hT hD hC1 hCA hCT htend
        hρpos hρB (P := fun n => lowTracePoly p (A n))
        (fun n => by
          have := natDegree_lowTracePoly_le p (A n)
          omega)
        (fun n => coeff_zero_lowTracePoly p (A n)) hv hvU hFval hFder hvne
    refine ⟨ρ, Q, hρpos, hρr, by omega, hQ0, hQval⟩

end

end GaloisForLFunctions.HTGeometry
