/-
# Hurwitz N=2 — wiring the linear block to the unconditional theorem

Discharges the `hrow`/`h0`/`h1`/`hc` hypotheses of `HurwitzN2Theorem.hurwitz_n2` from the genuine
relation alone, by extracting them from the vanishing of the monodromy blocks.

* `hrow` comes from the **top** Laurent coefficient of the linear block `Ψb`. Regrouping `Ψb` by the
  singular exponential `E_k = e^{−(s+k)z}` (`psi_regroup`) and peeling the top coefficient with
  `HurwitzSpine.quadratic_filtration_top` (in `x = e^z → 0`, no `cpow`) gives
  `C_2(0) = (q_{02}+q_{20})(−n)·ζ(s,−n) + l_2(−n) = 0` (using the triangular facts `q_{22}=0`,
  `q_{12}+q_{21}=0` from the quadratic descent and `tailFactored_zero_eq`).
* Once the density-shadow non-rationality (`survivor_killed`) forces `q_{02}+q_{20}=0` (so `q_{11}=0`),
  the cross terms of `Ψb` vanish identically and `Ψb` collapses to the **pure** linear block
  `∑_k l_k·E_k`; `lin_descent` then forces `l_0=l_1=l_2=0`, and `Θb=0` forces `c=0`.
-/
import GaloisForLFunctions.Hurwitz.N2Theorem
import GaloisForLFunctions.Hurwitz.N2TailValue
import GaloisForLFunctions.Hurwitz.N2PsiRegroup
import GaloisForLFunctions.Hurwitz.N2TailAnalytic

open Complex Filter Topology HurwitzN2Main HurwitzN2Tail HurwitzN2BlockAnalytic HurwitzSpine
  HurwitzN2Descent HurwitzN2PsiRegroup

namespace HurwitzN2Final

/-- The linear block regrouped by `E_w`: the `E_w`-coefficient
`C_w(x) = ∑_j (q_{wj}+q_{jw})(−n+x)·R_j(x) + l_w(−n+x)` (here `R_j(x) = tailFactored s j n x`). -/
noncomputable def Cfun (s : ℂ) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ)
    (w : Fin 3) (x : ℂ) : ℂ :=
  (∑ j : Fin 3, ((q w j + q j w).eval (-(n : ℂ) + x)) * tailFactored s (j : ℕ) n x)
    + (l w).eval (-(n : ℂ) + x)

/-- `C_w` is continuous at `x = 0` (polynomials + the analytic factored tail). -/
theorem Cfun_continuousAt {s : ℂ} (hs : 1 < s.re) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ)
    (l : Fin 3 → Polynomial ℂ) (w : Fin 3) : ContinuousAt (Cfun s n q l w) 0 := by
  unfold Cfun
  have htail : ∀ j : Fin 3, ContinuousAt (fun x : ℂ => tailFactored s (j : ℕ) n x) 0 :=
    fun j => ((tailFactored_analytic hs (j : ℕ) n).continuousOn).continuousAt
      (IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) (by norm_num))
  have hpoly : ∀ p : Polynomial ℂ, ContinuousAt (fun x : ℂ => p.eval (-(n : ℂ) + x)) 0 :=
    fun p => ((Polynomial.continuous p).comp (by fun_prop)).continuousAt
  simp only [Fin.sum_univ_three]
  exact ((((hpoly _).mul (htail 0)).add ((hpoly _).mul (htail 1))).add
    ((hpoly _).mul (htail 2))).add (hpoly _)

/-- `exp((s+2)·Log x)·exp(−(s+w)·Log x) = x^{2−w}` for `x ≠ 0` (`w ≤ 2`): the exponentials collapse to a
non-negative integer power of `x`, the form `quadratic_filtration_top` consumes. -/
theorem exp_collapse {s x : ℂ} (hx : x ≠ 0) (w : Fin 3) :
    Complex.exp ((s + 2) * Complex.log x) * Complex.exp (-(s + (w : ℂ)) * Complex.log x)
      = x ^ (2 - (w : ℕ)) := by
  have hw : (w : ℕ) ≤ 2 := Nat.lt_succ_iff.mp w.isLt
  have hcast : ((2 - (w : ℕ) : ℕ) : ℂ) = 2 - (w : ℂ) := by
    rw [Nat.cast_sub hw]; push_cast; ring
  rw [← Complex.exp_add,
    show (s + 2) * Complex.log x + -(s + (w : ℂ)) * Complex.log x
        = ((2 - (w : ℕ) : ℕ) : ℂ) * Complex.log x by rw [hcast]; ring,
    Complex.exp_nat_mul, Complex.exp_log hx]

/-- **From `Ψb = 0` to the `quadratic_filtration_top` form.** On the punctured neighborhood of `0`
(`x = e^z`, `z` deep in the half-plane), the linear block vanishing gives `∑_w C_w(x)·x^{2−w} = 0`. -/
theorem psi_to_qft {s : ℂ} (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ)
    (hPsi0 : ∀ z : ℂ, z.re < -Real.log 2 →
      PsiB s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    ∀ᶠ x : ℂ in 𝓝[≠] (0 : ℂ), ∑ w : Fin 3, Cfun s n q l w x * x ^ (2 - (w : ℕ)) = 0 := by
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1/2)),
    self_mem_nhdsWithin] with x hxball hxne
  have hxne' : x ≠ 0 := hxne
  have hnorm : ‖x‖ < 1/2 := by
    have := Metric.mem_ball.mp hxball; rwa [dist_zero_right] at this
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne'
  have hexp_x : Complex.exp (Complex.log x) = x := Complex.exp_log hxne'
  have hz_re : (Complex.log x).re < -Real.log 2 := by
    rw [Complex.log_re]
    have h12 : Real.log ‖x‖ < Real.log (1/2) := Real.log_lt_log hxpos hnorm
    rwa [one_div, Real.log_inv] at h12
  have hPsi := hPsi0 (Complex.log x) hz_re
  have hreg : PsiB s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) (Complex.log x)
      = ∑ k : Fin 3, ((∑ j : Fin 3,
          ((q k j).eval (-(n : ℂ) + Complex.exp (Complex.log x))
            + (q j k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
            * tailFactored s (j : ℕ) n (Complex.exp (Complex.log x)))
        + (l k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
        * Complex.exp (-(s + (k : ℂ)) * Complex.log x) := by
    rw [PsiB]
    exact psi_regroup (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
      (fun k => (l k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
      (fun j => tailFactored s (j : ℕ) n (Complex.exp (Complex.log x)))
      (fun k => Complex.exp (-(s + (k : ℂ)) * Complex.log x))
  rw [hreg] at hPsi
  rw [show (∑ w : Fin 3, Cfun s n q l w x * x ^ (2 - (w : ℕ)))
        = Complex.exp ((s + 2) * Complex.log x) * (∑ k : Fin 3,
          ((∑ j : Fin 3,
            ((q k j).eval (-(n : ℂ) + Complex.exp (Complex.log x))
              + (q j k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
              * tailFactored s (j : ℕ) n (Complex.exp (Complex.log x)))
          + (l k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
          * Complex.exp (-(s + (k : ℂ)) * Complex.log x)) from ?_, hPsi, mul_zero]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hC : Cfun s n q l w x
      = (∑ j : Fin 3, ((q w j).eval (-(n : ℂ) + Complex.exp (Complex.log x))
            + (q j w).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
            * tailFactored s (j : ℕ) n (Complex.exp (Complex.log x)))
        + (l w).eval (-(n : ℂ) + Complex.exp (Complex.log x)) := by
    rw [Cfun, hexp_x]; simp only [Polynomial.eval_add]
  rw [hC, ← exp_collapse hxne' w]; ring

/-- **The density-shadow row relation, extracted.** The top Laurent coefficient `C_2(0)` of the linear
block, peeled by `quadratic_filtration_top`, equals (using `q_{22}=0`, `q_{12}+q_{21}=0` and
`tailFactored_zero_eq`) the row relation `(q_{02}+q_{20})(−n)·ζ(s,−n) + l_2(−n) = 0`. -/
theorem row_extract {s : ℂ} (hs1 : 1 < s.re) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ)
    (l : Fin 3 → Polynomial ℂ) (hq22 : q 2 2 = 0) (hA3 : q 1 2 + q 2 1 = 0)
    (hPsi0 : ∀ z : ℂ, z.re < -Real.log 2 →
      PsiB s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    (q 0 2 + q 2 0).eval (-(n : ℂ)) * HurwitzZetaShift.hzeta s (-(n : ℂ))
      + (l 2).eval (-(n : ℂ)) = 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs1; exact absurd hs1 (by norm_num)
  have hC2 : Cfun s n q l (Fin.last 2) 0 = 0 :=
    quadratic_filtration_top (l := 𝓝[≠] (0:ℂ)) ((tendsto_id).mono_left nhdsWithin_le_nhds)
      (fun w => (Cfun_continuousAt hs1 n q l w).tendsto.mono_left nhdsWithin_le_nhds)
      (psi_to_qft n q l hPsi0)
  rw [show (Fin.last 2 : Fin 3) = 2 from by decide, Cfun] at hC2
  simp only [Fin.sum_univ_three, add_zero] at hC2
  have e22 : ((q 2 2 + q 2 2 : Polynomial ℂ)).eval (-(n:ℂ)) = 0 := by rw [hq22]; simp
  have e21 : ((q 2 1 + q 1 2 : Polynomial ℂ)).eval (-(n:ℂ)) = 0 := by
    rw [show q 2 1 + q 1 2 = q 1 2 + q 2 1 from add_comm _ _, hA3]; simp
  have e00 : tailFactored s ((0 : Fin 3) : ℕ) n 0 = HurwitzZetaShift.hzeta s (-(n:ℂ)) :=
    tailFactored_zero_eq s hs0 n
  rw [add_comm (q 0 2) (q 2 0)]
  linear_combination hC2 - (q 2 0 + q 0 2).eval (-(n:ℂ)) * e00
    - tailFactored s ((1 : Fin 3) : ℕ) n 0 * e21 - tailFactored s ((2 : Fin 3) : ℕ) n 0 * e22

/-- The weight-1 quadratic coefficient `A_1 = q_{01}+q_{10}`. -/
theorem Aq_one (q : Fin 3 → Fin 3 → Polynomial ℂ) : Aq q 1 = q 0 1 + q 1 0 := by
  have hset : (Finset.univ.filter (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = 1))
      = {(0, 1), (1, 0)} := by decide
  rw [Aq, hset, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The weight-3 quadratic coefficient `A_3 = q_{12}+q_{21}`. -/
theorem Aq_three (q : Fin 3 → Fin 3 → Polynomial ℂ) : Aq q 3 = q 1 2 + q 2 1 := by
  have hset : (Finset.univ.filter (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = 3))
      = {(1, 2), (2, 1)} := by decide
  rw [Aq, hset, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- **The linear block collapses to the pure linear block.** Once every symmetric quadratic combination
vanishes (`q_{00}=q_{11}=q_{22}=0`, `q_{01}+q_{10}=q_{12}+q_{21}=q_{02}+q_{20}=0`), the cross terms of
`Ψb` cancel and `Ψb = ∑_k l_k(−n+e^z)·e^{−(s+k)z}` — the form `lin_descent` consumes. -/
theorem psiB_pure {s : ℂ} (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ)
    (hq00 : q 0 0 = 0) (hq22 : q 2 2 = 0) (hq11 : q 1 1 = 0)
    (hA1 : q 0 1 + q 1 0 = 0) (hA3 : q 1 2 + q 2 1 = 0) (hQ : q 0 2 + q 2 0 = 0) (z : ℂ) :
    PsiB s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z
      = ∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) * Complex.exp (-(s + (k : ℂ)) * z) := by
  have z00 : q 0 0 + q 0 0 = 0 := by rw [hq00]; ring
  have z01 : q 0 1 + q 1 0 = 0 := hA1
  have z10 : q 1 0 + q 0 1 = 0 := by rw [add_comm]; exact hA1
  have z02 : q 0 2 + q 2 0 = 0 := hQ
  have z20 : q 2 0 + q 0 2 = 0 := by rw [add_comm]; exact hQ
  have z11 : q 1 1 + q 1 1 = 0 := by rw [hq11]; ring
  have z12 : q 1 2 + q 2 1 = 0 := hA3
  have z21 : q 2 1 + q 1 2 = 0 := by rw [add_comm]; exact hA3
  have z22 : q 2 2 + q 2 2 = 0 := by rw [hq22]; ring
  rw [PsiB, psi_regroup (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (fun k => (l k).eval (-(n : ℂ) + Complex.exp z))
      (fun j => tailFactored s (j : ℕ) n (Complex.exp z))
      (fun k => Complex.exp (-(s + (k : ℂ)) * z))]
  simp only [Fin.sum_univ_three, ← Polynomial.eval_add, z00, z01, z02, z10, z11, z12, z20, z21,
    z22, Polynomial.eval_zero, zero_mul, add_zero, zero_add]

end HurwitzN2Final
