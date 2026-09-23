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
  HurwitzN2Descent HurwitzN2PsiRegroup HurwitzEncoding

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

/-- **The regular block collapses to the constant.** Once every symmetric quadratic combination and
every linear coefficient vanishes, `Θb = c(−n+e^z)`. -/
theorem thetaB_const {s : ℂ} (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ)
    (cc : Polynomial ℂ) (hq00 : q 0 0 = 0) (hq22 : q 2 2 = 0) (hq11 : q 1 1 = 0)
    (hA1 : q 0 1 + q 1 0 = 0) (hA3 : q 1 2 + q 2 1 = 0) (hQ : q 0 2 + q 2 0 = 0)
    (hl0 : l 0 = 0) (hl1 : l 1 = 0) (hl2 : l 2 = 0) (z : ℂ) :
    ThetaB s n q l cc (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z
      = cc.eval (-(n : ℂ) + Complex.exp z) := by
  have e00 : (q 0 0).eval (-(n:ℂ) + Complex.exp z) = 0 := by rw [hq00]; simp
  have e11 : (q 1 1).eval (-(n:ℂ) + Complex.exp z) = 0 := by rw [hq11]; simp
  have e22 : (q 2 2).eval (-(n:ℂ) + Complex.exp z) = 0 := by rw [hq22]; simp
  have e01 : (q 0 1).eval (-(n:ℂ) + Complex.exp z) + (q 1 0).eval (-(n:ℂ) + Complex.exp z) = 0 := by
    rw [← Polynomial.eval_add, hA1]; simp
  have e12 : (q 1 2).eval (-(n:ℂ) + Complex.exp z) + (q 2 1).eval (-(n:ℂ) + Complex.exp z) = 0 := by
    rw [← Polynomial.eval_add, hA3]; simp
  have e02 : (q 0 2).eval (-(n:ℂ) + Complex.exp z) + (q 2 0).eval (-(n:ℂ) + Complex.exp z) = 0 := by
    rw [← Polynomial.eval_add, hQ]; simp
  have f0 : (l 0).eval (-(n:ℂ) + Complex.exp z) = 0 := by rw [hl0]; simp
  have f1 : (l 1).eval (-(n:ℂ) + Complex.exp z) = 0 := by rw [hl1]; simp
  have f2 : (l 2).eval (-(n:ℂ) + Complex.exp z) = 0 := by rw [hl2]; simp
  rw [ThetaB]
  simp only [Fin.sum_univ_three]
  linear_combination
    (tailFactored s ((0:Fin 3):ℕ) n (Complex.exp z))^(2 : ℕ) * e00
    + (tailFactored s ((0:Fin 3):ℕ) n (Complex.exp z)) * (tailFactored s ((1:Fin 3):ℕ) n (Complex.exp z)) * e01
    + (tailFactored s ((0:Fin 3):ℕ) n (Complex.exp z)) * (tailFactored s ((2:Fin 3):ℕ) n (Complex.exp z)) * e02
    + (tailFactored s ((1:Fin 3):ℕ) n (Complex.exp z))^(2 : ℕ) * e11
    + (tailFactored s ((1:Fin 3):ℕ) n (Complex.exp z)) * (tailFactored s ((2:Fin 3):ℕ) n (Complex.exp z)) * e12
    + (tailFactored s ((2:Fin 3):ℕ) n (Complex.exp z))^(2 : ℕ) * e22
    + (tailFactored s ((0:Fin 3):ℕ) n (Complex.exp z)) * f0
    + (tailFactored s ((1:Fin 3):ℕ) n (Complex.exp z)) * f1
    + (tailFactored s ((2:Fin 3):ℕ) n (Complex.exp z)) * f2

/-- **Hurwitz N=2 — no quadratic relation among `ζ(s,a), ζ(s+1,a), ζ(s+2,a)`, unconditional.** With
`1 < s.re`, `s ∉ ℤ`, `2s ∉ ℤ`, if the genuine factored relation holds near every large `a = −n`, then
the symmetric quadratic form, the linear coefficients, and the constant all vanish. This discharges the
`hrow/h0/h1/hc` hypotheses of `HurwitzN2Theorem.hurwitz_n2` from the relation alone. -/
theorem hurwitz_n2_unconditional {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s) (h2sZ : ∀ k : ℤ, (k : ℂ) ≠ 2 * s)
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) {N : ℕ}
    (hrel : ∀ n, N ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z) *
          ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) *
            (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0 := by
  have hlog : -1 < -Real.log 2 := by have := Real.log_two_lt_d9; linarith
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hblocks : ∀ n, N ≤ n →
      (∀ z : ℂ, z.re < -Real.log 2 → PhiB s n q z = 0)
      ∧ (∀ z : ℂ, z.re < -Real.log 2 →
          PsiB s n q l (fun k z => tailFactored s (k:ℕ) n (Complex.exp z)) z = 0)
      ∧ (∀ z : ℂ, z.re < -Real.log 2 →
          ThetaB s n q l cc (fun k z => tailFactored s (k:ℕ) n (Complex.exp z)) z = 0) := by
    intro n hn
    set R : Fin 3 → ℂ → ℂ := fun k z => tailFactored s (k:ℕ) n (Complex.exp z) with hRdef
    have hRper : ∀ k z, R k (z + 2*(Real.pi:ℂ)*Complex.I) = R k z :=
      fun k z => tailFactored_periodic s (k:ℕ) n z
    have hsplit : ∀ z:ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
        PhiB s n q z + PsiB s n q l R z + ThetaB s n q l cc R z = 0 := by
      intro z hz hz1 hz2
      rw [PhiB_eq_products, PsiB, ThetaB]
      have hcoll := relation_collect (s:=s) (fun i j => (q i j).eval (-(n:ℂ)+Complex.exp z))
        (fun k => (l k).eval (-(n:ℂ)+Complex.exp z)) (cc.eval (-(n:ℂ)+Complex.exp z)) z (fun k => R k z)
      have hr := hrel n hn z hz hz1 hz2
      linear_combination hr - hcoll
    exact n2_blocks_vanish s n hsZ h2sZ q l cc R hRper (z0:=-1) (B:=-Real.log 2)
      (by simpa using hlog) (by simpa using hpi) (by simpa using hpi)
      (blockSum_analytic hs1 n q l cc) hsplit
  obtain ⟨hq00, hq22, hsurv⟩ := n2_quad_coeffs s q (fun n hn z hz => (hblocks n hn).1 z hz)
  have hAqfun : ∀ w, w ≤ 4 → Aq q w = 0 :=
    HurwitzN2Descent.quad_descent q (fun n hn z hz => (hblocks n hn).1 z hz)
  have hA1 : q 0 1 + q 1 0 = 0 := by rw [← Aq_one]; exact hAqfun 1 (by norm_num)
  have hA3 : q 1 2 + q 2 1 = 0 := by rw [← Aq_three]; exact hAqfun 3 (by norm_num)
  have hrow : ∀ᶠ n : ℕ in Filter.atTop,
      (q 0 2 + q 2 0).eval (-(n:ℂ)) * HurwitzZetaShift.hzeta s (-(n:ℂ)) + (l 2).eval (-(n:ℂ)) = 0 := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact row_extract hs1 n q l hq22 hA3 (hblocks n hn).2.1
  obtain ⟨hQ, hl2⟩ := HurwitzN2DensityShadow.survivor_killed hs1 (fun k => (hsZ k).symm) hrow
  have hq11 : q 1 1 = 0 := by linear_combination hsurv - hQ
  have hlin : ∀ k, k ≤ 2 →
      (fun m : ℕ => if m = 0 then l 0 else if m = 1 then l 1 else l 2) k = 0 := by
    apply HurwitzN2Descent.lin_descent (s:=s)
      (fun m : ℕ => if m = 0 then l 0 else if m = 1 then l 1 else l 2) (N:=N)
      (Bregion := fun _ => -Real.log 2)
    intro n hn z hz
    have hPsi0 := (hblocks n hn).2.1 z hz
    rw [psiB_pure n q l hq00 hq22 hq11 hA1 hA3 hQ z] at hPsi0
    rw [← hPsi0, ← Fin.sum_univ_eq_sum_range
      (fun m : ℕ => (if m = 0 then l 0 else if m = 1 then l 1 else l 2).eval (-(n:ℂ)+Complex.exp z)
        * Complex.exp (-(s+(m:ℂ))*z)) 3]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hidx : (if (i : ℕ) = 0 then l 0 else if (i : ℕ) = 1 then l 1 else l 2) = l i := by
      fin_cases i <;> rfl
    rw [hidx]
  have hl0 : l 0 = 0 := by have := hlin 0 (by norm_num); simpa using this
  have hl1 : l 1 = 0 := by have := hlin 1 (by norm_num); simpa using this
  have hcc : cc = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem
      (f := fun m : ℕ => -((N:ℂ)) + (1:ℂ) / ((m + 3 : ℕ) : ℂ))
    · intro a b hab
      simp only [add_right_inj] at hab
      rw [one_div, one_div, inv_inj] at hab
      have := Nat.cast_injective (R := ℂ) hab
      omega
    · intro m
      have hx : ((m + 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hxr : ((m + 3 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hez : Complex.exp (Complex.log ((1:ℂ) / ((m + 3 : ℕ) : ℂ)))
          = (1:ℂ) / ((m + 3 : ℕ) : ℂ) := Complex.exp_log (div_ne_zero one_ne_zero hx)
      have hzre : (Complex.log ((1:ℂ) / ((m + 3 : ℕ) : ℂ))).re < -Real.log 2 := by
        rw [Complex.log_re, norm_div, norm_one, Complex.norm_natCast]
        rw [Real.log_div one_ne_zero hxr, Real.log_one, zero_sub]
        have h2 : Real.log 2 < Real.log ((m + 3 : ℕ) : ℝ) :=
          Real.log_lt_log (by norm_num) (by exact_mod_cast (show 2 < m + 3 by omega))
        linarith
      have hθ := (hblocks N le_rfl).2.2 _ hzre
      rw [thetaB_const N q l cc hq00 hq22 hq11 hA1 hA3 hQ hl0 hl1 hl2, hez] at hθ
      simpa [Set.mem_setOf_eq, Polynomial.IsRoot] using hθ
  exact ⟨hq00, hq22, hq11, hQ, hl2, hl0, hl1, hcc⟩

end HurwitzN2Final
