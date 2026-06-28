/-
# Hurwitz all-N — top row extraction from the linear block

After the all-`N` quadratic block has been killed, the linear block `Ψ_N`
contains the row equations used by the rational-tail descent.  This file proves
the first uniform extraction: the top Laurent coefficient of `Ψ_N` is the top
row relation against the shifted Hurwitz values.
-/
import GaloisForLFunctions.Hurwitz.AllNHalfInteger
import GaloisForLFunctions.Hurwitz.AllNTailIndependence
import GaloisForLFunctions.Hurwitz.N2TailValue

open Complex Filter Topology HurwitzN2Tail HurwitzSpine HurwitzAllNQuadFilt

namespace HurwitzAllNRowExtraction

variable {N : ℕ}

/-- The factored tail at `x = 0` is the shifted Hurwitz value. -/
theorem tailFactored_zero_eq_shift (s : ℂ) (k n : ℕ) (hs : s + (k : ℂ) ≠ 0) :
    tailFactored s k n 0 = HurwitzZetaShift.hzeta (s + (k : ℂ)) (-(n : ℂ)) := by
  rw [tailFactored, HurwitzZetaShift.hzeta]
  refine tsum_congr (fun m => ?_)
  by_cases hm : m = n
  · subst hm
    rw [if_pos rfl, show ((m : ℂ) + -(m : ℂ)) = 0 from by ring,
      Complex.zero_cpow (neg_ne_zero.mpr hs)]
  · rw [if_neg hm]
    simp [show ((m : ℂ) + -(n : ℂ)) = (m : ℂ) - (n : ℂ) from by ring]

/-- Regroup the all-`N` linear+cross block by the singular exponential `E_k`. -/
theorem psiN_regroup (q : Fin (N + 1) → Fin (N + 1) → ℂ) (l : Fin (N + 1) → ℂ)
    (E R : Fin (N + 1) → ℂ) :
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j * (E i * R j + E j * R i))
      + ∑ k : Fin (N + 1), l k * E k
    = ∑ k : Fin (N + 1), ((∑ j : Fin (N + 1), (q k j + q j k) * R j) + l k) * E k := by
  calc
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j * (E i * R j + E j * R i))
        + ∑ k : Fin (N + 1), l k * E k
      = ((∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j * (E i * R j))
          + (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j * (E j * R i)))
        + ∑ k : Fin (N + 1), l k * E k := by
          congr 1
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = ((∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q i j * (E i * R j))
          + (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), q j i * (E i * R j)))
        + ∑ k : Fin (N + 1), l k * E k := by
          congr 2
          rw [Finset.sum_comm]
    _ = (∑ i : Fin (N + 1), (∑ j : Fin (N + 1), (q i j + q j i) * R j) * E i)
        + ∑ k : Fin (N + 1), l k * E k := by
          congr 1
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_add_distrib, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = ∑ k : Fin (N + 1), ((∑ j : Fin (N + 1), (q k j + q j k) * R j) + l k) * E k := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun k _ => by ring)

/-- The `E_w` coefficient of the all-`N` linear+cross block in local coordinate `x`. -/
noncomputable def CfunN (s : ℂ) (n : ℕ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (w : Fin (N + 1)) (x : ℂ) : ℂ :=
  (∑ j : Fin (N + 1), ((q w j + q j w).eval (-(n : ℂ) + x))
      * tailFactored s (j : ℕ) n x)
    + (l w).eval (-(n : ℂ) + x)

/-- `CfunN_w` is continuous at `x = 0`. -/
theorem CfunN_continuousAt {s : ℂ} (hs : 1 < s.re) (n : ℕ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (w : Fin (N + 1)) :
    ContinuousAt (CfunN (N := N) s n q l w) 0 := by
  unfold CfunN
  have htail : ∀ j : Fin (N + 1),
      ContinuousAt (fun x : ℂ => tailFactored s (j : ℕ) n x) 0 :=
    fun j => ((tailFactored_analytic hs (j : ℕ) n).continuousOn).continuousAt
      (IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) (by norm_num))
  have hpoly : ∀ p : Polynomial ℂ,
      ContinuousAt (fun x : ℂ => p.eval (-(n : ℂ) + x)) 0 :=
    fun p => ((Polynomial.continuous p).comp (by fun_prop)).continuousAt
  fun_prop (disch := first | exact htail _ | exact hpoly _)

/-- The exponential factors collapse to the integer power `x^(N-w)`. -/
theorem exp_collapseN {s x : ℂ} (hx : x ≠ 0) (w : Fin (N + 1)) :
    Complex.exp ((s + (N : ℂ)) * Complex.log x)
      * Complex.exp (-(s + (w : ℂ)) * Complex.log x)
      = x ^ (N - (w : ℕ)) := by
  have hw : (w : ℕ) ≤ N := Nat.lt_succ_iff.mp w.isLt
  have hcast : ((N - (w : ℕ) : ℕ) : ℂ) = (N : ℂ) - (w : ℂ) := by
    simpa using (Nat.cast_sub hw : ((N - (w : ℕ) : ℕ) : ℂ) = (N : ℂ) - ((w : ℕ) : ℂ))
  rw [← Complex.exp_add,
    show (s + (N : ℂ)) * Complex.log x + -(s + (w : ℂ)) * Complex.log x
        = ((N - (w : ℕ) : ℕ) : ℂ) * Complex.log x by rw [hcast]; ring,
    Complex.exp_nat_mul, Complex.exp_log hx]

/-- Vanishing of `Ψ_N` gives the Laurent-top extraction form in `x = exp z`. -/
theorem psiN_to_qft {s : ℂ} (n : ℕ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ)
    (hPsi0 : ∀ z : ℂ, z.re < -Real.log 2 →
      PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    ∀ᶠ x : ℂ in 𝓝[≠] (0 : ℂ),
      ∑ w : Fin (N + 1), CfunN (N := N) s n q l w x * x ^ (N - (w : ℕ)) = 0 := by
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)),
    self_mem_nhdsWithin] with x hxball hxne
  have hxne' : x ≠ 0 := hxne
  have hnorm : ‖x‖ < 1 / 2 := by
    have := Metric.mem_ball.mp hxball
    rwa [dist_zero_right] at this
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne'
  have hexp_x : Complex.exp (Complex.log x) = x := Complex.exp_log hxne'
  have hz_re : (Complex.log x).re < -Real.log 2 := by
    rw [Complex.log_re]
    have h12 : Real.log ‖x‖ < Real.log (1 / 2) := Real.log_lt_log hxpos hnorm
    rwa [one_div, Real.log_inv] at h12
  have hPsi := hPsi0 (Complex.log x) hz_re
  have hreg : PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) (Complex.log x)
      = ∑ k : Fin (N + 1), ((∑ j : Fin (N + 1),
          ((q k j).eval (-(n : ℂ) + Complex.exp (Complex.log x))
            + (q j k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
            * tailFactored s (j : ℕ) n (Complex.exp (Complex.log x)))
        + (l k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
        * Complex.exp (-(s + (k : ℂ)) * Complex.log x) := by
    rw [PsiN]
    exact psiN_regroup (N := N)
      (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
      (fun k => (l k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
      (fun k => Complex.exp (-(s + (k : ℂ)) * Complex.log x))
      (fun j => tailFactored s (j : ℕ) n (Complex.exp (Complex.log x)))
  rw [hreg] at hPsi
  rw [show (∑ w : Fin (N + 1), CfunN (N := N) s n q l w x * x ^ (N - (w : ℕ)))
        = Complex.exp ((s + (N : ℂ)) * Complex.log x) * (∑ k : Fin (N + 1),
          ((∑ j : Fin (N + 1),
            ((q k j).eval (-(n : ℂ) + Complex.exp (Complex.log x))
              + (q j k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
              * tailFactored s (j : ℕ) n (Complex.exp (Complex.log x)))
          + (l k).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
          * Complex.exp (-(s + (k : ℂ)) * Complex.log x)) from ?_, hPsi, mul_zero]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hC : CfunN (N := N) s n q l w x
      = (∑ j : Fin (N + 1), ((q w j).eval (-(n : ℂ) + Complex.exp (Complex.log x))
            + (q j w).eval (-(n : ℂ) + Complex.exp (Complex.log x)))
            * tailFactored s (j : ℕ) n (Complex.exp (Complex.log x)))
        + (l w).eval (-(n : ℂ) + Complex.exp (Complex.log x)) := by
    rw [CfunN, hexp_x]
    simp only [Polynomial.eval_add]
  rw [hC, ← exp_collapseN (N := N) hxne' w]
  ring

/-- The top `E_N` coefficient of `Ψ_N` vanishes at `x = 0`. -/
theorem CfunN_top_eq_zero {s : ℂ} (hs1 : 1 < s.re) (n : ℕ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ)
    (hPsi0 : ∀ z : ℂ, z.re < -Real.log 2 →
      PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    CfunN (N := N) s n q l (Fin.last N) 0 = 0 :=
  quadratic_filtration_top (l := 𝓝[≠] (0 : ℂ))
    ((tendsto_id).mono_left nhdsWithin_le_nhds)
    (fun w => (CfunN_continuousAt (N := N) hs1 n q l w).tendsto.mono_left nhdsWithin_le_nhds)
    (psiN_to_qft (N := N) n q l hPsi0)

/-- The top row equation extracted from the linear block. -/
theorem top_row_extract {s : ℂ} (hs1 : 1 < s.re) (n : ℕ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ)
    (hPsi0 : ∀ z : ℂ, z.re < -Real.log 2 →
      PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    (∑ j : Fin (N + 1), ((q (Fin.last N) j + q j (Fin.last N)).eval (-(n : ℂ)))
        * HurwitzZetaShift.hzeta (s + (j : ℂ)) (-(n : ℂ)))
      + (l (Fin.last N)).eval (-(n : ℂ)) = 0 := by
  have htop := CfunN_top_eq_zero (N := N) hs1 n q l hPsi0
  have hs0 : ∀ j : Fin (N + 1), s + (j : ℂ) ≠ 0 := by
    intro j h
    have hre : s.re + (j : ℕ) = 0 := by
      have h' := congrArg Complex.re h
      simpa [Complex.add_re] using h'
    have hj : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg j.val
    linarith
  simpa [CfunN, tailFactored_zero_eq_shift, hs0] using htop

/-- Symmetric-form top row equation, matching the rational-tail close interface. -/
theorem top_row_extract_symmetric {s : ℂ} (hs1 : 1 < s.re) (n : ℕ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (hSymm : ∀ i j, q i j = q j i)
    (hPsi0 : ∀ z : ℂ, z.re < -Real.log 2 →
      PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    (l (Fin.last N)).eval (-(n : ℂ)) +
      (∑ i : Fin (N + 1), (q i (Fin.last N)).eval (-(n : ℂ)) *
        (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0 := by
  have htop := top_row_extract (N := N) hs1 n q l hPsi0
  rw [add_comm] at htop
  have hsum :
      (∑ i : Fin (N + 1), ((q (Fin.last N) i + q i (Fin.last N)).eval (-(n : ℂ)))
          * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))
        =
      (∑ i : Fin (N + 1), (q i (Fin.last N)).eval (-(n : ℂ)) *
          (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hSymm (Fin.last N) i, Polynomial.eval_add]
    ring
  rwa [hsum] at htop

/-- The extracted top row closes from the exact pole-root tail input: under
symmetry, `Ψ_N = 0` for all large `n` forces the top quadratic column and top
linear coefficient to vanish. This is the recursive row-descent brick consumed
after the all-`N` quadratic block has supplied the linear-block vanishing. -/
theorem top_column_close_of_poleRootInput {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (hSymm : ∀ i j, q i j = q j i) {M : ℕ}
    (hPsi : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    (∀ i : Fin (N + 1), q i (Fin.last N) = 0) ∧ l (Fin.last N) = 0 := by
  exact HurwitzAllNTailIndependence.row_close_of_rationalTailIndependent
    (N := N)
    (V := fun i n => HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))
    (hTail :=
      HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_hzeta_shift_neg_nat_of_poleRootInput
        (N := N) (s := s) hs1 hsZ hpole)
    (eta := fun _ => (1 : ℂ)) (zeta := fun _ => (0 : ℂ))
    (heta := by
      intro i
      norm_num)
    (q := q) (l := l) (j := Fin.last N) (M := M)
    (by
      intro n hn
      simpa using top_row_extract_symmetric (N := N) hs1 n q l hSymm (hPsi n hn))

end HurwitzAllNRowExtraction

namespace HurwitzAllNRowExtraction

/-- The first complete row-descent instance after the top-column brick. For a
2-term ladder (`N = 1`), symmetry plus `Ψ_1 = 0` for all large `n` closes both
quadratic columns and both linear coefficients from the exact pole-root tail
input. This is the concrete base pattern for the general recursive descent. -/
theorem two_column_close_of_poleRootInput {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput 1 s)
    (q : Fin 2 → Fin 2 → Polynomial ℂ) (l : Fin 2 → Polynomial ℂ)
    (hSymm : ∀ i j, q i j = q j i) {M : ℕ}
    (hPsi : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    (∀ i j : Fin 2, q i j = 0) ∧ (∀ j : Fin 2, l j = 0) := by
  obtain ⟨hcol1, hl1⟩ := top_column_close_of_poleRootInput
    (N := 1) (s := s) (M := M) hs1 hsZ hpole q l hSymm hPsi
  have hq01 : q 0 1 = 0 := hcol1 0
  have hq11 : q 1 1 = 0 := hcol1 1
  have hl1' : l 1 = 0 := by
    simpa using hl1
  have hq10 : q 1 0 = 0 := by
    rw [hSymm 1 0]
    exact hq01
  have hC1 : ∀ n x, CfunN (N := 1) s n q l 1 x = 0 := by
    intro n x
    simp [CfunN, Fin.sum_univ_two, hq01, hq10, hq11, hl1']
  have hrow0 : ∀ n, M ≤ n →
      (l 0).eval (-(n : ℂ)) +
        (∑ i : Fin 2, (q i 0).eval (-(n : ℂ)) *
          (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0 := by
    intro n hn
    have hC0zero : CfunN (N := 1) s n q l 0 0 = 0 := by
      have hev := psiN_to_qft (N := 1) n q l (hPsi n hn)
      have hC0_event : ∀ᶠ x : ℂ in 𝓝[≠] (0 : ℂ), CfunN (N := 1) s n q l 0 x = 0 := by
        filter_upwards [hev, self_mem_nhdsWithin] with x hx hxne
        rw [Fin.sum_univ_two] at hx
        simp [hC1 n x] at hx
        exact hx.resolve_right hxne
      have hlimC : Tendsto (CfunN (N := 1) s n q l 0) (𝓝[≠] (0 : ℂ))
          (𝓝 (CfunN (N := 1) s n q l 0 0)) :=
        (CfunN_continuousAt (N := 1) hs1 n q l 0).tendsto.mono_left nhdsWithin_le_nhds
      have hC0_eventEq : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝[≠] (0 : ℂ)]
          CfunN (N := 1) s n q l 0 :=
        hC0_event.mono (fun _ hx => hx.symm)
      have hlim0 : Tendsto (CfunN (N := 1) s n q l 0) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
        Filter.Tendsto.congr' hC0_eventEq tendsto_const_nhds
      exact tendsto_nhds_unique hlimC hlim0
    have hs0 : ∀ j : Fin 2, s + (j : ℂ) ≠ 0 := by
      intro j h
      have hre : s.re + (j : ℕ) = 0 := by
        have h' := congrArg Complex.re h
        simpa [Complex.add_re] using h'
      have hj : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg j.val
      linarith
    have hrow_unsym :
        (∑ j : Fin 2, ((q 0 j + q j 0).eval (-(n : ℂ)))
            * HurwitzZetaShift.hzeta (s + (j : ℂ)) (-(n : ℂ)))
          + (l 0).eval (-(n : ℂ)) = 0 := by
      simpa [CfunN, tailFactored_zero_eq_shift, hs0] using hC0zero
    rw [add_comm] at hrow_unsym
    have hsum :
        (∑ i : Fin 2, ((q 0 i + q i 0).eval (-(n : ℂ)))
            * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ))) =
        (∑ i : Fin 2, (q i 0).eval (-(n : ℂ)) *
          (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hSymm 0 i, Polynomial.eval_add]
      ring
    rwa [hsum] at hrow_unsym
  have hclose0 := HurwitzAllNTailIndependence.row_close_of_rationalTailIndependent
    (N := 1)
    (V := fun i n => HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))
    (hTail :=
      HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_hzeta_shift_neg_nat_of_poleRootInput
        (N := 1) (s := s) hs1 hsZ hpole)
    (eta := fun _ => (1 : ℂ)) (zeta := fun _ => (0 : ℂ))
    (heta := by
      intro i
      norm_num)
    (q := q) (l := l) (j := 0) (M := M)
    (by
      intro n hn
      simpa [zero_add, one_mul] using hrow0 n hn)
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases j
    · exact hclose0.1 i
    · exact hcol1 i
  · intro j
    fin_cases j
    · exact hclose0.2
    · exact hl1

end HurwitzAllNRowExtraction

namespace HurwitzAllNRowExtraction

/-- Peel an arbitrary coefficient from a filtered finite sum once all higher
coefficients are identically zero. This is the local Laurent step needed for the
downward `Ψ_N` row descent. -/
theorem filtered_coefficient_zero_of_higher_zero {N j : ℕ} (hj : j ≤ N)
    {A : ℕ → ℂ → ℂ} {l : Filter ℂ} [l.NeBot]
    (hid : Tendsto (fun x : ℂ => x) l (nhds 0)) (hne : ∀ᶠ x in l, x ≠ 0)
    (hA : ∀ k, k ≤ j → Tendsto (A k) l (nhds (A k 0)))
    (hhigher : ∀ k, j < k → k ≤ N → ∀ x, A k x = 0)
    (hrel : ∀ᶠ x in l, ∑ k ∈ Finset.range (N + 1), A k x * x ^ (N - k) = 0) :
    A j 0 = 0 := by
  have hrel_j : ∀ᶠ x in l, ∑ k ∈ Finset.range (j + 1), A k x * x ^ (j - k) = 0 := by
    filter_upwards [hrel, hne] with x hx hx0
    have hsubset : Finset.range (j + 1) ⊆ Finset.range (N + 1) := by
      intro k hk
      have hk_le_j : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (le_trans hk_le_j hj))
    have hdrop :
        (∑ k ∈ Finset.range (N + 1), A k x * x ^ (N - k)) =
          ∑ k ∈ Finset.range (j + 1), A k x * x ^ (N - k) := by
      rw [eq_comm]
      refine Finset.sum_subset hsubset ?_
      intro k hkN hknot
      have hkNle : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkN)
      have hjk : j < k := by
        have hnotlt : ¬ k < j + 1 := by simpa [Finset.mem_range] using hknot
        exact Nat.lt_of_not_ge (by simpa [Nat.lt_succ_iff] using hnotlt)
      simp [hhigher k hjk hkNle x]
    have hfactor :
        (∑ k ∈ Finset.range (j + 1), A k x * x ^ (N - k)) =
          x ^ (N - j) * (∑ k ∈ Finset.range (j + 1), A k x * x ^ (j - k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkj : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpow : x ^ (N - k) = x ^ (N - j) * x ^ (j - k) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      ring
    rw [hdrop, hfactor] at hx
    have hpow_ne : x ^ (N - j) ≠ 0 := pow_ne_zero _ hx0
    exact (mul_eq_zero.mp hx).resolve_left hpow_ne
  have hfin : ∀ᶠ x in l,
      ∑ k : Fin (j + 1), (fun x => A (k : ℕ) x) x * x ^ (j - (k : ℕ)) = 0 := by
    filter_upwards [hrel_j] with x hx
    rw [Fin.sum_univ_eq_sum_range (fun k => A k x * x ^ (j - k)) (j + 1)]
    simpa using hx
  have htend : ∀ k : Fin (j + 1),
      Tendsto (fun x => A (k : ℕ) x) l (nhds ((fun x => A (k : ℕ) x) 0)) := by
    intro k
    exact hA (k : ℕ) (Nat.le_of_lt_succ k.isLt)
  have htop := quadratic_filtration_top (W := j)
    (A := fun k => fun x => A (k : ℕ) x) hid htend hfin
  change A ((Fin.last j : Fin (j + 1)) : ℕ) 0 = 0 at htop
  rwa [Fin.val_last] at htop

/-- If all columns above `j` have already closed, then the filtered `Ψ_N`
identity extracts the `j`-th row equation and the rational-tail close kills the
`j`-th column. This is the reusable downward row-descent step. -/
theorem column_close_of_higher_columns_closed {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (hSymm : ∀ i j, q i j = q j i)
    {M : ℕ}
    (hPsi : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0)
    (j : Fin (N + 1))
    (hhigher : ∀ k : Fin (N + 1), (j : ℕ) < (k : ℕ) →
      (∀ i : Fin (N + 1), q i k = 0) ∧ l k = 0) :
    (∀ i : Fin (N + 1), q i j = 0) ∧ l j = 0 := by
  have hC_higher : ∀ k : Fin (N + 1), (j : ℕ) < (k : ℕ) → ∀ n x,
      CfunN (N := N) s n q l k x = 0 := by
    intro k hjk n x
    have hk := hhigher k hjk
    have hlk : l k = 0 := hk.2
    have hq_col : ∀ i : Fin (N + 1), q i k = 0 := hk.1
    have hq_row : ∀ i : Fin (N + 1), q k i = 0 := by
      intro i
      rw [hSymm k i]
      exact hq_col i
    simp [CfunN, hq_col, hq_row, hlk]
  have hrow : ∀ n, M ≤ n →
      (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (N + 1), (q i j).eval (-(n : ℂ)) *
          (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0 := by
    intro n hn
    let A : ℕ → ℂ → ℂ := fun k x => if hk : k < N + 1 then CfunN (N := N) s n q l ⟨k, hk⟩ x else 0
    have hCj0 : CfunN (N := N) s n q l j 0 = 0 := by
      have hrelRange : ∀ᶠ x in 𝓝[≠] (0 : ℂ),
          ∑ k ∈ Finset.range (N + 1), A k x * x ^ (N - k) = 0 := by
        have hev := psiN_to_qft (N := N) n q l (hPsi n hn)
        filter_upwards [hev] with x hx
        rw [← Fin.sum_univ_eq_sum_range
          (fun k => A k x * x ^ (N - k)) (N + 1)]
        simpa [A, Nat.lt_succ_iff, Fin.is_le] using hx
      have hAcont : ∀ k, k ≤ (j : ℕ) → Tendsto (A k) (𝓝[≠] (0 : ℂ)) (nhds (A k 0)) := by
        intro k hkj
        have hkN : k < N + 1 := Nat.lt_succ_iff.mpr (le_trans hkj (Nat.lt_succ_iff.mp j.isLt))
        simp only [A, dif_pos hkN]
        exact (CfunN_continuousAt (N := N) hs1 n q l ⟨k, hkN⟩).tendsto.mono_left
          nhdsWithin_le_nhds
      have hhigherA : ∀ k, (j : ℕ) < k → k ≤ N → ∀ x, A k x = 0 := by
        intro k hjk hkN x
        have hklt : k < N + 1 := Nat.lt_succ_iff.mpr hkN
        simp only [A, dif_pos hklt]
        exact hC_higher ⟨k, hklt⟩ hjk n x
      have hcoef := filtered_coefficient_zero_of_higher_zero
        (N := N) (j := (j : ℕ)) (Nat.lt_succ_iff.mp j.isLt)
        (A := A) (l := 𝓝[≠] (0 : ℂ))
        ((continuous_id.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with x hx using hx)
        hAcont hhigherA hrelRange
      simpa [A, j.isLt, Nat.lt_succ_iff, Fin.is_le] using hcoef
    have hs0 : ∀ i : Fin (N + 1), s + (i : ℂ) ≠ 0 := by
      intro i h
      have hre : s.re + (i : ℕ) = 0 := by
        have h' := congrArg Complex.re h
        simpa [Complex.add_re] using h'
      have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg i.val
      linarith
    have hrow_unsym :
        (∑ i : Fin (N + 1), ((q j i + q i j).eval (-(n : ℂ)))
            * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))
          + (l j).eval (-(n : ℂ)) = 0 := by
      simpa [CfunN, tailFactored_zero_eq_shift, hs0] using hCj0
    rw [add_comm] at hrow_unsym
    have hsum :
        (∑ i : Fin (N + 1), ((q j i + q i j).eval (-(n : ℂ)))
            * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ))) =
        (∑ i : Fin (N + 1), (q i j).eval (-(n : ℂ)) *
          (2 * HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hSymm j i, Polynomial.eval_add]
      ring
    rwa [hsum] at hrow_unsym
  exact HurwitzAllNTailIndependence.row_close_of_rationalTailIndependent
    (N := N)
    (V := fun i n => HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ)))
    (hTail :=
      HurwitzAllNTailIndependence.HurwitzZetaTail.rationalTailIndependent_hzeta_shift_neg_nat_of_poleRootInput
        (N := N) (s := s) hs1 hsZ hpole)
    (eta := fun _ => (1 : ℂ)) (zeta := fun _ => (0 : ℂ))
    (heta := by
      intro i
      norm_num)
    (q := q) (l := l) (j := j) (M := M)
    (by
      intro n hn
      simpa [zero_add, one_mul] using hrow n hn)

end HurwitzAllNRowExtraction

namespace HurwitzAllNRowExtraction

/-- Full finite descent for the linear+cross block.  From the exact pole-root
input and the vanishing of `Ψ_N` for all large `n`, symmetry closes every
quadratic column and every linear coefficient. -/
theorem all_columns_close_of_poleRootInput {N : ℕ} {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (hSymm : ∀ i j, q i j = q j i)
    {M : ℕ}
    (hPsi : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) :
    (∀ i j : Fin (N + 1), q i j = 0) ∧ (∀ j : Fin (N + 1), l j = 0) := by
  let ClosedFrom : ℕ → Prop := fun r =>
    ∀ k : Fin (N + 1), r ≤ (k : ℕ) → (∀ i : Fin (N + 1), q i k = 0) ∧ l k = 0
  have htopClose : (∀ i : Fin (N + 1), q i (Fin.last N) = 0) ∧ l (Fin.last N) = 0 := by
    exact column_close_of_higher_columns_closed
      (N := N) (s := s) (M := M) hs1 hsZ hpole q l hSymm hPsi (Fin.last N)
      (by
        intro k hk
        have hk_le : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
        have hlast : ((Fin.last N : Fin (N + 1)) : ℕ) = N := Fin.val_last N
        have : False := by omega
        exact False.elim this)
  have htop : ClosedFrom N := by
    dsimp [ClosedFrom]
    intro k hk
    have hk_le : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
    have hkval : (k : ℕ) = N := le_antisymm hk_le hk
    have hk_eq : k = Fin.last N := Fin.ext hkval
    simpa [hk_eq] using htopClose
  have hclosed0 : ClosedFrom 0 := by
    exact Nat.decreasingInduction' (m := 0) (n := N) (P := ClosedFrom)
      (by
        intro r hrN _ hsucc
        dsimp [ClosedFrom] at hsucc ⊢
        intro k hkr
        by_cases hnext : r + 1 ≤ (k : ℕ)
        · exact hsucc k hnext
        · have hkval : (k : ℕ) = r := by omega
          have hrleN : r ≤ N := le_of_lt hrN
          let j : Fin (N + 1) := ⟨r, Nat.lt_succ_iff.mpr hrleN⟩
          have hclosej : (∀ i : Fin (N + 1), q i j = 0) ∧ l j = 0 := by
            exact column_close_of_higher_columns_closed
              (N := N) (s := s) (M := M) hs1 hsZ hpole q l hSymm hPsi j
              (by
                intro kk hjkk
                exact hsucc kk (Nat.succ_le_of_lt (by simpa [j] using hjkk)))
          have hk_eq : k = j := Fin.ext hkval
          simpa [hk_eq] using hclosej)
      (Nat.zero_le N) htop
  refine ⟨?_, ?_⟩
  · intro i j
    exact (hclosed0 j (Nat.zero_le _)).1 i
  · intro j
    exact (hclosed0 j (Nat.zero_le _)).2

end HurwitzAllNRowExtraction
