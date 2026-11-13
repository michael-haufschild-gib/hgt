import GaloisForLFunctions.LogarithmicChowla.TwistVarVanishes

/-!
# (A5) `V(b/s, T) → 0`

For `s ≥ 1` (`tendsto_twistVar_zero`): with `g = (r, s)`, `q = s/g`, `C_r = #{χ mod q}`,
`D_r = τ(q)`, (A3) and (A4) give the pointwise bound (`twist_pointwise_le`)

`|T^{-1}Σ_{u<T} λ(n+u)e(ub/s)|² ≤ s Σ_{r<s} C_r (Σ_{χ ≠ 1} |T^{-1}dilWin_g(λχ)|² + D_r Σ_{e|q} |T^{-1}dilWin_{ge}(λ)|²)`,

the limit functional is linear on these bounded sequences (`limAvg_upper_eq`), and every term tends
to zero by (A2) (`tendsto_limAvg_dilWin`).
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Filter Topology GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {U : Ultrafilter ℝ}

/-- Equality of characters is decided classically. -/
noncomputable local instance (q : ℕ) : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

/-- The windows of the non-principal characters of a class. -/
def nonprincipalPart (s r T n : ℕ) : ℝ :=
  ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (s / Nat.gcd r s))).erase 1,
    ‖dilWin (twLiouville χ) (Nat.gcd r s) n T‖ ^ 2 / (T : ℝ) ^ 2

/-- The dilated windows of `λ` of a class. -/
def liouvillePart (s r T n : ℕ) : ℝ :=
  ∑ e ∈ (s / Nat.gcd r s).divisors,
    ‖dilWin (fun m => (ArithmeticFunction.liouville m : ℂ)) (Nat.gcd r s * e) n T‖ ^ 2
      / (T : ℝ) ^ 2

/-- The bound of a class. -/
def classPart (s r T n : ℕ) : ℝ :=
  (Fintype.card (DirichletCharacter ℂ (s / Nat.gcd r s)) : ℝ)
    * (nonprincipalPart s r T n + ((s / Nat.gcd r s).divisors.card : ℝ) * liouvillePart s r T n)

theorem gcd_pos_of {r s : ℕ} (hs : 1 ≤ s) : 1 ≤ Nat.gcd r s := Nat.gcd_pos_of_pos_right r (by omega)

theorem cls_q_pos {r s : ℕ} (hs : 1 ≤ s) : 0 < s / Nat.gcd r s :=
  Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right r s)) (gcd_pos_of hs)

/-- **The pointwise bound of the twisted window.** -/
theorem twist_pointwise_le {s : ℕ} (hs : 1 ≤ s) (b n T : ℕ) (hT : 0 < (T : ℝ)) :
    Complex.normSq (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * ((b : ℝ) / s))) / (T : ℝ) ^ 2
      ≤ s * ∑ r ∈ range s, classPart s r T n := by
  have h1 := normSq_twist_le hs b n T
  have hcls : ∀ r ∈ range s,
      ‖∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ)‖ ^ 2
        ≤ (T : ℝ) ^ 2 * classPart s r T n := by
    intro r hr
    have hr' : r < s := mem_range.mp hr
    haveI : NeZero (s / Nat.gcd r s) := ⟨(cls_q_pos (r := r) hs).ne'⟩
    have hc := normSq_classSum_le hs hr' n T
    rw [← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ (s / Nat.gcd r s)))] at hc
    have hp := normSq_dilWin_principal_le (cls_q_pos (r := r) hs) (gcd_pos_of (r := r) hs) n T
    have hT2 : (0 : ℝ) < (T : ℝ) ^ 2 := by positivity
    have hnp : (T : ℝ) ^ 2 * nonprincipalPart s r T n
        = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (s / Nat.gcd r s))).erase 1,
            ‖dilWin (twLiouville χ) (Nat.gcd r s) n T‖ ^ 2 := by
      rw [nonprincipalPart, Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by field_simp
    have hlp : (T : ℝ) ^ 2 * liouvillePart s r T n
        = ∑ e ∈ (s / Nat.gcd r s).divisors,
            ‖dilWin (fun m => (ArithmeticFunction.liouville m : ℂ)) (Nat.gcd r s * e) n T‖ ^ 2 := by
      rw [liouvillePart, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by field_simp
    have hC0 : (0 : ℝ) ≤ (Fintype.card (DirichletCharacter ℂ (s / Nat.gcd r s)) : ℝ) :=
      Nat.cast_nonneg _
    have e : (T : ℝ) ^ 2 * classPart s r T n
        = (Fintype.card (DirichletCharacter ℂ (s / Nat.gcd r s)) : ℝ)
          * ((T : ℝ) ^ 2 * nonprincipalPart s r T n
            + ((s / Nat.gcd r s).divisors.card : ℝ) * ((T : ℝ) ^ 2 * liouvillePart s r T n)) := by
      rw [classPart]; ring
    rw [e, hnp, hlp]
    refine le_trans hc (mul_le_mul_of_nonneg_left ?_ hC0)
    linarith
  have h2 : (s : ℝ) * ∑ r ∈ range s,
      ‖∑ u ∈ (range T).filter (fun u => (n + u) % s = r), ((lam (n + u) : ℝ) : ℂ)‖ ^ 2
      ≤ (s : ℝ) * ∑ r ∈ range s, (T : ℝ) ^ 2 * classPart s r T n :=
    mul_le_mul_of_nonneg_left (sum_le_sum hcls) (Nat.cast_nonneg s)
  rw [div_le_iff₀ (by positivity)]
  have e2 : (s : ℝ) * ∑ r ∈ range s, (T : ℝ) ^ 2 * classPart s r T n
      = (s : ℝ) * (∑ r ∈ range s, classPart s r T n) * (T : ℝ) ^ 2 := by
    rw [← mul_sum]; ring
  linarith

theorem bdd_nonprincipalPart {s r : ℕ} (hs : 1 ≤ s) (T : ℕ) :
    Bdd fun n => nonprincipalPart s r T n :=
  bdd_sum _ fun χ _ => bdd_dilWin_sq (norm_twLiouville_le χ) (gcd_pos_of hs) T

theorem bdd_liouvillePart {s r : ℕ} (hs : 1 ≤ s) (T : ℕ) :
    Bdd fun n => liouvillePart s r T n :=
  bdd_sum _ fun e he => bdd_dilWin_sq norm_liouville_le
    (Nat.mul_pos (gcd_pos_of hs) (Nat.pos_of_mem_divisors he)) T

theorem bdd_classPart {s r : ℕ} (hs : 1 ≤ s) (T : ℕ) : Bdd fun n => classPart s r T n :=
  ((bdd_nonprincipalPart hs T).add ((bdd_liouvillePart hs T).const_mul _)).const_mul _

/-- The limit of the class bound, term by term. -/
theorem limAvg_classPart (hU : (U : Filter ℝ) ≤ atTop) {s r : ℕ} (hs : 1 ≤ s) (T : ℕ) :
    limAvg U (fun n => classPart s r T n)
      = (Fintype.card (DirichletCharacter ℂ (s / Nat.gcd r s)) : ℝ)
        * (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (s / Nat.gcd r s))).erase 1,
            limAvg U (fun n => ‖dilWin (twLiouville χ) (Nat.gcd r s) n T‖ ^ 2 / (T : ℝ) ^ 2)
          + ((s / Nat.gcd r s).divisors.card : ℝ)
            * ∑ e ∈ (s / Nat.gcd r s).divisors,
                limAvg U (fun n => ‖dilWin (fun m => (ArithmeticFunction.liouville m : ℂ))
                  (Nat.gcd r s * e) n T‖ ^ 2 / (T : ℝ) ^ 2)) := by
  have hA := bdd_nonprincipalPart (r := r) hs T
  have hB := bdd_liouvillePart (r := r) hs T
  have hA' : limAvg U (fun n => nonprincipalPart s r T n)
      = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (s / Nat.gcd r s))).erase 1,
          limAvg U (fun n => ‖dilWin (twLiouville χ) (Nat.gcd r s) n T‖ ^ 2 / (T : ℝ) ^ 2) := by
    unfold nonprincipalPart
    exact limAvg_sum hU _ fun χ _ => bdd_dilWin_sq (norm_twLiouville_le χ) (gcd_pos_of hs) T
  have hB' : limAvg U (fun n => liouvillePart s r T n)
      = ∑ e ∈ (s / Nat.gcd r s).divisors,
          limAvg U (fun n => ‖dilWin (fun m => (ArithmeticFunction.liouville m : ℂ))
            (Nat.gcd r s * e) n T‖ ^ 2 / (T : ℝ) ^ 2) := by
    unfold liouvillePart
    exact limAvg_sum hU _ fun e he => bdd_dilWin_sq norm_liouville_le
      (Nat.mul_pos (gcd_pos_of hs) (Nat.pos_of_mem_divisors he)) T
  unfold classPart
  rw [limAvg_const_mul hU (hA.add (hB.const_mul _)), limAvg_add hU hA (hB.const_mul _),
    limAvg_const_mul hU hB, hA', hB']

/-- Each class bound tends to zero. -/
theorem tendsto_limAvg_classPart (hU : (U : Filter ℝ) ≤ atTop) {s r : ℕ} (hs : 1 ≤ s) :
    Tendsto (fun T : ℕ => limAvg U (fun n => classPart s r T n)) atTop (𝓝 0) := by
  haveI : NeZero (s / Nat.gcd r s) := ⟨(cls_q_pos (r := r) hs).ne'⟩
  simp_rw [limAvg_classPart hU hs]
  have hA : Tendsto (fun T : ℕ =>
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (s / Nat.gcd r s))).erase 1,
        limAvg U (fun n => ‖dilWin (twLiouville χ) (Nat.gcd r s) n T‖ ^ 2 / (T : ℝ) ^ 2))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum
      (f := fun (χ : DirichletCharacter ℂ (s / Nat.gcd r s)) (T : ℕ) =>
        limAvg U (fun n => ‖dilWin (twLiouville χ) (Nat.gcd r s) n T‖ ^ 2 / (T : ℝ) ^ 2))
      (a := fun _ => (0 : ℝ)) (x := atTop)
      ((Finset.univ : Finset (DirichletCharacter ℂ (s / Nat.gcd r s))).erase 1)
      fun χ hχ => tendsto_limAvg_dilWin hU (norm_twLiouville_le χ)
        (dyadicMR_twLiouville χ (ne_of_mem_erase hχ)) (gcd_pos_of hs)
    rw [sum_const_zero] at this
    exact this
  have hB : Tendsto (fun T : ℕ => ∑ e ∈ (s / Nat.gcd r s).divisors,
      limAvg U (fun n => ‖dilWin (fun m => (ArithmeticFunction.liouville m : ℂ))
        (Nat.gcd r s * e) n T‖ ^ 2 / (T : ℝ) ^ 2)) atTop (𝓝 0) := by
    have := tendsto_finsetSum
      (f := fun (e : ℕ) (T : ℕ) => limAvg U (fun n => ‖dilWin
        (fun m => (ArithmeticFunction.liouville m : ℂ)) (Nat.gcd r s * e) n T‖ ^ 2 / (T : ℝ) ^ 2))
      (a := fun _ => (0 : ℝ)) (x := atTop) ((s / Nat.gcd r s).divisors)
      fun e he => tendsto_limAvg_dilWin hU norm_liouville_le dyadicMR_liouville
        (Nat.mul_pos (gcd_pos_of hs) (Nat.pos_of_mem_divisors he))
    rw [sum_const_zero] at this
    exact this
  have h := (hA.add (hB.const_mul ((s / Nat.gcd r s).divisors.card : ℝ))).const_mul
    (Fintype.card (DirichletCharacter ℂ (s / Nat.gcd r s)) : ℝ)
  simp only [mul_zero, add_zero] at h
  exact h

/-- **(MR) for the twisted windows: `V(b/s, T) → 0`.** -/
theorem tendsto_twistVar_zero (hU : (U : Filter ℝ) ≤ atTop) {s : ℕ} (hs : 1 ≤ s) (b : ℕ) :
    Tendsto (fun T : ℕ => twistVar U ((b : ℝ) / s) T) atTop (𝓝 0) := by
  have hup : Tendsto (fun T : ℕ => (s : ℝ) * ∑ r ∈ range s, limAvg U (fun n => classPart s r T n))
      atTop (𝓝 0) := by
    have := (tendsto_finsetSum (f := fun (r : ℕ) (T : ℕ) => limAvg U (fun n => classPart s r T n))
      (a := fun _ => (0 : ℝ)) (x := atTop) (range s)
      fun r _ => tendsto_limAvg_classPart hU (r := r) hs).const_mul (s : ℝ)
    rw [sum_const_zero, mul_zero] at this
    exact this
  refine squeeze_zero' ?_ ?_ hup
  · refine Eventually.of_forall fun T => ?_
    have hb : Bdd fun n => Complex.normSq (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * ((b : ℝ) / s)))
        / (T : ℝ) ^ 2 := by
      refine ⟨1, fun n => ?_⟩
      rw [abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (by positivity))]
      rcases Nat.eq_zero_or_pos T with h0 | hT
      · rw [h0]; simp
      · have hTR : (0 : ℝ) < T := by exact_mod_cast hT
        rw [div_le_one (by positivity)]
        exact normSq_le_sq_of_norm_le (norm_sum_lam_ex_le T (fun u => n + u) fun u => u * ((b : ℝ) / s))
    exact limAvg_nonneg hU hb fun n => div_nonneg (Complex.normSq_nonneg _) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    have hb : Bdd fun n => Complex.normSq (∑ u ∈ range T, (lam (n + u) : ℂ) * ex (u * ((b : ℝ) / s)))
        / (T : ℝ) ^ 2 := by
      refine ⟨1, fun n => ?_⟩
      rw [abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (by positivity)),
        div_le_one (by positivity)]
      exact normSq_le_sq_of_norm_le (norm_sum_lam_ex_le T (fun u => n + u) fun u => u * ((b : ℝ) / s))
    have hbound := limAvg_mono hU hb
      (((bdd_sum (range s) fun r _ => bdd_classPart (r := r) hs T)).const_mul (s : ℝ))
      (fun n => twist_pointwise_le hs b n T hTR)
    rw [limAvg_const_mul hU (bdd_sum (range s) fun r _ => bdd_classPart (r := r) hs T),
      limAvg_sum hU (range s) fun r _ => bdd_classPart (r := r) hs T] at hbound
    exact hbound

end

end GaloisForLFunctions.LogarithmicChowla
