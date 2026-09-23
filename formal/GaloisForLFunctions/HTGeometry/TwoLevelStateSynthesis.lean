/-
# Every register state is synthesized by two-level rotations and coordinate phases

A unit vector of `ℂ^K` is built from the first basis vector by `K-1` real two-level rotations --
each moving the remaining tail weight one coordinate further -- followed by `K` single-coordinate
phase gates.  The rotation angle at a coordinate is the arccosine of the ratio of its amplitude to
the tail norm, and the phases are the arguments of the amplitudes, so the synthesis is exact and its
length is `2K-1` for every state.

Main results:
* `rotAct`, `phaseAct` — the two gate families, and their isometry.
* `absState`, `rotStep`, `absState_of_le` — the amplitude pass.
* `phState`, `phaseStep_twoLevelStateSynthesis`, `phState_top` — the phase pass.
-/
import GaloisForLFunctions.HTGeometry.PhaseGridApproximation

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {K : ℕ}

/-! ## The two gate families -/

/-- The real two-level rotation on coordinates `i` and `j`. -/
def rotAct (i j : Fin K) (θ : ℝ) (v : Fin K → ℂ) : Fin K → ℂ :=
  fun r =>
    if r = i then ((Real.cos θ : ℝ) : ℂ) * v i - ((Real.sin θ : ℝ) : ℂ) * v j
    else if r = j then ((Real.sin θ : ℝ) : ℂ) * v i + ((Real.cos θ : ℝ) : ℂ) * v j
    else v r

/-- The phase gate on one coordinate. -/
def phaseAct (i : Fin K) (θ : ℝ) (v : Fin K → ℂ) : Fin K → ℂ :=
  fun r => if r = i then Complex.exp ((θ : ℝ) * Complex.I) * v i else v r

theorem rotAct_apply_fst (i j : Fin K) (θ : ℝ) (v : Fin K → ℂ) :
    rotAct i j θ v i = ((Real.cos θ : ℝ) : ℂ) * v i - ((Real.sin θ : ℝ) : ℂ) * v j := by
  rw [rotAct, if_pos rfl]

theorem rotAct_apply_snd {i j : Fin K} (hij : i ≠ j) (θ : ℝ) (v : Fin K → ℂ) :
    rotAct i j θ v j = ((Real.sin θ : ℝ) : ℂ) * v i + ((Real.cos θ : ℝ) : ℂ) * v j := by
  rw [rotAct, if_neg (Ne.symm hij), if_pos rfl]

theorem rotAct_apply_ne (i j : Fin K) (θ : ℝ) (v : Fin K → ℂ) {r : Fin K}
    (hri : r ≠ i) (hrj : r ≠ j) : rotAct i j θ v r = v r := by
  rw [rotAct, if_neg hri, if_neg hrj]

theorem phaseAct_apply_self (i : Fin K) (θ : ℝ) (v : Fin K → ℂ) :
    phaseAct i θ v i = Complex.exp ((θ : ℝ) * Complex.I) * v i := by
  rw [phaseAct, if_pos rfl]

theorem phaseAct_apply_ne (i : Fin K) (θ : ℝ) (v : Fin K → ℂ) {r : Fin K} (hri : r ≠ i) :
    phaseAct i θ v r = v r := by
  rw [phaseAct, if_neg hri]

theorem sum_split_pair {i j : Fin K} (hij : i ≠ j) (f : Fin K → ℝ) :
    ∑ r, f r = f i + f j + ∑ r ∈ (Finset.univ.erase i).erase j, f r := by
  classical
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ i),
    ← Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  ring

/-- **The two-level rotation preserves the norm.** -/
theorem sum_normSq_rotAct {i j : Fin K} (hij : i ≠ j) (θ : ℝ) (v : Fin K → ℂ) :
    ∑ r, ‖rotAct i j θ v r‖ ^ (2 : ℕ) = ∑ r, ‖v r‖ ^ (2 : ℕ) := by
  classical
  rw [sum_split_pair hij (fun r => ‖rotAct i j θ v r‖ ^ (2 : ℕ)),
    sum_split_pair hij (fun r => ‖v r‖ ^ (2 : ℕ))]
  have hrest : ∀ r ∈ (Finset.univ.erase i).erase j,
      ‖rotAct i j θ v r‖ ^ (2 : ℕ) = ‖v r‖ ^ (2 : ℕ) := by
    intro r hr
    rw [rotAct_apply_ne i j θ v (Finset.mem_erase.mp (Finset.mem_of_mem_erase hr)).1
      (Finset.mem_erase.mp hr).1]
  rw [Finset.sum_congr rfl hrest]
  congr 1
  rw [rotAct_apply_fst i j θ v, rotAct_apply_snd hij θ v, Complex.sq_norm, Complex.sq_norm,
    Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination ((v i).re ^ (2 : ℕ) + (v i).im ^ (2 : ℕ) + (v j).re ^ (2 : ℕ) + (v j).im ^ (2 : ℕ)) *
    Real.sin_sq_add_cos_sq θ

/-- **The phase gate preserves the norm.** -/
theorem sum_normSq_phaseAct (i : Fin K) (θ : ℝ) (v : Fin K → ℂ) :
    ∑ r, ‖phaseAct i θ v r‖ ^ (2 : ℕ) = ∑ r, ‖v r‖ ^ (2 : ℕ) := by
  classical
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : r = i
  · subst hr
    rw [phaseAct_apply_self, norm_mul, Complex.norm_exp]
    simp
  · rw [phaseAct_apply_ne i θ v hr]

/-! ## The amplitude pass -/

/-- The tail weight of a state beyond a coordinate index. -/
def tailSq (ψ : Fin K → ℂ) (p : ℕ) : ℝ := ∑ r : Fin K, if p ≤ (r : ℕ) then ‖ψ r‖ ^ (2 : ℕ) else 0

theorem tailSq_nonneg (ψ : Fin K → ℂ) (p : ℕ) : 0 ≤ tailSq ψ p :=
  Finset.sum_nonneg fun r _ => by
    by_cases h : p ≤ (r : ℕ)
    · rw [if_pos h]
      positivity
    · rw [if_neg h]

/-- The tail norm. -/
def tailv (ψ : Fin K → ℂ) (p : ℕ) : ℝ := Real.sqrt (tailSq ψ p)

theorem tailv_nonneg (ψ : Fin K → ℂ) (p : ℕ) : 0 ≤ tailv ψ p := Real.sqrt_nonneg _

theorem sq_tailv (ψ : Fin K → ℂ) (p : ℕ) : (tailv ψ p) ^ (2 : ℕ) = tailSq ψ p :=
  Real.sq_sqrt (tailSq_nonneg ψ p)

theorem tailSq_succ (ψ : Fin K → ℂ) (i : Fin K) :
    tailSq ψ (i : ℕ) = ‖ψ i‖ ^ (2 : ℕ) + tailSq ψ ((i : ℕ) + 1) := by
  classical
  rw [tailSq, tailSq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [if_pos (le_refl (i : ℕ))]
  congr 1
  rw [← Finset.add_sum_erase _ (fun r : Fin K => if (i : ℕ) + 1 ≤ (r : ℕ) then ‖ψ r‖ ^ (2 : ℕ) else 0)
    (Finset.mem_univ i)]
  rw [if_neg (by omega), zero_add]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hne : (x : ℕ) ≠ (i : ℕ) := fun h => (Finset.mem_erase.mp hx).1 (Fin.ext h)
  by_cases hlt : (i : ℕ) ≤ (x : ℕ)
  · rw [if_pos hlt, if_pos (by omega)]
  · rw [if_neg hlt, if_neg (by omega)]

theorem tailSq_of_ge {ψ : Fin K → ℂ} {p : ℕ} (hp : K ≤ p) : tailSq ψ p = 0 := by
  refine Finset.sum_eq_zero fun r _ => ?_
  have : ¬ p ≤ (r : ℕ) := by omega
  rw [if_neg this]

/-- The state after the amplitude pass has processed the first `p` coordinates. -/
def absState (ψ : Fin K → ℂ) (p : ℕ) : Fin K → ℂ :=
  fun r =>
    if (r : ℕ) < p then ((‖ψ r‖ : ℝ) : ℂ)
    else if (r : ℕ) = p then ((tailv ψ p : ℝ) : ℂ) else 0

/-- The rotation angle used at one coordinate. -/
def rotAngle (ψ : Fin K → ℂ) (i : Fin K) : ℝ := Real.arccos (‖ψ i‖ / tailv ψ (i : ℕ))

theorem cos_rotAngle_mul {ψ : Fin K → ℂ} (i : Fin K) :
    Real.cos (rotAngle ψ i) * tailv ψ (i : ℕ) = ‖ψ i‖ := by
  by_cases h0 : tailv ψ (i : ℕ) = 0
  · have hsq : tailSq ψ (i : ℕ) = 0 := by
      have := sq_tailv ψ (i : ℕ)
      rw [h0] at this
      simpa using this.symm
    have : ‖ψ i‖ ^ (2 : ℕ) = 0 := by
      have hstep := tailSq_succ ψ i
      rw [hsq] at hstep
      nlinarith [tailSq_nonneg ψ ((i : ℕ) + 1), sq_nonneg ‖ψ i‖]
    have hzero : ‖ψ i‖ = 0 := by nlinarith [norm_nonneg (ψ i)]
    rw [h0, hzero, mul_zero]
  · have hpos : 0 < tailv ψ (i : ℕ) := lt_of_le_of_ne (tailv_nonneg ψ _) (Ne.symm h0)
    have hle : ‖ψ i‖ / tailv ψ (i : ℕ) ≤ 1 := by
      rw [div_le_one hpos]
      have hstep := tailSq_succ ψ i
      have h2 : ‖ψ i‖ ^ (2 : ℕ) ≤ (tailv ψ (i : ℕ)) ^ (2 : ℕ) := by
        rw [sq_tailv, hstep]
        nlinarith [tailSq_nonneg ψ ((i : ℕ) + 1)]
      nlinarith [norm_nonneg (ψ i), hpos, h2]
    have hge : -1 ≤ ‖ψ i‖ / tailv ψ (i : ℕ) := by
      have : 0 ≤ ‖ψ i‖ / tailv ψ (i : ℕ) := by positivity
      linarith
    rw [rotAngle, Real.cos_arccos hge hle]
    field_simp

theorem sin_rotAngle_mul {ψ : Fin K → ℂ} (i : Fin K) :
    Real.sin (rotAngle ψ i) * tailv ψ (i : ℕ) = tailv ψ ((i : ℕ) + 1) := by
  by_cases h0 : tailv ψ (i : ℕ) = 0
  · have hsq : tailSq ψ (i : ℕ) = 0 := by
      have := sq_tailv ψ (i : ℕ)
      rw [h0] at this
      simpa using this.symm
    have htail : tailSq ψ ((i : ℕ) + 1) = 0 := by
      have hstep := tailSq_succ ψ i
      rw [hsq] at hstep
      nlinarith [tailSq_nonneg ψ ((i : ℕ) + 1), sq_nonneg ‖ψ i‖]
    rw [h0, mul_zero, tailv, htail, Real.sqrt_zero]
  · have hpos : 0 < tailv ψ (i : ℕ) := lt_of_le_of_ne (tailv_nonneg ψ _) (Ne.symm h0)
    have hle : ‖ψ i‖ / tailv ψ (i : ℕ) ≤ 1 := by
      rw [div_le_one hpos]
      have hstep := tailSq_succ ψ i
      have h2 : ‖ψ i‖ ^ (2 : ℕ) ≤ (tailv ψ (i : ℕ)) ^ (2 : ℕ) := by
        rw [sq_tailv, hstep]
        nlinarith [tailSq_nonneg ψ ((i : ℕ) + 1)]
      nlinarith [norm_nonneg (ψ i), hpos, h2]
    have hge : -1 ≤ ‖ψ i‖ / tailv ψ (i : ℕ) := by
      have : 0 ≤ ‖ψ i‖ / tailv ψ (i : ℕ) := by positivity
      linarith
    rw [rotAngle, Real.sin_arccos]
    have hden : ‖ψ i‖ ^ (2 : ℕ) + tailSq ψ ((i : ℕ) + 1) ≠ 0 := by
      have hsq := sq_tailv ψ (i : ℕ)
      rw [tailSq_succ ψ i] at hsq
      intro h
      rw [h] at hsq
      exact h0 (by nlinarith [hsq, tailv_nonneg ψ (i : ℕ)])
    have hid : 1 - (‖ψ i‖ / tailv ψ (i : ℕ)) ^ (2 : ℕ)
        = (tailv ψ ((i : ℕ) + 1)) ^ (2 : ℕ) / (tailv ψ (i : ℕ)) ^ (2 : ℕ) := by
      rw [div_pow, sq_tailv, sq_tailv, tailSq_succ ψ i]
      field_simp
      ring
    have hsq : (tailv ψ ((i : ℕ) + 1)) ^ (2 : ℕ) / (tailv ψ (i : ℕ)) ^ (2 : ℕ)
        = (tailv ψ ((i : ℕ) + 1) / tailv ψ (i : ℕ)) ^ (2 : ℕ) := (div_pow _ _ _).symm
    rw [hid, hsq, Real.sqrt_sq (div_nonneg (tailv_nonneg ψ _) (tailv_nonneg ψ _))]
    field_simp


/-- **The amplitude step.**  One rotation moves the tail weight one coordinate onward. -/
theorem rotStep (ψ : Fin K → ℂ) {i j : Fin K} (hj : (j : ℕ) = (i : ℕ) + 1) :
    rotAct i j (rotAngle ψ i) (absState ψ (i : ℕ)) = absState ψ ((i : ℕ) + 1) := by
  have hij : i ≠ j := by
    intro h
    rw [h] at hj
    omega
  funext r
  by_cases hri : r = i
  · subst hri
    rw [rotAct_apply_fst, absState, absState, absState]
    rw [if_neg (by omega : ¬ (r : ℕ) < (r : ℕ)), if_pos rfl,
      if_neg (by omega : ¬ (j : ℕ) < (r : ℕ)), if_neg (by omega : ¬ (j : ℕ) = (r : ℕ)),
      if_pos (by omega : (r : ℕ) < (r : ℕ) + 1)]
    rw [mul_zero, sub_zero, ← Complex.ofReal_mul, cos_rotAngle_mul]
  · by_cases hrj : r = j
    · subst hrj
      rw [rotAct_apply_snd hij, absState, absState, absState]
      rw [if_neg (by omega : ¬ (i : ℕ) < (i : ℕ)), if_pos rfl,
        if_neg (by omega : ¬ (r : ℕ) < (i : ℕ)), if_neg (by omega : ¬ (r : ℕ) = (i : ℕ)),
        if_neg (by omega : ¬ (r : ℕ) < (i : ℕ) + 1), if_pos (by omega : (r : ℕ) = (i : ℕ) + 1)]
      rw [mul_zero, add_zero, ← Complex.ofReal_mul, sin_rotAngle_mul]
    · rw [rotAct_apply_ne i j _ _ hri hrj, absState, absState]
      have hne1 : (r : ℕ) ≠ (i : ℕ) := fun h => hri (Fin.ext h)
      have hne2 : (r : ℕ) ≠ (i : ℕ) + 1 := by
        intro h
        exact hrj (Fin.ext (by omega))
      by_cases hlt : (r : ℕ) < (i : ℕ)
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg hne1, if_neg (by omega : ¬ (r : ℕ) < (i : ℕ) + 1),
          if_neg (by omega : ¬ (r : ℕ) = (i : ℕ) + 1)]

theorem absState_zero (ψ : Fin K → ℂ) (hunit : ∑ r, ‖ψ r‖ ^ (2 : ℕ) = 1) :
    absState ψ 0 = fun r : Fin K => if (r : ℕ) = 0 then (1 : ℂ) else 0 := by
  funext r
  rw [absState, if_neg (by omega : ¬ (r : ℕ) < 0)]
  by_cases h : (r : ℕ) = 0
  · rw [if_pos h, if_pos h, tailv, tailSq]
    have : (∑ x : Fin K, if (0 : ℕ) ≤ (x : ℕ) then ‖ψ x‖ ^ (2 : ℕ) else 0) = 1 := by
      rw [← hunit]
      exact Finset.sum_congr rfl fun x _ => by rw [if_pos (Nat.zero_le _)]
    rw [this, Real.sqrt_one]
    norm_num
  · rw [if_neg h, if_neg h]

theorem absState_last (ψ : Fin K → ℂ) (hK : 0 < K) :
    absState ψ (K - 1) = fun r => ((‖ψ r‖ : ℝ) : ℂ) := by
  classical
  funext r
  have hrlt : (r : ℕ) < K := r.isLt
  rw [absState]
  by_cases h : (r : ℕ) < K - 1
  · rw [if_pos h]
  · have hEq : (r : ℕ) = K - 1 := by omega
    rw [if_neg h, if_pos hEq]
    congr 1
    rw [tailv, tailSq]
    have hsum : (∑ x : Fin K, if K - 1 ≤ (x : ℕ) then ‖ψ x‖ ^ (2 : ℕ) else 0) = ‖ψ r‖ ^ (2 : ℕ) := by
      rw [Finset.sum_eq_single r]
      · rw [if_pos (by omega)]
      · intro x _ hxr
        have : ¬ K - 1 ≤ (x : ℕ) := by
          have hxlt : (x : ℕ) < K := x.isLt
          intro hge
          exact hxr (Fin.ext (by omega))
        rw [if_neg this]
      · intro h
        exact absurd (Finset.mem_univ r) h
    rw [hsum, Real.sqrt_sq (norm_nonneg _)]

/-! ## The phase pass -/

/-- The state after the phase pass has processed the first `q` coordinates. -/
def phState (ψ : Fin K → ℂ) (q : ℕ) : Fin K → ℂ :=
  fun r => if (r : ℕ) < q then ψ r else ((‖ψ r‖ : ℝ) : ℂ)

theorem phaseStep_twoLevelStateSynthesis (ψ : Fin K → ℂ) (i : Fin K) :
    phaseAct i (Complex.arg (ψ i)) (phState ψ (i : ℕ)) = phState ψ ((i : ℕ) + 1) := by
  funext r
  by_cases hri : r = i
  · subst hri
    rw [phaseAct_apply_self, phState, phState, if_neg (by omega : ¬ (r : ℕ) < (r : ℕ)),
      if_pos (by omega : (r : ℕ) < (r : ℕ) + 1)]
    rw [mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I (ψ r)
  · rw [phaseAct_apply_ne i _ _ hri, phState, phState]
    have hne : (r : ℕ) ≠ (i : ℕ) := fun h => hri (Fin.ext h)
    by_cases hlt : (r : ℕ) < (i : ℕ)
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega : ¬ (r : ℕ) < (i : ℕ) + 1)]

theorem phState_zero (ψ : Fin K → ℂ) : phState ψ 0 = fun r => ((‖ψ r‖ : ℝ) : ℂ) := by
  funext r
  rw [phState, if_neg (by omega : ¬ (r : ℕ) < 0)]

theorem phState_of_ge (ψ : Fin K → ℂ) {q : ℕ} (hq : K ≤ q) : phState ψ q = ψ := by
  funext r
  rw [phState, if_pos (by omega : (r : ℕ) < q)]


/-! ## Linearity, isometry and parameter continuity -/

theorem rotAct_sub (i j : Fin K) (θ : ℝ) (v w : Fin K → ℂ) :
    rotAct i j θ (v - w) = rotAct i j θ v - rotAct i j θ w := by
  funext r
  simp only [Pi.sub_apply, rotAct]
  split_ifs <;> ring

theorem phaseAct_sub (i : Fin K) (θ : ℝ) (v w : Fin K → ℂ) :
    phaseAct i θ (v - w) = phaseAct i θ v - phaseAct i θ w := by
  funext r
  simp only [Pi.sub_apply, phaseAct]
  split_ifs <;> ring

theorem rotAct_mul_right (i j : Fin K) (θ : ℝ) (A : Fin K → ℂ) (c : ℂ) :
    rotAct i j θ (fun x => A x * c) = fun x => rotAct i j θ A x * c := by
  funext r
  simp only [rotAct]
  split_ifs <;> ring

theorem phaseAct_mul_right (i : Fin K) (θ : ℝ) (A : Fin K → ℂ) (c : ℂ) :
    phaseAct i θ (fun x => A x * c) = fun x => phaseAct i θ A x * c := by
  funext r
  simp only [phaseAct]
  split_ifs <;> ring

theorem norm_ofReal_mul_add_le (c s : ℝ) (x y : ℂ) :
    ‖((c : ℝ) : ℂ) * x + ((s : ℝ) : ℂ) * y‖ ≤ |c| * ‖x‖ + |s| * ‖y‖ := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

theorem coord_le_l2 (v : Fin K → ℂ) (x : Fin K) :
    ‖v x‖ ≤ Real.sqrt (∑ r, ‖v r‖ ^ (2 : ℕ)) := by
  rw [show ‖v x‖ = Real.sqrt (‖v x‖ ^ (2 : ℕ)) from (Real.sqrt_sq (norm_nonneg _)).symm]
  refine Real.sqrt_le_sqrt ?_
  exact Finset.single_le_sum (f := fun r => ‖v r‖ ^ (2 : ℕ)) (fun r _ => by positivity)
    (Finset.mem_univ x)

/-- **The two-level rotation moves with its trigonometric parameters.** -/
theorem norm_rotAct_sub_le (i j : Fin K) (θ θ' : ℝ) (v : Fin K → ℂ) (r : Fin K) :
    ‖rotAct i j θ v r - rotAct i j θ' v r‖
      ≤ (|Real.cos θ - Real.cos θ'| + |Real.sin θ - Real.sin θ'|) *
          Real.sqrt (∑ x, ‖v x‖ ^ (2 : ℕ)) := by
  classical
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = Real.sqrt (∑ x, ‖v x‖ ^ (2 : ℕ)) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; exact Real.sqrt_nonneg _
  have hvi : ∀ x : Fin K, ‖v x‖ ≤ M := by
    intro x
    rw [hMdef]
    exact coord_le_l2 v x
  have hkey : rotAct i j θ v r - rotAct i j θ' v r
      = if r = i then
          ((Real.cos θ - Real.cos θ' : ℝ) : ℂ) * v i
            + ((-(Real.sin θ - Real.sin θ') : ℝ) : ℂ) * v j
        else if r = j then
          ((Real.sin θ - Real.sin θ' : ℝ) : ℂ) * v i
            + ((Real.cos θ - Real.cos θ' : ℝ) : ℂ) * v j
        else 0 := by
    simp only [rotAct]
    split_ifs <;> push_cast <;> ring
  rw [hkey, ← hMdef]
  split_ifs
  · refine le_trans (norm_ofReal_mul_add_le _ _ _ _) ?_
    rw [abs_neg]
    nlinarith [hvi i, hvi j, hM0, abs_nonneg (Real.cos θ - Real.cos θ'),
      abs_nonneg (Real.sin θ - Real.sin θ'), norm_nonneg (v i), norm_nonneg (v j)]
  · refine le_trans (norm_ofReal_mul_add_le _ _ _ _) ?_
    nlinarith [hvi i, hvi j, hM0, abs_nonneg (Real.cos θ - Real.cos θ'),
      abs_nonneg (Real.sin θ - Real.sin θ'), norm_nonneg (v i), norm_nonneg (v j)]
  · rw [norm_zero]
    have h1 : (0 : ℝ) ≤ |Real.cos θ - Real.cos θ'| + |Real.sin θ - Real.sin θ'| := by positivity
    exact mul_nonneg h1 hM0

/-- **The phase gate moves with its phase.** -/
theorem norm_phaseAct_sub_le (i : Fin K) (θ θ' : ℝ) (v : Fin K → ℂ) (r : Fin K) :
    ‖phaseAct i θ v r - phaseAct i θ' v r‖
      ≤ ‖Complex.exp ((θ : ℝ) * Complex.I) - Complex.exp ((θ' : ℝ) * Complex.I)‖ *
          Real.sqrt (∑ x, ‖v x‖ ^ (2 : ℕ)) := by
  classical
  by_cases hri : r = i
  · subst hri
    rw [phaseAct_apply_self, phaseAct_apply_self, ← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (coord_le_l2 v r) (norm_nonneg _)
  · rw [phaseAct_apply_ne i θ v hri, phaseAct_apply_ne i θ' v hri, sub_self, norm_zero]
    positivity

end GaloisForLFunctions.HTGeometry

end
