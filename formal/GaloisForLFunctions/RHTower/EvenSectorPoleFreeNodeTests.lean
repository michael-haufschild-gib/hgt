import GaloisForLFunctions.RHTower.EvenSectorFarBumpPoleFreeCombination
import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth

/-!
# Pole-free even node tests and the growth of even pole-free weights

Let `φ` be the node bump of `n`, of radius `r`.  The profile

`q(v) = φ(v) − (φ(v − 2r) + φ(v + 2r))/(2 cosh r)`   (`evenPolarProfile`)

is even, vanishes for `|v| > 3r`, and satisfies `∫ q(v) e^{±v/2} dv = 0`; so every translate of `q`
is pole-free.  The even test `q(x − L/2) + q(x + L/2)`, `L = log n` (`evenPolarNode`), is
pole-free, and its autocorrelation meets the nodes `±log m`, `m ≥ 2`, only at `m = n`, with value
`2‖q‖²/√n > 0` (`logVector_evenPolarNode`).

**Theorem** (`exists_le_of_weilPositiveEvenPolar`).  If `lam` is Weil-positive on even tests with
`f̂(i/2) = 0`, then `lam(n) ≤ C √n (1 + log n)` for every `n ≥ 2`.  For weights bounded below this
is the two-sided bound `|lam(n)| ≤ C √n (1 + log n)`
(`exists_abs_le_of_weilPositiveEvenPolar_of_ge`).

The pole correction sits inside the node bump, at distance `2r`, so it costs only a bounded factor:
`‖f̂‖ ≤ 4‖φ̂‖` on the real line and `‖f̂(σi)‖ ≤ 4 e^{(log n)/4 + 1/4} ‖φ̂(σi)‖` for `|σ| ≤ 1/2`, the
bounds of the even node test with pole.
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided SeparatedBump

/-! ## The pole-free profile -/

/-- The pole-correction coefficient `1/(2 cosh r)`. -/
def evenPolarCoef (j : ℕ) : ℝ := 1 / (2 * Real.cosh (nodeBump j).rOut)

theorem evenPolarCoef_pos (j : ℕ) : 0 < evenPolarCoef j := by
  unfold evenPolarCoef; have := Real.cosh_pos (nodeBump j).rOut; positivity

theorem evenPolarCoef_le_half (j : ℕ) : evenPolarCoef j ≤ 1 / 2 := by
  unfold evenPolarCoef
  have h := Real.one_le_cosh (nodeBump j).rOut
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- The pole-free even profile `φ(v) − c (φ(v − 2r) + φ(v + 2r))`, `c = 1/(2 cosh r)`. -/
def evenPolarProfile (j : ℕ) (v : ℝ) : ℝ :=
  nodeBump j v - evenPolarCoef j * (nodeBump j (v - 2 * (nodeBump j).rOut) +
    nodeBump j (v + 2 * (nodeBump j).rOut))

theorem contDiff_evenPolarProfile (j : ℕ) : ContDiff ℝ 2 (evenPolarProfile j) :=
  (nodeBump j).contDiff.sub (contDiff_const.mul
    (((nodeBump j).contDiff.comp (contDiff_id.sub contDiff_const)).add
      ((nodeBump j).contDiff.comp (contDiff_id.add contDiff_const))))

theorem evenPolarProfile_eq_zero (j : ℕ) {u : ℝ} (hu : 6 * (nodeBump j).rOut / 2 < |u|) :
    evenPolarProfile j u = 0 := by
  have hr := (nodeBump j).rOut_pos
  have h1 := abs_sub_abs_le_abs_sub u (2 * (nodeBump j).rOut)
  have h2 := abs_sub_abs_le_abs_sub u (-(2 * (nodeBump j).rOut))
  rw [abs_of_pos (by linarith : 0 < 2 * (nodeBump j).rOut)] at h1
  rw [abs_neg, abs_of_pos (by linarith : 0 < 2 * (nodeBump j).rOut), sub_neg_eq_add] at h2
  unfold evenPolarProfile
  rw [nodeBump_eq_zero j (u := u) (by linarith),
    nodeBump_eq_zero j (u := u - 2 * (nodeBump j).rOut) (by linarith),
    nodeBump_eq_zero j (u := u + 2 * (nodeBump j).rOut) (by linarith)]
  ring

theorem evenPolarProfile_neg (j : ℕ) (v : ℝ) : evenPolarProfile j (-v) = evenPolarProfile j v := by
  unfold evenPolarProfile
  rw [nodeBump_neg, show -v - 2 * (nodeBump j).rOut = -(v + 2 * (nodeBump j).rOut) by ring,
    show -v + 2 * (nodeBump j).rOut = -(v - 2 * (nodeBump j).rOut) by ring, nodeBump_neg,
    nodeBump_neg]
  ring

theorem evenPolarProfileC_eq (j : ℕ) :
    (fun v => (evenPolarProfile j v : ℂ)) = fun v => ∑ k : Fin 3,
      (![1, -evenPolarCoef j, -evenPolarCoef j] k : ℂ) * (fun w => (nodeBump j w : ℂ))
        (v - ![0, 2 * (nodeBump j).rOut, -(2 * (nodeBump j).rOut)] k) := by
  funext v
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, evenPolarProfile, sub_zero, sub_neg_eq_add]
  push_cast
  ring

theorem cexp_I_mul_I_div_two (x : ℝ) :
    Complex.exp (I * (I / 2) * x) = ((Real.exp (-x / 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((x : ℂ) / 2) * Complex.I_sq

/-- **The profile is pole-free:** `∫ q(v) e^{−v/2} dv = 0`. -/
theorem paperFT_evenPolarProfile_I_div_two (j : ℕ) :
    paperFT (fun v => (evenPolarProfile j v : ℂ)) (I / 2) = 0 := by
  rw [evenPolarProfileC_eq, paperFT_sum_translate Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j)]
  set r := (nodeBump j).rOut with hr
  have hsum : (∑ k : Fin 3, (![1, -evenPolarCoef j, -evenPolarCoef j] k : ℂ) *
      Complex.exp (I * (I / 2) * ((![0, 2 * r, -(2 * r)] k : ℝ) : ℂ))) = 0 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, cexp_I_mul_I_div_two]
    have e1 : Real.exp (-(0 : ℝ) / 2) = 1 := by simp
    have e2 : Real.exp (-(2 * r) / 2) = Real.exp (-r) := by ring_nf
    have e3 : Real.exp (-(-(2 * r)) / 2) = Real.exp r := by ring_nf
    rw [e1, e2, e3]
    have hc : evenPolarCoef j * (Real.exp (-r) + Real.exp r) = 1 := by
      unfold evenPolarCoef
      rw [← hr, Real.cosh_eq]
      have : 0 < Real.exp r + Real.exp (-r) := by positivity
      field_simp
      ring
    have hc' : ((evenPolarCoef j : ℂ) * ((Real.exp (-r) : ℝ) + (Real.exp r : ℝ))) = 1 := by
      exact_mod_cast hc
    push_cast at hc' ⊢
    linear_combination -hc'
  rw [hsum, zero_mul]

theorem sq_nodeBump_le_sq_evenPolarProfile (j : ℕ) (v : ℝ) :
    nodeBump j v ^ 2 ≤ evenPolarProfile j v ^ 2 := by
  have hr := (nodeBump j).rOut_pos
  by_cases h : (nodeBump j).rOut ≤ |v|
  · rw [nodeBump_eq_zero j h]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · push Not at h
    have h1 := abs_sub_abs_le_abs_sub (2 * (nodeBump j).rOut) v
    have h2 := abs_sub_abs_le_abs_sub (2 * (nodeBump j).rOut) (-v)
    rw [abs_of_pos (by linarith : 0 < 2 * (nodeBump j).rOut), abs_sub_comm] at h1
    rw [abs_of_pos (by linarith : 0 < 2 * (nodeBump j).rOut), abs_neg, sub_neg_eq_add,
      add_comm] at h2
    unfold evenPolarProfile
    rw [nodeBump_eq_zero j (u := v - 2 * (nodeBump j).rOut) (by linarith),
      nodeBump_eq_zero j (u := v + 2 * (nodeBump j).rOut) (by linarith)]
    simp

theorem integrable_evenPolarProfile_sq (j : ℕ) : Integrable fun v => evenPolarProfile j v ^ 2 :=
  ((contDiff_evenPolarProfile j).continuous.pow 2).integrable_of_hasCompactSupport
    (SeparatedBump.hasCompactSupport_of_abs_gt (R := 6 * (nodeBump j).rOut / 2) fun u hu => by
      show evenPolarProfile j u ^ 2 = 0
      rw [evenPolarProfile_eq_zero j hu]
      norm_num)

theorem le_integral_evenPolarProfile_sq (j : ℕ) :
    (nodeScale j)⁻¹ * (∫ u, narrowBump 0 u ^ 2) ≤ ∫ u, evenPolarProfile j u ^ 2 := by
  rw [← integral_nodeBump_sq]
  refine integral_mono ?_ (integrable_evenPolarProfile_sq j)
    (sq_nodeBump_le_sq_evenPolarProfile j)
  simpa using integrable_sq_nodeBump_sub j 0

/-! ## The pole-free even node test -/

/-- `q(x − L/2) + q(x + L/2)`, `L = log j`, with the pole-free profile `q`. -/
def evenPolarNodeFn (j : ℕ) : ℝ → ℝ :=
  bumpSum (evenPolarProfile j) ![1, 1] ![Real.log j / 2, -(Real.log j / 2)]

theorem evenPolarNodeFn_neg (j : ℕ) (x : ℝ) : evenPolarNodeFn j (-x) = evenPolarNodeFn j x := by
  simp only [evenPolarNodeFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [show -x - Real.log j / 2 = -(x + Real.log j / 2) by ring,
    show -x - -(Real.log j / 2) = -(x - Real.log j / 2) by ring, evenPolarProfile_neg,
    evenPolarProfile_neg, show x - -(Real.log j / 2) = x + Real.log j / 2 by ring]
  ring

theorem contDiff_evenPolarNodeC (j : ℕ) : ContDiff ℝ 2 fun u => (evenPolarNodeFn j u : ℂ) := by
  have h : ContDiff ℝ 2 (evenPolarNodeFn j) :=
    contDiff_bumpSum (contDiff_evenPolarProfile j) _ _
  exact Complex.ofRealCLM.contDiff.comp h

theorem hasCompactSupport_evenPolarNodeC (j : ℕ) :
    HasCompactSupport fun u => (evenPolarNodeFn j u : ℂ) := by
  have h : HasCompactSupport (evenPolarNodeFn j) :=
    hasCompactSupport_bumpSum (fun u hu => evenPolarProfile_eq_zero j hu) _ _
  exact h.comp_left Complex.ofReal_zero

/-- The pole-free even test with node value `+2‖q‖²/√j`. -/
def evenPolarNode (j : ℕ) : EvenWeilTestFn :=
  ⟨⟨fun u => (evenPolarNodeFn j u : ℂ), contDiff_evenPolarNodeC j,
    hasCompactSupport_evenPolarNodeC j⟩, fun x => by simp only [evenPolarNodeFn_neg]⟩

theorem logVector_evenPolarNode (j : LogIndex) :
    logVector (evenPolarNode j).1 =
      Finsupp.single j (2 * (∫ u, evenPolarProfile j u ^ 2) / Real.sqrt j) := by
  ext m
  rw [logVector_apply, Finsupp.single_apply]
  change logValue (fun u => (evenPolarNodeFn j u : ℂ)) m = _
  unfold evenPolarNodeFn
  rw [logValue_evenPair j.2 _ (contDiff_evenPolarProfile j)
    (fun u hu => evenPolarProfile_eq_zero j hu) 1 1 m.2]
  by_cases h : (m : ℕ) = j
  · rw [if_pos h, if_pos (Subtype.ext h).symm, h]; ring
  · rw [if_neg h, if_neg fun h' => h (congrArg Subtype.val h'.symm)]

theorem evenPolarNodeC_eq (j : ℕ) :
    (fun u => (evenPolarNodeFn j u : ℂ)) = fun u => ∑ k : Fin 2, (![1, 1] k : ℂ) *
      (fun v => (evenPolarProfile j v : ℂ)) (u - ![Real.log j / 2, -(Real.log j / 2)] k) := by
  funext u
  simp only [evenPolarNodeFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  ring

theorem continuous_evenPolarProfileC (j : ℕ) : Continuous fun v => (evenPolarProfile j v : ℂ) :=
  Complex.continuous_ofReal.comp (contDiff_evenPolarProfile j).continuous

theorem hasCompactSupport_evenPolarProfileC (j : ℕ) :
    HasCompactSupport fun v => (evenPolarProfile j v : ℂ) :=
  (SeparatedBump.hasCompactSupport_of_abs_gt fun _ hu => evenPolarProfile_eq_zero j hu).comp_left
    Complex.ofReal_zero

/-- **The node test is pole-free.** -/
theorem paperFT_evenPolarNode_I_div_two (j : ℕ) :
    paperFT (fun u => (evenPolarNodeFn j u : ℂ)) (I / 2) = 0 := by
  rw [evenPolarNodeC_eq, paperFT_sum_translate Finset.univ _ _ (continuous_evenPolarProfileC j)
    (hasCompactSupport_evenPolarProfileC j), paperFT_evenPolarProfile_I_div_two, mul_zero]

theorem norm_paperFT_evenPolarProfile_le (j : ℕ) (r : ℝ) :
    ‖paperFT (fun v => (evenPolarProfile j v : ℂ)) r‖ ≤
      2 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ := by
  rw [evenPolarProfileC_eq]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) r).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hc := evenPolarCoef_pos j
  have hc2 := evenPolarCoef_le_half j
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_one,
    abs_of_pos hc]
  linarith

theorem norm_paperFT_evenPolarNode_le (j : ℕ) (r : ℝ) :
    ‖paperFT (fun u => (evenPolarNodeFn j u : ℂ)) r‖ ≤
      4 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ := by
  rw [evenPolarNodeC_eq]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _ (continuous_evenPolarProfileC j)
    (hasCompactSupport_evenPolarProfileC j) r).trans ?_
  have hs : (∑ k : Fin 2, ‖(![1, 1] k : ℂ)‖) = 2 := by simp [Fin.sum_univ_two]; norm_num
  rw [hs]
  linarith [norm_paperFT_evenPolarProfile_le j r]

theorem norm_paperFT_evenPolarProfile_imag_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (fun v => (evenPolarProfile j v : ℂ)) ((σ : ℂ) * I)‖ ≤
      2 * Real.exp (1 / 12) * ((nodeScale j)⁻¹ * bumpPoleConst) := by
  have hρ := nodeBump_rOut_le j
  have hρ0 := (nodeBump j).rOut_pos
  rw [evenPolarProfileC_eq]
  have hX : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      |![0, 2 * (nodeBump j).rOut, -(2 * (nodeBump j).rOut)] k| ≤ 1 / 6 := by
    intro k _
    fin_cases k <;> simp <;> rw [abs_of_pos (by linarith)] <;> linarith
  refine (norm_paperFT_sum_translate_imag_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) hσ hX).trans ?_
  have hc := evenPolarCoef_pos j
  have hc2 := evenPolarCoef_le_half j
  have hs : (∑ k : Fin 3, ‖(![1, -evenPolarCoef j, -evenPolarCoef j] k : ℂ)‖) ≤ 2 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_one,
      abs_of_pos hc]
    linarith
  rw [show (1 / 6 : ℝ) / 2 = 1 / 12 by norm_num]
  have hP := norm_paperFT_nodeBump_imag_le j hσ
  have hP0 : 0 ≤ ‖paperFT (fun u => (nodeBump j u : ℂ)) ((σ : ℂ) * I)‖ := norm_nonneg _
  have he : 0 < Real.exp (1 / 12) := Real.exp_pos _
  calc (∑ k : Fin 3, ‖(![1, -evenPolarCoef j, -evenPolarCoef j] k : ℂ)‖) * Real.exp (1 / 12) *
        ‖paperFT (fun u => (nodeBump j u : ℂ)) ((σ : ℂ) * I)‖
      ≤ 2 * Real.exp (1 / 12) * ‖paperFT (fun u => (nodeBump j u : ℂ)) ((σ : ℂ) * I)‖ := by
        gcongr
    _ ≤ 2 * Real.exp (1 / 12) * ((nodeScale j)⁻¹ * bumpPoleConst) := by gcongr

theorem norm_paperFT_evenPolarNode_imag_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (fun u => (evenPolarNodeFn j u : ℂ)) ((σ : ℂ) * I)‖ ≤
      4 * Real.exp (Real.log j / 4 + 1 / 4) * ((nodeScale j)⁻¹ * bumpPoleConst) := by
  rw [evenPolarNodeC_eq]
  have hl : 0 ≤ Real.log j := Real.log_natCast_nonneg j
  have hX : ∀ k ∈ (Finset.univ : Finset (Fin 2)),
      |![Real.log j / 2, -(Real.log j / 2)] k| ≤ Real.log j / 2 := by
    intro k _
    fin_cases k <;> simp [abs_of_nonneg (by linarith : 0 ≤ Real.log j / 2)]
  refine (norm_paperFT_sum_translate_imag_le Finset.univ _ _ (continuous_evenPolarProfileC j)
    (hasCompactSupport_evenPolarProfileC j) hσ hX).trans ?_
  have hs : (∑ k : Fin 2, ‖(![1, 1] k : ℂ)‖) = 2 := by simp [Fin.sum_univ_two]; norm_num
  rw [hs]
  have hq := norm_paperFT_evenPolarProfile_imag_le j hσ
  have hP0 : 0 ≤ (nodeScale j)⁻¹ * bumpPoleConst :=
    mul_nonneg (inv_nonneg.mpr (nodeScale_pos j).le) bumpPoleConst_nonneg
  have he : Real.exp (Real.log j / 2 / 2) * Real.exp (1 / 12) ≤
      Real.exp (Real.log j / 4 + 1 / 4) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  calc 2 * Real.exp (Real.log j / 2 / 2) *
        ‖paperFT (fun v => (evenPolarProfile j v : ℂ)) ((σ : ℂ) * I)‖
      ≤ 2 * Real.exp (Real.log j / 2 / 2) *
          (2 * Real.exp (1 / 12) * ((nodeScale j)⁻¹ * bumpPoleConst)) := by gcongr
    _ = 4 * (Real.exp (Real.log j / 2 / 2) * Real.exp (1 / 12)) *
          ((nodeScale j)⁻¹ * bumpPoleConst) := by ring
    _ ≤ 4 * Real.exp (Real.log j / 4 + 1 / 4) * ((nodeScale j)⁻¹ * bumpPoleConst) := by gcongr

/-! ## Growth of even pole-free weights -/

/-- **Even pole-free positivity bounds the weights above by `C √n (1 + log n)`.** -/
theorem exists_le_of_weilPositiveEvenPolar {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → lam n ≤ C * Real.sqrt n * (1 + Real.log n) := by
  have hJ : 0 < ∫ u, narrowBump 0 u ^ 2 := integral_narrowBump_sq_pos 0
  refine ⟨16 * Real.exp (1 / 2) * bumpPoleConst ^ 2 / (∫ u, narrowBump 0 u ^ 2) +
    4 * ((|gammaLogConst| + 3) * bumpMassConst + bumpLogConst) /
      (Real.pi * ∫ u, narrowBump 0 u ^ 2),
    add_nonneg (by positivity)
      (div_nonneg (by have := bumpMassConst_nonneg; have := bumpLogConst_nonneg; positivity)
        (by positivity)), fun n hn => ?_⟩
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hm0 := nodeScale_pos n
  have hmeq : nodeScale n = 2 * (n : ℝ) + 3 := rfl
  set Bd := 32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 +
    8 / (Real.pi * nodeScale n) *
      ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) with hBd
  have hW := hpf (evenPolarNode n).1.1 (evenPolarNode n).1.2.1 (evenPolarNode n).1.2.2
    (evenPolarNode n).2 (paperFT_evenPolarNode_I_div_two n)
  rw [re_weilFullFunctional_eq lam (evenPolarNode n).1, logVector_evenPolarNode ⟨n, hn⟩,
    Finsupp.linearCombination_single, smul_eq_mul] at hW
  have hA : |weilArchRe (EF.weilTest (evenPolarNode n).1.1 (evenPolarNode n).1.1)| ≤ Bd :=
    abs_weilArchRe_node_le n (evenPolarNode n).1.2.1.continuous (evenPolarNode n).1.2.2
      (norm_paperFT_evenPolarNode_le n) fun σ hσ => norm_paperFT_evenPolarNode_imag_le n hσ
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans hA
  set c₀ := 2 * ((nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2) / Real.sqrt n with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  have hcp : c₀ ≤ 2 * (∫ u, evenPolarProfile n u ^ 2) / Real.sqrt n :=
    div_le_div_of_nonneg_right (by linarith [le_integral_evenPolarProfile_sq n]) hsq.le
  have hup : lam n ≤ Bd / c₀ :=
    (le_div_of_node (lt_of_lt_of_le hc₀0 hcp) hW hA).trans
      (div_le_div_of_nonneg_left hBd0 hc₀0 hcp)
  have hfin : Bd / c₀ = Bd * (Real.sqrt n * nodeScale n / (2 * ∫ u, narrowBump 0 u ^ 2)) := by
    rw [hc₀]
    field_simp
  have hkey := node_bound_le (n := n) (J₀ := ∫ u, narrowBump 0 u ^ 2) (P := bumpPoleConst)
    (K := gammaLogConst) (I₀ := bumpMassConst) (I₁ := bumpLogConst) hn1 hJ bumpMassConst_nonneg
    bumpLogConst_nonneg
  rw [← hmeq, ← hBd, ← hfin] at hkey
  linarith

/-- **Two-sided growth of even pole-free weights bounded below.** -/
theorem exists_abs_le_of_weilPositiveEvenPolar_of_ge {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {C : ℝ} (hlb : ∀ n, 2 ≤ n → -C ≤ lam n) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ n : ℕ, 2 ≤ n → |lam n| ≤ C' * Real.sqrt n * (1 + Real.log n) := by
  obtain ⟨K, hK0, hK⟩ := exists_le_of_weilPositiveEvenPolar hpf
  refine ⟨K + |C|, by positivity, fun n hn => ?_⟩
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hS : 1 ≤ Real.sqrt n * (1 + Real.log n) := by nlinarith
  have hC : C ≤ |C| * (Real.sqrt n * (1 + Real.log n)) := by
    nlinarith [le_abs_self C, abs_nonneg C]
  have h1 := hK n hn
  have h2 := hlb n hn
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg C]

end RHTower.EvenSector

end
