import GaloisForLFunctions.RHTower.EvenSectorPoleFreeBlindFarkas

/-!
# Two-sided growth of even pole-free positive weights

**Theorem** (`exists_abs_le_of_weilPositiveEvenPolar`).  If `lam` is Weil-positive on all even
tests with `f̂(i/2) = 0`, then `|lam(n)| ≤ C √n (1 + log n)` for every `n ≥ 2`.

No pole weight, no odd test and no lower bound on `lam` are assumed.  So an even pole-free fake can
carry a super-pole `lam ≈ −m n^{σ₁}` only with `σ₁ ≤ ½`.

Proof.  The upper bound is `exists_le_of_weilPositiveEvenPolar`.  For the lower bound use the
negative pole-free node test `o(x − L/2) − o(x + L/2)` (`evenPolarMinusTest`).  Its profile is
`o = (A − κB)/(1 + κ)` with `A = φ(· − 2r) − φ(· + 2r)`, `B = φ(· − r) − φ(· + r)` and
`κ = 2 cosh(r/2) ≥ 2`.  It satisfies `‖o‖² ≥ 2(κ − 1)²‖φ‖²/(1 + κ)² ≥ (2/9)‖φ‖²`
(`le_integral_oddPolarProfile_sq`): both `A` and `B` are sums of two disjoint translates, and
`2AB ≤ A² + B²`.  Its Fourier transform is bounded by `4‖φ̂‖` on the real line and by the pole-test
bound on `|Im z| ≤ ½`, so the archimedean energy has the bound of the corpus even node test.
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided SeparatedBump

theorem two_le_oddPolarCoef (j : ℕ) : 2 ≤ oddPolarCoef j := by
  unfold oddPolarCoef; linarith [Real.one_le_cosh ((nodeBump j).rOut / 2)]

theorem nodeBump_mul_shift_eq_zero (j : ℕ) {a b : ℝ} (hab : 2 * (nodeBump j).rOut ≤ |a - b|)
    (v : ℝ) : nodeBump j (v - a) * nodeBump j (v - b) = 0 := by
  by_cases h : (nodeBump j).rOut ≤ |v - a|
  · rw [nodeBump_eq_zero j h, zero_mul]
  · push Not at h
    have : (nodeBump j).rOut ≤ |v - b| := by
      have h1 := abs_sub_abs_le_abs_sub (a - b) (v - b)
      rw [show a - b - (v - b) = -(v - a) by ring, abs_neg] at h1
      linarith
    rw [nodeBump_eq_zero j this, mul_zero]

theorem integral_nodeBump_shift_sq (j : ℕ) (c : ℝ) :
    ∫ v, nodeBump j (v - c) ^ 2 = ∫ v, nodeBump j v ^ 2 :=
  integral_sub_right_eq_self (fun u => nodeBump j u ^ 2) c

theorem integral_pair_sq (j : ℕ) {a b : ℝ} (hab : 2 * (nodeBump j).rOut ≤ |a - b|) :
    ∫ v, (nodeBump j (v - a) - nodeBump j (v - b)) ^ 2 = 2 * ∫ v, nodeBump j v ^ 2 := by
  have e : (fun v => (nodeBump j (v - a) - nodeBump j (v - b)) ^ 2) =
      fun v => nodeBump j (v - a) ^ 2 + nodeBump j (v - b) ^ 2 := by
    funext v
    have := nodeBump_mul_shift_eq_zero j hab v
    nlinarith [this]
  rw [e, integral_add (integrable_sq_nodeBump_sub j a) (integrable_sq_nodeBump_sub j b),
    integral_nodeBump_shift_sq, integral_nodeBump_shift_sq]
  ring

theorem integrable_pair_sq (j : ℕ) (a b : ℝ) :
    Integrable fun v => (nodeBump j (v - a) - nodeBump j (v - b)) ^ 2 := by
  have h1 := integrable_sq_nodeBump_sub j a
  have h2 := integrable_sq_nodeBump_sub j b
  refine ((h1.add h2).const_mul 2).mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((((nodeBump j).continuous.comp (continuous_sub_right a)).sub
      ((nodeBump j).continuous.comp (continuous_sub_right b))).pow 2).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (nodeBump j (v - a) + nodeBump j (v - b))]

/-- **The odd pole-free profile has mass `≥ (2/9)‖φ‖²`.** -/
theorem le_integral_oddPolarProfile_sq (j : ℕ) :
    2 / 9 * ((nodeScale j)⁻¹ * ∫ u, narrowBump 0 u ^ 2) ≤ ∫ u, oddPolarProfile j u ^ 2 := by
  rw [← integral_nodeBump_sq]
  set r := (nodeBump j).rOut with hr
  have hr0 := (nodeBump j).rOut_pos
  set κ := oddPolarCoef j with hκ
  have hκ2 : 2 ≤ κ := two_le_oddPolarCoef j
  set J := ∫ u, nodeBump j u ^ 2 with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun u => sq_nonneg _
  set A : ℝ → ℝ := fun v => nodeBump j (v - 2 * r) - nodeBump j (v - -(2 * r)) with hA
  set B : ℝ → ℝ := fun v => nodeBump j (v - r) - nodeBump j (v - -r) with hB
  have hAint := integrable_pair_sq j (2 * r) (-(2 * r))
  have hBint := integrable_pair_sq j r (-r)
  have h4 : 2 * r ≤ |2 * r - -(2 * r)| := by
    rw [show 2 * r - -(2 * r) = 4 * r by ring, abs_of_pos (by linarith)]; linarith
  have h2 : 2 * r ≤ |r - -r| := by
    rw [show r - -r = 2 * r by ring, abs_of_pos (by linarith)]
  have hA2 : ∫ v, A v ^ 2 = 2 * J := integral_pair_sq j h4
  have hB2 : ∫ v, B v ^ 2 = 2 * J := integral_pair_sq j h2
  have hpt : ∀ v, oddPolarProfile j v = (A v - κ * B v) / (1 + κ) := fun v => by
    simp only [oddPolarProfile, hA, hB, hr, hκ, sub_neg_eq_add]
  have hk1 : 0 < 1 + κ := by linarith
  -- pointwise lower bound
  have hlow : ∀ v, (1 - κ) * A v ^ 2 + (κ ^ 2 - κ) * B v ^ 2 ≤ (A v - κ * B v) ^ 2 := fun v => by
    nlinarith [sq_nonneg (A v - B v)]
  have hint1 : Integrable fun v => (1 - κ) * A v ^ 2 + (κ ^ 2 - κ) * B v ^ 2 :=
    (hAint.const_mul _).add (hBint.const_mul _)
  have hint2 : Integrable fun v => (A v - κ * B v) ^ 2 := by
    refine ((hAint.add hBint).const_mul (2 * (1 + κ ^ 2))).mono' ?_
      (Filter.Eventually.of_forall fun v => ?_)
    · exact (((((nodeBump j).continuous.comp (continuous_sub_right _)).sub
        ((nodeBump j).continuous.comp (continuous_sub_right _))).sub
        (continuous_const.mul (((nodeBump j).continuous.comp (continuous_sub_right _)).sub
        ((nodeBump j).continuous.comp (continuous_sub_right _))))).pow 2).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (κ * A v + B v), sq_nonneg κ]
  have hmono := integral_mono hint1 hint2 hlow
  rw [integral_add (hAint.const_mul _) (hBint.const_mul _), integral_const_mul,
    integral_const_mul, hA2, hB2] at hmono
  have hsq : ∫ u, oddPolarProfile j u ^ 2 = (∫ v, (A v - κ * B v) ^ 2) / (1 + κ) ^ 2 := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hpt, div_pow]
  rw [hsq, le_div_iff₀ (by positivity)]
  have hfac : (1 + κ) ^ 2 ≤ 9 * (κ - 1) ^ 2 := by nlinarith
  nlinarith

/-! ## The archimedean bound for the negative test -/

theorem norm_paperFT_oddPolarProfile_le (j : ℕ) (r : ℝ) :
    ‖paperFT (fun v => (oddPolarProfile j v : ℂ)) r‖ ≤
      2 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ := by
  rw [oddPolarProfileC_eq]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) r).trans
    (mul_le_mul_of_nonneg_right (le_of_eq ?_) (norm_nonneg _))
  have hk := oddPolarCoef_pos j
  have hk1 : (0 : ℝ) < 1 + oddPolarCoef j := by linarith
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, Complex.norm_real,
    Real.norm_eq_abs, abs_neg, abs_div, abs_one, abs_of_pos hk, abs_of_pos hk1]
  field_simp
  ring

theorem norm_paperFT_oddPolarProfile_imag_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (fun v => (oddPolarProfile j v : ℂ)) ((σ : ℂ) * I)‖ ≤
      2 * Real.exp (1 / 12) * ((nodeScale j)⁻¹ * bumpPoleConst) := by
  have hρ := nodeBump_rOut_le j
  have hρ0 := (nodeBump j).rOut_pos
  rw [oddPolarProfileC_eq]
  have hX : ∀ k ∈ (Finset.univ : Finset (Fin 4)),
      |![2 * (nodeBump j).rOut, -(2 * (nodeBump j).rOut), (nodeBump j).rOut,
        -(nodeBump j).rOut] k| ≤ 1 / 6 := by
    intro k _
    fin_cases k <;> simp <;> rw [abs_of_pos (by linarith)] <;> linarith
  refine (norm_paperFT_sum_translate_imag_le Finset.univ _ _ (continuous_nodeBumpC j)
    (hasCompactSupport_nodeBumpC j) hσ hX).trans ?_
  have hk := oddPolarCoef_pos j
  have hk1 : (0 : ℝ) < 1 + oddPolarCoef j := by linarith
  have hs : (∑ k : Fin 4, ‖(![1 / (1 + oddPolarCoef j), -(1 / (1 + oddPolarCoef j)),
      -(oddPolarCoef j / (1 + oddPolarCoef j)), oddPolarCoef j / (1 + oddPolarCoef j)] k : ℂ)‖)
      = 2 := by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, Complex.norm_real,
      Real.norm_eq_abs, abs_neg, abs_div, abs_one, abs_of_pos hk, abs_of_pos hk1]
    field_simp
    ring
  rw [hs, show (1 / 6 : ℝ) / 2 = 1 / 12 by norm_num]
  have hP := norm_paperFT_nodeBump_imag_le j hσ
  have he : 0 < Real.exp (1 / 12) := Real.exp_pos _
  calc 2 * Real.exp (1 / 12) * ‖paperFT (fun u => (nodeBump j u : ℂ)) ((σ : ℂ) * I)‖
      ≤ 2 * Real.exp (1 / 12) * ((nodeScale j)⁻¹ * bumpPoleConst) := by gcongr

theorem norm_paperFT_evenPolarMinus_le (j : ℕ) (r : ℝ) :
    ‖paperFT (fun u => (evenPolarMinusFn j u : ℂ)) r‖ ≤
      4 * ‖paperFT (fun u => (nodeBump j u : ℂ)) r‖ := by
  have e : (fun u => (evenPolarMinusFn j u : ℂ)) = fun u => ∑ k : Fin 2, (![1, -1] k : ℂ) *
      (fun v => (oddPolarProfile j v : ℂ)) (u - ![Real.log j / 2, -(Real.log j / 2)] k) := by
    funext u
    simp only [evenPolarMinusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    push_cast
    ring
  have hc : Continuous fun v => (oddPolarProfile j v : ℂ) :=
    Complex.continuous_ofReal.comp (contDiff_oddPolarProfile j).continuous
  have hcs : HasCompactSupport fun v => (oddPolarProfile j v : ℂ) :=
    (SeparatedBump.hasCompactSupport_of_abs_gt fun _ hu =>
      oddPolarProfile_eq_zero j hu).comp_left Complex.ofReal_zero
  rw [e]
  refine (norm_paperFT_sum_translate_le Finset.univ _ _ hc hcs r).trans ?_
  have hs : (∑ k : Fin 2, ‖(![1, -1] k : ℂ)‖) = 2 := by simp [Fin.sum_univ_two]; norm_num
  rw [hs]
  linarith [norm_paperFT_oddPolarProfile_le j r]

theorem norm_paperFT_evenPolarMinus_imag_le (j : ℕ) {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ‖paperFT (fun u => (evenPolarMinusFn j u : ℂ)) ((σ : ℂ) * I)‖ ≤
      4 * Real.exp (Real.log j / 4 + 1 / 4) * ((nodeScale j)⁻¹ * bumpPoleConst) := by
  have e : (fun u => (evenPolarMinusFn j u : ℂ)) = fun u => ∑ k : Fin 2, (![1, -1] k : ℂ) *
      (fun v => (oddPolarProfile j v : ℂ)) (u - ![Real.log j / 2, -(Real.log j / 2)] k) := by
    funext u
    simp only [evenPolarMinusFn, bumpSum, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    push_cast
    ring
  have hc : Continuous fun v => (oddPolarProfile j v : ℂ) :=
    Complex.continuous_ofReal.comp (contDiff_oddPolarProfile j).continuous
  have hcs : HasCompactSupport fun v => (oddPolarProfile j v : ℂ) :=
    (SeparatedBump.hasCompactSupport_of_abs_gt fun _ hu =>
      oddPolarProfile_eq_zero j hu).comp_left Complex.ofReal_zero
  have hl : 0 ≤ Real.log j := Real.log_natCast_nonneg j
  have hX : ∀ k ∈ (Finset.univ : Finset (Fin 2)),
      |![Real.log j / 2, -(Real.log j / 2)] k| ≤ Real.log j / 2 := by
    intro k _
    fin_cases k <;> simp [abs_of_nonneg (by linarith : 0 ≤ Real.log j / 2)]
  rw [e]
  refine (norm_paperFT_sum_translate_imag_le Finset.univ _ _ hc hcs hσ hX).trans ?_
  have hs : (∑ k : Fin 2, ‖(![1, -1] k : ℂ)‖) = 2 := by simp [Fin.sum_univ_two]; norm_num
  rw [hs]
  have hq := norm_paperFT_oddPolarProfile_imag_le j hσ
  have hP0 : 0 ≤ (nodeScale j)⁻¹ * bumpPoleConst :=
    mul_nonneg (inv_nonneg.mpr (nodeScale_pos j).le) bumpPoleConst_nonneg
  have he : Real.exp (Real.log j / 2 / 2) * Real.exp (1 / 12) ≤
      Real.exp (Real.log j / 4 + 1 / 4) := by
    rw [← Real.exp_add, Real.exp_le_exp]; linarith
  calc 2 * Real.exp (Real.log j / 2 / 2) *
        ‖paperFT (fun v => (oddPolarProfile j v : ℂ)) ((σ : ℂ) * I)‖
      ≤ 2 * Real.exp (Real.log j / 2 / 2) *
          (2 * Real.exp (1 / 12) * ((nodeScale j)⁻¹ * bumpPoleConst)) := by gcongr
    _ = 4 * (Real.exp (Real.log j / 2 / 2) * Real.exp (1 / 12)) *
          ((nodeScale j)⁻¹ * bumpPoleConst) := by ring
    _ ≤ 4 * Real.exp (Real.log j / 4 + 1 / 4) * ((nodeScale j)⁻¹ * bumpPoleConst) := by gcongr

/-! ## The two-sided bound -/

/-- **Even pole-free positivity bounds the weights below by `−C √n (1 + log n)`.** -/
theorem exists_ge_of_weilPositiveEvenPolar {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → -(C * Real.sqrt n * (1 + Real.log n)) ≤ lam n := by
  have hJ : 0 < ∫ u, narrowBump 0 u ^ 2 := integral_narrowBump_sq_pos 0
  set X := 16 * Real.exp (1 / 2) * bumpPoleConst ^ 2 / (∫ u, narrowBump 0 u ^ 2) +
    4 * ((|gammaLogConst| + 3) * bumpMassConst + bumpLogConst) /
      (Real.pi * ∫ u, narrowBump 0 u ^ 2) with hX
  have hX0 : 0 ≤ X := add_nonneg (by positivity)
    (div_nonneg (by have := bumpMassConst_nonneg; have := bumpLogConst_nonneg; positivity)
      (by positivity))
  refine ⟨9 / 2 * X, by positivity, fun n hn => ?_⟩
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hm0 := nodeScale_pos n
  have hmeq : nodeScale n = 2 * (n : ℝ) + 3 := rfl
  set Bd := 32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 +
    8 / (Real.pi * nodeScale n) *
      ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) with hBd
  have hW := hpf (evenPolarMinusTest n).1.1 (evenPolarMinusTest n).1.2.1
    (evenPolarMinusTest n).1.2.2 (evenPolarMinusTest n).2.1 (evenPolarMinusTest n).2.2
  rw [re_weilFullFunctional_eq lam (evenPolarMinusTest n).1,
    logVector_evenPolarMinusTest ⟨n, hn⟩, Finsupp.linearCombination_single, smul_eq_mul] at hW
  have hA : |weilArchRe (EF.weilTest (evenPolarMinusTest n).1.1 (evenPolarMinusTest n).1.1)| ≤
      Bd :=
    abs_weilArchRe_node_le n (evenPolarMinusTest n).1.2.1.continuous (evenPolarMinusTest n).1.2.2
      (norm_paperFT_evenPolarMinus_le n) fun σ hσ => norm_paperFT_evenPolarMinus_imag_le n hσ
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans hA
  set c₀ := 2 * ((nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2) / Real.sqrt n with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  have hcm : 2 / 9 * c₀ ≤ 2 * (∫ u, oddPolarProfile n u ^ 2) / Real.sqrt n := by
    have := le_integral_oddPolarProfile_sq n
    rw [hc₀, show 2 / 9 * (2 * ((nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2) / Real.sqrt n) =
      2 * (2 / 9 * ((nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2)) / Real.sqrt n by ring]
    exact div_le_div_of_nonneg_right (by linarith) hsq.le
  have hW' : 0 ≤ weilArchRe (EF.weilTest (evenPolarMinusTest n).1.1 (evenPolarMinusTest n).1.1) -
      2 * (∫ u, oddPolarProfile n u ^ 2) / Real.sqrt n * (-lam n) := by linarith
  have hlo : -lam n ≤ Bd / (2 / 9 * c₀) :=
    (le_div_of_node (lt_of_lt_of_le (by positivity) hcm) hW' hA).trans
      (div_le_div_of_nonneg_left hBd0 (by positivity) hcm)
  have hfin : Bd / c₀ = Bd * (Real.sqrt n * nodeScale n / (2 * ∫ u, narrowBump 0 u ^ 2)) := by
    rw [hc₀]
    field_simp
  have hkey := node_bound_le (n := n) (J₀ := ∫ u, narrowBump 0 u ^ 2) (P := bumpPoleConst)
    (K := gammaLogConst) (I₀ := bumpMassConst) (I₁ := bumpLogConst) hn1 hJ bumpMassConst_nonneg
    bumpLogConst_nonneg
  rw [← hmeq, ← hBd, ← hfin] at hkey
  have e : Bd / (2 / 9 * c₀) = 9 / 2 * (Bd / c₀) := by field_simp
  rw [e] at hlo
  have : 9 / 2 * (Bd / c₀) ≤ 9 / 2 * X * Real.sqrt n * (1 + Real.log n) := by
    have := mul_le_mul_of_nonneg_left hkey (by norm_num : (0 : ℝ) ≤ 9 / 2)
    linarith
  linarith

/-- **Two-sided growth of even pole-free positive weights.** -/
theorem exists_abs_le_of_weilPositiveEvenPolar {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → |lam n| ≤ C * Real.sqrt n * (1 + Real.log n) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_le_of_weilPositiveEvenPolar hpf
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_ge_of_weilPositiveEvenPolar hpf
  refine ⟨C₁ + C₂, by positivity, fun n hn => ?_⟩
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hS : 0 ≤ Real.sqrt n * (1 + Real.log n) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ n); positivity
  have h1 := hC₁ n hn
  have h2 := hC₂ n hn
  rw [abs_le]; constructor <;> nlinarith

end RHTower.EvenSector

end
