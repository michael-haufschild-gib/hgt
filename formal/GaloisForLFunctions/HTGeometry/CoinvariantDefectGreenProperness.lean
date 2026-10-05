import GaloisForLFunctions.HTGeometry.HypoexponentialRateReconstruction

/-!
# Character coinvariant defect, Green properness, and reflection–formation selection

For a probability law `ν` on `[0, ∞)` the character multipliers `a_n = L_ν(n)` satisfy
`1 ≥ a_1 ≥ a_2 ≥ ⋯ > 0`, and `a_1 = 1` exactly for `ν = δ_0` `(CDG.4)`–`(CDG.5)`, since
`1 - e^{-x} ≥ 0` vanishes only at `x = 0`.  On `c_0` the coinvariant defect `I - M_ν` has diagonal
`1 - a_n ∈ [1 - a_1, 1]`, so off `δ_0` it is an automorphism with
`(1 - a_1)‖b‖ ≤ ‖(I - M_ν) b‖ ≤ ‖b‖`; since `‖M_ν‖ = a_1 < 1` its inverse is the norm-convergent
positive Green series `Σ_k M_ν^k`, of norm exactly `1/(1 - a_1)` `(CDG.9)`–`(CDG.11)`.  The
anti-coinvariant defect `I + M_ν` has diagonal in `(1, 2]` and is always an automorphism with
inverse of norm `≤ 1` `(CDG.12)`–`(CDG.13)`.

Since `b_n(J ∗ ν) = a_n b_n(J)`, a finite signed current with `J ∗ ν = J` (`ν ≠ δ_0`) or
`J ∗ ν = -J` has all responses zero and vanishes (half-line Choquet–Deny); hence a reflection that
equals formation and has a parity selects the zero current.  For the all-subset law of a finite
prime set, `L(1) = Π_{∅ ≠ S} λ_S/(λ_S + 1) < 1`; the gap `1 - L(1)` grows with the aperture and
tends to one along the first primes, while direct deconvolution stays compact.

The exact anti-coinvariant gap is `inf_n (1 + a_n) = 1 + ν({0})`; the universal value `γ_+ = 1` is
attained exactly for atomless laws.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal ZeroAtInfty

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LaplaceTomography

open GaloisForLFunctions.HTGeometry.PrimeShiftSource Permutohedral

/-! ### The multipliers `(CDG.3)`–`(CDG.5)` -/

section Multipliers

variable (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]

theorem mult_antitone : Antitone (mult ν) := by
  refine antitone_nat_of_succ_le fun k => ?_
  refine integral_mono (integrable_exp_neg_mul ν _) (integrable_exp_neg_mul ν _) fun x => ?_
  show Real.exp (-(((k + 1 + 1 : ℕ) : ℝ) * (x : ℝ))) ≤ Real.exp (-(((k + 1 : ℕ) : ℝ) * (x : ℝ)))
  refine Real.exp_le_exp.2 ?_
  push_cast
  nlinarith [x.2]

theorem mult_le_mult_zero (k : ℕ) : mult ν k ≤ mult ν 0 := mult_antitone ν (Nat.zero_le k)

/-- **`(CDG.5)`**: `a_1 = 1` exactly for `ν = δ_0`. -/
theorem mult_zero_eq_one_iff : mult ν 0 = 1 ↔ ν = Measure.dirac 0 := by
  constructor
  · intro h1
    have hint : Integrable (fun x : ℝ≥0 => 1 - Real.exp (-(((0 + 1 : ℕ) : ℝ) * (x : ℝ)))) ν :=
      (integrable_const 1).sub (integrable_exp_neg_mul ν _)
    have hzero : ∫ x, (1 - Real.exp (-(((0 + 1 : ℕ) : ℝ) * (x : ℝ)))) ∂ν = 0 := by
      have : ∫ x, Real.exp (-(((0 + 1 : ℕ) : ℝ) * (x : ℝ))) ∂ν = 1 := h1
      rw [integral_sub (integrable_const 1) (integrable_exp_neg_mul ν _), this]
      simp
    have hnn : 0 ≤ fun x : ℝ≥0 => 1 - Real.exp (-(((0 + 1 : ℕ) : ℝ) * (x : ℝ))) := fun x => by
      simp only [Pi.zero_apply, sub_nonneg, Real.exp_le_one_iff, neg_nonpos]
      push_cast
      linarith [x.2]
    have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 hzero
    have h0 : ∀ᵐ x ∂ν, x ∈ ({0} : Set ℝ≥0) := hae.mono fun x hx => by
      simp only [Pi.zero_apply, sub_eq_zero] at hx
      push_cast at hx
      have : (x : ℝ) = 0 := by
        have h2 := Real.exp_eq_one_iff (-(1 * (x : ℝ))) |>.1 hx.symm
        linarith
      exact NNReal.coe_eq_zero.1 this
    have hone : ν {0} = 1 :=
      (prob_compl_eq_zero_iff (measurableSet_singleton 0)).1 (ae_iff.1 h0)
    rw [← Measure.restrict_eq_self_of_ae_mem h0, Measure.restrict_singleton, hone, one_smul]
  · rintro rfl
    simp [mult, laplaceInt]

theorem mult_zero_lt_one (hν : ν ≠ Measure.dirac 0) : mult ν 0 < 1 :=
  lt_of_le_of_ne (mult_le_one ν 0) fun h => hν ((mult_zero_eq_one_iff ν).1 h)

end Multipliers

/-! ### Diagonal operators on `c_0` -/

theorem clm_ext_c0 {A B : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ)} (h : ∀ b k, A b k = B b k) : A = B :=
  ContinuousLinearMap.ext fun b => ZeroAtInftyContinuousMap.ext fun k => h b k

/-- The diagonal operator with a bounded multiplier `c`. -/
def diagOp (c : ℕ → ℝ) {C : ℝ} (hc : ∀ k, |c k| ≤ C) : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun b => ofTendsto (fun k => c k * b k) (by
        have hlim := (tendsto_norm_zero.comp (tendsto_c0 b)).const_mul C
        rw [mul_zero] at hlim
        refine squeeze_zero_norm (fun k => ?_) hlim
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hc k) (abs_nonneg _))
      map_add' := fun b d => ZeroAtInftyContinuousMap.ext fun k => by simp [mul_add]
      map_smul' := fun a b => ZeroAtInftyContinuousMap.ext fun k => by
        simp only [ofTendsto_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
    (max C 0) fun b => by
      refine norm_le_of_forall (mul_nonneg (le_max_right _ _) (norm_nonneg _)) fun k => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ofTendsto_apply, abs_mul]
      exact mul_le_mul (le_max_of_le_left (hc k)) (abs_apply_le_norm b k) (abs_nonneg _)
        (le_max_right _ _)

@[simp] theorem diagOp_apply (c : ℕ → ℝ) {C : ℝ} (hc : ∀ k, |c k| ≤ C) (b : C₀(ℕ, ℝ)) (k : ℕ) :
    diagOp c hc b k = c k * b k := rfl

section Defect

variable (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]

theorem one_sub_diagMul_apply (b : C₀(ℕ, ℝ)) (k : ℕ) :
    ((1 - diagMul ν) b) k = (1 - mult ν k) * b k := by
  show (b - diagMul ν b) k = _
  simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, diagMul_apply]
  ring

theorem one_add_diagMul_apply (b : C₀(ℕ, ℝ)) (k : ℕ) :
    ((1 + diagMul ν) b) k = (1 + mult ν k) * b k := by
  show (b + diagMul ν b) k = _
  simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, diagMul_apply]
  ring

/-- `‖M_ν‖ = a_1`. -/
theorem norm_diagMul : ‖diagMul ν‖ = mult ν 0 := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (mult_pos ν 0).le fun b => ?_) ?_
  · refine norm_le_of_forall (mul_nonneg (mult_pos ν 0).le (norm_nonneg _)) fun k => ?_
    rw [diagMul_apply, abs_mul, abs_of_pos (mult_pos ν k)]
    exact mul_le_mul (mult_le_mult_zero ν k) (abs_apply_le_norm b k) (abs_nonneg _)
      (mult_pos ν 0).le
  · have := (diagMul ν).le_opNorm (unitC0 0)
    rwa [norm_diagMul_unitC0, norm_unitC0, mul_one] at this

/-- **Theorem 3.1, `(CDG.9)`**: `(1 - a_1)‖b‖ ≤ ‖(I - M_ν) b‖ ≤ ‖b‖`. -/
theorem one_sub_diagMul_bounds (b : C₀(ℕ, ℝ)) :
    (1 - mult ν 0) * ‖b‖ ≤ ‖(1 - diagMul ν) b‖ ∧ ‖(1 - diagMul ν) b‖ ≤ ‖b‖ := by
  have h0 := mult_le_one ν 0
  constructor
  · rcases (sub_nonneg.2 h0).lt_or_eq with hpos | heq
    · rw [← le_div_iff₀' hpos]
      refine norm_le_of_forall (by positivity) fun k => ?_
      rw [le_div_iff₀' hpos]
      calc (1 - mult ν 0) * |b k| ≤ (1 - mult ν k) * |b k| :=
            mul_le_mul_of_nonneg_right (by linarith [mult_le_mult_zero ν k]) (abs_nonneg _)
        _ = |((1 - diagMul ν) b) k| := by
            rw [one_sub_diagMul_apply, abs_mul,
              abs_of_nonneg (show (0 : ℝ) ≤ 1 - mult ν k by linarith [mult_le_one ν k])]
        _ ≤ _ := abs_apply_le_norm _ k
    · rw [← heq, zero_mul]; exact norm_nonneg _
  · refine norm_le_of_forall (norm_nonneg _) fun k => ?_
    rw [one_sub_diagMul_apply, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - mult ν k by linarith [mult_le_one ν k])]
    exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith [mult_pos ν k])).trans
      (abs_apply_le_norm b k)

/-- The positive Green operator `Σ_k M_ν^k`. -/
def greenOp : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ) := ∑' k : ℕ, diagMul ν ^ k

/-- **Theorem 3.1, `(CDG.10)`**: off `δ_0` the Green series inverts `I - M_ν`, coordinatewise
`(G b)_k = b_k/(1 - a_{k+1})`, positively, with `‖G‖ = 1/(1 - a_1)`. -/
theorem greenOp_spec (hν : ν ≠ Measure.dirac 0) :
    greenOp ν * (1 - diagMul ν) = 1 ∧ (1 - diagMul ν) * greenOp ν = 1 ∧
      (∀ b k, greenOp ν b k = b k / (1 - mult ν k)) ∧
      (∀ b : C₀(ℕ, ℝ), (∀ k, 0 ≤ b k) → ∀ k, 0 ≤ greenOp ν b k) ∧
      ‖greenOp ν‖ = 1 / (1 - mult ν 0) := by
  have hlt := mult_zero_lt_one ν hν
  have hnorm : ‖diagMul ν‖ < 1 := by rw [norm_diagMul]; exact hlt
  have h1 : greenOp ν * (1 - diagMul ν) = 1 := by
    unfold greenOp; exact geom_series_mul_neg (R := C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ)) _ hnorm
  have h2 : (1 - diagMul ν) * greenOp ν = 1 := by
    unfold greenOp; exact mul_neg_geom_series (R := C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ)) _ hnorm
  have hpos : ∀ k, 0 < 1 - mult ν k := fun k => by linarith [mult_le_mult_zero ν k]
  have hcoord : ∀ b k, greenOp ν b k = b k / (1 - mult ν k) := fun b k => by
    have := congrArg (fun A : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ) => A b k) h2
    change ((1 - diagMul ν) (greenOp ν b)) k = b k at this
    rw [one_sub_diagMul_apply] at this
    rw [eq_div_iff (hpos k).ne', mul_comm]
    exact this
  refine ⟨h1, h2, hcoord, fun b hb k => ?_, ?_⟩
  · rw [hcoord]; exact div_nonneg (hb k) (hpos k).le
  · refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity [hpos 0]) fun b => ?_)
      ?_
    · refine norm_le_of_forall (by positivity [hpos 0]) fun k => ?_
      rw [hcoord, abs_div, abs_of_pos (hpos k), div_le_iff₀ (hpos k), one_div, mul_comm,
        ← mul_assoc]
      have h3 : (1 - mult ν k) * (1 - mult ν 0)⁻¹ ≥ 1 := by
        rw [ge_iff_le, ← div_eq_mul_inv, le_div_iff₀ (hpos 0), one_mul]
        linarith [mult_le_mult_zero ν k]
      calc |b k| ≤ ‖b‖ := abs_apply_le_norm b k
        _ ≤ (1 - mult ν k) * (1 - mult ν 0)⁻¹ * ‖b‖ := le_mul_of_one_le_left (norm_nonneg _) h3
    · have := (greenOp ν).le_opNorm (unitC0 0)
      rw [norm_unitC0, mul_one] at this
      refine le_trans ?_ this
      have := abs_apply_le_norm (greenOp ν (unitC0 0)) 0
      rw [hcoord] at this
      simpa [unitC0, abs_of_pos (hpos 0)] using this

/-- **`(CDG.11)`**: `I - M_ν` is bounded below exactly when `ν ≠ δ_0`; at `δ_0`, `M_ν = I`. -/
theorem one_sub_diagMul_proper_iff :
    (∃ c > 0, ∀ b, c * ‖b‖ ≤ ‖(1 - diagMul ν) b‖) ↔ ν ≠ Measure.dirac 0 := by
  constructor
  · rintro ⟨c, hc, hb⟩ rfl
    have := hb (unitC0 0)
    rw [norm_unitC0, mul_one] at this
    have h1 : mult (Measure.dirac (0 : ℝ≥0)) 0 = 1 := (mult_zero_eq_one_iff _).2 rfl
    have h2 : (1 - diagMul (Measure.dirac (0 : ℝ≥0))) (unitC0 0) = 0 :=
      ZeroAtInftyContinuousMap.ext fun k => by
        rw [one_sub_diagMul_apply]
        simp only [unitC0, ofTendsto_apply, Pi.single_apply, ZeroAtInftyContinuousMap.coe_zero,
          Pi.zero_apply]
        split_ifs with hk
        · subst hk; rw [h1]; ring
        · ring
    rw [h2, norm_zero] at this
    linarith
  · intro hν
    exact ⟨1 - mult ν 0, by linarith [mult_zero_lt_one ν hν],
      fun b => (one_sub_diagMul_bounds ν b).1⟩

theorem diagMul_dirac : diagMul (Measure.dirac (0 : ℝ≥0)) = 1 := by
  refine clm_ext_c0 fun b k => ?_
  show mult (Measure.dirac (0 : ℝ≥0)) k * b k = b k
  have h : mult (Measure.dirac (0 : ℝ≥0)) k = 1 := by simp [mult, laplaceInt]
  rw [h, one_mul]

/-- **Theorem 3.2, `(CDG.12)`–`(CDG.13)`**: `‖b‖ ≤ ‖(I + M_ν) b‖ ≤ 2‖b‖`, and `I + M_ν` has a
two-sided inverse of norm at most one. -/
theorem one_add_diagMul_spec :
    (∀ b, ‖b‖ ≤ ‖(1 + diagMul ν) b‖ ∧ ‖(1 + diagMul ν) b‖ ≤ 2 * ‖b‖) ∧
      ∃ G : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ), G * (1 + diagMul ν) = 1 ∧ (1 + diagMul ν) * G = 1 ∧
        ‖G‖ ≤ 1 := by
  have hpos : ∀ k, 0 < 1 + mult ν k := fun k => by linarith [mult_pos ν k]
  have hc : ∀ k, |(1 + mult ν k)⁻¹| ≤ 1 := fun k => by
    rw [abs_of_pos (inv_pos.2 (hpos k))]
    exact inv_le_one_of_one_le₀ (by linarith [mult_pos ν k])
  refine ⟨fun b => ⟨?_, ?_⟩, diagOp (fun k => (1 + mult ν k)⁻¹) hc, ?_, ?_, ?_⟩
  · refine norm_le_of_forall (norm_nonneg _) fun k => ?_
    calc |b k| ≤ (1 + mult ν k) * |b k| := le_mul_of_one_le_left (abs_nonneg _)
          (by linarith [mult_pos ν k])
      _ = |((1 + diagMul ν) b) k| := by
          rw [one_add_diagMul_apply, abs_mul, abs_of_pos (show (0 : ℝ) < 1 + mult ν k from hpos k)]
      _ ≤ _ := abs_apply_le_norm _ k
  · refine norm_le_of_forall (by positivity) fun k => ?_
    rw [one_add_diagMul_apply, abs_mul, abs_of_pos (show (0 : ℝ) < 1 + mult ν k from hpos k)]
    exact mul_le_mul (by linarith [mult_le_one ν k]) (abs_apply_le_norm b k) (abs_nonneg _)
      (by norm_num)
  · refine clm_ext_c0 fun b k => ?_
    show diagOp _ hc ((1 + diagMul ν) b) k = b k
    rw [diagOp_apply, one_add_diagMul_apply, ← mul_assoc, inv_mul_cancel₀ (hpos k).ne', one_mul]
  · refine clm_ext_c0 fun b k => ?_
    show ((1 + diagMul ν) (diagOp _ hc b)) k = b k
    rw [one_add_diagMul_apply, diagOp_apply, ← mul_assoc, mul_inv_cancel₀ (hpos k).ne', one_mul]
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b => ?_
    refine norm_le_of_forall (by positivity) fun k => ?_
    rw [diagOp_apply, abs_mul, one_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hc k)).trans (abs_apply_le_norm b k)

/-- **`(CDG.14)`**: the coinvariant gap `1 - a_1` is attained; the anti-coinvariant gap is exactly
`inf_n (1 + a_n) = 1 + ν({0})`, which equals the universal value `1` for atomless laws. -/
theorem defect_gaps_exact :
    ‖(1 - diagMul ν) (unitC0 0)‖ = (1 - mult ν 0) * ‖unitC0 0‖ ∧
      (∀ b, (1 + ν.real {0}) * ‖b‖ ≤ ‖(1 + diagMul ν) b‖) ∧
      Tendsto (fun k => ‖(1 + diagMul ν) (unitC0 k)‖) atTop (𝓝 (1 + ν.real {0})) := by
  have hcoord : ∀ c : ℕ → ℝ, ∀ k, ∀ g : C₀(ℕ, ℝ), (∀ j, g j = c j * unitC0 k j) →
      ‖g‖ = |c k| := fun c k g hg => by
    refine le_antisymm (norm_le_of_forall (abs_nonneg _) fun j => ?_) ?_
    · rw [hg]
      simp only [unitC0, ofTendsto_apply, Pi.single_apply]
      split_ifs with h
      · subst h; simp
      · simp
    · have := abs_apply_le_norm g k
      rw [hg] at this
      simpa [unitC0] using this
  refine ⟨?_, fun b => ?_, ?_⟩
  · rw [hcoord (fun j => 1 - mult ν j) 0 _ fun j => one_sub_diagMul_apply ν _ j, norm_unitC0,
      mul_one, abs_of_nonneg (by linarith [mult_le_one ν 0])]
  · refine (le_div_iff₀' (by positivity)).1 (norm_le_of_forall (by positivity) fun k => ?_)
    rw [le_div_iff₀' (by positivity)]
    calc (1 + ν.real {0}) * |b k| ≤ (1 + mult ν k) * |b k| :=
          mul_le_mul_of_nonneg_right (by linarith [atom_le_mult ν k]) (abs_nonneg _)
      _ = |((1 + diagMul ν) b) k| := by
          rw [one_add_diagMul_apply, abs_mul,
            abs_of_pos (show (0 : ℝ) < 1 + mult ν k by linarith [mult_pos ν k])]
      _ ≤ _ := abs_apply_le_norm _ k
  · have h := (tendsto_mult ν).const_add 1
    refine h.congr fun k => ?_
    rw [hcoord (fun j => 1 + mult ν j) k _ fun j => one_add_diagMul_apply ν _ j,
      abs_of_pos (by linarith [mult_pos ν k])]

end Defect


/-! ### The properness table (§4) -/

/-- **§4**: at `δ_0`, `M_ν = I` and `I - M_ν = 0`; with an origin atom `M_ν` is an automorphism;
without one it is compact with nonclosed range; off `δ_0`, `I - M_ν` is an automorphism. -/
theorem properness_table (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    (diagMul (Measure.dirac (0 : ℝ≥0)) = 1 ∧ 1 - diagMul (Measure.dirac (0 : ℝ≥0)) = 0) ∧
      (0 < ν.real {0} → ∃ G : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ), G * diagMul ν = 1 ∧ diagMul ν * G = 1) ∧
      (ν {0} = 0 → IsCompactOperator (diagMul ν) ∧ ¬ IsClosed (range (diagMul ν))) ∧
      (ν ≠ Measure.dirac 0 → ∃ G : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ),
        G * (1 - diagMul ν) = 1 ∧ (1 - diagMul ν) * G = 1) := by
  refine ⟨⟨diagMul_dirac, by
    rw [diagMul_dirac]; exact sub_self (1 : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ))⟩, fun hα => ?_, fun hα => ?_,
    fun hν => ⟨greenOp ν, (greenOp_spec ν hν).1, (greenOp_spec ν hν).2.1⟩⟩
  · have hc : ∀ k, |(mult ν k)⁻¹| ≤ (ν.real {0})⁻¹ := fun k => by
      rw [abs_of_pos (inv_pos.2 (mult_pos ν k))]
      exact inv_anti₀ hα (atom_le_mult ν k)
    refine ⟨diagOp (fun k => (mult ν k)⁻¹) hc, clm_ext_c0 fun b k => ?_, clm_ext_c0 fun b k => ?_⟩
    · show diagOp _ hc (diagMul ν b) k = b k
      rw [diagOp_apply, diagMul_apply, ← mul_assoc, inv_mul_cancel₀ (mult_pos ν k).ne', one_mul]
    · show diagMul ν (diagOp _ hc b) k = b k
      rw [diagMul_apply, diagOp_apply, ← mul_assoc, mul_inv_cancel₀ (mult_pos ν k).ne', one_mul]
  · obtain ⟨-, hc, -, -, hn, -⟩ := originAtom_zero ν hα
    exact ⟨hc, hn⟩

/-- **Loop A, complementarity**: an atomless formation law makes `M_ν` compact with nonclosed
range while `I - M_ν` stays bounded below by `1 - L_ν(1) > 0`. -/
theorem complementarity (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (hα : ν {0} = 0) :
    IsCompactOperator (diagMul ν) ∧ ¬ IsClosed (range (diagMul ν)) ∧ 0 < 1 - mult ν 0 ∧
      ∀ b, (1 - mult ν 0) * ‖b‖ ≤ ‖(1 - diagMul ν) b‖ := by
  have hν : ν ≠ Measure.dirac 0 := fun h => by
    rw [h] at hα
    simp at hα
  obtain ⟨-, hc, -, -, hn, -⟩ := originAtom_zero ν hα
  exact ⟨hc, hn, by linarith [mult_zero_lt_one ν hν], fun b => (one_sub_diagMul_bounds ν b).1⟩

/-! ### Linearity of the responses -/

theorem isFiniteMeasure_variation {X : Type*} [MeasurableSpace X] (J : SignedMeasure X) :
    IsFiniteMeasure J.variation := by
  have h := VectorMeasure.variation_sub_le (μ := J.toJordanDecomposition.posPart.toSignedMeasure)
    (ν := J.toJordanDecomposition.negPart.toSignedMeasure)
  rw [Measure.variation_toSignedMeasure, Measure.variation_toSignedMeasure,
    ← JordanDecomposition.toSignedMeasure, J.toSignedMeasure_toJordanDecomposition] at h
  exact isFiniteMeasure_of_le _ h

theorem integrable_charResponse (J : SignedMeasure ℝ≥0) (n : ℕ) :
    VectorMeasure.Integrable J fun x : ℝ≥0 => Real.exp (-(n * (x : ℝ))) := by
  haveI := isFiniteMeasure_variation J
  exact integrable_exp_neg_mul _ n

theorem charResponse_sub (J K : SignedMeasure ℝ≥0) (n : ℕ) :
    charResponse (J - K) n = charResponse J n - charResponse K n :=
  VectorMeasure.integral_sub_vectorMeasure (integrable_charResponse J n)
    (integrable_charResponse K n)

theorem charResponse_add (J K : SignedMeasure ℝ≥0) (n : ℕ) :
    charResponse (J + K) n = charResponse J n + charResponse K n :=
  VectorMeasure.integral_add_vectorMeasure (integrable_charResponse J n)
    (integrable_charResponse K n)

theorem charResponse_smul (c : ℝ) (J : SignedMeasure ℝ≥0) (n : ℕ) :
    charResponse (c • J) n = c * charResponse J n := by
  rw [charResponse, VectorMeasure.integral_smul_vectorMeasure]
  rfl

/-! ### Half-line Choquet–Deny rigidity (Theorem 5.1) -/

/-- **Theorem 5.1 (1), `(CDG.15)`**: a finite signed current fixed by a nontrivial formation is
zero (no mass or origin condition is needed). -/
theorem eq_zero_of_conv_eq_self (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (hν : ν ≠ Measure.dirac 0) {J : SignedMeasure ℝ≥0} (h : convSigned J ν = J) : J = 0 := by
  refine eq_zero_of_charResponse_eq_zero J fun n hn => ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 := charResponse_convSigned J ν (k + 1)
  rw [h] at h1
  have hlt : laplaceInt ν (k + 1) < 1 :=
    (mult_le_mult_zero ν k).trans_lt (mult_zero_lt_one ν hν)
  have : (1 - laplaceInt ν (k + 1)) * charResponse J (k + 1) = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left (by linarith)

/-- **Theorem 5.1 (2), `(CDG.16)`**: a finite signed current anti-fixed by any formation is zero. -/
theorem eq_zero_of_conv_eq_neg (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    {J : SignedMeasure ℝ≥0} (h : convSigned J ν = -J) : J = 0 := by
  refine eq_zero_of_charResponse_eq_zero J fun n hn => ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 := charResponse_convSigned J ν (k + 1)
  rw [h, ← neg_one_smul ℝ J, charResponse_smul] at h1
  have hpos : 0 < laplaceInt ν (k + 1) := mult_pos ν k
  have : (1 + laplaceInt ν (k + 1)) * charResponse J (k + 1) = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left (by linarith)

/-- **Theorem 5.1** in the card's form, for zero-mass currents. -/
theorem choquetDeny (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] {J : SignedMeasure ℝ≥0}
    (_hmass : J univ = 0) :
    (ν ≠ Measure.dirac 0 → convSigned J ν = J → J = 0) ∧ (convSigned J ν = -J → J = 0) :=
  ⟨fun hν h => eq_zero_of_conv_eq_self ν hν h, fun h => eq_zero_of_conv_eq_neg ν h⟩

/-- **`(CDG.17)`–`(CDG.18)`**: response gaps for `J - J ∗ ν` and `J + J ∗ ν`. -/
theorem response_gaps (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (J : SignedMeasure ℝ≥0)
    (hJ : J {0} = 0) :
    (∀ k, ((1 - diagMul ν) (responseC0 J hJ)) k = charResponse (J - convSigned J ν) (k + 1)) ∧
      (∀ k, ((1 + diagMul ν) (responseC0 J hJ)) k =
        charResponse (J + convSigned J ν) (k + 1)) ∧
      (1 - mult ν 0) * ‖responseC0 J hJ‖ ≤ ‖(1 - diagMul ν) (responseC0 J hJ)‖ ∧
      ‖responseC0 J hJ‖ ≤ ‖(1 + diagMul ν) (responseC0 J hJ)‖ := by
  refine ⟨fun k => ?_, fun k => ?_, (one_sub_diagMul_bounds ν _).1,
    ((one_add_diagMul_spec ν).1 _).1⟩
  · rw [one_sub_diagMul_apply, charResponse_sub, charResponse_convSigned]
    simp only [responseC0, ofTendsto_apply, mult]
    ring
  · rw [one_add_diagMul_apply, charResponse_add, charResponse_convSigned]
    simp only [responseC0, ofTendsto_apply, mult]
    ring

/-! ### The reflection–formation selector (Corollary 6.1) -/

/-- **Corollary 6.1**: if a source action satisfies `R J = J ∗ ν` and has parity `R J = ε J`, then
`J = 0` (for `ε = 1` provided `ν ≠ δ_0`). -/
theorem reflection_formation_selection (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (R : SignedMeasure ℝ≥0 → SignedMeasure ℝ≥0) {J : SignedMeasure ℝ≥0}
    (hRJ : R J = convSigned J ν) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hpar : R J = ε • J)
    (hnontriv : ε = 1 → ν ≠ Measure.dirac 0) : J = 0 := by
  rcases hε with rfl | rfl
  · exact eq_zero_of_conv_eq_self ν (hnontriv rfl) (by rw [← hRJ, hpar, one_smul])
  · exact eq_zero_of_conv_eq_neg ν (by rw [← hRJ, hpar]; exact neg_one_smul ℝ J)


/-! ### The all-subset prime-log gap (§7) -/

instance (I : PrimeSet) : IsProbabilityMeasure (halfLineLaw (primeLaw I)) :=
  isProbabilityMeasure_halfLineLaw
    (ae_nonneg_of_hasHalfLineCDF (hasHalfLineCDF_subsetLaw I.grades_pos))

theorem laplaceInt_halfLineLaw {ν : Measure ℝ} (hν : ∀ᵐ x ∂ν, 0 ≤ x) (n : ℕ) :
    laplaceInt (halfLineLaw ν) n = ∫ x, Real.exp (-(n * x)) ∂ν := by
  conv_rhs => rw [← map_halfLineLaw hν]
  rw [measurableEmbedding_toReal.integral_map]
  rfl

/-- `Π_{∅ ≠ S ⊆ I} λ_S/(λ_S + 1)`. -/
def subsetProduct (I : PrimeSet) : ℝ :=
  ∏ S ∈ subsets I.1.card, (∑ i ∈ S, I.grades i) / ((∑ i ∈ S, I.grades i) + 1)

/-- **`(CDG.21)`**: `L_{ν_I}(1) = Π_{∅ ≠ S} λ_S/(λ_S + 1)`. -/
theorem mult_primeLaw_zero (I : PrimeSet) :
    mult (halfLineLaw (primeLaw I)) 0 = subsetProduct I := by
  rw [mult, laplaceInt_halfLineLaw (ν := primeLaw I) (ae_nonneg_of_hasHalfLineCDF
    (hasHalfLineCDF_subsetLaw I.grades_pos)), subsetProduct, ← integral_exp_subsetLaw
    I.grades_pos zero_le_one]
  simp [primeLaw]

theorem factor_mem (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x / (x + 1) ∧ x / (x + 1) ≤ 1 :=
  ⟨by positivity, (div_le_one (by linarith)).2 (by linarith)⟩

theorem subsetProduct_lt_one (I : PrimeSet) : subsetProduct I < 1 := by
  classical
  have huniv : (Finset.univ : Finset (Fin I.1.card)) ∈ subsets I.1.card :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.univ_nonempty_iff.2
      ⟨⟨0, Finset.card_pos.2 I.2.1⟩⟩⟩
  have hnn : ∀ S : Finset (Fin I.1.card), 0 ≤ ∑ i ∈ S, I.grades i :=
    fun S => Finset.sum_nonneg fun i _ => (I.grades_pos i).le
  rw [subsetProduct, ← Finset.mul_prod_erase _ _ huniv]
  have hlt : (∑ i, I.grades i) / ((∑ i, I.grades i) + 1) < 1 :=
    (div_lt_one (by linarith [hnn Finset.univ])).2 (by linarith)
  refine lt_of_le_of_lt (mul_le_of_le_one_right (factor_mem _ (hnn _)).1
    (Finset.prod_le_one (fun S _ => (factor_mem _ (hnn S)).1)
      fun S _ => (factor_mem _ (hnn S)).2)) hlt

/-- **`(CDG.22)`**: the all-subset formation is nontrivial, its coinvariant defect has the explicit
gap `γ_I = 1 - Π λ_S/(λ_S + 1) > 0`, while its direct deconvolution is compact and nonproper. -/
theorem allSubset_gap (I : PrimeSet) :
    halfLineLaw (primeLaw I) ≠ Measure.dirac 0 ∧
      mult (halfLineLaw (primeLaw I)) 0 = subsetProduct I ∧ 0 < 1 - subsetProduct I ∧
      (∀ b, (1 - subsetProduct I) * ‖b‖ ≤ ‖(1 - diagMul (halfLineLaw (primeLaw I))) b‖) ∧
      IsCompactOperator (diagMul (halfLineLaw (primeLaw I))) ∧
      ¬ IsClosed (range (diagMul (halfLineLaw (primeLaw I)))) := by
  obtain ⟨h0, -, hc, -, hn⟩ := primeLaw_compact_response I
  refine ⟨fun h => ?_, mult_primeLaw_zero I, by linarith [subsetProduct_lt_one I],
    fun b => ?_, hc, hn⟩
  · rw [h] at h0
    simp at h0
  · rw [← mult_primeLaw_zero]
    exact (one_sub_diagMul_bounds _ b).1

/-- The all-subset product over the subsets of a finite set of primes. -/
def primeSubsetProduct (s : Finset ℕ) : ℝ :=
  ∏ T ∈ s.powerset.filter Finset.Nonempty,
    (∑ p ∈ T, Real.log p) / ((∑ p ∈ T, Real.log p) + 1)

theorem subsetProduct_eq (I : PrimeSet) : subsetProduct I = primeSubsetProduct I.1 := by
  classical
  unfold subsetProduct primeSubsetProduct
  have hinj : Function.Injective I.prime := (I.1.orderEmbOfFin rfl).injective
  have hrange : ∀ p ∈ I.1, ∃ i, I.prime i = p := fun p hp => by
    have : p ∈ Set.range (I.1.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hp
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  refine Finset.prod_bij' (fun S _ => S.image I.prime)
    (fun T _ => Finset.univ.filter fun i => I.prime i ∈ T) (fun S hS => ?_) (fun T hT => ?_)
    (fun S _ => ?_) (fun T hT => ?_) (fun S _ => ?_)
  · rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun p hp => ?_, (Finset.mem_filter.1 hS).2.image _⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact Finset.orderEmbOfFin_mem _ _ _
  · rw [Finset.mem_filter, Finset.mem_powerset] at hT
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨p, hp⟩ := hT.2
    obtain ⟨i, rfl⟩ := hrange p (hT.1 hp)
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩⟩
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨j, hj, hji⟩
      rwa [hinj hji] at hj
    · intro hi
      exact ⟨i, hi, rfl⟩
  · rw [Finset.mem_filter, Finset.mem_powerset] at hT
    ext p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hp
      obtain ⟨i, rfl⟩ := hrange p (hT.1 hp)
      exact ⟨i, hp, rfl⟩
  · rw [Finset.sum_image (f := fun p : ℕ => Real.log p) (g := I.prime) fun a _ b _ h => hinj h]
    rfl

/-- **§7, aperture monotonicity**: enlarging the prime set can only decrease the all-subset product,
so the coinvariant gap `γ_I` increases with the aperture. -/
theorem subsetGap_mono {I J : PrimeSet} (hIJ : I.1 ⊆ J.1) :
    1 - subsetProduct I ≤ 1 - subsetProduct J := by
  classical
  rw [subsetProduct_eq, subsetProduct_eq, sub_le_sub_iff_left, primeSubsetProduct,
    primeSubsetProduct]
  have hsub : I.1.powerset.filter Finset.Nonempty ⊆ J.1.powerset.filter Finset.Nonempty :=
    fun T hT => by
      rw [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      exact ⟨hT.1.trans hIJ, hT.2⟩
  have hf : ∀ T ∈ J.1.powerset.filter Finset.Nonempty,
      0 ≤ (∑ p ∈ T, Real.log p) / ((∑ p ∈ T, Real.log p) + 1) ∧
        (∑ p ∈ T, Real.log p) / ((∑ p ∈ T, Real.log p) + 1) ≤ 1 := fun T hT => by
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    refine factor_mem _ (Finset.sum_nonneg fun p hp => Real.log_nonneg ?_)
    exact_mod_cast (J.2.2 p (hT.1 hp)).one_lt.le
  rw [← Finset.prod_sdiff hsub]
  exact mul_le_of_le_one_left (Finset.prod_nonneg fun T hT => (hf T (hsub hT)).1)
    (Finset.prod_le_one (fun T hT => (hf T (Finset.mem_sdiff.1 hT).1).1)
      fun T hT => (hf T (Finset.mem_sdiff.1 hT).1).2)

/-- **§7**: along the first primes the all-subset product tends to `0`, so `γ_{I_r} → 1`. -/
theorem tendsto_subsetProduct_firstPrimes :
    Tendsto (fun r : ℕ => subsetProduct (PrimeSet.firstPrimes (r + 1) r.succ_pos)) atTop
      (𝓝 0) := by
  have hlim : Tendsto (fun r : ℕ => 4 * (((r + 1 : ℕ) : ℝ) ^ 2 / 2 ^ (r + 1))) atTop (𝓝 0) := by
    have := ((tendsto_pow_const_div_const_pow_of_one_lt 2 (one_lt_two : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)).const_mul 4
    rwa [mul_zero] at this
  refine squeeze_zero (fun r => ?_) (fun r => ?_) hlim
  · exact Finset.prod_nonneg fun S _ => (factor_mem _ (Finset.sum_nonneg fun i _ =>
      ((PrimeSet.firstPrimes (r + 1) r.succ_pos).grades_pos i).le)).1
  set I := PrimeSet.firstPrimes (r + 1) r.succ_pos
  set A := ∑ i, I.grades i
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => (I.grades_pos i).le
  have hcardI : I.1.card = r + 1 := PrimeSet.card_firstPrimes (r + 1) r.succ_pos
  have hN : ((subsets I.1.card).card : ℝ) = 2 ^ (r + 1) - 1 := by
    rw [card_subsets, hcardI, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]
    norm_num
  -- every factor is at most `A/(A+1)`
  have hfac : ∀ S ∈ subsets I.1.card,
      (∑ i ∈ S, I.grades i) / ((∑ i ∈ S, I.grades i) + 1) ≤ A / (A + 1) := fun S _ => by
    have hS : ∑ i ∈ S, I.grades i ≤ A :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        fun i _ _ => (I.grades_pos i).le
    have h0 : 0 ≤ ∑ i ∈ S, I.grades i := Finset.sum_nonneg fun i _ => (I.grades_pos i).le
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h1 : subsetProduct I ≤ (A / (A + 1)) ^ (subsets I.1.card).card := by
    rw [subsetProduct, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun S _ => (factor_mem _ (Finset.sum_nonneg fun i _ =>
      (I.grades_pos i).le)).1) hfac
  set N := (subsets I.1.card).card
  have hNpos : (0 : ℝ) < N := by
    rw [hN]
    have : (2 : ℝ) ≤ 2 ^ (r + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  -- `(A/(A+1))^N ≤ exp(-N/(A+1)) ≤ (A+1)/N`
  have h2 : (A / (A + 1)) ^ N ≤ Real.exp (-(N / (A + 1))) := by
    have hle : A / (A + 1) ≤ Real.exp (-(1 / (A + 1))) := by
      have := Real.one_sub_le_exp_neg (1 / (A + 1))
      rwa [show 1 - 1 / (A + 1) = A / (A + 1) by field_simp; ring] at this
    calc (A / (A + 1)) ^ N ≤ Real.exp (-(1 / (A + 1))) ^ N :=
          pow_le_pow_left₀ (factor_mem _ hA0).1 hle N
      _ = Real.exp (-(N / (A + 1))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have h3 : Real.exp (-(N / (A + 1))) ≤ (A + 1) / N := by
    have hy : 0 < (N : ℝ) / (A + 1) := by positivity
    have := Real.add_one_le_exp ((N : ℝ) / (A + 1))
    rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) hNpos]
    have hNA : (N : ℝ) = N / (A + 1) * (A + 1) := by field_simp
    nlinarith
  -- `(A+1)/N ≤ 4 (r+1)²/2^{r+1}`
  have hAle : A ≤ (((r + 1 : ℕ) : ℝ) * (((r + 1 : ℕ) : ℝ) + 1) / 2) * Real.log 2 :=
    PrimeSet.sum_grades_firstPrimes_le (r + 1) r.succ_pos
  have hlog : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hA1 : A + 1 ≤ 2 * ((r + 1 : ℕ) : ℝ) ^ 2 := by
    have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 r
    have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
    nlinarith
  have hNge : (2 : ℝ) ^ (r + 1) / 2 ≤ N := by
    rw [hN]
    have : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  calc subsetProduct I ≤ (A + 1) / N := h1.trans (h2.trans h3)
    _ ≤ 2 * ((r + 1 : ℕ) : ℝ) ^ 2 / (2 ^ (r + 1) / 2) :=
        div_le_div₀ (by positivity) hA1 (by positivity) hNge
    _ = 4 * (((r + 1 : ℕ) : ℝ) ^ 2 / 2 ^ (r + 1)) := by ring

theorem tendsto_subsetGap_firstPrimes :
    Tendsto (fun r : ℕ => 1 - subsetProduct (PrimeSet.firstPrimes (r + 1) r.succ_pos)) atTop
      (𝓝 1) := by
  simpa using tendsto_subsetProduct_firstPrimes.const_sub 1

end GaloisForLFunctions.HTGeometry.LaplaceTomography
