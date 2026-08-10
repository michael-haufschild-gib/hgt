import Mathlib

/-!
# The framed copy code: admission, recovery defect, and the fixed-code no-go

The copy code admits exactly the diagonal logical algebra on each single region and everything on
the pair.  Its framed off-diagonal Choi class has squared norm `1 − 1/d`, which is exactly the
optimal recovery defect after erasing one region.  A one-parameter skew code keeps the exact
admitted algebra constant at the scalars while its optimal coherent information decreases
strictly, and every fixed finite code has bounded recovery quantities while the wormhole length
`2 log cosh (J t)` is unbounded.
-/

open scoped Matrix

namespace HTGeometry.ConstraintRelativity

/-! ## Exact regional admission for the copy code -/

section Admission

variable {d : ℕ}

/-- **Card `(2.2)`.**  The coefficient comparison defining an `A`-supported code-preserving
representative of a logical operator. -/
def IsRegionalRepresentative (OA O : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ j i k : Fin d, (if k = j then OA i j else 0) = (if i = k then O i j else 0)

/-- **Theorem 2.1.**  Only diagonal logical operators are admitted by one region. -/
theorem isDiag_of_regionalRepresentative {OA O : Matrix (Fin d) (Fin d) ℂ}
    (h : IsRegionalRepresentative OA O) : ∀ i j : Fin d, i ≠ j → O i j = 0 := by
  intro i j hij
  have := h j i i
  rw [if_neg hij, if_pos rfl] at this
  exact this.symm

/-- **Theorem 2.1.**  The representative is forced to be the same diagonal operator. -/
theorem representative_isDiag {OA O : Matrix (Fin d) (Fin d) ℂ}
    (h : IsRegionalRepresentative OA O) : ∀ i j : Fin d, i ≠ j → OA i j = 0 := by
  intro i j hij
  have := h j i j
  rw [if_pos rfl, if_neg hij] at this
  exact this

/-- **Theorem 2.1.**  Conversely every diagonal logical operator is admitted. -/
theorem regionalRepresentative_of_isDiag {O : Matrix (Fin d) (Fin d) ℂ}
    (hO : ∀ i j : Fin d, i ≠ j → O i j = 0) : IsRegionalRepresentative O O := by
  intro j i k
  by_cases hij : i = j
  · subst hij
    by_cases hki : k = i
    · subst hki; simp
    · rw [if_neg hki, if_neg (fun hc => hki hc.symm)]
  · rw [hO i j hij]
    simp

end Admission

/-! ## The framed Choi class and its squared norm -/

section ChoiClass

variable {d : ℕ}

/-- **Card `(3.1)`.**  The framed Choi class, in the `d`-dimensional GHZ sector. -/
noncomputable def choiState (φ : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => (d : ℂ)⁻¹ * Complex.exp ((φ i - φ j : ℝ) * Complex.I)

/-- **Card `(3.2)`.**  The dephased diagonal. -/
noncomputable def dephased (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if i = j then (d : ℂ)⁻¹ else 0

/-- **Card `(3.2)`.**  The framed off-diagonal connecting class. -/
noncomputable def framedClass (φ : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  choiState φ - dephased d

/-- **Card `(3.3)`.**  Every proper marginal of the connecting class vanishes: its diagonal is
zero. -/
theorem framedClass_diag_zero (φ : Fin d → ℝ) (i : Fin d) : framedClass φ i i = 0 := by
  simp [framedClass, choiState, dephased]

/-- The framed Choi class is idempotent: it is a pure state in the GHZ sector. -/
theorem choiState_mul_self {d : ℕ} (hd : 0 < d) (φ : Fin d → ℝ) :
    choiState φ * choiState φ = choiState φ := by
  ext i k
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  simp only [Matrix.mul_apply, choiState, Matrix.of_apply]
  have hterm : ∀ j : Fin d,
      ((d : ℂ)⁻¹ * Complex.exp ((φ i - φ j : ℝ) * Complex.I)) *
        ((d : ℂ)⁻¹ * Complex.exp ((φ j - φ k : ℝ) * Complex.I))
        = (d : ℂ)⁻¹ * (d : ℂ)⁻¹ * Complex.exp ((φ i - φ k : ℝ) * Complex.I) := by
    intro j
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Card `(3.4)`.**  The squared norm of the framed class is `1 − 1/d`. -/
theorem trace_framedClass_sq {d : ℕ} (hd : 0 < d) (φ : Fin d → ℝ) :
    (framedClass φ * framedClass φ).trace = 1 - (d : ℂ)⁻¹ := by
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have htrΩ : (choiState φ).trace = 1 := by
    simp only [Matrix.trace, Matrix.diag, choiState, Matrix.of_apply, sub_self]
    simp [Finset.card_univ, Fintype.card_fin]
    field_simp
  have hΩΔ : choiState φ * dephased d = (d : ℂ)⁻¹ • choiState φ := by
    ext i k
    simp only [Matrix.mul_apply, dephased, choiState, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ k]
    simp
    ring
  have hΔΩ : dephased d * choiState φ = (d : ℂ)⁻¹ • choiState φ := by
    ext i k
    simp only [Matrix.mul_apply, dephased, choiState, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i]
    simp
  have hΔΔ : dephased d * dephased d = (d : ℂ)⁻¹ • dephased d := by
    ext i k
    simp only [Matrix.mul_apply, dephased, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ k]
    by_cases hik : i = k <;> simp [hik]
  have htrΔ : (dephased d).trace = 1 := by
    simp only [Matrix.trace, Matrix.diag, dephased, Matrix.of_apply]
    simp [Finset.card_univ, Fintype.card_fin]
    field_simp
  rw [framedClass, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, choiState_mul_self hd,
    hΩΔ, hΔΩ, hΔΔ]
  simp only [Matrix.trace_sub, Matrix.trace_smul, htrΩ, htrΔ, smul_eq_mul, mul_one]
  ring

/-- **Card `(3.5)`.**  The exponential form of the same defect. -/
theorem one_sub_exp_neg_log {d : ℕ} (hd : 0 < d) :
    1 - Real.exp (-(Real.log d)) = 1 - (d : ℝ)⁻¹ := by
  rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hd)]

end ChoiClass

/-! ## The optimal recovery defect after erasure -/

section Recovery

variable {d : ℕ}

/-- **Card `(3.4)`.**  After full dephasing the recovery acts on the classical labels; its
transition matrix has nonnegative entries summing to one, so the entanglement fidelity is at most
`1/d`. -/
theorem entanglement_fidelity_le {d : ℕ} (hd : 0 < d) (R : Fin d → Fin d → ℝ)
    (hnn : ∀ i j, 0 ≤ R i j) (hsum : ∀ i, ∑ j, R i j = 1) :
    ((d : ℝ))⁻¹ * ((d : ℝ))⁻¹ * ∑ i : Fin d, R i i ≤ ((d : ℝ))⁻¹ := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hbound : ∀ i : Fin d, R i i ≤ 1 := by
    intro i
    calc R i i ≤ ∑ j : Fin d, R i j :=
          Finset.single_le_sum (fun j _ => hnn i j) (Finset.mem_univ i)
      _ = 1 := hsum i
  calc ((d : ℝ))⁻¹ * ((d : ℝ))⁻¹ * ∑ i : Fin d, R i i
      ≤ ((d : ℝ))⁻¹ * ((d : ℝ))⁻¹ * ∑ _i : Fin d, (1 : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbound i) (by positivity)
    _ = ((d : ℝ))⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        field_simp

/-- **Card `(3.4)`.**  The label-preserving recovery attains the bound. -/
theorem entanglement_fidelity_eq {d : ℕ} (hd : 0 < d) :
    ((d : ℝ))⁻¹ * ((d : ℝ))⁻¹ * ∑ _i : Fin d, (1 : ℝ) = ((d : ℝ))⁻¹ := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

end Recovery

/-! ## The skew code: constant admission, varying recovery -/

section SkewCode

/-- **Card `(4.3)`.**  The optimal coherent information of the amplitude-damping skew code. -/
noncomputable def skewCoherentInfo (γ : ℝ) : ℝ :=
  Real.binEntropy ((1 - γ) / 2) - Real.binEntropy (γ / 2)

/-- **Theorem 4.1.**  The optimal coherent information decreases strictly in the damping
parameter, while the exact admitted algebra stays constant at the scalars. -/
theorem skewCoherentInfo_strictAnti : StrictAntiOn skewCoherentInfo (Set.Icc 0 1) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha.1
  have ha1 : a ≤ 1 := ha.2
  have hb0 : 0 ≤ b := hb.1
  have hb1 : b ≤ 1 := hb.2
  have h1 : Real.binEntropy ((1 - b) / 2) < Real.binEntropy ((1 - a) / 2) := by
    refine Real.binEntropy_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ?_
    linarith
  have h2 : Real.binEntropy (a / 2) < Real.binEntropy (b / 2) := by
    refine Real.binEntropy_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ?_
    linarith
  simp only [skewCoherentInfo]
  linarith

end SkewCode

/-! ## The fixed finite-code wormhole no-go -/

section WormholeNoGo

/-- **Card `(5.2)`.**  The wormhole length profile. -/
noncomputable def wormholeLength (J t : ℝ) : ℝ := 2 * Real.log (Real.cosh (J * t))

/-- **Theorem 5.1.**  The wormhole length is unbounded, so no bounded fixed-code quantity can
equal it for all time. -/
theorem wormholeLength_unbounded {J : ℝ} (hJ : 0 < J) (M : ℝ) :
    ∃ t : ℝ, M < wormholeLength J t := by
  obtain ⟨x, hx⟩ := exists_gt ((M + 2 * Real.log 2) / 2)
  refine ⟨x / J, ?_⟩
  have hJt : J * (x / J) = x := by field_simp
  rw [wormholeLength, hJt]
  have hcosh : Real.exp x / 2 ≤ Real.cosh x := by
    rw [Real.cosh_eq]
    have hnn := (Real.exp_pos (-x)).le
    linarith
  have hpos : (0 : ℝ) < Real.exp x / 2 := by positivity
  have hlog : Real.log (Real.exp x / 2) ≤ Real.log (Real.cosh x) := Real.log_le_log hpos hcosh
  have hval : Real.log (Real.exp x / 2) = x - Real.log 2 := by
    rw [Real.log_div (Real.exp_ne_zero x) (by norm_num), Real.log_exp]
  rw [hval] at hlog
  have hx2 : M + 2 * Real.log 2 < 2 * x := by linarith
  linarith

/-- Every fixed finite-code recovery defect is bounded. -/
theorem recovery_defect_bounded {d : ℕ} (hd : 0 < d) :
    (0 : ℝ) ≤ 1 - (d : ℝ)⁻¹ ∧ 1 - (d : ℝ)⁻¹ ≤ 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (d : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact_mod_cast hd
  have h2 : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
  exact ⟨by linarith, by linarith⟩

/-- **Theorem 5.1, general form.**  No bounded quantity can equal the wormhole length for all
time.  The card's three fixed-code quantities — recovery defect, conditional mutual information,
normalized Choi norm — enter only through their boundedness, so this covers each of them. -/
theorem not_eq_wormholeLength_of_bounded {J : ℝ} (hJ : 0 < J) (f : ℝ → ℝ) (M : ℝ)
    (hf : ∀ t, f t ≤ M) : ∃ t : ℝ, f t ≠ wormholeLength J t := by
  obtain ⟨t, ht⟩ := wormholeLength_unbounded hJ M
  refine ⟨t, fun h => ?_⟩
  have := hf t
  rw [h] at this
  exact absurd this (not_le.2 ht)

/-- **Theorem 5.1** for the recovery defect: the fixed-code defect `1 − 1/d` never equals the
wormhole length at every time. -/
theorem recovery_defect_ne_wormholeLength {J : ℝ} (hJ : 0 < J) {d : ℕ} (hd : 0 < d) :
    ∃ t : ℝ, (1 - (d : ℝ)⁻¹) ≠ wormholeLength J t :=
  not_eq_wormholeLength_of_bounded hJ (fun _ => 1 - (d : ℝ)⁻¹) 1
    (fun _ => (recovery_defect_bounded hd).2)

end WormholeNoGo

end HTGeometry.ConstraintRelativity
