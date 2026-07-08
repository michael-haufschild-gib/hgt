/-
# Fitting vanishing vs one-sided and combined fakeness (standard presentation)

For `A = standardPres m = [[X^m, 1], [0, 1]]` and a defect `Δ = [[a,b],[c,d]]`:

* **Fitting vanishes** ⇔ `X^m ∣ (a − c)` (one congruence);
* **right-fake** (`Δ = A H + X^m K`) ⇔ `X^m ∣ (a−c)` **and** `X^m ∣ (b−d)`;
* **left-fake** (`Δ = H A + X^m K`) ⇔ `X^m ∣ a` **and** `X^m ∣ c`;
* **combined-fake** (`Δ = A Hᵣ + Hₗ A + X^m K`) ⇔ Fitting vanishes.

So Fitting vanishing is strictly weaker than either **one-sided** fakeness, but **equivalent** to
membership in the sum of the left and right fake modules modulo `X^m`.

Witness for the one-sided gap: `Δ₀ = [[1,0],[1,1]]` has Fitting zero, is not left-fake, not
right-fake, yet **is** combined-fake:
`Δ₀ = A·[[0,0],[1,0]] + [[0,0],[0,1]]·A`.

This is elementary presentation algebra (adjugate first variation / Fitting), not a novelty claim about
abstract Fitting ideals. Corrected after external review of the "bilateral" wording.
-/
import GaloisForLFunctions.RHTower.LiftedGluingFaces
import GaloisForLFunctions.RHTower.FittingSeamBoundary

noncomputable section

namespace RHTower

open Matrix Polynomial

/-! ### §0 Predicates: one-sided and combined fakeness -/

/-- Right-factor fake: `Δ = A H + X^m K`. -/
def IsRightFake (m : ℕ) (Δ : Matrix (Fin 2) (Fin 2) ℚ[X]) : Prop :=
  ∃ H K : Matrix (Fin 2) (Fin 2) ℚ[X],
    Δ = standardPres m * H + ((X : ℚ[X]) ^ m) • K

/-- Left-factor fake: `Δ = H A + X^m K`. -/
def IsLeftFake (m : ℕ) (Δ : Matrix (Fin 2) (Fin 2) ℚ[X]) : Prop :=
  ∃ H K : Matrix (Fin 2) (Fin 2) ℚ[X],
    Δ = H * standardPres m + ((X : ℚ[X]) ^ m) • K

/-- Combined (left-plus-right) fake: the standard tangent-module membership. -/
def IsCombinedFake (m : ℕ) (Δ : Matrix (Fin 2) (Fin 2) ℚ[X]) : Prop :=
  ∃ (Hr Hl K : Matrix (Fin 2) (Fin 2) ℚ[X]),
    Δ = standardPres m * Hr + Hl * standardPres m + ((X : ℚ[X]) ^ m) • K

/-- Fitting class vanishes. -/
def FittingZero (m : ℕ) (Δ : Matrix (Fin 2) (Fin 2) ℚ[X]) : Prop :=
  fittingBoundaryClass m (standardPres m) Δ = 0

/-! ### §1 Trace and Fitting for the standard presentation -/

theorem standardPres_adjugate (m : ℕ) :
    (standardPres m).adjugate = !![1, -1; 0, (X : ℚ[X]) ^ m] := by
  simp [standardPres, Matrix.adjugate_fin_two]

theorem standardPres_det' (m : ℕ) : (standardPres m).det = (X : ℚ[X]) ^ m := by
  simp [standardPres, Matrix.det_fin_two]

theorem fittingTrace_standardPres_general (m : ℕ) (a b c d : ℚ[X]) :
    fittingBoundaryTrace (standardPres m) !![a, b; c, d] =
      a - c + (X : ℚ[X]) ^ m * d := by
  unfold fittingBoundaryTrace
  rw [standardPres_adjugate m]
  have h00 : (!![(1 : ℚ[X]), -1; 0, X ^ m] * !![a, b; c, d]) 0 0 = a + (-1) * c := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (!![(1 : ℚ[X]), -1; 0, X ^ m] * !![a, b; c, d]) 1 1 = X ^ m * d := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.trace_fin_two, h00, h11]
  ring

theorem fittingClass_standardPres_eq_zero_iff (m : ℕ) (a b c d : ℚ[X]) :
    fittingBoundaryClass m (standardPres m) !![a, b; c, d] = 0 ↔
      (X : ℚ[X]) ^ m ∣ (a - c) := by
  rw [fittingBoundaryClass, fittingTrace_standardPres_general,
    jetClass, Ideal.Quotient.eq_zero_iff_mem, jetIdeal, Ideal.mem_span_singleton]
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h
    refine ⟨q - d, ?_⟩
    linear_combination hq
  · intro ⟨k, hk⟩
    refine ⟨k + d, ?_⟩
    rw [hk]; ring

theorem FittingZero_iff_dvd_a_sub_c (m : ℕ) (a b c d : ℚ[X]) :
    FittingZero m !![a, b; c, d] ↔ (X : ℚ[X]) ^ m ∣ (a - c) :=
  fittingClass_standardPres_eq_zero_iff m a b c d

/-! ### §2 Matrix multiplications by `A` -/

theorem standardPres_mul_apply (m : ℕ) (h00 h01 h10 h11 : ℚ[X]) :
    standardPres m * !![h00, h01; h10, h11] =
      !![X ^ m * h00 + h10, X ^ m * h01 + h11; h10, h11] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [standardPres, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_standardPres_apply (m : ℕ) (h00 h01 h10 h11 : ℚ[X]) :
    !![h00, h01; h10, h11] * standardPres m =
      !![X ^ m * h00, h00 + h01; X ^ m * h10, h10 + h11] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [standardPres, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-! ### §3 One-sided fakeness ⇒ Fitting zero; one-sided congruences -/

theorem fake_right_factor_two_congruences (m : ℕ)
    (a b c d : ℚ[X])
    (H K : Matrix (Fin 2) (Fin 2) ℚ[X])
    (h : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℚ[X]) =
      standardPres m * H + ((X : ℚ[X]) ^ m) • K) :
    (X : ℚ[X]) ^ m ∣ (a - c) ∧ (X : ℚ[X]) ^ m ∣ (b - d) := by
  have hH :
      standardPres m * H =
        !![X ^ m * H 0 0 + H 1 0, X ^ m * H 0 1 + H 1 1; H 1 0, H 1 1] := by
    have := standardPres_mul_apply m (H 0 0) (H 0 1) (H 1 0) (H 1 1)
    convert this using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hK : ((X : ℚ[X]) ^ m) • K =
      !![X ^ m * K 0 0, X ^ m * K 0 1; X ^ m * K 1 0, X ^ m * K 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  have habcd := h
  rw [hH, hK] at habcd
  have ha : a = X ^ m * H 0 0 + H 1 0 + X ^ m * K 0 0 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ[X] => M 0 0) habcd
  have hb : b = X ^ m * H 0 1 + H 1 1 + X ^ m * K 0 1 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ[X] => M 0 1) habcd
  have hc : c = H 1 0 + X ^ m * K 1 0 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ[X] => M 1 0) habcd
  have hd : d = H 1 1 + X ^ m * K 1 1 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ[X] => M 1 1) habcd
  constructor
  · refine ⟨H 0 0 + K 0 0 - K 1 0, ?_⟩
    rw [ha, hc]; ring
  · refine ⟨H 0 1 + K 0 1 - K 1 1, ?_⟩
    rw [hb, hd]; ring

theorem fake_left_factor_two_congruences (m : ℕ)
    (a b c d : ℚ[X])
    (H K : Matrix (Fin 2) (Fin 2) ℚ[X])
    (h : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℚ[X]) =
      H * standardPres m + ((X : ℚ[X]) ^ m) • K) :
    (X : ℚ[X]) ^ m ∣ a ∧ (X : ℚ[X]) ^ m ∣ c := by
  have hH :
      H * standardPres m =
        !![X ^ m * H 0 0, H 0 0 + H 0 1; X ^ m * H 1 0, H 1 0 + H 1 1] := by
    have := mul_standardPres_apply m (H 0 0) (H 0 1) (H 1 0) (H 1 1)
    convert this using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hK : ((X : ℚ[X]) ^ m) • K =
      !![X ^ m * K 0 0, X ^ m * K 0 1; X ^ m * K 1 0, X ^ m * K 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  have habcd := h
  rw [hH, hK] at habcd
  have ha : a = X ^ m * H 0 0 + X ^ m * K 0 0 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ[X] => M 0 0) habcd
  have hc : c = X ^ m * H 1 0 + X ^ m * K 1 0 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ[X] => M 1 0) habcd
  constructor
  · refine ⟨H 0 0 + K 0 0, ?_⟩
    rw [ha]; ring
  · refine ⟨H 1 0 + K 1 0, ?_⟩
    rw [hc]; ring

theorem X_pow_not_dvd_one {m : ℕ} (hm : 0 < m) : ¬ (X : ℚ[X]) ^ m ∣ (1 : ℚ[X]) := by
  intro h1
  obtain ⟨q, hq⟩ := h1
  have hR : (((X : ℚ[X]) ^ m) * q).coeff 0 = 0 := by
    rw [Polynomial.coeff_X_pow_mul']
    split_ifs with hle
    · omega
    · simp
  have : (1 : ℚ) = 0 := by
    have hco := congrArg (fun p : ℚ[X] => Polynomial.coeff p 0) hq
    simpa [Polynomial.coeff_one, hR] using hco
  exact one_ne_zero this

/-! ### §4 Combined fakeness ⇔ Fitting zero -/

/-- **Constructive half:** if `X^m ∣ (a−c)`, then `Δ` is combined-fake. -/
theorem combinedFake_of_dvd_a_sub_c (m : ℕ) (a b c d : ℚ[X])
    (h : (X : ℚ[X]) ^ m ∣ (a - c)) :
    IsCombinedFake m !![a, b; c, d] := by
  obtain ⟨k, hk⟩ := h
  -- Δ = A·[[0,0],[c,0]] + [[0,b],[0,d]]·A + X^m·[[k,0],[0,0]]
  refine ⟨!![0, 0; c, 0], !![0, b; 0, d], !![k, 0; 0, 0], ?_⟩
  have hR : standardPres m * !![0, 0; c, 0] = !![c, 0; c, 0] := by
    simpa using standardPres_mul_apply m 0 0 c 0
  have hL : !![0, b; 0, d] * standardPres m = !![0, b; 0, d] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [standardPres, Matrix.mul_apply, Fin.sum_univ_two]
  have hK : ((X : ℚ[X]) ^ m) • !![k, 0; 0, 0] = !![X ^ m * k, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  have ha : a = c + X ^ m * k := by
    have := sub_eq_iff_eq_add'.mp hk
    exact this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hR, hL, hK, Matrix.add_apply, ha]

/-- **Converse half:** combined-fake ⇒ Fitting zero (each summand kills Fitting). -/
theorem FittingZero_of_combinedFake (m : ℕ) {Δ : Matrix (Fin 2) (Fin 2) ℚ[X]}
    (h : IsCombinedFake m Δ) : FittingZero m Δ := by
  obtain ⟨Hr, Hl, K, rfl⟩ := h
  unfold FittingZero
  have hR : fittingBoundaryClass m (standardPres m) (standardPres m * Hr) = 0 := by
    have htr := fittingBoundaryTrace_right_factor (R := ℚ) (standardPres m) Hr
    rw [fittingBoundaryClass, htr, standardPres_det']
    exact jetClass_eq_zero_of_X_pow_dvd ℚ m ⟨Hr.trace, by ring⟩
  have hL : fittingBoundaryClass m (standardPres m) (Hl * standardPres m) = 0 := by
    have htr := fittingBoundaryTrace_left_factor (R := ℚ) (standardPres m) Hl
    rw [fittingBoundaryClass, htr, standardPres_det']
    exact jetClass_eq_zero_of_X_pow_dvd ℚ m ⟨Hl.trace, by ring⟩
  have hK : fittingBoundaryClass m (standardPres m) (((X : ℚ[X]) ^ m) • K) = 0 := by
    rw [fittingBoundaryClass, fittingBoundaryTrace_smul]
    -- trace is X^m * (something)
    exact jetClass_eq_zero_of_X_pow_dvd ℚ m
      ⟨((standardPres m).adjugate * K).trace, by ring⟩
  have hadd := fittingBoundaryClass_add (R := ℚ) m (standardPres m)
    (standardPres m * Hr + Hl * standardPres m) (((X : ℚ[X]) ^ m) • K)
  have hadd' := fittingBoundaryClass_add (R := ℚ) m (standardPres m)
    (standardPres m * Hr) (Hl * standardPres m)
  change fittingBoundaryClass m (standardPres m)
      (standardPres m * Hr + Hl * standardPres m + ((X : ℚ[X]) ^ m) • K) = 0
  rw [hadd, hadd', hR, hL, hK]
  abel

/-- **Equivalence:** Fitting vanishing ⇔ combined (left-plus-right) fakeness. -/
theorem FittingZero_iff_combinedFake (m : ℕ) (a b c d : ℚ[X]) :
    FittingZero m !![a, b; c, d] ↔ IsCombinedFake m !![a, b; c, d] := by
  constructor
  · intro h
    exact combinedFake_of_dvd_a_sub_c m a b c d ((FittingZero_iff_dvd_a_sub_c m a b c d).mp h)
  · intro h
    exact FittingZero_of_combinedFake m h

/-! ### §5 One-sided gap witness (not combined-nonfake) -/

/-- Witness that is Fitting-zero / combined-fake, but neither left- nor right-fake alone. -/
def oneSidedGapWitness : Matrix (Fin 2) (Fin 2) ℚ[X] :=
  !![1, 0; 1, 1]

theorem oneSidedGapWitness_fitting_zero (m : ℕ) :
    FittingZero m oneSidedGapWitness := by
  unfold FittingZero oneSidedGapWitness
  rw [fittingClass_standardPres_eq_zero_iff]
  simp

theorem oneSidedGapWitness_combinedFake (m : ℕ) :
    IsCombinedFake m oneSidedGapWitness := by
  -- explicit: A·[[0,0],[1,0]] + [[0,0],[0,1]]·A
  refine ⟨!![0, 0; 1, 0], !![0, 0; 0, 1], 0, ?_⟩
  have hR : standardPres m * !![0, 0; 1, 0] = !![1, 0; 1, 0] := by
    simpa using standardPres_mul_apply m 0 0 1 0
  have hL : !![0, 0; 0, 1] * standardPres m = !![0, 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [standardPres, Matrix.mul_apply, Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [oneSidedGapWitness, hR, hL, smul_zero, Matrix.add_apply]

theorem oneSidedGapWitness_not_right_fake {m : ℕ} (hm : 0 < m) :
    ¬ IsRightFake m oneSidedGapWitness := by
  rintro ⟨H, K, h⟩
  have hcong := fake_right_factor_two_congruences m 1 0 1 1 H K (by
    simpa [oneSidedGapWitness] using h)
  have h1 : (X : ℚ[X]) ^ m ∣ (1 : ℚ[X]) := by
    have : (X : ℚ[X]) ^ m ∣ (0 - 1 : ℚ[X]) := by simpa using hcong.2
    simpa [sub_eq_add_neg, dvd_neg] using this
  exact X_pow_not_dvd_one hm h1

theorem oneSidedGapWitness_not_left_fake {m : ℕ} (hm : 0 < m) :
    ¬ IsLeftFake m oneSidedGapWitness := by
  rintro ⟨H, K, h⟩
  have hcong := fake_left_factor_two_congruences m 1 0 1 1 H K (by
    simpa [oneSidedGapWitness] using h)
  exact X_pow_not_dvd_one hm (by simpa using hcong.1)

/-! ### §6 Capstones (corrected wording) -/

/-- **One-sided gap:** Fitting vanishing does not imply left-fakeness or right-fakeness separately. -/
theorem fitting_zero_not_imp_one_sided_fake {m : ℕ} (hm : 0 < m) :
    ∃ Δ : Matrix (Fin 2) (Fin 2) ℚ[X],
      FittingZero m Δ ∧ ¬ IsLeftFake m Δ ∧ ¬ IsRightFake m Δ ∧ IsCombinedFake m Δ :=
  ⟨oneSidedGapWitness, oneSidedGapWitness_fitting_zero m,
    oneSidedGapWitness_not_left_fake hm, oneSidedGapWitness_not_right_fake hm,
    oneSidedGapWitness_combinedFake m⟩

/-- **Equivalence with combined fakeness** (for general entry matrices). -/
theorem fitting_zero_iff_combined_fake_entries (m : ℕ) (a b c d : ℚ[X]) :
    FittingZero m !![a, b; c, d] ↔ IsCombinedFake m !![a, b; c, d] :=
  FittingZero_iff_combinedFake m a b c d

/-- **Program-facing summary.** Fitting vanishing is strictly weaker than either one-sided fakeness,
and equivalent to combined left-plus-right fakeness modulo `X^m`. -/
theorem fitting_vs_fake_summary {m : ℕ} (hm : 0 < m) :
    (∃ Δ, FittingZero m Δ ∧ ¬ IsLeftFake m Δ ∧ ¬ IsRightFake m Δ ∧ IsCombinedFake m Δ) ∧
    (∀ a b c d : ℚ[X], FittingZero m !![a, b; c, d] ↔ IsCombinedFake m !![a, b; c, d]) :=
  ⟨fitting_zero_not_imp_one_sided_fake hm, fun a b c d => FittingZero_iff_combinedFake m a b c d⟩

-- Compatibility aliases (old names used by drivers/cards during transition)
theorem bilateralWitness_fitting_zero (m : ℕ) :
    FittingZero m oneSidedGapWitness :=
  oneSidedGapWitness_fitting_zero m

theorem bilateralWitness_not_left_fake {m : ℕ} (hm : 0 < m) :
    ¬ IsLeftFake m oneSidedGapWitness :=
  oneSidedGapWitness_not_left_fake hm

theorem bilateralWitness_not_right_fake {m : ℕ} (hm : 0 < m) :
    ¬ IsRightFake m oneSidedGapWitness :=
  oneSidedGapWitness_not_right_fake hm

/-- Deprecated name: not “bilaterally non-fake”; one-sided non-fake + combined-fake. -/
theorem fitting_zero_not_bilaterally_fake {m : ℕ} (hm : 0 < m) :
    ∃ Δ : Matrix (Fin 2) (Fin 2) ℚ[X],
      FittingZero m Δ ∧ ¬ IsLeftFake m Δ ∧ ¬ IsRightFake m Δ :=
  ⟨oneSidedGapWitness, oneSidedGapWitness_fitting_zero m,
    oneSidedGapWitness_not_left_fake hm, oneSidedGapWitness_not_right_fake hm⟩

abbrev bilateralWitness := oneSidedGapWitness

end RHTower
