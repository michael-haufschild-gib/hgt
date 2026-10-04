import GaloisForLFunctions.HTGeometry.WeightedOrbitInductionSchatten
import GaloisForLFunctions.HTGeometry.FourthPowerCycleEscape

/-!
# Shift transgression, bounded primitives and character formation

On `ℓ²(ℕ; H)` let `S` be the unilateral right shift, `(S x)₀ = 0`, `(S x)ₙ₊₁ = xₙ`; its adjoint is
the left shift.  The **shift transgression** of `B : ℓ²(ℕ; H) → ℓ²(ℕ; K)` is
`δ(B) = B - S_K B S_H*`.  For a bounded amplitude sequence `a` and a block `D : H → K` let
`A_a = diag(aₙ D)`.

* **Bounded primitives.**  Every primitive `δ(B) = A_a` has diagonal history
  `B_nn = sₙ D`, `sₙ = ∑_{k ≤ n} a_k`; hence a bounded primitive exists exactly when the partial
  sums are bounded, and the least primitive norm is `‖D‖ sup |sₙ|`, attained by `diag(sₙ D)`
  (`isLeast_norm_shiftPrimitive`, `exists_shiftPrimitive_iff`).
* **Positive accumulation.**  For nonnegative amplitudes a bounded primitive exists exactly when
  `∑ aₙ < ∞`; the homogeneous law `aₙ = 1` has history `B_nn = (n+1) D`; the horizon-`N` law
  costs exactly `(N+1) ‖D‖`.
* **Characters.**  For `aₙ = zⁿ`, `|z| = 1`: a nontrivial character has a bounded primitive of
  least norm `‖D‖ sup |(1 - zⁿ⁺¹)/(1 - z)| ≤ 2‖D‖/|1 - z|`; the neutral character has none;
  reflection `z ↦ z̄` preserves the least norm.  A family of nontrivial characters has uniformly
  bounded primitives exactly when `inf |1 - z_j| > 0`.
* **Positive resonance.**  `A_z* A_w = diag((z̄ w)ⁿ D*D)`, which has a bounded primitive exactly
  when `z ≠ w`; every self-pair `A_z* A_z = diag(D*D)` is neutral and has none.
-/

open Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### The unilateral shift on `ℓ²(ℕ; H)` -/

section Shift

variable {H : Type*} [NormedAddCommGroup H]

/-- The right shift of a sequence. -/
def shiftRightSeq (x : ℕ → H) : ℕ → H
  | 0 => 0
  | n + 1 => x n

@[simp] theorem shiftRightSeq_zero (x : ℕ → H) : shiftRightSeq x 0 = 0 := rfl

@[simp] theorem shiftRightSeq_succ (x : ℕ → H) (n : ℕ) : shiftRightSeq x (n + 1) = x n := rfl

theorem hasSum_norm_sq_lp (x : lp (fun _ : ℕ => H) 2) :
    HasSum (fun n => ‖(x : ℕ → H) n‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem hasSum_norm_sq_shiftRightSeq (x : lp (fun _ : ℕ => H) 2) :
    HasSum (fun n => ‖shiftRightSeq (x : ℕ → H) n‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (hasSum_nat_add_iff (f := fun n => ‖shiftRightSeq (x : ℕ → H) n‖ ^ 2) 1).mp
    (hasSum_norm_sq_lp x)
  simpa using h

theorem hasSum_norm_sq_shiftLeft (x : lp (fun _ : ℕ => H) 2) :
    HasSum (fun n => ‖(x : ℕ → H) (n + 1)‖ ^ 2) (‖x‖ ^ 2 - ‖(x : ℕ → H) 0‖ ^ 2) := by
  have h := (hasSum_nat_add_iff' (f := fun n => ‖(x : ℕ → H) n‖ ^ 2) 1).mpr
    (hasSum_norm_sq_lp x)
  simpa using h

theorem memℓp_of_hasSum_norm_sq {f : ℕ → H} {c : ℝ} (h : HasSum (fun n => ‖f n‖ ^ 2) c) :
    Memℓp f 2 :=
  memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.summable)

variable [NormedSpace ℂ H]

/-- The unilateral right shift, an isometry of `ℓ²(ℕ; H)`. -/
def lpRightShift : lp (fun _ : ℕ => H) 2 →ₗᵢ[ℂ] lp (fun _ : ℕ => H) 2 where
  toFun x := ⟨shiftRightSeq (x : ℕ → H), memℓp_of_hasSum_norm_sq (hasSum_norm_sq_shiftRightSeq x)⟩
  map_add' x y := by
    apply lp.ext
    funext n
    cases n <;> simp
  map_smul' c x := by
    apply lp.ext
    funext n
    cases n <;> simp
  norm_map' x := by
    have h1 := hasSum_norm_sq_lp (⟨shiftRightSeq (x : ℕ → H),
      memℓp_of_hasSum_norm_sq (hasSum_norm_sq_shiftRightSeq x)⟩ : lp (fun _ : ℕ => H) 2)
    have h2 := (hasSum_norm_sq_shiftRightSeq x).unique h1
    exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2).symm

@[simp] theorem lpRightShift_apply_zero (x : lp (fun _ : ℕ => H) 2) :
    (lpRightShift x : ℕ → H) 0 = 0 := rfl

@[simp] theorem lpRightShift_apply_succ (x : lp (fun _ : ℕ => H) 2) (n : ℕ) :
    (lpRightShift x : ℕ → H) (n + 1) = (x : ℕ → H) n := rfl

/-- The left shift `(L x)ₙ = xₙ₊₁`, as a linear map. -/
def lpLeftShiftLM : lp (fun _ : ℕ => H) 2 →ₗ[ℂ] lp (fun _ : ℕ => H) 2 where
  toFun x := ⟨fun n => (x : ℕ → H) (n + 1), memℓp_of_hasSum_norm_sq (hasSum_norm_sq_shiftLeft x)⟩
  map_add' x y := by
    apply lp.ext
    funext n
    simp
  map_smul' c x := by
    apply lp.ext
    funext n
    simp

theorem norm_lpLeftShiftLM_le (x : lp (fun _ : ℕ => H) 2) : ‖lpLeftShiftLM x‖ ≤ 1 * ‖x‖ := by
  have h1 := hasSum_norm_sq_lp (lpLeftShiftLM x)
  have h2 := (hasSum_norm_sq_shiftLeft x).unique h1
  have hsq : ‖lpLeftShiftLM x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← h2]
    linarith [sq_nonneg ‖(x : ℕ → H) 0‖]
  rw [one_mul]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- The unilateral left shift. -/
def lpLeftShift : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => H) 2 :=
  LinearMap.mkContinuous lpLeftShiftLM 1 norm_lpLeftShiftLM_le

@[simp] theorem lpLeftShift_apply (x : lp (fun _ : ℕ => H) 2) (n : ℕ) :
    (lpLeftShift x : ℕ → H) n = (x : ℕ → H) (n + 1) := rfl

theorem lpLeftShift_single_succ (n : ℕ) (v : H) :
    lpLeftShift (lp.single 2 (n + 1) v : lp (fun _ : ℕ => H) 2) = lp.single 2 n v := by
  apply lp.ext
  funext m
  simp only [lpLeftShift_apply, lp.coeFn_single, Pi.single_apply, add_left_inj]

theorem lpLeftShift_single_zero (v : H) :
    lpLeftShift (lp.single 2 0 v : lp (fun _ : ℕ => H) 2) = 0 := by
  apply lp.ext
  funext m
  simp only [lpLeftShift_apply, lp.coeFn_single, Pi.single_apply, Nat.add_one_ne_zero,
    if_false, lp.coeFn_zero, Pi.zero_apply]

end Shift

section ShiftAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The adjoint of the right shift is the left shift. -/
theorem adjoint_lpRightShift :
    ContinuousLinearMap.adjoint (lpRightShift (H := H)).toContinuousLinearMap = lpLeftShift := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_).symm
  have h1 := lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : ℕ => H) (lpLeftShift x) y
  have h2 := lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : ℕ => H) x
    ((lpRightShift (H := H)).toContinuousLinearMap y)
  have h3 := (hasSum_nat_add_iff' (f := fun n => ⟪(x : ℕ → H) n,
    ((lpRightShift (H := H)).toContinuousLinearMap y : ℕ → H) n⟫_ℂ) 1).mpr h2
  simp only [Finset.range_one, Finset.sum_singleton, LinearIsometry.coe_toContinuousLinearMap,
    lpRightShift_apply_zero, inner_zero_right, sub_zero, lpRightShift_apply_succ] at h3
  exact h1.unique (h3.congr_fun fun n => rfl)

end ShiftAdjoint

/-! ### Diagonal compressions and the shift transgression -/

section Transgression

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The shift transgression `δ(B) = B - S_K B S_H*`. -/
def shiftTransgression (B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2) :
    lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2 :=
  B - (lpRightShift (H := K)).toContinuousLinearMap ∘L B ∘L
    ContinuousLinearMap.adjoint (lpRightShift (H := H)).toContinuousLinearMap

theorem shiftTransgression_apply (B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2)
    (x : lp (fun _ : ℕ => H) 2) :
    shiftTransgression B x = B x - lpRightShift (B (lpLeftShift x)) := by
  rw [shiftTransgression, adjoint_lpRightShift]
  rfl

omit [CompleteSpace H] in
/-- The `n`-th diagonal compression `B_nn = Pₙ B Iₙ`. -/
def diagCompression (B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2) (n : ℕ) :
    H →L[ℂ] K :=
  lpEvalCLM (G := fun _ : ℕ => K) n ∘L B ∘L lpSingleCLM (G := fun _ : ℕ => H) n

omit [CompleteSpace H] in
theorem diagCompression_apply (B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2) (n : ℕ)
    (v : H) : diagCompression B n v = (B (lp.single 2 n v) : ℕ → K) n := rfl

omit [CompleteSpace H] in
theorem diagCompression_sub (B C : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2) (n : ℕ) :
    diagCompression (B - C) n = diagCompression B n - diagCompression C n := by
  ext v
  simp [diagCompression_apply]

omit [CompleteSpace H] in
/-- Every diagonal compression has norm at most `‖B‖`. -/
theorem norm_diagCompression_le (B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2)
    (n : ℕ) : ‖diagCompression B n‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun v => ?_
  rw [diagCompression_apply]
  calc ‖(B (lp.single 2 n v) : ℕ → K) n‖ ≤ ‖B (lp.single 2 n v)‖ :=
        lp.norm_apply_le_norm (by norm_num) _ n
    _ ≤ ‖B‖ * ‖(lp.single 2 n v : lp (fun _ : ℕ => H) 2)‖ := B.le_opNorm _
    _ = ‖B‖ * ‖v‖ := by rw [lp.norm_single (by norm_num)]

/-- The shifted-back term contributes nothing to the first compression. -/
theorem diagCompression_shiftTransgression_zero
    (B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2) :
    diagCompression (shiftTransgression B) 0 = diagCompression B 0 := by
  ext v
  rw [diagCompression_apply, shiftTransgression_apply, lp.coeFn_sub, Pi.sub_apply,
    lpRightShift_apply_zero, sub_zero]
  rfl

/-- **The transgression recursion** `δ(B)_{n+1,n+1} = B_{n+1,n+1} - B_nn`. -/
theorem diagCompression_shiftTransgression_succ
    (B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2) (n : ℕ) :
    diagCompression (shiftTransgression B) (n + 1) =
      diagCompression B (n + 1) - diagCompression B n := by
  ext v
  rw [diagCompression_apply, shiftTransgression_apply, lp.coeFn_sub, Pi.sub_apply,
    lpRightShift_apply_succ, lpLeftShift_single_succ]
  rfl

/-- The diagonal formed operator `A_a = diag(aₙ D)`. -/
def diagFormed (a : ℕ → ℂ) (D : H →L[ℂ] K) (hbdd : BddAbove (Set.range fun n => ‖a n‖)) :
    lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2 :=
  weightedInduction a D (fun _ => LinearIsometryEquiv.refl ℂ H)
    (fun _ => LinearIsometryEquiv.refl ℂ K) hbdd

omit [CompleteSpace H] in
@[simp] theorem diagFormed_apply (a : ℕ → ℂ) (D : H →L[ℂ] K)
    (hbdd : BddAbove (Set.range fun n => ‖a n‖)) (x : lp (fun _ : ℕ => H) 2) (n : ℕ) :
    (diagFormed a D hbdd x : ℕ → K) n = a n • D ((x : ℕ → H) n) := rfl

omit [CompleteSpace H] in
theorem norm_diagFormed (a : ℕ → ℂ) (D : H →L[ℂ] K)
    (hbdd : BddAbove (Set.range fun n => ‖a n‖)) :
    ‖diagFormed a D hbdd‖ = ampSup a * ‖D‖ :=
  norm_weightedInduction a D _ _ hbdd

omit [CompleteSpace H] in
theorem diagCompression_diagFormed (a : ℕ → ℂ) (D : H →L[ℂ] K)
    (hbdd : BddAbove (Set.range fun n => ‖a n‖)) (n : ℕ) :
    diagCompression (diagFormed a D hbdd) n = a n • D := by
  ext v
  rw [diagCompression_apply, diagFormed_apply, lp.coeFn_single, Pi.single_eq_same]
  rfl

/-- The partial sums `sₙ = ∑_{k ≤ n} a_k`. -/
def ampPartialSum (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.range (n + 1), a k

theorem ampPartialSum_zero (a : ℕ → ℂ) : ampPartialSum a 0 = a 0 := by
  simp [ampPartialSum]

theorem ampPartialSum_succ (a : ℕ → ℂ) (n : ℕ) :
    ampPartialSum a (n + 1) = ampPartialSum a n + a (n + 1) :=
  Finset.sum_range_succ a (n + 1)

/-- **The diagonal history of a primitive.**  If `δ(B) = A_a` then `B_nn = sₙ D`. -/
theorem diagCompression_of_shiftPrimitive {a : ℕ → ℂ} {D : H →L[ℂ] K}
    {hbdd : BddAbove (Set.range fun n => ‖a n‖)}
    {B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2}
    (hB : shiftTransgression B = diagFormed a D hbdd) (n : ℕ) :
    diagCompression B n = ampPartialSum a n • D := by
  induction n with
  | zero =>
      rw [← diagCompression_shiftTransgression_zero, hB, diagCompression_diagFormed,
        ampPartialSum_zero]
  | succ n ih =>
      have h := diagCompression_shiftTransgression_succ B n
      rw [hB, diagCompression_diagFormed, ih] at h
      rw [ampPartialSum_succ, add_smul, h]
      abel

/-- Every primitive has norm at least `|sₙ| ‖D‖` for every `n`. -/
theorem norm_partialSum_mul_le_of_shiftPrimitive {a : ℕ → ℂ} {D : H →L[ℂ] K}
    {hbdd : BddAbove (Set.range fun n => ‖a n‖)}
    {B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2}
    (hB : shiftTransgression B = diagFormed a D hbdd) (n : ℕ) :
    ‖ampPartialSum a n‖ * ‖D‖ ≤ ‖B‖ := by
  rw [← norm_smul, ← diagCompression_of_shiftPrimitive hB n]
  exact norm_diagCompression_le B n

theorem ampSup_mul_le_of_shiftPrimitive {a : ℕ → ℂ} {D : H →L[ℂ] K}
    {hbdd : BddAbove (Set.range fun n => ‖a n‖)}
    {B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2}
    (hB : shiftTransgression B = diagFormed a D hbdd) :
    ampSup (ampPartialSum a) * ‖D‖ ≤ ‖B‖ := by
  rcases (norm_nonneg D).eq_or_lt with hD | hD
  · rw [← hD, mul_zero]
    exact norm_nonneg B
  · rw [← le_div_iff₀ hD]
    refine ampSup_le fun n => ?_
    rw [le_div_iff₀ hD]
    exact norm_partialSum_mul_le_of_shiftPrimitive hB n

/-- The diagonal primitive `diag(sₙ D)` solves `δ(B) = A_a`. -/
theorem shiftTransgression_diagFormed_ampPartialSum (a : ℕ → ℂ) (D : H →L[ℂ] K)
    (hbdd : BddAbove (Set.range fun n => ‖a n‖))
    (hs : BddAbove (Set.range fun n => ‖ampPartialSum a n‖)) :
    shiftTransgression (diagFormed (ampPartialSum a) D hs) = diagFormed a D hbdd := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [shiftTransgression_apply]
  apply lp.ext
  funext n
  rw [lp.coeFn_sub, Pi.sub_apply]
  cases n with
  | zero =>
      rw [lpRightShift_apply_zero, sub_zero, diagFormed_apply, diagFormed_apply, ampPartialSum_zero]
  | succ n =>
      rw [lpRightShift_apply_succ, diagFormed_apply, diagFormed_apply, diagFormed_apply,
        lpLeftShift_apply, ampPartialSum_succ, add_smul, add_sub_cancel_left]

/-- **Theorem 2.1, `(CTR.1)`.**  With bounded partial sums, the least norm of a primitive of
`A_a` is `‖D‖ sup |sₙ|`, attained by `diag(sₙ D)`. -/
theorem isLeast_norm_shiftPrimitive (a : ℕ → ℂ) (D : H →L[ℂ] K)
    (hbdd : BddAbove (Set.range fun n => ‖a n‖))
    (hs : BddAbove (Set.range fun n => ‖ampPartialSum a n‖)) :
    IsLeast {r | ∃ B, shiftTransgression B = diagFormed a D hbdd ∧ ‖B‖ = r}
      (ampSup (ampPartialSum a) * ‖D‖) := by
  refine ⟨⟨diagFormed (ampPartialSum a) D hs,
    shiftTransgression_diagFormed_ampPartialSum a D hbdd hs,
    norm_diagFormed _ D hs⟩, ?_⟩
  rintro r ⟨B, hB, rfl⟩
  exact ampSup_mul_le_of_shiftPrimitive hB

/-- **Theorem 2.1.**  For a nonzero block, a bounded primitive exists exactly when the partial
sums are bounded. -/
theorem exists_shiftPrimitive_iff (a : ℕ → ℂ) {D : H →L[ℂ] K} (hD : D ≠ 0)
    (hbdd : BddAbove (Set.range fun n => ‖a n‖)) :
    (∃ B, shiftTransgression B = diagFormed a D hbdd) ↔
      BddAbove (Set.range fun n => ‖ampPartialSum a n‖) := by
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨‖B‖ / ‖D‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [le_div_iff₀ hDpos]
    exact norm_partialSum_mul_le_of_shiftPrimitive hB n
  · intro hs
    exact ⟨_, shiftTransgression_diagFormed_ampPartialSum a D hbdd hs⟩

/-! ### Positive accumulation -/

/-- **Corollary 2.2.**  For nonnegative amplitudes a bounded primitive exists exactly when the
amplitude series converges. -/
theorem exists_shiftPrimitive_iff_summable {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) {D : H →L[ℂ] K}
    (hD : D ≠ 0) (hbdd : BddAbove (Set.range fun n => ‖(r n : ℂ)‖)) :
    (∃ B, shiftTransgression B = diagFormed (fun n => (r n : ℂ)) D hbdd) ↔ Summable r := by
  rw [exists_shiftPrimitive_iff _ hD]
  have hnorm : ∀ n, ‖ampPartialSum (fun n => (r n : ℂ)) n‖ = ∑ k ∈ Finset.range (n + 1), r k := by
    intro n
    rw [ampPartialSum, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => hr k)]
  simp_rw [hnorm]
  constructor
  · rintro ⟨M, hM⟩
    refine summable_of_sum_range_le (c := M) hr fun n => ?_
    calc ∑ k ∈ Finset.range n, r k ≤ ∑ k ∈ Finset.range (n + 1), r k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            fun k _ _ => hr k
      _ ≤ M := hM ⟨n, rfl⟩
  · intro hsum
    exact ⟨∑' k, r k, by rintro _ ⟨n, rfl⟩; exact hsum.sum_le_tsum _ fun k _ => hr k⟩

theorem bddAbove_one_amp : BddAbove (Set.range fun _ : ℕ => ‖(1 : ℂ)‖) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; simp⟩

/-- **Corollary 2.2.**  For the homogeneous law `aₙ = 1`, every primitive has diagonal history
`B_nn = (n + 1) D`. -/
theorem diagCompression_of_homogeneous_shiftPrimitive {D : H →L[ℂ] K}
    {B : lp (fun _ : ℕ => H) 2 →L[ℂ] lp (fun _ : ℕ => K) 2}
    (hB : shiftTransgression B = diagFormed (fun _ => 1) D bddAbove_one_amp) (n : ℕ) :
    diagCompression B n = ((n : ℂ) + 1) • D := by
  rw [diagCompression_of_shiftPrimitive hB n]
  simp [ampPartialSum]

/-- **Corollary 2.2.**  The homogeneous law has no bounded primitive. -/
theorem not_exists_homogeneous_shiftPrimitive {D : H →L[ℂ] K} (hD : D ≠ 0) :
    ¬ ∃ B, shiftTransgression B = diagFormed (fun _ => 1) D bddAbove_one_amp := by
  rw [exists_shiftPrimitive_iff _ hD]
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have h := hM ⟨n, rfl⟩
  simp only [ampPartialSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  rw [show ((n + 1 : ℕ) : ℂ) = ((n + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  linarith

/-- The horizon-`N` homogeneous amplitude `1_{n ≤ N}`. -/
def horizonAmp (N : ℕ) : ℕ → ℂ := fun n => if n ≤ N then 1 else 0

theorem bddAbove_horizonAmp (N : ℕ) : BddAbove (Set.range fun n => ‖horizonAmp N n‖) :=
  ⟨1, by
    rintro _ ⟨n, rfl⟩
    show ‖horizonAmp N n‖ ≤ 1
    unfold horizonAmp
    split_ifs <;> simp⟩

theorem ampPartialSum_horizonAmp (N n : ℕ) :
    ampPartialSum (horizonAmp N) n = (min n N : ℕ) + 1 := by
  induction n with
  | zero => simp [ampPartialSum_zero, horizonAmp]
  | succ n ih =>
      rw [ampPartialSum_succ, ih, horizonAmp]
      split_ifs with h
      · rw [Nat.min_eq_left h, Nat.min_eq_left (by omega)]
        push_cast
        ring
      · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega), add_zero]

/-- **Corollary 2.2.**  The horizon-`N` homogeneous primitive costs exactly `(N + 1) ‖D‖`. -/
theorem isLeast_norm_horizon_shiftPrimitive (N : ℕ) (D : H →L[ℂ] K) :
    IsLeast {r | ∃ B, shiftTransgression B = diagFormed (horizonAmp N) D (bddAbove_horizonAmp N) ∧
      ‖B‖ = r} ((N + 1) * ‖D‖) := by
  have hnorm : ∀ n, ‖ampPartialSum (horizonAmp N) n‖ = (min n N : ℕ) + 1 := by
    intro n
    rw [ampPartialSum_horizonAmp, show (((min n N : ℕ) : ℂ) + 1) = (((min n N : ℕ) + 1 : ℝ) : ℂ) by
      rw [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one], Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : BddAbove (Set.range fun n => ‖ampPartialSum (horizonAmp N) n‖) :=
    ⟨N + 1, by
      rintro _ ⟨n, rfl⟩
      dsimp only
      rw [hnorm]
      have : ((min n N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right n N
      linarith⟩
  have hsup : ampSup (ampPartialSum (horizonAmp N)) = N + 1 := by
    refine le_antisymm (ampSup_le fun n => ?_) ?_
    · rw [hnorm]
      have : ((min n N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right n N
      linarith
    · have h := le_ampSup hs N
      rw [hnorm, min_self] at h
      exact h
  have h := isLeast_norm_shiftPrimitive (horizonAmp N) D (bddAbove_horizonAmp N) hs
  rwa [hsup] at h

end Transgression

/-! ### Characters -/

section Character

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The character amplitude `aₙ = zⁿ`. -/
def charAmp (z : ℂ) : ℕ → ℂ := fun n => z ^ n

theorem bddAbove_charAmp {z : ℂ} (hz : ‖z‖ = 1) :
    BddAbove (Set.range fun n => ‖charAmp z n‖) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; simp [charAmp, hz]⟩

/-- **`(CTR.2)`**, nontrivial character. -/
theorem ampPartialSum_charAmp {z : ℂ} (hz1 : z ≠ 1) (n : ℕ) :
    ampPartialSum (charAmp z) n = (1 - z ^ (n + 1)) / (1 - z) := by
  have h1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have h2 : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  rw [ampPartialSum, show (fun k => charAmp z k) = fun k => z ^ k from rfl, geom_sum_eq hz1]
  field_simp
  ring

/-- **`(CTR.2)`**, neutral character. -/
theorem ampPartialSum_charAmp_one (n : ℕ) : ampPartialSum (charAmp 1) n = n + 1 := by
  simp [ampPartialSum, charAmp]

theorem norm_partialSum_charAmp_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (n : ℕ) :
    ‖ampPartialSum (charAmp z) n‖ ≤ 2 / ‖1 - z‖ := by
  have h2 : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  rw [ampPartialSum_charAmp hz1, norm_div]
  refine div_le_div_of_nonneg_right ?_ h2.le
  calc ‖1 - z ^ (n + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ (n + 1)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num

theorem bddAbove_partialSum_charAmp {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    BddAbove (Set.range fun n => ‖ampPartialSum (charAmp z) n‖) :=
  ⟨2 / ‖1 - z‖, by rintro _ ⟨n, rfl⟩; exact norm_partialSum_charAmp_le hz hz1 n⟩

/-- **Theorem 3.1 (1), `(CTR.3)`.**  A nontrivial character has a bounded primitive; the least
primitive norm is `‖D‖ sup |(1 - zⁿ⁺¹)/(1 - z)| ≤ 2‖D‖/|1 - z|`. -/
theorem character_shiftPrimitive {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (D : H →L[ℂ] K) :
    IsLeast {r | ∃ B, shiftTransgression B = diagFormed (charAmp z) D (bddAbove_charAmp hz) ∧
        ‖B‖ = r} (ampSup (ampPartialSum (charAmp z)) * ‖D‖) ∧
      ampSup (ampPartialSum (charAmp z)) = ⨆ n : ℕ, ‖(1 - z ^ (n + 1)) / (1 - z)‖ ∧
      ampSup (ampPartialSum (charAmp z)) * ‖D‖ ≤ 2 * ‖D‖ / ‖1 - z‖ := by
  refine ⟨isLeast_norm_shiftPrimitive _ D _ (bddAbove_partialSum_charAmp hz hz1), ?_, ?_⟩
  · simp only [ampSup, ampPartialSum_charAmp hz1]
  · rw [mul_comm 2, mul_div_assoc, mul_comm (‖D‖)]
    exact mul_le_mul_of_nonneg_right (ampSup_le (norm_partialSum_charAmp_le hz hz1))
      (norm_nonneg D)

/-- **Theorem 3.1 (2).**  The neutral character has no bounded primitive. -/
theorem not_exists_neutral_shiftPrimitive {D : H →L[ℂ] K} (hD : D ≠ 0) :
    ¬ ∃ B, shiftTransgression B = diagFormed (charAmp 1) D (bddAbove_charAmp (by simp)) := by
  have h := not_exists_homogeneous_shiftPrimitive hD
  have heq : diagFormed (charAmp 1) D (bddAbove_charAmp (by simp)) =
      diagFormed (fun _ => 1) D bddAbove_one_amp := by
    refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
    simp [charAmp]
  rwa [heq]

theorem ampPartialSum_charAmp_conj (z : ℂ) (n : ℕ) :
    ampPartialSum (charAmp (conj z)) n = conj (ampPartialSum (charAmp z) n) := by
  simp [ampPartialSum, charAmp, map_sum, map_pow]

/-- **Theorem 3.1 (3).**  Reflection `z ↦ z̄ = z⁻¹` preserves the partial-sum moduli and hence
the least primitive norm. -/
theorem ampSup_partialSum_charAmp_conj (z : ℂ) :
    ampSup (ampPartialSum (charAmp (conj z))) = ampSup (ampPartialSum (charAmp z)) := by
  simp only [ampSup, ampPartialSum_charAmp_conj, Complex.norm_conj]

theorem conj_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  simp

theorem norm_partialSum_charAmp_sub_le {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖ampPartialSum (charAmp z) N - (N + 1)‖ ≤ (N + 1) ^ 2 * ‖z - 1‖ := by
  have h : ampPartialSum (charAmp z) N - (N + 1) = ∑ k ∈ Finset.range (N + 1), (z ^ k - 1) := by
    simp [ampPartialSum, charAmp, Finset.sum_sub_distrib]
  rw [h]
  calc ‖∑ k ∈ Finset.range (N + 1), (z ^ k - 1)‖ ≤ ∑ k ∈ Finset.range (N + 1), ‖z ^ k - 1‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (N + 1), ((N + 1 : ℝ) * ‖z - 1‖) := by
        refine Finset.sum_le_sum fun k hk => ?_
        refine (StonehamParityDrift.norm_pow_sub_one_le hz k).trans ?_
        have : (k : ℝ) ≤ N + 1 := by
          have := Finset.mem_range.mp hk
          exact_mod_cast this.le
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = (N + 1) ^ 2 * ‖z - 1‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **Theorem 3.2.**  A family of nontrivial characters admits primitives with one uniform norm
bound exactly when the characters stay uniformly away from the neutral character. -/
theorem uniform_character_shiftPrimitive_iff {ι : Type*} (z : ι → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    (hz1 : ∀ j, z j ≠ 1) {D : H →L[ℂ] K} (hD : D ≠ 0) :
    (∃ M, ∀ j, ∃ B, shiftTransgression B = diagFormed (charAmp (z j)) D (bddAbove_charAmp (hz j))
        ∧ ‖B‖ ≤ M) ↔ ∃ ε > 0, ∀ j, ε ≤ ‖1 - z j‖ := by
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  constructor
  · rintro ⟨M, hM⟩
    by_contra hgap
    push Not at hgap
    obtain ⟨N, hN⟩ := exists_nat_gt (M / ‖D‖)
    obtain ⟨j, hj⟩ := hgap (1 / (N + 1) ^ 2) (by positivity)
    obtain ⟨B, hB, hBM⟩ := hM j
    have hlow := norm_partialSum_mul_le_of_shiftPrimitive hB N
    have hclose := norm_partialSum_charAmp_sub_le (hz j) N
    rw [norm_sub_rev (z j)] at hclose
    have hsmall : (N + 1 : ℝ) ^ 2 * ‖1 - z j‖ < 1 := by
      have := mul_lt_mul_of_pos_left hj (by positivity : (0 : ℝ) < (N + 1) ^ 2)
      rwa [one_div, mul_inv_cancel₀ (by positivity)] at this
    have hbig : (N : ℝ) < ‖ampPartialSum (charAmp (z j)) N‖ := by
      have h1 : ‖((N : ℂ) + 1)‖ = N + 1 := by
        rw [show ((N : ℂ) + 1) = ((N + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 := norm_sub_norm_le ((N : ℂ) + 1) (ampPartialSum (charAmp (z j)) N)
      rw [h1, norm_sub_rev] at h2
      linarith
    have : M < ‖B‖ := by
      calc M < N * ‖D‖ := by rwa [div_lt_iff₀ hDpos] at hN
        _ ≤ ‖ampPartialSum (charAmp (z j)) N‖ * ‖D‖ :=
            mul_le_mul_of_nonneg_right hbig.le (norm_nonneg D)
        _ ≤ ‖B‖ := hlow
    linarith
  · rintro ⟨ε, hε, hgap⟩
    refine ⟨2 * ‖D‖ / ε, fun j => ?_⟩
    obtain ⟨⟨⟨B, hB, hBn⟩, -⟩, -, -⟩ := character_shiftPrimitive (hz j) (hz1 j) D
    refine ⟨B, hB, ?_⟩
    rw [hBn]
    refine le_trans (character_shiftPrimitive (hz j) (hz1 j) D).2.2 ?_
    exact div_le_div_of_nonneg_left (by positivity) hε (hgap j)

/-! ### Positive resonance -/

omit [CompleteSpace H] in
theorem diagFormed_eq_of_eq {a b : ℕ → ℂ} (hab : a = b) (D : H →L[ℂ] K)
    (ha : BddAbove (Set.range fun n => ‖a n‖)) (hb : BddAbove (Set.range fun n => ‖b n‖)) :
    diagFormed a D ha = diagFormed b D hb := by
  subst hab
  rfl

variable [CompleteSpace K]

/-- **`(CTR.12)`.**  The pairing of two character packets is the ratio-character packet of the
Gram block: `A_z* A_w = diag((z̄ w)ⁿ D*D)`. -/
theorem adjoint_diagFormed_comp_diagFormed {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (D : H →L[ℂ] K) :
    ContinuousLinearMap.adjoint (diagFormed (charAmp z) D (bddAbove_charAmp hz)) ∘L
        diagFormed (charAmp w) D (bddAbove_charAmp hw) =
      diagFormed (charAmp (conj z * w)) (ContinuousLinearMap.adjoint D ∘L D)
        (bddAbove_charAmp (by rw [norm_mul, Complex.norm_conj, hz, hw, one_mul])) := by
  rw [diagFormed, adjoint_weightedInduction]
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun n => ?_)
  show star (z ^ n) • ContinuousLinearMap.adjoint D (w ^ n • D ((x : ℕ → H) n)) =
    (conj z * w) ^ n • (ContinuousLinearMap.adjoint D) (D ((x : ℕ → H) n))
  rw [map_smul, smul_smul, mul_pow, star_pow]
  rfl

theorem conj_mul_eq_one_iff {z w : ℂ} (hz : ‖z‖ = 1) : conj z * w = 1 ↔ z = w := by
  rw [conj_eq_inv_of_norm_eq_one hz]
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  constructor
  · intro h
    have := congrArg (z * ·) h
    simp only [← mul_assoc, mul_inv_cancel₀ hz0, one_mul, mul_one] at this
    exact this.symm
  · rintro rfl
    exact inv_mul_cancel₀ hz0

/-- **Theorem 5.2, `(CTR.12)`.**  The pairing `A_z* A_w` has a bounded shift primitive exactly when
`z ≠ w`. -/
theorem exists_shiftPrimitive_pairing_iff {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    {D : H →L[ℂ] K} (hD : D ≠ 0) :
    (∃ B, shiftTransgression B = ContinuousLinearMap.adjoint
        (diagFormed (charAmp z) D (bddAbove_charAmp hz)) ∘L
        diagFormed (charAmp w) D (bddAbove_charAmp hw)) ↔ z ≠ w := by
  have hzw : ‖conj z * w‖ = 1 := by rw [norm_mul, Complex.norm_conj, hz, hw, one_mul]
  rw [adjoint_diagFormed_comp_diagFormed hz hw]
  constructor
  · rintro hB rfl
    have h1 : conj z * z = 1 := (conj_mul_eq_one_iff hz).mpr rfl
    rw [diagFormed_eq_of_eq (b := charAmp 1) (by rw [h1]) _ _ (bddAbove_charAmp (by simp))] at hB
    exact not_exists_neutral_shiftPrimitive (adjoint_comp_self_ne_zero hD) hB
  · intro hne
    have h1 : conj z * w ≠ 1 := fun h => hne ((conj_mul_eq_one_iff hz).mp h)
    exact (exists_shiftPrimitive_iff _ (adjoint_comp_self_ne_zero hD) _).mpr
      (bddAbove_partialSum_charAmp hzw h1)

/-- **Theorem 5.2, `(CTR.11)`.**  Every self-pair is neutral: `A_z* A_z = diag(D*D)`, which has
no bounded shift primitive, although `A_z` itself has one for `z ≠ 1`. -/
theorem positive_selfPair_neutral {z : ℂ} (hz : ‖z‖ = 1) {D : H →L[ℂ] K} (hD : D ≠ 0) :
    ContinuousLinearMap.adjoint (diagFormed (charAmp z) D (bddAbove_charAmp hz)) ∘L
        diagFormed (charAmp z) D (bddAbove_charAmp hz) =
      diagFormed (fun _ => 1) (ContinuousLinearMap.adjoint D ∘L D) bddAbove_one_amp ∧
      ¬ ∃ B, shiftTransgression B = ContinuousLinearMap.adjoint
        (diagFormed (charAmp z) D (bddAbove_charAmp hz)) ∘L
        diagFormed (charAmp z) D (bddAbove_charAmp hz) := by
  refine ⟨?_, fun h => (exists_shiftPrimitive_pairing_iff hz hz hD).mp h rfl⟩
  have h1 : conj z * z = 1 := (conj_mul_eq_one_iff hz).mpr rfl
  rw [adjoint_diagFormed_comp_diagFormed hz hz]
  exact diagFormed_eq_of_eq (by funext n; simp [charAmp, h1]) _ _ _

/-! ### Positive work of a character packet -/

omit [CompleteSpace H] [CompleteSpace K] in
/-- **`(CTR.18)`.**  The character-tagged response has constant positive density. -/
theorem norm_sq_charResponse {z : ℂ} (hz : ‖z‖ = 1) (D : H →L[ℂ] K) (x : H) (n : ℕ) :
    ‖z ^ n • D x‖ ^ 2 = ‖D x‖ ^ 2 := by
  rw [norm_smul, norm_pow, hz, one_pow, one_mul]

omit [CompleteSpace H] [CompleteSpace K] in
/-- **`(CTR.19)`.**  Finite-horizon positive work grows linearly, `(N + 1) ‖D x‖²`, even when the
signed character packet has a bounded primitive. -/
theorem sum_norm_sq_charResponse {z : ℂ} (hz : ‖z‖ = 1) (D : H →L[ℂ] K) (x : H) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ‖z ^ n • D x‖ ^ 2 = (N + 1) * ‖D x‖ ^ 2 := by
  simp_rw [norm_sq_charResponse hz]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end Character

end GaloisForLFunctions.HTGeometry
