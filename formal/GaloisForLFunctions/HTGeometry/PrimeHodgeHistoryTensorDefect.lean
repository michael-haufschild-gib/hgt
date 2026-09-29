import GaloisForLFunctions.HTGeometry.HistoryTensorOperators
import GaloisForLFunctions.HTGeometry.CubicWallHodgeBetaFlux
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryFirstExitTransgression

/-!
# The prime–Hodge history defect as a history tensor

With the history flux `w_n = m_n - m_{n+1}` and the history operator `Φ e_n = w_n e_n`, the
prime–Hodge history defect is the history tensor

`T(t) = Φ ⊗ T_form(t)` on `ℓ²(ℕ; ℓ²(Primes)) = ℓ²(ℕ) ⊗ ℓ²(Primes)`,

canonically unitarily equivalent to the joint kernel operator on `ℓ²(ℕ × Primes)`.

* **(A)** `T(t)` is self-adjoint, `sign(t) T(t) ≥ 0`, Schatten-one with `tr T(t) = sign t`,
  `‖T(t)‖₁ = 1`, odd in `t`, with matrix `1_{n=k} w_n T_form(t)(p, q)` nonzero on every grade.
* **(B)** the history tails `Q_n` recover the jets: `tr((Q_n ⊗ 1) T(t)) = m_n`, and for the
  comoving wall `𝖠 = Φ ⊗ A`, `tr((Q_n ⊗ 1) 𝖠) = ‖adⁿ_X(A)‖²/((2n)! ‖A‖²)`, with adjacent fluxes
  `w_n` summing to one.
* **(C)** `Φ` is the only nonnegative diagonal with these tails.
* **(D)** `‖𝖠‖ ≤ (2/3)(4/√35) < 1`.
* **(E)** `T(t) → 0` strongly as `t → 0` with `‖T(t)‖₁ = 1`, while the comoving chart
  `1 ⊗ U_d` carries `T(±d)` to `±Φ ⊗ A_d → ±Φ ⊗ A_0` in trace norm.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance isProbabilityMeasure_expMeasure_one_history : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

local instance factTwoNeTopHistory : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## The history flux -/

theorem historyFlux_nonneg (n : ℕ) : 0 ≤ PrimeHodgeHistory.w n := (PrimeHodgeHistory.w_pos n).le

theorem historyFlux_le_one (n : ℕ) : PrimeHodgeHistory.w n ≤ 1 :=
  (PrimeHodgeHistory.w_le_two_thirds n).trans (by norm_num)

theorem historyFlux_norm_le (n : ℕ) : ‖((PrimeHodgeHistory.w n : ℝ) : ℂ)‖ ≤ 1 :=
  norm_ofReal_weight_le_one historyFlux_nonneg historyFlux_le_one n

/-- The flux tensor `Φ ⊗ B`. -/
abbrev fluxTensor {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (B : E →L[ℂ] F) :
    HistoryL2 E →L[ℂ] HistoryL2 F :=
  historyMap (fun n => ((PrimeHodgeHistory.w n : ℝ) : ℂ)) historyFlux_norm_le B

theorem homotopyEnergy_eq_m (n : ℕ) : homotopyEnergy n = PrimeHodgeHistory.m n := by
  rw [homotopyEnergy_eq, PrimeHodgeHistory.m]
  push_cast
  ring

/-! ## Theorem A -/

/-- **(PHIN.3).**  The prime–Hodge history defect `T(t) = Φ ⊗ T_form(t)`. -/
def historyDefect (t : ℝ) : HistoryL2 PrimeHilbert →L[ℂ] HistoryL2 PrimeHilbert :=
  fluxTensor (stokesCubicUnit t)

theorem historyDefect_neg (t : ℝ) : historyDefect (-t) = -historyDefect t := by
  simp only [historyDefect, fluxTensor]
  rw [stokesCubicUnit_neg, historyMap_neg]

theorem adjoint_historyDefect (t : ℝ) : adjoint (historyDefect t) = historyDefect t := by
  simp only [historyDefect, fluxTensor]
  rw [adjoint_historyMap, (isSelfAdjoint_stokesCubicUnit t).adjoint_eq]
  exact historyMap_congr _ _ (funext fun n => Complex.conj_ofReal _) _

theorem historyDefect_of_ne {t : ℝ} (ht : t ≠ 0) :
    historyDefect t = ((Real.sign t : ℝ) : ℂ) •
      fluxTensor (adjoint (burnolPrimeSynthesis (abs_pos.mpr ht)) ∘L
        burnolPrimeSynthesis (abs_pos.mpr ht)) := by
  simp only [historyDefect, fluxTensor]
  rw [stokesCubicUnit, historyMap_smul, normalizedStokesUnit_eq_adjoint_comp (abs_pos.mpr ht)]

theorem fluxTensor_positive_traceClass {d : ℝ} (hd : 0 < d) :
    (fluxTensor (adjoint (burnolPrimeSynthesis hd) ∘L burnolPrimeSynthesis hd)).IsPositive ∧
      MemSchattenClass 1
        (fluxTensor (adjoint (burnolPrimeSynthesis hd) ∘L burnolPrimeSynthesis hd)) ∧
      opTrace (fluxTensor (adjoint (burnolPrimeSynthesis hd) ∘L burnolPrimeSynthesis hd))
        = 1 := by
  obtain ⟨h1, h2, h3⟩ := historyMap_weight_traceClass historyFlux_nonneg historyFlux_le_one
    PrimeHodgeHistory.summable_w (isHilbertSchmidt_burnolPrimeSynthesis hd)
  refine ⟨h1, h2, ?_⟩
  rw [h3, PrimeHodgeHistory.tsum_w, burnolPrimeSynthesis, hsNormSq_commonRadialPrimeSynthesis]
  norm_num

/-- **(PHIN.5).**  `T(t)* = T(t)`, `sign(t) T(t) ≥ 0`, Schatten-one, `tr T(t) = sign t`,
`‖T(t)‖₁ = 1`, `T(-t) = -T(t)`. -/
theorem historyDefect_integral_nuclear {t : ℝ} (ht : t ≠ 0) :
    adjoint (historyDefect t) = historyDefect t ∧
      (((Real.sign t : ℝ) : ℂ) • historyDefect t).IsPositive ∧
      MemSchattenClass 1 (historyDefect t) ∧
      opTrace (historyDefect t) = ((Real.sign t : ℝ) : ℂ) ∧
      traceNorm (HistoryL2 PrimeHilbert) (historyDefect t) = 1 ∧
      historyDefect (-t) = -historyDefect t := by
  have hd := abs_pos.mpr ht
  obtain ⟨hpos, hS1, htr⟩ := fluxTensor_positive_traceClass hd
  have hsign : ((Real.sign t : ℝ) : ℂ) * ((Real.sign t : ℝ) : ℂ) = 1 := by
    have h3 := sign_sq_of_ne_zero ht
    exact_mod_cast h3
  refine ⟨adjoint_historyDefect t, ?_, ?_, ?_, ?_, historyDefect_neg t⟩
  · rw [historyDefect_of_ne ht, smul_smul, hsign, one_smul]
    exact hpos
  · rw [historyDefect_of_ne ht]
    exact memSchattenClass_one_smul hS1 _
  · rw [historyDefect_of_ne ht, GaloisForLFunctions.HTGeometry.opTrace_smul, htr, mul_one]
  · rw [historyDefect_of_ne ht, traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_sign_of_ne_zero ht, one_mul, traceNorm_eq_re_opTrace_of_isPositive hS1 hpos, htr,
      Complex.one_re]

/-- **(PHIN.4).**  The full matrix `1_{n=k} w_n sign(t) √(π(p)π(q)) κ(log p, log q)`. -/
theorem inner_historyDefect_single {t : ℝ} (ht : t ≠ 0) (n k : ℕ) (p q : Nat.Primes) :
    ⟪(lp.single 2 n (HilbertSchmidt.lpBasis Nat.Primes p) : HistoryL2 PrimeHilbert),
      historyDefect t (lp.single 2 k (HilbertSchmidt.lpBasis Nat.Primes q))⟫_ℂ
      = if n = k then ((PrimeHodgeHistory.w n : ℝ) : ℂ) *
          ((Real.sign t * (Real.sqrt (stokesWeight |t| p * stokesWeight |t| q)
            * routePPrimitiveGammaJuliaStokesWallCubicKernel (Real.log (p : ℝ))
              (Real.log (q : ℝ))) : ℝ) : ℂ)
        else 0 := by
  simp only [historyDefect, fluxTensor]
  rw [inner_historyMap_single, lpBasis_eq_lpBasisVec, inner_lpBasisVec,
    stokesCubicUnit_basis_coord ht]

/-- **(PHIN.6).**  Every same-grade cross-prime entry is nonzero. -/
theorem inner_historyDefect_single_ne_zero {t : ℝ} (ht : t ≠ 0) (n : ℕ) (p q : Nat.Primes) :
    ⟪(lp.single 2 n (HilbertSchmidt.lpBasis Nat.Primes p) : HistoryL2 PrimeHilbert),
      historyDefect t (lp.single 2 n (HilbertSchmidt.lpBasis Nat.Primes q))⟫_ℂ ≠ 0 := by
  simp only [historyDefect, fluxTensor]
  rw [inner_historyMap_single, if_pos rfl, lpBasis_eq_lpBasisVec, inner_lpBasisVec]
  refine mul_ne_zero ?_ (stokesCubicUnit_basis_coord_ne_zero ht p q)
  exact_mod_cast (PrimeHodgeHistory.w_pos n).ne'

/-! ## The canonical identification with `ℓ²(ℕ × Primes)` -/

/-- The history basis `δ_n ⊗ e_p` of `ℓ²(ℕ; ℓ²(Primes))`. -/
abbrev primeHistoryBasis : HilbertBasis (ℕ × Nat.Primes) ℂ (HistoryL2 PrimeHilbert) :=
  historyBasis (HilbertSchmidt.lpBasis Nat.Primes)

/-- The canonical unitary `ℓ²(ℕ × Primes) ≃ ℓ²(ℕ) ⊗ ℓ²(Primes)`. -/
def primeHistoryUnitary : PrimeHodgeHistoryHilbert →L[ℂ] HistoryL2 PrimeHilbert :=
  (primeHistoryBasis.repr.symm : PrimeHodgeHistoryHilbert →L[ℂ] HistoryL2 PrimeHilbert)

theorem adjoint_primeHistoryUnitary_basis (np : ℕ × Nat.Primes) :
    adjoint primeHistoryUnitary (primeHistoryBasis np)
      = HilbertSchmidt.lpBasis PrimeHodgeHistoryIndex np := by
  rw [primeHistoryUnitary, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  change primeHistoryBasis.repr (primeHistoryBasis np) = _
  rw [HilbertBasis.repr_self, HilbertSchmidt.lpBasis_apply]

/-- **The joint kernel is the history tensor.**  Under the canonical unitary the corpus defect on
`ℓ²(ℕ × Primes)` is `Φ ⊗ T_form(t)`. -/
theorem primeHistoryUnitary_conj (t : ℝ) :
    primeHistoryUnitary ∘L primeHodgeHistoryIntegralNuclearHomotopyDefect t ∘L
        adjoint primeHistoryUnitary = historyDefect t := by
  refine ext_hilbertBasis_inner primeHistoryBasis fun np kq => ?_
  rw [comp_apply, comp_apply, ← adjoint_inner_left, adjoint_primeHistoryUnitary_basis,
    adjoint_primeHistoryUnitary_basis, historyBasis_apply, historyBasis_apply]
  by_cases ht : t = 0
  · subst ht
    simp only [historyDefect, fluxTensor]
    rw [primeHodgeHistoryIntegralNuclearHomotopyDefect_zero, stokesCubicUnit,
      Real.sign_zero, Complex.ofReal_zero, zero_smul, historyMap_zero]
    simp
  have hd := abs_pos.mpr ht
  rw [inner_historyDefect_single ht]
  have hK : primeHodgeHistoryIntegralNuclearHomotopyDefect t
      = ((Real.sign t : ℝ) : ℂ) • primeHodgeHistoryDefectOperator hd := by
    rw [primeHodgeHistoryIntegralNuclearHomotopyDefect, dif_neg ht]
  rw [hK, smul_apply, inner_smul_right, HilbertSchmidt.lpBasis_apply, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]
  rw [HilbertSchmidt.lpBasis_apply, primeHodgeHistoryDefectOperator,
    HilbertSchmidt.toOperator_single, primeHodgeHistoryDefectKernel]
  by_cases hnk : np.1 = kq.1
  · rw [if_pos hnk, if_pos hnk, normalizedStokesPrimeKernel_eq hd]
    dsimp only
    push_cast
    ring
  · rw [if_neg hnk, if_neg hnk, mul_zero]

/-! ## Theorem B: homotopy is a tail observable -/

/-- The history tail projection `Q_n ⊗ 1`. -/
def historyTailProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (n : ℕ) :
    HistoryL2 E →L[ℂ] HistoryL2 E :=
  historyMap (historyTail n) (norm_historyTail_le n) (ContinuousLinearMap.id ℂ E)

/-- The tail flux weights `1_{k ≥ n} w_k`. -/
def tailFlux (n k : ℕ) : ℝ := if n ≤ k then PrimeHodgeHistory.w k else 0

theorem tailFlux_nonneg (n k : ℕ) : 0 ≤ tailFlux n k := by
  unfold tailFlux
  split_ifs
  · exact historyFlux_nonneg k
  · exact le_rfl

theorem tailFlux_le_one (n k : ℕ) : tailFlux n k ≤ 1 := by
  unfold tailFlux
  split_ifs
  · exact historyFlux_le_one k
  · norm_num

theorem hasSum_tailFlux (n : ℕ) : HasSum (tailFlux n) (PrimeHodgeHistory.m n) := by
  rw [← hasSum_nat_add_iff' n]
  have hzero : ∑ i ∈ Finset.range n, tailFlux n i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [tailFlux, if_neg (not_le.mpr (Finset.mem_range.mp hi))]
  rw [hzero, sub_zero]
  refine (PrimeHodgeHistory.tail_hasSum_w n).congr_fun fun k => ?_
  rw [tailFlux, if_pos (Nat.le_add_left n k)]

theorem historyTailProjection_comp_fluxTensor {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (n : ℕ)
    (B : E →L[ℂ] F) :
    historyTailProjection n ∘L fluxTensor B
      = historyMap (fun k => ((tailFlux n k : ℝ) : ℂ))
          (norm_ofReal_weight_le_one (tailFlux_nonneg n) (tailFlux_le_one n)) B := by
  rw [historyTailProjection, fluxTensor, historyMap_comp, ContinuousLinearMap.id_comp]
  refine historyMap_congr _ _ (funext fun k => ?_) _
  simp only [historyTail, tailFlux]
  split_ifs <;> simp

theorem opTrace_historyTail_fluxTensor {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (n : ℕ) {S : E →L[ℂ] F} (hS : IsHilbertSchmidt S) :
    opTrace (historyTailProjection n ∘L fluxTensor (adjoint S ∘L S))
      = ((PrimeHodgeHistory.m n * ContinuousLinearMap.hsNormSq S : ℝ) : ℂ) := by
  rw [historyTailProjection_comp_fluxTensor, (historyMap_weight_traceClass (tailFlux_nonneg n)
    (tailFlux_le_one n) (hasSum_tailFlux n).summable hS).2.2, (hasSum_tailFlux n).tsum_eq]

/-- **(PHIN.7).**  `tr((Q_n ⊗ 1) T(t)) = m_n` for `t > 0`. -/
theorem opTrace_historyTail_historyDefect (n : ℕ) {t : ℝ} (ht : 0 < t) :
    opTrace (historyTailProjection n ∘L historyDefect t) = (PrimeHodgeHistory.m n : ℂ) := by
  rw [historyDefect_of_ne ht.ne', ContinuousLinearMap.comp_smul, Real.sign_of_pos ht,
    Complex.ofReal_one, one_smul, opTrace_historyTail_fluxTensor n
      (isHilbertSchmidt_burnolPrimeSynthesis _), burnolPrimeSynthesis,
    hsNormSq_commonRadialPrimeSynthesis, mul_one]

/-- The comoving wall object `𝖠 = Φ ⊗ A` on `ℓ²(ℕ; L²(e^{-x} dx))`. -/
def historyWallOperator :
    HistoryL2 (Lp ℂ 2 (expMeasure 1)) →L[ℂ] HistoryL2 (Lp ℂ 2 (expMeasure 1)) :=
  fluxTensor wallOperator

/-- **(PHIN.8).**  `tr((Q_n ⊗ 1) 𝖠) = ‖adⁿ_X(A)‖²_HS/((2n)! ‖A‖²_HS)`. -/
theorem opTrace_historyTail_historyWallOperator (n : ℕ) :
    opTrace (historyTailProjection n ∘L historyWallOperator)
      = ((ContinuousLinearMap.hsNormSq (jetKernel n).op /
          ((2 * n).factorial * ContinuousLinearMap.hsNormSq wallOperator) : ℝ) : ℂ) := by
  have h := opTrace_historyTail_fluxTensor n isHilbertSchmidt_burnolSynthesis
  rw [← wallOperator_eq_adjoint_comp, hsNormSq_burnolSynthesis, mul_one] at h
  rw [historyWallOperator, h, ← homotopyEnergy_eq_m]
  rfl

/-- The adjacent grade weights `1_{k = n} w_k`. -/
def gradeFlux (n k : ℕ) : ℝ := if k = n then PrimeHodgeHistory.w k else 0

theorem gradeFlux_nonneg (n k : ℕ) : 0 ≤ gradeFlux n k := by
  unfold gradeFlux
  split_ifs
  · exact historyFlux_nonneg k
  · exact le_rfl

theorem gradeFlux_le_one (n k : ℕ) : gradeFlux n k ≤ 1 := by
  unfold gradeFlux
  split_ifs
  · exact historyFlux_le_one k
  · norm_num

theorem hasSum_gradeFlux (n : ℕ) : HasSum (gradeFlux n) (PrimeHodgeHistory.w n) := by
  convert hasSum_ite_eq n (PrimeHodgeHistory.w n) using 1
  funext k
  simp only [gradeFlux]
  split_ifs with h <;> simp [h]

/-- **(PHIN.9).**  `tr(((Q_n - Q_{n+1}) ⊗ 1) 𝖠) = w_n`. -/
theorem opTrace_historyGrade_historyWallOperator (n : ℕ) :
    opTrace ((historyTailProjection n - historyTailProjection (n + 1)) ∘L historyWallOperator)
      = (PrimeHodgeHistory.w n : ℂ) := by
  have hgrade : (historyTailProjection n - historyTailProjection (n + 1)) ∘L historyWallOperator
      = historyMap (fun k => ((gradeFlux n k : ℝ) : ℂ))
          (norm_ofReal_weight_le_one (gradeFlux_nonneg n) (gradeFlux_le_one n))
          (adjoint burnolSynthesis ∘L burnolSynthesis) := by
    rw [historyWallOperator, wallOperator_eq_adjoint_comp]
    ext f k
    simp only [sub_comp, sub_apply, lp.coeFn_sub, Pi.sub_apply, historyTailProjection,
      fluxTensor, comp_apply, historyMap_apply, id_apply, historyTail, gradeFlux]
    by_cases hk : k = n
    · subst hk
      simp
    · by_cases hnk : n ≤ k
      · have hnk' : n + 1 ≤ k := by omega
        simp [hk, hnk, hnk']
      · have hnk' : ¬ n + 1 ≤ k := by omega
        simp [hk, hnk, hnk']
  rw [hgrade, (historyMap_weight_traceClass (gradeFlux_nonneg n) (gradeFlux_le_one n)
    (hasSum_gradeFlux n).summable isHilbertSchmidt_burnolSynthesis).2.2,
    (hasSum_gradeFlux n).tsum_eq, hsNormSq_burnolSynthesis, mul_one]

/-- **(PHIN.10).**  The integral orientation is the sum of the local fluxes. -/
theorem hasSum_opTrace_historyGrade_historyWallOperator :
    HasSum (fun n => opTrace ((historyTailProjection n - historyTailProjection (n + 1)) ∘L
      historyWallOperator)) 1 := by
  simp_rw [opTrace_historyGrade_historyWallOperator]
  have h := Complex.hasSum_ofReal.mpr PrimeHodgeHistory.hasSum_w
  rwa [Complex.ofReal_one] at h

/-! ## Theorem C: canonicality -/

/-- **Theorem C.**  A nonnegative diagonal whose history tails are the normalized commutator
energies is the flux `w`. -/
theorem eq_historyFlux_of_tails {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (htail : ∀ n, HasSum (fun k => a (k + n)) (homotopyEnergy n)) :
    a = PrimeHodgeHistory.w := by
  funext n
  have h0 := htail n
  have h1 := htail (n + 1)
  have hsplit := (hasSum_nat_add_iff' 1).mpr h0
  simp only [Finset.range_one, Finset.sum_singleton, zero_add] at hsplit
  have hshift : (fun k => a (k + 1 + n)) = fun k => a (k + (n + 1)) := by
    funext k
    rw [add_assoc, add_comm 1 n]
  rw [hshift] at hsplit
  have := hsplit.unique h1
  have hw : PrimeHodgeHistory.w n = homotopyEnergy n - homotopyEnergy (n + 1) := by
    rw [homotopyEnergy_eq_m, homotopyEnergy_eq_m]
    rfl
  rw [hw]
  have _ := ha n
  linarith

/-! ## Theorem D: the sub-unit anchor -/

/-- **(PHIN.11).**  `‖Φ‖ = 2/3` and `‖𝖠‖ ≤ 8/(3√35) < 1`. -/
theorem norm_historyWallOperator_le :
    ‖primeHodgeHistoryFluxOperator‖ = 2 / 3 ∧
      ‖historyWallOperator‖ ≤ 8 / (3 * Real.sqrt 35) ∧ 8 / (3 * Real.sqrt 35) < 1 := by
  refine ⟨norm_primeHodgeHistoryFluxOperator, ?_, PrimeHodgeHistory.subunit_constant⟩
  refine (norm_historyMap_le _ _ _ (by norm_num : (0 : ℝ) ≤ 2 / 3) fun n => ?_).trans ?_
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (historyFlux_nonneg n)]
    exact PrimeHodgeHistory.w_le_two_thirds n
  · have h := norm_wallOperator_le
    calc 2 / 3 * ‖wallOperator‖ ≤ 2 / 3 * (4 / Real.sqrt 35) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 8 / (3 * Real.sqrt 35) := by field_simp; ring

/-! ## Theorem E: two incompatible wall closures -/

theorem norm_stokesCubicUnit_le_one (t : ℝ) : ‖stokesCubicUnit t‖ ≤ 1 := by
  rw [stokesCubicUnit, norm_smul]
  exact mul_le_one₀ (norm_sign_le_one t) (norm_nonneg _) (norm_normalizedStokesUnit_le_one _)

/-- **Fixed chart.**  `T(t) → 0` strongly as `t → 0`. -/
theorem tendsto_historyDefect_apply (f : HistoryL2 PrimeHilbert) :
    Tendsto (fun t => historyDefect t f) (𝓝[≠] 0) (𝓝 0) :=
  tendsto_historyMap_apply _ historyFlux_norm_le norm_stokesCubicUnit_le_one
    tendsto_stokesCubicUnit_apply f

/-- The comoving history chart `1 ⊗ U_d`. -/
def historyComovingChart {d : ℝ} (hd : 0 < d) :
    HistoryL2 PrimeHilbert →L[ℂ] HistoryL2 (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :=
  historyMap (fun _ => 1) (fun _ => by norm_num) (comovingChart hd)

theorem historyComovingChart_conj {d : ℝ} (hd : 0 < d) (B : PrimeHilbert →L[ℂ] PrimeHilbert) :
    historyComovingChart hd ∘L fluxTensor B ∘L adjoint (historyComovingChart hd)
      = fluxTensor (comovingChart hd ∘L B ∘L adjoint (comovingChart hd)) := by
  rw [historyComovingChart, adjoint_historyMap, fluxTensor, historyMap_comp, historyMap_comp]
  refine historyMap_congr _ _ (funext fun n => ?_) _
  simp

/-- **(PHIN.12).**  The comoving chart carries `T(±d)` to `±Φ ⊗ A_d`, and
`‖Φ ⊗ A_d - Φ ⊗ A_0‖₁ → 0`. -/
theorem historyDefect_comoving_landing :
    (∀ (d : ℝ) (hd : 0 < d),
      historyComovingChart hd ∘L historyDefect d ∘L adjoint (historyComovingChart hd)
          = fluxTensor (wallLandingOp d) ∧
        historyComovingChart hd ∘L historyDefect (-d) ∘L adjoint (historyComovingChart hd)
          = -fluxTensor (wallLandingOp d)) ∧
      Tendsto (fun d => traceNorm (HistoryL2 (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1))))
        (fluxTensor (wallLandingOp d) - fluxTensor quantileWallOperator)) (𝓝[>] 0) (𝓝 0) := by
  refine ⟨fun d hd => ⟨?_, ?_⟩, ?_⟩
  · rw [historyDefect, historyComovingChart_conj, comovingChart_conj_stokesCubicUnit hd]
  · rw [historyDefect_neg, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
      historyDefect, historyComovingChart_conj, comovingChart_conj_stokesCubicUnit hd]
  · have hup := tendsto_hsNorm_wallSynthesis_sub.const_mul 2
    rw [mul_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun _ => traceNorm_nonneg _) fun d => ?_
    set μ := routePPrimitiveGammaJuliaStokesWallHalfLineLaw d
    have h := traceNorm_historyMap_sub_le historyFlux_nonneg historyFlux_le_one
      PrimeHodgeHistory.summable_w (isHilbertSchmidt_quantileBurnolSynthesis μ)
      (isHilbertSchmidt_quantileBurnolSynthesis (expMeasure 1))
    rw [PrimeHodgeHistory.tsum_w, one_mul] at h
    have h1 := hsNorm_quantileBurnolSynthesis_le μ
    have h2 := hsNorm_quantileBurnolSynthesis_le (expMeasure 1)
    have h3 := ContinuousLinearMap.hsNorm_nonneg
      (quantileBurnolSynthesis μ - quantileBurnolSynthesis (expMeasure 1))
    rw [← quantileLandingOp_eq_adjoint_comp, ← quantileLandingOp_eq_adjoint_comp,
      quantileLandingOp_expMeasure_one] at h
    change traceNorm _ (fluxTensor (quantileLandingOp μ) - fluxTensor quantileWallOperator) ≤ _
    refine h.trans ?_
    nlinarith

/-- The negative chamber lands at `-Φ ⊗ A_0`. -/
theorem tendsto_traceNorm_neg_fluxTensor_wallLanding :
    Tendsto (fun d => traceNorm (HistoryL2 (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1))))
      (-fluxTensor (wallLandingOp d) - -fluxTensor quantileWallOperator)) (𝓝[>] 0) (𝓝 0) := by
  refine historyDefect_comoving_landing.2.congr fun d => ?_
  rw [show -fluxTensor (wallLandingOp d) - -fluxTensor quantileWallOperator
      = (-1 : ℂ) • (fluxTensor (wallLandingOp d) - fluxTensor quantileWallOperator) by
    rw [neg_one_smul]; abel, traceNorm_smul, norm_neg, norm_one, one_mul]

/-- The comoving limit `Φ ⊗ A_0` is the quantile transport `(1 ⊗ U_0) 𝖠 (1 ⊗ U_0)*` of
`𝖠 = Φ ⊗ A`. -/
theorem fluxTensor_quantileWallOperator :
    fluxTensor quantileWallOperator
      = historyMap (fun _ => 1) (fun _ => by norm_num)
          (compL2 (measurePreserving_quantile (expMeasure 1))) ∘L historyWallOperator ∘L
        adjoint (historyMap (fun _ => 1) (fun _ => by norm_num)
          (compL2 (measurePreserving_quantile (expMeasure 1)))) := by
  have hW : (wallKernelOf (expMeasure 1)).op = wallOperator :=
    SqIntKernel.op_congr _ (Eventually.of_forall fun _ => Eventually.of_forall fun _ => rfl)
  rw [historyWallOperator, adjoint_historyMap]
  simp only [fluxTensor]
  rw [historyMap_comp, historyMap_comp, ← quantileLandingOp_expMeasure_one,
    quantileLandingOp_eq_conj, hW]
  refine historyMap_congr _ _ (funext fun n => ?_) _
  simp

/-- **The prime–Hodge history integral nuclear defect.**  The history tensor `Φ ⊗ T_form(t)` is
the corpus joint defect under the canonical unitary; it is integral, nuclear and prime-mixed; its
history tails are the normalized commutator energies; it is a strict sub-unit anchor on the
comoving wall; and its two wall closures are the fixed-chart strong loss and the comoving
trace-norm landing at `±Φ ⊗ A_0`. -/
theorem prime_hodge_history_tensor_defect :
    (∀ t, primeHistoryUnitary ∘L primeHodgeHistoryIntegralNuclearHomotopyDefect t ∘L
        adjoint primeHistoryUnitary = historyDefect t) ∧
      (∀ t, t ≠ 0 → adjoint (historyDefect t) = historyDefect t ∧
        (((Real.sign t : ℝ) : ℂ) • historyDefect t).IsPositive ∧
        MemSchattenClass 1 (historyDefect t) ∧
        opTrace (historyDefect t) = ((Real.sign t : ℝ) : ℂ) ∧
        traceNorm (HistoryL2 PrimeHilbert) (historyDefect t) = 1 ∧
        historyDefect (-t) = -historyDefect t) ∧
      (∀ n t, 0 < t →
        opTrace (historyTailProjection n ∘L historyDefect t) = (PrimeHodgeHistory.m n : ℂ)) ∧
      (∀ n, opTrace (historyTailProjection n ∘L historyWallOperator)
        = ((ContinuousLinearMap.hsNormSq (jetKernel n).op /
          ((2 * n).factorial * ContinuousLinearMap.hsNormSq wallOperator) : ℝ) : ℂ)) ∧
      (∀ n, opTrace ((historyTailProjection n - historyTailProjection (n + 1)) ∘L
        historyWallOperator) = (PrimeHodgeHistory.w n : ℂ)) ∧
      ‖historyWallOperator‖ ≤ 8 / (3 * Real.sqrt 35) ∧ 8 / (3 * Real.sqrt 35) < 1 ∧
      (∀ f, Tendsto (fun t => historyDefect t f) (𝓝[≠] 0) (𝓝 0)) ∧
      Tendsto (fun d => traceNorm (HistoryL2 (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1))))
        (fluxTensor (wallLandingOp d) - fluxTensor quantileWallOperator)) (𝓝[>] 0) (𝓝 0) :=
  ⟨primeHistoryUnitary_conj, fun _ ht => historyDefect_integral_nuclear ht,
    fun n _ ht => opTrace_historyTail_historyDefect n ht, opTrace_historyTail_historyWallOperator,
    opTrace_historyGrade_historyWallOperator, norm_historyWallOperator_le.2.1,
    norm_historyWallOperator_le.2.2, tendsto_historyDefect_apply,
    historyDefect_comoving_landing.2⟩

end GaloisForLFunctions.HTGeometry
