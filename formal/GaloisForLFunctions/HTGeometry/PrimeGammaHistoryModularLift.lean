import GaloisForLFunctions.HTGeometry.PrimeGammaRelativeModularTransport
import GaloisForLFunctions.HTGeometry.HistoryTensorOperators

/-!
# The history lift of the relative modular transport

The degree-`k` history channel `Q_d^{(k)} = Φ^{1/2} ⊗ W_d^{(k)}` sends
`e_{(n,p)} ↦ √(w_n μ_d(p)) e_n ⊗ ψ_{log p}^{(k)}`.  Through the currying unitary
`ℓ²(ℕ × Primes) ≅ ℓ²(ℕ; ℓ²(Primes))` it is the history tensor `√w ⊗ W_d^{(k)}`, so:

* **(PPTI.34)** its left Gram is `Φ ⊗ B_d^{(k)}`: positive, Schatten-one of trace one, injective,
  with dense nonclosed range; its right Gram is (for `k = 3`) the prime–Hodge defect `𝖳_d`;
* **(PPTI.41)** `(I ⊗ A_∞) Q_d^{(2)} = Q_d^{(3)}` coordinatewise, and `I ⊗ U_∞` is unitary;
* **(PPTI.42)** the positive square root of `Φ ⊗ B_d^{(k)}` is `√w ⊗ (B_d^{(k)})^{1/2}`, and
  `(I ⊗ A_∞)` whitened by these square roots is exactly `I ⊗ U_∞`.
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## Uniqueness of positive square roots -/

section Sqrt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A positive operator is the unique positive square root of its square. -/
theorem isPositive_sqrt_unique {S T : E →L[ℂ] E} (hS : S.IsPositive) (hT : T.IsPositive)
    (h : S ∘L S = T ∘L T) : S = T := by
  have hS0 : 0 ≤ S := (nonneg_iff_isPositive S).2 hS
  have hT0 : 0 ≤ T := (nonneg_iff_isPositive T).2 hT
  have h1 : CFC.sqrt (S * S) = S := CFC.sqrt_mul_self S hS0
  have h2 : CFC.sqrt (T * T) = T := CFC.sqrt_mul_self T hT0
  rw [← h1, ← h2]
  exact congrArg CFC.sqrt h

end Sqrt

/-! ## History unitaries -/

section HistoryUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_historyUnitWeight_le_one (n : ℕ) : ‖(fun _ : ℕ => (1 : ℂ)) n‖ ≤ 1 := by simp

/-- The coordinatewise lift `I ⊗ U` of a unitary `U` of `E` to `ℓ²(ℕ; E)`. -/
def historyUnitary (U : E ≃ₗᵢ[ℂ] E) : HistoryL2 E ≃ₗᵢ[ℂ] HistoryL2 E :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (historyMap (fun _ => 1) norm_historyUnitWeight_le_one (U : E →L[ℂ] E) :
        HistoryL2 E →ₗ[ℂ] HistoryL2 E)
      norm_map' := fun f => by
        have h : ‖historyMap (fun _ => 1) norm_historyUnitWeight_le_one (U : E →L[ℂ] E) f‖ ^ 2 = ‖f‖ ^ 2 := by
          rw [norm_sq_historyL2, norm_sq_historyL2]
          refine tsum_congr fun n => ?_
          rw [historyMap_apply, one_smul]
          simp
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h }
    (fun f => ⟨historyMap (fun _ => 1) norm_historyUnitWeight_le_one (U.symm : E →L[ℂ] E) f, by
      ext n
      simp⟩)

omit [CompleteSpace E] in
@[simp] theorem historyUnitary_apply (U : E ≃ₗᵢ[ℂ] E) (f : HistoryL2 E) (n : ℕ) :
    historyUnitary U f n = U (f n) := by
  change historyMap (fun _ => 1) norm_historyUnitWeight_le_one (U : E →L[ℂ] E) f n = U (f n)
  rw [historyMap_apply, one_smul]
  rfl

end HistoryUnitary

/-! ## The degree-`k` history channel -/

variable {d : ℝ}

/-- The history–prime frame vector `√(w_n μ_d(p)) e_n ⊗ ψ_{log p}^{(k)}`. -/
def historyCoherentFrame (k : ℕ) [NeZero k] (d : ℝ) (np : ℕ × Nat.Primes) :
    HistoryL2 HalfLineL2 :=
  ((Real.sqrt (PrimeHodgeHistory.w np.1 * primeFormationLaw d np.2) : ℝ) : ℂ) •
    lp.single 2 np.1 (gammaCoherentVector k (primeClock_pos np.2))

theorem historyCoherentFrame_three : historyCoherentFrame 3 d = historyPrimeFrame d := rfl

theorem norm_sq_historyCoherentFrame (k : ℕ) [NeZero k] (hd : 0 < d) (np : ℕ × Nat.Primes) :
    ‖historyCoherentFrame k d np‖ ^ 2 = PrimeHodgeHistory.w np.1 * primeFormationLaw d np.2 := by
  rw [historyCoherentFrame, norm_smul, lp.norm_single (by norm_num), norm_gammaCoherentVector,
    mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (mul_pos (PrimeHodgeHistory.w_pos _) (primeFormationLaw_pos hd _)).le]

theorem summable_norm_sq_historyCoherentFrame (k : ℕ) [NeZero k] (hd : 0 < d) :
    Summable fun np : ℕ × Nat.Primes => ‖historyCoherentFrame k d np‖ ^ 2 := by
  simp_rw [norm_sq_historyCoherentFrame k hd]
  exact summable_mul_of_summable_norm (f := PrimeHodgeHistory.w) (g := primeFormationLaw d)
    (by simpa [Real.norm_of_nonneg (PrimeHodgeHistory.w_pos _).le] using
      PrimeHodgeHistory.summable_w)
    (by simpa [Real.norm_of_nonneg (primeFormationLaw_pos hd _).le] using
      (hasSum_primeFormationLaw hd).summable)

/-- **(PPTI.32).**  The history channel `Q_d^{(k)} = Φ^{1/2} ⊗ W_d^{(k)}`. -/
def historyCoherentChannel (k : ℕ) [NeZero k] (hd : 0 < d) :
    PrimeHodgeHistoryHilbert →L[ℂ] HistoryL2 HalfLineL2 :=
  squareSummableSynthesis (historyCoherentFrame k d) (summable_norm_sq_historyCoherentFrame k hd)

theorem historyCoherentChannel_three (hd : 0 < d) :
    historyCoherentChannel 3 hd = historyFormationChannel hd := rfl

theorem historyCoherentChannel_single (k : ℕ) [NeZero k] (hd : 0 < d) (np : ℕ × Nat.Primes) :
    historyCoherentChannel k hd (lp.single 2 np 1) = historyCoherentFrame k d np := by
  rw [historyCoherentChannel, squareSummableSynthesis_single, one_smul]

/-- `‖Q_d^{(k)}‖²_HS = Tr Φ · Tr A_d = 1`. -/
theorem hsNormSq_historyCoherentChannel (k : ℕ) [NeZero k] (hd : 0 < d) :
    ContinuousLinearMap.hsNormSq (historyCoherentChannel k hd) = 1 := by
  rw [historyCoherentChannel, hsNormSq_squareSummableSynthesis]
  simp_rw [norm_sq_historyCoherentFrame k hd]
  rw [tsum_mul_tsum_of_summable_norm (f := PrimeHodgeHistory.w) (g := primeFormationLaw d)
    (by simpa [Real.norm_of_nonneg (PrimeHodgeHistory.w_pos _).le] using
      PrimeHodgeHistory.summable_w)
    (by simpa [Real.norm_of_nonneg (primeFormationLaw_pos hd _).le] using
      (hasSum_primeFormationLaw hd).summable) |>.symm,
    PrimeHodgeHistory.tsum_w, (hasSum_primeFormationLaw hd).tsum_eq, mul_one]

/-! ## Currying and the tensor form -/

/-- The currying unitary `ℓ²(ℕ; ℓ²(Primes)) ≅ ℓ²(ℕ × Primes)`. -/
def historyPrimeCurrying :
    HistoryL2 (lp (fun _ : Nat.Primes => ℂ) 2) ≃ₗᵢ[ℂ] PrimeHodgeHistoryHilbert :=
  (historyBasis (HilbertSchmidt.lpBasis Nat.Primes)).repr

theorem historyPrimeCurrying_symm_single (np : ℕ × Nat.Primes) :
    historyPrimeCurrying.symm (lp.single 2 np 1) = lp.single 2 np.1 (lp.single 2 np.2 1) := by
  rw [historyPrimeCurrying, HilbertBasis.repr_symm_single, historyBasis_apply,
    HilbertSchmidt.lpBasis_apply]

/-- The history weight `√w_n`. -/
def sqrtHistoryWeight (n : ℕ) : ℂ := ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ)

theorem w_le_one (n : ℕ) : PrimeHodgeHistory.w n ≤ 1 :=
  (PrimeHodgeHistory.w_antitone (Nat.zero_le n)).trans
    (by rw [PrimeHodgeHistory.w_zero]; norm_num)

theorem norm_sqrtHistoryWeight_le_one (n : ℕ) : ‖sqrtHistoryWeight n‖ ≤ 1 := by
  rw [sqrtHistoryWeight, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (w_le_one n)

theorem sqrtHistoryWeight_ne_zero (n : ℕ) : sqrtHistoryWeight n ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (PrimeHodgeHistory.w_pos n)).ne'

theorem conj_sqrtHistoryWeight (n : ℕ) : conj (sqrtHistoryWeight n) = sqrtHistoryWeight n :=
  Complex.conj_ofReal _

/-- The history weight `w_n` as a scalar. -/
def historyWeight (n : ℕ) : ℂ := ((PrimeHodgeHistory.w n : ℝ) : ℂ)

theorem norm_historyWeight_le_one (n : ℕ) : ‖historyWeight n‖ ≤ 1 := by
  rw [historyWeight, Complex.norm_real, Real.norm_of_nonneg (PrimeHodgeHistory.w_pos n).le]
  exact w_le_one n

theorem sqrtHistoryWeight_mul_self (n : ℕ) :
    sqrtHistoryWeight n * sqrtHistoryWeight n = historyWeight n := by
  rw [sqrtHistoryWeight, historyWeight, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (PrimeHodgeHistory.w_pos n).le]

/-- **The tensor form.**  `Q_d^{(k)} = (√w ⊗ W_d^{(k)}) ∘ (currying)⁻¹`. -/
theorem historyCoherentChannel_eq_tensor (k : ℕ) [NeZero k] (hd : 0 < d) :
    historyCoherentChannel k hd =
      historyMap sqrtHistoryWeight norm_sqrtHistoryWeight_le_one (primeCoherentSynthesis k hd) ∘L
        (historyPrimeCurrying.symm : PrimeHodgeHistoryHilbert →L[ℂ] _) := by
  refine ContinuousLinearMap.ext_on (dense_span_lp_single (ι := ℕ × Nat.Primes)
    |> Submodule.dense_iff_topologicalClosure_eq_top.2) ?_
  rintro _ ⟨np, rfl⟩
  rw [historyCoherentChannel_single, ContinuousLinearMap.comp_apply]
  change historyCoherentFrame k d np =
    historyMap sqrtHistoryWeight norm_sqrtHistoryWeight_le_one (primeCoherentSynthesis k hd)
      (historyPrimeCurrying.symm (lp.single 2 np 1))
  rw [historyPrimeCurrying_symm_single, historyMap_single, primeCoherentSynthesis_single,
    historyCoherentFrame, primeCoherentFrame, smul_smul, ← lp.single_smul, sqrtHistoryWeight,
    Real.sqrt_mul (PrimeHodgeHistory.w_pos _).le, Complex.ofReal_mul]

theorem historyCoherentChannel_apply (k : ℕ) [NeZero k] (hd : 0 < d)
    (c : PrimeHodgeHistoryHilbert) (n : ℕ) :
    historyCoherentChannel k hd c n =
      sqrtHistoryWeight n • primeCoherentSynthesis k hd (historyPrimeCurrying.symm c n) := by
  rw [historyCoherentChannel_eq_tensor]
  rfl

/-! ## (PPTI.34): the left Gram -/

/-- **(PPTI.34).**  `Q_d^{(k)} Q_d^{(k)*} = Φ ⊗ B_d^{(k)}`. -/
theorem historyCoherentChannel_leftGram (k : ℕ) [NeZero k] (hd : 0 < d) :
    historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd) =
      historyMap historyWeight norm_historyWeight_le_one
        (primeCoherentSynthesis k hd ∘L adjoint (primeCoherentSynthesis k hd)) := by
  rw [historyCoherentChannel_eq_tensor, adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, adjoint_historyMap]
  refine ContinuousLinearMap.ext fun f => lp.ext (funext fun n => ?_)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
    historyMap_apply, map_smul, smul_smul, conj_sqrtHistoryWeight, sqrtHistoryWeight_mul_self]

theorem not_finiteDimensional_historyHalfLine : ¬ FiniteDimensional ℂ (HistoryL2 HalfLineL2) := by
  haveI : Nontrivial HalfLineL2 := ⟨⟨gammaCoherentVector 1 one_pos, 0, fun h => by
    have := norm_gammaCoherentVector 1 (t := 1) one_pos
    rw [h, norm_zero] at this
    exact zero_ne_one this⟩⟩
  exact not_finiteDimensional_lp (I := ℕ) (H := HalfLineL2)

/-- **(PPTI.34), properties.**  The left Gram `Φ ⊗ B_d^{(k)}` is positive, Schatten-one of trace
one, injective, has dense range, and its range is not closed. -/
theorem historyCoherentLeftGram_properties (k : ℕ) [NeZero k] (hd : 0 < d) :
    (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd)).IsPositive ∧
      MemSchattenClass 1 (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd)) ∧
      (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd)).opTrace = 1 ∧
      Function.Injective (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd)) ∧
      DenseRange (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd)) ∧
      ¬ IsClosed (Set.range
        (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd))) := by
  obtain ⟨hpos, hS, htr⟩ := leftGram_traceClass (summable_norm_sq_historyCoherentFrame k hd)
  have htr1 : (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd)).opTrace = 1 := by
    rw [historyCoherentChannel, htr]
    have h := hsNormSq_historyCoherentChannel k hd
    rw [historyCoherentChannel, hsNormSq_squareSummableSynthesis] at h
    rw [h, Complex.ofReal_one]
  have hinj : Function.Injective
      (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd)) := by
    rw [historyCoherentChannel_leftGram]
    refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
    obtain ⟨-, -, -, hBinj, -⟩ := primeFormationLeftGram_properties k hd
    refine lp.ext (funext fun n => ?_)
    have hn := congrArg (fun g : HistoryL2 HalfLineL2 => g n) hf
    simp only [historyMap_apply, lp.coeFn_zero, Pi.zero_apply] at hn
    have hw : historyWeight n ≠ 0 :=
      Complex.ofReal_ne_zero.2 (PrimeHodgeHistory.w_pos n).ne'
    have hB := (smul_eq_zero.1 hn).resolve_left hw
    rw [lp.coeFn_zero, Pi.zero_apply]
    exact (injective_iff_map_eq_zero _).1 hBinj _ hB
  have hsa : adjoint (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd)) =
      historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd) :=
    hpos.isSelfAdjoint.adjoint_eq
  have hdense : DenseRange
      (historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd)) := by
    have h := denseRange_adjoint_of_injective hinj
    rwa [hsa] at h
  refine ⟨hpos, hS, htr1, hinj, hdense, fun hclosed => ?_⟩
  exact not_finiteDimensional_historyHalfLine
    (finiteDimensional_of_compact_injective_isClosed_range _
      (hS.isCompactOperator one_pos) hinj hclosed)

/-- For `k = 3` the right Gram of the same channel is the prime–Hodge defect `𝖳_d`. -/
theorem historyCoherentChannel_rightGram_three (hd : 0 < d) :
    adjoint (historyCoherentChannel 3 hd) ∘L historyCoherentChannel 3 hd =
      primeHodgeHistoryDefectOperator hd :=
  adjoint_comp_historyFormationChannel hd

/-! ## (PPTI.41): the creator lifts through the history factor -/

/-- **(PPTI.41).**  `(I ⊗ A_∞) Q_d^{(2)} = Q_d^{(3)}`: every history coordinate of `Q^{(2)} c` lies
in the domain of `A_∞`, which sends it to the same coordinate of `Q^{(3)} c`. -/
theorem historyCoherentChannel_mem_graph (hd : 0 < d) (c : PrimeHodgeHistoryHilbert) (n : ℕ) :
    (historyCoherentChannel 2 hd c n, historyCoherentChannel 3 hd c n) ∈ mellinCreatorOp.graph := by
  rw [historyCoherentChannel_apply, historyCoherentChannel_apply]
  exact mellinCreatorOp.graph.smul_mem (sqrtHistoryWeight n)
    (primeCoherentSynthesis_mem_graph hd _)

/-- `U_history = I ⊗ U_∞`. -/
def historyRelativeModularUnitary (hd : 0 < d) : HistoryL2 HalfLineL2 ≃ₗᵢ[ℂ] HistoryL2 HalfLineL2 :=
  historyUnitary (relativeModularUnitary hd)

/-! ## (PPTI.42): whitening by the left Gram square roots -/

/-- The positive square root `√w ⊗ (B_d^{(k)})^{1/2}` of `Φ ⊗ B_d^{(k)}`. -/
def historyLeftGramRoot (k : ℕ) [NeZero k] (hd : 0 < d) :
    HistoryL2 HalfLineL2 →L[ℂ] HistoryL2 HalfLineL2 :=
  historyMap sqrtHistoryWeight norm_sqrtHistoryWeight_le_one
    (leftModulus (primeCoherentSynthesis k hd))

theorem historyLeftGramRoot_apply (k : ℕ) [NeZero k] (hd : 0 < d) (f : HistoryL2 HalfLineL2)
    (n : ℕ) :
    historyLeftGramRoot k hd f n =
      sqrtHistoryWeight n • leftModulus (primeCoherentSynthesis k hd) (f n) := rfl

theorem isPositive_historyLeftGramRoot (k : ℕ) [NeZero k] (hd : 0 < d) :
    (historyLeftGramRoot k hd).IsPositive := by
  refine ⟨?_, fun f => ?_⟩
  · have hsa : IsSelfAdjoint (historyLeftGramRoot k hd) := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff', historyLeftGramRoot,
        adjoint_historyMap, adjoint_leftModulus]
      exact historyMap_congr _ _ (funext conj_sqrtHistoryWeight) _
    exact hsa.isSymmetric
  · have hs := (RCLike.reCLM (K := ℂ)).hasSum
      (lp.hasSum_inner (𝕜 := ℂ) (historyLeftGramRoot k hd f) f)
    refine hs.nonneg fun n => ?_
    simp only [RCLike.reCLM_apply]
    rw [historyLeftGramRoot_apply, inner_smul_left, conj_sqrtHistoryWeight, sqrtHistoryWeight]
    have h := (isPositive_leftModulus (primeCoherentSynthesis k hd)).re_inner_nonneg_left (f n)
    have hre : RCLike.re (((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) *
        ⟪leftModulus (primeCoherentSynthesis k hd) (f n), f n⟫_ℂ) =
        Real.sqrt (PrimeHodgeHistory.w n) *
          RCLike.re ⟪leftModulus (primeCoherentSynthesis k hd) (f n), f n⟫_ℂ :=
      Complex.re_ofReal_mul _ _
    rw [hre]
    exact mul_nonneg (Real.sqrt_nonneg _) h

/-- **(PPTI.42), square roots.**  `(√w ⊗ (B^{(k)})^{1/2})² = Φ ⊗ B^{(k)} = Q^{(k)} Q^{(k)*}`, and it
is the unique positive square root. -/
theorem historyLeftGramRoot_sq (k : ℕ) [NeZero k] (hd : 0 < d) :
    historyLeftGramRoot k hd ∘L historyLeftGramRoot k hd =
      historyCoherentChannel k hd ∘L adjoint (historyCoherentChannel k hd) := by
  rw [historyCoherentChannel_leftGram, historyLeftGramRoot, historyMap_comp, leftModulus_comp_self]
  exact historyMap_congr _ _ (funext sqrtHistoryWeight_mul_self) _

theorem historyLeftGramRoot_eq_leftModulus (k : ℕ) [NeZero k] (hd : 0 < d) :
    historyLeftGramRoot k hd = leftModulus (historyCoherentChannel k hd) :=
  isPositive_sqrt_unique (isPositive_historyLeftGramRoot k hd)
    (isPositive_leftModulus _) ((historyLeftGramRoot_sq k hd).trans
      (leftModulus_comp_self _).symm)

/-- **(PPTI.42).**  `(𝖳_left^{(3)})^{-1/2} (I ⊗ A_∞) (𝖳_left^{(2)})^{1/2} = I ⊗ U_∞`: the history
vector `g` satisfies `(I ⊗ A_∞)(𝖳_left^{(2)})^{1/2} f = (𝖳_left^{(3)})^{1/2} g` coordinatewise
exactly when `g = (I ⊗ U_∞) f`. -/
theorem historyLeftGramRoot_mem_graph_iff (hd : 0 < d) (f g : HistoryL2 HalfLineL2) :
    (∀ n, (historyLeftGramRoot 2 hd f n, historyLeftGramRoot 3 hd g n) ∈ mellinCreatorOp.graph) ↔
      g = historyRelativeModularUnitary hd f := by
  have hcoord : ∀ n, (historyLeftGramRoot 2 hd f n, historyLeftGramRoot 3 hd g n) ∈
      mellinCreatorOp.graph ↔
        (leftModulus (primeCoherentSynthesis 2 hd) (f n),
          leftModulus (primeCoherentSynthesis 3 hd) (g n)) ∈ mellinCreatorOp.graph := by
    intro n
    rw [historyLeftGramRoot_apply, historyLeftGramRoot_apply]
    constructor
    · intro h
      have h' := mellinCreatorOp.graph.smul_mem (sqrtHistoryWeight n)⁻¹ h
      rwa [Prod.smul_mk, smul_smul, smul_smul, inv_mul_cancel₀ (sqrtHistoryWeight_ne_zero n),
        one_smul, one_smul] at h'
    · intro h
      exact mellinCreatorOp.graph.smul_mem (sqrtHistoryWeight n) h
  simp_rw [hcoord, mem_graph_leftModulus_iff]
  constructor
  · intro h
    ext n
    rw [h n, historyRelativeModularUnitary, historyUnitary_apply]
  · rintro rfl n
    rw [historyRelativeModularUnitary, historyUnitary_apply]

end GaloisForLFunctions.HTGeometry
