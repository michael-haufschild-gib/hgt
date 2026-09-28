import GaloisForLFunctions.RHTower.PoissonThermalFullLineMultipliers
import GaloisForLFunctions.HTGeometry.SchurKernelHalfLineCompression
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.RHTower.MertensClockDefectTraceClass
import GaloisForLFunctions.RHTower.PoissonPrimeClockCommutator
import GaloisForLFunctions.RHTower.SoninOrthonormalCompactVanishing

/-!
# The signed prime commutator carries the flat bulk modulo trace class

Let `U` be the harmonic-prime-cell isometry, `K` the prime Poisson Gram and
`C_P = i[X_P, K]` the prime clock commutator (`X_P` multiplies `δ_p` by `log log p`).  With
`R`, `E = R*` the half-line restriction and extension:

* `R W_full E = W` and `R J_full E = i W_j` (the Wiener–Hopf compressions);
* `U C_P U* = i A_j`, so `U C_P U* - P₊ J_full P₊ = i (A_j - W_j)` is trace class, and likewise
  `U K U* - P₊ W_full P₊ = A - W`.

Trace-class closeness does not transfer the sign: on `ℓ²(ℕ)` the compact self-adjoint diagonal
operators `L = diag(2^{-n})`, `L' = diag((-1)ⁿ 2^{-n})` differ by a trace-class operator, while
`sgn L - sgn L' = diag(1 - (-1)ⁿ)` is not compact.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2
local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-! ### Half-line compressions of the full-line operators -/

/-- `P₊ W_full P₊ = W`. -/
theorem halfLine_compression_thermalConvOp :
    halfLineRestrict ∘L thermalConvOp ∘L halfLineExtend = wienerHopfSechOp := by
  rw [thermalConvOp, SchurKernel.halfLineRestrict_comp_op_comp_halfLineExtend, wienerHopfSechOp]
  exact SchurKernel.op_eq_of_ae (Eventually.of_forall fun y => Eventually.of_forall fun z => rfl)

/-- `P₊ J_full P₊ = i W_j`. -/
theorem halfLine_compression_thermalCommOp :
    halfLineRestrict ∘L thermalCommOp ∘L halfLineExtend = Complex.I • wienerHopfTiltOp := by
  rw [thermalCommOp, SchurKernel.halfLineRestrict_comp_op_comp_halfLineExtend, wienerHopfTiltOp]
  exact SchurKernel.op_eq_smul_of_toFun Complex.I fun y z => rfl

/-- **`i[Y, W] = J` on the half-line.**  For `f ∈ L²(0,∞)` with `y f ∈ L²` (represented by `g`),
`W_j f = y · W f - W g` almost everywhere. -/
theorem wienerHopfTiltOp_ae_eq_commutator (f g : L²₊)
    (hg : (g : ℝ → ℂ) =ᵐ[halfLineMeasure] fun y => (y : ℂ) * f y) :
    (wienerHopfTiltOp f : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun y => (y : ℂ) * (wienerHopfSechOp f : ℝ → ℂ) y - (wienerHopfSechOp g : ℝ → ℂ) y :=
  SchurKernel.op_ae_eq_commutator wienerHopfSechKernel wienerHopfTiltKernel (fun y => (y : ℂ))
    (fun y z => by
      change ((sechSqHalfTilt (y - z) : ℝ) : ℂ) = ((y : ℂ) - z) * ((sechSqHalf (y - z) : ℝ) : ℂ)
      rw [sechSqHalfTilt]; push_cast; ring) f g hg

/-- **`U C_P U* = i[M_φ, A]` on the half-line.**  With the step clock `φ`, for `f ∈ L²(0,∞)` with
`φ f ∈ L²` (represented by `g`), `A_j f = φ · A f - A g` almost everywhere. -/
theorem mertensStepTiltOp_ae_eq_commutator (f g : L²₊)
    (hg : (g : ℝ → ℂ) =ᵐ[halfLineMeasure] fun y => (poissonClock y : ℂ) * f y) :
    (mertensStepTiltOp f : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun y => (poissonClock y : ℂ) * (mertensStepSechOp f : ℝ → ℂ) y -
        (mertensStepSechOp g : ℝ → ℂ) y :=
  SchurKernel.op_ae_eq_commutator mertensStepSechKernel mertensStepTiltKernel
    (fun y => (poissonClock y : ℂ))
    (fun y z => by
      change ((sechSqHalfTilt (poissonClock y - poissonClock z) : ℝ) : ℂ) =
        ((poissonClock y : ℂ) - poissonClock z) *
          ((sechSqHalf (poissonClock y - poissonClock z) : ℝ) : ℂ)
      rw [sechSqHalfTilt]; push_cast; ring) f g hg

/-! ### The prime clock commutator -/

/-- The prime clock commutator `C_P = i[X_P, K]` (bounded extension). -/
def poissonPrimeClockCommOp : ℓ²P →L[ℂ] ℓ²P := Complex.I • poissonPrimeCommOp

/-- **`C_P = i[X_P, K]` on finitely supported vectors.** -/
theorem poissonPrimeClockCommOp_core (s : Finset Nat.Primes) (c : Nat.Primes → ℂ)
    (p : Nat.Primes) :
    (poissonPrimeClockCommOp (∑ q ∈ s, c q • lpBasisVec q) : Nat.Primes → ℂ) p =
      Complex.I * ((mertensPrimeClock p : ℂ) *
          (poissonPrimeOp (∑ q ∈ s, c q • lpBasisVec q) : Nat.Primes → ℂ) p -
        (poissonPrimeOp (∑ q ∈ s, ((mertensPrimeClock q : ℂ) * c q) • lpBasisVec q) :
          Nat.Primes → ℂ) p) := by
  rw [mertensClock_mul_poissonPrimeOp_core, poissonPrimeClockCommOp, _root_.smul_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- `C_P` is self-adjoint. -/
theorem isSelfAdjoint_poissonPrimeClockCommOp : IsSelfAdjoint poissonPrimeClockCommOp := by
  change ContinuousLinearMap.adjoint poissonPrimeClockCommOp = poissonPrimeClockCommOp
  rw [poissonPrimeClockCommOp, LinearIsometryEquiv.map_smulₛₗ, adjoint_poissonPrimeCommOp,
    Complex.conj_I, smul_neg, neg_smul, neg_neg]

/-- `U C_P U* = i A_j`. -/
theorem primeCellOp_conj_poissonPrimeClockCommOp :
    primeCellOp ∘L poissonPrimeClockCommOp ∘L primeCellOp.adjoint =
      Complex.I • mertensStepTiltOp := by
  rw [poissonPrimeClockCommOp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    primeCellOp_conj_poissonPrimeCommOp]

/-! ### (3) The trace-class lift -/

/-- **(3)** `U C_P U* - P₊ J_full P₊ ∈ S₁`. -/
theorem memSchattenClass_one_primeClockComm_sub_compression :
    MemSchattenClass 1 (primeCellOp ∘L poissonPrimeClockCommOp ∘L primeCellOp.adjoint -
      halfLineRestrict ∘L thermalCommOp ∘L halfLineExtend) := by
  rw [primeCellOp_conj_poissonPrimeClockCommOp, halfLine_compression_thermalCommOp, ← smul_sub]
  exact memSchattenClass_one_smul memSchattenClass_one_mertensStepTiltOp_sub _

theorem isTraceClass_primeClockComm_sub_compression :
    ContinuousLinearMap.IsTraceClass (primeCellOp ∘L poissonPrimeClockCommOp ∘L
      primeCellOp.adjoint - halfLineRestrict ∘L thermalCommOp ∘L halfLineExtend) :=
  memSchattenClass_one_primeClockComm_sub_compression.one_isTraceClass

/-- The positive Gram: `U K U* - P₊ W_full P₊ ∈ S₁`. -/
theorem memSchattenClass_one_primeGram_sub_compression :
    MemSchattenClass 1 (primeCellOp ∘L poissonPrimeOp ∘L primeCellOp.adjoint -
      halfLineRestrict ∘L thermalConvOp ∘L halfLineExtend) := by
  rw [primeCellOp_conj_poissonPrimeOp, halfLine_compression_thermalConvOp]
  exact memSchattenClass_one_mertensStepSechOp_sub

/-! ### Trace-class closeness does not transfer the sign -/

section SignInstability

open _root_.HTGeometry

local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2

/-- The diagonal `2^{-n}`. -/
def dyadicDiagEntry (n : ℕ) : ℂ := (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)

/-- The diagonal `(-1)ⁿ 2^{-n}`. -/
def signedDyadicDiagEntry (n : ℕ) : ℂ := ((((-1 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ)

theorem norm_dyadicDiagEntry (n : ℕ) : ‖dyadicDiagEntry n‖ = (1 / 2 : ℝ) ^ n := by
  rw [dyadicDiagEntry, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem norm_signedDyadicDiagEntry (n : ℕ) : ‖signedDyadicDiagEntry n‖ = (1 / 2 : ℝ) ^ n := by
  rw [signedDyadicDiagEntry, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]

theorem norm_dyadicDiagEntry_le (n : ℕ) : ‖dyadicDiagEntry n‖ ≤ 1 := by
  rw [norm_dyadicDiagEntry]; exact pow_le_one₀ (by norm_num) (by norm_num)

theorem norm_signedDyadicDiagEntry_le (n : ℕ) : ‖signedDyadicDiagEntry n‖ ≤ 1 := by
  rw [norm_signedDyadicDiagEntry]; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- `L = diag(2^{-n})`. -/
def dyadicDiagOp : ℓ²ℕ →L[ℂ] ℓ²ℕ := ellTwoDiagonal dyadicDiagEntry norm_dyadicDiagEntry_le

/-- `L' = diag((-1)ⁿ 2^{-n})`. -/
def signedDyadicDiagOp : ℓ²ℕ →L[ℂ] ℓ²ℕ :=
  ellTwoDiagonal signedDyadicDiagEntry norm_signedDyadicDiagEntry_le

theorem summable_half_pow_sq : Summable fun n : ℕ => ((1 / 2 : ℝ) ^ n) ^ 2 := by
  simp_rw [← pow_mul, pow_mul']
  exact summable_geometric_of_lt_one (by positivity) (by norm_num)

theorem isSelfAdjoint_dyadicDiagOp : IsSelfAdjoint dyadicDiagOp := by
  change ContinuousLinearMap.adjoint dyadicDiagOp = dyadicDiagOp
  rw [dyadicDiagOp, adjoint_ellTwoDiagonal]
  congr 1
  funext n
  exact Complex.conj_ofReal _

theorem isSelfAdjoint_signedDyadicDiagOp : IsSelfAdjoint signedDyadicDiagOp := by
  change ContinuousLinearMap.adjoint signedDyadicDiagOp = signedDyadicDiagOp
  rw [signedDyadicDiagOp, adjoint_ellTwoDiagonal]
  congr 1
  funext n
  exact Complex.conj_ofReal _

theorem isCompactOperator_dyadicDiagOp : IsCompactOperator dyadicDiagOp :=
  ((isHilbertSchmidt_ellTwoDiagonal_iff _ _).mpr (by
    simp_rw [norm_dyadicDiagEntry]; exact summable_half_pow_sq)).isCompactOperator

theorem isCompactOperator_signedDyadicDiagOp : IsCompactOperator signedDyadicDiagOp :=
  ((isHilbertSchmidt_ellTwoDiagonal_iff _ _).mpr (by
    simp_rw [norm_signedDyadicDiagEntry]; exact summable_half_pow_sq)).isCompactOperator

/-- `(1/√2)ⁿ`, a square-summable factor of `2^{-n}`. -/
def halfSqrtEntry (n : ℕ) : ℂ := (((Real.sqrt (1 / 2)) ^ n : ℝ) : ℂ)

theorem norm_halfSqrtEntry (n : ℕ) : ‖halfSqrtEntry n‖ = Real.sqrt (1 / 2) ^ n := by
  rw [halfSqrtEntry, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem sqrt_half_le_one : Real.sqrt (1 / 2) ≤ 1 := by
  rw [Real.sqrt_le_one]; norm_num

theorem norm_halfSqrtEntry_le (n : ℕ) : ‖halfSqrtEntry n‖ ≤ 1 := by
  rw [norm_halfSqrtEntry]; exact pow_le_one₀ (Real.sqrt_nonneg _) sqrt_half_le_one

theorem summable_norm_halfSqrtEntry_sq : Summable fun n => ‖halfSqrtEntry n‖ ^ 2 := by
  simp_rw [norm_halfSqrtEntry, ← pow_mul, pow_mul', Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact summable_geometric_of_lt_one (by positivity) (by norm_num)

/-- The difference entry `(1 - (-1)ⁿ)(1/√2)ⁿ`. -/
def dyadicGapEntry (n : ℕ) : ℂ := (1 - (((-1 : ℝ) ^ n : ℝ) : ℂ)) * halfSqrtEntry n

theorem norm_dyadicGapEntry_le (n : ℕ) : ‖dyadicGapEntry n‖ ≤ 2 * Real.sqrt (1 / 2) ^ n := by
  rw [dyadicGapEntry, norm_mul, norm_halfSqrtEntry]
  gcongr
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow]
  norm_num

theorem norm_dyadicGapEntry_le_two (n : ℕ) : ‖dyadicGapEntry n‖ ≤ 2 :=
  (norm_dyadicGapEntry_le n).trans (by
    have := pow_le_one₀ (n := n) (Real.sqrt_nonneg (1 / 2)) sqrt_half_le_one; linarith)

theorem summable_norm_dyadicGapEntry_sq : Summable fun n => ‖dyadicGapEntry n‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_norm_halfSqrtEntry_sq.mul_left 4)
  rw [norm_halfSqrtEntry]
  calc ‖dyadicGapEntry n‖ ^ 2 ≤ (2 * Real.sqrt (1 / 2) ^ n) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_dyadicGapEntry_le n) 2
    _ = 4 * (Real.sqrt (1 / 2) ^ n) ^ 2 := by ring

theorem ellTwoDiagonal_congr_entries {a b : ℕ → ℂ} {C D : ℝ} (ha : ∀ n, ‖a n‖ ≤ C)
    (hb : ∀ n, ‖b n‖ ≤ D) (h : ∀ n, a n = b n) : ellTwoDiagonal a ha = ellTwoDiagonal b hb := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext n
  rw [ellTwoDiagonal_apply, ellTwoDiagonal_apply, h]

theorem ellTwoDiagonal_sub_ellTwoDiagonal (a b : ℕ → ℂ) {C D E : ℝ} (ha : ∀ n, ‖a n‖ ≤ C)
    (hb : ∀ n, ‖b n‖ ≤ D) (hab : ∀ n, ‖a n - b n‖ ≤ E) :
    ellTwoDiagonal a ha - ellTwoDiagonal b hb = ellTwoDiagonal (fun n => a n - b n) hab := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext n
  change ((ellTwoDiagonal a ha f - ellTwoDiagonal b hb f : ℓ²ℕ) : ℕ → ℂ) n = _
  rw [lp.coeFn_sub, Pi.sub_apply, ellTwoDiagonal_apply, ellTwoDiagonal_apply,
    ellTwoDiagonal_apply, sub_mul]

theorem dyadicDiagOp_sub_signedDyadicDiagOp :
    dyadicDiagOp - signedDyadicDiagOp =
      ellTwoDiagonal halfSqrtEntry norm_halfSqrtEntry_le ∘L
        ellTwoDiagonal dyadicGapEntry norm_dyadicGapEntry_le_two := by
  have hE : ∀ n, ‖dyadicDiagEntry n - signedDyadicDiagEntry n‖ ≤ 2 := fun n =>
    (norm_sub_le _ _).trans (by
      linarith [norm_dyadicDiagEntry_le n, norm_signedDyadicDiagEntry_le n])
  have hP : ∀ n, ‖halfSqrtEntry n * dyadicGapEntry n‖ ≤ 2 := fun n => by
    rw [norm_mul]
    have := norm_halfSqrtEntry_le n
    have := norm_dyadicGapEntry_le_two n
    nlinarith [norm_nonneg (halfSqrtEntry n), norm_nonneg (dyadicGapEntry n)]
  rw [dyadicDiagOp, signedDyadicDiagOp, ellTwoDiagonal_sub_ellTwoDiagonal _ _ _ _ hE,
    ellTwoDiagonal_comp _ _ _ _ hP]
  refine ellTwoDiagonal_congr_entries _ _ fun n => ?_
  rw [dyadicDiagEntry, signedDyadicDiagEntry, dyadicGapEntry, halfSqrtEntry]
  have h : (Real.sqrt (1 / 2) ^ n) * (Real.sqrt (1 / 2) ^ n) = (1 / 2 : ℝ) ^ n := by
    rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
  have hc : ((Real.sqrt (1 / 2) ^ n : ℝ) : ℂ) * ((Real.sqrt (1 / 2) ^ n : ℝ) : ℂ) =
      (((1 / 2 : ℝ) ^ n : ℝ) : ℂ) := by exact_mod_cast h
  push_cast at hc ⊢
  linear_combination (-(1 - (-1 : ℂ) ^ n)) * hc

/-- **`L - L'` is trace class.** -/
theorem isTraceClass_dyadicDiagOp_sub : ContinuousLinearMap.IsTraceClass (dyadicDiagOp - signedDyadicDiagOp) :=
  ⟨_, _, (isHilbertSchmidt_ellTwoDiagonal_iff _ _).mpr summable_norm_halfSqrtEntry_sq,
    (isHilbertSchmidt_ellTwoDiagonal_iff _ _).mpr summable_norm_dyadicGapEntry_sq,
    dyadicDiagOp_sub_signedDyadicDiagOp⟩

theorem memSchattenClass_one_dyadicDiagOp_sub : MemSchattenClass 1 (dyadicDiagOp - signedDyadicDiagOp) :=
  IsTraceClass.memSchattenClass_one isTraceClass_dyadicDiagOp_sub

theorem norm_sign_entry_le (d : ℕ → ℝ) (n : ℕ) : ‖((SignType.sign (d n) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases lt_trichotomy (d n) 0 with h | h | h
  · simp [sign_neg h]
  · simp [h]
  · simp [sign_pos h]

/-- The sign of a real diagonal operator in its Borel calculus: `diag(sgn dₙ)`. -/
def diagSignOp (d : ℕ → ℝ) : ℓ²ℕ →L[ℂ] ℓ²ℕ :=
  ellTwoDiagonal (fun n => ((SignType.sign (d n) : ℝ) : ℂ)) (norm_sign_entry_le d)

/-- `sgn L = 1`. -/
theorem diagSignOp_dyadic : diagSignOp (fun n => (1 / 2 : ℝ) ^ n) = ContinuousLinearMap.id ℂ ℓ²ℕ := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext n
  rw [diagSignOp, ellTwoDiagonal_apply, sign_pos (by positivity)]
  simp

/-- `sgn L' e_n = (-1)ⁿ e_n`. -/
theorem diagSignOp_signedDyadic_apply (f : ℓ²ℕ) (n : ℕ) :
    (diagSignOp (fun n => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) f) n = (-1 : ℂ) ^ n * f n := by
  rw [diagSignOp, ellTwoDiagonal_apply]
  congr 1
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, one_mul, sign_pos (by positivity), h.neg_one_pow]; simp
  · rw [h.neg_one_pow, neg_one_mul, sign_neg (by
      have : 0 < (1 / 2 : ℝ) ^ n := by positivity
      linarith), h.neg_one_pow]; simp

/-- `sgn L - sgn L' = diag(sgn 2^{-n} - sgn((-1)ⁿ 2^{-n}))`. -/
theorem diagSign_sub_eq :
    diagSignOp (fun n => (1 / 2 : ℝ) ^ n) - diagSignOp (fun n => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) =
      ellTwoDiagonal (fun n => ((SignType.sign ((1 / 2 : ℝ) ^ n) : ℝ) : ℂ) -
        ((SignType.sign ((-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) : ℝ) : ℂ))
        (fun n => (norm_sub_le _ _).trans (add_le_add (norm_sign_entry_le _ n)
          (norm_sign_entry_le (fun n => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) n))) :=
  ellTwoDiagonal_sub_ellTwoDiagonal _ _ _ _ _

/-- **`sgn L - sgn L'` is not compact.** -/
theorem not_isCompactOperator_diagSign_sub :
    ¬ IsCompactOperator (diagSignOp (fun n => (1 / 2 : ℝ) ^ n) -
      diagSignOp (fun n => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n)) := by
  intro hK
  have hon : Orthonormal ℂ fun k : ℕ => (ellTwoCoordinateBasis ℕ (2 * k + 1) : ℓ²ℕ) :=
    (ellTwoCoordinateBasis ℕ).orthonormal.comp _ fun a b h => by omega
  have ht := tendsto_norm_compactOperator_apply_orthonormal hK hon
  have hval : ∀ k : ℕ, ‖(diagSignOp (fun n => (1 / 2 : ℝ) ^ n) -
      diagSignOp (fun n => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n)) (ellTwoCoordinateBasis ℕ (2 * k + 1))‖
        = 2 := by
    intro k
    rw [diagSign_sub_eq, norm_ellTwoDiagonal_coordinateBasis,
      (odd_two_mul_add_one k).neg_one_pow, sign_pos (by positivity),
      sign_neg (by have : 0 < (1 / 2 : ℝ) ^ (2 * k + 1) := by positivity
                   linarith)]
    norm_num
  have : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 0) := ht.congr hval
  exact absurd (tendsto_nhds_unique this tendsto_const_nhds) (by norm_num)

/-- **Sign instability.**  Two compact self-adjoint operators with trace-class difference whose
signs differ by a noncompact operator. -/
theorem sign_not_stable_under_traceClass :
    IsSelfAdjoint dyadicDiagOp ∧ IsSelfAdjoint signedDyadicDiagOp ∧
    IsCompactOperator dyadicDiagOp ∧ IsCompactOperator signedDyadicDiagOp ∧
    MemSchattenClass 1 (dyadicDiagOp - signedDyadicDiagOp) ∧
    ¬ IsCompactOperator (diagSignOp (fun n => (1 / 2 : ℝ) ^ n) -
      diagSignOp (fun n => (-1 : ℝ) ^ n * (1 / 2 : ℝ) ^ n)) :=
  ⟨isSelfAdjoint_dyadicDiagOp, isSelfAdjoint_signedDyadicDiagOp, isCompactOperator_dyadicDiagOp,
    isCompactOperator_signedDyadicDiagOp, memSchattenClass_one_dyadicDiagOp_sub,
    not_isCompactOperator_diagSign_sub⟩

/-- The diagonal entries of `L`, `L'` are those of `diagSignOp`'s arguments. -/
theorem dyadicDiagOp_eq : dyadicDiagOp = ellTwoDiagonal (fun n => (((1 / 2 : ℝ) ^ n : ℝ) : ℂ))
    norm_dyadicDiagEntry_le := rfl

theorem signedDyadicDiagOp_eq : signedDyadicDiagOp =
    ellTwoDiagonal (fun n => ((((-1 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ))
      norm_signedDyadicDiagEntry_le := rfl

end SignInstability

end RHTower
