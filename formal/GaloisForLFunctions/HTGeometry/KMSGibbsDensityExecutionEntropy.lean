import GaloisForLFunctions.HTGeometry.ResetHasseExecutionDefect
import GaloisForLFunctions.HTGeometry.ResetBilateralDilation
import GaloisForLFunctions.HTGeometry.ConstitutiveInvariantPositivityKMSWall
import GaloisForLFunctions.HTGeometry.HaarRankEntropyFormation
import GaloisForLFunctions.HTGeometry.CfcEigenvectorRankOneAssembly
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator

/-!
# Execution entropy equals KMS state entropy; the reversibilization trilemma

The Toeplitz Gibbs density operator `ρ_q = (1 - q) q^N` is diagonal in the depth basis of
`ℓ²(ℕ)` with eigenvalues the KMS layer masses `p_q(n) = (1 - q) q^n`, and the Toeplitz Gibbs state
is `a ↦ Tr(ρ_q a)`.

* **Theorem 8.3, `(RFDM.38a)`–`(RFDM.38d)`**: `Tr ρ_q² = (1-q)/(1+q)`, so the linear entropy
  `1 - Tr ρ_q²` is the total-variation execution defect, and the von Neumann entropy
  `-Tr(ρ_q log ρ_q)` (real continuous functional calculus of `x log x`, trace of a
  Hilbert–Schmidt product) and the singular-value entropy `∑ η(s_n(ρ_q))` both equal the
  directed-KL execution defect `D(Δ_{p_q} ‖ p_q ⊗ p_q)`.
* **Corollary 8.4, `(RFDM.39)`**: at every `0 < q < 1`: a KMS state on an algebra in which the
  isometry becomes unitary forces `q = 1`; a fresh geometric reset has no finite-order
  deterministic execution and its attempted closure has the exact defects of Theorem 8.2; the
  bilateral dilation executes it reversibly and preserves endpoint information.
-/

open MeasureTheory InformationTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ResetDilation

open _root_.RHTower (EllTwo diagonalOperator diagonalOperator_apply)

/-! ### Diagonal operators on `ℓ²(ℕ)` -/

section Diagonal

theorem diagonalOperator_single (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C) (n : ℕ) :
    diagonalOperator lam hC (lp.single 2 n 1) = lam n • lp.single 2 n (1 : ℂ) := by
  refine lp.ext (funext fun k => ?_)
  rw [diagonalOperator_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases hk : k = n
  · subst hk; simp
  · simp [hk]

theorem norm_le_sqrt_tsum_sq {lam : ℕ → ℂ} (h : Summable fun n => ‖lam n‖ ^ 2) (n : ℕ) :
    ‖lam n‖ ≤ Real.sqrt (∑' m, ‖lam m‖ ^ 2) :=
  Real.le_sqrt_of_sq_le (h.le_tsum n fun _ _ => sq_nonneg _)

theorem isHilbertSchmidt_diagonalOperator {lam : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C)
    (h : Summable fun n => ‖lam n‖ ^ 2) : IsHilbertSchmidt (diagonalOperator lam hC) := by
  refine isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis ℕ) (h.congr fun n => ?_)
  rw [HilbertSchmidt.lpBasis_apply, diagonalOperator_single, norm_smul,
    lp.norm_single (by norm_num), norm_one, mul_one]

theorem diagonalOperator_comp {lam mu : ℕ → ℂ} {C D E : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C)
    (hD : ∀ n, ‖mu n‖ ≤ D) (hE : ∀ n, ‖lam n * mu n‖ ≤ E) :
    diagonalOperator lam hC ∘L diagonalOperator mu hD =
      diagonalOperator (fun n => lam n * mu n) hE := by
  ext1 f
  refine lp.ext (funext fun n => ?_)
  simp only [comp_apply, diagonalOperator_apply, mul_assoc]

theorem inner_single_smul_single (c : ℂ) (n : ℕ) :
    ⟪(lp.single 2 n (1 : ℂ) : EllTwo), c • (lp.single 2 n (1 : ℂ) : EllTwo)⟫_ℂ = c := by
  rw [lp.inner_single_left, lp.coeFn_smul, Pi.smul_apply, lp.single_apply_self, smul_eq_mul,
    mul_one, RCLike.inner_apply, map_one, mul_one]

/-- The trace of a product of two Hilbert–Schmidt diagonal operators is the sum of the products of
their diagonal entries. -/
theorem opTrace_diagonalOperator_comp {lam mu : ℕ → ℂ} {C D : ℝ} (hC : ∀ n, ‖lam n‖ ≤ C)
    (hD : ∀ n, ‖mu n‖ ≤ D) (hl : Summable fun n => ‖lam n‖ ^ 2)
    (hm : Summable fun n => ‖mu n‖ ^ 2) :
    opTrace (diagonalOperator lam hC ∘L diagonalOperator mu hD) = ∑' n, lam n * mu n := by
  rw [opTrace_comp_eq_tsum_basis (isHilbertSchmidt_diagonalOperator hC hl)
    (isHilbertSchmidt_diagonalOperator hD hm) (HilbertSchmidt.lpBasis ℕ)]
  refine tsum_congr fun n => ?_
  rw [HilbertSchmidt.lpBasis_apply, comp_apply, diagonalOperator_single, map_smul,
    diagonalOperator_single, smul_smul, mul_comm, inner_single_smul_single]

/-- A diagonal operator with real entries is self-adjoint. -/
theorem isSelfAdjoint_diagonalOperator_ofReal {r : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, ‖((r n : ℝ) : ℂ)‖ ≤ C) :
    IsSelfAdjoint (diagonalOperator (fun n => ((r n : ℝ) : ℂ)) hC) := by
  rw [isSelfAdjoint_iff_isSymmetric]
  intro f g
  simp only [coe_coe]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [diagonalOperator_apply, diagonalOperator_apply, RCLike.inner_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal]
  ring

/-- Real continuous functional calculus `g(A)` of an operator on a complex Hilbert space. -/
def realCFC {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (g : ℝ → ℝ) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  cfc g A

/-- `g(A) x = g(c) x` on an eigenvector `A x = c x` of a self-adjoint `A`. -/
theorem realCFC_apply_eigenvector {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {c : ℝ} {x : H}
    (hx : A x = (c : ℂ) • x) {g : ℝ → ℝ} (hg : Continuous g) :
    realCFC g A x = ((g c : ℝ) : ℂ) • x :=
  cfc_apply_eigenvector_rankOne A hA hx hg.continuousOn

/-- Two bounded operators on `ℓ²(ℕ)` agreeing on the standard basis are equal. -/
theorem ext_lpSingle {A B : EllTwo →L[ℂ] EllTwo}
    (h : ∀ n, A (lp.single 2 n 1) = B (lp.single 2 n 1)) : A = B := by
  refine ContinuousLinearMap.ext_on (s := Set.range (HilbertSchmidt.lpBasis ℕ))
    (Submodule.dense_iff_topologicalClosure_eq_top.2 (HilbertSchmidt.lpBasis ℕ).dense_span) ?_
  rintro _ ⟨n, rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  exact h n

/-- **Functional calculus of a real diagonal operator** is the diagonal operator of the values:
`g(diag r) = diag(g ∘ r)` for every continuous `g`. -/
theorem realCFC_diagonalOperator_ofReal {r : ℕ → ℝ} {C : ℝ}
    (hC : ∀ n, ‖((r n : ℝ) : ℂ)‖ ≤ C) {g : ℝ → ℝ} (hg : Continuous g) {D : ℝ}
    (hD : ∀ n, ‖((g (r n) : ℝ) : ℂ)‖ ≤ D) :
    realCFC g (diagonalOperator (fun n => ((r n : ℝ) : ℂ)) hC) =
      diagonalOperator (fun n => ((g (r n) : ℝ) : ℂ)) hD := by
  refine ext_lpSingle fun n => ?_
  rw [realCFC_apply_eigenvector _ (isSelfAdjoint_diagonalOperator_ofReal hC)
    (diagonalOperator_single _ hC n) hg, diagonalOperator_single]

end Diagonal

/-! ### The Toeplitz Gibbs density operator -/

section Gibbs

variable {q : ℝ}

theorem geometricLayerMass_antitone (hq0 : 0 ≤ q) (hq1 : q < 1) {i j : ℕ} (hij : i ≤ j) :
    geometricLayerMass q j ≤ geometricLayerMass q i :=
  mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1.le hij) (sub_nonneg.2 hq1.le)

/-- **`(RFDM.38a)`** the Toeplitz Gibbs density operator `ρ_q = (1 - q) q^N`. -/
def gibbsDensity (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : EllTwo →L[ℂ] EllTwo :=
  _root_.RHTower.antitoneDiagonalOperator (geometricLayerMass q)
    (geometricLayerMass_nonneg hq0 hq1) (geometricLayerMass_antitone hq0 hq1)

theorem norm_geometricLayerMass_le (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ‖((geometricLayerMass q n : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (geometricLayerMass_nonneg hq0 hq1 n)]
  exact geometricLayerMass_le_one hq0 hq1 n

theorem gibbsDensity_eq (hq0 : 0 ≤ q) (hq1 : q < 1) :
    gibbsDensity q hq0 hq1 = diagonalOperator (fun n => ((geometricLayerMass q n : ℝ) : ℂ))
      (norm_geometricLayerMass_le hq0 hq1) :=
  ext_lpSingle fun n => by
    rw [gibbsDensity, _root_.RHTower.antitoneDiagonalOperator, diagonalOperator_single,
      diagonalOperator_single]

/-- The depth basis diagonalizes `ρ_q` with eigenvalues the KMS layer masses. -/
theorem gibbsDensity_single (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    gibbsDensity q hq0 hq1 (lp.single 2 n 1) =
      ((geometricLayerMass q n : ℝ) : ℂ) • lp.single 2 n (1 : ℂ) := by
  rw [gibbsDensity_eq, diagonalOperator_single]

theorem summable_norm_sq_geometricLayerMass (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n => ‖((geometricLayerMass q n : ℝ) : ℂ)‖ ^ 2 := by
  refine ((summable_geometricLayerMass hq0 hq1).mul_left 1).of_nonneg_of_le
    (fun _ => sq_nonneg _) fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, one_mul]
  exact mul_le_of_le_one_left (geometricLayerMass_nonneg hq0 hq1 n)
    (geometricLayerMass_le_one hq0 hq1 n)

theorem norm_sqrt_geometricLayerMass_le (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ‖((Real.sqrt (geometricLayerMass q n) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (geometricLayerMass_le_one hq0 hq1 n)

theorem summable_norm_sq_sqrt_geometricLayerMass (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n => ‖((Real.sqrt (geometricLayerMass q n) : ℝ) : ℂ)‖ ^ 2 :=
  (summable_geometricLayerMass hq0 hq1).congr fun n => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (geometricLayerMass_nonneg hq0 hq1 n)]

/-- `ρ_q = D ∘ D` with `D = diag(√p_q)` Hilbert–Schmidt. -/
theorem gibbsDensity_eq_sqrt_comp (hq0 : 0 ≤ q) (hq1 : q < 1) :
    gibbsDensity q hq0 hq1 =
      diagonalOperator (fun n => ((Real.sqrt (geometricLayerMass q n) : ℝ) : ℂ))
          (norm_sqrt_geometricLayerMass_le hq0 hq1) ∘L
        diagonalOperator (fun n => ((Real.sqrt (geometricLayerMass q n) : ℝ) : ℂ))
          (norm_sqrt_geometricLayerMass_le hq0 hq1) := by
  rw [diagonalOperator_comp _ _ (fun n => by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (geometricLayerMass_nonneg hq0 hq1 n)]
      exact norm_geometricLayerMass_le hq0 hq1 n), gibbsDensity_eq]
  congr 1
  funext n
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (geometricLayerMass_nonneg hq0 hq1 n)]

/-- **`(RFDM.38a)`** the Toeplitz Gibbs state is `a ↦ Tr(ρ_q a)`. -/
theorem toeplitzGibbsState_eq_opTrace (hq0 : 0 ≤ q) (hq1 : q < 1)
    (a : ToeplitzSpace →L[ℂ] ToeplitzSpace) :
    toeplitzGibbsState q a = opTrace (gibbsDensity q hq0 hq1 ∘L a) := by
  set D := diagonalOperator (fun n => ((Real.sqrt (geometricLayerMass q n) : ℝ) : ℂ))
    (norm_sqrt_geometricLayerMass_le hq0 hq1)
  have hD : IsHilbertSchmidt D := isHilbertSchmidt_diagonalOperator _
    (summable_norm_sq_sqrt_geometricLayerMass hq0 hq1)
  rw [gibbsDensity_eq_sqrt_comp, comp_assoc,
    opTrace_comp_eq_tsum_basis hD (hD.comp_right a) (HilbertSchmidt.lpBasis ℕ),
    toeplitzGibbsState]
  refine tsum_congr fun n => ?_
  rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one,
    comp_apply, comp_apply, diagonalOperator_apply, diagonalOperator_apply, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (geometricLayerMass_nonneg hq0 hq1 n)]
  simp only [geometricLayerMass, basisVec]
  push_cast
  rfl

/-- **Theorem 8.3, `(RFDM.38b)`**: `Tr ρ_q² = (1 - q)/(1 + q)`. -/
theorem opTrace_gibbsDensity_sq (hq0 : 0 ≤ q) (hq1 : q < 1) :
    opTrace (gibbsDensity q hq0 hq1 ∘L gibbsDensity q hq0 hq1) =
      (((1 - q) / (1 + q) : ℝ) : ℂ) := by
  rw [gibbsDensity_eq, opTrace_diagonalOperator_comp _ _
    (summable_norm_sq_geometricLayerMass hq0 hq1) (summable_norm_sq_geometricLayerMass hq0 hq1),
    ← tsum_sq_geometricLayerMass hq0 hq1, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  push_cast
  ring

/-- **Theorem 8.3, `(RFDM.38c)`**: the linear entropy `1 - Tr ρ_q²` is the total-variation
execution defect. -/
theorem one_sub_purity_gibbsDensity (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 - (opTrace (gibbsDensity q hq0 hq1 ∘L gibbsDensity q hq0 hq1)).re =
      FormationExcess.totalVariation (diagonalVector (geometricLayerPMF q hq0 hq1))
        (productVector (geometricLayerPMF q hq0 hq1)) := by
  rw [opTrace_gibbsDensity_sq, Complex.ofReal_re, geometricLayer_totalVariation,
    geometricExecutionTV_eq_one_sub_purity hq0 hq1, tsum_sq_geometricLayerMass hq0 hq1]

theorem summable_geometricLayerMass_mul_log_sq (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n => geometricLayerMass q n * Real.log (geometricLayerMass q n) ^ 2 := by
  have hn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hn
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  refine (((h0.mul_left ((1 - q) * Real.log (1 - q) ^ 2)).add
    (h1.mul_left (2 * (1 - q) * Real.log (1 - q) * Real.log q))).add
    (h2.mul_left ((1 - q) * Real.log q ^ 2))).congr fun n => ?_
  simp only [geometricLayerMass]
  rw [Real.log_mul (sub_pos.2 hq1).ne' (pow_ne_zero n hq0.ne'), Real.log_pow]
  ring

/-- The entries `√p_n log p_n` of the second factor of `ρ_q log ρ_q`. -/
def sqrtMassLog (q : ℝ) (n : ℕ) : ℂ :=
  ((Real.sqrt (geometricLayerMass q n) * Real.log (geometricLayerMass q n) : ℝ) : ℂ)

theorem summable_norm_sq_sqrtMassLog (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n => ‖sqrtMassLog q n‖ ^ 2 :=
  (summable_geometricLayerMass_mul_log_sq hq0 hq1).congr fun n => by
    rw [sqrtMassLog, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt (geometricLayerMass_nonneg hq0.le hq1 n)]

/-- **Theorem 8.3, `(RFDM.38d)`**: the von Neumann entropy `-Tr(ρ_q log ρ_q)`, with `ρ log ρ` the
continuous functional calculus of `x log x`, is `-log(1-q) - q/(1-q) log q`. -/
theorem opTrace_cfc_mul_log_gibbsDensity (hq0 : 0 < q) (hq1 : q < 1) :
    -opTrace (realCFC (fun x : ℝ => x * Real.log x) (gibbsDensity q hq0.le hq1)) =
      ((geometricExecutionEntropy q : ℝ) : ℂ) := by
  have hE : ∀ n, ‖((Real.sqrt (geometricLayerMass q n) : ℝ) : ℂ) * sqrtMassLog q n‖ ≤
      Real.sqrt (∑' m, ‖sqrtMassLog q m‖ ^ 2) := fun n => by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (norm_sqrt_geometricLayerMass_le hq0.le hq1 n)).trans
        (norm_le_sqrt_tsum_sq (summable_norm_sq_sqrtMassLog hq0 hq1) n)
  have hfac : ∀ n, ((Real.sqrt (geometricLayerMass q n) : ℝ) : ℂ) * sqrtMassLog q n =
      ((geometricLayerMass q n * Real.log (geometricLayerMass q n) : ℝ) : ℂ) := fun n => by
    rw [sqrtMassLog, ← Complex.ofReal_mul, ← mul_assoc,
      Real.mul_self_sqrt (geometricLayerMass_nonneg hq0.le hq1 n)]
  have hcfc : realCFC (fun x : ℝ => x * Real.log x) (gibbsDensity q hq0.le hq1) =
      diagonalOperator (fun n => ((Real.sqrt (geometricLayerMass q n) : ℝ) : ℂ))
          (norm_sqrt_geometricLayerMass_le hq0.le hq1) ∘L
        diagonalOperator (sqrtMassLog q)
          (norm_le_sqrt_tsum_sq (summable_norm_sq_sqrtMassLog hq0 hq1)) := by
    rw [diagonalOperator_comp _ _ hE, gibbsDensity_eq,
      realCFC_diagonalOperator_ofReal _ Real.continuous_mul_log
        (fun n => by rw [← hfac]; exact hE n)]
    congr 1
    funext n
    rw [hfac]
  rw [hcfc, opTrace_diagonalOperator_comp _ _ (summable_norm_sq_sqrt_geometricLayerMass hq0.le hq1)
    (summable_norm_sq_sqrtMassLog hq0 hq1), ← tsum_geometricLayerShannonTerm hq0 hq1,
    Complex.ofReal_tsum, ← tsum_neg]
  refine tsum_congr fun n => ?_
  rw [hfac, geometricLayerShannonTerm]
  push_cast
  ring

/-- **Theorem 8.3**: the singular-value von Neumann entropy `∑ η(s_n(ρ_q))` is the same. -/
theorem vonNeumannEntropy_gibbsDensity (hq0 : 0 < q) (hq1 : q < 1) :
    vonNeumannEntropy (gibbsDensity q hq0.le hq1) = geometricExecutionEntropy q := by
  rw [vonNeumannEntropy, ← tsum_geometricLayerShannonTerm hq0 hq1]
  refine tsum_congr fun n => ?_
  rw [gibbsDensity, _root_.RHTower.approxNumber_antitoneDiagonalOperator_eq, Real.negMulLog_def,
    geometricLayerShannonTerm]

/-- **Theorem 8.3, `(RFDM.38c)`–`(RFDM.38d)`**: state mixedness and failure of finite path
closure are the same two scalar laws: the linear entropy is the total-variation execution defect,
and the von Neumann entropy is the directed-KL execution defect. -/
theorem execution_entropy_eq_kms_entropy (hq0 : 0 < q) (hq1 : q < 1) :
    1 - (opTrace (gibbsDensity q hq0.le hq1 ∘L gibbsDensity q hq0.le hq1)).re =
        FormationExcess.totalVariation (diagonalVector (geometricLayerPMF q hq0.le hq1))
          (productVector (geometricLayerPMF q hq0.le hq1)) ∧
      klDiv (diagonalCoupling (geometricLayerPMF q hq0.le hq1))
          (productCoupling (geometricLayerPMF q hq0.le hq1)) =
        ENNReal.ofReal
          (-opTrace (realCFC (fun x : ℝ => x * Real.log x) (gibbsDensity q hq0.le hq1))).re ∧
      klDiv (diagonalCoupling (geometricLayerPMF q hq0.le hq1))
          (productCoupling (geometricLayerPMF q hq0.le hq1)) =
        ENNReal.ofReal (vonNeumannEntropy (gibbsDensity q hq0.le hq1)) := by
  refine ⟨one_sub_purity_gibbsDensity hq0.le hq1, ?_, ?_⟩
  · rw [opTrace_cfc_mul_log_gibbsDensity hq0 hq1, Complex.ofReal_re,
      geometricLayer_klDiv_diagonal_product hq0 hq1]
  · rw [vonNeumannEntropy_gibbsDensity hq0 hq1, geometricLayer_klDiv_diagonal_product hq0 hq1]

end Gibbs

/-! ### Corollary 8.4: quotient, finite lift, or infinite dilation -/

section Trilemma

variable {q : ℝ} {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {R : X → X}

/-- The fresh geometric layer reset: every observer recovers the KMS layer law `p_q`. -/
def layerResetKernel (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : Kernel X ℕ :=
  Kernel.const X (geometricLayerPMF q hq0 hq1).toMeasure

instance (hq0 : 0 ≤ q) (hq1 : q < 1) : IsMarkovKernel (layerResetKernel (X := X) q hq0 hq1) := by
  unfold layerResetKernel; infer_instance

/-- **Corollary 8.4, `(RFDM.39)`** at every `0 < q < 1`:
1. *reversible quotient*: no KMS state with modular eigenvalue `q` survives on an algebra in which
   the history isometry becomes unitary;
2. *finite-order lift*: the fresh geometric reset has no finite-order deterministic execution, and
   its attempted closure has the exact defects `2q/(1+q)`, `-log(1-q) - q/(1-q) log q`, `∞`;
3. *infinite dilation*: the bilateral dilation executes the reset reversibly with the reset
   finite-dimensional laws and preserves endpoint information exactly. -/
theorem reversibilization_trilemma [Nonempty X] (hq0 : 0 < q) (hq1 : q < 1) (hR : Measurable R)
    (hinv : ∀ x, R (R x) = x) :
    (∀ {A : Type*} [Ring A] [Algebra ℂ A] (φ : A →ₗ[ℂ] ℂ) (σ : A →ₐ[ℂ] A),
      (∀ a b : A, φ (a * b) = φ (b * σ a)) → ∀ {u w : A}, σ u = (q : ℂ) • u → w * u = 1 →
        φ 1 = 1 → u * w ≠ 1) ∧
    ((∀ {Z : Type*} [MeasurableSpace Z]
        (E : ResetExecution (layerResetKernel (X := X) q hq0.le hq1) R hR Z) (N : ℕ),
        0 < N → E.T^[N] ≠ id) ∧
      FormationExcess.totalVariation (diagonalVector (geometricLayerPMF q hq0.le hq1))
          (productVector (geometricLayerPMF q hq0.le hq1)) = geometricExecutionTV q ∧
      klDiv (diagonalCoupling (geometricLayerPMF q hq0.le hq1))
          (productCoupling (geometricLayerPMF q hq0.le hq1)) =
        ENNReal.ofReal (geometricExecutionEntropy q) ∧
      klDiv (productCoupling (geometricLayerPMF q hq0.le hq1))
          (diagonalCoupling (geometricLayerPMF q hq0.le hq1)) = ⊤) ∧
    ((∀ x k, (dilationSource x).map
        (fun z (j : Fin (k + 1)) =>
          dilationPacket (layerResetKernel (X := X) q hq0.le hq1) ((dilationMap R)^[j] z)) =
        markovPath (splitFormation (Measure.dirac x) (layerResetKernel q hq0.le hq1))
          (formationLiftKernel (layerResetKernel q hq0.le hq1) R hR) k) ∧
      ∀ (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
        klDiv ((μ.prod historyLaw).map (dilationMap R)) ((ν.prod historyLaw).map (dilationMap R)) =
          klDiv μ ν ∧
        klDiv ((μ.prod historyLaw).map (dilationPacket (layerResetKernel q hq0.le hq1)))
          ((ν.prod historyLaw).map (dilationPacket (layerResetKernel q hq0.le hq1))) =
          klDiv μ ν) := by
  have hnd : ¬ ∃ n, (geometricLayerPMF q hq0.le hq1).toMeasure = Measure.dirac n := by
    rintro ⟨n, hn⟩
    have h := congrArg (fun m : Measure ℕ => m {n + 1}) hn
    simp only [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
      geometricLayerPMF_apply, Measure.dirac_apply' _ (MeasurableSet.singleton _),
      Set.indicator_of_notMem (show n ∉ ({n + 1} : Set ℕ) by simp)] at h
    exact (ENNReal.ofReal_pos.2 (geometricLayerMass_pos hq0 hq1 (n + 1))).ne' h
  refine ⟨fun φ σ hexch u w hσ hiso hone hunit => ?_, ⟨fun E N hN hper => ?_,
    geometricLayer_totalVariation _ _, geometricLayer_klDiv_diagonal_product hq0 hq1,
    geometricLayer_klDiv_product_diagonal hq0 hq1⟩, fun x k => ?_, fun μ ν _ _ => ?_⟩
  · have h := kms_forces_q_eq_one φ σ hexch hσ hiso hunit hone
    exact hq1.ne (by exact_mod_cast h)
  · obtain ⟨-, n, hn⟩ := resetExecution_not_periodic E hN hper
      (Classical.arbitrary X)
    exact hnd ⟨n, hn⟩
  · exact (resetDilation _ R hR hinv).fdd x k
  · obtain ⟨-, h2, h3⟩ := dilation_information_neutral (layerResetKernel q hq0.le hq1) R hR hinv μ ν
    exact ⟨h2, h3⟩

end Trilemma

end GaloisForLFunctions.HTGeometry.ResetDilation
