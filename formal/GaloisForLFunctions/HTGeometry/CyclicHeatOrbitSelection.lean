import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitCost
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.RHTower.SchattenTwoIdentity
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeCyclicExtension
import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.RHTower.RectangularSemilocalObserverTailSeparation

/-!
# Endogenous-cost selection for a cyclic heat source

For a positive trace-class operator `T` the extended orbit cost is
`E_G(T) = Σ_k γ_k^{-1} ⟨f_k, T f_k⟩ ∈ [0, ∞]` (**(OG.18)**), and `tr T ≤ ‖G‖ E_G(T)` (**(OG.31)**).

**Selection (OG.21).**  If positive trace-class `T_n` satisfy
`‖[T_n, D]‖₁ + ‖[T_n, P]‖₁ → 0` (**(OG.19)**) and `sup_n E_G(T_n) < ∞` (**(OG.20)**), then
`‖T_n‖₁ = tr T_n → 0`.

Proof.  The matrices of the `T_n` are bounded in `ℓ²(ι × ι)` by `tr T_n`.  Any weak limit `w` of a
subsequence is annihilated by both commutator constraints: the `D`-constraint
`(d_j - d_i) w(i,j) = 0` kills the off-diagonal entries (simple spectrum), the `P`-constraint
`v_i v̄_j (w(i,i) - w(j,j)) = 0` makes the diagonal constant (full support), and a constant diagonal
is square summable over an infinite index set only when it vanishes.  Hence `⟨x, T_n y⟩ → 0` for
all `x, y`, so the trace over the finitely many eigenvectors with `γ_k ≥ ε` tends to zero, while
the remaining trace is at most `ε E_G(T_n)` (**(OG.33)–(OG.34)**).
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*}

local notation "ℓ²ι" => lp (fun _ : ι => ℂ) 2
local notation "ℓ²ιι" => lp (fun _ : ι × ι => ℂ) 2

/-! ## Hilbert–Schmidt norm and trace norm -/

theorem hsNormSq_le_traceNorm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) :
    ContinuousLinearMap.hsNormSq T ≤ traceNorm H T ^ 2 := by
  have hs := hT.one_summable_approxNumber
  rw [hsNormSq_eq_tsum_approxNumber_sq hT.one_isHilbertSchmidt, traceNorm, sq,
    ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) ?_ (hs.mul_left _)
  · rw [sq]
    exact mul_le_mul_of_nonneg_right (hs.le_tsum n fun m _ => approxNumber_nonneg T m)
      (approxNumber_nonneg T n)
  · exact (hs.mul_left (∑' m, approxNumber T m)).of_nonneg_of_le (fun n => sq_nonneg _) fun n => by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hs.le_tsum n fun m _ => approxNumber_nonneg T m)
        (approxNumber_nonneg T n)

/-! ## The matrix bridge -/

section Matrix

theorem memℓp_testMatrix (x y : ℓ²ι) : Memℓp (fun p : ι × ι => x p.1 * starRingEnd ℂ (y p.2)) 2 := by
  refine memℓp_gen ?_
  have h : Summable fun p : ι × ι => ‖x p.1‖ ^ 2 * ‖y p.2‖ ^ 2 :=
    (summable_norm_sq_lp x).mul_of_nonneg (summable_norm_sq_lp y) (fun _ => sq_nonneg _)
      (fun _ => sq_nonneg _)
  refine h.congr fun p => ?_
  rw [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_conj, mul_pow]

/-- The rank-one test matrix `(i, j) ↦ x_i ȳ_j`. -/
def testMatrix (x y : ℓ²ι) : ℓ²ιι := ⟨fun p => x p.1 * starRingEnd ℂ (y p.2), memℓp_testMatrix x y⟩

theorem inner_testMatrix (x y : ℓ²ι) (w : ℓ²ιι) :
    ⟪testMatrix x y, w⟫_ℂ = ∑' p : ι × ι, starRingEnd ℂ (x p.1) * y p.2 * w p := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun p => ?_
  rw [RCLike.inner_apply]
  change w p * starRingEnd ℂ (x p.1 * starRingEnd ℂ (y p.2)) = _
  rw [map_mul, Complex.conj_conj]
  ring

variable [DecidableEq ι]

/-- The matrix `(i, j) ↦ ⟨e_i, T e_j⟩` of a Hilbert–Schmidt operator, as a vector of `ℓ²(ι × ι)`. -/
def operatorMatrixVec (T : ℓ²ι →L[ℂ] ℓ²ι) (hT : T.IsHilbertSchmidt) : ℓ²ιι :=
  ⟨HilbertSchmidt.matrixOf T, (HilbertSchmidt.isHS_matrixOf hT).memℓp⟩

theorem operatorMatrixVec_apply (T : ℓ²ι →L[ℂ] ℓ²ι) (hT : T.IsHilbertSchmidt) (p : ι × ι) :
    operatorMatrixVec T hT p = ⟪(lp.single 2 p.1 (1 : ℂ) : ℓ²ι), T (lp.single 2 p.2 1)⟫_ℂ := by
  exact (inner_single_one_left (T (lp.single 2 p.2 1)) p.1).symm

theorem norm_operatorMatrixVec_sq (T : ℓ²ι →L[ℂ] ℓ²ι) (hT : T.IsHilbertSchmidt) :
    ‖operatorMatrixVec T hT‖ ^ 2 = ContinuousLinearMap.hsNormSq T := by
  rw [lp_two_norm_sq_eq_tsum (operatorMatrixVec T hT)]
  conv_rhs => rw [← HilbertSchmidt.toOperator_matrixOf hT]
  rw [HilbertSchmidt.hsNormSq_toOperator]
  rfl

/-- **The matrix pairing.**  `⟨x ⊗ ȳ, mat T⟩ = ⟨x, T y⟩`. -/
theorem inner_testMatrix_operatorMatrixVec (T : ℓ²ι →L[ℂ] ℓ²ι) (hT : T.IsHilbertSchmidt) (x y : ℓ²ι) :
    ⟪testMatrix x y, operatorMatrixVec T hT⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have hsum := lp.summable_inner (𝕜 := ℂ) (testMatrix x y) (operatorMatrixVec T hT)
  have hrw : ∀ p : ι × ι, ⟪(testMatrix x y) p, (operatorMatrixVec T hT) p⟫_ℂ =
      starRingEnd ℂ (x p.1) * (HilbertSchmidt.matrixOf T p * y p.2) := fun p => by
    rw [RCLike.inner_apply]
    change HilbertSchmidt.matrixOf T p * starRingEnd ℂ (x p.1 * starRingEnd ℂ (y p.2)) = _
    rw [map_mul, Complex.conj_conj]
    ring
  rw [lp.inner_eq_tsum]
  simp_rw [hrw] at hsum ⊢
  conv_rhs => rw [← HilbertSchmidt.toOperator_matrixOf hT]
  rw [lp.inner_eq_tsum, hsum.tsum_prod]
  refine tsum_congr fun i => ?_
  rw [RCLike.inner_apply, HilbertSchmidt.toOperator_apply, ← tsum_mul_right]
  exact tsum_congr fun j => by ring

theorem norm_operatorMatrixVec_le (T : ℓ²ι →L[ℂ] ℓ²ι) (hT1 : MemSchattenClass 1 T) :
    ‖operatorMatrixVec T hT1.one_isHilbertSchmidt‖ ≤ traceNorm ℓ²ι T := by
  have h := hsNormSq_le_traceNorm_sq hT1
  rw [← norm_operatorMatrixVec_sq T hT1.one_isHilbertSchmidt] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (traceNorm_nonneg T) two_ne_zero).1 h

end Matrix

/-! ## Entries are controlled by the trace norm -/

theorem norm_inner_le_traceNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A : H →L[ℂ] H} (hA : MemSchattenClass 1 A) {x y : H} (hx : ‖x‖ ≤ 1)
    (hy : ‖y‖ ≤ 1) : ‖⟪x, A y⟫_ℂ‖ ≤ traceNorm H A := by
  calc ‖⟪x, A y⟫_ℂ‖ ≤ ‖x‖ * ‖A y‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖A‖ * ‖y‖) := mul_le_mul hx (A.le_opNorm y) (norm_nonneg _) zero_le_one
    _ ≤ 1 * (‖A‖ * 1) := by gcongr
    _ = ‖A‖ := by ring
    _ ≤ traceNorm H A := norm_le_traceNorm_of_memSchattenClass_one hA

theorem memSchattenClass_one_comp_sub_comp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) (A : H →L[ℂ] H) :
    MemSchattenClass 1 (T ∘L A - A ∘L T) := by
  have h1 : MemSchattenClass 1 (T ∘L A) := hT.one_comp_right A
  have h2 : MemSchattenClass 1 (A ∘L T) := memSchattenClass_one_comp_left hT A
  rw [sub_eq_add_neg]
  exact h1.one_add (by simpa using memSchattenClass_one_smul h2 (-1 : ℂ))

/-! ## The extended orbit cost and selection -/

namespace HeatSource

variable (s : HeatSource ι) [DecidableEq ι]

theorem heatReporter_single (j : ι) :
    s.heatReporter (lp.single 2 j (1 : ℂ)) = (((1 + s.lam j)⁻¹ : ℝ) : ℂ) • (lp.single 2 j (1 : ℂ) : ℓ²ι) := by
  refine lp.ext (funext fun k => ?_)
  rw [s.heatReporter_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
  by_cases hk : k = j
  · subst hk; simp
  · simp [Pi.single_eq_of_ne hk]

/-- The `D`-commutator entry `⟨e_i, [T, D] e_j⟩ = (d_j - d_i) ⟨e_i, T e_j⟩`. -/
theorem inner_single_commutator_heatReporter (T : ℓ²ι →L[ℂ] ℓ²ι) (i j : ι) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), (T ∘L s.heatReporter - s.heatReporter ∘L T) (lp.single 2 j 1)⟫_ℂ =
      ((((1 + s.lam j)⁻¹ : ℝ) : ℂ) - (((1 + s.lam i)⁻¹ : ℝ) : ℂ)) *
        ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), T (lp.single 2 j 1)⟫_ℂ := by
  rw [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, inner_sub_right,
    s.heatReporter_single, map_smul, inner_smul_right, s.inner_single_heatReporter]
  ring

/-- The `P`-commutator entry `⟨e_i, [T, P] e_j⟩ = v̄_j ⟨e_i, T v⟩ - v_i ⟨v, T e_j⟩`. -/
theorem inner_single_commutator_heatProjection (T : ℓ²ι →L[ℂ] ℓ²ι) (i j : ι) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), (T ∘L s.heatProjection - s.heatProjection ∘L T) (lp.single 2 j 1)⟫_ℂ =
      starRingEnd ℂ (s.v j) * ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), T s.v⟫_ℂ -
        s.v i * ⟪s.v, T (lp.single 2 j 1)⟫_ℂ := by
  rw [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, inner_sub_right,
    heatProjection, InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply, map_smul,
    inner_smul_right, inner_smul_right, inner_single_one_right, inner_single_one_left,
    inner_single_one_left]
  ring

end HeatSource

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι) [DecidableEq ι]

/-- **(OG.18)** The extended orbit cost `E_G(T) = Σ_k γ_k^{-1} ⟨f_k, T f_k⟩ ∈ [0, ∞]`. -/
def orbitDefectCost (T : ℓ²ι →L[ℂ] ℓ²ι) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal ((⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re / c.orbitEigenvalue k)

theorem traceNorm_eq_tsum_eigen {T : ℓ²ι →L[ℂ] ℓ²ι} (hpos : T.IsPositive) (hS : MemSchattenClass 1 T) :
    traceNorm ℓ²ι T = ∑' k, (⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re ∧
      Summable fun k => (⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re := by
  have hsum := hS.one_summable_inner_diag_basis c.orbitEigenbasis
  refine ⟨?_, Complex.reCLM.summable hsum⟩
  rw [traceNorm_eq_re_opTrace_of_isPositive hS hpos,
    opTrace_eq_tsum_basis_of_memSchattenClass_one hS c.orbitEigenbasis, Complex.re_tsum hsum]

/-- **(OG.31)** `tr T ≤ ‖G‖ E_G(T)`. -/
theorem ofReal_traceNorm_le {T : ℓ²ι →L[ℂ] ℓ²ι} (hpos : T.IsPositive) (hS : MemSchattenClass 1 T) :
    ENNReal.ofReal (traceNorm ℓ²ι T) ≤ ENNReal.ofReal ‖c.orbitGramian‖ * c.orbitDefectCost T := by
  obtain ⟨htr, hsum⟩ := c.traceNorm_eq_tsum_eigen hpos hS
  rw [htr, ENNReal.ofReal_tsum_of_nonneg (f := fun k => (⟪c.orbitEigenbasis k,
    T (c.orbitEigenbasis k)⟫_ℂ).re) (fun k => hpos.re_inner_nonneg_right _) hsum, orbitDefectCost,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hγ := c.orbitEigenvalue_pos k
  have hr := hpos.re_inner_nonneg_right (c.orbitEigenbasis k)
  calc (⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re
      = c.orbitEigenvalue k * ((⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re /
          c.orbitEigenvalue k) := by field_simp
    _ ≤ ‖c.orbitGramian‖ * ((⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re /
          c.orbitEigenvalue k) :=
        mul_le_mul_of_nonneg_right (c.orbitEigenvalue_le k) (by positivity)

/-- **(OG.34)** The trace splits into a head over `{γ_k ≥ ε}` and a tail of size at most
`ε E_G(T)`. -/
theorem traceNorm_le_head_add {T : ℓ²ι →L[ℂ] ℓ²ι} (hpos : T.IsPositive) (hS : MemSchattenClass 1 T)
    {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hM0 : 0 ≤ M) (hM : c.orbitDefectCost T ≤ ENNReal.ofReal M) :
    traceNorm ℓ²ι T ≤ ∑ k ∈ (c.finite_orbitEigenvalue_ge hε).toFinset,
      (⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re + ε * M := by
  obtain ⟨htr, hsum⟩ := c.traceNorm_eq_tsum_eigen hpos hS
  set r : EigenIndex c.orbitGramian → ℝ := fun k => (⟪c.orbitEigenbasis k, T (c.orbitEigenbasis k)⟫_ℂ).re
  set F := (c.finite_orbitEigenvalue_ge hε).toFinset
  have hr0 : ∀ k, 0 ≤ r k := fun k => hpos.re_inner_nonneg_right _
  have hcost : c.orbitDefectCost T < ⊤ := lt_of_le_of_lt hM ENNReal.ofReal_lt_top
  have hq : Summable fun k => r k / c.orbitEigenvalue k := by
    have h := ENNReal.summable_toReal hcost.ne
    refine h.congr fun k => ?_
    rw [ENNReal.toReal_ofReal (div_nonneg (hr0 k) (c.orbitEigenvalue_pos k).le)]
  have hqM : ∑' k, r k / c.orbitEigenvalue k ≤ M := by
    rw [orbitDefectCost, ← ENNReal.ofReal_tsum_of_nonneg
      (fun k => div_nonneg (hr0 k) (c.orbitEigenvalue_pos k).le) hq] at hM
    exact (ENNReal.ofReal_le_ofReal_iff hM0).1 hM
  rw [htr, ← hsum.sum_add_tsum_compl (s := F)]
  refine add_le_add le_rfl ?_
  have htail : ∀ k : ↑((F : Set (EigenIndex c.orbitGramian))ᶜ), r k ≤ ε * (r k / c.orbitEigenvalue k) :=
    fun k => by
      have hk : c.orbitEigenvalue k < ε := by
        have := k.2
        simp only [Set.mem_compl_iff, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
          not_le, F] at this
        exact this
      have hγ := c.orbitEigenvalue_pos k
      rw [mul_div_assoc', le_div_iff₀ hγ]
      exact mul_le_mul_of_nonneg_left hk.le (hr0 k) |>.trans_eq (mul_comm _ _)
  calc ∑' k : ↑((F : Set (EigenIndex c.orbitGramian))ᶜ), r k
      ≤ ∑' k : ↑((F : Set (EigenIndex c.orbitGramian))ᶜ), ε * (r k / c.orbitEigenvalue k) :=
        Summable.tsum_le_tsum htail (hsum.subtype _) ((hq.subtype _).mul_left ε)
    _ = ε * ∑' k : ↑((F : Set (EigenIndex c.orbitGramian))ᶜ), r k / c.orbitEigenvalue k := tsum_mul_left
    _ ≤ ε * M := by
        refine mul_le_mul_of_nonneg_left ((Summable.tsum_subtype_le _ _ (fun k =>
          div_nonneg (hr0 k) (c.orbitEigenvalue_pos k).le) hq).trans hqM) hε.le

omit [DecidableEq ι] in
theorem diag_injective : Function.Injective fun i : ι => (i, i) := fun _ _ h => congrArg Prod.fst h

/-- **(OG.33)** Approximately source-invariant defects with bounded trace converge weakly to zero:
`⟨x, T_n y⟩ → 0`. -/
theorem tendsto_inner_of_commutators [Infinite ι] [Countable ι] (T : ℕ → ℓ²ι →L[ℂ] ℓ²ι)
    (hS : ∀ n, MemSchattenClass 1 (T n)) {B : ℝ} (hB : ∀ n, traceNorm ℓ²ι (T n) ≤ B)
    (hD : Tendsto (fun n => traceNorm ℓ²ι (T n ∘L c.heatReporter - c.heatReporter ∘L T n)) atTop (𝓝 0))
    (hP : Tendsto (fun n => traceNorm ℓ²ι (T n ∘L c.heatProjection - c.heatProjection ∘L T n))
      atTop (𝓝 0)) (x y : ℓ²ι) :
    Tendsto (fun n => ⟪x, T n y⟫_ℂ) atTop (𝓝 0) := by
  set m : ℕ → ℓ²ιι := fun n => operatorMatrixVec (T n) (hS n).one_isHilbertSchmidt with hmdef
  have hm : ∀ n, ‖m n‖ ≤ B := fun n => (norm_operatorMatrixVec_le _ (hS n)).trans (hB n)
  have hpair : ∀ n a b, ⟪testMatrix a b, m n⟫_ℂ = ⟪a, T n b⟫_ℂ := fun n a b =>
    inner_testMatrix_operatorMatrixVec _ _ a b
  have hsingle : ∀ (i j : ι), ‖(lp.single 2 i (1 : ℂ) : ℓ²ι)‖ ≤ 1 := fun i j => by
    rw [lp.norm_single (by norm_num), norm_one]
  have hDent : ∀ i j, Tendsto (fun n => ((((1 + c.lam j)⁻¹ : ℝ) : ℂ) - (((1 + c.lam i)⁻¹ : ℝ) : ℂ)) *
      ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), T n (lp.single 2 j 1)⟫_ℂ) atTop (𝓝 0) := fun i j => by
    refine squeeze_zero_norm (fun n => ?_) hD
    rw [← c.inner_single_commutator_heatReporter]
    exact norm_inner_le_traceNorm (memSchattenClass_one_comp_sub_comp (hS n) _) (hsingle i j)
      (hsingle j i)
  have hPent : ∀ i j, Tendsto (fun n => starRingEnd ℂ (c.v j) * ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), T n c.v⟫_ℂ -
      c.v i * ⟪c.v, T n (lp.single 2 j 1)⟫_ℂ) atTop (𝓝 0) := fun i j => by
    refine squeeze_zero_norm (fun n => ?_) hP
    rw [← c.inner_single_commutator_heatProjection]
    exact norm_inner_le_traceNorm (memSchattenClass_one_comp_sub_comp (hS n) _) (hsingle i j)
      (hsingle j i)
  have hkey : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ w : ℓ²ιι,
      (∀ z, Tendsto (fun n => ⟪z, m (φ n)⟫_ℂ) atTop (𝓝 ⟪z, w⟫_ℂ)) → w = 0 := by
    intro φ hφ w hw
    have hent : ∀ i j, Tendsto (fun n => ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), T (φ n) (lp.single 2 j 1)⟫_ℂ)
        atTop (𝓝 (w (i, j))) := fun i j => by
      have h := hw (lp.single 2 (i, j) 1)
      rw [inner_single_one_left] at h
      refine h.congr fun n => ?_
      rw [inner_single_one_left, hmdef]
      exact operatorMatrixVec_apply _ _ (i, j)
    have hoff : ∀ i j, i ≠ j → w (i, j) = 0 := by
      intro i j hij
      have h1 := (hent i j).const_mul ((((1 + c.lam j)⁻¹ : ℝ) : ℂ) - (((1 + c.lam i)⁻¹ : ℝ) : ℂ))
      have h2 := (hDent i j).comp hφ.tendsto_atTop
      have heq := tendsto_nhds_unique h1 h2
      have hne : (((1 + c.lam j)⁻¹ : ℝ) : ℂ) - (((1 + c.lam i)⁻¹ : ℝ) : ℂ) ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        exact hij (c.reporterEigenvalue_injective c.simple (by exact_mod_cast h.symm))
      exact (mul_eq_zero.1 heq).resolve_left hne
    have e1 : ∀ i, ⟪testMatrix (lp.single 2 i (1 : ℂ)) c.v, w⟫_ℂ = c.v i * w (i, i) := fun i => by
      rw [inner_testMatrix, tsum_eq_single (i, i)]
      · simp
      · intro p hp
        by_cases h1 : p.1 = i
        · have h2 : p.2 ≠ i := fun h2 => hp (Prod.ext h1 h2)
          have : w p = 0 := by
            rw [show p = (i, p.2) from Prod.ext h1 rfl]
            exact hoff i p.2 (Ne.symm h2)
          rw [this, mul_zero]
        · rw [lp.single_apply, Pi.single_eq_of_ne h1]
          simp
    have e2 : ∀ j, ⟪testMatrix c.v (lp.single 2 j (1 : ℂ)), w⟫_ℂ = starRingEnd ℂ (c.v j) * w (j, j) :=
      fun j => by
        rw [inner_testMatrix, tsum_eq_single (j, j)]
        · simp
        · intro p hp
          by_cases h2 : p.2 = j
          · have h1 : p.1 ≠ j := fun h1 => hp (Prod.ext h1 h2)
            have : w p = 0 := by
              rw [show p = (p.1, j) from Prod.ext rfl h2]
              exact hoff p.1 j h1
            rw [this, mul_zero]
          · rw [lp.single_apply, Pi.single_eq_of_ne h2]
            simp
    have hdiag : ∀ i j, w (i, i) = w (j, j) := by
      intro i j
      have h1 := ((hw (testMatrix (lp.single 2 i (1 : ℂ)) c.v)).const_mul (starRingEnd ℂ (c.v j))).sub
        ((hw (testMatrix c.v (lp.single 2 j (1 : ℂ)))).const_mul (c.v i))
      have h2 := (hPent i j).comp hφ.tendsto_atTop
      have heq := tendsto_nhds_unique (h1.congr fun n => by
        simp only [Function.comp_apply, hpair]) h2
      rw [e1, e2] at heq
      have hvv : c.v i * starRingEnd ℂ (c.v j) ≠ 0 :=
        mul_ne_zero (c.fullSupport i) ((map_ne_zero _).2 (c.fullSupport j))
      have : c.v i * starRingEnd ℂ (c.v j) * (w (i, i) - w (j, j)) = 0 := by
        linear_combination heq
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hvv)
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have hc : w (i₀, i₀) = 0 := by
      have hs : Summable fun i : ι => ‖w (i, i)‖ ^ 2 :=
        (summable_norm_sq_lp w).comp_injective diag_injective
      simp_rw [hdiag _ i₀] at hs
      have := (summable_const_iff _).1 hs
      simpa using this
    refine lp.ext (funext fun p => ?_)
    rw [lp.coeFn_zero, Pi.zero_apply]
    by_cases hp : p.1 = p.2
    · rw [show p = (p.1, p.1) from Prod.ext rfl hp.symm, hdiag p.1 i₀, hc]
    · rw [show p = (p.1, p.2) from rfl]
      exact hoff p.1 p.2 hp
  haveI := separableSpace_lp_countable (ι := ι × ι)
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  have hfr : ∃ᶠ n in atTop, ε ≤ dist ⟪x, T n y⟫_ℂ 0 := Filter.frequently_atTop.2 hfreq
  obtain ⟨ψ, hψ, hψε⟩ := extraction_of_frequently_atTop hfr
  obtain ⟨w, φ, hφ, -, hweak⟩ := exists_weaklyConvergent_subseq_of_bounded (fun n => m (ψ n)) B
    (fun n => hm _)
  have hweak' : ∀ z, Tendsto (fun n => ⟪z, m (ψ (φ n))⟫_ℂ) atTop (𝓝 ⟪z, w⟫_ℂ) := fun z => by
    have h := (Complex.continuous_conj.tendsto _).comp (hweak z)
    simp only [Function.comp_def, inner_conj_symm] at h
    exact h
  have hw0 := hkey (ψ ∘ φ) (hψ.comp hφ) w hweak'
  have hlim := hweak' (testMatrix x y)
  rw [hw0, inner_zero_right] at hlim
  simp_rw [hpair] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (Metric.ball_mem_nhds 0 hε)).exists
  exact absurd (hψε (φ n)) (not_le.2 hn)

/-- **(OG.21) Endogenous-cost selection.**  Positive trace-class defects with
`‖[T_n, D]‖₁ + ‖[T_n, P]‖₁ → 0` and uniformly bounded orbit cost have `‖T_n‖₁ → 0`. -/
theorem tendsto_traceNorm_of_selection [Infinite ι] [Countable ι] (T : ℕ → ℓ²ι →L[ℂ] ℓ²ι)
    (hpos : ∀ n, (T n).IsPositive) (hS : ∀ n, MemSchattenClass 1 (T n))
    (hcomm : Tendsto (fun n => traceNorm ℓ²ι (T n ∘L c.heatReporter - c.heatReporter ∘L T n) +
      traceNorm ℓ²ι (T n ∘L c.heatProjection - c.heatProjection ∘L T n)) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ n, c.orbitDefectCost (T n) ≤ ENNReal.ofReal M) :
    Tendsto (fun n => traceNorm ℓ²ι (T n)) atTop (𝓝 0) := by
  set M' := max M 0
  have hM' : ∀ n, c.orbitDefectCost (T n) ≤ ENNReal.ofReal M' := fun n =>
    (hM n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hD : Tendsto (fun n => traceNorm ℓ²ι (T n ∘L c.heatReporter - c.heatReporter ∘L T n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => traceNorm_nonneg _) (fun n => le_add_of_nonneg_right (traceNorm_nonneg _)) hcomm
  have hP : Tendsto (fun n => traceNorm ℓ²ι (T n ∘L c.heatProjection - c.heatProjection ∘L T n))
      atTop (𝓝 0) :=
    squeeze_zero (fun n => traceNorm_nonneg _) (fun n => le_add_of_nonneg_left (traceNorm_nonneg _)) hcomm
  have hB : ∀ n, traceNorm ℓ²ι (T n) ≤ ‖c.orbitGramian‖ * M' := fun n => by
    have h := (c.ofReal_traceNorm_le (hpos n) (hS n)).trans
      (mul_le_mul' le_rfl (hM' n))
    rw [← ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    exact h
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε := δ / (2 * (M' + 1)) with hεdef
  have hε : 0 < ε := by positivity
  set F := (c.finite_orbitEigenvalue_ge hε).toFinset
  have hhead : Tendsto (fun n => ∑ k ∈ F, (⟪c.orbitEigenbasis k, T n (c.orbitEigenbasis k)⟫_ℂ).re)
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ _k ∈ F, (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun k _ => ?_
    have h := (Complex.continuous_re.tendsto 0).comp
      (c.tendsto_inner_of_commutators T hS hB hD hP (c.orbitEigenbasis k) (c.orbitEigenbasis k))
    rw [Complex.zero_re] at h
    exact h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hhead) (δ / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := c.traceNorm_le_head_add (hpos n) (hS n) hε hM0 (hM' n)
  have h2 := hN n hn
  rw [Real.dist_eq, sub_zero] at h2 ⊢
  have hεM : ε * M' < δ / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [abs_of_nonneg (traceNorm_nonneg _)]
  have := (le_abs_self _).trans h2.le
  linarith [abs_lt.1 h2]

/-- **(OG.33)** Under the selection hypotheses `tr(T_n K) → 0` for every bounded (in particular
every compact) observer `K`. -/
theorem tendsto_opTrace_comp_of_selection [Infinite ι] [Countable ι] (T : ℕ → ℓ²ι →L[ℂ] ℓ²ι)
    (hpos : ∀ n, (T n).IsPositive) (hS : ∀ n, MemSchattenClass 1 (T n))
    (hcomm : Tendsto (fun n => traceNorm ℓ²ι (T n ∘L c.heatReporter - c.heatReporter ∘L T n) +
      traceNorm ℓ²ι (T n ∘L c.heatProjection - c.heatProjection ∘L T n)) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ n, c.orbitDefectCost (T n) ≤ ENNReal.ofReal M) (K : ℓ²ι →L[ℂ] ℓ²ι) :
    Tendsto (fun n => (T n ∘L K).opTrace) atTop (𝓝 0) := by
  have h := c.tendsto_traceNorm_of_selection T hpos hS hcomm hM
  refine squeeze_zero_norm (fun n => norm_opTrace_comp_le_norm_mul_traceNorm (hS n) K) ?_
  simpa using h.mul_const ‖K‖

end CyclicHeatSource

end GaloisForLFunctions.HTGeometry
