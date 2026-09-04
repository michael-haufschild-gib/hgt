import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall
import GaloisForLFunctions.RHTower.RectangularSemilocalObserverTailSeparation
import GaloisForLFunctions.RHTower.NuclearRankOneTrace
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.IntegrableDerivLimit

/-!
# Prime--Hodge purity-cost firewall

Coordinate-free exact operator- and trace-norm distances from positive trace-one Schatten
operators to rank-one pure states, instantiated at the actual prime-mixed relative-curvature
source.  The source has norm at most `1/3`, so the full primitive Euler collision budget cannot
reach any pure horizon by an additive trace-class correction, bounded-variation operator path,
or absolutely continuous Schatten-one path.

This module is unconditional: it contains no Xi-zero, divisor, or ordinate parameter.
-/


open Complex Filter Topology
open scoped BigOperators InnerProductSpace ComplexOrder

noncomputable section
namespace RHTower

open ContinuousLinearMap InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def purityRankOneProjection (x : H) : H →L[ℂ] H := rankOne ℂ x x

omit [CompleteSpace H] in
theorem purityRankOneProjection_apply {x : H} (y : H) :
    purityRankOneProjection x y = inner ℂ x y • x := by
  rfl

theorem purityRankOneProjection_adjoint {x : H} : ContinuousLinearMap.adjoint (purityRankOneProjection x) = purityRankOneProjection x := by
  rw [purityRankOneProjection, InnerProductSpace.adjoint_rankOne]

omit [CompleteSpace H] in
theorem purityRankOneProjection_mul_self {x : H} (hx : ‖x‖ = 1) : purityRankOneProjection x * purityRankOneProjection x = purityRankOneProjection x := by
  ext y
  simp [purityRankOneProjection, rankOne_apply, hx, inner_self_eq_norm_sq_to_K]

omit [CompleteSpace H] in
theorem purityReflection_sq {x : H} (hx : ‖x‖ = 1) :
    ((2 : ℂ) • purityRankOneProjection x - 1) * ((2 : ℂ) • purityRankOneProjection x - 1) = 1 := by
  rw [sub_mul, mul_sub, mul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, mul_one, one_mul, purityRankOneProjection_mul_self hx]
  module

theorem purityReflection_adjoint {x : H} :
    ContinuousLinearMap.adjoint ((2 : ℂ) • purityRankOneProjection x - 1) =
      (2 : ℂ) • purityRankOneProjection x - 1 := by
  change ContinuousLinearMap.adjoint
      ((2 : ℂ) • purityRankOneProjection x - ContinuousLinearMap.id ℂ H) =
    (2 : ℂ) • purityRankOneProjection x - ContinuousLinearMap.id ℂ H
  rw [map_sub, map_smulₛₗ, purityRankOneProjection_adjoint]
  simp only [map_ofNat, ContinuousLinearMap.adjoint_id]

theorem purityReflection_norm_le_one {x : H} (hx : ‖x‖ = 1) :
    ‖(2 : ℂ) • purityRankOneProjection x - 1‖ ≤ 1 := by
  let A : H →L[ℂ] H := (2 : ℂ) • purityRankOneProjection x - 1
  have hAdj : ContinuousLinearMap.adjoint A = A := purityReflection_adjoint
  have hSq : A * A = 1 := purityReflection_sq hx
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  have hinner : inner ℂ (A y) (A y) = inner ℂ y y := by
    calc
      inner ℂ (A y) (A y) =
          inner ℂ y (ContinuousLinearMap.adjoint A (A y)) :=
        (ContinuousLinearMap.adjoint_inner_right A y (A y)).symm
      _ = inner ℂ y ((ContinuousLinearMap.adjoint A * A) y) := rfl
      _ = inner ℂ y y := by
        rw [hAdj, hSq]
        simp
  have hre := congrArg Complex.re hinner
  simp only [inner_self_eq_norm_sq_to_K] at hre
  have hnormSq : ‖A y‖ ^ 2 = ‖y‖ ^ 2 := by exact_mod_cast hre
  nlinarith [norm_nonneg (A y), norm_nonneg y]

omit [CompleteSpace H] in
theorem purityRankOneProjection_hasRankLE_one (x : H) : HasRankLE (purityRankOneProjection x) 1 := by
  simpa [purityRankOneProjection] using
    (hasRankLE_sum_range_rankOne (fun _ : ℕ => x) (fun _ : ℕ => x) 1)

omit [CompleteSpace H] in
theorem purityRankOneProjection_memSchattenClass_one (x : H) : MemSchattenClass 1 (purityRankOneProjection x) :=
  memSchattenClass_of_hasRankLE one_pos (purityRankOneProjection_hasRankLE_one x)

theorem purityRankOneProjection_opTrace {x : H} (hx : ‖x‖ = 1) :
    ContinuousLinearMap.opTrace (purityRankOneProjection x) = 1 := by
  rw [purityRankOneProjection, GaloisForLFunctions.HTGeometry.opTrace_rankOne,
    inner_self_eq_norm_sq_to_K, hx]
  norm_num

omit [CompleteSpace H] in
theorem mul_purityRankOneProjection_eq_rankOne (S : H →L[ℂ] H) (x : H) :
    S * purityRankOneProjection x = rankOne ℂ (S x) x := by
  ext y
  simp [purityRankOneProjection, rankOne_apply]

theorem opTrace_mul_purityRankOneProjection (S : H →L[ℂ] H) (x : H) :
    ContinuousLinearMap.opTrace (S * purityRankOneProjection x) = inner ℂ x (S x) := by
  rw [mul_purityRankOneProjection_eq_rankOne,
    GaloisForLFunctions.HTGeometry.opTrace_rankOne]

omit [CompleteSpace H] in
theorem purityRankOneProjection_sub_mul_purityReflection
    (S : H →L[ℂ] H) {x : H} (hx : ‖x‖ = 1) :
    (purityRankOneProjection x - S) * ((2 : ℂ) • purityRankOneProjection x - 1) =
      purityRankOneProjection x - (2 : ℂ) • (S * purityRankOneProjection x) + S := by
  rw [sub_mul, mul_sub, mul_sub]
  simp only [mul_smul_comm, purityRankOneProjection_mul_self hx, mul_one]
  module

theorem opTrace_purityRankOneProjection_sub_mul_purityReflection
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hTr : ContinuousLinearMap.opTrace S = 1)
    {x : H} (hx : ‖x‖ = 1) :
    ContinuousLinearMap.opTrace
      ((purityRankOneProjection x - S) * ((2 : ℂ) • purityRankOneProjection x - 1)) =
        2 * (1 - inner ℂ x (S x)) := by
  rw [purityRankOneProjection_sub_mul_purityReflection S hx]
  have hP := purityRankOneProjection_memSchattenClass_one x
  have hSP : MemSchattenClass 1 (S * purityRankOneProjection x) := hS.one_comp_right (purityRankOneProjection x)
  have h2SP : MemSchattenClass 1 ((2 : ℂ) • (S * purityRankOneProjection x)) :=
    memSchattenClass_one_smul hSP 2
  rw [show purityRankOneProjection x - (2 : ℂ) • (S * purityRankOneProjection x) + S =
      (purityRankOneProjection x - (2 : ℂ) • (S * purityRankOneProjection x)) + S by rfl]
  rw [opTrace_add_of_memSchattenClass_one
      (hP.one_sub h2SP) hS,
    opTrace_sub_of_memSchattenClass_one hP h2SP,
    GaloisForLFunctions.HTGeometry.opTrace_smul,
    opTrace_mul_purityRankOneProjection, purityRankOneProjection_opTrace hx, hTr]
  ring

theorem traceNorm_purityRankOneProjection_sub_ge_two_mul_one_sub_norm
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hTr : ContinuousLinearMap.opTrace S = 1)
    {x : H} (hx : ‖x‖ = 1) :
    2 * (1 - ‖S‖) ≤ traceNorm H (purityRankOneProjection x - S) := by
  let K : H →L[ℂ] H := purityRankOneProjection x - S
  let A : H →L[ℂ] H := (2 : ℂ) • purityRankOneProjection x - 1
  have hK : MemSchattenClass 1 K := (purityRankOneProjection_memSchattenClass_one x).one_sub hS
  have hA : ‖A‖ ≤ 1 := purityReflection_norm_le_one hx
  have hdual := norm_opTrace_comp_le_norm_mul_traceNorm hK A
  have htrace : ContinuousLinearMap.opTrace (K * A) =
      2 * (1 - inner ℂ x (S x)) :=
    opTrace_purityRankOneProjection_sub_mul_purityReflection hS hTr hx
  have hquad : (inner ℂ x (S x)).re ≤ ‖S‖ := by
    calc
      (inner ℂ x (S x)).re ≤ ‖inner ℂ x (S x)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖S x‖ := norm_inner_le_norm _ _
      _ = ‖S x‖ := by rw [hx, one_mul]
      _ ≤ ‖S‖ * ‖x‖ := S.le_opNorm x
      _ = ‖S‖ := by rw [hx, mul_one]
  change ‖ContinuousLinearMap.opTrace (K * A)‖ ≤
    traceNorm H K * ‖A‖ at hdual
  rw [htrace] at hdual
  have hre : 2 * (1 - ‖S‖) ≤
      (2 * (1 - inner ℂ x (S x))).re := by
    rw [Complex.mul_re]
    norm_num
    linarith
  calc
    2 * (1 - ‖S‖) ≤ (2 * (1 - inner ℂ x (S x))).re := hre
    _ ≤ ‖2 * (1 - inner ℂ x (S x))‖ := Complex.re_le_norm _
    _ ≤ traceNorm H K * ‖A‖ := hdual
    _ ≤ traceNorm H K * 1 :=
      mul_le_mul_of_nonneg_left hA (traceNorm_nonneg K)
    _ = traceNorm H (purityRankOneProjection x - S) := by simp [K]

omit [CompleteSpace H] in
theorem purityRankOneProjection_norm {x : H} (hx : ‖x‖ = 1) : ‖purityRankOneProjection x‖ = 1 := by
  rw [purityRankOneProjection, InnerProductSpace.norm_rankOne, hx]
  norm_num

omit [CompleteSpace H] in
theorem norm_purityRankOneProjection_sub_ge_one_sub_norm (S : H →L[ℂ] H)
    {x : H} (hx : ‖x‖ = 1) :
    1 - ‖S‖ ≤ ‖purityRankOneProjection x - S‖ := by
  rw [← purityRankOneProjection_norm hx]
  exact norm_sub_norm_le _ _

omit [CompleteSpace H] in
theorem positive_remainder_at_eigenvector
    {S : H →L[ℂ] H} (hpos : S.IsPositive)
    {x : H} (hx : ‖x‖ = 1) {lam : ℝ}
    (heig : S x = (lam : ℂ) • x) :
    (S - (lam : ℂ) • purityRankOneProjection x).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · apply hpos.isSymmetric.sub
    apply LinearMap.IsSymmetric.smul (by simp)
    intro y z
    simp [purityRankOneProjection, rankOne_apply, inner_smul_left, inner_smul_right, mul_comm]
  · intro y
    let z : H := y - inner ℂ x y • x
    have hxz : inner ℂ x z = 0 := by
      simp [z, inner_self_eq_norm_sq_to_K, hx]
    have hxSz : inner ℂ x (S z) = 0 := by
      calc
        inner ℂ x (S z) = inner ℂ (S x) z := (hpos.isSymmetric x z).symm
        _ = 0 := by rw [heig, inner_smul_left, hxz, mul_zero]
    have hSzx : inner ℂ (S z) x = 0 := by
      rw [← inner_conj_symm, hxSz, map_zero]
    have hRy : (S - (lam : ℂ) • purityRankOneProjection x) y = S z := by
      simp only [sub_apply, smul_apply,
        purityRankOneProjection, rankOne_apply, z]
      rw [map_sub, map_smul, heig]
      module
    rw [hRy]
    have hdecomp : y = z + inner ℂ x y • x := by
      simp [z]
    rw [hdecomp, inner_add_right, inner_smul_right, hSzx, mul_zero, add_zero]
    exact ((ContinuousLinearMap.isPositive_iff S).mp hpos).2 z

theorem exists_top_positive_eigenvector
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hpos : S.IsPositive) (hTr : ContinuousLinearMap.opTrace S = 1) :
    ∃ x : H, ‖x‖ = 1 ∧ S x = ((‖S‖ : ℝ) : ℂ) • x ∧
      (S - ((‖S‖ : ℝ) : ℂ) • purityRankOneProjection x).IsPositive := by
  have hS0 : S ≠ 0 := by
    intro h
    subst S
    simp at hTr
  obtain ⟨mu, x, hmu, hx, heig⟩ :=
    ContinuousLinearMap.exists_unit_eigenvector_norm (hS.isCompactOperator one_pos)
      hpos.isSymmetric hS0
  have hmu_nonneg : 0 ≤ mu := by
    have hq := ((ContinuousLinearMap.isPositive_iff S).mp hpos).2 x
    rw [heig, inner_smul_left, inner_self_eq_norm_sq_to_K, hx] at hq
    simpa using hq
  have hmu_eq : mu = ‖S‖ := by
    simpa [abs_of_nonneg hmu_nonneg] using hmu
  subst mu
  exact ⟨x, hx, heig, positive_remainder_at_eigenvector hpos hx heig⟩

theorem traceNorm_eq_one_of_positive_trace_one
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hpos : S.IsPositive) (hTr : ContinuousLinearMap.opTrace S = 1) :
    traceNorm H S = 1 := by
  rw [traceNorm_eq_re_opTrace_of_isPositive hS hpos, hTr]
  norm_num

theorem norm_le_one_of_positive_trace_one
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hpos : S.IsPositive) (hTr : ContinuousLinearMap.opTrace S = 1) :
    ‖S‖ ≤ 1 := by
  rw [← traceNorm_eq_one_of_positive_trace_one hS hpos hTr]
  exact norm_le_traceNorm_of_memSchattenClass_one hS

theorem top_eigenvector_remainder_traceNorm
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hpos : S.IsPositive) (hTr : ContinuousLinearMap.opTrace S = 1)
    {x : H} (hx : ‖x‖ = 1)
    (heig : S x = ((‖S‖ : ℝ) : ℂ) • x) :
    traceNorm H (S - ((‖S‖ : ℝ) : ℂ) • purityRankOneProjection x) = 1 - ‖S‖ := by
  let R : H →L[ℂ] H := S - ((‖S‖ : ℝ) : ℂ) • purityRankOneProjection x
  have hP : MemSchattenClass 1 (purityRankOneProjection x) := purityRankOneProjection_memSchattenClass_one x
  have hscaled : MemSchattenClass 1 (((‖S‖ : ℝ) : ℂ) • purityRankOneProjection x) :=
    memSchattenClass_one_smul hP _
  have hR : MemSchattenClass 1 R := hS.one_sub hscaled
  have hRpos : R.IsPositive := positive_remainder_at_eigenvector hpos hx heig
  rw [traceNorm_eq_re_opTrace_of_isPositive hR hRpos]
  change (ContinuousLinearMap.opTrace
    (S - ((‖S‖ : ℝ) : ℂ) • purityRankOneProjection x)).re = _
  rw [opTrace_sub_of_memSchattenClass_one hS hscaled,
    GaloisForLFunctions.HTGeometry.opTrace_smul, purityRankOneProjection_opTrace hx, hTr]
  norm_num

theorem exists_rankOne_traceNorm_distance_eq_purity_cost
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hpos : S.IsPositive) (hTr : ContinuousLinearMap.opTrace S = 1) :
    ∃ x : H, ‖x‖ = 1 ∧
      traceNorm H (purityRankOneProjection x - S) = 2 * (1 - ‖S‖) := by
  obtain ⟨x, hx, heig, hRpos⟩ := exists_top_positive_eigenvector hS hpos hTr
  refine ⟨x, hx, le_antisymm ?_ (traceNorm_purityRankOneProjection_sub_ge_two_mul_one_sub_norm hS hTr hx)⟩
  let R : H →L[ℂ] H := S - ((‖S‖ : ℝ) : ℂ) • purityRankOneProjection x
  let Q : H →L[ℂ] H := (((1 - ‖S‖ : ℝ) : ℂ) • purityRankOneProjection x)
  have hP : MemSchattenClass 1 (purityRankOneProjection x) := purityRankOneProjection_memSchattenClass_one x
  have hQ : MemSchattenClass 1 Q := memSchattenClass_one_smul hP _
  have hscaled : MemSchattenClass 1 (((‖S‖ : ℝ) : ℂ) • purityRankOneProjection x) :=
    memSchattenClass_one_smul hP _
  have hR : MemSchattenClass 1 R := hS.one_sub hscaled
  have hnegR : MemSchattenClass 1 (-R) := hR.one_neg
  have hdecomp : purityRankOneProjection x - S = Q + (-R) := by
    simp [Q, R]
    module
  rw [hdecomp]
  calc
    traceNorm H (Q + -R) ≤ traceNorm H Q + traceNorm H (-R) :=
      traceNorm_add_le (hQ.isCompactOperator one_pos) (hnegR.isCompactOperator one_pos)
        hQ.one_summable_approxNumber hnegR.one_summable_approxNumber
    _ = ‖((1 - ‖S‖ : ℝ) : ℂ)‖ * traceNorm H (purityRankOneProjection x) + traceNorm H R := by
      rw [traceNorm_smul, show -R = (-1 : ℂ) • R by module, traceNorm_smul]
      norm_num
    _ = (1 - ‖S‖) + (1 - ‖S‖) := by
      rw [traceNorm_eq_norm_of_hasRankLE_one (purityRankOneProjection_hasRankLE_one x), purityRankOneProjection_norm hx,
        top_eigenvector_remainder_traceNorm hS hpos hTr hx heig]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (norm_le_one_of_positive_trace_one hS hpos hTr))]
      ring
    _ = 2 * (1 - ‖S‖) := by ring

theorem top_eigenvector_rankOne_operator_distance
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hpos : S.IsPositive) (hTr : ContinuousLinearMap.opTrace S = 1)
    {x : H} (hx : ‖x‖ = 1)
    (heig : S x = ((‖S‖ : ℝ) : ℂ) • x) :
    ‖purityRankOneProjection x - S‖ = 1 - ‖S‖ := by
  let a : ℝ := 1 - ‖S‖
  let P : H →L[ℂ] H := purityRankOneProjection x
  let R : H →L[ℂ] H := S - ((‖S‖ : ℝ) : ℂ) • P
  have ha : 0 ≤ a := sub_nonneg.mpr (norm_le_one_of_positive_trace_one hS hpos hTr)
  have hPapply (y : H) : P y = inner ℂ x y • x := by rfl
  have hPx : P x = x := by
    rw [hPapply, inner_self_eq_norm_sq_to_K, hx]
    norm_num
  have hRx : R x = 0 := by
    simp only [R, sub_apply, smul_apply, hPx, heig]
    module
  have hRpos : R.IsPositive := by
    simpa [R, P] using positive_remainder_at_eigenvector hpos hx heig
  have hPmem : MemSchattenClass 1 P := purityRankOneProjection_memSchattenClass_one x
  have hscaled : MemSchattenClass 1 (((‖S‖ : ℝ) : ℂ) • P) :=
    memSchattenClass_one_smul hPmem _
  have hRmem : MemSchattenClass 1 R := hS.one_sub hscaled
  have hRtrace : traceNorm H R = a := by
    simpa [R, P, a] using top_eigenvector_remainder_traceNorm hS hpos hTr hx heig
  have hRnorm : ‖R‖ ≤ a := by
    rw [← hRtrace]
    exact norm_le_traceNorm_of_memSchattenClass_one hRmem
  have hupper : ‖P - S‖ ≤ a := by
    apply ContinuousLinearMap.opNorm_le_bound _ ha
    intro y
    let p : H := P y
    let z : H := y - p
    have hp : p = inner ℂ x y • x := hPapply y
    have hxz : inner ℂ x z = 0 := by
      simp [z, p, hp, inner_self_eq_norm_sq_to_K, hx]
    have hpz : inner ℂ p z = 0 := by
      rw [hp, inner_smul_left, hxz, mul_zero]
    have hRz_x : inner ℂ x (R z) = 0 := by
      calc
        inner ℂ x (R z) = inner ℂ (R x) z := (hRpos.isSymmetric x z).symm
        _ = 0 := by rw [hRx, inner_zero_left]
    have hpRz : inner ℂ p (R z) = 0 := by
      rw [hp, inner_smul_left, hRz_x, mul_zero]
    have hRp : R p = 0 := by
      rw [hp, map_smul, hRx, smul_zero]
    have hRy : R y = R z := by
      have hy : y = p + z := by simp [z]
      rw [hy, map_add, hRp, zero_add]
    have hDy : (P - S) y = ((a : ℝ) : ℂ) • p - R z := by
      have hSR : S = R + ((‖S‖ : ℝ) : ℂ) • P := by
        simp [R]
      simp only [sub_apply]
      rw [hSR, add_apply, smul_apply, hRy]
      simp only [p]
      change P y - (R z + (‖S‖ : ℂ) • P y) = (a : ℂ) • P y - R z
      simp [a]
      module
    have hsplit : ‖p‖ ^ 2 + ‖z‖ ^ 2 = ‖y‖ ^ 2 := by
      have hy : y = p + z := by simp [z]
      rw [hy, norm_add_sq (𝕜 := ℂ) p z, hpz]
      norm_num
    have hRz : ‖R z‖ ≤ a * ‖z‖ := by
      calc
        ‖R z‖ ≤ ‖R‖ * ‖z‖ := R.le_opNorm z
        _ ≤ a * ‖z‖ := mul_le_mul_of_nonneg_right hRnorm (norm_nonneg z)
    have hRzsq : ‖R z‖ ^ 2 ≤ a ^ 2 * ‖z‖ ^ 2 := by
      nlinarith [norm_nonneg (R z), norm_nonneg z]
    have hnormsq : ‖(P - S) y‖ ^ 2 = a ^ 2 * ‖p‖ ^ 2 + ‖R z‖ ^ 2 := by
      rw [hDy, norm_sub_sq (𝕜 := ℂ), inner_smul_left, hpRz, mul_zero, map_zero, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
      ring
    have hsquared : ‖(P - S) y‖ ^ 2 ≤ (a * ‖y‖) ^ 2 := by
      rw [hnormsq]
      nlinarith [sq_nonneg a, sq_nonneg (norm y)]
    nlinarith [norm_nonneg ((P - S) y), mul_nonneg ha (norm_nonneg y)]
  apply le_antisymm
  · simpa [P] using hupper
  · simpa [P] using norm_purityRankOneProjection_sub_ge_one_sub_norm S hx

theorem exists_rankOne_operator_distance_eq_purity_cost
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hpos : S.IsPositive) (hTr : ContinuousLinearMap.opTrace S = 1) :
    ∃ x : H, ‖x‖ = 1 ∧ ‖purityRankOneProjection x - S‖ = 1 - ‖S‖ := by
  obtain ⟨x, hx, heig, -⟩ := exists_top_positive_eigenvector hS hpos hTr
  exact ⟨x, hx, top_eigenvector_rankOne_operator_distance hS hpos hTr hx heig⟩

/-- Coordinate-free operator-norm distance from a state to pure rank-one projections. -/
noncomputable def operatorPureRadius (S : H →L[ℂ] H) : ℝ :=
  sInf {r : ℝ | ∃ x : H, ‖x‖ = 1 ∧ r = ‖purityRankOneProjection x - S‖}

/-- Coordinate-free trace-norm distance from a state to pure rank-one projections. -/
noncomputable def tracePureRadius (S : H →L[ℂ] H) : ℝ :=
  sInf {r : ℝ | ∃ x : H, ‖x‖ = 1 ∧ r = traceNorm H (purityRankOneProjection x - S)}

theorem operatorPureRadius_eq_one_sub_norm
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hpos : S.IsPositive) (hTr : ContinuousLinearMap.opTrace S = 1) :
    operatorPureRadius S = 1 - ‖S‖ := by
  obtain ⟨x, hx, hdist⟩ := exists_rankOne_operator_distance_eq_purity_cost hS hpos hTr
  let s : Set ℝ := {r : ℝ | ∃ y : H, ‖y‖ = 1 ∧ r = ‖purityRankOneProjection y - S‖}
  have hs_nonempty : s.Nonempty := ⟨1 - ‖S‖, x, hx, hdist.symm⟩
  have hs_lower : ∀ r ∈ s, 1 - ‖S‖ ≤ r := by
    rintro r ⟨y, hy, rfl⟩
    exact norm_purityRankOneProjection_sub_ge_one_sub_norm S hy
  have hs_bdd : BddBelow s := ⟨1 - ‖S‖, hs_lower⟩
  change sInf s = 1 - ‖S‖
  apply le_antisymm
  · exact csInf_le hs_bdd ⟨x, hx, hdist.symm⟩
  · exact le_csInf hs_nonempty hs_lower

theorem tracePureRadius_eq_two_mul_one_sub_norm
    {S : H →L[ℂ] H} (hS : MemSchattenClass 1 S)
    (hpos : S.IsPositive) (hTr : ContinuousLinearMap.opTrace S = 1) :
    tracePureRadius S = 2 * (1 - ‖S‖) := by
  obtain ⟨x, hx, hdist⟩ := exists_rankOne_traceNorm_distance_eq_purity_cost hS hpos hTr
  let s : Set ℝ := {r : ℝ | ∃ y : H, ‖y‖ = 1 ∧ r = traceNorm H (purityRankOneProjection y - S)}
  have hs_nonempty : s.Nonempty := ⟨2 * (1 - ‖S‖), x, hx, hdist.symm⟩
  have hs_lower : ∀ r ∈ s, 2 * (1 - ‖S‖) ≤ r := by
    rintro r ⟨y, hy, rfl⟩
    exact traceNorm_purityRankOneProjection_sub_ge_two_mul_one_sub_norm hS hTr hy
  have hs_bdd : BddBelow s := ⟨2 * (1 - ‖S‖), hs_lower⟩
  change sInf s = 2 * (1 - ‖S‖)
  apply le_antisymm
  · exact csInf_le hs_bdd ⟨x, hx, hdist.symm⟩
  · exact le_csInf hs_nonempty hs_lower

/-! ## Prime--Hodge source and primitive Euler firewall -/

theorem routePPrimitiveCollisionCubicTraceBudget_lt_115_div_216 :
    routePPrimitiveCollisionCubicTraceBudget < 115 / 216 := by
  calc
    routePPrimitiveCollisionCubicTraceBudget ≤
        (115 / 432 : ℝ) * ∑' p : Nat.Primes, invNatLogSq p :=
      routePPrimitiveCollisionCubicTraceBudget_le_primeInvLogSq
    _ < (115 / 432 : ℝ) * 2 := by
      exact mul_lt_mul_of_pos_left tsum_prime_invNatLogSq_lt_two (by norm_num)
    _ = 115 / 216 := by norm_num

theorem routePPrimitiveCollisionCubicTraceBudget_add_primeHodgePuritySource_norm_lt_one :
    routePPrimitiveCollisionCubicTraceBudget +
      ‖primeHodgeHistoryRelativeCurvaturePrimeLift‖ < 1 := by
  have hB := routePPrimitiveCollisionCubicTraceBudget_lt_115_div_216
  have hT := norm_primeHodgeHistoryRelativeCurvaturePrimeLift_le_one_third
  norm_num at hB hT ⊢
  linarith

theorem routePPrimitiveCollisionCubicTraceBudget_lt_two_thirds :
    routePPrimitiveCollisionCubicTraceBudget < 2 / 3 := by
  have hB := routePPrimitiveCollisionCubicTraceBudget_lt_115_div_216
  norm_num at hB ⊢
  linarith

theorem two_mul_routePPrimitiveCollisionCubicTraceBudget_lt_four_thirds :
    2 * routePPrimitiveCollisionCubicTraceBudget < 4 / 3 := by
  have hB := routePPrimitiveCollisionCubicTraceBudget_lt_115_div_216
  norm_num at hB ⊢
  linarith

theorem primeHodgePuritySource_operator_distance_gt_budget
    {x : PrimeHodgeHistoryHilbert} (hx : ‖x‖ = 1) :
    routePPrimitiveCollisionCubicTraceBudget <
      ‖purityRankOneProjection x - primeHodgeHistoryRelativeCurvaturePrimeLift‖ := by
  have hlower := norm_purityRankOneProjection_sub_ge_one_sub_norm
    primeHodgeHistoryRelativeCurvaturePrimeLift hx
  have hnorm := norm_primeHodgeHistoryRelativeCurvaturePrimeLift_le_one_third
  have hB := routePPrimitiveCollisionCubicTraceBudget_lt_two_thirds
  linarith

theorem primeHodgePuritySource_trace_distance_gt_two_budget
    {x : PrimeHodgeHistoryHilbert} (hx : ‖x‖ = 1) :
    2 * routePPrimitiveCollisionCubicTraceBudget <
      traceNorm PrimeHodgeHistoryHilbert
        (purityRankOneProjection x - primeHodgeHistoryRelativeCurvaturePrimeLift) := by
  have hlower := traceNorm_purityRankOneProjection_sub_ge_two_mul_one_sub_norm
    primeHodgeHistoryRelativeCurvaturePrimeLift_memSchattenClass_one
    opTrace_primeHodgeHistoryRelativeCurvaturePrimeLift hx
  have hnorm := norm_primeHodgeHistoryRelativeCurvaturePrimeLift_le_one_third
  have hB := two_mul_routePPrimitiveCollisionCubicTraceBudget_lt_four_thirds
  linarith

theorem primeHodgePuritySource_trace_distance_gt_four_thirds
    {x : PrimeHodgeHistoryHilbert} (hx : ‖x‖ = 1) :
    4 / 3 ≤ traceNorm PrimeHodgeHistoryHilbert
      (purityRankOneProjection x - primeHodgeHistoryRelativeCurvaturePrimeLift) := by
  have hlower := traceNorm_purityRankOneProjection_sub_ge_two_mul_one_sub_norm
    primeHodgeHistoryRelativeCurvaturePrimeLift_memSchattenClass_one
    opTrace_primeHodgeHistoryRelativeCurvaturePrimeLift hx
  have hnorm := norm_primeHodgeHistoryRelativeCurvaturePrimeLift_le_one_third
  norm_num at hnorm ⊢
  linarith

theorem no_budgeted_traceClass_additive_pure_landing
    {x : PrimeHodgeHistoryHilbert} (hx : ‖x‖ = 1) :
    ¬ ∃ R : PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert,
      MemSchattenClass 1 R ∧
      purityRankOneProjection x = primeHodgeHistoryRelativeCurvaturePrimeLift + R ∧
      traceNorm PrimeHodgeHistoryHilbert R ≤
        2 * routePPrimitiveCollisionCubicTraceBudget := by
  rintro ⟨R, -, hland, hbudget⟩
  have hR : purityRankOneProjection x - primeHodgeHistoryRelativeCurvaturePrimeLift = R := by
    rw [hland]
    abel
  have hcost := primeHodgePuritySource_trace_distance_gt_two_budget hx
  rw [hR] at hcost
  exact (not_lt_of_ge hbudget) hcost

theorem operatorPureRadius_primeHodgePuritySource :
    operatorPureRadius primeHodgeHistoryRelativeCurvaturePrimeLift =
      1 - ‖primeHodgeHistoryRelativeCurvaturePrimeLift‖ :=
  operatorPureRadius_eq_one_sub_norm
    primeHodgeHistoryRelativeCurvaturePrimeLift_memSchattenClass_one
    primeHodgeHistoryRelativeCurvaturePrimeLift_isPositive
    opTrace_primeHodgeHistoryRelativeCurvaturePrimeLift

theorem tracePureRadius_primeHodgePuritySource :
    tracePureRadius primeHodgeHistoryRelativeCurvaturePrimeLift =
      2 * (1 - ‖primeHodgeHistoryRelativeCurvaturePrimeLift‖) :=
  tracePureRadius_eq_two_mul_one_sub_norm
    primeHodgeHistoryRelativeCurvaturePrimeLift_memSchattenClass_one
    primeHodgeHistoryRelativeCurvaturePrimeLift_isPositive
    opTrace_primeHodgeHistoryRelativeCurvaturePrimeLift

theorem primeHodgePuritySource_operatorPath_variation_gt_budget
    {x : PrimeHodgeHistoryHilbert} (hx : ‖x‖ = 1)
    {K : ℝ → PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert}
    (hK0 : K 0 = primeHodgeHistoryRelativeCurvaturePrimeLift)
    (hK1 : K 1 = purityRankOneProjection x)
    (hvar : BoundedVariationOn K (Set.Icc 0 1)) :
    routePPrimitiveCollisionCubicTraceBudget <
      (eVariationOn K (Set.Icc 0 1)).toReal := by
  have hend : dist (K 1) (K 0) ≤ (eVariationOn K (Set.Icc 0 1)).toReal :=
    hvar.dist_le (by norm_num) (by norm_num)
  rw [hK1, hK0, dist_eq_norm] at hend
  exact (primeHodgePuritySource_operator_distance_gt_budget hx).trans_le hend

/-- Prime--Hodge source as an element of the genuine Schatten-one Banach carrier. -/
noncomputable def primeHodgePuritySourceSchattenOne :
    SchattenOneOperator PrimeHodgeHistoryHilbert :=
  ⟨primeHodgeHistoryRelativeCurvaturePrimeLift,
    primeHodgeHistoryRelativeCurvaturePrimeLift_memSchattenClass_one⟩

/-- Unit-vector rank-one projection as an element of the Schatten-one Banach carrier. -/
noncomputable def rankOneProjectionSchattenOne
    (x : PrimeHodgeHistoryHilbert) : SchattenOneOperator PrimeHodgeHistoryHilbert :=
  ⟨purityRankOneProjection x, purityRankOneProjection_memSchattenClass_one x⟩

theorem primeHodgePuritySource_traceClassPath_action_gt_two_budget
    {x : PrimeHodgeHistoryHilbert} (hx : ‖x‖ = 1)
    {K K' : ℝ → SchattenOneOperator PrimeHodgeHistoryHilbert}
    (hK0 : K 0 = primeHodgePuritySourceSchattenOne)
    (hK1 : K 1 = rankOneProjectionSchattenOne x)
    (hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt K (K' u) u)
    (hint : IntervalIntegrable K' MeasureTheory.volume 0 1) :
    2 * routePPrimitiveCollisionCubicTraceBudget <
      ∫ u in (0 : ℝ)..1, ‖K' u‖ := by
  have hcost : 2 * routePPrimitiveCollisionCubicTraceBudget < ‖K 1 - K 0‖ := by
    rw [hK1, hK0, SchattenOneOperator.norm_def]
    change 2 * routePPrimitiveCollisionCubicTraceBudget <
      traceNorm PrimeHodgeHistoryHilbert
        (purityRankOneProjection x - primeHodgeHistoryRelativeCurvaturePrimeLift)
    exact primeHodgePuritySource_trace_distance_gt_two_budget hx
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hnorm : ‖∫ u in (0 : ℝ)..1, K' u‖ ≤ ∫ u in (0 : ℝ)..1, ‖K' u‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by norm_num)
  rw [← hFTC] at hcost
  exact hcost.trans_le hnorm

/-- Closed certificate for the corrected prime--Hodge purity-cost firewall.  The actual corpus
source is the positive trace-one, cross-prime relative-curvature lift; its `1/3` norm ceiling is
strictly stronger than the ceiling needed for every endpoint, additive, variation, and action
obstruction above. -/
theorem primeHodgePurityCostFirewall :
    routePPrimitiveCollisionCubicTraceBudget < 115 / 216 ∧
    primeHodgeHistoryRelativeCurvaturePrimeLift.IsPositive ∧
    MemSchattenClass 1 primeHodgeHistoryRelativeCurvaturePrimeLift ∧
    ContinuousLinearMap.opTrace primeHodgeHistoryRelativeCurvaturePrimeLift = 1 ∧
    traceNorm PrimeHodgeHistoryHilbert
      primeHodgeHistoryRelativeCurvaturePrimeLift = 1 ∧
    ‖primeHodgeHistoryRelativeCurvaturePrimeLift‖ ≤ 1 / 3 ∧
    routePPrimitiveCollisionCubicTraceBudget +
      ‖primeHodgeHistoryRelativeCurvaturePrimeLift‖ < 1 ∧
    operatorPureRadius primeHodgeHistoryRelativeCurvaturePrimeLift =
      1 - ‖primeHodgeHistoryRelativeCurvaturePrimeLift‖ ∧
    tracePureRadius primeHodgeHistoryRelativeCurvaturePrimeLift =
      2 * (1 - ‖primeHodgeHistoryRelativeCurvaturePrimeLift‖) ∧
    (∀ x : PrimeHodgeHistoryHilbert, ‖x‖ = 1 →
      routePPrimitiveCollisionCubicTraceBudget <
        ‖purityRankOneProjection x - primeHodgeHistoryRelativeCurvaturePrimeLift‖) ∧
    (∀ x : PrimeHodgeHistoryHilbert, ‖x‖ = 1 →
      2 * routePPrimitiveCollisionCubicTraceBudget <
        traceNorm PrimeHodgeHistoryHilbert
          (purityRankOneProjection x - primeHodgeHistoryRelativeCurvaturePrimeLift)) ∧
    (∀ n : ℕ, ∀ p q : Nat.Primes,
      historyStokesKernel PrimeHodgeHistory.relativeCurvatureWeight 1
        ((n, p), (n, q)) ≠ 0) := by
  refine ⟨routePPrimitiveCollisionCubicTraceBudget_lt_115_div_216,
    primeHodgeHistoryRelativeCurvaturePrimeLift_isPositive,
    primeHodgeHistoryRelativeCurvaturePrimeLift_memSchattenClass_one,
    opTrace_primeHodgeHistoryRelativeCurvaturePrimeLift,
    traceNorm_primeHodgeHistoryRelativeCurvaturePrimeLift,
    norm_primeHodgeHistoryRelativeCurvaturePrimeLift_le_one_third,
    routePPrimitiveCollisionCubicTraceBudget_add_primeHodgePuritySource_norm_lt_one,
    operatorPureRadius_primeHodgePuritySource,
    tracePureRadius_primeHodgePuritySource, ?_, ?_, ?_⟩
  · exact fun _ hx => primeHodgePuritySource_operator_distance_gt_budget hx
  · exact fun _ hx => primeHodgePuritySource_trace_distance_gt_two_budget hx
  · exact primeHodgeHistoryRelativeCurvaturePrimeLift_sameHistory_ne_zero

end RHTower


