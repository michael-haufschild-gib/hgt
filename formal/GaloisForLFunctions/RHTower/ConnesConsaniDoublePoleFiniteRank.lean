import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity
import GaloisForLFunctions.HTGeometry.LpInjectionCompression
import GaloisForLFunctions.RHTower.CCMArchimedeanCircleTraceCocycle
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten

open Complex
open scoped ENNReal InnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Nonnegative circle Fourier index. -/
def ccmPositiveHardyIndex (n : ℕ) : ℤ := n

theorem ccmPositiveHardyIndex_injective : Function.Injective ccmPositiveHardyIndex := by
  intro m n h
  change (m : ℤ) = (n : ℤ) at h
  exact Int.ofNat_injective h

/-- Strictly negative circle Fourier index, ordered from `-1` downwards. -/
def ccmNegativeHardyIndex (n : ℕ) : ℤ := -((n + 1 : ℕ) : ℤ)

theorem ccmNegativeHardyIndex_injective : Function.Injective ccmNegativeHardyIndex := by
  intro m n h
  simp only [ccmNegativeHardyIndex, neg_inj] at h
  exact Nat.add_right_cancel (Int.ofNat_injective h)

/-- Source isometry from `ell^(2 : ℕ)(N)` to nonnegative circle Fourier modes. -/
def ccmPositiveHardyIsometry : HardyDisk →ₗᵢ[ℂ] CCMCircleL2 :=
  (fourierBasis (T := (1 : ℝ))).repr.symm.toLinearIsometry.comp
    (lpScalarInjection ccmPositiveHardyIndex ccmPositiveHardyIndex_injective)

/-- Source isometry from `ell^(2 : ℕ)(N)` to strictly negative circle Fourier modes. -/
def ccmNegativeHardyIsometry : HardyDisk →ₗᵢ[ℂ] CCMCircleL2 :=
  (fourierBasis (T := (1 : ℝ))).repr.symm.toLinearIsometry.comp
    (lpScalarInjection ccmNegativeHardyIndex ccmNegativeHardyIndex_injective)

@[simp] theorem ccmPositiveHardyIsometry_single (n : ℕ) :
    ccmPositiveHardyIsometry (lp.single 2 n 1) =
      (fourierLp 2 (n : ℤ) : CCMCircleL2) := by
  change (fourierBasis (T := (1 : ℝ))).repr.symm
      (lpScalarInjection ccmPositiveHardyIndex ccmPositiveHardyIndex_injective
        (lp.single 2 n 1)) = _
  rw [lpScalarInjection_single, HilbertBasis.repr_symm_single, coe_fourierBasis]
  rfl

@[simp] theorem ccmNegativeHardyIsometry_single (n : ℕ) :
    ccmNegativeHardyIsometry (lp.single 2 n 1) =
      (fourierLp 2 (-((n + 1 : ℕ) : ℤ)) : CCMCircleL2) := by
  change (fourierBasis (T := (1 : ℝ))).repr.symm
      (lpScalarInjection ccmNegativeHardyIndex ccmNegativeHardyIndex_injective
        (lp.single 2 n 1)) = _
  rw [lpScalarInjection_single, HilbertBasis.repr_symm_single, coe_fourierBasis]
  rfl

/-- Cayley image of the double pole in Connes--Consani Theorem 4.4. -/
def connesConsaniDoublePoleNode : ℂ := -(1 / 3)

theorem norm_connesConsaniDoublePoleNode_lt_one :
    ‖connesConsaniDoublePoleNode‖ < 1 := by
  rw [connesConsaniDoublePoleNode, norm_neg, norm_div, norm_one]
  norm_num

@[simp] theorem star_connesConsaniDoublePoleNode :
    (starRingEnd ℂ) connesConsaniDoublePoleNode =
      connesConsaniDoublePoleNode := by
  have hthree : (starRingEnd ℂ) (3 : ℂ) = 3 := by
    rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, map_add, map_add, map_one]
  rw [connesConsaniDoublePoleNode, map_neg, map_div₀, map_one, hthree]

/-- Geometric Hardy vector at the fixed double-pole node. -/
def connesConsaniDoublePoleKernel : HardyDisk :=
  hardyKernel norm_connesConsaniDoublePoleNode_lt_one

@[simp] theorem connesConsaniDoublePoleKernel_apply (n : ℕ) :
    connesConsaniDoublePoleKernel n = connesConsaniDoublePoleNode ^ n := by
  change ((starRingEnd ℂ) connesConsaniDoublePoleNode) ^ n = _
  congr 1
  have hthree : (starRingEnd ℂ) (3 : ℂ) = 3 := by
    rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, map_add, map_add, map_one]
  rw [connesConsaniDoublePoleNode, map_neg, map_div₀]
  rw [map_one, hthree]

theorem memlp_connesConsaniDoublePoleWeightedKernel :
    Memℓp (fun n : ℕ => (n : ℂ) * connesConsaniDoublePoleNode ^ n) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hgeom : ‖connesConsaniDoublePoleNode‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg connesConsaniDoublePoleNode,
      norm_connesConsaniDoublePoleNode_lt_one]
  have hratio : ‖(‖connesConsaniDoublePoleNode‖ ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hgeom
  have hsum : Summable (fun n : ℕ =>
      (n : ℝ) ^ 2 * (‖connesConsaniDoublePoleNode‖ ^ 2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hratio
  refine hsum.congr fun n => ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, norm_natCast,
    norm_pow]
  ring

/-- First derivative of the geometric Hardy kernel at the double-pole node. -/
def connesConsaniDoublePoleWeightedKernel : HardyDisk :=
  ⟨fun n => (n : ℂ) * connesConsaniDoublePoleNode ^ n,
    memlp_connesConsaniDoublePoleWeightedKernel⟩

@[simp] theorem connesConsaniDoublePoleWeightedKernel_apply (n : ℕ) :
    connesConsaniDoublePoleWeightedKernel n =
      (n : ℂ) * connesConsaniDoublePoleNode ^ n := rfl

theorem inner_fourierLp_ccmPositiveHardyIsometry (n : ℕ) (a : HardyDisk) :
    inner ℂ (fourierLp 2 (n : ℤ) : CCMCircleL2)
        (ccmPositiveHardyIsometry a) = a n := by
  rw [← ccmPositiveHardyIsometry_single n,
    ccmPositiveHardyIsometry.inner_map_map, lp.inner_single_left]
  simp

theorem inner_ccmNegativeHardyIsometry_fourierLp (n : ℕ) (a : HardyDisk) :
    inner ℂ (ccmNegativeHardyIsometry a)
        (fourierLp 2 (-((n + 1 : ℕ) : ℤ)) : CCMCircleL2) =
      (starRingEnd ℂ) (a n) := by
  rw [← ccmNegativeHardyIsometry_single n,
    ccmNegativeHardyIsometry.inner_map_map, lp.inner_single_right]
  rw [RCLike.inner_apply]
  simp

@[simp] theorem inner_fourierLp_ccmPositiveDoublePoleKernel (n : ℕ) :
    inner ℂ (fourierLp 2 (n : ℤ) : CCMCircleL2)
        (ccmPositiveHardyIsometry connesConsaniDoublePoleKernel) =
      connesConsaniDoublePoleNode ^ n := by
  rw [inner_fourierLp_ccmPositiveHardyIsometry,
    connesConsaniDoublePoleKernel_apply]

@[simp] theorem inner_ccmNegativeDoublePoleKernel_fourierLp (n : ℕ) :
    inner ℂ (ccmNegativeHardyIsometry connesConsaniDoublePoleKernel)
        (fourierLp 2 (-((n + 1 : ℕ) : ℤ)) : CCMCircleL2) =
      connesConsaniDoublePoleNode ^ n := by
  rw [inner_ccmNegativeHardyIsometry_fourierLp,
    connesConsaniDoublePoleKernel_apply, map_pow]
  congr 1
  have hthree : (starRingEnd ℂ) (3 : ℂ) = 3 := by
    rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, map_add, map_add, map_one]
  rw [connesConsaniDoublePoleNode, map_neg, map_div₀, map_one, hthree]

@[simp] theorem inner_fourierLp_ccmPositiveDoublePoleWeightedKernel (n : ℕ) :
    inner ℂ (fourierLp 2 (n : ℤ) : CCMCircleL2)
        (ccmPositiveHardyIsometry connesConsaniDoublePoleWeightedKernel) =
      (n : ℂ) * connesConsaniDoublePoleNode ^ n := by
  rw [inner_fourierLp_ccmPositiveHardyIsometry,
    connesConsaniDoublePoleWeightedKernel_apply]

@[simp] theorem inner_ccmNegativeDoublePoleWeightedKernel_fourierLp (n : ℕ) :
    inner ℂ (ccmNegativeHardyIsometry connesConsaniDoublePoleWeightedKernel)
        (fourierLp 2 (-((n + 1 : ℕ) : ℤ)) : CCMCircleL2) =
      (n : ℂ) * connesConsaniDoublePoleNode ^ n := by
  rw [inner_ccmNegativeHardyIsometry_fourierLp,
    connesConsaniDoublePoleWeightedKernel_apply, map_mul, map_pow]
  have hnat : (starRingEnd ℂ) (n : ℂ) = n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, map_add, map_one, ih]
  rw [hnat]
  congr 1
  have hthree : (starRingEnd ℂ) (3 : ℂ) = 3 := by
    rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, map_add, map_add, map_one]
  rw [connesConsaniDoublePoleNode, map_neg, map_div₀, map_one, hthree]

@[simp] theorem inner_ccmPositiveDoublePoleKernel_fourierLp (n : ℕ) :
    inner ℂ (ccmPositiveHardyIsometry connesConsaniDoublePoleKernel)
        (fourierLp 2 (n : ℤ) : CCMCircleL2) =
      connesConsaniDoublePoleNode ^ n := by
  rw [← inner_conj_symm, inner_fourierLp_ccmPositiveDoublePoleKernel,
    map_pow, star_connesConsaniDoublePoleNode]

@[simp] theorem inner_ccmPositiveDoublePoleWeightedKernel_fourierLp (n : ℕ) :
    inner ℂ (ccmPositiveHardyIsometry connesConsaniDoublePoleWeightedKernel)
        (fourierLp 2 (n : ℤ) : CCMCircleL2) =
      (n : ℂ) * connesConsaniDoublePoleNode ^ n := by
  rw [← inner_conj_symm, inner_fourierLp_ccmPositiveDoublePoleWeightedKernel,
    map_mul, map_natCast, map_pow, star_connesConsaniDoublePoleNode]

@[simp] theorem inner_fourierLp_ccmNegativeDoublePoleKernel (n : ℕ) :
    inner ℂ (fourierLp 2 (-((n + 1 : ℕ) : ℤ)) : CCMCircleL2)
        (ccmNegativeHardyIsometry connesConsaniDoublePoleKernel) =
      connesConsaniDoublePoleNode ^ n := by
  rw [← inner_conj_symm, inner_ccmNegativeDoublePoleKernel_fourierLp,
    map_pow, star_connesConsaniDoublePoleNode]

@[simp] theorem inner_fourierLp_ccmNegativeDoublePoleWeightedKernel (n : ℕ) :
    inner ℂ (fourierLp 2 (-((n + 1 : ℕ) : ℤ)) : CCMCircleL2)
        (ccmNegativeHardyIsometry connesConsaniDoublePoleWeightedKernel) =
      (n : ℂ) * connesConsaniDoublePoleNode ^ n := by
  rw [← inner_conj_symm, inner_ccmNegativeDoublePoleWeightedKernel_fourierLp,
    map_mul, map_natCast, map_pow, star_connesConsaniDoublePoleNode]

/-- Double-pole linear coefficient in Connes--Consani Theorem 4.4. -/
def connesConsaniDoublePoleBeta (p : Nat.Primes) : ℂ :=
  -128 * ((p : ℂ) - 1) / (27 * (p : ℂ) * Real.log p)

/-- Double-pole constant coefficient in Connes--Consani Theorem 4.4. -/
def connesConsaniDoublePoleAlpha (p : Nat.Primes) : ℂ :=
  8 / (27 * (p : ℂ) * Real.log p) *
    (((p : ℂ) - 1) *
        (3 * Real.eulerMascheroniConstant - 8 + 6 * Real.log Real.pi -
          3 * Complex.digamma (1 / 2)) -
      3 * ((p : ℂ) - 3) * Real.log p)

/-- First range vector in the source double-pole block. -/
def connesConsaniDoublePoleRangeOne (p : Nat.Primes) : CCMCircleL2 :=
  connesConsaniDoublePoleAlpha p •
      ccmNegativeHardyIsometry connesConsaniDoublePoleKernel +
    connesConsaniDoublePoleBeta p •
      ccmNegativeHardyIsometry connesConsaniDoublePoleWeightedKernel

/-- Second range vector in the source double-pole block. -/
def connesConsaniDoublePoleRangeTwo (p : Nat.Primes) : CCMCircleL2 :=
  connesConsaniDoublePoleBeta p •
    ccmNegativeHardyIsometry connesConsaniDoublePoleKernel

/-- Exact finite-rank contribution of the double pole at zero in the paper Hardy coordinate of
Theorem 4.4. -/
def connesConsaniDoublePoleOperator (p : Nat.Primes) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  InnerProductSpace.rankOne ℂ (connesConsaniDoublePoleRangeOne p)
      (ccmPositiveHardyIsometry connesConsaniDoublePoleKernel) +
    InnerProductSpace.rankOne ℂ (connesConsaniDoublePoleRangeTwo p)
      (ccmPositiveHardyIsometry connesConsaniDoublePoleWeightedKernel)

/-- Exact Fourier matrix of the double-pole contribution. -/
theorem inner_fourierLp_connesConsaniDoublePoleOperator_fourierLp
    (p : Nat.Primes) (r s : ℕ) :
    inner ℂ (fourierLp 2 (-((r + 1 : ℕ) : ℤ)) : CCMCircleL2)
        (connesConsaniDoublePoleOperator p
          (fourierLp 2 (s : ℤ) : CCMCircleL2)) =
      connesConsaniDoublePoleAlpha p *
          connesConsaniDoublePoleNode ^ (r + s) +
        connesConsaniDoublePoleBeta p * ((r + s : ℕ) : ℂ) *
          connesConsaniDoublePoleNode ^ (r + s) := by
  rw [connesConsaniDoublePoleOperator, add_apply,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    inner_add_right, inner_smul_right, inner_smul_right]
  simp only [connesConsaniDoublePoleRangeOne,
    connesConsaniDoublePoleRangeTwo]
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right]
  simp only [inner_ccmPositiveDoublePoleKernel_fourierLp,
    inner_ccmPositiveDoublePoleWeightedKernel_fourierLp,
    inner_fourierLp_ccmNegativeDoublePoleKernel,
    inner_fourierLp_ccmNegativeDoublePoleWeightedKernel]
  rw [pow_add]
  push_cast
  ring

/-- The double-pole contribution has rank at most two. -/
theorem connesConsaniDoublePoleOperator_hasRankLE_two (p : Nat.Primes) :
    HasRankLE (connesConsaniDoublePoleOperator p) 2 := by
  classical
  let v : Bool → CCMCircleL2 := fun b =>
    if b then connesConsaniDoublePoleRangeOne p
    else connesConsaniDoublePoleRangeTwo p
  let V : Submodule ℂ CCMCircleL2 := Submodule.span ℂ (Set.range v)
  have hVfd : FiniteDimensional ℂ V :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  refine ⟨V, hVfd, ?_, fun z => ?_⟩
  · letI := hVfd
    refine le_trans (finrank_span_le_card (R := ℂ) (Set.range v)) ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  · rw [connesConsaniDoublePoleOperator, add_apply,
      InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply]
    exact V.add_mem
      (V.smul_mem _ (Submodule.subset_span ⟨true, by simp [v]⟩))
      (V.smul_mem _ (Submodule.subset_span ⟨false, by simp [v]⟩))

/-- The double-pole contribution is trace class. -/
theorem connesConsaniDoublePoleOperator_memSchattenClass_one (p : Nat.Primes) :
    MemSchattenClass 1 (connesConsaniDoublePoleOperator p) :=
  memSchattenClass_of_hasRankLE one_pos
    (connesConsaniDoublePoleOperator_hasRankLE_two p)

end

end RHTower
