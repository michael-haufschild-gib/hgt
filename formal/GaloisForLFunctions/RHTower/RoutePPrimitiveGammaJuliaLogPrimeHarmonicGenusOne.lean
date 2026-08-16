import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaLogCofinalTraceNoGo
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.HTGeometry.FredholmDeterminantInfinite
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalDeterminant
import GaloisForLFunctions.HTGeometry.CountableSeparableInteractionOperatorLaw

/-!
# SP-E prime-harmonic genus-one carrier

P-G105H proves that literal prime-log promotion of joint prime-depth source has diagonal
weight `w(p,e) = (1/4) p^{-(e+1)} (e+1)^{-3}`.

Its depth-zero face is non-summable Euler density `1/(4p)`. Previous Stokes transport
canceled this pole to recover a trace-class child, but multiplicity-exact Xi divisor cannot be
reciprocal spectrum of any trace-class operator. This file retains rather than cancels Euler
face and proves resulting exact source density lies in `l2` but not `l1`.

Diagonal source operator is self-adjoint Hilbert--Schmidt and provably not Schatten-one.
Forced balanced Hellinger spectrum supplies signs `+8` and `-8`, producing second
self-adjoint Hilbert--Schmidt/non-trace-class operator and its entire Hilbert--Carleman `det2`.
Its zero divisor is classified exactly as `z = (plus-or-minus 8 w(p,e))^-1`.

Thus SP-E now has literal source-native genus-one determinant with symmetric real zeros. This
does not identify explicit prime-depth divisor with Xi; that arithmetic divisor comparison
remains separate. No Xi zero or coefficient is used in this construction.
-/
open scoped BigOperators InnerProductSpace

namespace RHTower

noncomputable section

theorem routePPrimitiveGammaJuliaLogCofinalTraceWeight_sq_le_geometric
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveGammaJuliaLogCofinalTraceWeight pe ^ 2 ≤
      (1 / 16 : ℝ) * (1 / (pe.1 : ℝ) ^ 2) * (1 / 4 : ℝ) ^ pe.2 := by
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by exact_mod_cast pe.1.property.pos
  have hp2 : (2 : ℝ) ≤ (pe.1 : ℝ) := by exact_mod_cast pe.1.property.two_le
  have hpInv : (pe.1 : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using
      (inv_le_inv₀ hp (by norm_num : (0 : ℝ) < 2)).2 hp2
  have hpPow : ((pe.1 : ℝ)⁻¹) ^ pe.2 ≤ (1 / 2 : ℝ) ^ pe.2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hpInv pe.2
  have hkOne : (1 : ℝ) ≤ (pe.2 : ℝ) + 1 := by
    exact_mod_cast Nat.le_add_left 1 pe.2
  have hkPow : (1 : ℝ) ≤ ((pe.2 : ℝ) + 1) ^ 3 := one_le_pow₀ hkOne
  have hkInv : (((pe.2 : ℝ) + 1) ^ 3)⁻¹ ≤ (1 : ℝ) := by
    simpa using
      (inv_le_inv₀ (by positivity : 0 < ((pe.2 : ℝ) + 1) ^ 3)
        (by norm_num : (0 : ℝ) < 1)).2 hkPow
  rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight_eq]
  have hbase : 0 ≤ (1 / 4 : ℝ) * ((pe.1 : ℝ)⁻¹) := by positivity
  have htail :
      (1 / 4 : ℝ) * ((pe.1 : ℝ)⁻¹) *
          (((pe.1 : ℝ)⁻¹) ^ pe.2 * (((pe.2 : ℝ) + 1) ^ 3)⁻¹) ≤
        (1 / 4 : ℝ) * ((pe.1 : ℝ)⁻¹) * (1 / 2 : ℝ) ^ pe.2 := by
    apply mul_le_mul_of_nonneg_left _ hbase
    calc
      ((pe.1 : ℝ)⁻¹) ^ pe.2 * (((pe.2 : ℝ) + 1) ^ 3)⁻¹ ≤
          ((pe.1 : ℝ)⁻¹) ^ pe.2 * 1 := by
        gcongr
      _ ≤ (1 / 2 : ℝ) ^ pe.2 := by simpa using hpPow
  have hnonneg :
      0 ≤ (1 / 4 : ℝ) * ((pe.1 : ℝ)⁻¹) *
        (((pe.1 : ℝ)⁻¹) ^ pe.2 * (((pe.2 : ℝ) + 1) ^ 3)⁻¹) := by positivity
  have hnonneg' :
      0 ≤ (1 / 4 : ℝ) * ((pe.1 : ℝ)⁻¹) * (1 / 2 : ℝ) ^ pe.2 := by positivity
  calc
    ((1 / 4 : ℝ) * ((pe.1 : ℝ)⁻¹) ^ (pe.2 + 1) *
          (((pe.2 : ℝ) + 1) ^ 3)⁻¹) ^ 2 =
        ((1 / 4 : ℝ) * ((pe.1 : ℝ)⁻¹) *
          (((pe.1 : ℝ)⁻¹) ^ pe.2 * (((pe.2 : ℝ) + 1) ^ 3)⁻¹)) ^ 2 := by
      rw [pow_succ]
      ring
    _ ≤ ((1 / 4 : ℝ) * ((pe.1 : ℝ)⁻¹) * (1 / 2 : ℝ) ^ pe.2) ^ 2 :=
      (sq_le_sq₀ hnonneg hnonneg').2 htail
    _ = (1 / 16 : ℝ) * ((pe.1 : ℝ)⁻¹) ^ 2 *
          (((1 / 2 : ℝ) ^ 2) ^ pe.2) := by
      ring_nf
      rw [mul_comm pe.2 2, pow_mul]
      norm_num
    _ = (1 / 16 : ℝ) * (1 / (pe.1 : ℝ) ^ 2) * (1 / 4 : ℝ) ^ pe.2 := by
      simp only [one_div, inv_pow]
      norm_num

theorem summable_routePPrimitiveGammaJuliaLogCofinalTraceWeight_sq :
    Summable (fun pe : Nat.Primes × ℕ =>
      routePPrimitiveGammaJuliaLogCofinalTraceWeight pe ^ 2) := by
  let major : Nat.Primes × ℕ → ℝ := fun pe =>
    (1 / 16 : ℝ) * (1 / (pe.1 : ℝ) ^ 2) * (1 / 4 : ℝ) ^ pe.2
  have hmajorNonneg : 0 ≤ major := by
    intro pe
    dsimp only [major]
    positivity
  have hmajor : Summable major := by
    rw [summable_prod_of_nonneg hmajorNonneg]
    constructor
    · intro p
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
        ((1 / 16 : ℝ) * (1 / (p : ℝ) ^ 2))
    · apply (burnolSummable_prime_one_div_sq.mul_left (1 / 12 : ℝ)).congr
      intro p
      dsimp only [major]
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
  exact Summable.of_nonneg_of_le
    (fun pe => sq_nonneg _)
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_sq_le_geometric
    hmajor

def routePPrimitiveGammaJuliaLogDiagonalKernel
    (ij : (Nat.Primes × ℕ) × (Nat.Primes × ℕ)) : ℂ :=
  HilbertSchmidt.diagMul
    (fun pe => (routePPrimitiveGammaJuliaLogCofinalTraceWeight pe : ℂ)) ij

theorem routePPrimitiveGammaJuliaLogDiagonalKernel_isHS :
    HilbertSchmidt.IsHS routePPrimitiveGammaJuliaLogDiagonalKernel := by
  apply HilbertSchmidt.isHS_diagMul_infinite
  exact summable_routePPrimitiveGammaJuliaLogCofinalTraceWeight_sq.congr
    fun pe => by
      simp [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (routePPrimitiveGammaJuliaLogCofinalTraceWeight_nonneg pe)]

def routePPrimitiveGammaJuliaLogDiagonalOperator :
    XiGammaEulerPrimitiveJointDepthHilbert →L[ℂ]
      XiGammaEulerPrimitiveJointDepthHilbert :=
  HilbertSchmidt.toOperator routePPrimitiveGammaJuliaLogDiagonalKernel_isHS

theorem routePPrimitiveGammaJuliaLogDiagonalOperator_isHilbertSchmidt :
    routePPrimitiveGammaJuliaLogDiagonalOperator.IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator
    routePPrimitiveGammaJuliaLogDiagonalKernel_isHS

theorem routePPrimitiveGammaJuliaLogDiagonalOperator_basis
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveGammaJuliaLogDiagonalOperator
        (HilbertSchmidt.lpBasis (Nat.Primes × ℕ) pe) =
      (routePPrimitiveGammaJuliaLogCofinalTraceWeight pe : ℂ) •
        HilbertSchmidt.lpBasis (Nat.Primes × ℕ) pe := by
  apply lp.ext
  funext q
  rw [routePPrimitiveGammaJuliaLogDiagonalOperator,
    HilbertSchmidt.lpBasis_apply,
    HilbertSchmidt.toOperator_single
      routePPrimitiveGammaJuliaLogDiagonalKernel_isHS]
  change routePPrimitiveGammaJuliaLogDiagonalKernel (q, pe) =
    ((routePPrimitiveGammaJuliaLogCofinalTraceWeight pe : ℂ) •
      (lp.single 2 pe 1 : XiGammaEulerPrimitiveJointDepthHilbert)) q
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hq : q = pe
  · subst q
    simp [routePPrimitiveGammaJuliaLogDiagonalKernel,
      HilbertSchmidt.diagMul]
  · simp [routePPrimitiveGammaJuliaLogDiagonalKernel,
      HilbertSchmidt.diagMul, hq]

theorem routePPrimitiveGammaJuliaLogDiagonalKernel_hsAdjoint :
    HilbertSchmidt.hsAdjoint routePPrimitiveGammaJuliaLogDiagonalKernel =
      routePPrimitiveGammaJuliaLogDiagonalKernel := by
  funext ij
  rcases ij with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    simp [HilbertSchmidt.hsAdjoint,
      routePPrimitiveGammaJuliaLogDiagonalKernel, HilbertSchmidt.diagMul]
  · have hji : j ≠ i := Ne.symm hij
    simp [HilbertSchmidt.hsAdjoint,
      routePPrimitiveGammaJuliaLogDiagonalKernel, HilbertSchmidt.diagMul,
      hij, hji]

theorem routePPrimitiveGammaJuliaLogDiagonalOperator_isSelfAdjoint :
    IsSelfAdjoint routePPrimitiveGammaJuliaLogDiagonalOperator := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',
    routePPrimitiveGammaJuliaLogDiagonalOperator,
    HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _
    routePPrimitiveGammaJuliaLogDiagonalKernel_hsAdjoint

theorem routePPrimitiveGammaJuliaLogDiagonalOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 routePPrimitiveGammaJuliaLogDiagonalOperator := by
  intro htrace
  have hdiag := htrace.one_summable_inner_diag_basis
    (HilbertSchmidt.lpBasis (Nat.Primes × ℕ))
  have hcomplex : Summable (fun pe : Nat.Primes × ℕ =>
      (routePPrimitiveGammaJuliaLogCofinalTraceWeight pe : ℂ)) := by
    apply hdiag.congr
    intro pe
    rw [routePPrimitiveGammaJuliaLogDiagonalOperator_basis]
    rw [inner_smul_right]
    have hnorm :=
      (HilbertSchmidt.lpBasis (Nat.Primes × ℕ)).orthonormal.1 pe
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  exact routePPrimitiveGammaJuliaLogCofinalTraceWeight_not_summable
    (Complex.summable_ofReal.mp hcomplex)

def routePPrimitiveGammaJuliaLogBalancedSpectralSign (i : Fin 2) : ℝ :=
  if i = 0 then 8 else -8

theorem routePPrimitiveGammaJuliaLogBalancedSpectralSign_sq (i : Fin 2) :
    routePPrimitiveGammaJuliaLogBalancedSpectralSign i ^ 2 = 64 := by
  fin_cases i <;>
    simp [routePPrimitiveGammaJuliaLogBalancedSpectralSign] <;> norm_num

def routePPrimitiveGammaJuliaLogBalancedMultiplier
    (ip : Fin 2 × (Nat.Primes × ℕ)) : ℂ :=
  (routePPrimitiveGammaJuliaLogBalancedSpectralSign ip.1 : ℂ) *
    (routePPrimitiveGammaJuliaLogCofinalTraceWeight ip.2 : ℂ)

theorem summable_norm_routePPrimitiveGammaJuliaLogBalancedMultiplier_sq :
    Summable (fun ip : Fin 2 × (Nat.Primes × ℕ) =>
      ‖routePPrimitiveGammaJuliaLogBalancedMultiplier ip‖ ^ 2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro i
    have hw : Summable (fun pe : Nat.Primes × ℕ =>
        ‖(routePPrimitiveGammaJuliaLogCofinalTraceWeight pe : ℂ)‖ ^ 2) :=
      summable_routePPrimitiveGammaJuliaLogCofinalTraceWeight_sq.congr
        (fun pe => by
          simp [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (routePPrimitiveGammaJuliaLogCofinalTraceWeight_nonneg pe)])
    apply (hw.mul_left
      (‖(routePPrimitiveGammaJuliaLogBalancedSpectralSign i : ℂ)‖ ^ 2)).congr
    intro pe
    simp only [routePPrimitiveGammaJuliaLogBalancedMultiplier,
      norm_mul, mul_pow]
  · exact Summable.of_finite

def routePPrimitiveGammaJuliaLogBalancedKernel
    (ij : (Fin 2 × (Nat.Primes × ℕ)) ×
      (Fin 2 × (Nat.Primes × ℕ))) : ℂ :=
  HilbertSchmidt.diagMul
    routePPrimitiveGammaJuliaLogBalancedMultiplier ij

theorem routePPrimitiveGammaJuliaLogBalancedKernel_isHS :
    HilbertSchmidt.IsHS routePPrimitiveGammaJuliaLogBalancedKernel := by
  exact HilbertSchmidt.isHS_diagMul_infinite
    routePPrimitiveGammaJuliaLogBalancedMultiplier
    summable_norm_routePPrimitiveGammaJuliaLogBalancedMultiplier_sq

abbrev RoutePPrimitiveGammaJuliaLogBalancedHilbert : Type :=
  lp (fun _ : Fin 2 × (Nat.Primes × ℕ) => ℂ) 2

def routePPrimitiveGammaJuliaLogBalancedOperator :
    RoutePPrimitiveGammaJuliaLogBalancedHilbert →L[ℂ]
      RoutePPrimitiveGammaJuliaLogBalancedHilbert :=
  HilbertSchmidt.toOperator routePPrimitiveGammaJuliaLogBalancedKernel_isHS

theorem routePPrimitiveGammaJuliaLogBalancedOperator_basis
    (ip : Fin 2 × (Nat.Primes × ℕ)) :
    routePPrimitiveGammaJuliaLogBalancedOperator
        (HilbertSchmidt.lpBasis (Fin 2 × (Nat.Primes × ℕ)) ip) =
      routePPrimitiveGammaJuliaLogBalancedMultiplier ip •
        HilbertSchmidt.lpBasis (Fin 2 × (Nat.Primes × ℕ)) ip := by
  apply lp.ext
  funext jq
  rw [routePPrimitiveGammaJuliaLogBalancedOperator,
    HilbertSchmidt.lpBasis_apply,
    HilbertSchmidt.toOperator_single
      routePPrimitiveGammaJuliaLogBalancedKernel_isHS]
  change routePPrimitiveGammaJuliaLogBalancedKernel (jq, ip) =
    (routePPrimitiveGammaJuliaLogBalancedMultiplier ip •
      (lp.single 2 ip 1 : RoutePPrimitiveGammaJuliaLogBalancedHilbert)) jq
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hq : jq = ip
  · subst jq
    simp [routePPrimitiveGammaJuliaLogBalancedKernel,
      HilbertSchmidt.diagMul]
  · simp [routePPrimitiveGammaJuliaLogBalancedKernel,
      HilbertSchmidt.diagMul, hq]

theorem routePPrimitiveGammaJuliaLogBalancedKernel_hsAdjoint :
    HilbertSchmidt.hsAdjoint routePPrimitiveGammaJuliaLogBalancedKernel =
      routePPrimitiveGammaJuliaLogBalancedKernel := by
  funext ij
  rcases ij with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    simp [HilbertSchmidt.hsAdjoint,
      routePPrimitiveGammaJuliaLogBalancedKernel, HilbertSchmidt.diagMul,
      routePPrimitiveGammaJuliaLogBalancedMultiplier]
  · have hji : j ≠ i := Ne.symm hij
    simp [HilbertSchmidt.hsAdjoint,
      routePPrimitiveGammaJuliaLogBalancedKernel, HilbertSchmidt.diagMul,
      hij, hji]

theorem routePPrimitiveGammaJuliaLogBalancedOperator_isSelfAdjoint :
    IsSelfAdjoint routePPrimitiveGammaJuliaLogBalancedOperator := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',
    routePPrimitiveGammaJuliaLogBalancedOperator,
    HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _
    routePPrimitiveGammaJuliaLogBalancedKernel_hsAdjoint

theorem routePPrimitiveGammaJuliaLogBalancedOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 routePPrimitiveGammaJuliaLogBalancedOperator := by
  intro htrace
  have hdiag := htrace.one_summable_inner_diag_basis
    (HilbertSchmidt.lpBasis (Fin 2 × (Nat.Primes × ℕ)))
  have hside : Summable (fun pe : Nat.Primes × ℕ =>
      (8 : ℂ) * (routePPrimitiveGammaJuliaLogCofinalTraceWeight pe : ℂ)) := by
    have hcomp := hdiag.comp_injective
      (i := fun pe : Nat.Primes × ℕ => (0, pe))
      (fun _ _ h => congrArg Prod.snd h)
    apply hcomp.congr
    intro pe
    simp only [Function.comp_apply]
    rw [routePPrimitiveGammaJuliaLogBalancedOperator_basis]
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    have hnorm :=
      (HilbertSchmidt.lpBasis (Fin 2 × (Nat.Primes × ℕ))).orthonormal.1 (0, pe)
    rw [hnorm]
    simp [routePPrimitiveGammaJuliaLogBalancedMultiplier,
      routePPrimitiveGammaJuliaLogBalancedSpectralSign]
  have hcomplex : Summable (fun pe : Nat.Primes × ℕ =>
      (routePPrimitiveGammaJuliaLogCofinalTraceWeight pe : ℂ)) :=
    (summable_mul_left_iff (by norm_num : (8 : ℂ) ≠ 0)).mp hside
  exact routePPrimitiveGammaJuliaLogCofinalTraceWeight_not_summable
    (Complex.summable_ofReal.mp hcomplex)

def routePPrimitiveGammaJuliaLogBalancedEntireDet2 : ℂ → ℂ :=
  GaloisForLFunctions.HTGeometry.entireDet2
    routePPrimitiveGammaJuliaLogBalancedKernel

theorem differentiable_routePPrimitiveGammaJuliaLogBalancedEntireDet2 :
    Differentiable ℂ routePPrimitiveGammaJuliaLogBalancedEntireDet2 :=
  GaloisForLFunctions.HTGeometry.differentiable_entireDet2
    routePPrimitiveGammaJuliaLogBalancedKernel_isHS

theorem routePPrimitiveGammaJuliaLogBalancedEntireDet2_zero_im
    {z : ℂ} (hz : routePPrimitiveGammaJuliaLogBalancedEntireDet2 z = 0) :
    z.im = 0 := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    have hone :=
      (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
        routePPrimitiveGammaJuliaLogBalancedKernel_isHS).eq_one_at_zero
    exact one_ne_zero (hone.symm.trans hz)
  obtain ⟨w, hw0, hw⟩ :=
    GaloisForLFunctions.HTGeometry.exists_eigenvector_of_entireDet2_eq_zero
      routePPrimitiveGammaJuliaLogBalancedKernel_isHS hz0 hz
  let T := routePPrimitiveGammaJuliaLogBalancedOperator
  have heig : Module.End.HasEigenvalue
      (T : Module.End ℂ RoutePPrimitiveGammaJuliaLogBalancedHilbert) z⁻¹ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hw0⟩
    rw [Module.End.mem_eigenspace_iff]
    exact hw
  have hrealInv : star z⁻¹ = z⁻¹ :=
    routePPrimitiveGammaJuliaLogBalancedOperator_isSelfAdjoint.isSymmetric
      |>.conj_eigenvalue_eq_self heig
  have himInv : z⁻¹.im = 0 := Complex.conj_eq_iff_im.mp hrealInv
  rw [Complex.inv_im] at himInv
  have hnorm : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz0).ne'
  exact neg_eq_zero.mp (div_eq_zero_iff.mp himInv |>.resolve_right hnorm)

theorem routePPrimitiveGammaJuliaLogBalancedMultiplier_ne_zero
    (ip : Fin 2 × (Nat.Primes × ℕ)) :
    routePPrimitiveGammaJuliaLogBalancedMultiplier ip ≠ 0 := by
  apply mul_ne_zero
  · rcases ip with ⟨i, pe⟩
    fin_cases i <;>
      simp [routePPrimitiveGammaJuliaLogBalancedSpectralSign]
  · apply Complex.ofReal_ne_zero.mpr
    have hpos : 0 < routePPrimitiveGammaJuliaLogCofinalTraceWeight ip.2 := by
      rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight_eq]
      have hp : 0 < (ip.2.1 : ℝ) := by
        exact_mod_cast ip.2.1.property.pos
      have he : 0 < (ip.2.2 : ℝ) + 1 := by positivity
      exact mul_pos
        (mul_pos (by norm_num) (pow_pos (inv_pos.mpr hp) _))
        (inv_pos.mpr (pow_pos he 3))
    exact hpos.ne'

theorem routePPrimitiveGammaJuliaLogBalancedEntireDet2_zero_iff
    {z : ℂ} :
    routePPrimitiveGammaJuliaLogBalancedEntireDet2 z = 0 ↔
      ∃ ip : Fin 2 × (Nat.Primes × ℕ),
        z = (routePPrimitiveGammaJuliaLogBalancedMultiplier ip)⁻¹ := by
  constructor
  · intro hz
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      have hone :=
        (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
          routePPrimitiveGammaJuliaLogBalancedKernel_isHS).eq_one_at_zero
      exact one_ne_zero (hone.symm.trans hz)
    obtain ⟨w, hw0, hw⟩ :=
      GaloisForLFunctions.HTGeometry.exists_eigenvector_of_entireDet2_eq_zero
        routePPrimitiveGammaJuliaLogBalancedKernel_isHS hz0 hz
    have hexists : ∃ ip : Fin 2 × (Nat.Primes × ℕ), w ip ≠ 0 := by
      by_contra hnone
      apply hw0
      apply lp.ext
      funext ip
      by_contra hip
      exact hnone ⟨ip, hip⟩
    obtain ⟨ip, hip⟩ := hexists
    have hcoord := congrArg (fun x : RoutePPrimitiveGammaJuliaLogBalancedHilbert => x ip) hw
    change routePPrimitiveGammaJuliaLogBalancedOperator w ip = (z⁻¹ • w) ip at hcoord
    have happ := GaloisForLFunctions.HTGeometry.toOperator_diagMul_apply
      routePPrimitiveGammaJuliaLogBalancedMultiplier
      summable_norm_routePPrimitiveGammaJuliaLogBalancedMultiplier_sq w ip
    change routePPrimitiveGammaJuliaLogBalancedOperator w ip =
      routePPrimitiveGammaJuliaLogBalancedMultiplier ip * w ip at happ
    rw [happ] at hcoord
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hcoord
    have heig : routePPrimitiveGammaJuliaLogBalancedMultiplier ip = z⁻¹ := by
      exact mul_right_cancel₀ hip hcoord
    refine ⟨ip, ?_⟩
    rw [heig, inv_inv]
  · rintro ⟨ip, rfl⟩
    have hmult := routePPrimitiveGammaJuliaLogBalancedMultiplier_ne_zero ip
    apply (GaloisForLFunctions.HTGeometry.entireDet2_eq_zero_iff_exists_eigenvector
      routePPrimitiveGammaJuliaLogBalancedKernel_isHS (inv_ne_zero hmult)).2
    let e := HilbertSchmidt.lpBasis (Fin 2 × (Nat.Primes × ℕ)) ip
    have he0 : e ≠ 0 := by
      intro he
      have hnorm :=
        (HilbertSchmidt.lpBasis
          (Fin 2 × (Nat.Primes × ℕ))).orthonormal.1 ip
      change ‖e‖ = 1 at hnorm
      rw [he, norm_zero] at hnorm
      norm_num at hnorm
    refine ⟨e, he0, ?_⟩
    change routePPrimitiveGammaJuliaLogBalancedOperator e =
      ((routePPrimitiveGammaJuliaLogBalancedMultiplier ip)⁻¹)⁻¹ • e
    rw [routePPrimitiveGammaJuliaLogBalancedOperator_basis, inv_inv]

/-- **SP-E genus-one capstone.** Literal prime-log source density is square-summable but not
summable. Its forced balanced signed channel is self-adjoint Hilbert--Schmidt, not Schatten-one,
and its entire `det₂` has exactly explicit symmetric real reciprocal source zeros. -/
theorem routePPrimitive_GammaJulia_logPrimeHarmonicGenusOne :
    Summable (fun pe : Nat.Primes × ℕ =>
      routePPrimitiveGammaJuliaLogCofinalTraceWeight pe ^ 2) ∧
    (¬ Summable routePPrimitiveGammaJuliaLogCofinalTraceWeight) ∧
    HilbertSchmidt.IsHS routePPrimitiveGammaJuliaLogBalancedKernel ∧
    IsSelfAdjoint routePPrimitiveGammaJuliaLogBalancedOperator ∧
    (¬ MemSchattenClass 1 routePPrimitiveGammaJuliaLogBalancedOperator) ∧
    (∀ z : ℂ,
      routePPrimitiveGammaJuliaLogBalancedEntireDet2 z = 0 ↔
        ∃ ip : Fin 2 × (Nat.Primes × ℕ),
          z = (routePPrimitiveGammaJuliaLogBalancedMultiplier ip)⁻¹) := by
  exact ⟨summable_routePPrimitiveGammaJuliaLogCofinalTraceWeight_sq,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_not_summable,
    routePPrimitiveGammaJuliaLogBalancedKernel_isHS,
    routePPrimitiveGammaJuliaLogBalancedOperator_isSelfAdjoint,
    routePPrimitiveGammaJuliaLogBalancedOperator_not_memSchattenClass_one,
    fun _ => routePPrimitiveGammaJuliaLogBalancedEntireDet2_zero_iff⟩

end

end RHTower
