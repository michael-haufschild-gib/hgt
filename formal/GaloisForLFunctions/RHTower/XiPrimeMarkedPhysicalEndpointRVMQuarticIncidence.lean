import GaloisForLFunctions.RHTower.XiPrimeMarkedCofiniteRVMQuarticReserve
import GaloisForLFunctions.RHTower.XiPrimeMarkedCofinalTriangleNuclearCarrier
import GaloisForLFunctions.HTGeometry.QuantumMasterEffectPurity
import GaloisForLFunctions.HTGeometry.QuantumReplicaHausdorff

/-!
# Exact quadratic and quartic Route K source incidence

An explicit strict source-moment cone allows a finite two-level diagonal carrier to absorb the
exact residual quadratic and quartic moments after retaining two cofinite structures: the
reciprocal smooth-RVM diagonal and a positively scaled trace-class cycle carrier.  Orthogonal
prime-index support makes both moment identities exact.  Thus no global rescaling contaminates
the RVM tail, and nonzero cofinal holonomy survives.
-/

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

open ContinuousLinearMap

def routeKQuarticHalfMass : ℝ :=
  routeKSourceZerothMoment / 2

def routeKQuarticHalfEnergy : ℝ :=
  routeKSourceFirstMoment / 2

def routeKQuarticGap : ℝ :=
  routeKQuarticHalfMass ^ (2 : ℕ) - routeKQuarticHalfEnergy

theorem routeKQuarticHalfMass_pos : 0 < routeKQuarticHalfMass := by
  exact div_pos routeKSourceZerothMoment_pos (by norm_num)

theorem routeKQuarticHalfEnergy_pos : 0 < routeKQuarticHalfEnergy := by
  exact div_pos routeKSourceFirstMoment_pos (by norm_num)

theorem routeKQuarticGap_pos : 0 < routeKQuarticGap := by
  rw [routeKQuarticGap, routeKQuarticHalfMass,
    routeKQuarticHalfEnergy]
  have h := routeKSourceFirstMoment_lt_half_sq_zeroth
  nlinarith

def routeKQuarticControlRadius : ℝ :=
  min (routeKQuarticHalfMass / 2)
    (min
      (routeKQuarticGap / (4 * routeKQuarticHalfMass))
      (Real.sqrt (routeKQuarticHalfEnergy / 2) / 2))

theorem routeKQuarticControlRadius_pos :
    0 < routeKQuarticControlRadius := by
  rw [routeKQuarticControlRadius, lt_min_iff, lt_min_iff]
  refine ⟨div_pos routeKQuarticHalfMass_pos (by norm_num),
    div_pos routeKQuarticGap_pos
      (mul_pos (by norm_num) routeKQuarticHalfMass_pos), ?_⟩
  exact div_pos
    (Real.sqrt_pos.2
      (div_pos routeKQuarticHalfEnergy_pos (by norm_num)))
    (by norm_num)

theorem routeKQuarticControlRadius_lt_halfMass :
    routeKQuarticControlRadius < routeKQuarticHalfMass := by
  have hle :
      routeKQuarticControlRadius ≤ routeKQuarticHalfMass / 2 :=
    min_le_left _ _
  nlinarith [routeKQuarticHalfMass_pos]

theorem two_mul_halfMass_mul_routeKQuarticControlRadius_lt_gap :
    2 * routeKQuarticHalfMass * routeKQuarticControlRadius <
      routeKQuarticGap := by
  have hle :
      routeKQuarticControlRadius ≤
        routeKQuarticGap / (4 * routeKQuarticHalfMass) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hA := routeKQuarticHalfMass_pos
  have hgap := routeKQuarticGap_pos
  have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ 2 * routeKQuarticHalfMass by positivity)
  field_simp at hmul
  nlinarith

theorem routeKQuarticControlRadius_sq_lt_halfEnergy_half :
    routeKQuarticControlRadius ^ (2 : ℕ) <
      routeKQuarticHalfEnergy / 2 := by
  have hle :
      routeKQuarticControlRadius ≤
        Real.sqrt (routeKQuarticHalfEnergy / 2) / 2 :=
    min_le_right _ _ |>.trans (min_le_right _ _)
  have hη := routeKQuarticControlRadius_pos
  have hsqrt :
      (Real.sqrt (routeKQuarticHalfEnergy / 2)) ^ (2 : ℕ) =
        routeKQuarticHalfEnergy / 2 :=
    Real.sq_sqrt (div_nonneg routeKQuarticHalfEnergy_pos.le (by norm_num))
  nlinarith [Real.sqrt_nonneg (routeKQuarticHalfEnergy / 2)]

/-- Any Hilbert--Schmidt carrier can be retained with positive scale and arbitrarily small
energy; unlike zero scaling this preserves every nonzero matrix invariant. -/
theorem exists_pos_scale_hsNormSq_smul_lt
    (C : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hC : C.IsHilbertSchmidt) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ hsNormSq ((δ : ℂ) • C) < ε := by
  let c := hsNormSq C
  have hc : 0 ≤ c := hsNormSq_nonneg C
  have hden : 0 < 1 + c := by linarith
  let δ := Real.sqrt (ε / (1 + c))
  have hδ : 0 < δ := by
    exact Real.sqrt_pos.2 (div_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  rw [hsNormSq_smul_eq hC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hδ]
  have hsq : δ ^ (2 : ℕ) = ε / (1 + c) := by
    exact Real.sq_sqrt (div_nonneg hε.le hden.le)
  rw [hsq]
  have hfrac : c / (1 + c) < 1 := by
    rw [div_lt_one hden]
    linarith
  calc
    ε / (1 + c) * hsNormSq C = ε * (c / (1 + c)) := by
      rw [show hsNormSq C = c by rfl]
      field_simp
    _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
    _ = ε := mul_one ε

/-- Parameters retaining both a cofinite exact RVM diagonal and a positive cofinal cycle carrier,
while pushing their total energy below the quartic control radius. -/
structure RouteKQuarticReserveParameters where
  N : ℕ
  hN : 2 ≤ N
  hratio :
    2 * routeKQuarticHalfMass ^ (2 : ℕ) / routeKQuarticHalfEnergy < N
  delta : ℝ
  hdelta : 0 < delta
  htail :
    hsNormSq (routeKRVMTailOperator (routeKInitialPrimeFinset N)) <
      routeKQuarticControlRadius / 4
  hcycle :
    hsNormSq ((delta : ℂ) •
      routeKCofinalTriangleNuclearCarrierFrom N) <
      routeKQuarticControlRadius / 4

theorem exists_routeKQuarticReserveParameters :
    Nonempty RouteKQuarticReserveParameters := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt
      (2 * routeKQuarticHalfMass ^ (2 : ℕ) / routeKQuarticHalfEnergy)
  obtain ⟨N, hNlower, htail⟩ :=
    exists_routeKRVM_initial_tail_energy_lt
      (div_pos routeKQuarticControlRadius_pos
        (by norm_num : (0 : ℝ) < 4))
      (max 2 N₀)
  obtain ⟨δ, hδ, hcycle⟩ :=
    exists_pos_scale_hsNormSq_smul_lt
      (routeKCofinalTriangleNuclearCarrierFrom N)
      (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt N)
      (div_pos routeKQuarticControlRadius_pos
        (by norm_num : (0 : ℝ) < 4))
  refine ⟨{
    N := N
    hN := (le_max_left 2 N₀).trans hNlower
    hratio := ?_
    delta := δ
    hdelta := hδ
    htail := htail
    hcycle := hcycle }⟩
  exact hN₀.trans_le
    (Nat.cast_le.2 (le_max_right 2 N₀ |>.trans hNlower))

def routeKQuarticReserveParameters : RouteKQuarticReserveParameters :=
  Classical.choice exists_routeKQuarticReserveParameters

def routeKQuarticRVMReserve :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  routeKRVMTailOperator
    (routeKInitialPrimeFinset routeKQuarticReserveParameters.N)

def routeKQuarticCycleReserve :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  (routeKQuarticReserveParameters.delta : ℂ) •
    routeKCofinalTriangleNuclearCarrierFrom
      routeKQuarticReserveParameters.N

def routeKQuarticReserve :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  routeKQuarticRVMReserve + routeKQuarticCycleReserve

theorem routeKQuarticRVMReserve_isHilbertSchmidt :
    routeKQuarticRVMReserve.IsHilbertSchmidt :=
  routeKRVMTailOperator_isHilbertSchmidt _

theorem routeKQuarticCycleReserve_isHilbertSchmidt :
    routeKQuarticCycleReserve.IsHilbertSchmidt :=
  (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt _).smul _

theorem routeKQuarticReserve_isHilbertSchmidt :
    routeKQuarticReserve.IsHilbertSchmidt :=
  routeKQuarticRVMReserve_isHilbertSchmidt.add
    routeKQuarticCycleReserve_isHilbertSchmidt

theorem routeKQuarticReserve_isSelfAdjoint :
    IsSelfAdjoint routeKQuarticReserve := by
  apply IsSelfAdjoint.add
  · exact routeKRVMTailOperator_isSelfAdjoint _
  · apply IsSelfAdjoint.smul
    · simp [IsSelfAdjoint]
    · exact routeKCofinalTriangleNuclearCarrierFrom_isSelfAdjoint _

theorem hsNormSq_routeKQuarticReserve_lt_control :
    hsNormSq routeKQuarticReserve < routeKQuarticControlRadius := by
  rw [routeKQuarticReserve]
  have hle :=
    hsNormSq_add_le
      routeKQuarticRVMReserve_isHilbertSchmidt
      routeKQuarticCycleReserve_isHilbertSchmidt
  have htail := routeKQuarticReserveParameters.htail
  have hcycle := routeKQuarticReserveParameters.hcycle
  change hsNormSq routeKQuarticRVMReserve <
    routeKQuarticControlRadius / 4 at htail
  change hsNormSq routeKQuarticCycleReserve <
    routeKQuarticControlRadius / 4 at hcycle
  nlinarith

theorem routeKQuarticReserve_sq_isHilbertSchmidt :
    (routeKQuarticReserve ^ (2 : ℕ)).IsHilbertSchmidt := by
  simpa only [pow_two, ContinuousLinearMap.mul_def] using
    routeKQuarticReserve_isHilbertSchmidt.comp_left routeKQuarticReserve

theorem hsNormSq_routeKQuarticReserve_sq_le :
    hsNormSq (routeKQuarticReserve ^ (2 : ℕ)) ≤
      hsNormSq routeKQuarticReserve ^ (2 : ℕ) := by
  have hpurity :=
    HTGeometry.hsNormSq_adjoint_comp_self_le_sq
      routeKQuarticReserve routeKQuarticReserve_isHilbertSchmidt
  have hself := routeKQuarticReserve_isSelfAdjoint
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hself
  simpa only [hself,
    pow_two, ContinuousLinearMap.mul_def] using hpurity

def routeKQuarticReserveMass : ℝ :=
  hsNormSq routeKQuarticReserve

def routeKQuarticReserveEnergy : ℝ :=
  hsNormSq (routeKQuarticReserve ^ (2 : ℕ))

def routeKQuarticResidualMass : ℝ :=
  routeKQuarticHalfMass - routeKQuarticReserveMass

def routeKQuarticResidualEnergy : ℝ :=
  routeKQuarticHalfEnergy - routeKQuarticReserveEnergy

theorem routeKQuarticReserveMass_nonneg :
    0 ≤ routeKQuarticReserveMass :=
  hsNormSq_nonneg _

theorem routeKQuarticReserveMass_lt_control :
    routeKQuarticReserveMass < routeKQuarticControlRadius :=
  hsNormSq_routeKQuarticReserve_lt_control

theorem routeKQuarticReserveEnergy_nonneg :
    0 ≤ routeKQuarticReserveEnergy :=
  hsNormSq_nonneg _

theorem routeKQuarticReserveEnergy_le_sq_mass :
    routeKQuarticReserveEnergy ≤ routeKQuarticReserveMass ^ (2 : ℕ) :=
  hsNormSq_routeKQuarticReserve_sq_le

theorem routeKQuarticResidualMass_pos :
    0 < routeKQuarticResidualMass := by
  have he := routeKQuarticReserveMass_lt_control
  have hη := routeKQuarticControlRadius_lt_halfMass
  rw [routeKQuarticResidualMass]
  linarith

theorem routeKQuarticReserveEnergy_lt_halfEnergy_half :
    routeKQuarticReserveEnergy < routeKQuarticHalfEnergy / 2 := by
  have hf := routeKQuarticReserveEnergy_le_sq_mass
  have he := routeKQuarticReserveMass_lt_control
  have he0 := routeKQuarticReserveMass_nonneg
  have hη := routeKQuarticControlRadius_pos
  have hsquare :
      routeKQuarticReserveMass ^ (2 : ℕ) <
        routeKQuarticControlRadius ^ (2 : ℕ) := by nlinarith
  exact lt_of_le_of_lt hf
    (hsquare.trans routeKQuarticControlRadius_sq_lt_halfEnergy_half)

theorem routeKQuarticResidualEnergy_pos :
    0 < routeKQuarticResidualEnergy := by
  have hf := routeKQuarticReserveEnergy_lt_halfEnergy_half
  have hB := routeKQuarticHalfEnergy_pos
  rw [routeKQuarticResidualEnergy]
  linarith

theorem routeKQuarticResidualEnergy_lt_residualMass_sq :
    routeKQuarticResidualEnergy < routeKQuarticResidualMass ^ (2 : ℕ) := by
  have he := routeKQuarticReserveMass_lt_control
  have he0 := routeKQuarticReserveMass_nonneg
  have hf0 := routeKQuarticReserveEnergy_nonneg
  have hcontrol :=
    two_mul_halfMass_mul_routeKQuarticControlRadius_lt_gap
  have hmul :
      2 * routeKQuarticHalfMass * routeKQuarticReserveMass <
        2 * routeKQuarticHalfMass * routeKQuarticControlRadius :=
    mul_lt_mul_of_pos_left he
      (mul_pos (by norm_num) routeKQuarticHalfMass_pos)
  rw [routeKQuarticResidualEnergy, routeKQuarticResidualMass,
    routeKQuarticGap] at *
  nlinarith

theorem routeKQuarticResidualMass_sq_div_N_lt_residualEnergy :
    routeKQuarticResidualMass ^ (2 : ℕ) /
        routeKQuarticReserveParameters.N <
      routeKQuarticResidualEnergy := by
  let N := routeKQuarticReserveParameters.N
  have hNnat : 2 ≤ N := routeKQuarticReserveParameters.hN
  have hN : (0 : ℝ) < N := by positivity
  have hratio := routeKQuarticReserveParameters.hratio
  change
    2 * routeKQuarticHalfMass ^ (2 : ℕ) /
        routeKQuarticHalfEnergy < (N : ℝ) at hratio
  have hB := routeKQuarticHalfEnergy_pos
  have hAN :
      routeKQuarticHalfMass ^ (2 : ℕ) / (N : ℝ) <
        routeKQuarticHalfEnergy / 2 := by
    rw [div_lt_iff₀ hN]
    rw [div_lt_iff₀ hB] at hratio
    nlinarith
  have hE_le :
      routeKQuarticResidualMass ^ (2 : ℕ) ≤
        routeKQuarticHalfMass ^ (2 : ℕ) := by
    have he0 := routeKQuarticReserveMass_nonneg
    have hres := routeKQuarticResidualMass_pos
    rw [routeKQuarticResidualMass] at hres ⊢
    nlinarith
  have hdiv_le :
      routeKQuarticResidualMass ^ (2 : ℕ) / (N : ℝ) ≤
        routeKQuarticHalfMass ^ (2 : ℕ) / (N : ℝ) :=
    div_le_div_of_nonneg_right hE_le hN.le
  have hF :
      routeKQuarticHalfEnergy / 2 <
        routeKQuarticResidualEnergy := by
    have hf := routeKQuarticReserveEnergy_lt_halfEnergy_half
    rw [routeKQuarticResidualEnergy]
    linarith
  exact hdiv_le.trans_lt (hAN.trans hF)

def routeKQuarticHead :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  twoLevelPrimeDiagonalOperator
    routeKQuarticResidualMass routeKQuarticResidualEnergy
    routeKQuarticReserveParameters.N
    routeKQuarticResidualMass_pos
    routeKQuarticReserveParameters.hN
    routeKQuarticResidualMass_sq_div_N_lt_residualEnergy
    routeKQuarticResidualEnergy_lt_residualMass_sq.le

theorem routeKQuarticHead_isHilbertSchmidt :
    routeKQuarticHead.IsHilbertSchmidt :=
  twoLevelPrimeDiagonalOperator_isHilbertSchmidt
    routeKQuarticResidualMass_pos
    routeKQuarticReserveParameters.hN
    routeKQuarticResidualMass_sq_div_N_lt_residualEnergy
    routeKQuarticResidualEnergy_lt_residualMass_sq.le

theorem routeKQuarticHead_isSelfAdjoint :
    IsSelfAdjoint routeKQuarticHead :=
  twoLevelPrimeDiagonalOperator_isSelfAdjoint
    routeKQuarticResidualMass_pos
    routeKQuarticReserveParameters.hN
    routeKQuarticResidualMass_sq_div_N_lt_residualEnergy
    routeKQuarticResidualEnergy_lt_residualMass_sq.le

theorem hsNormSq_routeKQuarticHead :
    hsNormSq routeKQuarticHead = routeKQuarticResidualMass :=
  hsNormSq_twoLevelPrimeDiagonalOperator
    routeKQuarticResidualMass_pos
    routeKQuarticReserveParameters.hN
    routeKQuarticResidualMass_sq_div_N_lt_residualEnergy
    routeKQuarticResidualEnergy_lt_residualMass_sq.le

theorem routeKQuarticHead_sq_isHilbertSchmidt :
    (routeKQuarticHead ^ (2 : ℕ)).IsHilbertSchmidt :=
  twoLevelPrimeDiagonalOperator_sq_isHilbertSchmidt
    routeKQuarticResidualMass_pos
    routeKQuarticReserveParameters.hN
    routeKQuarticResidualMass_sq_div_N_lt_residualEnergy
    routeKQuarticResidualEnergy_lt_residualMass_sq.le

theorem hsNormSq_routeKQuarticHead_sq :
    hsNormSq (routeKQuarticHead ^ (2 : ℕ)) =
      routeKQuarticResidualEnergy :=
  hsNormSq_sq_twoLevelPrimeDiagonalOperator
    routeKQuarticResidualMass_pos
    routeKQuarticReserveParameters.hN
    routeKQuarticResidualMass_sq_div_N_lt_residualEnergy
    routeKQuarticResidualEnergy_lt_residualMass_sq.le

theorem routeKQuarticHead_basis
    (p : Nat.Primes) :
    routeKQuarticHead (routeKPrimeBasis p) =
      (twoLevelPrimeWeight
        routeKQuarticResidualMass routeKQuarticResidualEnergy
        routeKQuarticReserveParameters.N p : ℂ) •
          routeKPrimeBasis p :=
  twoLevelPrimeDiagonalOperator_basis
    routeKQuarticResidualMass_pos
    routeKQuarticReserveParameters.hN
    routeKQuarticResidualMass_sq_div_N_lt_residualEnergy
    routeKQuarticResidualEnergy_lt_residualMass_sq.le p

theorem routeKQuarticHead_basis_eq_zero_of_index_ge
    {p : Nat.Primes}
    (hp : routeKQuarticReserveParameters.N ≤ nthPrimeEquiv.symm p) :
    routeKQuarticHead (routeKPrimeBasis p) = 0 :=
  twoLevelPrimeDiagonalOperator_basis_eq_zero_of_le_index
    routeKQuarticResidualMass_pos
    routeKQuarticReserveParameters.hN
    routeKQuarticResidualMass_sq_div_N_lt_residualEnergy
    routeKQuarticResidualEnergy_lt_residualMass_sq.le hp

theorem routeKQuarticReserve_basis_eq_zero_of_index_lt
    {p : Nat.Primes}
    (hp : nthPrimeEquiv.symm p < routeKQuarticReserveParameters.N) :
    routeKQuarticReserve (routeKPrimeBasis p) = 0 := by
  rw [routeKQuarticReserve, add_apply]
  have htail :
      routeKQuarticRVMReserve (routeKPrimeBasis p) = 0 := by
    rw [routeKQuarticRVMReserve, routeKRVMTailOperator_basis,
      routeKRVMTailWeight_initial, if_pos hp]
    simp
  have hcycle :
      routeKQuarticCycleReserve (routeKPrimeBasis p) = 0 := by
    rw [routeKQuarticCycleReserve, smul_apply,
      routeKCofinalTriangleNuclearCarrierFrom_basis_eq_zero_of_index_lt hp]
    simp
  rw [htail, hcycle, add_zero]

theorem routeKQuarticReserve_mul_head_eq_zero :
    routeKQuarticReserve * routeKQuarticHead = 0 := by
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis Nat.Primes).dense_span) ?_
  rintro x ⟨p, rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  change (routeKQuarticReserve * routeKQuarticHead)
      (routeKPrimeBasis p) = 0
  rw [mul_apply_eq_comp]
  by_cases hp :
      nthPrimeEquiv.symm p < routeKQuarticReserveParameters.N
  · rw [routeKQuarticHead_basis, map_smul,
      routeKQuarticReserve_basis_eq_zero_of_index_lt hp, smul_zero]
  · have hpge :
        routeKQuarticReserveParameters.N ≤ nthPrimeEquiv.symm p := by
      omega
    rw [routeKQuarticHead_basis_eq_zero_of_index_ge hpge, map_zero]

theorem routeKQuarticHead_mul_reserve_eq_zero :
    routeKQuarticHead * routeKQuarticReserve = 0 := by
  have hstar := congrArg star routeKQuarticReserve_mul_head_eq_zero
  have hH := routeKQuarticHead_isSelfAdjoint
  have hR := routeKQuarticReserve_isSelfAdjoint
  change star routeKQuarticHead = routeKQuarticHead at hH
  change star routeKQuarticReserve = routeKQuarticReserve at hR
  simpa [star_mul, hH, hR] using hstar

theorem hsInner_routeKQuarticHead_reserve_eq_zero :
    hsInner routeKQuarticHead routeKQuarticReserve = 0 := by
  rw [hsInner_eq_tsum_basis
    routeKQuarticHead_isHilbertSchmidt
    routeKQuarticReserve_isHilbertSchmidt
    (HilbertSchmidt.lpBasis Nat.Primes)]
  have hterm :
      (fun p : Nat.Primes =>
        inner ℂ
          (routeKQuarticHead
            (HilbertSchmidt.lpBasis Nat.Primes p))
          (routeKQuarticReserve
            (HilbertSchmidt.lpBasis Nat.Primes p))) = 0 := by
    funext p
    rw [HilbertSchmidt.lpBasis_apply]
    change inner ℂ
      (routeKQuarticHead (routeKPrimeBasis p))
      (routeKQuarticReserve (routeKPrimeBasis p)) = 0
    by_cases hp :
        nthPrimeEquiv.symm p < routeKQuarticReserveParameters.N
    · rw [routeKQuarticReserve_basis_eq_zero_of_index_lt hp]
      simp
    · have hpge :
          routeKQuarticReserveParameters.N ≤ nthPrimeEquiv.symm p := by
        omega
      rw [routeKQuarticHead_basis_eq_zero_of_index_ge hpge]
      simp
  rw [hterm]
  exact tsum_zero

theorem routeKQuarticHead_sq_basis_eq_zero_of_index_ge
    {p : Nat.Primes}
    (hp : routeKQuarticReserveParameters.N ≤ nthPrimeEquiv.symm p) :
    (routeKQuarticHead ^ (2 : ℕ)) (routeKPrimeBasis p) = 0 := by
  rw [pow_two, mul_apply_eq_comp,
    routeKQuarticHead_basis_eq_zero_of_index_ge hp, map_zero]

theorem routeKQuarticReserve_sq_basis_eq_zero_of_index_lt
    {p : Nat.Primes}
    (hp : nthPrimeEquiv.symm p < routeKQuarticReserveParameters.N) :
    (routeKQuarticReserve ^ (2 : ℕ)) (routeKPrimeBasis p) = 0 := by
  rw [pow_two, mul_apply_eq_comp,
    routeKQuarticReserve_basis_eq_zero_of_index_lt hp, map_zero]

theorem hsInner_routeKQuarticHead_sq_reserve_sq_eq_zero :
    hsInner (routeKQuarticHead ^ (2 : ℕ)) (routeKQuarticReserve ^ (2 : ℕ)) = 0 := by
  rw [hsInner_eq_tsum_basis
    routeKQuarticHead_sq_isHilbertSchmidt
    routeKQuarticReserve_sq_isHilbertSchmidt
    (HilbertSchmidt.lpBasis Nat.Primes)]
  have hterm :
      (fun p : Nat.Primes =>
        inner ℂ
          ((routeKQuarticHead ^ (2 : ℕ))
            (HilbertSchmidt.lpBasis Nat.Primes p))
          ((routeKQuarticReserve ^ (2 : ℕ))
            (HilbertSchmidt.lpBasis Nat.Primes p))) = 0 := by
    funext p
    rw [HilbertSchmidt.lpBasis_apply]
    change inner ℂ
      ((routeKQuarticHead ^ (2 : ℕ)) (routeKPrimeBasis p))
      ((routeKQuarticReserve ^ (2 : ℕ)) (routeKPrimeBasis p)) = 0
    by_cases hp :
        nthPrimeEquiv.symm p < routeKQuarticReserveParameters.N
    · rw [routeKQuarticReserve_sq_basis_eq_zero_of_index_lt hp]
      simp
    · have hpge :
          routeKQuarticReserveParameters.N ≤ nthPrimeEquiv.symm p := by
        omega
      rw [routeKQuarticHead_sq_basis_eq_zero_of_index_ge hpge]
      simp
  rw [hterm]
  exact tsum_zero

/-- Quartically admitted Route K operator: exact finite moment head plus cofinite RVM/cycle
reserve. -/
def routeKQuarticallyAdmittedOperator :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  routeKQuarticHead + routeKQuarticReserve

theorem routeKQuarticallyAdmittedOperator_isHilbertSchmidt :
    routeKQuarticallyAdmittedOperator.IsHilbertSchmidt :=
  routeKQuarticHead_isHilbertSchmidt.add
    routeKQuarticReserve_isHilbertSchmidt

theorem routeKQuarticallyAdmittedOperator_isSelfAdjoint :
    IsSelfAdjoint routeKQuarticallyAdmittedOperator :=
  routeKQuarticHead_isSelfAdjoint.add
    routeKQuarticReserve_isSelfAdjoint

theorem hsNormSq_routeKQuarticallyAdmittedOperator :
    hsNormSq routeKQuarticallyAdmittedOperator =
      routeKQuarticHalfMass := by
  rw [routeKQuarticallyAdmittedOperator,
    hsNormSq_add_eq_of_hsInner_eq_zero
      routeKQuarticHead_isHilbertSchmidt
      routeKQuarticReserve_isHilbertSchmidt
      hsInner_routeKQuarticHead_reserve_eq_zero,
    hsNormSq_routeKQuarticHead,
    show hsNormSq routeKQuarticReserve =
      routeKQuarticReserveMass by rfl,
    routeKQuarticResidualMass]
  ring

theorem routeKQuarticallyAdmittedOperator_sq :
    routeKQuarticallyAdmittedOperator ^ (2 : ℕ) =
      routeKQuarticHead ^ (2 : ℕ) + routeKQuarticReserve ^ (2 : ℕ) := by
  rw [routeKQuarticallyAdmittedOperator, pow_two, add_mul,
    mul_add, mul_add, routeKQuarticHead_mul_reserve_eq_zero,
    routeKQuarticReserve_mul_head_eq_zero]
  simp [pow_two]

/-- The finite moment head and cofinite reserve are reducing summands, hence their cubic
traces cannot generate mixed terms. -/
theorem routeKQuarticallyAdmittedOperator_cube :
    routeKQuarticallyAdmittedOperator ^ (3 : ℕ) =
      routeKQuarticHead ^ (3 : ℕ) + routeKQuarticReserve ^ (3 : ℕ) := by
  rw [show 3 = 2 + 1 by norm_num, pow_add,
    routeKQuarticallyAdmittedOperator_sq, routeKQuarticallyAdmittedOperator]
  noncomm_ring [routeKQuarticHead_mul_reserve_eq_zero,
    routeKQuarticReserve_mul_head_eq_zero]

theorem routeKQuarticHead_cube_isHilbertSchmidt :
    (routeKQuarticHead ^ (3 : ℕ)).IsHilbertSchmidt := by
  rw [show 3 = 2 + 1 by norm_num, pow_succ, ContinuousLinearMap.mul_def]
  exact routeKQuarticHead_isHilbertSchmidt.comp_left (routeKQuarticHead ^ (2 : ℕ))

/-- The old quartic head has an exact sixth energy: it is the lower endpoint of the
three-level cubic-moment interval. -/
theorem hsNormSq_routeKQuarticHead_cube :
    hsNormSq (routeKQuarticHead ^ (3 : ℕ)) =
      twoLevelLarge routeKQuarticResidualMass routeKQuarticResidualEnergy
        routeKQuarticReserveParameters.N ^ (3 : ℕ) +
      ((routeKQuarticReserveParameters.N : ℝ) - 1) *
        twoLevelSmall routeKQuarticResidualMass routeKQuarticResidualEnergy
          routeKQuarticReserveParameters.N ^ (3 : ℕ) := by
  exact hsNormSq_cube_twoLevelPrimeDiagonalOperator
    routeKQuarticResidualMass_pos
    routeKQuarticReserveParameters.hN
    routeKQuarticResidualMass_sq_div_N_lt_residualEnergy
    routeKQuarticResidualEnergy_lt_residualMass_sq.le

theorem routeKQuarticReserve_cube_isHilbertSchmidt :
    (routeKQuarticReserve ^ (3 : ℕ)).IsHilbertSchmidt := by
  rw [show 3 = 2 + 1 by norm_num, pow_succ, ContinuousLinearMap.mul_def]
  exact routeKQuarticReserve_isHilbertSchmidt.comp_left (routeKQuarticReserve ^ (2 : ℕ))

/-- The cofinal RVM/cycle reserve loses at least two powers of its retained
Hilbert--Schmidt mass at sixth energy.  Thus making the reserve small at quadratic order makes
its cubic power-energy small cubically as well. -/
theorem hsNormSq_routeKQuarticReserve_cube_le_mass_cubed :
    hsNormSq (routeKQuarticReserve ^ (3 : ℕ)) ≤ routeKQuarticReserveMass ^ (3 : ℕ) := by
  have hcomp := HTGeometry.hsNormSq_comp_left_le_opNorm
    routeKQuarticReserve_sq_isHilbertSchmidt routeKQuarticReserve
  have hcomp' : hsNormSq (routeKQuarticReserve ^ (3 : ℕ)) ≤
      ‖routeKQuarticReserve‖ ^ (2 : ℕ) * routeKQuarticReserveEnergy := by
    rw [show routeKQuarticReserve ^ (3 : ℕ) =
      routeKQuarticReserve ∘L routeKQuarticReserve ^ (2 : ℕ) by
        change routeKQuarticReserve ^ (3 : ℕ) =
          routeKQuarticReserve * routeKQuarticReserve ^ (2 : ℕ)
        rw [← pow_succ']]
    exact hcomp
  have hop := ContinuousLinearMap.opNorm_le_hsNorm routeKQuarticReserve_isHilbertSchmidt
  have hhs : hsNorm routeKQuarticReserve ^ (2 : ℕ) = routeKQuarticReserveMass := by
    change hsNorm routeKQuarticReserve ^ (2 : ℕ) = hsNormSq routeKQuarticReserve
    rw [ContinuousLinearMap.hsNorm,
      Real.sq_sqrt (hsNormSq_nonneg routeKQuarticReserve)]
  have hopSq : ‖routeKQuarticReserve‖ ^ (2 : ℕ) ≤ routeKQuarticReserveMass := by
    calc
      ‖routeKQuarticReserve‖ ^ (2 : ℕ) ≤ hsNorm routeKQuarticReserve ^ (2 : ℕ) :=
        (sq_le_sq₀ (norm_nonneg _) (ContinuousLinearMap.hsNorm_nonneg _)).mpr hop
      _ = routeKQuarticReserveMass := hhs
  calc
    hsNormSq (routeKQuarticReserve ^ (3 : ℕ)) ≤
        ‖routeKQuarticReserve‖ ^ (2 : ℕ) * routeKQuarticReserveEnergy := hcomp'
    _ ≤ routeKQuarticReserveMass * routeKQuarticReserveEnergy := by
      exact mul_le_mul_of_nonneg_right hopSq routeKQuarticReserveEnergy_nonneg
    _ ≤ routeKQuarticReserveMass * routeKQuarticReserveMass ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left routeKQuarticReserveEnergy_le_sq_mass
        routeKQuarticReserveMass_nonneg
    _ = routeKQuarticReserveMass ^ (3 : ℕ) := by ring

/-- The sixth energy of the retained RVM/cycle reserve lies strictly below the cubic control
budget.  A three-level head can therefore be designed against a genuine open sixth-energy margin. -/
theorem hsNormSq_routeKQuarticReserve_cube_lt_control_cubed :
    hsNormSq (routeKQuarticReserve ^ (3 : ℕ)) < routeKQuarticControlRadius ^ (3 : ℕ) := by
  refine (hsNormSq_routeKQuarticReserve_cube_le_mass_cubed).trans_lt ?_
  exact pow_lt_pow_left₀ routeKQuarticReserveMass_lt_control
    routeKQuarticReserveMass_nonneg (by norm_num)

theorem routeKQuarticHead_cube_mul_reserve_cube_eq_zero :
    routeKQuarticHead ^ (3 : ℕ) * routeKQuarticReserve ^ (3 : ℕ) = 0 := by
  calc
    routeKQuarticHead ^ (3 : ℕ) * routeKQuarticReserve ^ (3 : ℕ) =
        routeKQuarticHead ^ (2 : ℕ) *
          (routeKQuarticHead * routeKQuarticReserve) *
            routeKQuarticReserve ^ (2 : ℕ) := by
      rw [show routeKQuarticHead ^ (3 : ℕ) = routeKQuarticHead ^ (2 : ℕ) * routeKQuarticHead by
        rw [pow_succ]]
      rw [show routeKQuarticReserve ^ (3 : ℕ) =
          routeKQuarticReserve * routeKQuarticReserve ^ (2 : ℕ) by
        rw [← pow_succ']]
      noncomm_ring
    _ = 0 := by rw [routeKQuarticHead_mul_reserve_eq_zero]; simp

theorem hsInner_routeKQuarticHead_cube_reserve_cube_eq_zero :
    hsInner (routeKQuarticHead ^ (3 : ℕ)) (routeKQuarticReserve ^ (3 : ℕ)) = 0 := by
  have hself : IsSelfAdjoint (routeKQuarticHead ^ (3 : ℕ)) := by
    have hhead := routeKQuarticHead_isSelfAdjoint
    change star routeKQuarticHead = routeKQuarticHead at hhead
    change star (routeKQuarticHead ^ (3 : ℕ)) = routeKQuarticHead ^ (3 : ℕ)
    rw [star_pow, hhead]
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hself
  calc
    hsInner (routeKQuarticHead ^ (3 : ℕ)) (routeKQuarticReserve ^ (3 : ℕ)) =
        opTrace (ContinuousLinearMap.adjoint (routeKQuarticHead ^ (3 : ℕ)) ∘L
          routeKQuarticReserve ^ (3 : ℕ)) := by
      symm
      calc
        opTrace (ContinuousLinearMap.adjoint (routeKQuarticHead ^ (3 : ℕ)) ∘L
            routeKQuarticReserve ^ (3 : ℕ)) =
            hsInner (ContinuousLinearMap.adjoint
              (ContinuousLinearMap.adjoint (routeKQuarticHead ^ (3 : ℕ))))
              (routeKQuarticReserve ^ (3 : ℕ)) :=
          opTrace_comp_eq_hsInner
            (ContinuousLinearMap.adjoint (routeKQuarticHead ^ (3 : ℕ)))
            (routeKQuarticReserve ^ (3 : ℕ))
        _ = hsInner (routeKQuarticHead ^ (3 : ℕ)) (routeKQuarticReserve ^ (3 : ℕ)) := by
          rw [ContinuousLinearMap.adjoint_adjoint]
    _ = opTrace (routeKQuarticHead ^ (3 : ℕ) * routeKQuarticReserve ^ (3 : ℕ)) := by
      rw [hself]
      rfl
    _ = 0 := by
      rw [routeKQuarticHead_cube_mul_reserve_cube_eq_zero]
      simp

/-- The sixth energy has no mixed head--reserve contribution. -/
theorem hsNormSq_routeKQuarticallyAdmittedOperator_cube :
    hsNormSq (routeKQuarticallyAdmittedOperator ^ (3 : ℕ)) =
      hsNormSq (routeKQuarticHead ^ (3 : ℕ)) +
        hsNormSq (routeKQuarticReserve ^ (3 : ℕ)) := by
  rw [routeKQuarticallyAdmittedOperator_cube,
    hsNormSq_add_eq_of_hsInner_eq_zero
      routeKQuarticHead_cube_isHilbertSchmidt
      routeKQuarticReserve_cube_isHilbertSchmidt
      hsInner_routeKQuarticHead_cube_reserve_cube_eq_zero]

theorem routeKQuarticallyAdmittedOperator_sq_isHilbertSchmidt :
    (routeKQuarticallyAdmittedOperator ^ (2 : ℕ)).IsHilbertSchmidt := by
  rw [routeKQuarticallyAdmittedOperator_sq]
  exact routeKQuarticHead_sq_isHilbertSchmidt.add
    routeKQuarticReserve_sq_isHilbertSchmidt

theorem hsNormSq_routeKQuarticallyAdmittedOperator_sq :
    hsNormSq (routeKQuarticallyAdmittedOperator ^ (2 : ℕ)) =
      routeKQuarticHalfEnergy := by
  rw [routeKQuarticallyAdmittedOperator_sq,
    hsNormSq_add_eq_of_hsInner_eq_zero
      routeKQuarticHead_sq_isHilbertSchmidt
      routeKQuarticReserve_sq_isHilbertSchmidt
      hsInner_routeKQuarticHead_sq_reserve_sq_eq_zero,
    hsNormSq_routeKQuarticHead_sq,
    show hsNormSq (routeKQuarticReserve ^ (2 : ℕ)) =
      routeKQuarticReserveEnergy by rfl,
    routeKQuarticResidualEnergy]
  ring

/-- Exact reflected degree-two source moment. -/
theorem two_mul_hsNormSq_routeKQuarticallyAdmittedOperator :
    2 * hsNormSq routeKQuarticallyAdmittedOperator =
      routeKSourceZerothMoment := by
  rw [hsNormSq_routeKQuarticallyAdmittedOperator,
    routeKQuarticHalfMass]
  ring

/-- Exact reflected quartic source moment. -/
theorem two_mul_hsNormSq_sq_routeKQuarticallyAdmittedOperator :
    2 * hsNormSq (routeKQuarticallyAdmittedOperator ^ (2 : ℕ)) =
      routeKSourceFirstMoment := by
  rw [hsNormSq_routeKQuarticallyAdmittedOperator_sq,
    routeKQuarticHalfEnergy]
  ring

theorem routeKQuarticallyAdmittedOperator_sq_isSelfAdjoint :
    IsSelfAdjoint (routeKQuarticallyAdmittedOperator ^ (2 : ℕ)) := by
  have hT := routeKQuarticallyAdmittedOperator_isSelfAdjoint
  change star routeKQuarticallyAdmittedOperator =
    routeKQuarticallyAdmittedOperator at hT
  change star (routeKQuarticallyAdmittedOperator ^ (2 : ℕ)) =
    routeKQuarticallyAdmittedOperator ^ (2 : ℕ)
  rw [star_pow, hT]

theorem two_mul_opTrace_sq_routeKQuarticallyAdmittedOperator :
    2 * opTrace (routeKQuarticallyAdmittedOperator ^ (2 : ℕ)) =
      (routeKSourceZerothMoment : ℂ) := by
  have hT := routeKQuarticallyAdmittedOperator_isSelfAdjoint
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hT
  rw [HTGeometry.opTrace_sq_eq_ofReal_hsNormSq
    routeKQuarticallyAdmittedOperator_isHilbertSchmidt hT]
  have h :=
    congrArg (fun x : ℝ => (x : ℂ))
      two_mul_hsNormSq_routeKQuarticallyAdmittedOperator
  simpa using h

theorem two_mul_opTrace_four_routeKQuarticallyAdmittedOperator :
    2 * opTrace (routeKQuarticallyAdmittedOperator ^ (4 : ℕ)) =
      (routeKSourceFirstMoment : ℂ) := by
  have hT2 := routeKQuarticallyAdmittedOperator_sq_isSelfAdjoint
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hT2
  have hpow :
      routeKQuarticallyAdmittedOperator ^ (4 : ℕ) =
        (routeKQuarticallyAdmittedOperator ^ (2 : ℕ)) ^ (2 : ℕ) := by
    noncomm_ring
  rw [hpow, HTGeometry.opTrace_sq_eq_ofReal_hsNormSq
    routeKQuarticallyAdmittedOperator_sq_isHilbertSchmidt hT2]
  have h :=
    congrArg (fun x : ℝ => (x : ℂ))
      two_mul_hsNormSq_sq_routeKQuarticallyAdmittedOperator
  simpa using h

/-- Outside the finite moment head, the admitted diagonal is exactly the reciprocal smooth-RVM
skeleton.  The retained cycle carrier contributes no diagonal term. -/
theorem routeKQuarticallyAdmittedOperator_diagonal_of_index_ge
    {p : Nat.Primes}
    (hp : routeKQuarticReserveParameters.N ≤ nthPrimeEquiv.symm p) :
    inner ℂ (routeKPrimeBasis p)
        (routeKQuarticallyAdmittedOperator (routeKPrimeBasis p)) =
      (routeKPrimeRVMReciprocal p : ℂ) := by
  rw [routeKQuarticallyAdmittedOperator, add_apply, inner_add_right,
    routeKQuarticHead_basis_eq_zero_of_index_ge hp, inner_zero_right,
    zero_add, routeKQuarticReserve, add_apply, inner_add_right,
    routeKQuarticRVMReserve, routeKRVMTailOperator_basis,
    routeKRVMTailWeight_initial, if_neg (not_lt_of_ge hp),
    inner_smul_right, inner_routeKPrimeBasis_routeKPrimeBasis,
    if_pos rfl, mul_one, routeKQuarticCycleReserve, smul_apply,
    inner_smul_right,
    routeKCofinalTriangleNuclearCarrierFrom_diagonal_zero,
    mul_zero, add_zero]

/-- Every retained triangle edge survives with one common positive scale. -/
theorem routeKQuarticallyAdmittedOperator_selectedEdge
    (n : ℕ) (i : Fin 3) :
    inner ℂ
        (routeKPrimeBasis
          (routeKCofinalTrianglePrime
            (n + routeKQuarticReserveParameters.N) i))
        (routeKQuarticallyAdmittedOperator
          (routeKPrimeBasis
            (routeKCofinalTrianglePrimeNext
              (n + routeKQuarticReserveParameters.N) i))) =
      (routeKQuarticReserveParameters.delta : ℂ) *
        (routeKCofinalTriangleAmplitude
          (n + routeKQuarticReserveParameters.N) i : ℂ) := by
  let K := routeKQuarticReserveParameters.N
  let p := routeKCofinalTrianglePrime (n + K) i
  let q := routeKCofinalTrianglePrimeNext (n + K) i
  have hqIndex : K ≤ nthPrimeEquiv.symm q := by
    have hstart : n + K ≤ routeKCofinalTriangleStart (n + K) :=
      routeKCofinalTriangleStart_self_le (n + K)
    have hnext :
        routeKCofinalTriangleStart (n + K) ≤ nthPrimeEquiv.symm q :=
      nthPrimeEquiv_symm_routeKCofinalTrianglePrimeNext_ge (n + K) i
    omega
  have hpq : p ≠ q :=
    routeKCofinalTrianglePrime_ne_next (n + K) i
  change inner ℂ (routeKPrimeBasis p)
      (routeKQuarticallyAdmittedOperator (routeKPrimeBasis q)) = _
  rw [routeKQuarticallyAdmittedOperator, add_apply, inner_add_right,
    routeKQuarticHead_basis_eq_zero_of_index_ge hqIndex,
    inner_zero_right, zero_add, routeKQuarticReserve, add_apply,
    inner_add_right, routeKQuarticRVMReserve,
    routeKRVMTailOperator_basis, inner_smul_right,
    inner_routeKPrimeBasis_routeKPrimeBasis, if_neg hpq, mul_zero,
    zero_add, routeKQuarticCycleReserve, smul_apply, inner_smul_right]
  change
    (routeKQuarticReserveParameters.delta : ℂ) *
      inner ℂ (routeKPrimeBasis
        (routeKCofinalTrianglePrime (n + K) i))
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKPrimeBasis
            (routeKCofinalTrianglePrimeNext (n + K) i))) = _
  rw [routeKCofinalTriangleNuclearCarrierFrom_selectedEdge]

/-- Cofinal cycle holonomy remains nonzero after exact simultaneous quadratic/quartic admission. -/
theorem routeKQuarticallyAdmittedOperator_selectedHolonomy_ne_zero
    (n : ℕ) :
    inner ℂ
        (routeKPrimeBasis
          (routeKCofinalTrianglePrime
            (n + routeKQuarticReserveParameters.N) 0))
        (routeKQuarticallyAdmittedOperator
          (routeKPrimeBasis
            (routeKCofinalTrianglePrime
              (n + routeKQuarticReserveParameters.N) 1))) *
      inner ℂ
        (routeKPrimeBasis
          (routeKCofinalTrianglePrime
            (n + routeKQuarticReserveParameters.N) 1))
        (routeKQuarticallyAdmittedOperator
          (routeKPrimeBasis
            (routeKCofinalTrianglePrime
              (n + routeKQuarticReserveParameters.N) 2))) *
      inner ℂ
        (routeKPrimeBasis
          (routeKCofinalTrianglePrime
            (n + routeKQuarticReserveParameters.N) 2))
        (routeKQuarticallyAdmittedOperator
          (routeKPrimeBasis
            (routeKCofinalTrianglePrime
              (n + routeKQuarticReserveParameters.N) 0))) ≠ 0 := by
  have hdelta :
      (routeKQuarticReserveParameters.delta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr routeKQuarticReserveParameters.hdelta.ne'
  have h0 :=
    routeKQuarticallyAdmittedOperator_selectedEdge n (0 : Fin 3)
  have h1 :=
    routeKQuarticallyAdmittedOperator_selectedEdge n (1 : Fin 3)
  have h2 :=
    routeKQuarticallyAdmittedOperator_selectedEdge n (2 : Fin 3)
  simp only [routeKCofinalTrianglePrimeNext_zero] at h0
  simp only [routeKCofinalTrianglePrimeNext_one] at h1
  simp only [routeKCofinalTrianglePrimeNext_two] at h2
  rw [h0, h1, h2]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero hdelta
        (Complex.ofReal_ne_zero.mpr
          (routeKCofinalTriangleAmplitude_pos
            (n + routeKQuarticReserveParameters.N) 0).ne'))
      (mul_ne_zero hdelta
        (Complex.ofReal_ne_zero.mpr
          (routeKCofinalTriangleAmplitude_pos
            (n + routeKQuarticReserveParameters.N) 1).ne')))
    (mul_ne_zero hdelta
      (Complex.ofReal_ne_zero.mpr
        (routeKCofinalTriangleAmplitude_pos
          (n + routeKQuarticReserveParameters.N) 2).ne'))

end

end RHTower
