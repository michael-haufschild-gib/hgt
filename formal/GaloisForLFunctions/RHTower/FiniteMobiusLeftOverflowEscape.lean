import GaloisForLFunctions.RHTower.FiniteCutoffCompensatingInfinityNoGo

/-!
# Strict-left zeros force two finite-source processes to escape

Let `H_N` be the constant-coefficient Dirichlet head, `B_N` the Möbius head, `O_N` their
rectangle overflow, and `C_N` the finite continuation correction.  At a nontrivial zeta zero
strictly left of the critical line, neither `O_N` nor `C_N B_N` is bounded on a cutoff tail,
although their sum converges to `-1`.

The source of escape is the consecutive-cutoff law for `B_N`.  If `H_N B_N` were tail bounded,
the normalized head asymptotic would force `N^s B_N` and `(N+1)^s B_N` to vanish.  Their difference
recovers the Möbius value at `N+1`, contradicting its value `-1` at arbitrarily large primes.

This gives a zero-specific two-process infinity before any information-geometric completion is
introduced.  It uses only finite coefficient identities, the already proved head asymptotic, and
infinitude of primes.
-/

noncomputable section

open Complex Filter Set
open scoped Topology BigOperators

namespace RHTower.DeletionMixedRefinement

/-- A nontrivial zero strictly left of the critical line. -/
abbrev StrictLeftNontrivialZetaZero :=
  {rho : RiemannGaussian.NontrivialZetaZero // rho.1.re < (1 : ℝ) / 2}

/-- A nontrivial zero away from the critical line. -/
abbrev OffCriticalNontrivialZetaZero :=
  {rho : RiemannGaussian.NontrivialZetaZero // rho.1.re ≠ (1 : ℝ) / 2}

/-- Every off-critical functional-equation orbit has a strict-left member. -/
def offCriticalZero_strictLeftMember
    (rho : OffCriticalNontrivialZetaZero) : StrictLeftNontrivialZetaZero := by
  by_cases hleft : rho.1.1.re < (1 : ℝ) / 2
  · exact ⟨rho.1, hleft⟩
  · refine ⟨RiemannGaussian.NontrivialZetaZero.functionalPartner rho.1, ?_⟩
    change (1 - rho.1.1).re < (1 : ℝ) / 2
    simp only [Complex.sub_re, Complex.one_re]
    have hright : (1 : ℝ) / 2 < rho.1.1.re :=
      lt_of_le_of_ne (le_of_not_gt hleft) rho.2.symm
    linarith

/-- Adding one cutoff exposes exactly one Möbius-weighted Dirichlet term. -/
theorem finiteMobiusRecoveryHead_succ (N : ℕ) (s : ℂ) :
    finiteMobiusRecoveryHead (N + 1) s =
      finiteMobiusRecoveryHead N s +
        (ArithmeticFunction.moebius (N + 1) : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
  rw [finiteMobiusRecoveryHead, finiteMobiusRecoveryHead,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- Rescaling the consecutive-cutoff difference recovers the Möbius coefficient exactly. -/
theorem natSucc_cpow_mul_finiteMobiusRecoveryHead_sub (N : ℕ) (s : ℂ) :
    ((N + 1 : ℕ) : ℂ) ^ s * finiteMobiusRecoveryHead (N + 1) s -
        ((N + 1 : ℕ) : ℂ) ^ s * finiteMobiusRecoveryHead N s =
      (ArithmeticFunction.moebius (N + 1) : ℂ) := by
  rw [finiteMobiusRecoveryHead_succ]
  have hN : ((N + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : N + 1 ≠ 0)
  have hcancel :
      ((N + 1 : ℕ) : ℂ) ^ s * ((N + 1 : ℕ) : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hN]
    simp
  calc
    _ = (ArithmeticFunction.moebius (N + 1) : ℂ) *
        (((N + 1 : ℕ) : ℂ) ^ s * ((N + 1 : ℕ) : ℂ) ^ (-s)) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- The two adjacent rescalings of a Möbius head cannot both vanish asymptotically. -/
theorem finiteMobiusRecoveryHead_scaled_pair_not_both_zero
    (s : ℂ)
    (hcurrent : Tendsto (fun N : ℕ =>
      (N : ℂ) ^ s * finiteMobiusRecoveryHead N s) atTop (nhds 0))
    (hprevious : Tendsto (fun N : ℕ =>
      ((N + 1 : ℕ) : ℂ) ^ s * finiteMobiusRecoveryHead N s) atTop (nhds 0)) :
    False := by
  have hsuccessor : Tendsto (fun N : ℕ =>
      ((N + 1 : ℕ) : ℂ) ^ s * finiteMobiusRecoveryHead (N + 1) s)
      atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hcurrent.comp (tendsto_add_atTop_nat 1)
  have hmu : Tendsto (fun N : ℕ =>
      (ArithmeticFunction.moebius (N + 1) : ℂ)) atTop (nhds 0) := by
    simpa only [sub_zero] using
      (hsuccessor.sub hprevious).congr'
        (Filter.Eventually.of_forall fun N =>
          natSucc_cpow_mul_finiteMobiusRecoveryHead_sub N s)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ‖(ArithmeticFunction.moebius (N + 1) : ℂ) - 0‖ < (1 : ℝ) / 2 :=
    hmu.eventually (eventually_norm_sub_lt 0 (by norm_num : (0 : ℝ) < 1 / 2))
  rcases (eventually_atTop.1 hsmall) with ⟨N0, hN0⟩
  rcases Nat.exists_infinite_primes (N0 + 1) with ⟨p, hpN, hp⟩
  have hbound := hN0 (p - 1) (by omega : N0 ≤ p - 1)
  rw [show p - 1 + 1 = p by omega, ArithmeticFunction.moebius_apply_prime hp] at hbound
  norm_num at hbound

/-- The complex power of the consecutive-cutoff ratio tends to one. -/
theorem tendsto_natSucc_div_nat_cpow (s : ℂ) :
    Tendsto (fun N : ℕ =>
      ((((N + 1 : ℕ) : ℝ) / (N : ℝ) : ℝ) : ℂ) ^ s) atTop (nhds 1) := by
  have hbaseInv : Tendsto (fun N : ℕ =>
      ((N : ℂ) / ((N : ℂ) + 1))⁻¹) atTop (nhds 1) :=
    by simpa using (tendsto_natCast_div_add_atTop (1 : ℂ)).inv₀ one_ne_zero
  have hbase : Tendsto (fun N : ℕ =>
      ((((N + 1 : ℕ) : ℝ) / (N : ℝ) : ℝ) : ℂ)) atTop (nhds 1) := by
    apply hbaseInv.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    push_cast
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have hpow := (continuousAt_cpow_const (b := s) (by
    simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp hbase
  simpa [Function.comp_def] using hpow

/-- The ratio power transports the cutoff power from `N` to `N+1`. -/
theorem natSucc_div_nat_cpow_mul_nat_cpow
    (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    ((((N + 1 : ℕ) : ℝ) / (N : ℝ) : ℝ) : ℂ) ^ s * (N : ℂ) ^ s =
      ((N + 1 : ℕ) : ℂ) ^ s := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsuccR : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < N + 1)
  have hratioR : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) / (N : ℝ) :=
    div_pos hsuccR hNR
  have hlogRatio :
      Complex.log ((((N + 1 : ℕ) : ℝ) / (N : ℝ) : ℝ) : ℂ) =
        (Real.log (((N + 1 : ℕ) : ℝ) / (N : ℝ)) : ℂ) := by
    exact (Complex.ofReal_log hratioR.le).symm
  have hlogN : Complex.log (N : ℂ) = (Real.log (N : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hNR.le).symm
  have hlogSucc : Complex.log ((N + 1 : ℕ) : ℂ) =
      (Real.log ((N + 1 : ℕ) : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hsuccR.le).symm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hratioR.ne'),
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega : N ≠ 0)),
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega : N + 1 ≠ 0)),
    ← Complex.exp_add]
  congr 1
  rw [hlogRatio, hlogN, hlogSucc,
    Real.log_div (ne_of_gt hsuccR) (ne_of_gt hNR)]
  push_cast
  ring

/-- A vanishing rescaled head remains vanishing after shifting its cutoff power once. -/
theorem tendsto_natSucc_cpow_mul_finiteMobiusRecoveryHead_zero
    (s : ℂ)
    (hcurrent : Tendsto (fun N : ℕ =>
      (N : ℂ) ^ s * finiteMobiusRecoveryHead N s) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      ((N + 1 : ℕ) : ℂ) ^ s * finiteMobiusRecoveryHead N s) atTop (nhds 0) := by
  have hproduct := (tendsto_natSucc_div_nat_cpow s).mul hcurrent
  simpa only [mul_zero] using hproduct.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [← mul_assoc, natSucc_div_nat_cpow_mul_nat_cpow N hN s])

/-- Below the critical line, the cutoff power times the formation normalizer vanishes. -/
theorem tendsto_nat_cpow_mul_finiteCutoffNormalizer_zero
    (rho : StrictLeftNontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      (N : ℂ) ^ rho.1.1 *
        finiteCutoffNormalizer (finiteCutoffOpenStripPointOfZero rho.1) N)
      atTop (nhds 0) := by
  have hexponent : (rho.1.1 + (rho.1.1 - 1)).re < 0 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
    linarith [rho.2]
  have hpow : Tendsto (fun N : ℕ =>
      (N : ℂ) ^ (rho.1.1 + (rho.1.1 - 1))) atTop (nhds 0) :=
    tendsto_nat_cpow_zero hexponent
  have hscaled :=
    (tendsto_const_nhds (x := (1 - rho.1.1))).mul hpow
  simpa only [mul_zero] using hscaled.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    change (1 - rho.1.1) *
        (N : ℂ) ^ (rho.1.1 + (rho.1.1 - 1)) =
      (N : ℂ) ^ rho.1.1 *
        ((1 - rho.1.1) * (N : ℂ) ^ (rho.1.1 - 1))
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [Complex.cpow_add _ _ hN0]
    ring)

/-- Tail boundedness of the head product forces the rescaled Möbius head to vanish. -/
theorem tendsto_nat_cpow_mul_finiteMobiusRecoveryHead_zero_of_bounded_product
    (rho : StrictLeftNontrivialZetaZero)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun N : ℕ =>
      finiteZetaFormationHead N rho.1.1 * finiteMobiusRecoveryHead N rho.1.1)) :
    Tendsto (fun N : ℕ =>
      (N : ℂ) ^ rho.1.1 * finiteMobiusRecoveryHead N rho.1.1)
      atTop (nhds 0) := by
  let stripPoint := finiteCutoffOpenStripPointOfZero rho.1
  have hscale := tendsto_nat_cpow_mul_finiteCutoffNormalizer_zero rho
  have hzero : Tendsto (fun N : ℕ =>
      ((N : ℂ) ^ rho.1.1 * finiteCutoffNormalizer stripPoint N) *
        (finiteZetaFormationHead N rho.1.1 * finiteMobiusRecoveryHead N rho.1.1))
      atTop (nhds 0) :=
    hscale.zero_mul_isBoundedUnder_le hbounded
  have hnormalized := tendsto_normalized_finiteZetaFormationHead stripPoint
  have hinverse := hnormalized.inv₀ one_ne_zero
  have hproduct := hzero.mul hinverse
  simpa only [zero_mul] using hproduct.congr' (by
    filter_upwards [hnormalized.eventually_ne one_ne_zero] with N hne
    have hcancel :
        (finiteCutoffNormalizer stripPoint N * finiteZetaFormationHead N rho.1.1) *
          (finiteCutoffNormalizer stripPoint N * finiteZetaFormationHead N rho.1.1)⁻¹ = 1 :=
      mul_inv_cancel₀ hne
    calc
      ((N : ℂ) ^ rho.1.1 * finiteCutoffNormalizer stripPoint N) *
            (finiteZetaFormationHead N rho.1.1 * finiteMobiusRecoveryHead N rho.1.1) *
          (finiteCutoffNormalizer stripPoint N *
            finiteZetaFormationHead N rho.1.1)⁻¹ =
        ((N : ℂ) ^ rho.1.1 * finiteMobiusRecoveryHead N rho.1.1) *
          ((finiteCutoffNormalizer stripPoint N *
            finiteZetaFormationHead N rho.1.1) *
              (finiteCutoffNormalizer stripPoint N *
                finiteZetaFormationHead N rho.1.1)⁻¹) := by ring
      _ = _ := by rw [hcancel, mul_one])

/-- Rectangle overflow for the Möbius and constant-coefficient laws. -/
def finiteMobiusOverflow (N : ℕ) (s : ℂ) : ℂ :=
  finiteDirichletOverflow
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) N s

/-- The head product is one plus rectangle overflow at every nonempty cutoff. -/
theorem finiteZetaFormationHead_mul_finiteMobiusRecoveryHead_eq_one_add_overflow
    (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    finiteZetaFormationHead N s * finiteMobiusRecoveryHead N s =
      1 + finiteMobiusOverflow N s := by
  rw [finiteZetaFormationHead, finiteMobiusRecoveryHead_eq_finiteDirichletHead,
    mul_comm]
  simpa [finiteMobiusOverflow, hN] using finiteMobiusHead_mul_zetaHead N s

/-- Tail boundedness of overflow would bound the complete head product. -/
theorem bounded_finiteMobiusOverflow_implies_bounded_head_product
    (s : ℂ)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun N : ℕ => finiteMobiusOverflow N s)) :
    IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun N : ℕ =>
      finiteZetaFormationHead N s * finiteMobiusRecoveryHead N s) := by
  rcases hbounded.eventually_le with ⟨C, hC⟩
  apply isBoundedUnder_of_eventually_le (a := 1 + C)
  filter_upwards [hC, eventually_ge_atTop 1] with N hbound hN
  simp only [Function.comp_apply] at hbound ⊢
  rw [finiteZetaFormationHead_mul_finiteMobiusRecoveryHead_eq_one_add_overflow N hN]
  exact (norm_add_le _ _).trans (by simpa using add_le_add_left hbound 1)

/-- At a strict-left nontrivial zero, the Möbius rectangle overflow is not tail bounded. -/
theorem finiteMobiusOverflow_not_isBoundedUnder_at_strictLeftZero
    (rho : StrictLeftNontrivialZetaZero) :
    ¬ IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun N : ℕ => finiteMobiusOverflow N rho.1.1) := by
  intro hbounded
  have hproduct := bounded_finiteMobiusOverflow_implies_bounded_head_product rho.1.1 hbounded
  have hcurrent :=
    tendsto_nat_cpow_mul_finiteMobiusRecoveryHead_zero_of_bounded_product rho hproduct
  have hprevious :=
    tendsto_natSucc_cpow_mul_finiteMobiusRecoveryHead_zero rho.1.1 hcurrent
  exact finiteMobiusRecoveryHead_scaled_pair_not_both_zero rho.1.1 hcurrent hprevious

/-- Interaction between continuation correction and Möbius recovery. -/
def finiteCorrectionRecoveryInteraction (N : ℕ) (s : ℂ) : ℂ :=
  finiteCutoffContinuationCorrection N s * finiteMobiusRecoveryHead N s

/-- At a strict-left zero, the matched correction--recovery process is not tail bounded. -/
theorem finiteCorrectionRecoveryInteraction_not_isBoundedUnder_at_strictLeftZero
    (rho : StrictLeftNontrivialZetaZero) :
    ¬ IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun N : ℕ => finiteCorrectionRecoveryInteraction N rho.1.1) := by
  intro hinteraction
  have htotal : Tendsto (fun N : ℕ =>
      finiteMobiusOverflow N rho.1.1 +
        finiteCorrectionRecoveryInteraction N rho.1.1) atTop (nhds (-1)) := by
    simpa [finiteMobiusOverflow, finiteCorrectionRecoveryInteraction] using
      tendsto_finiteMobiusBoundaryFailureTotal_at_zero rho.1
  have htotalBound : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun N : ℕ =>
      finiteMobiusOverflow N rho.1.1 +
        finiteCorrectionRecoveryInteraction N rho.1.1) :=
    htotal.norm.isBoundedUnder_le
  rcases htotalBound.eventually_le with ⟨C, hC⟩
  rcases hinteraction.eventually_le with ⟨D, hD⟩
  apply finiteMobiusOverflow_not_isBoundedUnder_at_strictLeftZero rho
  apply isBoundedUnder_of_eventually_le (a := C + D)
  filter_upwards [hC, hD] with N hsum hright
  simp only [Function.comp_apply] at hsum hright ⊢
  calc
    ‖finiteMobiusOverflow N rho.1.1‖ =
        ‖(finiteMobiusOverflow N rho.1.1 +
            finiteCorrectionRecoveryInteraction N rho.1.1) -
          finiteCorrectionRecoveryInteraction N rho.1.1‖ := by ring_nf
    _ ≤ ‖finiteMobiusOverflow N rho.1.1 +
          finiteCorrectionRecoveryInteraction N rho.1.1‖ +
        ‖finiteCorrectionRecoveryInteraction N rho.1.1‖ := norm_sub_le _ _
    _ ≤ C + D := add_le_add hsum hright

/-- A strict-left nontrivial zero forces both labelled boundary processes to escape every bounded
tail while their exact total converges to `-1`. -/
theorem strictLeftZero_forces_two_process_overflow_escape
    (rho : StrictLeftNontrivialZetaZero) :
    (¬ IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun N : ℕ => finiteMobiusOverflow N rho.1.1)) ∧
    (¬ IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun N : ℕ => finiteCorrectionRecoveryInteraction N rho.1.1)) ∧
    Tendsto (fun N : ℕ =>
      finiteMobiusOverflow N rho.1.1 +
        finiteCorrectionRecoveryInteraction N rho.1.1) atTop (nhds (-1)) := by
  exact ⟨finiteMobiusOverflow_not_isBoundedUnder_at_strictLeftZero rho,
    finiteCorrectionRecoveryInteraction_not_isBoundedUnder_at_strictLeftZero rho,
    by simpa [finiteMobiusOverflow, finiteCorrectionRecoveryInteraction] using
      tendsto_finiteMobiusBoundaryFailureTotal_at_zero rho.1⟩

/-- Rectangle overflow crosses any prescribed norm threshold after any prescribed cutoff. -/
theorem exists_finiteMobiusOverflow_norm_gt_after
    (rho : StrictLeftNontrivialZetaZero) (R : ℝ) (N0 : ℕ) :
    ∃ N, N0 ≤ N ∧ R < ‖finiteMobiusOverflow N rho.1.1‖ := by
  by_contra h
  push Not at h
  apply finiteMobiusOverflow_not_isBoundedUnder_at_strictLeftZero rho
  apply isBoundedUnder_of_eventually_le (a := R)
  filter_upwards [eventually_ge_atTop N0] with N hN
  simpa only [Function.comp_apply] using h N hN

/-- Both labelled processes cross any norm threshold simultaneously at arbitrarily late cutoffs. -/
theorem exists_joint_overflow_escape_after
    (rho : StrictLeftNontrivialZetaZero) (R : ℝ) (N0 : ℕ) :
    ∃ N, N0 ≤ N ∧
      R < ‖finiteMobiusOverflow N rho.1.1‖ ∧
      R < ‖finiteCorrectionRecoveryInteraction N rho.1.1‖ := by
  have htotal : Tendsto (fun N : ℕ =>
      finiteMobiusOverflow N rho.1.1 +
        finiteCorrectionRecoveryInteraction N rho.1.1) atTop (nhds (-1)) := by
    simpa [finiteMobiusOverflow, finiteCorrectionRecoveryInteraction] using
      tendsto_finiteMobiusBoundaryFailureTotal_at_zero rho.1
  rcases htotal.norm.isBoundedUnder_le.eventually_le with ⟨C, hC⟩
  rcases eventually_atTop.1 hC with ⟨M, hM⟩
  rcases exists_finiteMobiusOverflow_norm_gt_after rho (R + C) (max N0 M) with
    ⟨N, hN, hoverflow⟩
  have hsum := hM N (le_trans (le_max_right N0 M) hN)
  have hCnonneg : 0 ≤ C :=
    le_trans (norm_nonneg (finiteMobiusOverflow N rho.1.1 +
      finiteCorrectionRecoveryInteraction N rho.1.1)) hsum
  refine ⟨N, le_trans (le_max_left N0 M) hN, ?_, ?_⟩
  · linarith
  · have htriangle : ‖finiteMobiusOverflow N rho.1.1‖ ≤
        ‖finiteMobiusOverflow N rho.1.1 +
          finiteCorrectionRecoveryInteraction N rho.1.1‖ +
        ‖finiteCorrectionRecoveryInteraction N rho.1.1‖ := by
      calc
        ‖finiteMobiusOverflow N rho.1.1‖ =
            ‖(finiteMobiusOverflow N rho.1.1 +
                finiteCorrectionRecoveryInteraction N rho.1.1) -
              finiteCorrectionRecoveryInteraction N rho.1.1‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith

/-- Every off-critical zero orbit has a member whose two source processes jointly escape. -/
theorem offCriticalZeroOrbit_exists_joint_overflow_escape_after
    (rho : OffCriticalNontrivialZetaZero) (R : ℝ) (N0 : ℕ) :
    ∃ left : StrictLeftNontrivialZetaZero, ∃ N, N0 ≤ N ∧
      R < ‖finiteMobiusOverflow N left.1.1‖ ∧
      R < ‖finiteCorrectionRecoveryInteraction N left.1.1‖ := by
  let left := offCriticalZero_strictLeftMember rho
  exact ⟨left, exists_joint_overflow_escape_after left R N0⟩

end RHTower.DeletionMixedRefinement
