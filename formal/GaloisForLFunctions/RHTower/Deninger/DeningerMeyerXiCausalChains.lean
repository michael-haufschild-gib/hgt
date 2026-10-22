import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerCausalDivision
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerExactXiCapSource
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFiniteXiJetPacket

/-!
# Actual Xi Jordan sources in Meyer cohomology

Repeated causal division of the fixed Xi boundary realizes the entire local
divisor chain inside the all-weight Meyer target.  Negative differentiation
descends through genuine Poisson boundaries.  The resulting cohomology
classes have exactly the prescribed local jet orders, with zero full jets
at every other Xi divisor.
-/

open Complex Set Filter Topology MeromorphicOn
open scoped Classical

namespace RHTower
noncomputable section

theorem xi_analyticOrderAt_support (rho : XiDivisorSupport) :
    analyticOrderAt xi (rho : ℂ) = (xiSupportMultiplicity rho : ℕ∞) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (xi_order_ne_top rho)
  have hD : (MeromorphicOn.divisor xi Set.univ) (rho : ℂ) = (n : ℤ) := by
    rw [xi_analyticOnNhd_univ.divisor_apply (Set.mem_univ (rho : ℂ)), ← hn]
    simp
  rw [← hn, xiSupportMultiplicity, hD]
  simp

private theorem mellin_zero_before_xi_order
    (rho : XiDivisorSupport) (g : DeningerMeyerStrongLogTarget)
    (k : ℕ) (hk : k < xiSupportMultiplicity rho)
    (hfactor : ∀ s, xi s = (s - (rho : ℂ)) ^ k * deningerMeyerStrongLogMellin g s) :
    deningerMeyerStrongLogMellin g (rho : ℂ) = 0 := by
  by_contra hn
  have hfun : xi = ((· - (rho : ℂ)) ^ k) * deningerMeyerStrongLogMellin g := by
    funext s
    exact hfactor s
  have ho := xi_analyticOrderAt_support rho
  conv_lhs at ho => arg 1; rw [hfun]
  rw [analyticOrderAt_mul (by fun_prop)
    (analyticOnNhd_deningerMeyerStrongLogMellin g.property _ (Set.mem_univ _)),
    analyticOrderAt_centeredMonomial,
    analyticOrderAt_eq_zero.mpr (Or.inr hn), add_zero] at ho
  have he : k = xiSupportMultiplicity rho := by exact_mod_cast ho
  omega

/-- The literal source and its exact entire Mellin factorization, constructed together. -/
def deningerMeyerXiCausalSourceData (rho : XiDivisorSupport) :
    (k : ℕ) → k ≤ xiSupportMultiplicity rho →
      {g : DeningerMeyerStrongLogTarget //
        ∀ s, xi s = (s - (rho : ℂ)) ^ k * deningerMeyerStrongLogMellin g s}
  | 0, _ => ⟨deningerMeyerStrongLogSumLM deningerMeyerXiCapSource, by
      intro s
      simpa only [pow_zero, one_mul, deningerMeyerBoundaryMellin] using
        (deningerMeyerXiCapSource_mellin s).symm⟩
  | k + 1, hk => by
      let prev := deningerMeyerXiCausalSourceData rho k (by omega)
      have hz := mellin_zero_before_xi_order rho prev.val k (by omega) prev.property
      refine ⟨deningerMeyerCausalDivide prev.val (rho : ℂ) hz, ?_⟩
      intro s
      rw [prev.property s, ← deningerMeyerCausalDivide_mellin prev.val (rho : ℂ) hz s,
        pow_succ]
      ring

/-- `k` successive causal divisions of the fixed actual Xi boundary. -/
def deningerMeyerXiCausalSource (rho : XiDivisorSupport) (k : ℕ)
    (hk : k ≤ xiSupportMultiplicity rho) : DeningerMeyerStrongLogTarget :=
  (deningerMeyerXiCausalSourceData rho k hk).val

theorem deningerMeyerXiCausalSource_factor (rho : XiDivisorSupport) (k : ℕ)
    (hk : k ≤ xiSupportMultiplicity rho) (s : ℂ) :
    xi s = (s - (rho : ℂ)) ^ k *
      deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk) s :=
  (deningerMeyerXiCausalSourceData rho k hk).property s

theorem deningerMeyerXiCausalSource_generator (rho : XiDivisorSupport) (k : ℕ)
    (hk : k + 1 ≤ xiSupportMultiplicity rho) :
    deningerMeyerStrongLogGenerator (deningerMeyerXiCausalSource rho (k + 1) hk) =
      (rho : ℂ) • deningerMeyerXiCausalSource rho (k + 1) hk +
        deningerMeyerXiCausalSource rho k (by omega) :=
  deningerMeyerStrongLogGenerator_causalDivide _ _
    (mellin_zero_before_xi_order rho (deningerMeyerXiCausalSource rho k (by omega))
      k (by omega) (deningerMeyerXiCausalSource_factor rho k (by omega)))

theorem deningerMeyerXiCausalSource_order (rho : XiDivisorSupport) (k : ℕ)
    (hk : k ≤ xiSupportMultiplicity rho) :
    analyticOrderAt
      (deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk)) (rho : ℂ) =
      ((xiSupportMultiplicity rho - k : ℕ) : ℕ∞) := by
  have hfun : xi = ((· - (rho : ℂ)) ^ k) *
      deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk) := by
    funext s
    exact deningerMeyerXiCausalSource_factor rho k hk s
  have ho := xi_analyticOrderAt_support rho
  conv_lhs at ho => arg 1; rw [hfun]
  rw [analyticOrderAt_mul (by fun_prop)
    (analyticOnNhd_deningerMeyerStrongLogMellin
      (deningerMeyerXiCausalSource rho k hk).property _ (Set.mem_univ _)),
    analyticOrderAt_centeredMonomial] at ho
  apply ENat.add_right_injective_of_ne_top (n := (k : ℕ∞)) (by simp)
  dsimp only
  rw [ho, ← Nat.cast_add, Nat.add_sub_of_le hk]

theorem deningerMeyerXiCausalSource_order_other (rho tau : XiDivisorSupport)
    (hne : tau ≠ rho) (k : ℕ) (hk : k ≤ xiSupportMultiplicity rho) :
    analyticOrderAt
      (deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk)) (tau : ℂ) =
      (xiSupportMultiplicity tau : ℕ∞) := by
  have hfun : xi = ((· - (rho : ℂ)) ^ k) *
      deningerMeyerStrongLogMellin (deningerMeyerXiCausalSource rho k hk) := by
    funext s
    exact deningerMeyerXiCausalSource_factor rho k hk s
  have hne' : (tau : ℂ) - (rho : ℂ) ≠ 0 := sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr hne)
  have hz : analyticOrderAt (((· - (rho : ℂ)) ^ k) : ℂ → ℂ) (tau : ℂ) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (pow_ne_zero k hne'))
  have ho := xi_analyticOrderAt_support tau
  conv_lhs at ho => arg 1; rw [hfun]
  rw [analyticOrderAt_mul (by fun_prop)
    (analyticOnNhd_deningerMeyerStrongLogMellin
      (deningerMeyerXiCausalSource rho k hk).property _ (Set.mem_univ _)),
    hz, zero_add] at ho
  exact ho

theorem deningerMeyerStrongLogGenerator_boundary (f : DeningerMeyerCap) :
    deningerMeyerStrongLogGenerator (deningerMeyerStrongLogSumLM f) =
      deningerMeyerStrongLogSumLM (deningerMeyerNegativeEuler f) := by
  apply Subtype.ext
  exact (deningerMeyerNegativeEuler_boundary f).symm

/-- The logarithmic generator on the literal quotient by actual boundaries. -/
def deningerMeyerCohomologyGenerator : Module.End ℂ DeningerMeyerStrongLogCohomology :=
  (LinearMap.range deningerMeyerStrongLogSumLM).mapQ
    (LinearMap.range deningerMeyerStrongLogSumLM) deningerMeyerStrongLogGenerator (by
      rintro _ ⟨f, rfl⟩
      exact ⟨deningerMeyerNegativeEuler f,
        (deningerMeyerStrongLogGenerator_boundary f).symm⟩)

@[simp]
theorem deningerMeyerCohomologyGenerator_mk (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerCohomologyGenerator (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (deningerMeyerStrongLogGenerator g) := rfl

/-- Divided Xi source class in actual Meyer cohomology. -/
def deningerMeyerXiCausalClass (rho : XiDivisorSupport) (k : ℕ)
    (hk : k ≤ xiSupportMultiplicity rho) : DeningerMeyerStrongLogCohomology :=
  Submodule.Quotient.mk (deningerMeyerXiCausalSource rho k hk)

@[simp]
theorem deningerMeyerXiCausalClass_zero (rho : XiDivisorSupport) :
    deningerMeyerXiCausalClass rho 0 (Nat.zero_le _) = 0 :=
  deningerMeyerStrongLog_boundary_class_zero deningerMeyerXiCapSource

/-- Every full Xi multiplicity chain is realized by genuine source classes. -/
theorem deningerMeyerXiCausalClass_generator (rho : XiDivisorSupport) (k : ℕ)
    (hk : k + 1 ≤ xiSupportMultiplicity rho) :
    deningerMeyerCohomologyGenerator (deningerMeyerXiCausalClass rho (k + 1) hk) =
      (rho : ℂ) • deningerMeyerXiCausalClass rho (k + 1) hk +
        deningerMeyerXiCausalClass rho k (by omega) := by
  change Submodule.Quotient.mk
    (deningerMeyerStrongLogGenerator (deningerMeyerXiCausalSource rho (k + 1) hk)) = _
  rw [deningerMeyerXiCausalSource_generator]
  simp only [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul,
    deningerMeyerXiCausalClass]

/-- Chain indexed by its first nonzero local jet, for finite triangular synthesis. -/
def deningerMeyerXiJetSource (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) : DeningerMeyerStrongLogCohomology :=
  deningerMeyerXiCausalClass rho (xiSupportMultiplicity rho - j.val) (Nat.sub_le _ _)

theorem deningerMeyerXiJetSource_jet_zero (rho : XiDivisorSupport)
    (j i : DeningerArithmeticJetIndex rho) (hi : i.val < j.val) :
    deningerMeyerXiSupportJetEvaluationLM rho i (deningerMeyerXiJetSource rho j) = 0 := by
  rw [deningerMeyerXiJetSource, deningerMeyerXiCausalClass,
    deningerMeyerXiSupportJetEvaluationLM_mk,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  have ho := deningerMeyerXiCausalSource_order rho
    (xiSupportMultiplicity rho - j.val) (Nat.sub_le _ _)
  have hj : xiSupportMultiplicity rho - (xiSupportMultiplicity rho - j.val) = j.val := by
    omega
  rw [hj] at ho
  exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (analyticOnNhd_deningerMeyerStrongLogMellin
      (deningerMeyerXiCausalSource rho _ _).property _ (Set.mem_univ _))).mp ho |>.1 i.val hi

theorem deningerMeyerXiJetSource_jet_ne_zero (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerXiSupportJetEvaluationLM rho j (deningerMeyerXiJetSource rho j) ≠ 0 := by
  rw [deningerMeyerXiJetSource, deningerMeyerXiCausalClass,
    deningerMeyerXiSupportJetEvaluationLM_mk,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  have ho := deningerMeyerXiCausalSource_order rho
    (xiSupportMultiplicity rho - j.val) (Nat.sub_le _ _)
  have hj : xiSupportMultiplicity rho - (xiSupportMultiplicity rho - j.val) = j.val := by
    omega
  rw [hj] at ho
  exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (analyticOnNhd_deningerMeyerStrongLogMellin
      (deningerMeyerXiCausalSource rho _ _).property _ (Set.mem_univ _))).mp ho |>.2

theorem deningerMeyerXiJetSource_other_jet_zero (rho tau : XiDivisorSupport)
    (hne : tau ≠ rho) (j : DeningerArithmeticJetIndex rho)
    (i : DeningerArithmeticJetIndex tau) :
    deningerMeyerXiSupportJetEvaluationLM tau i (deningerMeyerXiJetSource rho j) = 0 := by
  rw [deningerMeyerXiJetSource, deningerMeyerXiCausalClass,
    deningerMeyerXiSupportJetEvaluationLM_mk,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  have ho := deningerMeyerXiCausalSource_order_other rho tau hne
    (xiSupportMultiplicity rho - j.val) (Nat.sub_le _ _)
  exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (analyticOnNhd_deningerMeyerStrongLogMellin
      (deningerMeyerXiCausalSource rho _ _).property _ (Set.mem_univ _))).mp ho |>.1 i.val i.isLt

theorem deningerMeyerXiJetSource_generator (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerCohomologyGenerator (deningerMeyerXiJetSource rho j) =
      (rho : ℂ) • deningerMeyerXiJetSource rho j +
        if hj : j.val + 1 < xiSupportMultiplicity rho then
          deningerMeyerXiJetSource rho ⟨j.val + 1, hj⟩ else 0 := by
  by_cases hj : j.val + 1 < xiSupportMultiplicity rho
  · rw [dif_pos hj]
    have he : xiSupportMultiplicity rho - j.val =
        (xiSupportMultiplicity rho - (j.val + 1)) + 1 := by omega
    simpa only [deningerMeyerXiJetSource, he] using
      deningerMeyerXiCausalClass_generator rho
        (xiSupportMultiplicity rho - (j.val + 1)) (by omega)
  · rw [dif_neg hj]
    have he : xiSupportMultiplicity rho - j.val = 1 := by omega
    simpa only [deningerMeyerXiJetSource, he, deningerMeyerXiCausalClass_zero] using
      deningerMeyerXiCausalClass_generator rho 0 (xiSupportMultiplicity_pos rho)

end
end RHTower
