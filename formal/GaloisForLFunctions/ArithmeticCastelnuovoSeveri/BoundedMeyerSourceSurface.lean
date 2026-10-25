import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerCriticalTopAlgebra
import GaloisForLFunctions.RHTower.ArithmeticJointJetExclusion
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision

/-!
# Riemann–Roch and Bézout on the bounded Meyer source surface

Restrict the original Meyer intersection surface to sources with bounded full-Hasse
centered orbits. Its actual trace defect is nonnegative, so the genuine degree cone
has RR, Bézout, and ampleness. Numerical and principal equivalence agree on this
carrier exactly when the critical zeros are simple; off-line jets are already absent.
-/

noncomputable section
open Complex RHTower
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Both fibres together with the actual bounded centered-orbit source carrier. -/
def meyerBoundedCycleSubmodule : Submodule ℝ MeyerScalingCycle where
  carrier := {x | MeyerCriticalTopJets x.2.2}
  zero_mem' := meyerCriticalTopSourceSubmodule.zero_mem
  add_mem' := fun _ _ hx hy => meyerCriticalTopSourceSubmodule.add_mem hx hy
  smul_mem' a x hx := by
    change MeyerCriticalTopJets ((a : ℂ) • x.2.2)
    exact meyerCriticalTopSourceSubmodule.smul_mem (a : ℂ) hx

private theorem bounded_H : meyerScalingSurface.H ∈ meyerBoundedCycleSubmodule :=
  meyerCriticalTopSourceSubmodule.zero_mem

private theorem bounded_V : meyerScalingSurface.V ∈ meyerBoundedCycleSubmodule :=
  meyerCriticalTopSourceSubmodule.zero_mem

/-- The restriction retains the original pairing and both pole degrees. -/
def meyerBoundedSurface : PolarSurface meyerBoundedCycleSubmodule where
  pair := meyerScalingSurface.pair.compl₁₂
    meyerBoundedCycleSubmodule.subtype meyerBoundedCycleSubmodule.subtype
  pair_comm x y := meyerScalingSurface.pair_comm x.1 y.1
  H := ⟨meyerScalingSurface.H, bounded_H⟩
  V := ⟨meyerScalingSurface.V, bounded_V⟩
  pair_H_H := meyerScalingSurface.pair_H_H
  pair_V_V := meyerScalingSurface.pair_V_V
  pair_H_V := meyerScalingSurface.pair_H_V

theorem meyerBoundedSurface_defect (x y : meyerBoundedCycleSubmodule) :
    meyerBoundedSurface.defect x y = meyerSourceTrace x.1.2.2 y.1.2.2 :=
  meyerScalingSurface_defect x.1 y.1

/-- The restricted Hodge index follows from actual trace positivity on the bounded-orbit carrier. -/
theorem meyerBoundedSurface_hodgeIndex : meyerBoundedSurface.HodgeIndex := by
  apply meyerBoundedSurface.hodgeIndex_iff_defect_nonneg.mpr
  intro x
  rw [meyerBoundedSurface_defect]
  exact meyerCriticalTopJets_trace_nonneg x.2

/-- The actual cohomological degree cone restricted to bounded source orbits. -/
def meyerBoundedDegreeSourceCone : Set meyerBoundedCycleSubmodule :=
  {x | x.1 ∈ meyerDegreeSourceCone}

theorem meyerBoundedDegreeSourceCone_eq_positiveCone :
    meyerBoundedDegreeSourceCone = meyerBoundedSurface.positiveCone := by
  unfold meyerBoundedDegreeSourceCone
  rw [meyerDegreeSourceCone_eq_positiveCone]
  rfl

/-- Riemann–Roch holds on the actual restricted source surface. -/
theorem meyerBoundedDegreeSourceCone_riemannRoch :
    meyerBoundedSurface.RiemannRochAxiom meyerBoundedDegreeSourceCone := by
  rw [meyerBoundedDegreeSourceCone_eq_positiveCone]
  exact meyerBoundedSurface.positiveCone_riemannRoch

/-- Bézout positivity holds simultaneously on this restricted carrier. -/
theorem meyerBoundedDegreeSourceCone_bezout :
    meyerBoundedSurface.BezoutAxiom meyerBoundedDegreeSourceCone := by
  rw [meyerBoundedDegreeSourceCone_eq_positiveCone]
  exact meyerBoundedSurface.positiveCone_bezout meyerBoundedSurface_hodgeIndex

theorem meyerBoundedDegreeSourceCone_ample :
    meyerBoundedSurface.AmpleAxiom meyerBoundedDegreeSourceCone := by
  rw [meyerBoundedDegreeSourceCone_eq_positiveCone]
  exact meyerBoundedSurface.positiveCone_ample_iff_hodgeIndex.mpr meyerBoundedSurface_hodgeIndex

theorem meyerBoundedDegreeSourceCone_add_closed :
    ∀ x ∈ meyerBoundedDegreeSourceCone, ∀ y ∈ meyerBoundedDegreeSourceCone,
      x + y ∈ meyerBoundedDegreeSourceCone := by
  rw [meyerBoundedDegreeSourceCone_eq_positiveCone]
  exact meyerBoundedSurface.positiveCone_add_closed_iff_hodgeIndex.mpr meyerBoundedSurface_hodgeIndex

/-- Restricted numerical readings still detect both pole degrees and every surviving value. -/
theorem meyerBoundedSurface_radical_iff (x : meyerBoundedCycleSubmodule) :
    (∀ y : meyerBoundedCycleSubmodule, meyerBoundedSurface.pair x y = 0) ↔
      meyerDegreeH x.1 = 0 ∧ meyerDegreeV x.1 = 0 ∧
        ∀ rho : XiDivisorSupport, deningerMeyerStrongLogMellin x.1.2.2 (rho : ℂ) = 0 := by
  constructor
  · intro h
    have hH := h meyerBoundedSurface.H
    have hV := h meyerBoundedSurface.V
    change meyerScalingSurface.pair x.1 meyerScalingSurface.H = 0 at hH
    change meyerScalingSurface.pair x.1 meyerScalingSurface.V = 0 at hV
    rw [meyerScalingSurface_pair_H] at hH
    rw [meyerScalingSurface_pair_V] at hV
    refine ⟨hH, hV, (meyerCriticalTopJets_trace_radical_iff x.1.2.2 x.2).mp ?_⟩
    intro g hg
    have he := h ⟨(0, 0, g), hg⟩
    change meyerScalingPair x.1 (0, 0, g) = 0 at he
    simpa only [meyerScalingPair, hH, hV, zero_mul, zero_add, zero_sub, neg_eq_zero] using he
  · intro h y
    exact (meyerScalingPair_radical_iff x.1).mpr h y.1

/-- Cone lineality is precisely the restricted numerical radical. -/
theorem meyerBoundedDegreeSourceCone_lineality_iff (x : meyerBoundedCycleSubmodule) :
    (x ∈ meyerBoundedDegreeSourceCone ∧ -x ∈ meyerBoundedDegreeSourceCone) ↔
      ∀ y : meyerBoundedCycleSubmodule, meyerBoundedSurface.pair x y = 0 := by
  constructor
  · rintro ⟨hx, hn⟩
    apply meyerBoundedDegreeSourceCone_ample x hx
    rw [meyerBoundedDegreeSourceCone_eq_positiveCone] at hx hn
    have hp := hx.2
    have hm := hn.2
    have he : meyerBoundedSurface.pair (-x) meyerBoundedSurface.ample =
        -meyerBoundedSurface.pair x meyerBoundedSurface.ample :=
      (meyerBoundedSurface.pair.flip meyerBoundedSurface.ample).map_neg x
    rw [he] at hm
    exact le_antisymm (neg_nonneg.mp hm) hp
  · intro h
    rw [meyerBoundedDegreeSourceCone_eq_positiveCone]
    constructor
    · exact ⟨(h x).ge, (h _).ge⟩
    · have hn (y : meyerBoundedCycleSubmodule) : meyerBoundedSurface.pair (-x) y = 0 := by
        calc
          meyerBoundedSurface.pair (-x) y = -meyerBoundedSurface.pair x y :=
            (meyerBoundedSurface.pair.flip y).map_neg x
          _ = 0 := by rw [h y, neg_zero]
      exact ⟨(hn (-x)).ge, (hn _).ge⟩

/-- The only remaining discrepancy between numerical and principal classes is critical multiplicity. -/
theorem meyerBoundedSurface_radical_eq_principal_iff :
    (∀ x : meyerBoundedCycleSubmodule,
      (∀ y : meyerBoundedCycleSubmodule, meyerBoundedSurface.pair x y = 0) ↔
        ∃ f : DeningerMeyerCap, x.1 = meyerPrincipalCycle f) ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h rho hr
    by_contra hne
    have hm : 1 < xiSupportMultiplicity rho := by
      have hp := xiSupportMultiplicity_pos rho
      omega
    let j : DeningerArithmeticJetIndex rho := ⟨xiSupportMultiplicity rho - 1, by omega⟩
    let g := meyerSingleJetSource rho j
    have hg : MeyerCriticalTopJets g := meyerSingleTopSource_criticalTopJets rho hr
    let x : meyerBoundedCycleSubmodule := ⟨(-meyerPoleA g, -meyerPoleB g, g), hg⟩
    have hrad : ∀ y : meyerBoundedCycleSubmodule, meyerBoundedSurface.pair x y = 0 := by
      apply (meyerBoundedSurface_radical_iff x).mpr
      refine ⟨by simp only [x, meyerDegreeH, neg_add_cancel],
        by simp only [x, meyerDegreeV, neg_add_cancel], ?_⟩
      intro sigma
      have he := meyerSingleJetSource_jet rho j sigma ⟨0, xiSupportMultiplicity_pos sigma⟩
      have hj : (0 : ℕ) ≠ j.val := by dsimp only [j]; omega
      simpa only [hj, and_false, ↓reduceIte] using he
    obtain ⟨f, hf⟩ := (h x).mp hrad
    have he : g = deningerMeyerStrongLogSumLM f := congrArg (fun z : MeyerScalingCycle => z.2.2) hf
    exact meyerSingleJetSource_not_boundary rho j ⟨f, he.symm⟩
  · intro hs x
    constructor
    · intro hrad
      obtain ⟨hH, hV, hv⟩ := (meyerBoundedSurface_radical_iff x).mp hrad
      have hg : x.1.2.2 ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
        apply (meyerSource_boundary_iff_jets_zero _).mpr
        intro rho j
        by_cases hr : (rho : ℂ).re = 1 / 2
        · have hj : j.val = 0 := by
            have hlt := j.isLt
            have hm := hs rho hr
            omega
          rw [hj]
          exact hv rho
        · exact x.2 rho j (Or.inl hr)
      obtain ⟨f, hf⟩ := hg
      refine ⟨f, ?_⟩
      apply Prod.ext
      · change x.1.1 = -meyerPoleA (deningerMeyerStrongLogSumLM f)
        rw [hf]
        change x.1.1 + meyerPoleA x.1.2.2 = 0 at hV
        linarith only [hV]
      · apply Prod.ext
        · change x.1.2.1 = -meyerPoleB (deningerMeyerStrongLogSumLM f)
          rw [hf]
          change x.1.2.1 + meyerPoleB x.1.2.2 = 0 at hH
          linarith only [hH]
        · exact hf.symm
    · rintro ⟨f, hf⟩ y
      change meyerScalingPair x.1 y.1 = 0
      rw [hf]
      exact meyerPrincipalCycle_pair_left f y.1

/-- Pointedness modulo genuine principal classes has the same critical-simplicity boundary. -/
theorem meyerBoundedDegreeSourceCone_pointed_mod_principal_iff :
    (∀ x : meyerBoundedCycleSubmodule,
      (x ∈ meyerBoundedDegreeSourceCone ∧ -x ∈ meyerBoundedDegreeSourceCone) ↔
        ∃ f : DeningerMeyerCap, x.1 = meyerPrincipalCycle f) ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1 := by
  simp only [meyerBoundedDegreeSourceCone_lineality_iff]
  exact meyerBoundedSurface_radical_eq_principal_iff

/-- This restricted surface is the whole genuine source surface exactly under simple criticality. -/
theorem meyerBoundedCycleSubmodule_eq_top_iff :
    meyerBoundedCycleSubmodule = ⊤ ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  rw [← all_meyerHilbertOrbits_bounded_iff]
  constructor
  · intro h g
    have hg : (0, 0, g) ∈ meyerBoundedCycleSubmodule := by rw [h]; exact Submodule.mem_top
    exact (meyerHilbertOrbitBounded_iff_criticalTopJets g).mpr hg
  · intro h
    apply top_unique
    intro x _
    exact (meyerHilbertOrbitBounded_iff_criticalTopJets x.2.2).mp (h x.2.2)

/-- Actual simple critical points above every height supply strictly positive bounded-orbit sources. -/
theorem exists_high_meyer_bounded_source_trace_one (T : ℝ) :
    ∃ rho : XiDivisorSupport, T < (rho : ℂ).im ∧ (rho : ℂ).re = 1 / 2 ∧
      xiSupportMultiplicity rho = 1 ∧ MeyerCriticalTopJets (meyerPointSource rho) ∧
      meyerSourceTrace (meyerPointSource rho) (meyerPointSource rho) = 1 := by
  obtain ⟨t, ht, _, hz, hm⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi T
  let rho : XiDivisorSupport := ⟨DeletionMixedRefinement.criticalResponsePoint t,
    mem_xi_divisor_support_of_eq_zero hz⟩
  have hr : (rho : ℂ).re = 1 / 2 := by simp [rho, DeletionMixedRefinement.criticalResponsePoint]
  have hs : xiSupportMultiplicity rho = 1 := by
    rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat]
    exact hm
  refine ⟨rho, ?_, hr, hs, ?_, ?_⟩
  · simpa [rho, DeletionMixedRefinement.criticalResponsePoint] using ht
  · simpa only [meyerPointSource, hs, Nat.sub_self] using
      meyerSingleTopSource_criticalTopJets rho hr
  · rw [meyerPointSource_trace, meyerPointSource_values,
      if_pos (meyerLineReflect_eq_self_of_critical rho hr), hs]
    norm_num

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedSurface_defect
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedSurface_hodgeIndex
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedDegreeSourceCone_eq_positiveCone
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedDegreeSourceCone_riemannRoch
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedDegreeSourceCone_bezout
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedDegreeSourceCone_ample
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedDegreeSourceCone_add_closed
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedSurface_radical_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedDegreeSourceCone_lineality_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedSurface_radical_eq_principal_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedDegreeSourceCone_pointed_mod_principal_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedCycleSubmodule_eq_top_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_high_meyer_bounded_source_trace_one
