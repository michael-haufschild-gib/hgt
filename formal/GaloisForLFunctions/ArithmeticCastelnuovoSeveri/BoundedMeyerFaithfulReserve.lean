import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.BoundedMeyerSourceSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerHilbertReserveFlowRigidity

/-!
# Faithful reserves on the bounded Meyer surface

The faithful Hilbert–Schmidt reserve is invariant on every bounded centered orbit.
Its effective cone has Bézout and ampleness there, but RR holds exactly when all
critical Xi zeros are simple. Multiple critical highest jets account for the
remaining adjoint defect; no assertion about off-line zeros is needed.
-/

noncomputable section
open Complex RHTower ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem bounded_operator_diagonal
    (hs : ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1)
    {g : DeningerMeyerStrongLogTarget} (hg : MeyerCriticalTopJets g)
    (x : DeningerArithmeticJetHilbert) (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHilbertConvolution g x q =
      deningerMeyerStrongLogMellin g (q.1 : ℂ) * x q := by
  by_cases hr : (q.1 : ℂ).re = 1 / 2
  · have hq : q.2.val = 0 := by
      have hlt := q.2.isLt
      have hm := hs q.1 hr
      omega
    rw [deningerMeyerHilbertConvolution_jets, hq]
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton,
      deningerMeyerHasseMoment, Nat.factorial_zero, Nat.cast_one, div_one,
      deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero]
  · have hv : deningerMeyerStrongLogMellin g (q.1 : ℂ) = 0 :=
      hg q.1 ⟨0, xiSupportMultiplicity_pos q.1⟩ (Or.inl hr)
    rw [hv, zero_mul, deningerMeyerHilbertConvolution_jets]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≤ q.2.val := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hklt : k < xiSupportMultiplicity q.1 := lt_of_le_of_lt hkj q.2.isLt
    rw [deningerMeyerHasseMoment, hg q.1 ⟨k, hklt⟩ (Or.inl hr), zero_div, zero_mul]

/-- Critical simplicity makes arithmetic sharp the adjoint on the bounded carrier alone. -/
theorem meyerBounded_sharp_eq_adjoint_of_critical_simple
    (hs : ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1)
    {g : DeningerMeyerStrongLogTarget} (hg : MeyerCriticalTopJets g) :
    deningerMeyerHilbertConvolution (deningerMeyerSourceSharp g) =
      adjoint (deningerMeyerHilbertConvolution g) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  rw [bounded_operator_diagonal hs hg,
    bounded_operator_diagonal hs (meyerCriticalTopJets_sharp hg)]
  have he : deningerMeyerStrongLogMellin (deningerMeyerSourceSharp g) (q.1 : ℂ) =
      star (deningerMeyerStrongLogMellin g (q.1 : ℂ)) := by
    by_cases hr : (q.1 : ℂ).re = 1 / 2
    · rw [deningerMeyerSourceSharp_mellin, ← meyerLineReflect_val,
        meyerLineReflect_eq_self_of_critical q.1 hr]
    · have h1 : deningerMeyerStrongLogMellin g (q.1 : ℂ) = 0 :=
        hg q.1 ⟨0, xiSupportMultiplicity_pos q.1⟩ (Or.inl hr)
      have h2 : deningerMeyerStrongLogMellin (deningerMeyerSourceSharp g) (q.1 : ℂ) = 0 :=
        meyerCriticalTopJets_sharp hg q.1 ⟨0, xiSupportMultiplicity_pos q.1⟩ (Or.inl hr)
      rw [h1, h2, star_zero]
  simp only [RCLike.inner_apply, he]
  change y q * star (star (deningerMeyerStrongLogMellin g (q.1 : ℂ)) * x q) =
    (deningerMeyerStrongLogMellin g (q.1 : ℂ) * y q) * star (x q)
  rw [star_mul, star_star]
  ring

/-- The faithful reserve agrees with trace on the bounded carrier exactly at critical simplicity. -/
theorem meyerBounded_reserve_eq_trace_iff :
    (∀ g : DeningerMeyerStrongLogTarget, MeyerCriticalTopJets g →
      meyerHilbertReserve (0, 0, g) = meyerSourceTrace g g) ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1 := by
  constructor
  · intro he rho hr
    by_contra hne
    have hm : 1 < xiSupportMultiplicity rho := by
      have hp := xiSupportMultiplicity_pos rho
      omega
    let j : DeningerArithmeticJetIndex rho := ⟨xiSupportMultiplicity rho - 1, by omega⟩
    let g := meyerSingleJetSource rho j
    have hg : MeyerCriticalTopJets g := meyerSingleTopSource_criticalTopJets rho hr
    have hv : ∀ sigma : XiDivisorSupport, deningerMeyerStrongLogMellin g (sigma : ℂ) = 0 := by
      intro sigma
      have h := meyerSingleJetSource_jet rho j sigma ⟨0, xiSupportMultiplicity_pos sigma⟩
      have hj : (0 : ℕ) ≠ j.val := by dsimp only [j]; omega
      simpa only [hj, and_false, ↓reduceIte] using h
    have ht : meyerSourceTrace g g = 0 :=
      (meyerSourceTrace_radical_iff_values_zero g).mpr hv g
    have hz : meyerHilbertReserve (0, 0, g) = 0 := (he g hg).trans ht
    exact meyerSingleJetSource_not_boundary rho j
      ((meyerHilbertReserve_eq_zero_iff (0, 0, g)).mp hz)
  · intro hs g hg
    have ha := meyerBounded_sharp_eq_adjoint_of_critical_simple hs hg
    have h := meyerHilbertReserve_sub_defect (0, 0, g)
    rw [meyerScalingSurface_defect, ha, adjoint_adjoint, sub_self] at h
    have hz : hsNormSq (0 : DeningerArithmeticJetHilbert →L[ℂ]
        DeningerArithmeticJetHilbert) = 0 := by
      simp only [hsNormSq, zero_apply, norm_zero, zero_pow (by omega : 2 ≠ 0), tsum_zero]
    rw [hz, zero_div] at h
    exact sub_eq_zero.mp h

/-- The bounded-carrier adjoint criterion does not impose criticality outside this carrier. -/
theorem meyerBounded_sharp_eq_adjoint_iff :
    (∀ g : DeningerMeyerStrongLogTarget, MeyerCriticalTopJets g →
      deningerMeyerHilbertConvolution (deningerMeyerSourceSharp g) =
        adjoint (deningerMeyerHilbertConvolution g)) ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h
    apply meyerBounded_reserve_eq_trace_iff.mp
    intro g hg
    have he := half_hsNormSq_sum_le_re_trace_iff
      (meyerHilbertConvolution_isHilbertSchmidt g)
      (meyerHilbertConvolution_isHilbertSchmidt (deningerMeyerSourceSharp g))
    have hle : meyerHilbertReserve (0, 0, g) ≤ meyerSourceTrace g g := by
      apply he.mpr
      rw [h g hg, adjoint_adjoint]
    have hdef := meyerHilbertReserve_sub_defect (0, 0, g)
    rw [meyerScalingSurface_defect] at hdef
    have hn := hsNormSq_nonneg (deningerMeyerHilbertConvolution g -
      adjoint (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp g)))
    linarith only [hle, hdef, hn]
  · exact fun hs _ hg => meyerBounded_sharp_eq_adjoint_of_critical_simple hs hg

/-- Restriction of the faithful reserve cone to the actual bounded source surface. -/
def meyerBoundedHilbertSourceCone : Set meyerBoundedCycleSubmodule :=
  meyerBoundedSurface.sourceCone (fun x => meyerHilbertReserve x.1)

private theorem bounded_mem_cone (x : meyerBoundedCycleSubmodule) :
    x ∈ meyerBoundedHilbertSourceCone ↔ x.1 ∈ meyerHilbertSourceCone := Iff.rfl

/-- The faithful bounded-carrier cone has Bézout without critical-simplicity assumptions. -/
theorem meyerBoundedHilbertSourceCone_bezout :
    meyerBoundedSurface.BezoutAxiom meyerBoundedHilbertSourceCone := by
  intro x hx y hy
  exact meyerHilbertSourceCone_bezout x.1 ((bounded_mem_cone x).mp hx)
    y.1 ((bounded_mem_cone y).mp hy)

theorem meyerBoundedHilbertSourceCone_ample :
    meyerBoundedSurface.AmpleAxiom meyerBoundedHilbertSourceCone := by
  intro x hx hz y
  exact meyerHilbertSourceCone_ample x.1 ((bounded_mem_cone x).mp hx) hz y.1

private theorem bounded_reserve_even (x : meyerBoundedCycleSubmodule) :
    meyerHilbertReserve (-x).1 = meyerHilbertReserve x.1 := by
  rw [← meyerHilbertReserveBilinear_self, ← meyerHilbertReserveBilinear_self]
  change meyerHilbertReserveBilinear (-x.1) (-x.1) = _
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

private theorem bounded_reserve_fibre (x : meyerBoundedCycleSubmodule) (a b : ℝ) :
    meyerHilbertReserve (x + a • meyerBoundedSurface.H + b • meyerBoundedSurface.V).1 =
      meyerHilbertReserve x.1 := by
  have he : (x + a • meyerBoundedSurface.H + b • meyerBoundedSurface.V).1.2.2 = x.1.2.2 := by
    change x.1.2.2 + a • (0 : DeningerMeyerStrongLogTarget) + b • 0 = x.1.2.2
    simp only [smul_zero, add_zero]
  simp only [meyerHilbertReserve, he]

/-- RR for the restricted faithful cone is exactly equality with its actual trace defect. -/
theorem meyerBoundedHilbertSourceCone_riemannRoch_iff_trace :
    meyerBoundedSurface.RiemannRochAxiom meyerBoundedHilbertSourceCone ↔
      ∀ g : DeningerMeyerStrongLogTarget, MeyerCriticalTopJets g →
        meyerHilbertReserve (0, 0, g) = meyerSourceTrace g g := by
  have he := meyerBoundedSurface.sourceCone_riemannRoch_and_bezout_iff
    (fun x : meyerBoundedCycleSubmodule => meyerHilbertReserve_nonneg x.1)
    bounded_reserve_even bounded_reserve_fibre
  constructor
  · intro h g hg
    have hh := he.mp ⟨h, meyerBoundedHilbertSourceCone_bezout⟩ ⟨(0, 0, g), hg⟩
    rwa [meyerBoundedSurface_defect] at hh
  · intro h
    apply (he.mpr ?_).1
    intro x
    rw [meyerBoundedSurface_defect]
    exact h x.1.2.2 x.2

/-- Critical multiplicity is precisely the remaining RR obstruction on bounded orbits. -/
theorem meyerBoundedHilbertSourceCone_riemannRoch_iff :
    meyerBoundedSurface.RiemannRochAxiom meyerBoundedHilbertSourceCone ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1 :=
  meyerBoundedHilbertSourceCone_riemannRoch_iff_trace.trans meyerBounded_reserve_eq_trace_iff

/-- The faithful and ordinary bounded-carrier cones agree exactly at critical simplicity. -/
theorem meyerBoundedHilbertSourceCone_eq_degree_iff :
    meyerBoundedHilbertSourceCone = meyerBoundedDegreeSourceCone ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h
    apply meyerBoundedHilbertSourceCone_riemannRoch_iff.mp
    rw [h]
    exact meyerBoundedDegreeSourceCone_riemannRoch
  · intro hs
    have he := meyerBounded_reserve_eq_trace_iff.mpr hs
    rw [meyerBoundedDegreeSourceCone_eq_positiveCone]
    unfold meyerBoundedHilbertSourceCone
    exact meyerBoundedSurface.sourceCone_eq_positiveCone_of_exact_source
      (fun x => meyerHilbertReserve_nonneg x.1) (fun x => by
        rw [meyerBoundedSurface_defect]
        exact he x.1.2.2 x.2)

/-- Reserve invariance on this carrier is unconditional, even when its RR criterion is unresolved. -/
theorem meyerBoundedHilbertReserve_flow_invariant
    (g : meyerCriticalTopSourceSubmodule) (c : ℝ) :
    meyerHilbertReserve (0, 0, deningerMeyerStrongLogCenteredFlow c g.1) =
      meyerHilbertReserve (0, 0, g.1) :=
  meyerHilbertReserve_centeredFlow_of_criticalTopJets g.1 g.2 c

/-- A faithful positive linear degree on bounded classes exists exactly at critical simplicity. -/
theorem exists_faithful_positive_bounded_meyer_degree_iff :
    (∃ d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
      ∀ g : DeningerMeyerStrongLogTarget, MeyerCriticalTopJets g →
        g ∉ LinearMap.range deningerMeyerStrongLogSumLM →
          0 < (d (Submodule.Quotient.mk
            (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))).re) ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1 := by
  constructor
  · rintro ⟨d, hd⟩ rho hr
    by_contra hne
    have hm : 1 < xiSupportMultiplicity rho := by
      have hp := xiSupportMultiplicity_pos rho
      omega
    let j : DeningerArithmeticJetIndex rho := ⟨xiSupportMultiplicity rho - 1, by omega⟩
    have hpos := hd (meyerSingleJetSource rho j)
      (meyerSingleTopSource_criticalTopJets rho hr) (meyerSingleJetSource_not_boundary rho j)
    have hb := meyerSingleJetSource_sharp_square_boundary rho j (Or.inr (by
      change xiSupportMultiplicity rho ≤ 2 * (xiSupportMultiplicity rho - 1)
      omega))
    have hq : (Submodule.Quotient.mk
        (deningerMeyerSourceConvolution (meyerSingleJetSource rho j)
          (deningerMeyerSourceSharp (meyerSingleJetSource rho j))) :
          DeningerMeyerStrongLogCohomology) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hb
    rw [hq, map_zero, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  · intro hs
    refine ⟨meyerCohomologyTraceDegree, fun g hg hnonprincipal => ?_⟩
    rw [← meyerSourceTrace_eq_degree_product,
      ← meyerBounded_reserve_eq_trace_iff.mpr hs g hg]
    by_contra hnot
    have hz : meyerHilbertReserve (0, 0, g) = 0 :=
      le_antisymm (le_of_not_gt hnot) (meyerHilbertReserve_nonneg _)
    exact hnonprincipal ((meyerHilbertReserve_eq_zero_iff (0, 0, g)).mp hz)

/-- Exact linear-degree representation on bounded sources detects critical simplicity alone. -/
theorem exists_meyerBoundedHilbertReserve_linear_degree_iff :
    (∃ d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
      ∀ g : DeningerMeyerStrongLogTarget, MeyerCriticalTopJets g →
        meyerHilbertReserve (0, 0, g) =
          (d (Submodule.Quotient.mk
            (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))).re) ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 → xiSupportMultiplicity rho = 1 := by
  constructor
  · rintro ⟨d, hd⟩
    apply exists_faithful_positive_bounded_meyer_degree_iff.mp
    refine ⟨d, fun g hg hnot => ?_⟩
    rw [← hd g hg]
    exact lt_of_le_of_ne (meyerHilbertReserve_nonneg _) (fun he =>
      hnot ((meyerHilbertReserve_eq_zero_iff (0, 0, g)).mp he.symm))
  · intro hs
    refine ⟨meyerCohomologyTraceDegree, fun g hg => ?_⟩
    rw [← meyerSourceTrace_eq_degree_product]
    exact meyerBounded_reserve_eq_trace_iff.mpr hs g hg

/-- Linear representation of the bounded reserve is exactly its restricted RR condition. -/
theorem meyerBoundedHilbertSourceCone_riemannRoch_iff_linear_degree :
    meyerBoundedSurface.RiemannRochAxiom meyerBoundedHilbertSourceCone ↔
      ∃ d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
        ∀ g : DeningerMeyerStrongLogTarget, MeyerCriticalTopJets g →
          meyerHilbertReserve (0, 0, g) =
            (d (Submodule.Quotient.mk
              (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))).re :=
  meyerBoundedHilbertSourceCone_riemannRoch_iff.trans
    exists_meyerBoundedHilbertReserve_linear_degree_iff.symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBounded_sharp_eq_adjoint_of_critical_simple
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBounded_reserve_eq_trace_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBounded_sharp_eq_adjoint_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedHilbertSourceCone_bezout
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedHilbertSourceCone_ample
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedHilbertSourceCone_riemannRoch_iff_trace
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedHilbertSourceCone_riemannRoch_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedHilbertSourceCone_eq_degree_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedHilbertReserve_flow_invariant

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_faithful_positive_bounded_meyer_degree_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_meyerBoundedHilbertReserve_linear_degree_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerBoundedHilbertSourceCone_riemannRoch_iff_linear_degree
