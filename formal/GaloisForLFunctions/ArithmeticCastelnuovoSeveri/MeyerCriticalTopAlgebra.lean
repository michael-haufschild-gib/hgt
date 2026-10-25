import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerBoundedCenteredOrbits
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FaithfulPositiveMeyerDegrees
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveMeyerDegreesCanForgetClasses

/-!
# The algebra carried by bounded centered Meyer orbits

The critical highest-jet carrier is a sharp-stable complex subspace. Products
retain only simple critical values; its multiple critical part annihilates the
whole carrier. Ordinary trace is positive here, while full jet classes can remain
in its radical. Actual finite causal sources make the carrier nontrivial.
-/

noncomputable section
open Complex RHTower ContinuousLinearMap
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Sources with bounded full-Hasse orbit form a complex linear subspace. -/
def meyerCriticalTopSourceSubmodule : Submodule ℂ DeningerMeyerStrongLogTarget where
  carrier := {g | MeyerCriticalTopJets g}
  zero_mem' := by intro rho j _; exact map_zero _
  add_mem' := by
    intro g h hg hh rho j hj
    rw [map_add, hg rho j hj, hh rho j hj, zero_add]
  smul_mem' := by
    intro c g hg rho j hj
    rw [map_smul, hg rho j hj, smul_zero]

theorem meyerLineReflect_eq_self_of_critical (rho : XiDivisorSupport)
    (hr : (rho : ℂ).re = 1 / 2) : meyerLineReflect rho = rho := by
  apply Subtype.ext
  rw [meyerLineReflect_val]
  apply Complex.ext
  · change 1 - (rho : ℂ).re = (rho : ℂ).re
    linarith only [hr]
  · change -(0 - (rho : ℂ).im) = (rho : ℂ).im
    ring

/-- Arithmetic sharp preserves the entire bounded-orbit carrier. -/
theorem meyerCriticalTopJets_sharp {g : DeningerMeyerStrongLogTarget}
    (hg : MeyerCriticalTopJets g) : MeyerCriticalTopJets (deningerMeyerSourceSharp g) := by
  intro rho j hj
  have hi : j.val < xiSupportMultiplicity (meyerLineReflect rho) := by
    rw [meyerLineReflect_multiplicity]
    exact j.isLt
  have hk : (meyerLineReflect rho : ℂ).re ≠ 1 / 2 ∨
      j.val + 1 < xiSupportMultiplicity (meyerLineReflect rho) := by
    rcases hj with hr | hj
    · left
      intro he
      have he' : 1 - (rho : ℂ).re = 1 / 2 := by
        simpa only [meyerLineReflect_val, Complex.star_def, Complex.conj_re,
          Complex.sub_re, Complex.one_re] using he
      exact hr (by linarith only [he'])
    · right
      rwa [meyerLineReflect_multiplicity]
  rw [meyerSourceSharp_jet, hg (meyerLineReflect rho) ⟨j.val, hi⟩ hk, star_zero, mul_zero]

/-- Products of bounded-orbit sources vanish in every off-line or multiple block. -/
theorem meyerCriticalTopJets_product_jet_zero
    {g h : DeningerMeyerStrongLogTarget} (hg : MeyerCriticalTopJets g)
    (hh : MeyerCriticalTopJets h) (rho : XiDivisorSupport)
    (hbad : (rho : ℂ).re ≠ 1 / 2 ∨ 1 < xiSupportMultiplicity rho)
    (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerStrongLogMellinJetLM j.val (rho : ℂ)
      (deningerMeyerSourceConvolution g h) = 0 := by
  have hm : deningerMeyerHasseMoment (deningerMeyerSourceConvolution g h)
      j.val (rho : ℂ) = 0 := by
    rw [deningerMeyerHasseMoment_convolution]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≤ j.val := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hklt : k < xiSupportMultiplicity rho := lt_of_le_of_lt hkj j.isLt
    rcases hbad with hoff | hmultiple
    · rw [deningerMeyerHasseMoment, hg rho ⟨k, hklt⟩ (Or.inl hoff), zero_div, zero_mul]
    · by_cases hlow : k + 1 < xiSupportMultiplicity rho
      · rw [deningerMeyerHasseMoment, hg rho ⟨k, hklt⟩ (Or.inr hlow), zero_div, zero_mul]
      · have hsub : j.val - k = 0 := by have hj := j.isLt; omega
        have hz := hh rho ⟨0, xiSupportMultiplicity_pos rho⟩ (Or.inr hmultiple)
        have hhzero : deningerMeyerHasseMoment h (j.val - k) (rho : ℂ) = 0 := by
          rw [hsub, deningerMeyerHasseMoment, hz, zero_div]
        rw [hhzero, mul_zero]
  have hf : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
  have he := congrArg (fun z : ℂ => z * (j.val.factorial : ℂ)) hm
  simpa only [deningerMeyerHasseMoment, div_mul_cancel₀ _ hf, zero_mul] using he

/-- Convolution preserves bounded centered orbits. -/
theorem meyerCriticalTopJets_convolution {g h : DeningerMeyerStrongLogTarget}
    (hg : MeyerCriticalTopJets g) (hh : MeyerCriticalTopJets h) :
    MeyerCriticalTopJets (deningerMeyerSourceConvolution g h) := by
  intro rho j hj
  apply meyerCriticalTopJets_product_jet_zero hg hh rho _ j
  rcases hj with hoff | hj
  · exact Or.inl hoff
  · exact Or.inr (by omega)

/-- The value-zero part annihilates the entire bounded-orbit algebra in genuine cohomology. -/
theorem meyerCriticalTopJets_value_zero_product_boundary
    {g h : DeningerMeyerStrongLogTarget} (hg : MeyerCriticalTopJets g)
    (hh : MeyerCriticalTopJets h)
    (hz : ∀ rho : XiDivisorSupport, deningerMeyerStrongLogMellin g (rho : ℂ) = 0) :
    deningerMeyerSourceConvolution g h ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
  apply (meyerSource_boundary_iff_jets_zero _).mpr
  intro rho j
  by_cases hm : 1 < xiSupportMultiplicity rho
  · exact meyerCriticalTopJets_product_jet_zero hg hh rho (Or.inr hm) j
  · have hj : j.val = 0 := by
      have hp := xiSupportMultiplicity_pos rho
      have hlt := j.isLt
      omega
    rw [hj]
    change deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g h) (rho : ℂ) = 0
    rw [deningerMeyerSourceConvolution_mellin, hz rho, zero_mul]

/-- Ordinary trace is nonnegative on the bounded-orbit carrier, without global criticality. -/
theorem meyerCriticalTopJets_trace_nonneg {g : DeningerMeyerStrongLogTarget}
    (hg : MeyerCriticalTopJets g) : 0 ≤ meyerSourceTrace g g := by
  rw [meyerSourceTrace, ← deningerMeyerHilbertConvolution_mul,
    deningerMeyerHilbertConvolution_opTrace,
    Complex.re_tsum (deningerMeyerHilbertConvolution_summable_diagonal
      (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))]
  apply tsum_nonneg
  intro q
  rw [deningerMeyerSourceConvolution_mellin, deningerMeyerSourceSharp_mellin]
  by_cases hr : (q.1 : ℂ).re = 1 / 2
  · have href : star (1 - (q.1 : ℂ)) = (q.1 : ℂ) := by
      rw [← meyerLineReflect_val, meyerLineReflect_eq_self_of_critical q.1 hr]
    rw [href]
    change 0 ≤ (deningerMeyerStrongLogMellin g (q.1 : ℂ) *
      conj (deningerMeyerStrongLogMellin g (q.1 : ℂ))).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  · have hz := hg q.1 ⟨0, xiSupportMultiplicity_pos q.1⟩ (Or.inl hr)
    change deningerMeyerStrongLogMellin g (q.1 : ℂ) = 0 at hz
    simp only [hz, zero_mul, Complex.zero_re, le_refl]

/-- Every critical point has an actual nonprincipal source in the bounded-orbit carrier. -/
theorem meyerSingleTopSource_criticalTopJets (rho : XiDivisorSupport)
    (hr : (rho : ℂ).re = 1 / 2) :
    MeyerCriticalTopJets (meyerSingleJetSource rho
      ⟨xiSupportMultiplicity rho - 1, by have hp := xiSupportMultiplicity_pos rho; omega⟩) := by
  intro sigma j hj
  rw [meyerSingleJetSource_jet, if_neg]
  rintro ⟨hs, he⟩
  rcases hj with hoff | hj
  · exact hoff ((congrArg (fun q : XiDivisorSupport => (q : ℂ).re) hs).trans hr)
  · have hp := xiSupportMultiplicity_pos rho
    have hj' : j.val + 1 < xiSupportMultiplicity rho := by simpa only [hs] using hj
    omega

/-- Hardy's critical point makes the bounded-orbit carrier nontrivial in genuine cohomology. -/
theorem exists_nonprincipal_meyer_bounded_orbit :
    ∃ g : DeningerMeyerStrongLogTarget,
      MeyerHilbertOrbitIsometric g ∧ g ∉ LinearMap.range deningerMeyerStrongLogSumLM := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_eq_half
  let j : DeningerArithmeticJetIndex q.1 :=
    ⟨xiSupportMultiplicity q.1 - 1, by have hp := xiSupportMultiplicity_pos q.1; omega⟩
  refine ⟨meyerSingleJetSource q.1 j, ?_, meyerSingleJetSource_not_boundary q.1 j⟩
  exact meyerHilbertOrbitIsometric_of_criticalTopJets
    (meyerSingleTopSource_criticalTopJets q.1 hq)

/-- A multiple critical highest jet has principal sharp square despite its faithful nonzero class. -/
theorem meyerMultipleCriticalTopSource_sharp_square_boundary
    (rho : XiDivisorSupport) (hr : (rho : ℂ).re = 1 / 2)
    (hm : 1 < xiSupportMultiplicity rho) :
    ∃ g : DeningerMeyerStrongLogTarget,
      MeyerHilbertOrbitIsometric g ∧ g ∉ LinearMap.range deningerMeyerStrongLogSumLM ∧
      deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g) ∈
        LinearMap.range deningerMeyerStrongLogSumLM := by
  let j : DeningerArithmeticJetIndex rho := ⟨xiSupportMultiplicity rho - 1, by omega⟩
  refine ⟨meyerSingleJetSource rho j,
    meyerHilbertOrbitIsometric_of_criticalTopJets (meyerSingleTopSource_criticalTopJets rho hr),
    meyerSingleJetSource_not_boundary rho j,
    meyerSingleJetSource_sharp_square_boundary rho j (Or.inr ?_)⟩
  change xiSupportMultiplicity rho ≤ 2 * (xiSupportMultiplicity rho - 1)
  omega


/-- The trace radical inside the bounded-orbit carrier is exactly its value-zero part. -/
theorem meyerCriticalTopJets_trace_radical_iff
    (g : DeningerMeyerStrongLogTarget) (hg : MeyerCriticalTopJets g) :
    (∀ h : DeningerMeyerStrongLogTarget, MeyerCriticalTopJets h → meyerSourceTrace g h = 0) ↔
      ∀ rho : XiDivisorSupport, deningerMeyerStrongLogMellin g (rho : ℂ) = 0 := by
  constructor
  · intro hkernel rho
    by_cases hr : (rho : ℂ).re = 1 / 2
    · by_cases hm : 1 < xiSupportMultiplicity rho
      · exact hg rho ⟨0, xiSupportMultiplicity_pos rho⟩ (Or.inr hm)
      · have hs : xiSupportMultiplicity rho = 1 := by
          have hp := xiSupportMultiplicity_pos rho
          omega
        have hp : MeyerCriticalTopJets (meyerPointSource rho) := by
          simpa only [meyerPointSource, hs, Nat.sub_self] using
            meyerSingleTopSource_criticalTopJets rho hr
        let z := (xiSupportMultiplicity rho : ℂ) * deningerMeyerStrongLogMellin g (rho : ℂ)
        have hp' : MeyerCriticalTopJets (conj z • meyerPointSource rho) :=
          meyerCriticalTopSourceSubmodule.smul_mem (conj z) hp
        have h := hkernel (deningerMeyerSourceSharp (conj z • meyerPointSource rho))
          (meyerCriticalTopJets_sharp hp')
        have hinv (u : DeningerMeyerStrongLogTarget) :
            deningerMeyerSourceSharp (deningerMeyerSourceSharp u) = u := by
          simp only [deningerMeyerSourceSharp, deningerMeyerStrongLogConj_J,
            deningerMeyerStrongLogConj_sq, deningerMeyerStrongLogJ_sq]
        rw [meyerSourceTrace, hinv, meyerPointSource_product_trace] at h
        change (conj z * z).re = 0 at h
        rw [mul_comm, Complex.mul_conj, Complex.ofReal_re] at h
        have hz0 : z = 0 := Complex.normSq_eq_zero.mp h
        have hmult : (xiSupportMultiplicity rho : ℂ) ≠ 0 := by
          exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
        exact (mul_eq_zero.mp hz0).resolve_left hmult
    · exact hg rho ⟨0, xiSupportMultiplicity_pos rho⟩ (Or.inl hr)
  · intro hz h _
    exact (meyerSourceTrace_radical_iff_values_zero g).mpr hz h

/-- Trace-null bounded-orbit classes annihilate every bounded-orbit class. -/
theorem meyerCriticalTopJets_trace_radical_annihilates
    (g : DeningerMeyerStrongLogTarget) (hg : MeyerCriticalTopJets g)
    (hz : ∀ h : DeningerMeyerStrongLogTarget, MeyerCriticalTopJets h → meyerSourceTrace g h = 0)
    (h : DeningerMeyerStrongLogTarget) (hh : MeyerCriticalTopJets h) :
    deningerMeyerSourceConvolution g h ∈ LinearMap.range deningerMeyerStrongLogSumLM :=
  meyerCriticalTopJets_value_zero_product_boundary hg hh
    ((meyerCriticalTopJets_trace_radical_iff g hg).mp hz)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerLineReflect_eq_self_of_critical
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerCriticalTopJets_sharp
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerCriticalTopJets_product_jet_zero
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerCriticalTopJets_convolution
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerCriticalTopJets_value_zero_product_boundary
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerCriticalTopJets_trace_nonneg
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerSingleTopSource_criticalTopJets
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_nonprincipal_meyer_bounded_orbit
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerMultipleCriticalTopSource_sharp_square_boundary
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerCriticalTopJets_trace_radical_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerCriticalTopJets_trace_radical_annihilates
