import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerSourceIntersectionSurface

/-!
# Faithful positive degrees and sharp-square roots of Poisson boundaries

The arithmetic sharp exchanges reflected Xi jet blocks. An off-line value block or a
higher jet supplies a nonprincipal source with principal sharp square. Consequently a
faithful positive linear degree on the genuine quotient exists exactly under RH and
simplicity. Ordinary trace positivity alone does not impose the second condition.
-/

noncomputable section
open Complex Zeta23 RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Critical-line reflection preserves the complete Xi multiplicity. -/
theorem meyerLineReflect_multiplicity (rho : XiDivisorSupport) :
    xiSupportMultiplicity (meyerLineReflect rho) = xiSupportMultiplicity rho := by
  unfold xiSupportMultiplicity
  change Int.toNat ((MeromorphicOn.divisor xi Set.univ) (1 - conj (rho : ℂ))) = _
  rw [xi_divisor_one_sub, xi_divisor_conj]

/-- The arithmetic sharp reflects every raw Mellin jet with its exact parity sign. -/
theorem meyerSourceSharp_jet (g : DeningerMeyerStrongLogTarget)
    (k : ℕ) (rho : XiDivisorSupport) :
    deningerMeyerStrongLogMellinJetLM k (rho : ℂ) (deningerMeyerSourceSharp g) =
      (-1 : ℂ) ^ k * star
        (deningerMeyerStrongLogMellinJetLM k (meyerLineReflect rho : ℂ) g) := by
  rw [deningerMeyerSourceSharp, deningerMeyerStrongLogMellinJetLM_J,
    deningerMeyerStrongLogMellinJetLM_conj, meyerLineReflect_val]

/-- A prescribed nonzero Xi jet is an actual nonprincipal source. -/
theorem meyerSingleJetSource_not_boundary (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    meyerSingleJetSource rho j ∉ LinearMap.range deningerMeyerStrongLogSumLM := by
  intro hg
  have hz := (meyerSource_boundary_iff_jets_zero _).mp hg rho j
  rw [meyerSingleJetSource_jet, if_pos ⟨rfl, rfl⟩] at hz
  exact one_ne_zero hz

/-- Disjoint reflected blocks and sufficiently high jets have principal sharp square. -/
theorem meyerSingleJetSource_sharp_square_boundary
    (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho)
    (h : meyerLineReflect rho ≠ rho ∨ xiSupportMultiplicity rho ≤ 2 * j.val) :
    deningerMeyerSourceConvolution (meyerSingleJetSource rho j)
      (deningerMeyerSourceSharp (meyerSingleJetSource rho j)) ∈
        LinearMap.range deningerMeyerStrongLogSumLM := by
  apply (meyerSource_boundary_iff_jets_zero _).mpr
  intro sigma i
  have hz : deningerMeyerHasseMoment
      (deningerMeyerSourceConvolution (meyerSingleJetSource rho j)
        (deningerMeyerSourceSharp (meyerSingleJetSource rho j))) i.val (sigma : ℂ) = 0 := by
    rw [deningerMeyerHasseMoment_convolution]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≤ i.val := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hklt : k < xiSupportMultiplicity sigma := lt_of_le_of_lt hk' i.isLt
    by_cases hfirst : sigma = rho ∧ k = j.val
    · obtain ⟨rfl, hkval⟩ := hfirst
      have hsub : i.val - k < xiSupportMultiplicity (meyerLineReflect rho) := by
        rw [meyerLineReflect_multiplicity]
        exact lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
      have hsecond : ¬ (meyerLineReflect rho = rho ∧ i.val - k = j.val) := by
        rintro ⟨he, hj⟩
        rcases h with hne | hm
        · exact hne he
        · have hi := i.isLt
          omega
      have hv := meyerSingleJetSource_jet rho j (meyerLineReflect rho) ⟨i.val - k, hsub⟩
      rw [if_neg hsecond] at hv
      simp only [deningerMeyerHasseMoment, meyerSourceSharp_jet, hv, star_zero,
        mul_zero, zero_div]
    · have hv := meyerSingleJetSource_jet rho j sigma ⟨k, hklt⟩
      rw [if_neg hfirst] at hv
      simp only [deningerMeyerHasseMoment, hv, zero_div, zero_mul]
  have hf : (i.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
  change deningerMeyerStrongLogMellinJetLM i.val (sigma : ℂ)
    (deningerMeyerSourceConvolution (meyerSingleJetSource rho j)
      (deningerMeyerSourceSharp (meyerSingleJetSource rho j))) /
        (i.val.factorial : ℂ) = 0 at hz
  have he := congrArg (fun z : ℂ => z * (i.val.factorial : ℂ)) hz
  rw [div_mul_cancel₀ _ hf, zero_mul] at he
  exact he

/-- The exact local obstruction consists of reflection away from the point or enough jet order. -/
theorem meyerSingleJetSource_sharp_square_boundary_iff
    (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerSourceConvolution (meyerSingleJetSource rho j)
      (deningerMeyerSourceSharp (meyerSingleJetSource rho j)) ∈
        LinearMap.range deningerMeyerStrongLogSumLM ↔
      meyerLineReflect rho ≠ rho ∨ xiSupportMultiplicity rho ≤ 2 * j.val := by
  constructor
  · intro hb
    by_contra h
    have hfix : meyerLineReflect rho = rho := by
      by_contra hne
      exact h (Or.inl hne)
    have hlow : 2 * j.val < xiSupportMultiplicity rho := by
      by_contra hnot
      exact h (Or.inr (Nat.le_of_not_gt hnot))
    have hz := (meyerSource_boundary_iff_jets_zero _).mp hb rho ⟨2 * j.val, hlow⟩
    have hmoment : deningerMeyerHasseMoment
        (deningerMeyerSourceConvolution (meyerSingleJetSource rho j)
          (deningerMeyerSourceSharp (meyerSingleJetSource rho j))) (2 * j.val) (rho : ℂ) = 0 := by
      change deningerMeyerStrongLogMellinJetLM (2 * j.val) (rho : ℂ) _ /
        ((2 * j.val).factorial : ℂ) = 0
      rw [hz, zero_div]
    have hjet := meyerSingleJetSource_jet rho j rho j
    rw [if_pos ⟨rfl, rfl⟩] at hjet
    have hsum : deningerMeyerHasseMoment
        (deningerMeyerSourceConvolution (meyerSingleJetSource rho j)
          (deningerMeyerSourceSharp (meyerSingleJetSource rho j))) (2 * j.val) (rho : ℂ) =
        (1 / (j.val.factorial : ℂ)) * ((-1 : ℂ) ^ j.val / (j.val.factorial : ℂ)) := by
      rw [deningerMeyerHasseMoment_convolution, Finset.sum_eq_single j.val]
      · have hj : 2 * j.val - j.val = j.val := by omega
        simp only [hj, deningerMeyerHasseMoment, meyerSourceSharp_jet, hfix,
          hjet, star_one, mul_one]
      · intro k hk hne
        have hklt : k < xiSupportMultiplicity rho := by
          have hk' := Finset.mem_range.mp hk
          omega
        have hv := meyerSingleJetSource_jet rho j rho ⟨k, hklt⟩
        rw [if_neg (fun he => hne he.2)] at hv
        simp only [deningerMeyerHasseMoment, hv, zero_div, zero_mul]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
    have hf : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
    have hn : (1 / (j.val.factorial : ℂ)) *
        ((-1 : ℂ) ^ j.val / (j.val.factorial : ℂ)) ≠ 0 :=
      mul_ne_zero (div_ne_zero one_ne_zero hf)
        (div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hf)
    exact hn (hsum.symm.trans hmoment)
  · exact meyerSingleJetSource_sharp_square_boundary rho j

/-- Every off-line zero gives an actual nonprincipal source whose sharp square is principal. -/
theorem exists_meyer_principal_sharp_square_of_off_line
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ∃ g : DeningerMeyerStrongLogTarget,
      g ∉ LinearMap.range deningerMeyerStrongLogSumLM ∧
      deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g) ∈
        LinearMap.range deningerMeyerStrongLogSumLM := by
  have hne : meyerLineReflect rho ≠ rho := by
    intro he
    have hr := congrArg (fun q : XiDivisorSupport => (q : ℂ).re) he
    change 1 - (rho : ℂ).re = (rho : ℂ).re at hr
    exact hoff (by linarith only [hr])
  let j : DeningerArithmeticJetIndex rho := ⟨0, xiSupportMultiplicity_pos rho⟩
  exact ⟨meyerSingleJetSource rho j, meyerSingleJetSource_not_boundary rho j,
    meyerSingleJetSource_sharp_square_boundary rho j (Or.inl hne)⟩

/-- Every multiple zero gives the same obstruction, whether or not it is critical. -/
theorem exists_meyer_principal_sharp_square_of_multiple
    (rho : XiDivisorSupport) (hm : 1 < xiSupportMultiplicity rho) :
    ∃ g : DeningerMeyerStrongLogTarget,
      g ∉ LinearMap.range deningerMeyerStrongLogSumLM ∧
      deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g) ∈
        LinearMap.range deningerMeyerStrongLogSumLM := by
  let j : DeningerArithmeticJetIndex rho := ⟨xiSupportMultiplicity rho - 1, by omega⟩
  refine ⟨meyerSingleJetSource rho j, meyerSingleJetSource_not_boundary rho j,
    meyerSingleJetSource_sharp_square_boundary rho j (Or.inr ?_)⟩
  change xiSupportMultiplicity rho ≤ 2 * (xiSupportMultiplicity rho - 1)
  omega

/-- Sharp-square-root closure of the actual Poisson ideal is precisely RH plus simplicity. -/
theorem meyerSource_sharp_square_root_boundary_iff :
    (∀ g : DeningerMeyerStrongLogTarget,
      deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g) ∈
        LinearMap.range deningerMeyerStrongLogSumLM →
      g ∈ LinearMap.range deningerMeyerStrongLogSumLM) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h
    have hline (rho : XiDivisorSupport) : (rho : ℂ).re = 1 / 2 := by
      by_contra hoff
      obtain ⟨g, hnot, hsquare⟩ := exists_meyer_principal_sharp_square_of_off_line rho hoff
      exact hnot (h g hsquare)
    refine ⟨?_, ?_⟩
    · rw [rh_iff_xi_ne_zero_right]
      intro z hz hzero
      exact (ne_of_gt (mem_rightHalf.mp hz))
        (hline ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩)
    · intro rho
      by_contra hne
      have hm : 1 < xiSupportMultiplicity rho := by
        have hp := xiSupportMultiplicity_pos rho
        omega
      obtain ⟨g, hnot, hsquare⟩ := exists_meyer_principal_sharp_square_of_multiple rho hm
      exact hnot (h g hsquare)
  · rintro ⟨hRH, hs⟩ g hg
    apply (meyerSourceTrace_positive_faithful_iff.mpr ⟨hRH, hs⟩ g).2.mp
    rw [meyerSourceTrace_eq_degree_product]
    have hz : (Submodule.Quotient.mk
        (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)) :
          DeningerMeyerStrongLogCohomology) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)).mpr hg
    rw [hz, map_zero, Complex.zero_re]

/-- Changing the linear degree cannot avoid RH or simplicity while preserving faithfulness. -/
theorem exists_faithful_positive_meyer_degree_iff :
    (∃ d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
      ∀ g : DeningerMeyerStrongLogTarget,
        g ∉ LinearMap.range deningerMeyerStrongLogSumLM →
        0 < (d (Submodule.Quotient.mk
          (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))).re) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · rintro ⟨d, hd⟩
    apply meyerSource_sharp_square_root_boundary_iff.mp
    intro g hg
    by_contra hnot
    have hp := hd g hnot
    have hz : (Submodule.Quotient.mk
        (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)) :
          DeningerMeyerStrongLogCohomology) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)).mpr hg
    rw [hz, map_zero, Complex.zero_re] at hp
    exact lt_irrefl _ hp
  · intro h
    refine ⟨meyerCohomologyTraceDegree, ?_⟩
    intro g hnot
    rw [← meyerSourceTrace_eq_degree_product]
    have ht := meyerSourceTrace_positive_faithful_iff.mpr h g
    exact lt_of_le_of_ne ht.1 (fun he => hnot (ht.2.mp he.symm))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerSourceSharp_jet
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerSingleJetSource_sharp_square_boundary_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_meyer_principal_sharp_square_of_off_line
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_meyer_principal_sharp_square_of_multiple
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerSource_sharp_square_root_boundary_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_faithful_positive_meyer_degree_iff
