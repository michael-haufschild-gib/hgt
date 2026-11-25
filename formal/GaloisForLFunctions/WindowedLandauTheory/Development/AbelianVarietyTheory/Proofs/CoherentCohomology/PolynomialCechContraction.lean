import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PolynomialLocalizationCoefficients
import GaloisForLFunctions.HTGeometry.LaurentCechVanishing

/-! The coefficientwise Čech contraction leaves only the finitely many monomials
with every exponent negative. -/

noncomputable section

open HTGeometry GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory

variable {ι R : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [LinearOrder ι]

abbrev polynomialCechDatum (R : Type) [CommRing R] (n : ℤ) :=
  homLocDatum (ι := ι) (polyGrading ι R) n

def polynomialCechCoefficients {n : ℤ} (c : (polynomialCechDatum (ι := ι) R n).Cochain)
    (s : Finset ι) : (ι → ℤ) →₀ R :=
  localizedCoefficients R s n (c s)

theorem polynomialCechCoefficients_d {n : ℤ} (c : (polynomialCechDatum (ι := ι) R n).Cochain)
    (s : Finset ι) :
    polynomialCechCoefficients ((polynomialCechDatum (ι := ι) R n).d c) s =
      monoCechD (polynomialCechCoefficients c) s := by
  rw [polynomialCechCoefficients, FinsetCechDatum.d, map_sum, monoCechD]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  change (cechSign s i : ℤ) • localizedCoefficients R s n
    (homLocRes (polyGrading ι R) (Finset.erase_subset i s) n (c (s.erase i))) = _
  rw [localizedCoefficients_restrict]
  have hsign : ((cechSign s i : ℤ) : R) = cechSign s i := by simp [cechSign]
  rw [← hsign, Int.cast_smul_eq_zsmul]
  rfl

/-- All cocycles with zero fully negative coefficients are boundaries in the augmented complex. -/
theorem polynomialCech_exists_primitive [Nonempty ι] {n : ℤ} {p : ℕ}
    {c : (polynomialCechDatum (ι := ι) R n).Cochain}
    (hc : (polynomialCechDatum (ι := ι) R n).IsDeg c p)
    (hδ : (polynomialCechDatum (ι := ι) R n).d c = 0)
    (hfull : ∀ a : ι → ℤ, (∀ i, a i < 0) → polynomialCechCoefficients c Finset.univ a = 0) :
    ∃ b : (polynomialCechDatum (ι := ι) R n).Cochain,
      (∀ s, s.card ≠ p → b s = 0) ∧ (polynomialCechDatum (ι := ι) R n).d b = c := by
  classical
  let neg (a : ι → ℤ) := Finset.univ.filter fun i => a i < 0
  have hneg (s : Finset ι) (a : ι → ℤ) (ha : a ∈ (polynomialCechCoefficients c s).support) :
      neg a ⊆ s := by
    intro i hi
    by_contra h
    exact not_lt_of_ge (localizedCoefficients_support s n (c s) a ha).2 i h
      (Finset.mem_filter.1 hi).2
  have hproper (s : Finset ι) (a : ι → ℤ) (ha : a ∈ (polynomialCechCoefficients c s).support) :
      neg a ≠ Finset.univ := by
    intro e
    have hs := hneg s a ha
    rw [e, Finset.univ_subset_iff] at hs
    subst s
    apply (Finsupp.mem_support_iff.1 ha)
    exact hfull a fun i => (Finset.mem_filter.1 (e.symm ▸ Finset.mem_univ i)).2
  have hdegree (s : Finset ι) (hs : s.card ≠ p + 1) : polynomialCechCoefficients c s = 0 := by
    rw [polynomialCechCoefficients, hc s hs, map_zero]
  have hclosed : monoCechD (polynomialCechCoefficients c) = 0 := by
    funext s
    rw [← polynomialCechCoefficients_d, hδ]
    exact map_zero (localizedCoefficients R s n)
  obtain ⟨η, hηdeg, hηneg, hηsupport, hηd⟩ :=
    monoCech_vanishing (supp := neg) hdegree hneg hclosed hproper
  have hlift (s : Finset ι) : η s ∈ LinearMap.range (localizedCoefficients R s n) := by
    rw [localizedCoefficients_range, Finsupp.mem_supported]
    intro a ha
    obtain ⟨t, ht⟩ := hηsupport s a ha
    refine ⟨(localizedCoefficients_support t n (c t) a ht).1, fun i hi => ?_⟩
    by_contra h
    exact hi (hηneg s a ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_not_ge h⟩))
  choose b hb using hlift
  refine ⟨b, fun s hs => localizedCoefficients_injective s n ((hb s).trans ?_),
    funext fun s => localizedCoefficients_injective s n ?_⟩
  · rw [hηdeg s hs, map_zero]
  · change polynomialCechCoefficients ((polynomialCechDatum (ι := ι) R n).d b) s =
      polynomialCechCoefficients c s
    rw [polynomialCechCoefficients_d, show polynomialCechCoefficients b = η from funext hb, hηd]

theorem polynomialCech_boundary_full_negative {n : ℤ}
    (c : (polynomialCechDatum (ι := ι) R n).Cochain) (a : ι → ℤ) (ha : ∀ i, a i < 0) :
    polynomialCechCoefficients ((polynomialCechDatum (ι := ι) R n).d c) Finset.univ a = 0 := by
  classical
  rw [polynomialCechCoefficients_d, monoCechD, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have e : polynomialCechCoefficients c (Finset.univ.erase i) a = 0 := by
    by_contra h
    have hmem := localizedCoefficients_support (Finset.univ.erase i) n (c (Finset.univ.erase i))
      a (Finsupp.mem_support_iff.2 h)
    exact (not_lt_of_ge (hmem.2 i (Finset.notMem_erase i _))) (ha i)
  rw [Finsupp.smul_apply, e, smul_zero]

theorem polynomialCech_exactAt_of_nonneg [Nonempty ι] {n : ℤ} (hn : 0 ≤ n) (p : ℕ) :
    (polynomialCechDatum (ι := ι) R n).ExactAt p := by
  classical
  intro c hc hδ
  refine polynomialCech_exists_primitive hc hδ fun a ha => ?_
  by_contra h
  have hsum := (localizedCoefficients_support Finset.univ n (c Finset.univ)
    a (Finsupp.mem_support_iff.2 h)).1
  obtain ⟨i⟩ := ‹Nonempty ι›
  have he := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
  have hrest : ∑ j ∈ Finset.univ.erase i, a j ≤ 0 := Finset.sum_nonpos fun j _ => (ha j).le
  rw [hsum] at he
  have hi := ha i
  omega

end GlobalTheory
