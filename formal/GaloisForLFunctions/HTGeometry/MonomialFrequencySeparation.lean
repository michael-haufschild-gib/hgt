import GaloisForLFunctions.HTGeometry.InfiniteTorusEquidistribution

/-!
# Distinct monomials have distinct frequencies

A monomial in the characters of a frequency family has one frequency: the sum of the family's
frequencies with the monomial's multiplicities.  If the frequencies are rationally independent,
distinct monomials have distinct frequencies, because their difference is an integer character whose
detuning cannot vanish.

This is the combinatorial half of a hypertranscendence argument: it is what lets a single Fourier
coefficient of a differential relation see a single monomial.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- The frequency of a monomial in the characters: the frequencies summed with multiplicity. -/
def monomialFrequency (omega : ι → ℝ) (s : ι →₀ ℕ) : ℝ :=
  ∑ i ∈ s.support, (s i : ℝ) * omega i

theorem monomialFrequency_eq_sum (omega : ι → ℝ) (s : ι →₀ ℕ) {u : Finset ι}
    (hu : s.support ⊆ u) : monomialFrequency omega s = ∑ i ∈ u, (s i : ℝ) * omega i := by
  refine Finset.sum_subset hu fun i _ hi => ?_
  rw [Finsupp.notMem_support_iff.mp hi]
  simp

theorem characterDetuning_eq_sum (omega : ι → ℝ) (n : ι →₀ ℤ) {u : Finset ι}
    (hu : n.support ⊆ u) : characterDetuning n omega = ∑ i ∈ u, (n i : ℝ) * omega i := by
  refine Finset.sum_subset hu fun i _ hi => ?_
  rw [Finsupp.notMem_support_iff.mp hi]
  simp

/-- **Distinct monomials have distinct frequencies.** -/
theorem monomialFrequency_injective [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) :
    Function.Injective (monomialFrequency omega) := by
  classical
  intro s t hst
  set n : ι →₀ ℤ :=
    Finsupp.mapRange (fun k : ℕ => (k : ℤ)) rfl s - Finsupp.mapRange (fun k : ℕ => (k : ℤ)) rfl t
    with hn
  have hcoeff : ∀ i, n i = (s i : ℤ) - (t i : ℤ) := by
    intro i
    simp [hn]
  set u : Finset ι := n.support ∪ (s.support ∪ t.support) with hu
  have hnu : n.support ⊆ u := Finset.subset_union_left
  have hsu : s.support ⊆ u := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_union_left _ hi)
  have htu : t.support ⊆ u := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_union_right _ hi)
  have hdet : characterDetuning n omega = 0 := by
    rw [characterDetuning_eq_sum omega n hnu]
    have hterm : ∀ i ∈ u, ((n i : ℤ) : ℝ) * omega i
        = (s i : ℝ) * omega i - (t i : ℝ) * omega i := by
      intro i _
      rw [hcoeff i]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
      ← monomialFrequency_eq_sum omega s hsu, ← monomialFrequency_eq_sum omega t htu, hst,
      sub_self]
  have hzero : n = 0 := (characterDetuning_eq_zero_iff h n).mp hdet
  ext i
  have hi := congrArg (fun f : ι →₀ ℤ => f i) hzero
  simp only [hcoeff i, Finsupp.coe_zero, Pi.zero_apply] at hi
  omega

end

end GaloisForLFunctions.HTGeometry
