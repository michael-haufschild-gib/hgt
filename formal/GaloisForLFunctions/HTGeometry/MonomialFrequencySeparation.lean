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

/-! ## The multiset a tuple uses -/

theorem monomialFrequency_zero (omega : ι → ℝ) : monomialFrequency omega 0 = 0 := by
  rw [monomialFrequency]
  simp

theorem monomialFrequency_add [DecidableEq ι] (omega : ι → ℝ) (s t : ι →₀ ℕ) :
    monomialFrequency omega (s + t)
      = monomialFrequency omega s + monomialFrequency omega t := by
  classical
  set u : Finset ι := (s + t).support ∪ (s.support ∪ t.support) with hu
  have hst : (s + t).support ⊆ u := Finset.subset_union_left
  have hs : s.support ⊆ u := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_union_left _ hi)
  have ht : t.support ⊆ u := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_union_right _ hi)
  rw [monomialFrequency_eq_sum omega (s + t) hst, monomialFrequency_eq_sum omega s hs,
    monomialFrequency_eq_sum omega t ht, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hval : ((s + t) i : ℝ) = (s i : ℝ) + (t i : ℝ) := by
    push_cast [Finsupp.add_apply]
    ring
  rw [hval]
  ring

/-- The frequency of a monomial, as an additive map. -/
def monomialFrequencyHom [DecidableEq ι] (omega : ι → ℝ) : (ι →₀ ℕ) →+ ℝ where
  toFun := monomialFrequency omega
  map_zero' := monomialFrequency_zero omega
  map_add' := monomialFrequency_add omega

theorem monomialFrequency_single [DecidableEq ι] (omega : ι → ℝ) (i : ι) :
    monomialFrequency omega (Finsupp.single i 1) = omega i := by
  classical
  rw [monomialFrequency, show (Finsupp.single i (1 : ℕ)).support = {i} from by simp]
  simp

/-- The multiset of indices a tuple uses. -/
def tupleCount [DecidableEq ι] {m : ℕ} (n : Fin m → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (n j) 1

/-- **A tuple's frequency is the frequency of the multiset it uses.** -/
theorem monomialFrequency_tupleCount [DecidableEq ι] (omega : ι → ℝ) {m : ℕ} (n : Fin m → ι) :
    monomialFrequency omega (tupleCount n) = ∑ j, omega (n j) := by
  classical
  have hhom : monomialFrequency omega (tupleCount n)
      = ∑ j, monomialFrequency omega (Finsupp.single (n j) 1) := by
    rw [tupleCount]
    exact map_sum (monomialFrequencyHom omega) _ _
  rw [hhom]
  exact Finset.sum_congr rfl fun j _ => monomialFrequency_single omega (n j)

/-- **Tuples with the same frequency use the same multiset of indices.** -/
theorem tupleCount_eq_of_frequency_eq [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) {m : ℕ} {n n' : Fin m → ι}
    (hfreq : ∑ j, omega (n j) = ∑ j, omega (n' j)) : tupleCount n = tupleCount n' := by
  refine monomialFrequency_injective h ?_
  rw [monomialFrequency_tupleCount, monomialFrequency_tupleCount]
  exact hfreq

/-- **Rationally independent frequencies are pairwise distinct.** -/
theorem injective_of_rationallyIndependentSequence [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) : Function.Injective omega := by
  classical
  intro i j hij
  by_contra hne
  set n : ι →₀ ℤ := Finsupp.single i 1 - Finsupp.single j 1 with hn
  have hcoeff : ∀ k, n k = (if k = i then (1 : ℤ) else 0) - (if k = j then (1 : ℤ) else 0) := by
    intro k
    simp [hn, Finsupp.single_apply, eq_comm]
  have hsupp : n.support ⊆ ({i, j} : Finset ι) := by
    intro k hk
    by_contra hkij
    have hki : k ≠ i := fun hcon => hkij (by simp [hcon])
    have hkj : k ≠ j := fun hcon => hkij (by simp [hcon])
    have hzero : n k = 0 := by
      rw [hcoeff k, if_neg hki, if_neg hkj]
      ring
    exact (Finsupp.mem_support_iff.mp hk) hzero
  have hdet : characterDetuning n omega = 0 := by
    rw [characterDetuning_eq_sum omega n hsupp, Finset.sum_pair hne]
    rw [hcoeff i, hcoeff j, if_pos rfl, if_neg (Ne.symm hne), if_pos rfl,
      if_neg hne, hij]
    push_cast
    ring
  have hzero : n = 0 := (characterDetuning_eq_zero_iff h n).mp hdet
  have hi : n i = 0 := by rw [hzero]; rfl
  rw [hcoeff i, if_pos rfl, if_neg hne] at hi
  norm_num at hi

/-- **The multiset a tuple uses determines its length.**  Testing against the constant frequency
family reads the length off the multiset. -/
theorem card_eq_of_tupleCount_eq [DecidableEq ι] {M M' : ℕ} {n : Fin M → ι} {n' : Fin M' → ι}
    (h : tupleCount n = tupleCount n') : M = M' := by
  have h1 := monomialFrequency_tupleCount (fun _ : ι => (1 : ℝ)) n
  have h2 := monomialFrequency_tupleCount (fun _ : ι => (1 : ℝ)) n'
  rw [h, h2] at h1
  have hM : ((M' : ℕ) : ℝ) = ((M : ℕ) : ℝ) := by
    simpa using h1
  exact_mod_cast hM.symm

/-- **Tuples of different lengths have different frequencies.** -/
theorem card_eq_of_frequency_eq [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) {M M' : ℕ} {n : Fin M → ι} {n' : Fin M' → ι}
    (hfreq : ∑ j, omega (n j) = ∑ j, omega (n' j)) : M = M' := by
  refine card_eq_of_tupleCount_eq (n := n) (n' := n') ?_
  refine monomialFrequency_injective h ?_
  rw [monomialFrequency_tupleCount, monomialFrequency_tupleCount]
  exact hfreq

end

end GaloisForLFunctions.HTGeometry
