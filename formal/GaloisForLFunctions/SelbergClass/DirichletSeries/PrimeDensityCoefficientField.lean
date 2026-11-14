import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeFilterCoefficientField

/-!
# Coefficient fields with density-zero prime activity

Finite prime windows give a density-zero ideal without requiring any asymptotic regularity of
the windows. Its complementary filter produces a coefficient field. Prime-supported series are
algebraically independent over this field exactly when every nonzero coefficient combination
has support whose window density does not tend to zero.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical Topology

noncomputable section

/-- Fraction of a finite prime window lying in a set. Empty windows have frequency zero. -/
def primeWindowFrequency (W : ℕ → Finset Nat.Primes) (S : Set Nat.Primes) (n : ℕ) : ℝ :=
  ((W n).filter (· ∈ S)).card / (W n).card

/-- Density zero along the specified finite prime windows. -/
def PrimeWindowDensityZero (W : ℕ → Finset Nat.Primes) (S : Set Nat.Primes) : Prop :=
  Tendsto (primeWindowFrequency W S) atTop (𝓝 0)

theorem primeWindowFrequency_nonneg (W : ℕ → Finset Nat.Primes)
    (S : Set Nat.Primes) (n : ℕ) : 0 ≤ primeWindowFrequency W S n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem primeWindowFrequency_mono (W : ℕ → Finset Nat.Primes)
    {S T : Set Nat.Primes} (h : S ⊆ T) (n : ℕ) :
    primeWindowFrequency W S n ≤ primeWindowFrequency W T n := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : (W n).filter (· ∈ S) ⊆ (W n).filter (· ∈ T) := by
    intro p hp
    obtain ⟨hpW, hpS⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpW, h hpS⟩
  exact_mod_cast Finset.card_le_card hsub

theorem primeWindowFrequency_union_le (W : ℕ → Finset Nat.Primes)
    (S T : Set Nat.Primes) (n : ℕ) :
    primeWindowFrequency W (S ∪ T) n ≤
      primeWindowFrequency W S n + primeWindowFrequency W T n := by
  have heq : (W n).filter (· ∈ S ∪ T) =
      (W n).filter (· ∈ S) ∪ (W n).filter (· ∈ T) := by
    ext p
    simp only [Finset.mem_filter, Set.mem_union, Finset.mem_union]
    tauto
  unfold primeWindowFrequency
  rw [heq, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_union_le ((W n).filter (· ∈ S)) ((W n).filter (· ∈ T))

theorem primeWindowDensityZero_empty (W : ℕ → Finset Nat.Primes) :
    PrimeWindowDensityZero W ∅ := by
  simpa only [PrimeWindowDensityZero, primeWindowFrequency, Set.mem_empty_iff_false,
    Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Density-zero prime sets are closed under taking subsets. -/
theorem PrimeWindowDensityZero.subset {W : ℕ → Finset Nat.Primes}
    {S T : Set Nat.Primes} (hT : PrimeWindowDensityZero W T) (hST : S ⊆ T) :
    PrimeWindowDensityZero W S :=
  squeeze_zero (primeWindowFrequency_nonneg W S) (primeWindowFrequency_mono W hST) hT

/-- Density-zero prime sets are closed under finite unions. -/
theorem PrimeWindowDensityZero.union {W : ℕ → Finset Nat.Primes}
    {S T : Set Nat.Primes} (hS : PrimeWindowDensityZero W S)
    (hT : PrimeWindowDensityZero W T) : PrimeWindowDensityZero W (S ∪ T) := by
  apply squeeze_zero (primeWindowFrequency_nonneg W (S ∪ T))
    (primeWindowFrequency_union_le W S T)
  simpa only [add_zero] using hS.add hT

/-- Large prime sets are those whose complements have window density zero. -/
def primeWindowDensityFilter (W : ℕ → Finset Nat.Primes) : Filter Nat.Primes where
  sets := {S | PrimeWindowDensityZero W Sᶜ}
  univ_sets := by
    change PrimeWindowDensityZero W Set.univᶜ
    rw [Set.compl_univ]
    exact primeWindowDensityZero_empty W
  sets_of_superset := by
    intro S T hS hST
    exact hS.subset (Set.compl_subset_compl.mpr hST)
  inter_sets := by
    intro S T hS hT
    change PrimeWindowDensityZero W (S ∩ T)ᶜ
    rw [Set.compl_inter]
    exact hS.union hT

/-- Fractions whose detectable primes have density zero in the chosen windows. -/
abbrev primeDensityCoefficientField (W : ℕ → Finset Nat.Primes) :=
  primeFilterCoefficientField (primeWindowDensityFilter W)

theorem mem_primeDensityCoefficientField_iff
    (W : ℕ → Finset Nat.Primes) (x : arithmeticFunctionFractionField) :
    x ∈ primeDensityCoefficientField W ↔
      PrimeWindowDensityZero W (finitePrimeActivity x) := Iff.rfl

/-- Exact density criterion for prime-supported series. A polynomial relation exists precisely
when some nonzero linear coefficient combination is supported on a density-zero prime set. -/
theorem algebraicIndependent_primeColumns_over_densityField_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (W : ℕ → Finset Nat.Primes) (a : I → Nat.Primes → ℂ) :
    AlgebraicIndependent (primeDensityCoefficientField W)
        (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (a i))) ↔
      ∀ c : I → ℂ,
        PrimeWindowDensityZero W {p | ∑ i, c i * a i p ≠ 0} → c = 0 :=
  algebraicIndependent_primeColumns_over_filterField_iff (primeWindowDensityFilter W) a

#print axioms primeWindowDensityFilter
#print axioms algebraicIndependent_primeColumns_over_densityField_iff

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
