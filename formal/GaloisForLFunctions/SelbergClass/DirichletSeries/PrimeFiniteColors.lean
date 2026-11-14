import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeDensityCoefficientField

/-!
# Finite-valued prime data over exceptional-prime coefficient fields

For a finite prime coloring, an eventual property is determined exactly by the colors whose
fibers are frequent. Consequently, the algebraic independence of prime columns depending only
on the color is the ordinary linear independence of their values on these surviving colors.
This is a finite matrix criterion for arbitrary prime filters, including density-zero exceptions.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- Colors whose prime fibers cannot be removed by the filter's exceptional sets. -/
def frequentPrimeColors {C : Type*} (F : Filter Nat.Primes) (color : Nat.Primes → C) : Set C :=
  {c | ∃ᶠ p in F, color p = c}

/-- With finitely many colors, eventual properties are exactly the properties true on every
frequent color. Finiteness is used only to intersect the exceptional sets of the absent colors. -/
theorem eventually_prime_color_property_iff
    {C : Type*} [Finite C] (F : Filter Nat.Primes) (color : Nat.Primes → C) (P : C → Prop) :
    (∀ᶠ p in F, P (color p)) ↔ ∀ c, (∃ᶠ p in F, color p = c) → P c := by
  constructor
  · intro h c hc
    by_contra hn
    apply hc
    filter_upwards [h] with p hp hpc
    exact hn (hpc ▸ hp)
  · intro h
    have heach : ∀ c, ∀ᶠ p in F, color p = c → P c := by
      intro c
      by_cases hc : ∃ᶠ p in F, color p = c
      · exact Eventually.of_forall fun _ _ => h c hc
      · filter_upwards [not_frequently.mp hc] with p hp hpc
        exact False.elim (hp hpc)
    filter_upwards [eventually_all.mpr heach] with p hp
    exact hp (color p) rfl

/-- Prime-column independence modulo a filter reduces to a finite table of surviving colors. -/
theorem filterCoefficientIndependent_finiteColors_iff
    {I C : Type*} [Fintype I] [Finite C]
    (F : Filter Nat.Primes) (color : Nat.Primes → C) (b : I → C → ℂ) :
    FilterCoefficientIndependent F (fun i p => b i (color p)) ↔
      LinearIndependent ℂ (fun i (c : frequentPrimeColors F color) => b i c.1) := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h c hc i
    have hzero := h c (by
      apply (eventually_prime_color_property_iff F color (fun d => ∑ j, c j * b j d = 0)).mpr
      intro d hd
      have heval := congrFun hc (⟨d, hd⟩ : frequentPrimeColors F color)
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using heval)
    exact congrFun hzero i
  · intro h c hc
    funext i
    apply h c _ i
    funext d
    have heval := (eventually_prime_color_property_iff F color
      (fun d => ∑ j, c j * b j d = 0)).mp hc d.1 d.2
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using heval

/-- Exact finite-color algebraic independence criterion over the full filter coefficient field. -/
theorem algebraicIndependent_finiteColorPrimeColumns_iff
    {I C : Type*} [Fintype I] [DecidableEq I] [Finite C]
    (F : Filter Nat.Primes) (color : Nat.Primes → C) (b : I → C → ℂ) :
    AlgebraicIndependent (primeFilterCoefficientField F)
        (fun i => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (fun p => b i (color p)))) ↔
      LinearIndependent ℂ (fun i (c : frequentPrimeColors F color) => b i c.1) := by
  rw [algebraicIndependent_primeColumns_over_filterField_iff,
    filterCoefficientIndependent_finiteColors_iff]

/-- Under the density filter, a color survives precisely when its fiber does not have density zero. -/
theorem mem_frequentPrimeColors_density_iff
    {C : Type*} (W : ℕ → Finset Nat.Primes) (color : Nat.Primes → C) (c : C) :
    c ∈ frequentPrimeColors (primeWindowDensityFilter W) color ↔
      ¬ PrimeWindowDensityZero W {p | color p = c} := by
  change (¬ PrimeWindowDensityZero W {p | color p ≠ c}ᶜ) ↔ _
  simp only [Set.compl_setOf, not_not]

/-- Under the cofinite filter, surviving colors are exactly the colors with infinite prime fibers. -/
theorem mem_frequentPrimeColors_cofinite_iff
    {C : Type*} (color : Nat.Primes → C) (c : C) :
    c ∈ frequentPrimeColors cofinite color ↔ {p | color p = c}.Infinite := by
  change (¬ ∀ᶠ p in cofinite, color p ≠ c) ↔ _
  rw [eventually_cofinite]
  simp only [not_not, Set.Infinite]

/-- Indicators of all prime colors are algebraically independent exactly when every color survives.
The prime-indicator series is their sum, rather than a scalar constant of the convolution algebra. -/
theorem algebraicIndependent_primeColorIndicators_iff
    {C : Type*} [Fintype C] [DecidableEq C]
    (F : Filter Nat.Primes) (color : Nat.Primes → C) :
    AlgebraicIndependent (primeFilterCoefficientField F)
        (fun c => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (fun p => if color p = c then 1 else 0))) ↔
      ∀ c, ∃ᶠ p in F, color p = c := by
  rw [algebraicIndependent_finiteColorPrimeColumns_iff F color
    (fun c d => if d = c then 1 else 0)]
  constructor
  · intro h c
    by_contra hc
    apply h.ne_zero c
    funext d
    have hdc : d.1 ≠ c := by
      intro heq
      exact hc (heq ▸ d.2)
    simp only [hdc, if_false, Pi.zero_apply]
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have heval := congrFun hc (⟨i, h i⟩ : frequentPrimeColors F color)
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using heval

/-- Every surviving color provides an independent prime-indicator generator, without assumptions
on the coloring or the filter. -/
theorem algebraicIndependent_frequentPrimeColorIndicators
    {C : Type*} [Fintype C] [DecidableEq C]
    (F : Filter Nat.Primes) (color : Nat.Primes → C) :
    AlgebraicIndependent (primeFilterCoefficientField F)
      (fun c : frequentPrimeColors F color =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (fun p => if color p = c.1 then 1 else 0))) := by
  rw [algebraicIndependent_finiteColorPrimeColumns_iff F color
    (fun (c : frequentPrimeColors F color) d => if d = c.1 then 1 else 0)]
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have heval := congrFun hc i
  have hcoe : ∀ d : frequentPrimeColors F color, i.1 = d.1 ↔ i = d :=
    fun _ => ⟨Subtype.ext, congrArg Subtype.val⟩
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcoe] using heval

#print axioms algebraicIndependent_finiteColorPrimeColumns_iff
#print axioms algebraicIndependent_primeColorIndicators_iff
#print axioms algebraicIndependent_frequentPrimeColorIndicators

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
