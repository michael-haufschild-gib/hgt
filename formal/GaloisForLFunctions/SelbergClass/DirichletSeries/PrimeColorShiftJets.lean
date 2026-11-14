import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeColorBasis
import GaloisForLFunctions.HTGeometry.PrimeExpLogFiberRigidity

/-!
# Finite-color shift–jet independence with sparse prime exceptions

An eventual relation restricts to an infinite subset of every surviving color fiber. The
exponential-polynomial rigidity theorem then separates all shifts and logarithmic powers on
that subset. Thus adjoining the full shift–jet rectangle preserves precisely the finite-color
independence criterion, including over the density-zero prime coefficient field.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- Fiber rigidity separates every shift and clock order in a filter relation. -/
theorem filterCoefficientIndependent_colorShiftJet_of_fiberRigidity
    {J A C : Type*} [Fintype J] [Fintype A]
    (F : Filter Nat.Primes) (hF : F ≤ cofinite)
    (color : Nat.Primes → C) (b : J → C → ℂ)
    (factor : A → Nat.Primes → ℂ) (clock : Nat.Primes → ℂ) (m : ℕ)
    (hcolor : LinearIndependent ℂ (fun j (c : frequentPrimeColors F color) => b j c.1))
    (hrigid : FactorClockFiberIndependent factor clock m) :
    FilterCoefficientIndependent F
      (coefficientShiftJet (fun j p => b j (color p)) factor clock m) := by
  intro q hq
  have hcolumn : ∀ ak : A × Fin (m + 1), (fun j => q (j, ak)) = 0 := by
    intro ak
    have hvalues : ∀ c : frequentPrimeColors F color, ∑ j, q (j, ak) * b j c.1 = 0 := by
      intro c
      let U : Set Nat.Primes := {p | color p = c.1 ∧
        ∑ jak, q jak * coefficientShiftJet (fun j p => b j (color p)) factor clock m jak p = 0}
      have hU : U.Infinite := by
        intro hfinite
        have hn : ∀ᶠ p in F, p ∉ U := hF (eventually_cofinite.mpr (by simpa using hfinite))
        apply c.2
        filter_upwards [hq, hn] with p hp hn hpc
        exact hn ⟨hpc, hp⟩
      let d : A × Fin (m + 1) → ℂ := fun rk => ∑ j, q (j, rk) * b j c.1
      have hd : d = 0 := by
        apply hrigid U hU d
        apply Set.finite_empty.subset
        intro p hp
        obtain ⟨⟨hpc, hpzero⟩, hpne⟩ := hp
        apply hpne
        calc
          ∑ rk, d rk * factor rk.1 p * clock p ^ (rk.2 : ℕ) =
              ∑ jak, q jak *
                coefficientShiftJet (fun j p => b j (color p)) factor clock m jak p := by
            conv_rhs =>
              rw [Fintype.sum_prod_type, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro rk _
            simp only [d, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            simp only [coefficientShiftJet, hpc]
            ring
          _ = 0 := hpzero
      exact congrFun hd ak
    funext j
    apply (Fintype.linearIndependent_iff.mp hcolor) (fun j => q (j, ak)) _ j
    funext c
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hvalues c
  funext jak
  exact congrFun (hcolumn jak.2) jak.1

/-- Any nonempty shift–jet rectangle detects every dependence of its original source columns. -/
theorem filterCoefficientIndependent_of_coefficientShiftJet
    {J A : Type*} [Fintype J] [Fintype A] [Nonempty A]
    (F : Filter Nat.Primes) (c : J → Nat.Primes → ℂ)
    (factor : A → Nat.Primes → ℂ) (clock : Nat.Primes → ℂ) (m : ℕ)
    (h : FilterCoefficientIndependent F (coefficientShiftJet c factor clock m)) :
    FilterCoefficientIndependent F c := by
  let a₀ := Classical.arbitrary A
  intro q hq
  let q' : J × (A × Fin (m + 1)) → ℂ := fun jak =>
    if jak.2 = (a₀, 0) then q jak.1 else 0
  have hevent : ∀ᶠ p in F,
      ∑ jak, q' jak * coefficientShiftJet c factor clock m jak p = 0 := by
    filter_upwards [hq] with p hp
    rw [Fintype.sum_prod_type]
    simp only [q', coefficientShiftJet]
    simp
    calc
      ∑ j, q j * (c j p * factor a₀ p) = (∑ j, q j * c j p) * factor a₀ p := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hp, zero_mul]
  have hzero := h q' hevent
  funext j
  simpa only [q', if_pos rfl, Pi.zero_apply] using congrFun hzero (j, a₀, 0)

/-- Prime exponential-polynomial rigidity supplies the analytic input: all finite shift–jet
rectangles have exactly the independence of the surviving color table. -/
theorem filterCoefficientIndependent_primeColorShiftJet_iff
    {J A C : Type*} [Fintype J] [Fintype A] [Nonempty A] [Finite C]
    (F : Filter Nat.Primes) (hF : F ≤ cofinite)
    (color : Nat.Primes → C) (b : J → C → ℂ)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) (m : ℕ) :
    FilterCoefficientIndependent F
        (coefficientShiftJet (fun j p => b j (color p))
          (fun a p => primeShiftFactor (alpha a) p) primeLogClock m) ↔
      LinearIndependent ℂ (fun j (c : frequentPrimeColors F color) => b j c.1) := by
  constructor
  · intro h
    exact (filterCoefficientIndependent_finiteColors_iff F color b).mp
      (filterCoefficientIndependent_of_coefficientShiftJet F _ _ _ m h)
  · intro h
    exact filterCoefficientIndependent_colorShiftJet_of_fiberRigidity F hF color b _ _ m h
      (primeFactorClockFiberIndependent alpha hdistinct m)

/-- The complete prime shift–jet family is algebraically independent precisely when its finite
color table is independent on the surviving colors. -/
theorem algebraicIndependent_primeColorShiftJets_over_filterField_iff
    {J A C : Type*} [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
    [Nonempty A] [Finite C]
    (F : Filter Nat.Primes) (hF : F ≤ cofinite)
    (color : Nat.Primes → C) (b : J → C → ℂ)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) (m : ℕ) :
    AlgebraicIndependent (primeFilterCoefficientField F)
        (fun jak => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (coefficientShiftJet (fun j p => b j (color p))
            (fun a p => primeShiftFactor (alpha a) p) primeLogClock m jak))) ↔
      LinearIndependent ℂ (fun j (c : frequentPrimeColors F color) => b j c.1) := by
  rw [algebraicIndependent_primeColumns_over_filterField_iff]
  exact filterCoefficientIndependent_primeColorShiftJet_iff F hF color b alpha hdistinct m

/-- Natural shifts have distinct real parts, so no separation premise is needed for them. -/
theorem primeNaturalShift_real_injective (n : ℕ) :
    Function.Injective (fun a : Fin (n + 1) => ((a : ℕ) : ℂ).re) := by
  intro a b h
  apply Fin.ext
  change ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) at h
  exact_mod_cast h

/-- Over the ordinary density-zero prime coefficient field, every finite natural-shift/log-jet
rectangle obeys the exact surviving-color criterion. -/
theorem algebraicIndependent_primeColorNaturalShiftJets_over_densityField_iff
    {J C : Type*} [Fintype J] [DecidableEq J] [Finite C]
    (color : Nat.Primes → C) (b : J → C → ℂ) (n m : ℕ) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
        (fun jak => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (coefficientShiftJet (fun j p => b j (color p))
            (fun (a : Fin (n + 1)) p => primeShiftFactor (a : ℕ) p) primeLogClock m jak))) ↔
      LinearIndependent ℂ (fun j
        (c : frequentPrimeColors (primeWindowDensityFilter primeCountingWindow) color) =>
          b j c.1) :=
  algebraicIndependent_primeColorShiftJets_over_filterField_iff _
    (primeWindowDensityFilter_le_cofinite _ primeCountingWindow_card_tendsto)
    color b _ (primeNaturalShift_real_injective n) m

/-- A complete finite color basis retains every natural shift and logarithmic jet exactly when
no color fiber has prime density zero. -/
theorem algebraicIndependent_primeColorBasisNaturalShiftJets_over_densityField_iff
    {J C : Type*} [Fintype J] [DecidableEq J] [Finite C]
    (color : Nat.Primes → C) (B : Module.Basis J ℂ (C → ℂ)) (n m : ℕ) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
        (fun jak => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (coefficientShiftJet (fun j p => B j (color p))
            (fun (a : Fin (n + 1)) p => primeShiftFactor (a : ℕ) p) primeLogClock m jak))) ↔
      ∀ c, ¬ PrimeWindowDensityZero primeCountingWindow {p | color p = c} := by
  rw [algebraicIndependent_primeColorNaturalShiftJets_over_densityField_iff,
    linearIndependent_restrict_functionBasis_iff, Set.eq_univ_iff_forall]
  exact forall_congr' fun c => mem_frequentPrimeColors_density_iff _ color c

#print axioms algebraicIndependent_primeColorNaturalShiftJets_over_densityField_iff
#print axioms algebraicIndependent_primeColorBasisNaturalShiftJets_over_densityField_iff

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
