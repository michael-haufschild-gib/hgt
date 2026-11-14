import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeColorShiftJets

/-!
# All natural shifts and logarithmic orders over the density coefficient field

Every polynomial relation involves only finitely many indices, so finite shift–jet squares
control the complete countable rectangle. The exact finite-color criterion therefore persists
after adjoining all natural shifts and every logarithmic derivative order simultaneously.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- Independence of a doubly indexed family is detected on its finite square truncations. -/
theorem algebraicIndependent_natPair_iff_finiteSquares
    {R K J : Type*} [CommRing R] [CommRing K] [Algebra R K]
    (x : J × (ℕ × ℕ) → K) :
    AlgebraicIndependent R x ↔ ∀ n,
      AlgebraicIndependent R (fun q : J × (Fin (n + 1) × Fin (n + 1)) =>
        x (q.1, q.2.1, q.2.2)) := by
  constructor
  · intro h n
    apply h.comp
    intro q r hqr
    apply Prod.ext
    · exact congrArg (fun t : J × (ℕ × ℕ) => t.1) hqr
    · apply Prod.ext
      · exact Fin.ext (congrArg (fun t : J × (ℕ × ℕ) => t.2.1) hqr)
      · exact Fin.ext (congrArg (fun t : J × (ℕ × ℕ) => t.2.2) hqr)
  · intro h
    apply algebraicIndependent_of_finite_type
    intro s hs
    obtain ⟨N, hN⟩ := (hs.image (fun q => max q.2.1 q.2.2)).bddAbove
    have hb (q : s) : max q.1.2.1 q.1.2.2 ≤ N := hN ⟨q.1, q.2, rfl⟩
    let e : s → J × (Fin (N + 1) × Fin (N + 1)) := fun q =>
      (q.1.1, ⟨q.1.2.1, Nat.lt_succ_of_le ((le_max_left _ _).trans (hb q))⟩,
        ⟨q.1.2.2, Nat.lt_succ_of_le ((le_max_right _ _).trans (hb q))⟩)
    have he : Function.Injective e := by
      intro q r hqr
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun t : J × (Fin (N + 1) × Fin (N + 1)) => t.1) hqr
      · apply Prod.ext
        · exact congrArg (fun t : J × (Fin (N + 1) × Fin (N + 1)) => (t.2.1 : ℕ)) hqr
        · exact congrArg (fun t : J × (Fin (N + 1) × Fin (N + 1)) => (t.2.2 : ℕ)) hqr
    exact (h N).comp e he

/-- A prime-supported color observable with a natural shift and logarithmic order. -/
def primeColorNaturalShiftLogJet {J C : Type*}
    (color : Nat.Primes → C) (b : J → C → ℂ) (q : J × (ℕ × ℕ)) :
    arithmeticFunctionFractionField :=
  algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
    (arithmeticOfPrimeColumn (fun p =>
      b q.1 (color p) * primeShiftFactor q.2.1 p * primeLogClock p ^ q.2.2))

/-- All natural shifts and logarithmic orders are jointly independent exactly when the color
table is independent on its non-negligible prime fibers. -/
theorem algebraicIndependent_primeColorInfiniteJets_over_densityField_iff
    {J C : Type*} [Fintype J] [DecidableEq J] [Finite C]
    (color : Nat.Primes → C) (b : J → C → ℂ) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
        (primeColorNaturalShiftLogJet color b) ↔
      LinearIndependent ℂ (fun j
        (c : frequentPrimeColors (primeWindowDensityFilter primeCountingWindow) color) =>
          b j c.1) := by
  rw [algebraicIndependent_natPair_iff_finiteSquares]
  constructor
  · intro h
    exact (algebraicIndependent_primeColorNaturalShiftJets_over_densityField_iff
      color b 0 0).mp (h 0)
  · intro h n
    exact (algebraicIndependent_primeColorNaturalShiftJets_over_densityField_iff
      color b n n).mpr h

/-- A complete function basis remains jointly independent through all shifts and logarithmic
orders exactly when every color fiber survives density-zero prime exceptions. -/
theorem algebraicIndependent_primeColorBasisInfiniteJets_over_densityField_iff
    {J C : Type*} [Fintype J] [DecidableEq J] [Finite C]
    (color : Nat.Primes → C) (B : Module.Basis J ℂ (C → ℂ)) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
        (primeColorNaturalShiftLogJet color (fun j c => B j c)) ↔
      ∀ c, ¬ PrimeWindowDensityZero primeCountingWindow {p | color p = c} := by
  rw [algebraicIndependent_primeColorInfiniteJets_over_densityField_iff,
    linearIndependent_restrict_functionBasis_iff, Set.eq_univ_iff_forall]
  exact forall_congr' fun c => mem_frequentPrimeColors_density_iff _ color c

#print axioms algebraicIndependent_primeColorInfiniteJets_over_densityField_iff
#print axioms algebraicIndependent_primeColorBasisInfiniteJets_over_densityField_iff

/-- Every surviving color supplies all natural shifts and logarithmic orders as independent
generators. No assumption that all original colors survive is needed. -/
theorem algebraicIndependent_frequentPrimeColorInfiniteJets_over_densityField
    {C : Type*} [Fintype C] [DecidableEq C] (color : Nat.Primes → C) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
      (primeColorNaturalShiftLogJet color
        (fun (c : frequentPrimeColors (primeWindowDensityFilter primeCountingWindow) color) d =>
          if d = c.1 then 1 else 0)) := by
  let F := primeWindowDensityFilter primeCountingWindow
  let b := fun (c : frequentPrimeColors F color) (d : C) => if d = c.1 then (1 : ℂ) else 0
  apply (algebraicIndependent_primeColorInfiniteJets_over_densityField_iff color b).mpr
  exact (algebraicIndependent_finiteColorPrimeColumns_iff F color b).mp
    (algebraicIndependent_frequentPrimeColorIndicators F color)

#print axioms algebraicIndependent_frequentPrimeColorInfiniteJets_over_densityField

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
