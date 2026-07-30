import GaloisForLFunctions.HTGeometry.PrimeResidueValuationInteractionSuperselection
import GaloisForLFunctions.HTGeometry.PrimePowerAnalyticDilation
import GaloisForLFunctions.HTGeometry.PrimeWalshDifferentialRank
import GaloisForLFunctions.HTGeometry.UpperEndConstantField
import GaloisForLFunctions.HTGeometry.DirectionalDerivationLawSpace

/-!
# Analytic prime-residue valuation superselection

The formal source-creation tower has a faithful realization by actual Dirichlet-series germs at
the complex upper end. This module packages finite-abscissa L-series as an injective differential
map into the upper-end meromorphic field and applies the nonuniform prime-power packet theorem to
the complete residue-interaction grid.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Module ArithmeticFunction Filter
open scoped Differential LSeries.notation

noncomputable section

universe u

local instance upperEndAnalyticDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance upperEndMeroComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance upperEndMeroDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- The analytic-subring element represented by a finite-abscissa rotated L-series. -/
def finiteAbscissaLSeriesUpperEndAnalyticElement
    (f : finiteAbscissaArithmeticSubalgebra) : upperEndAnalyticSubring := by
  refine ⟨finiteAbscissaLSeriesToUpperEndGerm f, ?_⟩
  obtain ⟨H, hH⟩ := finiteAbscissa_rotatedLSeries_eventuallyAnalytic f
  exact ⟨fun z : ℂ => LSeries (fun n => f.1 n) (-Complex.I * z), H, hH, rfl⟩

@[simp]
theorem finiteAbscissaLSeriesUpperEndAnalyticElement_coe
    (f : finiteAbscissaArithmeticSubalgebra) :
    (finiteAbscissaLSeriesUpperEndAnalyticElement f : Germ upperEndFilter ℂ) =
      finiteAbscissaLSeriesToUpperEndGerm f :=
  rfl

/-- Faithful analytic realization of the finite-abscissa arithmetic algebra in the upper-end
meromorphic field. -/
noncomputable def finiteAbscissaLSeriesToUpperEndMero :
    finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] upperEndMeroField where
  toFun f := algebraMap upperEndAnalyticSubring upperEndMeroField
    (finiteAbscissaLSeriesUpperEndAnalyticElement f)
  map_zero' := by
    rw [← map_zero (algebraMap upperEndAnalyticSubring upperEndMeroField)]
    congr 1
    apply Subtype.ext
    exact finiteAbscissaLSeriesToUpperEndGerm.map_zero
  map_one' := by
    rw [← map_one (algebraMap upperEndAnalyticSubring upperEndMeroField)]
    congr 1
    apply Subtype.ext
    exact finiteAbscissaLSeriesToUpperEndGerm.map_one
  map_add' f g := by
    rw [← map_add (algebraMap upperEndAnalyticSubring upperEndMeroField)]
    congr 1
    apply Subtype.ext
    exact finiteAbscissaLSeriesToUpperEndGerm.map_add f g
  map_mul' f g := by
    rw [← map_mul (algebraMap upperEndAnalyticSubring upperEndMeroField)]
    congr 1
    apply Subtype.ext
    exact finiteAbscissaLSeriesToUpperEndGerm.map_mul f g
  commutes' c := by
    change algebraMap upperEndAnalyticSubring upperEndMeroField
        (finiteAbscissaLSeriesUpperEndAnalyticElement
          (algebraMap ℂ finiteAbscissaArithmeticSubalgebra c)) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndPolyToAnalytic (Polynomial.C c))
    congr 1
    apply Subtype.ext
    change finiteAbscissaLSeriesToUpperEndGerm
        (algebraMap ℂ finiteAbscissaArithmeticSubalgebra c) =
      (upperEndPolyToAnalytic (Polynomial.C c) : Germ upperEndFilter ℂ)
    rw [finiteAbscissaLSeriesToUpperEndGerm.commutes]
    change (↑(fun _ : ℂ => c) : Germ upperEndFilter ℂ) =
      ↑(fun z : ℂ => (Polynomial.C c).eval z)
    rw [Germ.coe_eq]
    exact Filter.Eventually.of_forall fun z => by simp

theorem finiteAbscissaLSeriesToUpperEndMero_injective :
    Function.Injective finiteAbscissaLSeriesToUpperEndMero := by
  intro f g hfg
  have hanalytic : finiteAbscissaLSeriesUpperEndAnalyticElement f =
      finiteAbscissaLSeriesUpperEndAnalyticElement g :=
    (IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField) hfg
  exact finiteAbscissaLSeriesToUpperEndGerm_injective
    (congrArg Subtype.val hanalytic)

theorem upperEndAnalyticDeriv_finiteAbscissaLSeriesElement
    (f : finiteAbscissaArithmeticSubalgebra) :
    upperEndAnalyticDeriv (finiteAbscissaLSeriesUpperEndAnalyticElement f) =
      finiteAbscissaLSeriesUpperEndAnalyticElement (finiteAbscissaRotatedDeriv f) := by
  apply Subtype.ext
  exact upperEndGermDeriv_finiteAbscissaLSeries f

theorem deriv_finiteAbscissaLSeriesToUpperEndMero
    (f : finiteAbscissaArithmeticSubalgebra) :
    (finiteAbscissaLSeriesToUpperEndMero f)′ =
      finiteAbscissaLSeriesToUpperEndMero (finiteAbscissaRotatedDeriv f) := by
  change (algebraMap upperEndAnalyticSubring upperEndMeroField
    (finiteAbscissaLSeriesUpperEndAnalyticElement f))′ = _
  rw [upperEndMeroFieldDifferential_algebraMap,
    upperEndAnalyticDeriv_finiteAbscissaLSeriesElement]
  rfl

theorem differentialJet_finiteAbscissaLSeriesToUpperEndMero
    (f : finiteAbscissaArithmeticSubalgebra) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (finiteAbscissaLSeriesToUpperEndMero f) =
      finiteAbscissaLSeriesToUpperEndMero
        ((finiteAbscissaRotatedDeriv^[k]) f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [GaloisForLFunctions.differentialJet_succ, ih,
        Function.iterate_succ_apply', deriv_finiteAbscissaLSeriesToUpperEndMero]

/-- The nonuniform prime-power analytic packet remains algebraically independent after passage
to the upper-end meromorphic field. -/
theorem algebraicIndependent_primePowerDilatedUpperEndMero
    {d : ℕ} (B : Fin d → Type*)
    [∀ r, Fintype (B r)] [∀ r, DecidableEq (B r)]
    (f : ∀ r, B r → finiteAbscissaArithmeticSubalgebra)
    (a : ∀ r, B r → Nat.Primes → ℂ)
    (hf : ∀ r i, (f r i).1 = arithmeticOfPrimeColumn (a r i))
    (htail : ∀ r, TailCoefficientIndependent (a r)) :
    AlgebraicIndependent ℂ
      (fun i : Σ r, B r =>
        finiteAbscissaLSeriesToUpperEndMero
          (finiteAbscissaPrimePowerDilation i.1 (f i.1 i.2))) := by
  let g : (Σ r, B r) → finiteAbscissaArithmeticSubalgebra := fun i =>
    finiteAbscissaPrimePowerDilation i.1 (f i.1 i.2)
  have hpacket := cofinitePrimePowerPacket_of_layerwise_tailIndependent d B a htail
  have hraw := algebraicIndependent_arithmeticPrimePowerColumns_of_cofinitePacket
    (primePowerSigmaExponent (A := B)) (primePowerSigmaCoefficient a) hpacket
  let incl : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] ArithmeticFunction ℂ :=
    finiteAbscissaArithmeticSubalgebra.val
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext hxy
  have hg : AlgebraicIndependent ℂ g := by
    apply (AlgHom.algebraicIndependent_iff incl hincl).mp
    convert hraw using 1
    funext i
    exact finiteAbscissaPrimePowerDilation_eq_arithmeticOfPrimePowerColumn
      i.1 (f i.1 i.2) (a i.1 i.2) (hf i.1 i.2)
  exact hg.map' finiteAbscissaLSeriesToUpperEndMero_injective

theorem primeResidueInteractionCoefficient_norm_le_one
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) (z : ∀ i, A i) (p : Nat.Primes) :
    ‖primeResidueInteractionCoefficient A y z p‖ ≤ 1 := by
  classical
  rw [primeResidueInteractionCoefficient, anchoredProductBasis_apply, norm_prod]
  apply Finset.prod_le_one
  · intro i _
    exact norm_nonneg _
  · intro i _
    by_cases hz : z i = 1
    · simp [hz]
    · by_cases hyz : y p i = z i <;> simp [hz, hyz]

def primeResidueFiniteAbscissaSource
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) (z : ∀ i, A i) :
    finiteAbscissaArithmeticSubalgebra :=
  boundedPrimeFiniteAbscissa (primeResidueInteractionCoefficient A y z)
    (primeResidueInteractionCoefficient_norm_le_one A y z)

def primeResidueValuationUpperEndCarrier
    {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) (e : ℕ) (z : ∀ i, A i) :
    upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero
    (finiteAbscissaPrimePowerDilation e (primeResidueFiniteAbscissaSource A y z))

def primeResidueAnalyticJetSource
    {m : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (x : (∀ i, A i) × (Unit × Fin (m + 1))) :
    finiteAbscissaArithmeticSubalgebra :=
  (finiteAbscissaRotatedDeriv^[x.2.2])
    (primeResidueFiniteAbscissaSource A y x.1)

def primeResidueAnalyticJetCoefficient
    {m : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (x : (∀ i, A i) × (Unit × Fin (m + 1))) (p : Nat.Primes) : ℂ :=
  primeResidueInteractionCoefficient A y x.1 p *
    rotatedPrimeLogClock p ^ (x.2.2 : ℕ)

theorem primeResidueAnalyticJetSource_eq_arithmeticOfPrimeColumn
    {m : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (x : (∀ i, A i) × (Unit × Fin (m + 1))) :
    (primeResidueAnalyticJetSource A y x).1 =
      arithmeticOfPrimeColumn (primeResidueAnalyticJetCoefficient A y x) := by
  ext n
  rw [primeResidueAnalyticJetSource,
    finiteAbscissaRotatedDeriv_iterate_apply]
  by_cases hn : n.Prime
  · let p : Nat.Primes := ⟨n, hn⟩
    rw [show (primeResidueFiniteAbscissaSource A y x.1).1 n =
        primeResidueInteractionCoefficient A y x.1 p by
      exact arithmeticOfPrimeColumn_apply_prime _ p]
    rw [arithmeticOfPrimeColumn_apply_prime _ p]
    simp only [p, primeResidueAnalyticJetCoefficient, rotatedPrimeLogClock,
      primeLogClock, mul_pow]
    ring
  · have hsource : (primeResidueFiniteAbscissaSource A y x.1).1 n = 0 := by
      simp [primeResidueFiniteAbscissaSource, boundedPrimeFiniteAbscissa,
        arithmeticOfPrimeColumn, hn]
    rw [hsource]
    simp [arithmeticOfPrimeColumn, hn]

theorem cofiniteTailDenseOn_primeResidueAnalyticJetCoefficient_tailIndependent
    {m : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)] [Fintype (∀ i, A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    TailCoefficientIndependent (primeResidueAnalyticJetCoefficient (m := m) A y) := by
  letI : DecidableEq (∀ i, A i) := Classical.decEq _
  let f : (∀ i, A i) → (∀ i, A i) → ℂ := fun z => anchoredProductBasis A z
  have hf : ∀ z, Continuous (f z) := fun _ => continuous_of_discreteTopology
  have hlinear : LinearIndependent ℂ
      (fun z => fun v : FullValueSubtype (∀ i, A i) => f z v.1) := by
    have hfamily :
        (fun z => fun v : FullValueSubtype (∀ i, A i) => f z v.1) =
          (anchoredRestrictedProductBasis A :
            (∀ i, A i) → FullValueSubtype (∀ i, A i) → ℂ) := by
      funext z v
      rfl
    rw [hfamily]
    exact (anchoredRestrictedProductBasis A).linearIndependent
  let raw : ((∀ i, A i) × (Unit × Fin (m + 1))) → Nat.Primes → ℂ :=
    fun jak p =>
      f jak.1 (y p) *
        primeShiftFactor ((fun _ : Unit => (0 : ℂ)) jak.2.1) p *
          ((((0 + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (jak.2.2 : ℕ))
  have hraw : TailCoefficientIndependent raw := by
    exact cofiniteTailDenseOn_primePowerShiftedRotatedJet_tailIndependent
      0 y Set.univ hy f hf hlinear (fun _ : Unit => 0)
        (fun _ _ _ => Subsingleton.elim _ _) m
  have hfamily :
      raw = primeResidueAnalyticJetCoefficient (m := m) A y := by
    funext jak p
    simp [raw, f, primeShiftFactor, primeResidueAnalyticJetCoefficient,
      primeResidueInteractionCoefficient]
  rw [← hfamily]
  exact hraw

/-- Every finite valuation--residue--derivative rectangle is algebraically independent as an
actual upper-end meromorphic germ family. -/
theorem cofiniteTailDenseOn_primeResidueValuationUpperEndCarrier_jets_algebraicIndependent
    {d m : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    AlgebraicIndependent ℂ
      (fun q : PrimeResidueValuationInteractionGridIndex d A × Fin (m + 1) =>
        GaloisForLFunctions.differentialJet q.2
          (primeResidueValuationUpperEndCarrier A y q.1.1 q.1.2)) := by
  letI : Fintype (∀ i, A i) := Fintype.ofFinite _
  letI : DecidableEq (∀ i, A i) := Classical.decEq _
  let B : Fin d → Type u := fun _ =>
    (∀ i, A i) × (Unit × Fin (m + 1))
  letI (r : Fin d) : Fintype (B r) := inferInstance
  letI (r : Fin d) : DecidableEq (B r) := Classical.decEq _
  let f : ∀ r, B r → finiteAbscissaArithmeticSubalgebra := fun _ x =>
    primeResidueAnalyticJetSource A y x
  let a : ∀ r, B r → Nat.Primes → ℂ := fun _ x =>
    primeResidueAnalyticJetCoefficient A y x
  have hf : ∀ r x, (f r x).1 = arithmeticOfPrimeColumn (a r x) := by
    intro r x
    exact primeResidueAnalyticJetSource_eq_arithmeticOfPrimeColumn A y x
  have htail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r
    exact cofiniteTailDenseOn_primeResidueAnalyticJetCoefficient_tailIndependent A y hy
  have hraw := algebraicIndependent_primePowerDilatedUpperEndMero B f a hf htail
  let embed : PrimeResidueValuationInteractionGridIndex d A × Fin (m + 1) →
      Σ r, B r := fun q => ⟨q.1.1, (q.1.2, ((), q.2))⟩
  let project : (Σ r, B r) →
      PrimeResidueValuationInteractionGridIndex d A × Fin (m + 1) :=
    fun q => (⟨q.1, q.2.1⟩, q.2.2.2)
  have hembed : Function.Injective embed := by
    exact Function.LeftInverse.injective (fun q => rfl : ∀ q, project (embed q) = q)
  have hsub := hraw.comp embed hembed
  let scale : PrimeResidueValuationInteractionGridIndex d A × Fin (m + 1) → ℂ :=
    fun q => (((q.1.1.1 + 1 : ℕ) : ℂ) ^ (q.2 : ℕ))
  have hscale : ∀ q, scale q ≠ 0 := by
    intro q
    exact pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero q.1.1.1)
  have hscaled :=
    AlgebraicIndependent.const_mul_coordinates hsub scale hscale
  convert! hscaled using 1
  funext q
  change GaloisForLFunctions.differentialJet q.2
      (finiteAbscissaLSeriesToUpperEndMero
        (finiteAbscissaPrimePowerDilation q.1.1
          (primeResidueFiniteAbscissaSource A y q.1.2))) =
    algebraMap ℂ upperEndMeroField
        ((((q.1.1.1 + 1 : ℕ) : ℂ) ^ (q.2 : ℕ))) *
      finiteAbscissaLSeriesToUpperEndMero
        (finiteAbscissaPrimePowerDilation q.1.1
          ((finiteAbscissaRotatedDeriv^[q.2])
            (primeResidueFiniteAbscissaSource A y q.1.2)))
  rw [differentialJet_finiteAbscissaLSeriesToUpperEndMero,
    finiteAbscissaRotatedDeriv_iterate_primePowerDilation]
  rw [map_smul]
  rw [Algebra.smul_def]

/-- Finite derivative rectangles exhaust a complete countable jet family. -/
theorem algebraicIndependent_prod_nat_of_all_fin
    {K I : Type*} [Field K] [CommRing I] [Algebra K I]
    {J : Type*} [Finite J] (x : J × ℕ → I)
    (h : ∀ m, AlgebraicIndependent K
      (fun q : J × Fin (m + 1) => x (q.1, q.2))) :
    AlgebraicIndependent K x := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  have hfinite : (Prod.snd '' (t : Set (J × ℕ))).Finite := ht.image _
  obtain ⟨m, hm⟩ := hfinite.bddAbove
  let embed : t → J × Fin (m + 1) := fun q =>
    ⟨q.1.1, ⟨q.1.2, Nat.lt_succ_of_le (hm ⟨q.1, q.2, rfl⟩)⟩⟩
  have hembed : Function.Injective embed := by
    intro q r hqr
    apply Subtype.ext
    have hval := congrArg (fun z : J × Fin (m + 1) => (z.1, (z.2 : ℕ))) hqr
    simpa [embed] using hval
  have hsub := (h m).comp embed hembed
  simpa [embed, Function.comp_def] using hsub

/-- **Analytic rectangular differential spectrum.** Every finite valuation--residue grid is
jointly differentially independent over the complex constants as a family of actual meromorphic
Dirichlet germs. -/
theorem cofiniteTailDenseOn_primeResidueValuationUpperEndCarrier_differentialIndependent
    {d : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun x : PrimeResidueValuationInteractionGridIndex d A =>
        primeResidueValuationUpperEndCarrier A y x.1 x.2) := by
  unfold GaloisForLFunctions.DifferentialIndependent
  exact algebraicIndependent_prod_nat_of_all_fin _ fun m =>
    cofiniteTailDenseOn_primeResidueValuationUpperEndCarrier_jets_algebraicIndependent
      A y hy

def primeResidueValuationUpperEndGridCarrier
    {d : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (x : PrimeResidueValuationInteractionGridIndex d A) : upperEndMeroField :=
  primeResidueValuationUpperEndCarrier A y x.1 x.2

def primeResidueValuationUpperEndGridSectorCarrier
    {d : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (Q : PrimeResidueValuationInteractionGridIndex d A → Prop)
    (x : PrimeResidueValuationGridSectorIndex d A Q) : upperEndMeroField :=
  primeResidueValuationUpperEndGridCarrier A y x.1

def primeResidueValuationUpperEndGridSectorComplementCarrier
    {d : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i)
    (Q : PrimeResidueValuationInteractionGridIndex d A → Prop)
    (x : PrimeResidueValuationGridSectorComplementIndex d A Q) : upperEndMeroField :=
  primeResidueValuationUpperEndGridCarrier A y x.1

/-- Every selected set of analytic valuation--residue cells is relatively HT over the
differential field generated by its complete complement. -/
theorem cofiniteTailDenseOn_primeResidueValuationUpperEndGridSector_relativeHT
    {d : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    (Q : PrimeResidueValuationInteractionGridIndex d A → Prop) :
    GaloisForLFunctions.DifferentialIndependent
      (GaloisForLFunctions.differentialAdjoin ℂ
        (Set.range (primeResidueValuationUpperEndGridSectorComplementCarrier A y Q)))
      (primeResidueValuationUpperEndGridSectorCarrier A y Q) := by
  let total := PrimeResidueValuationInteractionGridIndex d A
  let other := PrimeResidueValuationGridSectorComplementIndex d A Q
  let cell := PrimeResidueValuationGridSectorIndex d A Q
  let full : total → upperEndMeroField :=
    primeResidueValuationUpperEndGridCarrier A y
  let left : other → upperEndMeroField :=
    primeResidueValuationUpperEndGridSectorComplementCarrier A y Q
  let right : cell → upperEndMeroField :=
    primeResidueValuationUpperEndGridSectorCarrier A y Q
  have hfull :=
    cofiniteTailDenseOn_primeResidueValuationUpperEndCarrier_differentialIndependent
      (d := d) A y hy
  let embed : other ⊕ cell → total
    | Sum.inl x => x.1
    | Sum.inr x => x.1
  have hembed : Function.Injective embed := by
    intro x z hxz
    rcases x with x | x <;> rcases z with z | z
    · exact congrArg Sum.inl (Subtype.ext hxz)
    · exfalso
      change x.1 = z.1 at hxz
      exact x.2 (hxz ▸ z.2)
    · exfalso
      change x.1 = z.1 at hxz
      exact z.2 (hxz.symm ▸ x.2)
    · exact congrArg Sum.inr (Subtype.ext hxz)
  have hjoint := hfull.comp embed hembed
  have hfamily : full ∘ embed = Sum.elim left right := by
    funext x
    rcases x with x | x <;> rfl
  have hjoint' : GaloisForLFunctions.DifferentialIndependent ℂ
      (Sum.elim left right) := by
    rw [← hfamily]
    exact hjoint
  exact GaloisForLFunctions.differentialIndependent_sum_right_over_left_differentialAdjoin
    left right hjoint'

abbrev primeResidueValuationUpperEndDepthPrefixCarrier
    {n : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) :=
  primeResidueValuationUpperEndGridSectorComplementCarrier A y
    (fun x : PrimeResidueValuationInteractionGridIndex (n + 2) A =>
      x.1.1 = n + 1)

abbrev primeResidueValuationUpperEndNextLayerCarrier
    {n : ℕ} {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) :=
  primeResidueValuationUpperEndGridSectorCarrier A y
    (fun x : PrimeResidueValuationInteractionGridIndex (n + 2) A =>
      x.1.1 = n + 1)

def primeResidueValuationUpperEndDepthPrefixField
    (n : ℕ) {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) : IntermediateField ℂ upperEndMeroField :=
  GaloisForLFunctions.differentialAdjoin ℂ
    (Set.range (primeResidueValuationUpperEndDepthPrefixCarrier (n := n) A y))

/-- The complete next analytic valuation layer is relatively HT over every analytic carrier at
every earlier depth, with exact relative rank equal to the residue-state cardinality. -/
theorem cofiniteTailDenseOn_primeResidueValuationUpperEndNextLayer_relativeHT
    (n : ℕ) {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    GaloisForLFunctions.DifferentialIndependent
        (primeResidueValuationUpperEndDepthPrefixField n A y)
        (primeResidueValuationUpperEndNextLayerCarrier (n := n) A y) ∧
      Nat.card (PrimeResidueValuationNextLayerIndex n A) =
        ∏ i, Fintype.card (A i) := by
  constructor
  · simpa only [primeResidueValuationUpperEndDepthPrefixField,
      primeResidueValuationUpperEndDepthPrefixCarrier,
      primeResidueValuationUpperEndNextLayerCarrier] using!
      (cofiniteTailDenseOn_primeResidueValuationUpperEndGridSector_relativeHT
        A y hy (fun x : PrimeResidueValuationInteractionGridIndex (n + 2) A =>
          x.1.1 = n + 1))
  · exact primeResidueValuationNextLayerIndex_card n A

theorem cofiniteTailDenseOn_primeResidueValuationUpperEndNextLayer_not_mem_prefix
    (n : ℕ) {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) (z : ∀ i, A i) :
    primeResidueValuationUpperEndCarrier A y (n + 1) z ∉
      primeResidueValuationUpperEndDepthPrefixField n A y := by
  let out : PrimeResidueValuationNextLayerIndex n A :=
    ⟨⟨⟨n + 1, by omega⟩, z⟩, rfl⟩
  have hrel :=
    (cofiniteTailDenseOn_primeResidueValuationUpperEndNextLayer_relativeHT
      n A y hy).1
  unfold GaloisForLFunctions.DifferentialIndependent at hrel
  have hout :
      primeResidueValuationUpperEndNextLayerCarrier (n := n) A y out =
        primeResidueValuationUpperEndCarrier A y (n + 1) z := by
    rfl
  have htrans : Transcendental (primeResidueValuationUpperEndDepthPrefixField n A y)
      (primeResidueValuationUpperEndCarrier A y (n + 1) z) := by
    rw [← hout]
    simpa using hrel.transcendental (out, 0)
  intro hmem
  apply htrans
  exact isAlgebraic_algebraMap
    (R := primeResidueValuationUpperEndDepthPrefixField n A y)
    (A := upperEndMeroField)
    (⟨primeResidueValuationUpperEndCarrier A y (n + 1) z, hmem⟩ :
      primeResidueValuationUpperEndDepthPrefixField n A y)

/-- The analytic depth-prefix fields form a strict infinite tower. -/
theorem cofiniteTailDenseOn_primeResidueValuationUpperEndDepthPrefixField_strictMono
    (n : ℕ) {ι : Type u} [Fintype ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ) :
    primeResidueValuationUpperEndDepthPrefixField n A y <
      primeResidueValuationUpperEndDepthPrefixField (n + 1) A y := by
  have hrange :
      Set.range (primeResidueValuationUpperEndDepthPrefixCarrier (n := n) A y) ⊆
        Set.range
          (primeResidueValuationUpperEndDepthPrefixCarrier (n := n + 1) A y) := by
    rintro _ ⟨q, rfl⟩
    let q' : PrimeResidueValuationDepthPrefixIndex (n + 1) A :=
      ⟨⟨⟨q.1.1.1, by omega⟩, q.1.2⟩, by
        change q.1.1.1 ≠ n + 1 + 1
        omega⟩
    exact ⟨q', rfl⟩
  have hle : primeResidueValuationUpperEndDepthPrefixField n A y ≤
      primeResidueValuationUpperEndDepthPrefixField (n + 1) A y := by
    unfold primeResidueValuationUpperEndDepthPrefixField
    unfold GaloisForLFunctions.differentialAdjoin
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨x, hx, k, rfl⟩
    exact IntermediateField.subset_adjoin ℂ _ ⟨x, hrange hx, k, rfl⟩
  let vacuum : ∀ i, A i := fun _ => 1
  have hnot : primeResidueValuationUpperEndCarrier A y (n + 1) vacuum ∉
      primeResidueValuationUpperEndDepthPrefixField n A y :=
    cofiniteTailDenseOn_primeResidueValuationUpperEndNextLayer_not_mem_prefix
      n A y hy vacuum
  have hmem : primeResidueValuationUpperEndCarrier A y (n + 1) vacuum ∈
      primeResidueValuationUpperEndDepthPrefixField (n + 1) A y := by
    let q : PrimeResidueValuationDepthPrefixIndex (n + 1) A :=
      ⟨⟨⟨n + 1, by omega⟩, vacuum⟩, by
        change n + 1 ≠ n + 1 + 1
        omega⟩
    change primeResidueValuationUpperEndCarrier A y (n + 1) vacuum ∈
      GaloisForLFunctions.differentialAdjoin ℂ
        (Set.range
          (primeResidueValuationUpperEndDepthPrefixCarrier (n := n + 1) A y))
    exact GaloisForLFunctions.subset_differentialAdjoin _ _ ⟨q, rfl⟩
  exact lt_of_le_of_ne hle fun heq => hnot (heq ▸ hmem)

/-- **Analytic finite-prefix fusion escape.** Both analytic input carriers belong to the complete
depth prefix. Their underlying prime-local coefficient columns fuse exactly to the union-support
next layer, but the corresponding actual meromorphic Dirichlet germ is not in the prefix field. -/
theorem cofiniteTailDenseOn_primeResidueValuationUpperEndFusion_escapes_completePrefix
    (n : ℕ) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Type u) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, One (A i)]
    [TopologicalSpace (∀ i, A i)] [DiscreteTopology (∀ i, A i)]
    (y : Nat.Primes → ∀ i, A i)
    (hy : CofiniteTailDenseOn y Set.univ)
    (z w : ∀ i, A i)
    (hdis : Disjoint (pointedSupport A z) (pointedSupport A w)) :
    primeResidueValuationUpperEndCarrier A y n z ∈
        primeResidueValuationUpperEndDepthPrefixField n A y ∧
      primeResidueValuationUpperEndCarrier A y 0 w ∈
        primeResidueValuationUpperEndDepthPrefixField n A y ∧
      primeValuationFusion n 0
          (primeResidueValuationObservableColumn A y n
            (anchoredRestrictedProductBasis A z))
          (primeResidueValuationObservableColumn A y 0
            (anchoredRestrictedProductBasis A w)) =
        primeResidueValuationObservableColumn A y (n + 1)
          (anchoredRestrictedProductBasis A (pointedUnion A z w)) ∧
      primeResidueValuationUpperEndCarrier A y (n + 1) (pointedUnion A z w) ∉
        primeResidueValuationUpperEndDepthPrefixField n A y := by
  let inputN : PrimeResidueValuationDepthPrefixIndex n A :=
    ⟨⟨⟨n, by omega⟩, z⟩, by
      change n ≠ n + 1
      omega⟩
  let inputZero : PrimeResidueValuationDepthPrefixIndex n A :=
    ⟨⟨⟨0, by omega⟩, w⟩, by
      change 0 ≠ n + 1
      omega⟩
  constructor
  · change primeResidueValuationUpperEndCarrier A y n z ∈
      GaloisForLFunctions.differentialAdjoin ℂ
        (Set.range (primeResidueValuationUpperEndDepthPrefixCarrier (n := n) A y))
    exact GaloisForLFunctions.subset_differentialAdjoin _ _ ⟨inputN, rfl⟩
  constructor
  · change primeResidueValuationUpperEndCarrier A y 0 w ∈
      GaloisForLFunctions.differentialAdjoin ℂ
        (Set.range (primeResidueValuationUpperEndDepthPrefixCarrier (n := n) A y))
    exact GaloisForLFunctions.subset_differentialAdjoin _ _ ⟨inputZero, rfl⟩
  constructor
  · simpa only [Nat.add_zero] using
      (primeResidueValuationAnchoredBasisColumn_fusion_of_disjoint
        A y n 0 z w hdis)
  · exact cofiniteTailDenseOn_primeResidueValuationUpperEndNextLayer_not_mem_prefix
      n A y hy (pointedUnion A z w)

/-- **Actual-prime analytic source-creation tower.** For simultaneous unit residues modulo
pairwise-coprime moduli, every next analytic valuation layer is relatively HT over the complete
earlier prefix, has exact rank `∏_i φ(q_i)`, and strictly enlarges the prefix field. -/
theorem pairwiseCoprimePrimeResidueValuationUpperEndSourceCreationTower
    (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (modulus : ι → ℕ) [∀ i, NeZero (modulus i)]
    [NeZero (∏ i, modulus i)]
    (h : Pairwise (Function.onFun Nat.Coprime modulus)) :
    let A := fun i => (ZMod (modulus i))ˣ
    let y := pairwiseCoprimePrimeUnitResidueProfile modulus h
    GaloisForLFunctions.DifferentialIndependent
        (primeResidueValuationUpperEndDepthPrefixField n A y)
        (primeResidueValuationUpperEndNextLayerCarrier (n := n) A y) ∧
      Nat.card (PrimeResidueValuationNextLayerIndex n A) =
        ∏ i, Nat.totient (modulus i) ∧
      primeResidueValuationUpperEndDepthPrefixField n A y <
        primeResidueValuationUpperEndDepthPrefixField (n + 1) A y := by
  dsimp only
  let A := fun i => (ZMod (modulus i))ˣ
  let y := pairwiseCoprimePrimeUnitResidueProfile modulus h
  letI : TopologicalSpace (∀ i, A i) := ⊥
  letI : DiscreteTopology (∀ i, A i) := ⟨rfl⟩
  have hy : CofiniteTailDenseOn y Set.univ :=
    cofiniteTailDenseOn_univ_of_recurringValueSet_eq_univ y
      (recurringValueSet_pairwiseCoprimePrimeUnitResidueProfile modulus h)
  obtain ⟨hrel, hrank⟩ :=
    cofiniteTailDenseOn_primeResidueValuationUpperEndNextLayer_relativeHT n A y hy
  refine ⟨hrel, ?_,
    cofiniteTailDenseOn_primeResidueValuationUpperEndDepthPrefixField_strictMono
      n A y hy⟩
  dsimp [A] at hrank ⊢
  simpa only [ZMod.card_units_eq_totient] using hrank

end

end GaloisForLFunctions.HTGeometry
