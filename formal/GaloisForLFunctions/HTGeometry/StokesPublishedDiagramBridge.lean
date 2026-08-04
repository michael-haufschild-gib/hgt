import GaloisForLFunctions.HTGeometry.StokesGlobalPuiseuxWittLaw
import GaloisForLFunctions.HTGeometry.StokesEquivariantSpectrumIntegrality

open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes.OrbitCoareaDatum

noncomputable section

variable {n m e K N : ℕ}

/-- Boalch--Yamakawa--Douçot core adjacency entry:
`Irr Hom - ramification product`, with the published diagonal correction `+1`. -/
def publishedCoreAdjacency (d : OrbitCoareaDatum n m e) (i j : Fin n) : ℝ :=
  d.homIrregularity i j - d.ramification i * d.ramification j +
    if i = j then 1 else 0

/-- Symmetric generalized Cartan entry `2 Id - B` of the published core diagram. -/
def publishedCoreCartan (d : OrbitCoareaDatum n m e) (i j : Fin n) : ℝ :=
  (if i = j then 2 else 0) - d.publishedCoreAdjacency i j

/-- Quadratic form of the published generalized Cartan matrix. -/
def publishedCoreCartanQuadratic (d : OrbitCoareaDatum n m e)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j * d.publishedCoreCartan i j

theorem publishedCoreCartan_apply (d : OrbitCoareaDatum n m e) (i j : Fin n) :
    d.publishedCoreCartan i j =
      (if i = j then 1 else 0) +
        d.ramification i * d.ramification j - d.homIrregularity i j := by
  by_cases hij : i = j
  · simp [publishedCoreCartan, publishedCoreAdjacency, hij]
    ring
  · simp [publishedCoreCartan, publishedCoreAdjacency, hij]

theorem publishedCoreAdjacency_symm (d : OrbitCoareaDatum n m e) (i j : Fin n) :
    d.publishedCoreAdjacency i j = d.publishedCoreAdjacency j i := by
  rw [publishedCoreAdjacency, publishedCoreAdjacency, d.homIrregularity_symm]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji, mul_comm]

private theorem diagonal_double_sum (x : Fin n → ℝ) :
    (∑ i, ∑ j, x i * x j * (if i = j then 1 else 0)) = ∑ i, x i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

private theorem ramification_double_sum (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    (∑ i, ∑ j, x i * x j * (d.ramification i * d.ramification j)) =
      (∑ i, x i * d.ramification i) ^ 2 := by
  calc
    (∑ i, ∑ j, x i * x j * (d.ramification i * d.ramification j)) =
        ∑ i, ∑ j, (x i * d.ramification i) * (x j * d.ramification j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ i, x i * d.ramification i) *
        (∑ j, x j * d.ramification j) := by rw [double_sum_mul]
    _ = (∑ i, x i * d.ramification i) ^ 2 := by ring

/-- Exact interface theorem: the generalized Cartan quadratic form from the published diagram
formula is definitionally the coefficient/contact Stokes polarization. -/
theorem publishedCoreCartanQuadratic_eq_cartanQuadratic
    (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    d.publishedCoreCartanQuadratic x = d.cartanQuadratic x := by
  calc
    d.publishedCoreCartanQuadratic x =
        ∑ i, ∑ j, x i * x j *
          ((if i = j then 1 else 0) +
            d.ramification i * d.ramification j - d.homIrregularity i j) := by
              unfold publishedCoreCartanQuadratic
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [d.publishedCoreCartan_apply]
    _ = ∑ i, ∑ j,
          (x i * x j * (if i = j then 1 else 0) +
            x i * x j * (d.ramification i * d.ramification j) -
            x i * x j * d.homIrregularity i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ i, ∑ j, x i * x j * (if i = j then 1 else 0)) +
        (∑ i, ∑ j, x i * x j * (d.ramification i * d.ramification j)) -
        (∑ i, ∑ j, x i * x j * d.homIrregularity i j) := by
          simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [diagonal_double_sum, ramification_double_sum]
  rw [← d.physicalRank_eq_ramification_sum]
  change d.terminalEnergy x + d.physicalRank x ^ 2 - d.orbitContactPairing x =
    d.cartanQuadratic x
  rw [d.orbitContactPairing_eq_contactPairing]
  rfl

/-! ## Coefficient-generated published Cartan form -/

/-- The published core Cartan matrix, realized as a quadratic form directly from finite
Puiseux coefficients.  Its value theorem below identifies it with the matrix formula, so the
inertia statement is about the published diagram rather than an auxiliary contact function. -/
noncomputable def coefficientPublishedCoreCartanForm
    (d : PuiseuxOrbitCoareaDatum n m K N) : QuadraticForm ℝ (Fin n → ℝ) :=
  GlobalPuiseuxWitt.localWittForm d

theorem coefficientPublishedCoreCartanForm_apply
    (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ) :
    coefficientPublishedCoreCartanForm d x =
      d.toOrbitCoareaDatum.publishedCoreCartanQuadratic x := by
  rw [coefficientPublishedCoreCartanForm,
    GlobalPuiseuxWitt.localWittForm_apply,
    publishedCoreCartanQuadratic_eq_cartanQuadratic]

/-- **Published-diagram Lorentz law.** For every core diagram generated by finite Puiseux
coefficients, negative inertia plus Cartan nullity is at most one.  In particular a negative
line and an affine radical line cannot coexist. -/
theorem coefficientPublishedCoreCartanForm_sigNeg_add_radical_finrank_le_one
    (d : PuiseuxOrbitCoareaDatum n m K N) :
    sigNeg (coefficientPublishedCoreCartanForm d) +
      Module.finrank ℝ (coefficientPublishedCoreCartanForm d).radical ≤ 1 := by
  apply GlobalPuiseuxWitt.sigNeg_add_radical_finrank_le_one_of_pos_on_ker
    (coefficientPublishedCoreCartanForm d)
    (GlobalPuiseuxWitt.localRankLinear d)
  intro x hrank hx
  rw [coefficientPublishedCoreCartanForm,
    GlobalPuiseuxWitt.localWittForm_apply]
  change d.toOrbitCoareaDatum.physicalRank x = 0 at hrank
  exact d.cartanQuadratic_pos_of_physicalRank_eq_zero hrank hx

/-! ## Genuine monodromy-orbit specialization -/

/-- Published core Cartan form for the Stokes circles generated by an actual cyclic Puiseux
continuation action. -/
noncomputable def equivariantPublishedCoreCartanForm
    (p : EquivariantFinitePuiseuxFamily m K N) :
    QuadraticForm ℝ (Fin p.orbitClassCount → ℝ) :=
  coefficientPublishedCoreCartanForm p.toPuiseuxOrbitCoareaDatum

theorem equivariantPublishedCoreCartanForm_apply
    (p : EquivariantFinitePuiseuxFamily m K N)
    (x : Fin p.orbitClassCount → ℝ) :
    equivariantPublishedCoreCartanForm p x =
      p.toPuiseuxOrbitCoareaDatum.toOrbitCoareaDatum.publishedCoreCartanQuadratic x :=
  coefficientPublishedCoreCartanForm_apply p.toPuiseuxOrbitCoareaDatum x

/-- **Analytic-continuation orbit Lorentz law.** The published Cartan form attached to the
genuine cyclic Stokes circles of an equivariant finite Puiseux spectrum has at most one
nonpositive channel, counted jointly by negative inertia and nullity. -/
theorem equivariantPublishedCoreCartanForm_sigNeg_add_radical_finrank_le_one
    (p : EquivariantFinitePuiseuxFamily m K N) :
    sigNeg (equivariantPublishedCoreCartanForm p) +
      Module.finrank ℝ (equivariantPublishedCoreCartanForm p).radical ≤ 1 :=
  coefficientPublishedCoreCartanForm_sigNeg_add_radical_finrank_le_one
    p.toPuiseuxOrbitCoareaDatum

end

end GaloisForLFunctions.IrregularStokes.OrbitCoareaDatum
