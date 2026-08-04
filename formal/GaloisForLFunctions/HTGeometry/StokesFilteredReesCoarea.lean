import GaloisForLFunctions.HTGeometry.StokesGaloisMicrolocalCoarea

/-!
# Filtered Rees deformation of Stokes coarea

Each canonical threshold cut is one associated-graded channel.  Independent Rees parameters scale
those channels.  Unit specialization recovers the Stokes Cartan form; zero specialization contracts
selected filtration intervals; the associated-graded norm is exactly the positive block coarea.
The sole rank channel is independent of all Rees parameters, so every nonnegative specialization
remains strictly positive on physical-rank-zero charges.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

noncomputable section

namespace OrbitCoareaDatum

variable {n m e : ℕ}

/-- Charge carried by one threshold-class graded channel. -/
def cutCharge (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) (edge : Fin e) : ℝ :=
  ∑ a, d.liftCharge x a * d.cuts.side edge a

/-- Multi-Rees deformation of the positive block energy. -/
def reesBlockEnergy (d : OrbitCoareaDatum n m e) (parameter : Fin e → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ edge, parameter edge * d.cuts.length edge * d.cutCharge x edge ^ 2

/-- Rees-deformed Cartan quadratic form. -/
def reesCartanQuadratic (d : OrbitCoareaDatum n m e) (parameter : Fin e → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  d.terminalEnergy x + d.reesBlockEnergy parameter x -
    (d.cuts.root - 1) * d.physicalRank x ^ 2

/-- Associated-graded coordinate of one cut channel. -/
def gradedChannel (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ)
    (edge : Fin e) : ℝ :=
  Real.sqrt (d.cuts.length edge) * d.cutCharge x edge

/-- Associated-graded squared norm is exactly block coarea energy. -/
theorem sum_gradedChannel_sq_eq_blockEnergy
    (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    (∑ edge, d.gradedChannel x edge ^ 2) = d.blockEnergy x := by
  simp only [gradedChannel, blockEnergy, cutCharge, mul_pow,
    Real.sq_sqrt (d.cuts.length_pos _).le]

/-- Unit Rees parameter recovers undeformed block energy. -/
theorem reesBlockEnergy_one (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    d.reesBlockEnergy (fun _ => 1) x = d.blockEnergy x := by
  simp [reesBlockEnergy, blockEnergy, cutCharge]

/-- Unit specialization recovers the original Cartan form. -/
theorem reesCartanQuadratic_one (d : OrbitCoareaDatum n m e) (x : Fin n → ℝ) :
    d.reesCartanQuadratic (fun _ => 1) x = d.cartanQuadratic x := by
  rw [reesCartanQuadratic, d.reesBlockEnergy_one,
    d.cartanQuadratic_eq_positive_sub_onePort]

/-- Nonnegative Rees parameters preserve nonnegativity of every local channel. -/
theorem reesBlockEnergy_nonneg (d : OrbitCoareaDatum n m e)
    {parameter : Fin e → ℝ} (hparameter : ∀ edge, 0 ≤ parameter edge)
    (x : Fin n → ℝ) : 0 ≤ d.reesBlockEnergy parameter x := by
  apply Finset.sum_nonneg
  intro edge _
  exact mul_nonneg (mul_nonneg (hparameter edge) (d.cuts.length_pos edge).le) (sq_nonneg _)

/-- Every nonnegative Rees specialization remains positive on physical-rank-zero charges. -/
theorem reesCartanQuadratic_pos_of_physicalRank_eq_zero
    (d : OrbitCoareaDatum n m e) {parameter : Fin e → ℝ}
    (hparameter : ∀ edge, 0 ≤ parameter edge) {x : Fin n → ℝ}
    (hrank : d.physicalRank x = 0) (hx : x ≠ 0) :
    0 < d.reesCartanQuadratic parameter x := by
  rw [reesCartanQuadratic, hrank]
  have ht := d.terminalEnergy_pos hx
  have hb := d.reesBlockEnergy_nonneg hparameter x
  nlinarith

/-- Set contracted filtration intervals to zero while retaining all other parameters. -/
def specialize (parameter : Fin e → ℝ) (retained : Fin e → Prop)
    [DecidablePred retained] (edge : Fin e) : ℝ :=
  if retained edge then parameter edge else 0

/-- Specialization is exactly deletion of contracted graded channels. -/
theorem reesBlockEnergy_specialize (d : OrbitCoareaDatum n m e)
    (parameter : Fin e → ℝ) (retained : Fin e → Prop) [DecidablePred retained]
    (x : Fin n → ℝ) :
    d.reesBlockEnergy (specialize parameter retained) x =
      ∑ edge ∈ Finset.univ.filter retained,
        parameter edge * d.cuts.length edge * d.cutCharge x edge ^ 2 := by
  simp only [reesBlockEnergy, specialize]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite]
  simp

/-- Changing Rees parameters changes only local graded channels; global rank channel is fixed. -/
theorem reesCartan_parameter_difference (d : OrbitCoareaDatum n m e)
    (left right : Fin e → ℝ) (x : Fin n → ℝ) :
    d.reesCartanQuadratic left x - d.reesCartanQuadratic right x =
      d.reesBlockEnergy left x - d.reesBlockEnergy right x := by
  simp only [reesCartanQuadratic]
  ring

end OrbitCoareaDatum
end
end IrregularStokes
end GaloisForLFunctions
