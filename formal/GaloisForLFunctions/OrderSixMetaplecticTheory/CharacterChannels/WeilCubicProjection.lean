import GaloisForLFunctions.OrderSixMetaplecticTheory.TheOrderSixFamilyIsOrthogonalToTheUntwistedSquare

/-!
# The ramified cubic channel of the Weil phase

The actual phase `Γ(c)χ₂(c)` modulo four pairs only with the inverse cubic
rotation component of a class function. The three-term character projector
extracts that component without changing the signed pairing. This strengthens
mean-zero orthogonality to an exact projection identity, using the character
projection mechanism of Lemma 5.3 of arXiv:2610.23742.

The identity separates the local phase from any proposed class-restricted
residues; it does not assert their existence or evaluate them.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein

abbrev ResidueFour := O ⧸ Ideal.span {(4 : O)}

local instance : Finite ResidueFour :=
  (Ideal.span {(4 : O)}).finiteQuotientOfFreeOfNeBot
    (fun h => (by norm_num : (4 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
local instance : Fintype ResidueFour := Fintype.ofFinite _

/-- Multiplication by the cubic unit on residues modulo four. -/
def rotate (c : ResidueFour) : ResidueFour := Ideal.Quotient.mk _ omega * c

/-- The actual ramified phase of the squarefree order-six row. -/
def phase (c : ResidueFour) : ℂ := fixedDualAverage (rep4 c) * cubicTwoChar (rep4 c)

theorem phase_mk (c : O) :
    phase (Ideal.Quotient.mk _ c) = fixedDualAverage c * cubicTwoChar c := by
  have h := mk_rep4 (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c)
  have h4 : (4 : O) ∣ rep4 (Ideal.Quotient.mk _ c) - c :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h)
  have h2 := (show (2 : O) ∣ 4 from ⟨2, by norm_num⟩).trans h4
  rw [phase, fixedDualAverage_eq_of_mod_four _ _ h, cubicTwoChar_congr h2]

theorem rotate_three (c : ResidueFour) : rotate (rotate (rotate c)) = c := by
  have h : (Ideal.Quotient.mk (Ideal.span {(4 : O)}) omega) ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  calc
    rotate (rotate (rotate c)) = (Ideal.Quotient.mk _ omega) ^ 3 * c := by
      dsimp [rotate]
      ring
    _ = c := by rw [h, one_mul]

/-- The Weil factor is invariant; the cubic factor supplies the rotation eigenvalue. -/
theorem phase_rotate (c : ResidueFour) :
    phase (rotate c) = cubicTwoChar omega * phase c := by
  have hcong : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (rep4 (rotate c)) =
      Ideal.Quotient.mk _ (omega * rep4 c) := by
    rw [mk_rep4, map_mul, mk_rep4]
    rfl
  have h4 : (4 : O) ∣ rep4 (rotate c) - omega * rep4 c :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hcong)
  have h2 := (show (2 : O) ∣ 4 from ⟨2, by norm_num⟩).trans h4
  rw [phase, fixedDualAverage_eq_of_mod_four _ _ hcong, fixedDualAverage_omega_mul,
    cubicTwoChar_congr h2, cubicTwoChar_mul, phase]
  ring

private theorem cubicTwoChar_omega_cube : cubicTwoChar omega ^ 3 = 1 := by
  rw [cubicTwoChar_omega, ← pow_mul, Nat.mul_comm 2 3, pow_mul,
    ← map_pow, omega_primitive.pow_eq_one, map_one, one_pow]

/-- The inverse cubic rotation component of an arbitrary class function. -/
def cubicProjection (f : ResidueFour → ℂ) (c : ResidueFour) : ℂ :=
  (f c + cubicTwoChar omega * f (rotate c) +
    cubicTwoChar omega ^ 2 * f (rotate (rotate c))) / 3

/-- The extracted component has exactly the inverse eigenvalue to the row phase. -/
theorem cubicProjection_rotate (f : ResidueFour → ℂ) (c : ResidueFour) :
    cubicTwoChar omega * cubicProjection f (rotate c) = cubicProjection f c := by
  dsimp only [cubicProjection]
  rw [rotate_three]
  linear_combination (f c / 3) * cubicTwoChar_omega_cube

/-- Repeating the character projection loses no further information. -/
theorem cubicProjection_idempotent (f : ResidueFour → ℂ) :
    cubicProjection (cubicProjection f) = cubicProjection f := by
  funext c
  have h₂ : cubicTwoChar omega ^ 2 * cubicProjection f (rotate (rotate c)) =
      cubicProjection f c := by
    calc
      _ = cubicTwoChar omega *
          (cubicTwoChar omega * cubicProjection f (rotate (rotate c))) := by ring
      _ = cubicTwoChar omega * cubicProjection f (rotate c) := by
        rw [cubicProjection_rotate]
      _ = cubicProjection f c := cubicProjection_rotate f c
  rw [cubicProjection, cubicProjection_rotate, h₂]
  ring

/-- Signed pairing of a class function with the actual order-six phase. -/
def weightedSum (f : ResidueFour → ℂ) : ℂ := ∑ c, phase c * f c

theorem weightedSum_rotation (f : ResidueFour → ℂ) :
    weightedSum f = cubicTwoChar omega * weightedSum (fun c => f (rotate c)) := by
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) omega) :=
    (omega_primitive.isUnit (by norm_num)).map _
  calc
    weightedSum f = ∑ c, phase (rotate c) * f (rotate c) := by
      simpa only [weightedSum, rotate, Units.mulLeft_apply, IsUnit.unit_spec] using
        (Equiv.sum_comp (Units.mulLeft hu.unit) (fun c => phase c * f c)).symm
    _ = cubicTwoChar omega * weightedSum (fun c => f (rotate c)) := by
      simp only [phase_rotate, weightedSum, Finset.mul_sum, mul_assoc]

/-- Only the inverse cubic component contributes, with the full Weil-phase signs preserved. -/
theorem weightedSum_eq_projected (f : ResidueFour → ℂ) :
    weightedSum (cubicProjection f) = weightedSum f := by
  have h₁ := weightedSum_rotation f
  have h₂ : cubicTwoChar omega ^ 2 * weightedSum (fun c => f (rotate (rotate c))) =
      weightedSum f := by
    calc
      _ = cubicTwoChar omega *
          (cubicTwoChar omega * weightedSum (fun c => f (rotate (rotate c)))) := by ring
      _ = cubicTwoChar omega * weightedSum (fun c => f (rotate c)) := by
        rw [← weightedSum_rotation (fun c => f (rotate c))]
      _ = weightedSum f := h₁.symm
  calc
    weightedSum (cubicProjection f) = ∑ c,
        (phase c * f c + cubicTwoChar omega * (phase c * f (rotate c)) +
          cubicTwoChar omega ^ 2 * (phase c * f (rotate (rotate c)))) / 3 := by
      apply Finset.sum_congr rfl
      intro c _
      dsimp only [cubicProjection]
      ring
    _ = (weightedSum f + cubicTwoChar omega * weightedSum (fun c => f (rotate c)) +
        cubicTwoChar omega ^ 2 * weightedSum (fun c => f (rotate (rotate c)))) / 3 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    _ = weightedSum f := by rw [← h₁, h₂]; ring

/-- Squared cubic Gauss sums collected by their actual residue class modulo four. -/
def gaussSquareClassMass (S : Finset O) (w : O → ℂ) (r : ResidueFour) : ℂ :=
  ∑ c ∈ S.filter (fun c => Ideal.Quotient.mk (Ideal.span {(4 : O)}) c = r),
    normalizedCubicUnitGauss c ^ 2 * w c

/-- The finite order-six row sum is exactly the projected class pairing; no absolute values occur. -/
theorem finite_row_sum_eq_projected (S : Finset O) (w : O → ℂ) :
    (∑ c ∈ S, fixedDualAverage c * cubicTwoChar c * normalizedCubicUnitGauss c ^ 2 * w c) =
      weightedSum (cubicProjection (gaussSquareClassMass S w)) := by
  rw [weightedSum_eq_projected]
  unfold weightedSum gaussSquareClassMass
  simp_rw [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, phase_mk]
  ring

#print axioms cubicProjection_rotate
#print axioms cubicProjection_idempotent
#print axioms weightedSum_eq_projected
#print axioms finite_row_sum_eq_projected

end GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
