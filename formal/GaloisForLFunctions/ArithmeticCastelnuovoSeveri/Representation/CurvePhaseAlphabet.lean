import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Representation.EndpointCalibration
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CycleCharacterIdentification

/-!
# Positive phase alphabets and the purity boundary for curves

The imaginary parts of all periodic zeros give a positive summable endpoint alphabet for every
nonempty curve datum. Its normalized independent-color character exists even for impure data.
Coordinatewise agreement with the actual endpoint alphabet holds exactly when every Frobenius
eigenvalue is unitary; a positive phase model alone therefore cannot establish purity.
-/

open scoped BigOperators ComplexOrder Classical
noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open SymmetricCharacters
namespace CurveDatum
variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- Endpoint weight after projecting a periodic zero onto the critical line. -/
def phaseEndpointWeight (p : ι × ℤ) : ℝ :=
  1 / (1 / 4 + (D.zetaZero p.1 p.2).im ^ 2)

theorem phaseEndpointWeight_pos (p : ι × ℤ) : 0 < D.phaseEndpointWeight p := by
  unfold phaseEndpointWeight
  positivity

/-- The periodic height bound dominates the alphabet by a summable quadratic tail. -/
theorem phaseEndpointWeight_le (i : ι) (k : ℤ) :
    D.phaseEndpointWeight (i, k) ≤
      (2 / min (1 / 4) ((D.period / 2) ^ 2)) * (1 / (1 + |(k : ℝ)|) ^ 2) := by
  let c := D.period / 2
  let m := min (1 / 4) (c ^ 2)
  have hc : 0 < c := by dsimp [c]; linarith [D.period_pos]
  have hm : 0 < m := lt_min (by positivity) (sq_pos_of_pos hc)
  have hm1 : m ≤ 1 / 4 := min_le_left _ _
  have hm2 : m ≤ c ^ 2 := min_le_right _ _
  have hk : ((k : ℝ) * c) ^ 2 ≤ (D.zetaZero i k).im ^ 2 :=
    D.sq_le_sq_im_zetaZero i k
  have hsq : (1 + |(k : ℝ)|) ^ 2 ≤ 2 * (1 + (k : ℝ) ^ 2) := by
    nlinarith only [sq_abs (k : ℝ), sq_nonneg (|(k : ℝ)| - 1)]
  have hcx : m * (k : ℝ) ^ 2 ≤ ((k : ℝ) * c) ^ 2 := by
    rw [mul_pow]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm2 (sq_nonneg (k : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ m / 2 by positivity)
  have hlow : m / 2 * (1 + |(k : ℝ)|) ^ 2 ≤ 1 / 4 + (D.zetaZero i k).im ^ 2 := by
    nlinarith only [h2, hcx, hk, hm1]
  have hden : 0 < 1 / 4 + (D.zetaZero i k).im ^ 2 := by positivity
  have hpos : 0 < (1 + |(k : ℝ)|) ^ 2 := by positivity
  change 1 / (1 / 4 + (D.zetaZero i k).im ^ 2) ≤ (2 / m) * (1 / (1 + |(k : ℝ)|) ^ 2)
  rw [div_le_iff₀ hden]
  calc
    1 = ((2 / m) * (1 / (1 + |(k : ℝ)|) ^ 2)) *
        (m / 2 * (1 + |(k : ℝ)|) ^ 2) := by field_simp [hm.ne', hpos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

theorem summable_phaseEndpointWeight : Summable D.phaseEndpointWeight := by
  let C := 2 / min (1 / 4) ((D.period / 2) ^ 2)
  have h1 : Summable fun _ : ι => (1 : ℝ) := (hasSum_fintype fun _ : ι => (1 : ℝ)).summable
  have hg : Summable fun p : ι × ℤ => C * (1 * (1 / (1 + |(p.2 : ℝ)|) ^ 2)) :=
    (h1.mul_of_nonneg RHTower.hasSum_inv_one_add_abs_sq.summable (fun _ => zero_le_one)
      (fun _ => by positivity)).mul_left C
  apply Summable.of_nonneg_of_le (fun p => (D.phaseEndpointWeight_pos p).le) _ hg
  intro p
  simpa only [one_mul] using D.phaseEndpointWeight_le p.1 p.2

/-- Total mass of the positive phase alphabet. -/
def phaseEndpointMass : ℝ := ∑' p, D.phaseEndpointWeight p

theorem phaseEndpointMass_pos [Nonempty ι] : 0 < D.phaseEndpointMass := by
  let i : ι := Classical.choice inferInstance
  exact lt_of_lt_of_le (D.phaseEndpointWeight_pos (i, 0))
    (D.summable_phaseEndpointWeight.le_tsum (i, 0)
      (fun p _ => (D.phaseEndpointWeight_pos p).le))

/-- Normalized phase weights, including every periodic copy. -/
def phaseEndpointColor [Nonempty ι] (p : ι × ℤ) : NNReal :=
  ⟨D.phaseEndpointWeight p / D.phaseEndpointMass,
    div_nonneg (D.phaseEndpointWeight_pos p).le D.phaseEndpointMass_pos.le⟩

theorem summable_phaseEndpointColor [Nonempty ι] :
    Summable (fun p => (D.phaseEndpointColor p : ℝ)) :=
  D.summable_phaseEndpointWeight.div_const D.phaseEndpointMass

theorem tsum_phaseEndpointColor [Nonempty ι] : (∑' p, (D.phaseEndpointColor p : ℝ)) = 1 := by
  change (∑' p, D.phaseEndpointWeight p / D.phaseEndpointMass) = 1
  rw [tsum_div_const]
  exact div_self D.phaseEndpointMass_pos.ne'

private theorem endpointCoordinate_critical {z : ℂ} (hz : z.re = 1 / 2) :
    endpointCoordinate z = ((1 / (1 / 4 + z.im ^ 2) : ℝ) : ℂ) := by
  have he : z * (1 - z) = ((1 / 4 + z.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, Complex.ofReal_re, hz]
      ring
    · simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, Complex.ofReal_im, hz]
      ring
  rw [endpointCoordinate, he]
  push_cast
  simp only [one_div]

/-- Agreement with the actual endpoint coordinates detects Frobenius purity. -/
theorem phaseEndpointWeight_eq_endpoint_iff :
    (∀ i k, (D.phaseEndpointWeight (i, k) : ℂ) = endpointCoordinate (D.zetaZero i k)) ↔
      ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · intro h i
    apply (D.endpoint_firstPeriod_real_iff i).mp
    have hi := congrArg Complex.im (h i 1)
    simpa only [Complex.ofReal_im] using hi.symm
  · intro h i k
    exact (endpointCoordinate_critical ((D.zetaZero_re_eq_half_iff i k).mpr (h i))).symm

/-- The same coordinatewise purity test survives normalization by the positive phase mass. -/
theorem phaseEndpointColor_eq_endpoint_iff [Nonempty ι] :
    (∀ i k, ((D.phaseEndpointColor (i, k) : ℝ) : ℂ) =
      endpointCoordinate (D.zetaZero i k) / (D.phaseEndpointMass : ℂ)) ↔
      ∀ i, ‖D.β i‖ = 1 := by
  have hM : (D.phaseEndpointMass : ℂ) ≠ 0 := by exact_mod_cast D.phaseEndpointMass_pos.ne'
  constructor
  · intro h
    apply D.phaseEndpointWeight_eq_endpoint_iff.mp
    intro i k
    have he := h i k
    change ((D.phaseEndpointWeight (i, k) / D.phaseEndpointMass : ℝ) : ℂ) = _ at he
    push_cast at he
    field_simp [hM] at he
    exact he
  · intro h i k
    change ((D.phaseEndpointWeight (i, k) / D.phaseEndpointMass : ℝ) : ℂ) = _
    push_cast
    rw [D.phaseEndpointWeight_eq_endpoint_iff.mpr h i k]

/-- Every nonempty curve datum has a positive phase character, independently of purity. -/
theorem phaseEndpoint_positiveCycleFamily [Nonempty ι] :
    PositiveCycleFamily (fun n => ∑' p, (D.phaseEndpointColor p : ℝ) ^ (n + 1)) :=
  wordCharacter_positiveCycleFamily D.phaseEndpointColor
    D.summable_phaseEndpointColor D.tsum_phaseEndpointColor
end CurveDatum

/-- The golden fake has a positive phase character but fails the exact endpoint identification. -/
theorem golden_phase_character_boundary :
    PositiveCycleFamily (fun n => ∑' p, (goldenDatum.phaseEndpointColor p : ℝ) ^ (n + 1)) ∧
    ¬ (∀ i k, ((goldenDatum.phaseEndpointColor (i, k) : ℝ) : ℂ) =
      endpointCoordinate (goldenDatum.zetaZero i k) / (goldenDatum.phaseEndpointMass : ℂ)) := by
  refine ⟨goldenDatum.phaseEndpoint_positiveCycleFamily, ?_⟩
  rw [goldenDatum.phaseEndpointColor_eq_endpoint_iff]
  exact goldenDatum_not_unitary

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
