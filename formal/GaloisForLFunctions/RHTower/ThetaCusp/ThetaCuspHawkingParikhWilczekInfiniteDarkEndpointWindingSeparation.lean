import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekCountableMatrixThreeMomentNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekEndpointWindingPolynomialDarkSeparation

/-!
# PW endpoint winding defeats the infinite three-moment dark kernel

The countable PW recoil no-go contains a nonzero positive-semidefinite rank-one kernel with
infinite diagonal support that is invisible to the complete three-moment recoil family.  Its
generating vector is

`w_n = (1/2)^n + 2 delta_(n=0) - 4 delta_(n=1)`.

This module evaluates that exact corpus counterexample on the literal finite-energy PW endpoint
winding.  For `q=exp(-1/(4 epsilon))` and `epsilon>0`, the response converges to

`q(1-q)(3-2q)/(1-q/2)`,

which is strictly positive because `0<q<1`.  The associated countable rank-one matrix energy is
the square of the response and is therefore strictly positive.  Thus the source-native
nonperturbative endpoint channel escapes both the finite polynomial dark families and the known
admissible infinite-support three-moment obstruction.

`[NEW] [SOURCE-EXACT INFINITE-SUPPORT SEPARATION] [GEOMETRIC GENERATING FUNCTION]
[COUNTABLE POSITIVE ENERGY] [LEAN-PROVED]`
-/

open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Exact generating-function law for the corpus's infinite-support PW dark vector. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkWeight_endpointPower_hasSum
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ =>
      schwarzschildParikhWilczekInfiniteGradeDarkWeight n * q ^ (n + 1))
      (q * (1 - q) * (3 - 2 * q) / (1 - q / 2)) := by
  have hratio0 : 0 ≤ q / 2 := by positivity
  have hratio1 : q / 2 < 1 := by linarith
  have hgeo0 : HasSum (fun n : ℕ => (q / 2) ^ n) (1 - q / 2)⁻¹ :=
    hasSum_geometric_of_lt_one hratio0 hratio1
  have hgeo : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * q ^ (n + 1))
      (q / (1 - q / 2)) := by
    have hgeo' : HasSum (fun n : ℕ => q * (q / 2) ^ n)
        (q * (1 - q / 2)⁻¹) := hgeo0.mul_left q
    have hgeoPower : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * q ^ (n + 1))
        (q * (1 - q / 2)⁻¹) := hgeo'.congr_fun (fun n => by
      rw [pow_succ]
      simp only [div_eq_mul_inv, mul_pow]
      ring)
    simpa only [div_eq_mul_inv] using hgeoPower
  have hzero := hasSum_ite_eq (0 : ℕ) (2 * q)
  have hone := hasSum_ite_eq (1 : ℕ) (-4 * q ^ (2 : ℕ))
  have hraw : HasSum (fun n : ℕ =>
      schwarzschildParikhWilczekInfiniteGradeDarkWeight n * q ^ (n + 1))
      ((q / (1 - q / 2) + 2 * q) + (-4 * q ^ (2 : ℕ))) := by
    apply ((hgeo.add hzero).add hone).congr_fun
    intro n
    by_cases hn0 : n = 0
    · subst n
      norm_num [schwarzschildParikhWilczekInfiniteGradeDarkWeight]
      ring
    by_cases hn1 : n = 1
    · subst n
      norm_num [schwarzschildParikhWilczekInfiniteGradeDarkWeight]
      ring
    simp [schwarzschildParikhWilczekInfiniteGradeDarkWeight, hn0, hn1]
  have hid : (q / (1 - q / 2) + 2 * q) + (-4 * q ^ (2 : ℕ)) =
      q * (1 - q) * (3 - 2 * q) / (1 - q / 2) := by
    have htwo : 2 - q ≠ 0 := by linarith
    field_simp [htwo]
    ring
  rw [← hid]
  exact hraw

/-- Countable scalar response of the existing infinite PW-dark vector to physical endpoint
winding. -/
def schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse
    (epsilon : ℝ) : ℝ :=
  ∑' n : ℕ, schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
    schwarzschildParikhWilczekWindingTerm n epsilon
      (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon)

theorem schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse_eq
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse epsilon =
      let q := schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon
      q * (1 - q) * (3 - 2 * q) / (1 - q / 2) := by
  let q := schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon
  have hq0 : 0 < q :=
    schwarzschildParikhWilczekEndpointWindingLaplaceBase_pos hepsilon
  have hq1 : q < 1 :=
    schwarzschildParikhWilczekEndpointWindingLaplaceBase_lt_one hepsilon
  have hs := schwarzschildParikhWilczekInfiniteGradeDarkWeight_endpointPower_hasSum hq0 hq1
  rw [schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse]
  apply HasSum.tsum_eq
  convert hs using 1
  funext n
  rw [schwarzschildParikhWilczekWindingTerm_energyEndpoint_eq_laplaceBase_pow n hepsilon]

/-- The known infinite-support PW-dark vector has strictly positive physical endpoint response. -/
theorem schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse_pos
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse epsilon := by
  rw [schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse_eq hepsilon]
  let q := schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon
  have hq0 : 0 < q :=
    schwarzschildParikhWilczekEndpointWindingLaplaceBase_pos hepsilon
  have hq1 : q < 1 :=
    schwarzschildParikhWilczekEndpointWindingLaplaceBase_lt_one hepsilon
  have hden : 0 < 1 - q / 2 := by linarith
  have h1q : 0 < 1 - q := by linarith
  have h3q : 0 < 3 - 2 * q := by linarith
  exact div_pos (mul_pos (mul_pos hq0 h1q) h3q) hden

/-- Countable rank-one energy of the existing infinite dark matrix against two physical endpoint
winding legs. -/
def schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy
    (epsilon : ℝ) : ℝ :=
  ∑' ij : ℕ × ℕ,
    schwarzschildParikhWilczekInfiniteGradeDarkMatrix ij.1 ij.2 *
      schwarzschildParikhWilczekWindingTerm ij.1 epsilon
        (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon) *
      schwarzschildParikhWilczekWindingTerm ij.2 epsilon
        (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon)

/-- The countable endpoint energy factors as the square of the scalar response. -/
theorem schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy_eq_sq
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy epsilon =
      schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse epsilon ^ (2 : ℕ) := by
  let q := schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon
  let f : ℕ → ℝ := fun n =>
    schwarzschildParikhWilczekInfiniteGradeDarkWeight n * q ^ (n + 1)
  have hq0 : 0 < q :=
    schwarzschildParikhWilczekEndpointWindingLaplaceBase_pos hepsilon
  have hq1 : q < 1 :=
    schwarzschildParikhWilczekEndpointWindingLaplaceBase_lt_one hepsilon
  have hf : Summable f :=
    (schwarzschildParikhWilczekInfiniteGradeDarkWeight_endpointPower_hasSum hq0 hq1).summable
  have hfnorm : Summable (fun n => ‖f n‖) := hf.norm
  rw [schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy]
  calc
    (∑' ij : ℕ × ℕ,
      schwarzschildParikhWilczekInfiniteGradeDarkMatrix ij.1 ij.2 *
        schwarzschildParikhWilczekWindingTerm ij.1 epsilon
          (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon) *
        schwarzschildParikhWilczekWindingTerm ij.2 epsilon
          (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon)) =
        ∑' ij : ℕ × ℕ, f ij.1 * f ij.2 := by
          apply tsum_congr
          intro ij
          rw [schwarzschildParikhWilczekInfiniteGradeDarkMatrix,
            schwarzschildParikhWilczekWindingTerm_energyEndpoint_eq_laplaceBase_pow ij.1 hepsilon,
            schwarzschildParikhWilczekWindingTerm_energyEndpoint_eq_laplaceBase_pow ij.2 hepsilon]
          ring
    _ = (∑' i : ℕ, f i) * ∑' j : ℕ, f j := by
      rw [tsum_mul_tsum_of_summable_norm (f := f) (g := f) hfnorm hfnorm]
    _ = schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse epsilon ^ (2 : ℕ) := by
      rw [pow_two, schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse]
      congr 1 <;> apply tsum_congr <;> intro n <;>
        rw [schwarzschildParikhWilczekWindingTerm_energyEndpoint_eq_laplaceBase_pow n hepsilon]

/-- The existing countable PW-dark matrix has strictly positive physical endpoint energy. -/
theorem schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy_pos
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy epsilon := by
  rw [schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy_eq_sq hepsilon]
  exact sq_pos_of_pos
    (schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse_pos hepsilon)

/-- The literal endpoint channel defeats the explicit admissible infinite-support three-moment
dark kernel at every positive backreaction scale. -/
theorem schwarzschildParikhWilczekEndpointWinding_defeats_infiniteGradeDarkMatrix
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse epsilon ≠ 0 ∧
      0 < schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy epsilon := by
  exact ⟨(schwarzschildParikhWilczekInfiniteDarkEndpointWindingResponse_pos hepsilon).ne',
    schwarzschildParikhWilczekInfiniteDarkEndpointWindingEnergy_pos hepsilon⟩

end

end RHTower
