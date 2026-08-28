import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFinitePolynomialGradeNoGo

/-!
# Finite-energy PW endpoint winding defeats every polynomial dark packet

The finite-polynomial PW no-go constructs, at every reporter degree `d`, a nonzero finite-support
positive-semidefinite rank-one packet invisible to every polynomial readout of that degree. The
literal Parikh--Wilczek finite-energy endpoint supplies a source-native nonpolynomial observable:
its grade-`k` winding amplitude is `q^(k+1)`, where `q=exp(-1/(4 epsilon))` lies in `(0,1)`.

This module evaluates the dark packet on that physical endpoint profile exactly. Its response is

`q * (q - 1)^(2*d+1)`,

which is strictly negative for every positive backreaction scale, and the associated rank-one
matrix energy is its strictly positive square. Thus the actual nonperturbative endpoint winding
detects every known finite-polynomial PW dark packet. Remaining PW-B burden is to couple this
faithful grade channel to oriented recoil before divisor specialization and prove the global wall
law.

`[NEW] [SOURCE-EXACT NONPOLYNOMIAL ESCAPE] [ALL-DEGREE DARK-PACKET SEPARATION]
[STRICT POSITIVE ENERGY] [LEAN-PROVED]`
-/

open Complex Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

def schwarzschildParikhWilczekEndpointWindingLaplaceBase
    (epsilon : ℝ) : ℝ :=
  Real.exp (-(1 / (4 * epsilon)))

theorem schwarzschildParikhWilczekWindingTerm_energyEndpoint_eq_laplaceBase_pow
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    schwarzschildParikhWilczekWindingTerm n epsilon
        (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon) =
      schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon ^ (n + 1) := by
  rw [schwarzschildParikhWilczekWindingTerm_energyEndpoint n hepsilon.ne']
  rw [schwarzschildParikhWilczekEndpointWindingLaplaceBase,
    ← Real.exp_nat_mul]
  congr 1
  rw [schwarzschildParikhWilczekEndpointAction]
  push_cast
  field_simp [hepsilon.ne']

theorem schwarzschildParikhWilczekEndpointWindingLaplaceBase_pos
    {epsilon : ℝ} (_hepsilon : 0 < epsilon) :
    0 < schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon := by
  exact Real.exp_pos _

theorem schwarzschildParikhWilczekEndpointWindingLaplaceBase_lt_one
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon < 1 := by
  rw [schwarzschildParikhWilczekEndpointWindingLaplaceBase,
    Real.exp_lt_one_iff]
  have hden : 0 < 4 * epsilon := by positivity
  exact neg_neg_iff_pos.mpr (div_pos (by norm_num) hden)

def schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse
    (d : ℕ) (epsilon : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
    schwarzschildParikhWilczekPolynomialGradeDarkWeight d k *
      schwarzschildParikhWilczekWindingTerm k epsilon
        (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon)

theorem schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse_eq
    (d : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse d epsilon =
      schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon *
        (schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon - 1) ^
          schwarzschildParikhWilczekPolynomialGradeDarkOrder d := by
  let n := schwarzschildParikhWilczekPolynomialGradeDarkOrder d
  let q := schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon
  have hbin : (q - 1) ^ n =
      ∑ k ∈ Finset.range (n + 1),
        q ^ k * (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) := by
    simpa [sub_eq_add_neg] using add_pow q (-1) n
  rw [schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse]
  simp_rw [schwarzschildParikhWilczekWindingTerm_energyEndpoint_eq_laplaceBase_pow _ hepsilon]
  change (∑ k ∈ Finset.range (n + 1),
      schwarzschildParikhWilczekPolynomialGradeDarkWeight d k * q ^ (k + 1)) =
    q * (q - 1) ^ n
  rw [hbin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [schwarzschildParikhWilczekPolynomialGradeDarkWeight]
  dsimp only [n]
  rw [pow_succ]
  ring

theorem schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse_neg
    (d : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse d epsilon < 0 := by
  rw [schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse_eq d hepsilon]
  let q := schwarzschildParikhWilczekEndpointWindingLaplaceBase epsilon
  have hq0 : 0 < q :=
    schwarzschildParikhWilczekEndpointWindingLaplaceBase_pos hepsilon
  have hq1 : q < 1 :=
    schwarzschildParikhWilczekEndpointWindingLaplaceBase_lt_one hepsilon
  have hqm1 : q - 1 < 0 := by linarith
  have hpow : (q - 1) ^ schwarzschildParikhWilczekPolynomialGradeDarkOrder d < 0 := by
    rw [schwarzschildParikhWilczekPolynomialGradeDarkOrder,
      show 2 * d + 1 = d + d + 1 by omega, pow_succ, pow_add]
    exact mul_neg_of_pos_of_neg
      (mul_self_pos.mpr (pow_ne_zero d hqm1.ne)) hqm1
  exact mul_neg_of_pos_of_neg hq0 hpow

def schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy
    (d : ℕ) (epsilon : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
    ∑ j ∈ Finset.range (schwarzschildParikhWilczekPolynomialGradeDarkOrder d + 1),
      schwarzschildParikhWilczekPolynomialGradeDarkMatrix d i j *
        schwarzschildParikhWilczekWindingTerm i epsilon
          (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon) *
        schwarzschildParikhWilczekWindingTerm j epsilon
          (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon)

theorem schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy_eq_sq
    (d : ℕ) (epsilon : ℝ) :
    schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy d epsilon =
      schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse d epsilon ^ 2 := by
  rw [schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy,
    schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse, pow_two,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwarzschildParikhWilczekPolynomialGradeDarkMatrix]
  ring

theorem schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy_pos
    (d : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy d epsilon := by
  rw [schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy_eq_sq]
  exact sq_pos_of_neg
    (schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse_neg d hepsilon)

theorem schwarzschildParikhWilczekEndpointWinding_defeats_everyPolynomialDarkPacket
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ d : ℕ,
      schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse d epsilon ≠ 0 ∧
        0 < schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy d epsilon := by
  intro d
  exact ⟨(schwarzschildParikhWilczekPolynomialDarkEndpointWindingResponse_neg
      d hepsilon).ne,
    schwarzschildParikhWilczekPolynomialDarkEndpointWindingEnergy_pos d hepsilon⟩

end

end RHTower
