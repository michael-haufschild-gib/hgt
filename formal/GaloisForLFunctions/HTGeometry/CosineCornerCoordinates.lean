import GaloisForLFunctions.HTGeometry.CosineCornerUnfolding
import GaloisForLFunctions.HTGeometry.CosineCornerMarker

/-! # Exact specialization of the analytic corner to the cosine pair -/

namespace GaloisForLFunctions.HTGeometry.CosineCornerCoordinates

open Complex Filter LabeledCosineDescent CosineCornerUnfolding CosineCornerMarker
open scoped Topology

noncomputable section

def lifted (n : ℕ) (u : ℂ) : ℂ := u + n * (2 * Real.pi)
def point (n : ℕ) (u : ℂ) : ℂ := squareCoordinate (lifted n u)
def exponentialParameter (n : ℕ) : ℂ := exp (-(n : ℂ) * (2 * Real.pi))

theorem source_point (n : ℕ) (u : ℂ) : source (point n u) = cos u := by
  rw [point, source_squareCoordinate]
  exact Complex.cos_add_nat_mul_two_pi u n

theorem correction_conic {n : ℕ} {u e : ℂ} (hn : (n : ℂ) ≠ 0)
    (he : conicRelation conicConstant (((n : ℂ)⁻¹, u), e) = 0) :
    lifted n u ^ 2 + (I * (lifted n u - e)) ^ 2 = conicConstant := by
  have h : 2 * lifted n u * e - e ^ 2 = conicConstant := by
    dsimp [conicRelation] at he
    field_simp [hn] at he
    dsimp [lifted]
    linear_combination he
  rw [mul_pow, I_sq]
  linear_combination h

theorem reflected_source {U v : ℂ} (hc : U ^ 2 + v ^ 2 = conicConstant) :
    source (-squareCoordinate U) = cos v := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : squareCoordinate v + squareCoordinate U = 0 := by
    calc
      _ = 27 * (U ^ 2 + v ^ 2) / (4 * (Real.pi : ℂ) ^ 2) - 1 / 6 := by
        dsimp [squareCoordinate]
        ring
      _ = 0 := by rw [hc]; dsimp [conicConstant]; field_simp; ring
  have hv : squareCoordinate v = -squareCoordinate U := by linear_combination hs
  rw [← hv, source_squareCoordinate]

theorem exponential_coordinate (n : ℕ) (u e : ℂ) :
    exp ((I * (lifted n u - e)) * I) = exponentialParameter n * exp (-u + e) := by
  unfold exponentialParameter
  rw [← Complex.exp_add]
  congr 1
  dsimp [lifted, exponentialParameter]
  ring_nf
  rw [I_sq]
  ring

theorem reflected_factor_identity (n : ℕ) (u e : ℂ) :
    2 * (exponentialParameter n * exp (-u + e)) *
        (cos (I * (lifted n u - e)) - source 0) =
      1 - 2 * source 0 * (exponentialParameter n * exp (-u + e)) +
        (exponentialParameter n * exp (-u + e)) ^ 2 := by
  let v := I * (lifted n u - e)
  have hx := exponential_coordinate n u e
  change exp (v * I) = _ at hx
  rw [← hx]
  have hn : exp (-v * I) = (exp (v * I))⁻¹ := by rw [neg_mul, Complex.exp_neg]
  have hc := Complex.two_cos v
  rw [hn] at hc
  have hz : exp (v * I) ≠ 0 := Complex.exp_ne_zero _
  linear_combination exp (v * I) * hc + (mul_inv_cancel₀ hz)

theorem fiber_of_corner {n : ℕ} {u e : ℂ}
    (hn : (n : ℂ) ≠ 0)
    (he : conicRelation conicConstant (((n : ℂ)⁻¹, u), e) = 0)
    (hp : cos u - source 0 ≠ 0)
    (hz : 1 - 2 * source 0 * (exponentialParameter n * exp (-u + e)) +
      (exponentialParameter n * exp (-u + e)) ^ 2 ≠ 0)
    (hf : 2 * (exponentialParameter n * exp (-u + e)) /
      (1 - 2 * source 0 * (exponentialParameter n * exp (-u + e)) +
        (exponentialParameter n * exp (-u + e)) ^ 2) -
      (cos u - source 0)⁻¹ - slope = 0)
    (hw : point n u ≠ 0) :
    CosineProductRepair.denominator (point n u) ≠ 0 ∧
      CosineProductRepair.repair (point n u) = mark := by
  let w := point n u
  let z := exponentialParameter n * exp (-u + e)
  have hs : source (-w) = cos (I * (lifted n u - e)) :=
    reflected_source (correction_conic hn he)
  have hfactor : 2 * z * (source (-w) - source 0) = 1 - 2 * source 0 * z + z ^ 2 := by
    rw [hs]
    exact reflected_factor_identity n u e
  have hq : source (-w) - source 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfactor
    exact hz hfactor.symm
  have hzp : z ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have hinv : 2 * z / (1 - 2 * source 0 * z + z ^ 2) = (source (-w) - source 0)⁻¹ := by
    rw [← hfactor]
    field_simp
  have hps : source w - source 0 ≠ 0 := by simpa [w, source_point] using hp
  have hf' : (source (-w) - source 0)⁻¹ - (source w - source 0)⁻¹ = slope := by
    rw [← hinv, source_point]
    exact sub_eq_zero.mp hf
  have hrel : source w - source (-w) =
      slope * ((source w - source 0) * (source (-w) - source 0)) := by
    field_simp [hps, hq] at hf'
    linear_combination hf'
  have hcoords := CosineProductRepair.scaled_coordinates w
  have hden : w * CosineProductRepair.denominator w =
      (slope - I) * ((source w - source 0) * (source (-w) - source 0)) := by
    rw [hcoords.2, hrel]
    ring
  have hd : CosineProductRepair.denominator w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hden
    exact (mul_ne_zero slope_sub_I_ne_zero (mul_ne_zero hps hq)) hden.symm
  refine ⟨hd, ?_⟩
  apply (div_eq_iff hd).mpr
  apply mul_left_cancel₀ hw
  change w * CosineProductRepair.numerator w = w * (mark * CosineProductRepair.denominator w)
  rw [hcoords.1, hrel]
  calc
    _ = mark * ((slope - I) * ((source w - source 0) * (source (-w) - source 0))) := by
      linear_combination ((source w - source 0) * (source (-w) - source 0)) * slope_mark_relation
    _ = _ := by rw [← hden]; ring

end

end GaloisForLFunctions.HTGeometry.CosineCornerCoordinates
