/-
Portions adapted from OpenAI’s Gauss-sum formalization, Apache-2.0.
See LICENSE and NOTICE in this directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheDifferentNormalizesTheTraceCharacter
import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinCoordinates
import GaloisForLFunctions.MetaplecticMobiusDescent.ShiftedEisensteinGaussianMass

/-!
# The Gaussian Abel limit of a quadratic residue sum

Partition the Eisenstein lattice into residue classes of a nonzero principal
ideal. Each class has the same Gaussian Abel mass. Multiplication by the
quadratic trace phase therefore recovers the finite Gauss sum in the limit.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
namespace GaloisForLFunctions.MetaplecticMobiusDescent

namespace EisensteinFiberShift

def Q (x y : ℝ) : ℝ := x*x-x*y+y*y
def q (a b : ℝ) : ℝ := Q a b
noncomputable def shiftX (a b x y : ℝ) : ℝ := ((a-b)*x+b*y)/q a b
noncomputable def shiftY (a b x y : ℝ) : ℝ := (-b*x+a*y)/q a b

theorem exact_shift (a b x y m n : ℝ) (hq : q a b ≠ 0) :
    Q (x+a*m-b*n) (y+b*m+(a-b)*n) =
      q a b * Q (m+shiftX a b x y) (n+shiftY a b x y) := by
  dsimp [shiftX, shiftY, Q]
  field_simp [hq]
  dsimp [q, Q]
  ring

end EisensteinFiberShift

namespace GaussianAbelPartition

theorem tsum_by_finite_fibers {A B : Type*} [Fintype B]
    (q : A → B) (f : A → ℂ) (hf : Summable f) :
    (∑' a : A, f a) =
      ∑ b : B, ∑' a : (q ⁻¹' {b}), f a.1 := by
  have h := (hf.hasSum.tsum_fiberwise q).tsum_eq
  simpa only [tsum_fintype] using h.symm

theorem tsum_periodic_weighted_partition {A B : Type*} [Fintype B]
    (q : A → B) (P : B → ℂ) (W : A → ℂ)
    (hf : Summable (fun a => P (q a) * W a)) :
    (∑' a : A, P (q a) * W a) =
      ∑ b : B, P b * ∑' a : (q ⁻¹' {b}), W a.1 := by
  rw [tsum_by_finite_fibers q _ hf]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑' a : (q ⁻¹' {b}), P (q a.1) * W a.1) =
        ∑' a : (q ⁻¹' {b}), P b * W a.1 := by
      apply tsum_congr
      intro a
      have ha : q a.1 = b := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using a.property
      rw [ha]
    _ = P b * ∑' a : (q ⁻¹' {b}), W a.1 := tsum_mul_left

end GaussianAbelPartition

namespace Eisenstein

private theorem finite_quotient_span {c : O} (hc : c ≠ 0) :
    Finite (O ⧸ Ideal.span {c}) :=
  (Ideal.span {c}).finiteQuotientOfFreeOfNeBot
    (fun h => hc (Ideal.span_singleton_eq_bot.mp h))

private theorem complex_norm_coordinates_sq (a b : ℤ) :
    ‖ringComplex (Coordinates.eval a b)‖ ^ 2 = ((a*a-a*b+b*b : ℤ) : ℝ) := by
  simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul, pow_two] using
    Coordinates.complex_norm_eval_sq a b

private theorem coordinate_norm_pos_of_nonzero (a b : ℤ)
    (hc : Coordinates.eval a b ≠ 0) : 0 < a*a-a*b+b*b := by
  simpa only [pow_two] using Coordinates.coordinate_norm_pos a b hc

theorem actual_quadratic_gaussian_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (principalTraceChar c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (principalTraceChar c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (principalTraceChar c hc)
          (r ^ 2) *
          ∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c}))
    (fun r => (principalTraceChar c hc)
      (r ^ 2)) W hsum

namespace GaussianFiberEquiv


def fiberMap (c : O) (r : O ⧸ Ideal.span {c})
    (r0 : O) (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (w : O) : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) := by
  refine ⟨r0 + c*w, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {c}) (r0 + c*w) = r
  rw [map_add, map_mul]
  have hc0 : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton c))
  rw [hc0, zero_mul, add_zero, hr]

private theorem fiberMap_injective (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Injective (fiberMap c r r0 hr) := by
  intro u v h
  have hval := congrArg Subtype.val h
  change r0 + c*u = r0 + c*v at hval
  exact mul_left_cancel₀ hc (add_left_cancel hval)

private theorem fiberMap_surjective (c : O)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Surjective (fiberMap c r r0 hr) := by
  rintro ⟨z, hz⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {c}) z = r := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
  have hdiff : z-r0 ∈ Ideal.span {c} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem z r0).mp (hz'.trans hr.symm)
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hdiff
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change r0 + c*w = z
  rw [← hw]
  ring

noncomputable def fiberEquiv (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    O ≃ ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) :=
  Equiv.ofBijective (fiberMap c r r0 hr)
    ⟨fiberMap_injective c hc r r0 hr, fiberMap_surjective c r r0 hr⟩

theorem fiber_tsum (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (W : O → ℂ) :
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1) =
      ∑' w : O, W (r0 + c*w) := by
  have h := (fiberEquiv c hc r r0 hr).tsum_eq (fun z => W z.1)
  have happ (w : O) : ((fiberEquiv c hc r r0 hr) w).1 = r0 + c*w := rfl
  simpa only [happ] using h.symm

end GaussianFiberEquiv

namespace GaussianShiftedPartition


noncomputable def representative (c : O) (r : O ⧸ Ideal.span {c}) : O :=
  Classical.choose (Ideal.Quotient.mk_surjective r)

theorem representative_spec (c : O) (r : O ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (representative c r) = r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)

theorem actual_quadratic_shifted_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (principalTraceChar c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (principalTraceChar c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (principalTraceChar c hc)
          (r ^ 2) *
          ∑' w : O, W (representative c r + c*w) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [actual_quadratic_gaussian_partition c hc W hsum]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact GaussianFiberEquiv.fiber_tsum c hc r
    (representative c r) (representative_spec c r) W

end GaussianShiftedPartition

theorem fiber_coordinates (a b x y m n : ℤ) :
    Coordinates.eval x y +
      Coordinates.eval a b *
        Coordinates.eval m n =
    Coordinates.eval (x + a*m-b*n)
      (y+b*m+(a-b)*n) := by
  rw [Coordinates.eval_mul]
  simp only [Coordinates.eval]
  push_cast
  ring

theorem fiber_quadratic_expansion (a b x y m n : ℤ) :
    let q := a*a-a*b+b*b
    let X := x+a*m-b*n
    let Y := y+b*m+(a-b)*n
    X*X-X*Y+Y*Y =
      q*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) := by
  dsimp
  ring

theorem ringComplex_fiber_norm_sq (a b x y m n : ℤ) :
    ‖ringComplex
      (Coordinates.eval x y +
        Coordinates.eval a b *
          Coordinates.eval m n)‖ ^ 2 =
      ((a*a-a*b+b*b)*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) : ℤ) := by
  rw [fiber_coordinates, complex_norm_coordinates_sq]
  exact_mod_cast fiber_quadratic_expansion a b x y m n

theorem actual_fiber_gaussian_eq_shifted
    (a b x y m n : ℤ)
    (hc : Coordinates.eval a b ≠ 0) (η : ℝ) :
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖ringComplex
        (Coordinates.eval x y +
          Coordinates.eval a b *
            Coordinates.eval m n)‖ ^ 2 : ℂ)) =
      RankTwoEisShift.shifted
        (η * ((a*a-a*b+b*b : ℤ) : ℝ))
        (EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    ne_of_gt (coordinate_norm_pos_of_nonzero a b hc)
  have hqR : EisensteinFiberShift.q (a : ℝ) (b : ℝ) ≠ 0 := by
    dsimp [EisensteinFiberShift.q, EisensteinFiberShift.Q]
    exact_mod_cast hqZ
  have hshift := EisensteinFiberShift.exact_shift
    (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ) (m : ℝ) (n : ℝ) hqR
  have hnormC : ((‖ringComplex
      (Coordinates.eval x y +
        Coordinates.eval a b *
          Coordinates.eval m n)‖ : ℂ)^2) =
      (((a*a-a*b+b*b)*(m*m-m*n+n*n) +
        ((2*a-b)*x+(2*b-a)*y)*m +
        (-(a+b)*x+(2*a-b)*y)*n +
        (x*x-x*y+y*y) : ℤ) : ℂ) := by
    exact_mod_cast ringComplex_fiber_norm_sq a b x y m n
  rw [hnormC]
  dsimp [RankTwoEisShift.shifted, RankTwoEisShift.Q]
  congr 1
  dsimp [EisensteinFiberShift.Q, EisensteinFiberShift.q] at hshift
  have hshiftC := congrArg (fun v : ℝ => (v : ℂ)) hshift
  push_cast at hshiftC ⊢
  linear_combination -(Real.pi : ℂ) * (η : ℂ) * hshiftC

/-- Every principal residue class has the same Gaussian mass after Abel normalization. -/
theorem actual_fiber_gaussian_mass (a b x y : ℤ)
    (hc : Coordinates.eval a b ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ,
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖ringComplex
            (Coordinates.eval x y +
              Coordinates.eval a b *
                Coordinates.eval z.1 z.2)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  have hq : 0 < (((a*a-a*b+b*b : ℤ) : ℝ)) := by
    exact_mod_cast coordinate_norm_pos_of_nonzero a b hc
  let u := EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  let v := EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  have h := EisensteinAbelFiber.scaled_shifted_gaussian_mass
    (((a*a-a*b+b*b : ℤ) : ℝ)) hq u v
  convert h using 1
  funext η
  congr 1
  apply tsum_congr
  intro z
  exact actual_fiber_gaussian_eq_shifted a b x y z.1 z.2 hc η

theorem eis_gaussian_summable {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖ringComplex z‖ ^ 2 : ℂ))) := by
  have hbase := RankTwoPoisson.eis_gauss_summable hη
  have hcomp : Summable (fun z : O =>
      RankTwoPoisson.eisGauss η (Coordinates.coordinateEquiv z)) :=
    (Coordinates.coordinateEquiv.summable_iff).2 hbase
  convert hcomp using 1
  funext z
  let p := Coordinates.coords z
  have hz : z = Coordinates.eval p.1 p.2 :=
    (Coordinates.eval_coords z).symm
  rw [hz]
  have hnormC : ((‖ringComplex
      (Coordinates.eval p.1 p.2)‖ : ℂ)^2) =
      ((p.1*p.1-p.1*p.2+p.2*p.2 : ℤ) : ℂ) := by
    exact_mod_cast complex_norm_coordinates_sq p.1 p.2
  rw [hnormC]
  change _ = RankTwoPoisson.eisGauss η
    (Coordinates.coords
      (Coordinates.eval p.1 p.2))
  rw [Coordinates.coords_eval]
  dsimp [RankTwoPoisson.eisGauss, RankTwoPoisson.eisQ]
  congr 1
  push_cast
  ring

theorem actual_oscillatory_kernel_summable (c : O) (hc : c ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O =>
      (principalTraceChar c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖ringComplex z‖ ^ 2 : ℂ))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  have hbase := (eis_gaussian_summable hη).norm
  apply hbase.of_norm_bounded
  intro z
  simp only [norm_mul]
  rw [AddChar.norm_apply]
  simp

theorem actual_O_fiber_gaussian_mass (c r : O) (hc : c ≠ 0) :
    let a := (Coordinates.coords c).1
    let b := (Coordinates.coords c).2
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' w : O, Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖ringComplex (r+c*w)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  dsimp only
  let a := (Coordinates.coords c).1
  let b := (Coordinates.coords c).2
  let x := (Coordinates.coords r).1
  let y := (Coordinates.coords r).2
  have hceq : c = Coordinates.eval a b :=
    (Coordinates.eval_coords c).symm
  have hreq : r = Coordinates.eval x y :=
    (Coordinates.eval_coords r).symm
  have hcE : Coordinates.eval a b ≠ 0 := by
    rw [← hceq]
    exact hc
  have hmass := actual_fiber_gaussian_mass a b x y hcE
  convert hmass using 1
  funext η
  congr 1
  let W : O → ℂ := fun w => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖ringComplex (r+c*w)‖ ^ 2 : ℂ))
  have hsum := (Coordinates.coordinateEquiv.symm.tsum_eq W).symm
  have happly (z : ℤ × ℤ) : Coordinates.coordinateEquiv.symm z =
      Coordinates.eval z.1 z.2 := rfl
  simpa only [W, hceq, hreq, happly] using hsum

/-- The Abel limit of the damped quadratic phase is the finite trace Gauss sum times lattice density. -/
theorem original_abel_gauss_limit (c : O) (hc : c ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let a := (Coordinates.coords c).1
    let b := (Coordinates.coords c).2
    let K : ℂ := ((2 / (Real.sqrt 3 *
      (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (principalTraceChar c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖ringComplex z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {c},
        (principalTraceChar c hc) (r ^ 2))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let a := (Coordinates.coords c).1
  let b := (Coordinates.coords c).2
  let K : ℂ := ((2 / (Real.sqrt 3 *
    (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
  let ψ := principalTraceChar c hc
  let W (η : ℝ) (z : O) := Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖ringComplex z‖ ^ 2 : ℂ))
  have hfiber (r : O ⧸ Ideal.span {c}) :
      Tendsto (fun η : ℝ => (η : ℂ) *
        (∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w)))
        (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    simpa only [K, a, b, W] using
      actual_O_fiber_gaussian_mass c
        (GaussianShiftedPartition.representative c r) hc
  have hsum : Tendsto (fun η : ℝ =>
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) * K)) := by
    apply tendsto_finsetSum Finset.univ
    intro r hr
    exact (hfiber r).const_mul (ψ (r ^ 2))
  have hpoint (η : ℝ) (hη : 0 < η) :
      (η : ℂ) * (∑' z : O, ψ
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))) := by
    have hpart := GaussianShiftedPartition.actual_quadratic_shifted_partition
      c hc (W η) (actual_oscillatory_kernel_summable c hc hη)
    change (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w) at hpart
    rw [hpart, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have heq : (fun η : ℝ => (η : ℂ) *
      (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z)) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w)))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hpoint η hη
  have hlim := hsum.congr' heq.symm
  simpa only [K, ψ, W, Finset.mul_sum, mul_comm] using hlim

end Eisenstein
end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.actual_fiber_gaussian_mass

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.actual_oscillatory_kernel_summable

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.original_abel_gauss_limit
