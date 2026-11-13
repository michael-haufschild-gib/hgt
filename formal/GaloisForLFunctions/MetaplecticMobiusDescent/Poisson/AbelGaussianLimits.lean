/-
Abel limits of Gaussian phases adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.EisensteinLatticePoisson
import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.RankTwoGaussianPoisson

/-!
# Abel limits of Gaussian phases

Every principal residue class has the same Gaussian mass after Abel normalization; the Abel
limit of the damped quadratic phase is the finite trace Gauss sum times the lattice density.
Freezing the dual phase preserves the limit. CRT product decompositions of ideal quotients
(`IdealGaussCRT`).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory

namespace QuadraticPhase

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

theorem finite_quotient_span {c : O} (hc : c ≠ 0) :
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
end QuadraticPhase

open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory

namespace QuadraticPhase

namespace GaussianPhasePointwise

theorem exp_imag_diff_le (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) -
      Complex.exp (Complex.I * (v : ℂ))‖ ≤ |u - v| := by
  have heq :
      Complex.exp (Complex.I * (u : ℂ)) -
        Complex.exp (Complex.I * (v : ℂ)) =
      (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (v : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))

theorem exp_imag_denominator_error (θ A η : ℝ) (hA : 0 ≤ A) :
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
      |θ| * (A * η ^ 2) := by
  let r : ℝ := 1 + A * η ^ 2
  have hAη : 0 ≤ A * η ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdiff : |θ / r - θ| = |θ| * ((r - 1) / r) := by
    have heq : θ / r - θ = -θ * ((r - 1) / r) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hrpos.le)]
  have hfrac : (r - 1) / r ≤ r - 1 := by
    apply (div_le_iff₀ hrpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr)]
  have hbound := exp_imag_diff_le (θ / r) θ
  dsimp [r] at hbound ⊢
  calc
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
        |θ / (1 + A * η ^ 2) - θ| := hbound
    _ = |θ| * (((1 + A * η ^ 2) - 1) / (1 + A * η ^ 2)) := hdiff
    _ ≤ |θ| * (A * η ^ 2) := by
      have hfrac' := hfrac
      dsimp [r] at hfrac'
      nlinarith [mul_nonneg (abs_nonneg θ) (sub_nonneg.mpr hfrac')]

end GaussianPhasePointwise

namespace GaussianMoment

theorem x_exp_neg_le (x : ℝ) (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have hlin : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-x)).le
  calc
    x * Real.exp (-x) = 2 * ((x / 2) * Real.exp (-x)) := by ring
    _ ≤ 2 * (Real.exp (x / 2) * Real.exp (-x)) := by
      gcongr
    _ = 2 * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

theorem gaussian_moment_term_bound (q t : ℝ) (hq : 0 ≤ q) (ht : 0 < t) :
    q * Real.exp (-t * q) ≤
      (2 / t) * Real.exp (-(t * q / 2)) := by
  have h := x_exp_neg_le (t * q) (mul_nonneg ht.le hq)
  have hpos : 0 ≤ t := ht.le
  calc
    q * Real.exp (-t * q) =
        ((t * q) * Real.exp (-(t * q))) / t := by
          field_simp
    _ ≤ (2 * Real.exp (-(t * q / 2))) / t :=
      div_le_div_of_nonneg_right h hpos
    _ = (2 / t) * Real.exp (-(t * q / 2)) := by ring


noncomputable def realGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * RankTwoPoisson.eisQ z)

theorem realGauss_nonneg (t : ℝ) (z : ℤ × ℤ) :
    0 ≤ realGauss t z := (Real.exp_pos _).le

theorem realGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (realGauss t) := by
  have h := (RankTwoPoisson.eis_gauss_summable ht).norm
  convert h using 1
  funext z
  dsimp [realGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp

theorem realGauss_cast (t : ℝ) (z : ℤ × ℤ) :
    (realGauss t z : ℂ) = RankTwoEisShift.shifted t 0 0 z := by
  dsimp [realGauss, RankTwoPoisson.eisQ,
    RankTwoEisShift.shifted, RankTwoEisShift.Q]
  rw [← Complex.ofReal_exp]
  congr 1
  ring_nf

theorem real_gaussian_mass :
    Tendsto (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  have hC := EisensteinAbelFiber.shifted_gaussian_mass 0 0
  have hRe := (Complex.continuous_re.tendsto
    (((2 / Real.sqrt 3 : ℝ) : ℂ))).comp hC
  have hsum (t : ℝ) :
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
        (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) := by
    calc
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
          ∑' z : ℤ × ℤ, (realGauss t z : ℂ) := by
            apply tsum_congr
            intro z
            exact (realGauss_cast t z).symm
      _ = (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) :=
        (Complex.ofReal_tsum (realGauss t)).symm
  have hfun (t : ℝ) :
      t * (∑' z : ℤ × ℤ, realGauss t z) =
        (((t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z)).re) := by
    rw [hsum]
    norm_cast
  have hEq :
      (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z)) =
        (Complex.re ∘
          (fun t : ℝ => (t : ℂ) *
            (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z))) := by
    funext t
    exact hfun t
  rw [← hEq] at hRe
  simpa only [Complex.ofReal_re] using hRe


private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]

private theorem moment_term_bound {t : ℝ} (ht : 0 < t) (z : ℤ × ℤ) :
    RankTwoPoisson.eisQ z * realGauss t z ≤
      (2 / (Real.pi * t)) * realGauss (t / 2) z := by
  have h := gaussian_moment_term_bound (RankTwoPoisson.eisQ z) (Real.pi * t)
    (eisQ_nonneg z) (mul_pos Real.pi_pos ht)
  convert h using 1 <;> dsimp [realGauss] <;> ring_nf

private theorem moment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => RankTwoPoisson.eisQ z * realGauss t z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  exact hmajor.of_nonneg_of_le
    (fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z))
    (moment_term_bound ht)

private theorem moment_tsum_bound {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
      (2 / (Real.pi * t)) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  have h := Summable.tsum_le_tsum (moment_term_bound ht)
    (moment_summable ht) hmajor
  simpa only [tsum_mul_left] using h

private theorem moment_tsum_nonneg (t : ℝ) :
    0 ≤ (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) := by
  exact tsum_nonneg fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z)

private theorem half_tendsto_within :
    Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => t / 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact half_pos ht

private theorem t_tendsto_zero :
    Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

private theorem scaled_half_mass_tendsto :
    Tendsto
      (fun t : ℝ => (t / 2) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  simpa only [Function.comp_def] using real_gaussian_mass.comp half_tendsto_within

/-- The Gaussian moment costs two inverse powers of scale, leaving one vanishing power. -/
theorem scaled_moment_vanishes :
    Tendsto
      (fun t : ℝ => t ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hright : Tendsto
      (fun t : ℝ => (4 / Real.pi) * t *
        ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (t_tendsto_zero.mul scaled_half_mass_tendsto).const_mul (4 / Real.pi)
    simpa only [zero_mul, mul_zero, Function.comp_def, mul_assoc] using h
  have hleft : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact mul_nonneg (pow_nonneg ht.le _) (moment_tsum_nonneg t)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have h := moment_tsum_bound ht
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht.le _
    have hmul := mul_le_mul_of_nonneg_left h ht3
    calc
      t ^ 3 * (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
          t ^ 3 * ((2 / (Real.pi * t)) *
            (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := hmul
      _ = (4 / Real.pi) * t *
          ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := by
        field_simp [ht.ne']
        ring


theorem scaled_moment_vanishes_const (K : ℝ) (hK : 0 < K) :
    Tendsto
      (fun η : ℝ => η ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss (K * η) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hscale : Tendsto (fun η : ℝ => K * η)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun η : ℝ => K * η) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      change 0 < η at hη
      exact mul_pos hK hη
  have h := scaled_moment_vanishes.comp hscale
  have h' := h.const_mul (1 / K ^ 3)
  convert h' using 1
  · funext η
    dsimp [Function.comp_def]
    field_simp [hK.ne']
  · simp

end GaussianMoment

namespace OscSpecial

noncomputable def phaseBoundConstant (a b : ℝ) : ℝ :=
  2 * (|a - b| + |a| + |b|) + 1

theorem phaseBoundConstant_pos (a b : ℝ) :
    0 < phaseBoundConstant a b := by
  unfold phaseBoundConstant
  positivity

theorem quadratic_phase_abs_le (a b k l : ℝ) :
    |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
      phaseBoundConstant a b * (k ^ 2 + k * l + l ^ 2) := by
  let Q : ℝ := k ^ 2 + k * l + l ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    nlinarith only [sq_nonneg (k + l), sq_nonneg k, sq_nonneg l]
  have hsum : k ^ 2 + l ^ 2 ≤ 2 * Q := by
    dsimp [Q]
    nlinarith only [sq_nonneg (k + l)]
  have hcross : 2 * |k| * |l| ≤ k ^ 2 + l ^ 2 := by
    nlinarith only [sq_nonneg (|k| - |l|), sq_abs k, sq_abs l]
  have hk : k ^ 2 ≤ 2 * Q := by nlinarith only [hsum, sq_nonneg l]
  have hl : l ^ 2 ≤ 2 * Q := by nlinarith only [hsum, sq_nonneg k]
  have hkl : 2 * |k| * |l| ≤ 2 * Q := hcross.trans hsum
  have h1 := mul_le_mul_of_nonneg_left hk (abs_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hkl (abs_nonneg a)
  have h3 := mul_le_mul_of_nonneg_left hl (abs_nonneg b)
  have htri :
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
        |a - b| * k ^ 2 + 2 * |a| * |k| * |l| + |b| * l ^ 2 := by
    calc
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
          |(a - b) * k ^ 2| + |2 * a * k * l| + |b * l ^ 2| := by
        calc
          _ ≤ |(a - b) * k ^ 2 + 2 * a * k * l| + |b * l ^ 2| := abs_add_le _ _
          _ ≤ _ := by
            have hh := abs_add_le ((a - b) * k ^ 2) (2 * a * k * l)
            linarith
      _ = _ := by
        simp [abs_mul,  abs_of_nonneg (sq_nonneg k),
          abs_of_nonneg (sq_nonneg l)]
  unfold phaseBoundConstant
  nlinarith only [htri, h1, h2, h3, hQ]


noncomputable def dualQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 + (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2

noncomputable def dualTrace (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  (a - b) * (z.1 : ℝ) ^ 2 + 2 * a * (z.1 : ℝ) * (z.2 : ℝ) +
    b * (z.2 : ℝ) ^ 2

noncomputable def phaseA (a b : ℝ) : ℝ := 3 * q a b / 16
noncomputable def phaseAngle (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  -(Real.pi / 2) * dualTrace a b z
noncomputable def dualAmp (η a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z)
noncomputable def dualVarTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ))
noncomputable def dualFixedTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * (phaseAngle a b z : ℂ))

private theorem dualQ_nonneg (z : ℤ × ℤ) : 0 ≤ dualQ z := by
  unfold dualQ
  nlinarith [sq_nonneg ((z.1 : ℝ) + (z.2 : ℝ)), sq_nonneg (z.1 : ℝ),
    sq_nonneg (z.2 : ℝ)]

private theorem phaseAngle_bound (a b : ℝ) (z : ℤ × ℤ) :
    |phaseAngle a b z| ≤
      (Real.pi / 2) * phaseBoundConstant a b * dualQ z := by
  have h := quadratic_phase_abs_le a b (z.1 : ℝ) (z.2 : ℝ)
  dsimp [phaseAngle, dualTrace, dualQ]
  rw [abs_mul, abs_neg, abs_of_pos (half_pos Real.pi_pos)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left h (half_pos Real.pi_pos).le

private theorem r_eq_one_add_phaseA (η a b : ℝ) :
    r η a b = 1 + phaseA a b * η ^ 2 := by
  unfold r phaseA
  ring

private theorem phaseA_nonneg {a b : ℝ} (hq : 0 ≤ q a b) :
    0 ≤ phaseA a b := by
  unfold phaseA
  positivity

theorem dual_phase_term_error {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
      dualAmp η a b z *
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
        (phaseA a b * η ^ 2) := by
  have hA : 0 ≤ phaseA a b := phaseA_nonneg hq.le
  have hamp : 0 ≤ dualAmp η a b z := (Real.exp_pos _).le
  have hphase := GaussianPhasePointwise.exp_imag_denominator_error
    (phaseAngle a b z) (phaseA a b) η hA
  rw [← r_eq_one_add_phaseA η a b] at hphase
  have hangle := phaseAngle_bound a b z
  have hangle' := mul_le_mul_of_nonneg_right hangle
    (mul_nonneg hA (sq_nonneg η))
  dsimp [dualVarTerm, dualFixedTerm]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hamp]
  nlinarith only [mul_le_mul_of_nonneg_left hphase hamp,
    mul_le_mul_of_nonneg_left hangle' hamp]

noncomputable def dualRealGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * dualQ z)

private theorem dualRealGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (dualRealGauss t) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss t (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable ht)
  convert hE.norm using 1
  funext z
  dsimp [dualRealGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_re]
  congr 1
  dsimp [dualQ, RankTwoPoisson.eisQ]
  push_cast
  ring

private theorem dualMoment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => dualQ z * dualRealGauss t z) := by
  have hmaj : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * dualRealGauss (t / 2) z) :=
    (dualRealGauss_summable (half_pos ht)).mul_left _
  apply hmaj.of_nonneg_of_le
  · intro z
    exact mul_nonneg (dualQ_nonneg z) (Real.exp_pos _).le
  · intro z
    have h := GaussianMoment.gaussian_moment_term_bound
      (dualQ z) (Real.pi * t) (dualQ_nonneg z) (mul_pos Real.pi_pos ht)
    convert h using 1 <;> dsimp [dualRealGauss] <;> ring_nf

private theorem dualAmp_eq_realGauss (η a b : ℝ) (z : ℤ × ℤ) :
    dualAmp η a b z = dualRealGauss (η * q a b / (4 * r η a b)) z := rfl

private theorem dualAmp_norm_var (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualVarTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le

private theorem dualAmp_norm_fixed (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualFixedTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualFixedTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le

private theorem dualAmp_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualAmp η a b) := by
  have hr : 0 < r η a b := r_pos hη hq
  have ht : 0 < η * q a b / (4 * r η a b) := by positivity
  convert dualRealGauss_summable ht using 1
  funext z
  exact dualAmp_eq_realGauss η a b z

private theorem dualVar_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualVarTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_var η a b z))

private theorem dualFixed_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualFixedTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_fixed η a b z))

private theorem dualAmp_le_small {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2)
    (z : ℤ × ℤ) :
    dualAmp η a b z ≤ dualRealGauss (η * q a b / 8) z := by
  have hr : 0 < r η a b := r_pos hη hq
  have hp : 0 < η * q a b := mul_pos hη hq
  have ht : η * q a b / 8 ≤ η * q a b / (4 * r η a b) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (by positivity : 0 < 4 * r η a b)).2
    nlinarith [mul_le_mul_of_nonneg_left hrle hp.le]
  dsimp [dualAmp, dualRealGauss]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right ht
    (mul_nonneg Real.pi_pos.le (dualQ_nonneg z))
  nlinarith [hm]

noncomputable def phaseErrorConstant (a b : ℝ) : ℝ :=
  (Real.pi / 2) * phaseBoundConstant a b * phaseA a b

private theorem phaseErrorConstant_nonneg {a b : ℝ} (hq : 0 < q a b) :
    0 ≤ phaseErrorConstant a b := by
  unfold phaseErrorConstant
  exact mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
    (phaseBoundConstant_pos a b).le) (phaseA_nonneg hq.le)

theorem normalized_dual_phase_sum_error {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2) :
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ ≤
      phaseErrorConstant a b * η ^ 3 *
        (∑' z : ℤ × ℤ,
          dualQ z * dualRealGauss (η * q a b / 8) z) := by
  let t : ℝ := η * q a b / 8
  have ht : 0 < t := by dsimp [t]; positivity
  have hK : 0 ≤ phaseErrorConstant a b := phaseErrorConstant_nonneg hq
  have hpoint (z : ℤ × ℤ) :
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        (phaseErrorConstant a b * η ^ 2) *
          (dualQ z * dualRealGauss t z) := by
    have hbase := dual_phase_term_error hη hq z
    have hamp := dualAmp_le_small hη hq hrle z
    have hfac : 0 ≤
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
          (phaseBoundConstant_pos a b).le) (dualQ_nonneg z))
        (mul_nonneg (phaseA_nonneg hq.le) (sq_nonneg η))
    have hmul := mul_le_mul_of_nonneg_right hamp hfac
    dsimp [t, phaseErrorConstant]
    calc
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        dualAmp η a b z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := hbase
      _ ≤ dualRealGauss (η * q a b / 8) z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by nlinarith only [hmul]
      _ = ((Real.pi / 2 * phaseBoundConstant a b * phaseA a b) * η ^ 2) *
          (dualQ z * dualRealGauss (η * q a b / 8) z) := by ring
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (phaseErrorConstant a b * η ^ 2) *
        (dualQ z * dualRealGauss t z)) :=
    (dualMoment_summable ht).mul_left _
  have hnorm : Summable (fun z : ℤ × ℤ =>
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
    hmajor.of_nonneg_of_le (fun z => norm_nonneg _) hpoint
  have hsum := norm_tsum_le_tsum_norm hnorm
  have htsum := Summable.tsum_le_tsum hpoint hnorm hmajor
  have hvar := dualVar_summable hη hq
  have hfixed := dualFixed_summable hη hq
  calc
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ =
      η * ‖(∑' z : ℤ × ℤ, (dualVarTerm η a b z - dualFixedTerm η a b z))‖ := by
        rw [hvar.tsum_sub hfixed]
    _ ≤ η * (∑' z : ℤ × ℤ,
          ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
      mul_le_mul_of_nonneg_left hsum hη.le
    _ ≤ η * (∑' z : ℤ × ℤ,
          (phaseErrorConstant a b * η ^ 2) *
            (dualQ z * dualRealGauss t z)) :=
      mul_le_mul_of_nonneg_left htsum hη.le
    _ = phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ, dualQ z * dualRealGauss (η * q a b / 8) z) := by
      rw [tsum_mul_left]
      dsimp [t]
      ring


private theorem dual_moment_reindex (t : ℝ) :
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
      ∑' z : ℤ × ℤ,
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  calc
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
        ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ (e z) * GaussianMoment.realGauss t (e z) := by
      apply tsum_congr
      intro z
      have hQ : RankTwoPoisson.eisQ (e z) = dualQ z := by
        rcases z with ⟨k,l⟩
        change (k : ℝ) ^ 2 - (k : ℝ) * ((-l : ℤ) : ℝ) +
          ((-l : ℤ) : ℝ) ^ 2 =
          (k : ℝ) ^ 2 + (k : ℝ) * (l : ℝ) + (l : ℝ) ^ 2
        push_cast
        ring
      simp only [GaussianMoment.realGauss, dualRealGauss, hQ]
    _ = ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z :=
      e.tsum_eq (fun z : ℤ × ℤ =>
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z)

/-- Freezing the dual phase preserves the normalized Abel limit. -/
theorem normalized_dual_phase_sum_error_tendsto_zero {a b : ℝ}
    (hq : 0 < q a b) :
    Tendsto
      (fun η : ℝ =>
        η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
          (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let K : ℝ := q a b / 8
  have hK : 0 < K := by dsimp [K]; positivity
  have hmoment :
      Tendsto
        (fun η : ℝ => η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert GaussianMoment.scaled_moment_vanishes_const K hK using 1
    funext η
    dsimp [K]
    rw [dual_moment_reindex]
    ring_nf
  have hright :
      Tendsto
        (fun η : ℝ => phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert hmoment.const_mul (phaseErrorConstant a b) using 1
    · funext η
      ring
    · simp
  have hr_lim : Tendsto (fun η : ℝ => r η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun η : ℝ => r η a b) 0 := by
      unfold r
      fun_prop
    simpa [r] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hrle : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), r η a b ≤ 2 := by
    have hevent : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), x ≤ 2 :=
      eventually_le_nhds (by norm_num)
    exact hr_lim.eventually hevent
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hright
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact mul_nonneg hη.le (norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin, hrle] with η hη hbound
    exact normalized_dual_phase_sum_error hη hq hbound

theorem dualGaussian_eq_dualVarTerm {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      dualVarTerm η a b z := by
  rw [dualGaussian_explicit hη hq z]
  have hQ :
      ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) =
        (dualQ z : ℂ) := by
    dsimp [dualQ]
    push_cast
    ring
  have hT :
      (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
        2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
        (b : ℂ) * (z.2 : ℂ) ^ 2) =
        (dualTrace a b z : ℂ) := by
    dsimp [dualTrace]
    push_cast
    ring
  rw [hQ, hT]
  have hrC : (r η a b : ℂ) ≠ 0 := by
    exact_mod_cast (r_pos hη hq).ne'
  have harg :
      -(Real.pi : ℂ) *
        ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ)) *
          (dualQ z : ℂ) +
          Complex.I / (2 * (r η a b : ℂ)) * (dualTrace a b z : ℂ)) =
      (((-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z : ℝ) : ℂ)) +
        Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ) := by
    dsimp [phaseAngle]
    push_cast
    field_simp [hrC]
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  rfl



noncomputable def dualScale (η a b : ℝ) : ℝ :=
  η * q a b / (4 * r η a b)

theorem dualScale_tendsto (a b : ℝ) (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hnum : ContinuousAt (fun η : ℝ => η * q a b) 0 := by fun_prop
  have hden : ContinuousAt (fun η : ℝ => 4 * r η a b) 0 := by
    change ContinuousAt
      (fun η : ℝ => 4 * (1 + 3 * q a b * η ^ 2 / 16)) 0
    fun_prop
  have hden0 : 4 * r 0 a b ≠ 0 := by simp [r]
  have hcont : ContinuousAt (fun η : ℝ => dualScale η a b) 0 := by
    exact hnum.div hden hden0
  have hlim : Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [dualScale] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact hlim
  · filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hr : 0 < r η a b := by
      unfold r
      positivity
    exact div_pos (mul_pos hη hq) (mul_pos (by norm_num) hr)

/-- The dual damping rescales Abel mass by the limiting ratio of the two scales. -/
theorem abel_mass_dual_scale (a b : ℝ) (hq : 0 < q a b)
    (F : ℝ → ℂ) (L : ℂ)
    (hF : Tendsto (fun t : ℝ => (t : ℂ) * F t)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun η : ℝ => (η : ℂ) * F (dualScale η a b))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((4 / q a b : ℝ) : ℂ) * L)) := by
  have hscale := dualScale_tendsto a b hq
  have hF' := hF.comp hscale
  have hrcont : ContinuousAt
      (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ)) 0 := by
    change ContinuousAt
      (fun η : ℝ => ((4 * (1 + 3 * q a b * η ^ 2 / 16) / q a b : ℝ) : ℂ)) 0
    fun_prop
  have hr : Tendsto (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((4 / q a b : ℝ) : ℂ)) := by
    simpa [r] using hrcont.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hr.mul hF'
  have heq : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      (η : ℂ) * F (dualScale η a b) =
        ((4 * r η a b / q a b : ℝ) : ℂ) *
          (((dualScale η a b : ℝ) : ℂ) * F (dualScale η a b)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hrpos : 0 < r η a b := by
      unfold r
      positivity
    have hqC : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hrC : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    dsimp [dualScale]
    push_cast
    field_simp [hqC, hrC]
  exact hprod.congr' (heq.mono fun η h => h.symm)


private theorem R_eq_four_r_div_q {η a b : ℝ} (hq : q a b ≠ 0) :
    R η a b = 4 * r η a b / q a b := by
  unfold R r
  field_simp [hq]
  ring

private theorem sqrt_R_eq {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b) :
    Real.sqrt (R η a b) = 2 * Real.sqrt (r η a b) / Real.sqrt (q a b) := by
  rw [R_eq_four_r_div_q hq.ne']
  rw [Real.sqrt_div' (4 * r η a b) hq.le]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs4]

theorem prefactor_eq_real_sqrt {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ) := by
  have hR : 0 ≤ R η a b := by unfold R; positivity
  have hqS : Real.sqrt (q a b) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hrS : Real.sqrt (r η a b) ≠ 0 :=
    (Real.sqrt_pos.mpr (r_pos hη hq)).ne'
  have hcpow : (R η a b : ℂ) ^ (1 / 2 : ℂ) =
      ((R η a b) ^ (1 / 2 : ℝ) : ℝ) := by
    simpa using (Complex.ofReal_cpow hR (1 / 2 : ℝ)).symm
  rw [hcpow]
  simp only [Complex.ofReal_div]
  rw [← Real.sqrt_eq_rpow, sqrt_R_eq hη hq]
  push_cast
  field_simp [hqS, hrS]


/-- The principal Poisson prefactor tends to half the square root of the norm form. -/
theorem prefactor_tendsto {a b : ℝ} (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) := by
  have hrcont : Continuous (fun η : ℝ => r η a b) := by
    unfold r
    fun_prop
  have hr : Tendsto (fun η : ℝ => r η a b) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [r] using (hrcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun η : ℝ => Real.sqrt (r η a b))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hd : Tendsto (fun η : ℝ => Real.sqrt (q a b) /
      (2 * Real.sqrt (r η a b))) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (q a b) / 2)) := by
    simpa only [Pi.div_def, mul_one] using
      (tendsto_const_nhds (x := Real.sqrt (q a b))).div
        ((tendsto_const_nhds (x := (2 : ℝ))).mul hs)
        (by norm_num : (2 : ℝ) * 1 ≠ 0)
  have hc : Tendsto (fun η : ℝ =>
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hd
  have heq : (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact prefactor_eq_real_sqrt hη hq
  exact hc.congr' heq.symm

end OscSpecial

/-- A vanishing normalized phase error transfers an Abel limit through a convergent prefactor. -/
theorem abel_transfer (P V W : ℝ → ℂ) (p w : ℂ)
    (hP : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 p))
    (hW : Tendsto (fun η : ℝ => (η : ℂ) * W η) (𝓝[>] (0 : ℝ)) (𝓝 w))
    (hE : Tendsto (fun η => η * ‖V η - W η‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Tendsto (fun η : ℝ => (η : ℂ) * (P η * V η))
      (𝓝[>] (0 : ℝ)) (𝓝 (p * w)) := by
  have hdiff : Tendsto (fun η : ℝ => (η : ℂ) * (V η - W η))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun η : ℝ => ‖(η : ℂ) * (V η - W η)‖) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun η => η * ‖V η - W η‖) := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    exact hE.congr' heq.symm
  have hV : Tendsto (fun η : ℝ => (η : ℂ) * V η)
      (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    convert hW.add hdiff using 1
    · funext η; ring
    · simp
  convert hP.mul hV using 1
  · funext η; ring


end QuadraticPhase

open scoped BigOperators Topology
open Filter

namespace QuadraticPhase.Eisenstein
open Coordinates

/-- The dual frequency lattice in the integral Eisenstein basis. -/
def dualFrequencyEquiv : ℤ × ℤ ≃ O :=
  ({ toFun := fun z => (z.1+z.2,z.1)
     invFun := fun z => (z.2,z.1-z.2)
     left_inv := by rintro ⟨k,l⟩; simp
     right_inv := by rintro ⟨k,l⟩; simp } : (ℤ × ℤ) ≃ (ℤ × ℤ)).trans
    coordinateEquiv.symm

theorem dualFrequencyEquiv_apply (z : ℤ × ℤ) :
    dualFrequencyEquiv z = eval (z.1+z.2) z.1 := rfl

theorem dualFrequency_norm_sq (z : ℤ × ℤ) :
    ‖ringComplex (dualFrequencyEquiv z)‖ ^ 2 = OscSpecial.dualQ z := by
  rw [dualFrequencyEquiv_apply, complex_norm_eval_sq]
  dsimp [OscSpecial.dualQ]
  push_cast
  ring

/-- The fixed phase of the inverse quadratic form is the trace phase modulo four. -/
theorem dualFrequency_phase (a b : ℤ) (z : ℤ × ℤ) :
    fixedDualPhase (eval a b) (dualFrequencyEquiv z) =
      Complex.exp (Complex.I * (OscSpecial.phaseAngle (a : ℝ) (b : ℝ) z : ℂ)) := by
  rw [dualFrequencyEquiv_apply, fixedDualPhase_eval]
  conv_lhs => rw [← Complex.exp_pi_div_two_mul_I, ← Complex.exp_int_mul]
  congr 1
  dsimp [OscSpecial.phaseAngle, OscSpecial.dualTrace]
  push_cast
  ring

/-- Reindexing the fixed dual Gaussian exposes its period-two residue classes. -/
theorem fixed_dual_sum_eq (a b : ℤ) (η : ℝ) :
    (∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z) =
      ∑' y : O, fixedDualPhase (eval a b) y *
        Complex.exp (-(Real.pi : ℂ) * (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
          (‖ringComplex y‖ ^ 2 : ℂ)) := by
  rw [← dualFrequencyEquiv.tsum_eq (fun y : O => fixedDualPhase (eval a b) y *
    Complex.exp (-(Real.pi : ℂ) * (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
      (‖ringComplex y‖ ^ 2 : ℂ)))]
  apply tsum_congr
  intro z
  have hnorm : (‖ringComplex (dualFrequencyEquiv z)‖ : ℂ) ^ 2 =
      (OscSpecial.dualQ z : ℂ) := by exact_mod_cast dualFrequency_norm_sq z
  rw [dualFrequency_phase, hnorm]
  dsimp [OscSpecial.dualFixedTerm, OscSpecial.dualAmp, OscSpecial.dualScale]
  rw [Complex.ofReal_exp]
  push_cast
  ring

/-- The actual quadratic trace kernel is the oscillatory binary Gaussian. -/
theorem original_kernel_eq_binary (a b x y : ℤ) (hc : eval a b ≠ 0) (η : ℝ) :
    principalTraceChar (eval a b) hc
        (Ideal.Quotient.mk (Ideal.span {eval a b}) (eval x y) ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) * (‖ringComplex (eval x y)‖ ^ 2 : ℂ)) =
      RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ)) (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (x,y) := by
  have hnorm : (‖ringComplex (eval x y)‖ : ℂ) ^ 2 =
      (x : ℂ) ^ 2 - (x : ℂ) * (y : ℂ) + (y : ℂ) ^ 2 := by
    exact_mod_cast complex_norm_eval_sq x y
  rw [principalTraceChar_square, hnorm, ← Complex.exp_add]
  dsimp [RankTwoComplex.binaryGaussian, OscSpecial.A, OscSpecial.B, OscSpecial.D,
    OscSpecial.q]
  congr 1
  push_cast
  ring

theorem original_sum_eq_binary (a b : ℤ) (hc : eval a b ≠ 0) (η : ℝ) :
    (∑' z : O, principalTraceChar (eval a b) hc
        (Ideal.Quotient.mk (Ideal.span {eval a b}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) * (‖ringComplex z‖ ^ 2 : ℂ))) =
      ∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ)) (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) z := by
  rw [← coordinateEquiv.symm.tsum_eq (fun z : O =>
    principalTraceChar (eval a b) hc (Ideal.Quotient.mk (Ideal.span {eval a b}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) * (‖ringComplex z‖ ^ 2 : ℂ)))]
  exact tsum_congr fun z => original_kernel_eq_binary a b z.1 z.2 hc η

private theorem finite_mod_two : Finite (O ⧸ Ideal.span {(2 : O)}) :=
  (Ideal.span {(2 : O)}).finiteQuotientOfFreeOfNeBot
    (fun h => (by norm_num : (2 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))

/-- Equal Abel mass in the four classes leaves their fixed phase average. -/
theorem fixed_phase_abel_limit (c : O) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      (∑' y : O, fixedDualPhase c y *
        Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (‖ringComplex y‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / (Real.sqrt 3 : ℂ)) * fixedDualAverage c)) := by
  letI : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_mod_two
  letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let rep := GaussianShiftedPartition.representative (2 : O)
  let P : O ⧸ Ideal.span {(2 : O)} → ℂ := fun r => fixedDualPhase c (rep r)
  let W (t : ℝ) (y : O) : ℂ :=
    Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (‖ringComplex y‖ ^ 2 : ℂ))
  have hP (y : O) : P (Ideal.Quotient.mk (Ideal.span {(2 : O)}) y) =
      fixedDualPhase c y :=
    fixedDualPhase_eq_of_mod_two c _ _
      (GaussianShiftedPartition.representative_spec 2 _)
  have hfiber (r : O ⧸ Ideal.span {(2 : O)}) :
      Tendsto (fun t : ℝ => (t : ℂ) * (∑' y : O, W t (rep r + 2*y)))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / (2 * (Real.sqrt 3 : ℂ)))) := by
    have h := actual_O_fiber_gaussian_mass (2 : O) (rep r) (by norm_num)
    have hcoords : coords (2 : O) = (2,0) := by
      rw [← show eval 2 0 = (2 : O) by norm_num [eval], coords_eval]
    simp only [hcoords] at h
    convert h using 1
    dsimp [W]
    push_cast
    ring
  have hsum := tendsto_finsetSum Finset.univ (fun r _ => (hfiber r).const_mul (P r))
  have hpoint (t : ℝ) (ht : 0 < t) :
      (t : ℂ) * (∑' y : O, fixedDualPhase c y * W t y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)}, P r *
        ((t : ℂ) * (∑' y : O, W t (rep r + 2*y))) := by
    have hconv : Summable (fun y : O => P (Ideal.Quotient.mk (Ideal.span {(2 : O)}) y) * W t y) := by
      apply (eis_gaussian_summable ht).norm.of_norm_bounded
      intro y
      simpa only [norm_mul, hP, fixedDualPhase_norm, one_mul] using (le_refl ‖W t y‖)
    have hp := GaussianAbelPartition.tsum_periodic_weighted_partition
      (Ideal.Quotient.mk (Ideal.span {(2 : O)})) P (W t) hconv
    simp only [hP] at hp
    rw [hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [GaussianFiberEquiv.fiber_tsum 2 (by norm_num) r (rep r)
      (GaussianShiftedPartition.representative_spec 2 r) (W t)]
    ring
  have heq : (fun t : ℝ => (t : ℂ) * (∑' y : O, fixedDualPhase c y * W t y)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ∑ r : O ⧸ Ideal.span {(2 : O)}, P r *
        ((t : ℂ) * (∑' y : O, W t (rep r + 2*y)))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpoint t ht
  have hlim := hsum.congr' heq.symm
  convert hlim using 1
  congr 1
  unfold fixedDualAverage
  change (1 / (Real.sqrt 3 : ℂ)) * ((∑ r, P r) / 2) = _
  rw [← Finset.sum_mul]
  ring

/-- The fixed dual sum has its residue average as its rescaled Abel limit. -/
theorem fixed_dual_abel_limit (a b : ℤ) (hc : eval a b ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) *
        ((1 / (Real.sqrt 3 : ℂ)) * fixedDualAverage (eval a b)))) := by
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    dsimp [OscSpecial.q]
    exact_mod_cast coordinate_norm_pos a b hc
  have h := OscSpecial.abel_mass_dual_scale (a : ℝ) (b : ℝ) hq
    (fun t : ℝ => ∑' y : O, fixedDualPhase (eval a b) y *
      Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (‖ringComplex y‖ ^ 2 : ℂ)))
    _ (fixed_phase_abel_limit (eval a b))
  simpa only [fixed_dual_sum_eq] using h

/-- Poisson summation and the vanishing phase error give the dual limit of the original kernel. -/
theorem original_dual_abel_limit (a b : ℤ) (hc : eval a b ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O, principalTraceChar (eval a b) hc
        (Ideal.Quotient.mk (Ideal.span {eval a b}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) * (‖ringComplex z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ)) *
        (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) *
          ((1 / (Real.sqrt 3 : ℂ)) * fixedDualAverage (eval a b))))) := by
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    dsimp [OscSpecial.q]
    exact_mod_cast coordinate_norm_pos a b hc
  have h := abel_transfer
    (fun η : ℝ => 1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ)))
    (fun η : ℝ => ∑' z : ℤ × ℤ, OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z)
    (fun η : ℝ => ∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z)
    _ _ (OscSpecial.prefactor_tendsto hq) (fixed_dual_abel_limit a b hc)
    (OscSpecial.normalized_dual_phase_sum_error_tendsto_zero hq)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [original_sum_eq_binary, OscSpecial.oscillatory_gaussian_poisson hη hq]
  congr 2
  exact tsum_congr fun z => (OscSpecial.dualGaussian_eq_dualVarTerm hη hq z).symm

/-- The normalized quadratic trace Gauss sum is the four-residue dual average. -/
theorem normalizedQuadraticTraceGauss_eq_average (a b : ℤ) (hc : eval a b ≠ 0) :
    normalizedQuadraticTraceGauss (eval a b) hc = fixedDualAverage (eval a b) := by
  have ho := original_abel_gauss_limit (eval a b) hc
  simp only [coords_eval] at ho
  have hd := original_dual_abel_limit a b hc
  have heq := tendsto_nhds_unique ho hd
  let n := ‖ringComplex (eval a b)‖
  have hn : 0 < n := norm_pos_iff.mpr
    (fun h => hc (ringComplex_injective (by simpa using h)))
  have hq : OscSpecial.q (a : ℝ) (b : ℝ) = n ^ 2 :=
    (complex_norm_eval_sq a b).symm
  have hsqrt : Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) = n := by
    rw [hq, Real.sqrt_sq hn.le]
  have hi : (((a*a-a*b+b*b : ℤ) : ℝ)) = n ^ 2 := by
    simpa only [OscSpecial.q, Int.cast_add, Int.cast_sub, Int.cast_mul, pow_two] using hq
  change ((2 / (Real.sqrt 3 * (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ) *
      quadraticTraceGauss (eval a b) hc = _ at heq
  rw [hi, hsqrt, hq] at heq
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  change quadraticTraceGauss (eval a b) hc / (n : ℂ) = _
  apply mul_left_cancel₀ (show (2 / ((Real.sqrt 3 : ℂ) * (n : ℂ))) ≠ 0 by
    exact div_ne_zero (by norm_num) (mul_ne_zero hsC hnC))
  convert heq using 1 <;> push_cast <;> field_simp [hnC, hsC]
  all_goals ring

/-- Every nonzero modulus has an explicit quadratic trace Gauss phase modulo four. -/
theorem normalizedQuadraticTraceGauss_formula (a b : ℤ) (hc : eval a b ≠ 0) :
    normalizedQuadraticTraceGauss (eval a b) hc =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  rw [normalizedQuadraticTraceGauss_eq_average, fixedDualAverage_formula]

/-- The intrinsic normalized sum is the dual average, independently of coordinate choices. -/
theorem normalizedQuadraticTraceGauss_eq_fixedDualAverage (c : O) (hc : c ≠ 0) :
    normalizedQuadraticTraceGauss c hc = fixedDualAverage c := by
  obtain ⟨a,b,hab⟩ := exists_coordinates c
  change c = eval a b at hab
  subst c
  exact normalizedQuadraticTraceGauss_eq_average a b hc

/-- The normalized quadratic trace sum depends only on the modulus modulo four. -/
theorem normalizedQuadraticTraceGauss_eq_of_mod_four (c d : O) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) :
    normalizedQuadraticTraceGauss c hc = normalizedQuadraticTraceGauss d hd := by
  rw [normalizedQuadraticTraceGauss_eq_fixedDualAverage,
    normalizedQuadraticTraceGauss_eq_fixedDualAverage,
    fixedDualAverage_eq_of_mod_four c d h]

/-- The quadratic trace Gauss sum is positive on the principal class modulo four. -/
theorem quadraticTraceGauss_eq_norm (c : O) (hc : c ≠ 0)
    (hfour : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c = 1) :
    quadraticTraceGauss c hc = (‖ringComplex c‖ : ℂ) := by
  have h := normalizedQuadraticTraceGauss_eq_fixedDualAverage c hc
  rw [fixedDualAverage_eq_one _ hfour] at h
  have hn : (‖ringComplex c‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr
      (fun h => hc (ringComplex_injective (by simpa using h)))
  exact (div_eq_one_iff_eq hn).mp h

end QuadraticPhase.Eisenstein

namespace QuadraticPhase.ProductGauss
open _root_.GaloisForLFunctions.MetaplecticMobiusDescent.ProductGauss

/-- Counting square roots identifies the quadratic-character Gauss sum with its square phase. -/
theorem quadratic_eq_square_sum {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hchar : ringChar F ≠ 2) (hψ : ψ ≠ 1) :
    gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ =
      ∑ x : F, ψ (x ^ 2) := by
  classical
  have hfiber : (∑ x : F, ψ (x ^ 2)) =
      ∑ y : F, (({x : F | x ^ 2 = y}.toFinset.card : ℕ) : ℂ) * ψ y := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun x : F => x ^ 2) (f := fun x : F => ψ (x ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_congr rfl (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hx])]
    simp
  have hcount (y : F) : (({x : F | x ^ 2 = y}.toFinset.card : ℕ) : ℂ) =
      (quadraticChar F y : ℂ) + 1 := by
    exact_mod_cast quadraticChar_card_sqrts hchar y
  rw [hfiber]
  simp_rw [hcount, add_mul, one_mul]
  rw [Finset.sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]

/-- The square phase factors over the actual coordinate decomposition. -/
theorem square_sum_factorization (ψ : AddChar (∀ i, F i) ℂ) :
    (∑ x : ∀ i, F i, ψ (x ^ 2)) =
      ∏ i, ∑ y : F i, localChar F ψ i (y ^ 2) := by
  simp_rw [character_eq_prod F ψ, Pi.pow_apply]
  exact (Fintype.prod_sum (fun i y => localChar F ψ i (y ^ 2))).symm

/-- A primitive character on a product of odd finite fields has the same quadratic Gauss sum and square sum. -/
theorem quadratic_factorization_equiv {R : Type*} [CommRing R] [Fintype R]
    (e : R ≃+* ∀ i, F i) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (hchar : ∀ i, ringChar (F i) ≠ 2) :
    (∑ x : R, (∏ i, ((quadraticChar (F i)).ringHomComp (Int.castRingHom ℂ)) (e x i)) * ψ x) =
      ∑ x : R, ψ (x ^ 2) := by
  rw [factorization_equiv F e]
  have hψ' := primitive_comp_ringEquiv e.symm ψ hψ
  calc
    _ = ∏ i, ∑ y : F i,
        localChar F (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i (y ^ 2) := by
      apply Finset.prod_congr rfl
      intro i _
      apply quadratic_eq_square_sum _ (hchar i)
      have hp := localChar_primitive F _ hψ' i
      simpa only [AddChar.mulShift_one] using hp (a := 1) one_ne_zero
    _ = ∑ x : ∀ i, F i, (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (x ^ 2) :=
      (square_sum_factorization F _).symm
    _ = ∑ x : R, ψ (x ^ 2) := by
      apply Fintype.sum_equiv e.symm.toEquiv
      intro x
      change ψ (e.symm (x ^ 2)) = ψ ((e.symm x) ^ 2)
      rw [map_pow]

end QuadraticPhase.ProductGauss

open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap

namespace FiniteOverlapDecomposition
open scoped Classical
variable {ι : Type*} [DecidableEq ι]

/-- Common support and two disjoint residual supports. -/
abbrev Triple (ι : Type*) := Σ _ : Finset ι, Finset ι × Finset ι

def triples (F : Finset ι) : Finset (Triple ι) :=
  F.powerset.sigma fun G => ((F \ G).powerset ×ˢ (F \ G).powerset).filter fun UV => Disjoint UV.1 UV.2

def split (ST : Finset ι × Finset ι) : Triple ι :=
  ⟨ST.1 ∩ ST.2, ST.1 \ ST.2, ST.2 \ ST.1⟩

def join (GUV : Triple ι) : Finset ι × Finset ι :=
  (GUV.1 ∪ GUV.2.1, GUV.1 ∪ GUV.2.2)

lemma join_split (ST : Finset ι × Finset ι) : join (split ST) = ST := by
  apply Prod.ext
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

lemma split_mem {F : Finset ι} {ST : Finset ι × Finset ι}
    (hST : ST ∈ F.powerset ×ˢ F.powerset) : split ST ∈ triples F := by
  rcases Finset.mem_product.mp hST with ⟨hS, hT⟩
  have hSF := Finset.mem_powerset.mp hS
  have hTF := Finset.mem_powerset.mp hT
  simp only [triples, split, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨Finset.inter_subset_left.trans hSF, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hSF hi.1, by tauto⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hTF hi.1, by tauto⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

lemma join_mem {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    join GUV ∈ F.powerset ×ˢ F.powerset := by
  rcases (by simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
    Finset.mem_product, Finset.mem_powerset] using h) with ⟨hG, ⟨hU, hV⟩, _⟩
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_powerset.mpr
  · exact Finset.union_subset hG (hU.trans Finset.sdiff_subset)
  · exact Finset.union_subset hG (hV.trans Finset.sdiff_subset)

lemma split_join {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    split (join GUV) = GUV := by
  rcases GUV with ⟨G, U, V⟩
  have hh : G ⊆ F ∧ (U ⊆ F \ G ∧ V ⊆ F \ G) ∧ Disjoint U V := by
    simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powerset] using h
  rcases hh with ⟨_, ⟨hU, hV⟩, hd⟩
  have hUG : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hU hi)).2 hg)
  have hVG : Disjoint V G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hV hi)).2 hg)
  have h₀ : (G ∪ U) ∩ (G ∪ V) = G := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have h₁ : (G ∪ U) \ (G ∪ V) = U := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    have hj : i ∈ U → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hUG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have h₂ : (G ∪ V) \ (G ∪ U) = V := by
    ext i
    have hi : i ∈ V → i ∈ U → False := fun hi hj => Finset.disjoint_left.mp hd.symm hi hj
    have hj : i ∈ V → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hVG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  simp only [split, join, h₀, h₁, h₂]

theorem sum_pair_eq_overlap {β : Type*} [AddCommMonoid β]
    (F : Finset ι) (C : Finset ι → Finset ι → β) :
    (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, C S T) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then C (G ∪ U) (G ∪ V) else 0 := by
  classical
  have hs : (∑ ST ∈ F.powerset ×ˢ F.powerset, C ST.1 ST.2) =
      ∑ GUV ∈ triples F, C (join GUV).1 (join GUV).2 := by
    apply Finset.sum_bij (fun ST _ => split ST)
    · intro ST hST
      exact split_mem hST
    · intro ST hST SU hSU heq
      have hh := congrArg join heq
      simpa only [join_split] using hh
    · intro GUV hGUV
      exact ⟨join GUV, join_mem hGUV, split_join hGUV⟩
    · intro ST hST
      rw [join_split]
  simpa only [triples, Finset.sum_sigma, Finset.sum_filter, Finset.sum_product, join] using hs

end FiniteOverlapDecomposition

open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical

namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

theorem sum_powerset_split {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→β) :
    (∑S∈F.powerset,f S)=∑A∈B.powerset,∑U∈(F\B).powerset,f (A∪U) := by
  have hsplit (S : Finset ι) : S∩B∪S\B=S := by
    ext i
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have he : (∑S∈F.powerset,f S)=
      ∑AU∈B.powerset ×ˢ (F\B).powerset,f (AU.1∪AU.2) := by
    apply Finset.sum_bij (fun S _ => (S∩B,S\B))
    · intro S hS
      rw [Finset.mem_product,Finset.mem_powerset,Finset.mem_powerset]
      refine ⟨Finset.inter_subset_right,?_⟩
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) (Finset.mem_sdiff.mp hi).1,(Finset.mem_sdiff.mp hi).2⟩
    · intro S hS T hT he
      have hi := congrArg (fun AU : Finset ι×Finset ι => AU.1∪AU.2) he
      simpa only [hsplit] using hi
    · intro AU hAU
      rcases Finset.mem_product.mp hAU with ⟨hA,hU⟩
      have hAB := Finset.mem_powerset.mp hA
      have hUFB := Finset.mem_powerset.mp hU
      refine ⟨AU.1∪AU.2,Finset.mem_powerset.mpr (Finset.union_subset (hAB.trans hB) (hUFB.trans Finset.sdiff_subset)),?_⟩
      apply Prod.ext <;> ext i
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_inter,Finset.mem_union]
        tauto
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_sdiff,Finset.mem_union]
        tauto
    · intro S hS
      rw [hsplit]
  simpa only [Finset.sum_product] using he

theorem sum_pair_split_cube {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→Finset ι→β) :
    (∑S∈F.powerset,∑T∈F.powerset,f S T)=
      ∑A₂∈B.powerset,∑A₁∈B.powerset,∑C∈(F\B).powerset,
        ∑N∈((F\B)\C).powerset,∑P∈((F\B)\C).powerset,
          if Disjoint N P then f ((A₂∪C)∪N) ((A₁∪C)∪P) else 0 := by
  rw [sum_powerset_split F B hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  simp_rw [sum_powerset_split F B hB]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  rw [sum_pair_eq_overlap]
  simp only [Finset.union_assoc]

end FiniteOverlapDecomposition

open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open scoped BigOperators Classical
namespace IdealGaussCRT
theorem finite_prod_eq_iInf {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P)) :
    (∏ i, P i) = ⨅ i, P i := by
  simpa using (Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := P) (by
      intro i _ j _ hij
      exact hc hij))

noncomputable def quotientProdEquivPi {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P)) :
    (A ⧸ ∏ i, P i) ≃+* ∀ i, A ⧸ P i :=
  (Ideal.quotEquivOfEq (finite_prod_eq_iInf P hc)).trans
    (Ideal.quotientInfRingEquivPiQuotient P hc)

@[simp] theorem quotientProdEquivPi_mk {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P))
    (a : A) (i : ι) :
    quotientProdEquivPi P hc (Ideal.Quotient.mk (∏ j, P j) a) i =
      Ideal.Quotient.mk (P i) a := by
  simp only [quotientProdEquivPi, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl


end IdealGaussCRT
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
