/-
The nearest-point comparison is adapted from OpenAI’s formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Nearest points in the Eisenstein lattice

Integral coordinates make bounded norm sublevels finite, so distance to
any complex point attains a minimum. Comparison with the six neighboring
units bounds its squared distance by `1/3`, in either complex embedding.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein
open Coordinates

/-- Integral coordinates are controlled by twice the complex modulus. -/
lemma coordinates_norm_le (n : O) : ‖coords n‖≤2*‖ringComplex n‖ := by
  have hq := complex_norm_eval_sq (coords n).1 (coords n).2
  rw [eval_coords] at hq
  have hcoord (a b t : ℝ) (ht : 0≤t) (heq : t^2=a^2-a*b+b^2) :
      |a|≤2*t ∧ |b|≤2*t := by
    constructor <;> apply abs_le.mpr <;> constructor <;>
      nlinarith only [ht, heq, sq_nonneg (a-b), sq_nonneg (a+b),
        sq_nonneg (a-2*b), sq_nonneg (b-2*a)]
  have h := hcoord _ _ _ (norm_nonneg _) hq
  rw [Prod.norm_def, max_le_iff]
  exact ⟨by simpa only [Int.norm_eq_abs] using h.1,
    by simpa only [Int.norm_eq_abs] using h.2⟩

/-- A bounded disk contains only finitely many Eisenstein integers. -/
lemma finite_norm_sublevel (C : ℝ) : Set.Finite {n : O | ‖ringComplex n‖≤C} := by
  have hf : Set.Finite (Metric.closedBall (0 : ℤ×ℤ) (2*C)) :=
    (isCompact_closedBall _ _).finite_of_discrete
  apply (hf.preimage coordinateEquiv.injective.injOn).subset
  intro n hn
  change coords n ∈ Metric.closedBall 0 (2*C)
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (coordinates_norm_le n).trans (mul_le_mul_of_nonneg_left hn (by norm_num))

/-- Minimize over the finite disk containing every competitor to zero. -/
lemma exists_nearest_eisenstein (z : ℂ) :
    ∃n : O, ∀m : O, ‖z-ringComplex n‖≤‖z-ringComplex m‖ := by
  let S := {n : O | ‖z-ringComplex n‖≤‖z‖}
  have hf : S.Finite := (finite_norm_sublevel (2*‖z‖)).subset (by
    intro n hn
    change ‖z-ringComplex n‖≤‖z‖ at hn
    have ht := norm_sub_le z (z-ringComplex n)
    rw [sub_sub_cancel] at ht
    exact ht.trans (by change ‖z‖+‖z-ringComplex n‖≤2*‖z‖; linarith [hn]))
  have hne : S.Nonempty := ⟨0,by simp [S]⟩
  obtain ⟨n,hn,hmin⟩ := Set.exists_min_image S (fun n => ‖z-ringComplex n‖) hf hne
  refine ⟨n,fun m => ?_⟩
  by_cases hm : m∈S
  · exact hmin m hm
  · exact hn.trans (le_of_not_ge hm)

/-- The primitive root has real part `−1/2`; the imaginary sign is immaterial. -/
lemma complex_omega_coordinates :
    (ringComplex omega).re= -1/2 ∧ (ringComplex omega).im^2=3/4 := by
  have h0 := complex_norm_eval_sq 0 1
  have h1 := complex_norm_eval_sq 1 1
  norm_num only [eval, Int.cast_zero, Int.cast_one, zero_add, one_mul, map_add,
    map_one, zero_pow, zero_mul, sub_self, one_pow, zero_sub] at h0 h1
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply] at h0 h1
  simp only [Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,zero_add] at h1
  constructor <;> nlinarith only [h0,h1]

private lemma hexagon_norm_sq_bound (x y t : ℝ) (ht : t^2=3/4)
    (hx : |x|≤1/2)
    (h₁ : x+2*t*y≤1) (h₂ : x-2*t*y≤1)
    (h₃ : -x+2*t*y≤1) (h₄ : -x-2*t*y≤1) : x^2+y^2≤1/3 := by
  have ha : |x|+|2*t*y|≤1 := by
    rcases le_total 0 x with hp | hn <;> rcases le_total 0 (2*t*y) with hq | hr
    · simpa only [abs_of_nonneg hp,abs_of_nonneg hq] using h₁
    · simpa only [abs_of_nonneg hp,abs_of_nonpos hr,sub_eq_add_neg] using h₂
    · simpa only [abs_of_nonpos hn,abs_of_nonneg hq] using h₃
    · simpa only [abs_of_nonpos hn,abs_of_nonpos hr,sub_eq_add_neg] using h₄
  have hp : 0≤(1-|x|-|2*t*y|)*(1-|x|+|2*t*y|) :=
    mul_nonneg (by linarith only [ha]) (by linarith [abs_nonneg (2*t*y)])
  have hxprod : |x| * (2*|x|-1)≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (abs_nonneg x) (by linarith only [hx])
  have hxy : |2*t*y|^2=3*y^2 := by rw [sq_abs,mul_pow,mul_pow,ht]; ring
  nlinarith only [hp,hxprod,hxy,sq_abs x]

/-- The Eisenstein lattice has squared covering radius at most one third. -/
theorem exists_eisenstein_distance_sq_le_third (z : ℂ) :
    ∃n : O, Complex.normSq (z-ringComplex n)≤1/3 := by
  obtain ⟨n,hn⟩ := exists_nearest_eisenstein z
  let w := z-ringComplex n
  have hmin (u : O) : Complex.normSq w≤Complex.normSq (w-ringComplex u) := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
    apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa only [map_add,sub_add_eq_sub_sub] using hn (n+u)
  obtain ⟨hre,him⟩ := complex_omega_coordinates
  have h1 := hmin 1
  have hn1 := hmin (-1)
  have hω := hmin omega
  have hnω := hmin (-omega)
  have hη := hmin (1+omega)
  have hnη := hmin (-(1+omega))
  simp only [map_one,map_neg,map_add,Complex.normSq_apply,Complex.sub_re,
    Complex.sub_im,Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im,
    Complex.one_re,Complex.one_im,hre] at h1 hn1 hω hnω hη hnη
  refine ⟨n,?_⟩
  change Complex.normSq w≤1/3
  rw [Complex.normSq_apply,←sq,←sq]
  apply hexagon_norm_sq_bound _ _ _ him
  · apply abs_le.mpr
    constructor <;> nlinarith only [h1,hn1]
  · nlinarith only [hη,him]
  · nlinarith only [hnω,him]
  · nlinarith only [hω,him]
  · nlinarith only [hnη,him]

end GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.finite_norm_sublevel
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.exists_nearest_eisenstein
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.exists_eisenstein_distance_sq_le_third
