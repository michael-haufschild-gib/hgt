import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-!
# Circulant flat source currents with faithful amplitude retention

Exact reconstruction following the RunPod flat-current normalization discriminator.
Three cyclic column projections have an area-valued boundary current. A real graph
retains every complex source value without changing its first-jet trace pairing;
fixed constants give the logarithmic phase current unit coefficient after doubling.

This file does not assert arithmetic Hardy admission, operator-index landing,
source moderation, bounded inverse recovery, or the Riemann Hypothesis.
Paper proof and computation provenance: cubic-flat-current-normalization card/report.
-/

open scoped BigOperators ComplexConjugate Kronecker
open scoped Matrix.Norms.Elementwise
namespace RHTower
noncomputable section

def cubicCirculant {A : Type*} (a b c : A) : Matrix (Fin 3) (Fin 3) A :=
  !![a, b, c; c, a, b; b, c, a]

section Algebra
variable {A : Type*} [CommRing A]

theorem cubicCirculant_mul (a b c d e f : A) :
    cubicCirculant a b c * cubicCirculant d e f =
      cubicCirculant (a*d+b*f+c*e) (a*e+b*d+c*f) (a*f+b*e+c*d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCirculant, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem cubicCirculant_commute (a b c d e f : A) :
    cubicCirculant a b c * cubicCirculant d e f =
      cubicCirculant d e f * cubicCirculant a b c := by
  rw [cubicCirculant_mul, cubicCirculant_mul]
  congr 1 <;> ring

def cyclicSourceGram (x y : A) := cubicCirculant 1 x y
def cyclicSourceCurrent (x y : A) := cubicCirculant 0 (x-y^2) (x^2-y)
def cyclicSourceCurrentJet (x y dx dy : A) :=
  cubicCirculant 0 (dx-2*y*dy) (2*x*dx-dy)

theorem cyclicSource_flat (x y : A) :
    cyclicSourceGram x y * cyclicSourceCurrent x y =
      cyclicSourceCurrent x y * cyclicSourceGram x y :=
  cubicCirculant_commute _ _ _ _ _ _

def cyclicFrameProjection (t u v : A) (j : Fin 3) : Matrix (Fin 3) (Fin 3) A :=
  fun i k => cubicCirculant t u 0 i j * cubicCirculant t 0 v j k

theorem cyclicFrameProjection_idempotent (t u v : A) (h : t^2+u*v=1)
    (j : Fin 3) :
    cyclicFrameProjection t u v j * cyclicFrameProjection t u v j =
      cyclicFrameProjection t u v j := by
  have hdiag : ∀ j : Fin 3,
      (cubicCirculant t 0 v * cubicCirculant t u 0) j j = 1 := by
    intro j
    rw [cubicCirculant_mul]
    fin_cases j <;> simp [cubicCirculant]
    all_goals simpa [pow_two, mul_comm] using h
  ext i k
  simp only [Matrix.mul_apply, cyclicFrameProjection]
  calc
    ∑ l, (cubicCirculant t u 0 i j * cubicCirculant t 0 v j l) *
        (cubicCirculant t u 0 l j * cubicCirculant t 0 v j k) =
        cubicCirculant t u 0 i j *
          (∑ l, cubicCirculant t 0 v j l * cubicCirculant t u 0 l j) *
          cubicCirculant t 0 v j k := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by rw [← Matrix.mul_apply, hdiag]; ring

theorem cyclicFrameProjection_sum (t u v : A) (h : t^2+u*v=1) :
    cyclicFrameProjection t u v 0 + cyclicFrameProjection t u v 1 +
      cyclicFrameProjection t u v 2 = cyclicSourceGram (t*u) (t*v) := by
  have hm : cubicCirculant t u 0 * cubicCirculant t 0 v =
      cyclicSourceGram (t*u) (t*v) := by
    rw [cubicCirculant_mul]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    have hh : t*t+u*v=1 := by simpa [pow_two] using h
    rw [hh]
    simp [cyclicSourceGram, mul_comm]
  ext i k
  have hi := congrFun (congrFun hm i) k
  simpa [cyclicFrameProjection, Matrix.mul_apply, Fin.sum_univ_three] using hi

def cyclicTripleCurrent (p q r : Matrix (Fin 3) (Fin 3) A) :=
  (p*q-q*p)+(q*r-r*q)+(r*p-p*r)

theorem cyclicFrameProjection_current_raw (t u v : A) :
    cyclicTripleCurrent (cyclicFrameProjection t u v 0)
      (cyclicFrameProjection t u v 1) (cyclicFrameProjection t u v 2) =
      cubicCirculant 0 ((t^2+u*v)*(t*u)-(t*v)^2)
        ((t*u)^2-(t^2+u*v)*(t*v)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicTripleCurrent, cyclicFrameProjection, cubicCirculant,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem cyclicFrameProjection_current (t u v : A) (h : t^2+u*v=1) :
    cyclicTripleCurrent (cyclicFrameProjection t u v 0)
      (cyclicFrameProjection t u v 1) (cyclicFrameProjection t u v 2) =
      cyclicSourceCurrent (t*u) (t*v) := by
  rw [cyclicFrameProjection_current_raw, h]
  simp only [one_mul]
  rfl

/-- Exact first-jet transgression: a polynomial derivative plus oriented area. -/
theorem cyclicSource_trace_transgression (x y dx dy : A) :
    Matrix.trace (cyclicSourceGram x y * cyclicSourceCurrentJet x y dx dy) =
      6*x^2*dx-6*y^2*dy+3*(y*dx-x*dy) := by
  simp [cyclicSourceGram, cyclicSourceCurrentJet,
    Matrix.trace, Matrix.diag, Fin.sum_univ_three, cubicCirculant, Matrix.mul_apply]
  ring

/-- The differential two-form is constant, unlike the two-channel spectral curve. -/
theorem cyclicSource_trace_curvature (x y a b c d : A) :
    Matrix.trace (cubicCirculant 0 a b * cyclicSourceCurrentJet x y c d -
      cubicCirculant 0 c d * cyclicSourceCurrentJet x y a b) =
      -6*(a*d-b*c) := by
  simp [cyclicSourceCurrentJet, Matrix.trace,
    Matrix.diag, Fin.sum_univ_three, cubicCirculant]
  ring

end Algebra

theorem cyclicFrameProjection_selfAdjoint (t : ℝ) (u : ℂ) (j : Fin 3) :
    (cyclicFrameProjection (t : ℂ) u (conj u) j).conjTranspose =
      cyclicFrameProjection (t : ℂ) u (conj u) j := by
  ext i k
  fin_cases i <;> fin_cases k <;> fin_cases j <;>
    simp [cyclicFrameProjection, cubicCirculant, Matrix.conjTranspose_apply,
      mul_comm]

/-- The declared first jet is the actual derivative of the matrix current. -/
theorem hasDerivAt_cyclicSourceCurrent {x y : ℝ → ℂ} {dx dy : ℂ} {s : ℝ}
    (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s) :
    HasDerivAt (fun w => cyclicSourceCurrent (x w) (y w))
      (cyclicSourceCurrentJet (x s) (y s) dx dy) s := by
  have hleft : HasDerivAt (fun w => x w-y w^2) (dx-2*y s*dy) s := by
    convert hx.sub (hy.pow 2) using 1
    · congr
    · rfl
    · norm_num
  have hright : HasDerivAt (fun w => x w^2-y w) (2*x s*dx-dy) s := by
    convert (hx.pow 2).sub hy using 1
    · congr
    · rfl
    · norm_num
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    first
    | simpa [cyclicSourceCurrent, cyclicSourceCurrentJet, cubicCirculant,
        pow_one] using hleft
    | simpa [cyclicSourceCurrent, cyclicSourceCurrentJet, cubicCirculant,
        pow_one] using hright
    | simpa [cyclicSourceCurrent, cyclicSourceCurrentJet, cubicCirculant]
        using (hasDerivAt_const s (0:ℂ))

/-- Two identical circulant frames give coefficient one for the logarithmic phase
current when `6*r²=1`. No winding number is inserted into the construction. -/
theorem cyclicSource_twoCopy_unit_normalization
    (r u v du dv : ℂ) (hr : 6*r^2=1) (huv : u*v=1)
    (htangent : u*dv+v*du=0) :
    2 * Matrix.trace (cyclicSourceGram (r*u) (r*v) *
      cyclicSourceCurrentJet (r*u) (r*v) (r*du) (r*dv)) =
      12*(r*u)^2*(r*du)-12*(r*v)^2*(r*dv)+2*(du/u) := by
  have hu : u ≠ 0 := by intro hz; simp [hz] at huv
  have hdiv : du/u=v*du := by
    apply (div_eq_iff hu).2
    calc
      du = du*(u*v) := by rw [huv]; ring
      _ = v*du*u := by ring
  rw [cyclicSource_trace_transgression, hdiv]
  linear_combination (2*v*du)*hr - (6*r^2)*htangent

/-- Real amplitude is retained in a rank-one graph, not discarded by phase normalization. -/
def cyclicAmplitudeGraph (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/(1+(a:ℂ)^2), (a:ℂ)/(1+(a:ℂ)^2);
     (a:ℂ)/(1+(a:ℂ)^2), (a:ℂ)^2/(1+(a:ℂ)^2)]

private theorem cyclicAmplitudeDenom_ne (a : ℝ) : 1+(a:ℂ)^2 ≠ 0 := by
  exact_mod_cast (ne_of_gt (by positivity : (0:ℝ)<1+a^2))

theorem cyclicAmplitudeGraph_idempotent (a : ℝ) :
    cyclicAmplitudeGraph a * cyclicAmplitudeGraph a = cyclicAmplitudeGraph a := by
  have hd := cyclicAmplitudeDenom_ne a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicAmplitudeGraph, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

theorem cyclicAmplitudeGraph_selfAdjoint (a : ℝ) :
    (cyclicAmplitudeGraph a).conjTranspose = cyclicAmplitudeGraph a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicAmplitudeGraph, Matrix.conjTranspose_apply]

theorem cyclicAmplitudeGraph_trace (a : ℝ) :
    Matrix.trace (cyclicAmplitudeGraph a) = 1 := by
  have hd := cyclicAmplitudeDenom_ne a
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, cyclicAmplitudeGraph]
  field_simp

def cyclicAmplitudeGraphJet (a da : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-2*(a:ℂ)*da/(1+(a:ℂ)^2)^2, (1-(a:ℂ)^2)*da/(1+(a:ℂ)^2)^2;
     (1-(a:ℂ)^2)*da/(1+(a:ℂ)^2)^2, 2*(a:ℂ)*da/(1+(a:ℂ)^2)^2]

theorem cyclicAmplitudeGraph_trace_tangent (a da : ℝ) :
    Matrix.trace (cyclicAmplitudeGraph a * cyclicAmplitudeGraphJet a da) = 0 := by
  have hd := cyclicAmplitudeDenom_ne a
  simp [cyclicAmplitudeGraph, cyclicAmplitudeGraphJet, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

/-- The amplitude graph has no cost in the boundary one-form. This is an exact
identity of first jets, not a claim that subsequent nonlinear recovery is bounded. -/
theorem cyclicAmplitudeGraph_preserves_boundary_current (a da : ℝ)
    (G K dK : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.trace ((cyclicAmplitudeGraph a ⊗ₖ G) *
      (cyclicAmplitudeGraphJet a da ⊗ₖ K + cyclicAmplitudeGraph a ⊗ₖ dK)) =
      Matrix.trace (G*dK) := by
  rw [Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Matrix.trace_kronecker,
    cyclicAmplitudeGraph_idempotent, cyclicAmplitudeGraph_trace,
    cyclicAmplitudeGraph_trace_tangent]
  ring

def cyclicFaithfulSourceAggregate (r : ℝ) (z : ℂ) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  cyclicAmplitudeGraph ‖z‖ ⊗ₖ
    cyclicSourceGram ((r:ℂ)*(z/(‖z‖:ℂ))) ((r:ℂ)*conj (z/(‖z‖:ℂ)))

def cyclicFaithfulSourceRecover (r : ℝ)
    (M : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) : ℂ :=
  M (0,0) (1,0) * M (0,0) (0,1) / ((r:ℂ)*M (0,0) (0,0)^2)

/-- All literal source values survive the nonlinear projection encoding. In
particular two source functions with equal encoded matrices are equal pointwise. -/
theorem cyclicFaithfulSourceRecover_eq (r : ℝ) (hr : r ≠ 0) (z : ℂ) :
    cyclicFaithfulSourceRecover r (cyclicFaithfulSourceAggregate r z) = z := by
  have hrc : (r:ℂ) ≠ 0 := by exact_mod_cast hr
  have hd := cyclicAmplitudeDenom_ne ‖z‖
  by_cases hz : z = 0
  · subst z
    simp [cyclicFaithfulSourceRecover, cyclicFaithfulSourceAggregate,
      cyclicAmplitudeGraph, cyclicSourceGram, cubicCirculant,
      Matrix.kroneckerMap_apply]
  · have hn : (‖z‖:ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    simp [cyclicFaithfulSourceRecover, cyclicFaithfulSourceAggregate,
      cyclicAmplitudeGraph, cyclicSourceGram, cubicCirculant,
      Matrix.kroneckerMap_apply]
    field_simp

theorem cyclicFaithfulSourceAggregate_injective (r : ℝ) (hr : r ≠ 0) :
    Function.Injective (cyclicFaithfulSourceAggregate r) := by
  intro z w h
  have hh := congrArg (cyclicFaithfulSourceRecover r) h
  simpa only [cyclicFaithfulSourceRecover_eq r hr] using hh

/-- Tensoring retains honest orthogonal projections and not only their aggregate. -/
theorem cyclicAmplitudeGraph_projection_lift (a t : ℝ) (u : ℂ)
    (h : (t:ℂ)^2+u*conj u=1) (j : Fin 3) :
    let P := cyclicAmplitudeGraph a ⊗ₖ cyclicFrameProjection (t:ℂ) u (conj u) j
    P*P=P ∧ P.conjTranspose=P := by
  dsimp
  constructor
  · rw [← Matrix.mul_kronecker_mul, cyclicAmplitudeGraph_idempotent,
      cyclicFrameProjection_idempotent _ _ _ h]
  · rw [Matrix.conjTranspose_kronecker, cyclicAmplitudeGraph_selfAdjoint,
      cyclicFrameProjection_selfAdjoint]

/-- Source-independent real constants implement the two-copy unit normalization. -/
theorem exists_cyclicSource_unit_constants :
    ∃ t b : ℝ, t^2+b^2=1 ∧ 6*(t*b)^2=1 ∧ t*b ≠ 0 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs3 : Real.sqrt 3 < 3 := by nlinarith
  let t := Real.sqrt ((3+Real.sqrt 3)/6)
  let b := Real.sqrt ((3-Real.sqrt 3)/6)
  have ht : t^2=(3+Real.sqrt 3)/6 := Real.sq_sqrt (by positivity)
  have hb : b^2=(3-Real.sqrt 3)/6 := Real.sq_sqrt (by positivity)
  have htb : 6*(t*b)^2=1 := by rw [mul_pow, ht, hb]; nlinarith
  refine ⟨t,b,?_,htb,?_⟩
  · rw [ht,hb]; ring
  · intro hz
    rw [hz] at htb
    norm_num at htb

theorem cyclicSource_phase_unit {z : ℂ} (hz : z ≠ 0) :
    (z/(‖z‖:ℂ))*conj (z/(‖z‖:ℂ)) = 1 := by
  have hn : (‖z‖:ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hzz : z*conj z=(‖z‖:ℂ)^2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp [div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_pow, hn, ← pow_two]

/-- One fixed, value-faithful family of honest source projections, with the
constant required by two-copy unit boundary normalization. This does not assert
trace-class operator admission or a bound on the nonlinear recovery map. -/
theorem exists_unit_normalized_faithful_cyclicSource_family :
    ∃ r : ℝ, r ≠ 0 ∧ 6*r^2=1 ∧
      Function.Injective (cyclicFaithfulSourceAggregate r) ∧
      ∀ z : ℂ, z ≠ 0 →
        ∃ P : Fin 3 → Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ,
          (∀ j, P j*P j=P j ∧ (P j).conjTranspose=P j) ∧
          P 0+P 1+P 2=cyclicFaithfulSourceAggregate r z := by
  obtain ⟨t,b,hnorm,hunit,hne⟩ := exists_cyclicSource_unit_constants
  refine ⟨t*b,hne,hunit,cyclicFaithfulSourceAggregate_injective _ hne,?_⟩
  intro z hz
  let u : ℂ := (b:ℂ)*(z/(‖z‖:ℂ))
  have hphase := cyclicSource_phase_unit hz
  have hncomplex : (t:ℂ)^2+(b:ℂ)^2=1 := by exact_mod_cast hnorm
  have hu : (t:ℂ)^2+u*conj u=1 := by
    dsimp [u]
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination hncomplex + (b:ℂ)^2*hphase
  refine ⟨fun j => cyclicAmplitudeGraph ‖z‖ ⊗ₖ
    cyclicFrameProjection (t:ℂ) u (conj u) j, ?_, ?_⟩
  · exact fun j => cyclicAmplitudeGraph_projection_lift ‖z‖ t u hu j
  · have hs := congrArg (fun M => cyclicAmplitudeGraph ‖z‖ ⊗ₖ M)
      (cyclicFrameProjection_sum (t:ℂ) u (conj u) hu)
    simpa [Matrix.kronecker_add, cyclicFaithfulSourceAggregate, u,
      map_mul, mul_assoc] using hs

/-- Rational-entry witness reconstructed after the numerical falsification. -/
def cyclicFlatCounterProjection (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i k => (1/2:ℂ) * cubicCirculant 1 1 0 i j * cubicCirculant 1 0 1 j k

theorem cyclicFlatCounterProjection_orthogonal (j : Fin 3) :
    cyclicFlatCounterProjection j * cyclicFlatCounterProjection j =
      cyclicFlatCounterProjection j ∧
    (cyclicFlatCounterProjection j).conjTranspose = cyclicFlatCounterProjection j := by
  constructor <;> ext i k <;> fin_cases i <;> fin_cases k <;> fin_cases j <;>
    norm_num [cyclicFlatCounterProjection, cubicCirculant, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three, Matrix.cons_val_two]

theorem cyclicFlatCounterProjection_aggregate :
    cyclicFlatCounterProjection 0 + cyclicFlatCounterProjection 1 +
      cyclicFlatCounterProjection 2 = cyclicSourceGram (1/2:ℂ) (1/2:ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicFlatCounterProjection, cubicCirculant, cyclicSourceGram,
      Matrix.cons_val_two]

theorem cyclicFlatCounterProjection_current :
    cyclicTripleCurrent (cyclicFlatCounterProjection 0) (cyclicFlatCounterProjection 1)
      (cyclicFlatCounterProjection 2) = cyclicSourceCurrent (1/2:ℂ) (1/2:ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicTripleCurrent, cyclicFlatCounterProjection, cubicCirculant,
      cyclicSourceCurrent, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]

theorem cyclicFlatCounterProjection_casimir :
    let S := cyclicSourceGram (1/2:ℂ) (1/2:ℂ)
    let K := cyclicSourceCurrent (1/2:ℂ) (1/2:ℂ)
    K * (3*K^2+S^2*(3-S)^2) = K := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [cyclicSourceGram, cyclicSourceCurrent, pow_two,
      Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_three, Matrix.ofNat_apply, cubicCirculant,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> norm_num [Matrix.cons_val_two, Fin.ext_iff]

theorem cyclicFlatCounterProjection_current_ne_zero :
    cyclicSourceCurrent (1/2:ℂ) (1/2:ℂ) ≠ 0 := by
  intro h
  have hh := congrFun (congrFun h 0) 1
  norm_num [cyclicSourceCurrent, cubicCirculant] at hh

end
end RHTower

