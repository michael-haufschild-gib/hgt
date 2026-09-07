import GaloisForLFunctions.RHTower.EulerDeletionJointNilpotentWitness
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleSecondConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Actual weighted circulation and the fifth chronological word

Finite identities retain all terminal terms before using source-specific zero landing.
The actual weighted fifth word equals an absolutely convergent polynomial circulation
at every zeta zero with real part greater than one fifth. In the open strip above that
line, absolute convergence of this literal source is equivalent to zeta vanishing:
nonzero endpoint products retain a nonsummable first-order tail.

All source factors, within-segment terms, and endpoint corrections are explicit.
No numerical premise, added axiom, or critical-line selection is supplied.
-/

open Filter Topology
open scoped BigOperators Matrix.Norms.Operator
namespace RHTower.DeletionJointCirculation
open DeletionJointSharpness GaloisForLFunctions.HTGeometry.NoncommutativeAbel
noncomputable section
local instance : TopologicalSpace A := (inferInstance : NormedRing A).toUniformSpace.toTopologicalSpace

/-- Actual complex polynomial line integral on one straight segment. -/
def segment (x y a b : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, (x+(t:ℂ)*a)*(y+(t:ℂ)*b)^3*a

private theorem integral_quartic (a b c d e : ℂ) :
    (∫ t in (0:ℝ)..1, a + b*(t:ℂ) + c*(t:ℂ)^2 + d*(t:ℂ)^3 + e*(t:ℂ)^4) =
      a + b/2 + c/3 + d/4 + e/5 := by
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun u : ℝ => a*(u:ℂ) + b*(u:ℂ)^2/2 + c*(u:ℂ)^3/3 +
        d*(u:ℂ)^4/4 + e*(u:ℂ)^5/5)
      (a + b*(t:ℂ) + c*(t:ℂ)^2 + d*(t:ℂ)^3 + e*(t:ℂ)^4) t := by
    intro t _
    have ht : HasDerivAt (fun u : ℝ => (u:ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    convert ((((ht.const_mul a).add (((ht.pow 2).const_mul b).div_const 2)).add
      (((ht.pow 3).const_mul c).div_const 3)).add
      (((ht.pow 4).const_mul d).div_const 4)).add
      (((ht.pow 5).const_mul e).div_const 5) using 1
    all_goals first | rfl | ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num

/-- Symbolic evaluation of the literal segment integral, with complex increments unchanged. -/
theorem segment_eq (x y a b : ℂ) :
    segment x y a b = a*x*y^3 + (a^2*y^3+3*a*x*y^2*b)/2 +
      (3*a^2*y^2*b+3*a*x*y*b^2)/3 + (3*a^2*y*b^2+a*x*b^3)/4 + a^2*b^3/5 := by
  unfold segment
  have he : (fun t : ℝ => (x+(t:ℂ)*a)*(y+(t:ℂ)*b)^3*a) =
      fun t : ℝ => a*x*y^3 + (a^2*y^3+3*a*x*y^2*b)*(t:ℂ) +
      (3*a^2*y^2*b+3*a*x*y*b^2)*(t:ℂ)^2 +
      (3*a^2*y*b^2+a*x*b^3)*(t:ℂ)^3 + a^2*b^3*(t:ℂ)^4 := by funext t; ring
  rw [he, integral_quartic]

/-- Chronological development of arbitrary complex straight-segment increments. -/
def pathProduct (a b : ℕ → ℂ) : ℕ → A :=
  orderedProduct (fun n => chainExp (a n) (b n))

def endpoint (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, a n

private theorem row_step (M : A) (a b : ℂ) :
    (M*chainExp a b) 0 =
      ![M 0 0, M 0 0*a+M 0 1, M 0 0*a^2/2+M 0 1*a+M 0 2,
        M 0 0*a^2*b/6+M 0 1*a*b/2+M 0 2*b+M 0 3,
        M 0 0*a^2*b^2/24+M 0 1*a*b^2/6+M 0 2*b^2/2+M 0 3*b+M 0 4,
        M 0 0*a^2*b^3/120+M 0 1*a*b^3/24+M 0 2*b^3/6+M 0 3*b^2/2+
          M 0 4*b+M 0 5] := by
  ext j
  fin_cases j <;> norm_num [chainExp, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> rfl

/-- The first repeated-letter coordinates are exact endpoint powers. -/
theorem prefix_first_coordinates (a b : ℕ → ℂ) (N : ℕ) :
    pathProduct a b N 0 0 = 1 ∧ pathProduct a b N 0 1 = endpoint a N ∧
      pathProduct a b N 0 2 = (endpoint a N)^2/2 := by
  induction N with
  | zero => simp [pathProduct, orderedProduct, endpoint]
  | succ N ih =>
    change ((pathProduct a b N)*chainExp (a N) (b N)) 0 0 = 1 ∧
      ((pathProduct a b N)*chainExp (a N) (b N)) 0 1 = _ ∧
      ((pathProduct a b N)*chainExp (a N) (b N)) 0 2 = _
    rw [row_step]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      ih.1, ih.2.1, ih.2.2, endpoint, Finset.sum_range_succ]
    constructor
    · trivial
    constructor <;> ring

/-- Complete terminal polynomial; the lower-word endpoint terms are retained. -/
def boundary (a b : ℕ → ℂ) (N : ℕ) : ℂ :=
  -6*pathProduct a b N 0 5 + 6*endpoint b N*pathProduct a b N 0 4 -
    3*(endpoint b N)^2*pathProduct a b N 0 3 + (endpoint a N)^2*(endpoint b N)^3/2

/-- Exact finite circulation identity, with no closure premise. -/
theorem finite_circulation_eq_boundary (a b : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, segment (endpoint a n) (endpoint b n) (a n) (b n) =
      boundary a b N := by
  induction N with
  | zero => simp [boundary, pathProduct, orderedProduct, endpoint]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, segment_eq]
    have h := prefix_first_coordinates a b N
    have hs : pathProduct a b (N+1) = pathProduct a b N * chainExp (a N) (b N) := rfl
    simp only [boundary, hs, row_step, Matrix.cons_val, h.1, h.2.1, h.2.2, endpoint, Finset.sum_range_succ]
    ring


private def coordinate (j : Fin 6) : A →ₗ[ℂ] ℂ where
  toFun M := M 0 j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Closed coordinate endpoints remove precisely the finite terminal terms. -/
theorem circulation_limit_of_closed_endpoints {a b : ℕ → ℂ} {U : A}
    (hU : Tendsto (pathProduct a b) atTop (nhds U))
    (ha : Tendsto (endpoint a) atTop (nhds 0))
    (hb : Tendsto (endpoint b) atTop (nhds 0)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      segment (endpoint a n) (endpoint b n) (a n) (b n)) atTop (nhds (-6*U 0 5)) := by
  have hc (j : Fin 6) : Tendsto (fun N => pathProduct a b N 0 j) atTop (nhds (U 0 j)) := by
    simpa only [Function.comp_def, coordinate, LinearMap.coe_mk, AddHom.coe_mk] using
      ((coordinate j).continuous_of_finiteDimensional.tendsto U).comp hU
  have ht := (((hc 5).const_mul (-6)).add ((hb.mul (hc 4)).const_mul 6)).sub
    (((hb.pow 2).mul (hc 3)).const_mul 3)
  have ht := ht.add (((ha.pow 2).mul (hb.pow 3)).div_const 2)
  simp only [zero_pow (by omega : 2 ≠ 0), zero_pow (by omega : 3 ≠ 0),
    zero_mul, mul_zero, zero_div, add_zero, sub_zero] at ht
  convert ht using 1
  funext N
  rw [finite_circulation_eq_boundary]
  unfold boundary
  ring

private theorem smul_chain_eq (z a b : ℂ) : z • chain a b = chain (z*a) (z*b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chain, Matrix.smul_apply]

/-- The segment increments are the literal Dirichlet-weighted deletion source. -/
theorem source_factor_eq_chainExp (s : ℂ) (n : ℕ) :
    DeletionJointProduct.sourceFactor generatorX generatorY s n =
      chainExp (eulerDeletionWeightedJump 1 s n) (eulerDeletionWeightedJump 2 s n) := by
  unfold DeletionJointProduct.sourceFactor
  rw [sourceVelocity_chain, smul_chain_eq, exp_chain]
  congr 1 <;> simp only [eulerDeletionWeightedJump, eulerDeletionDirichletCoefficient,
    arithmeticDirichletWeight, Nat.reduceAdd] <;> ring

/-- Exact identification at every chronological cutoff, including incomplete six-blocks. -/
theorem source_product_eq_pathProduct (s : ℂ) (N : ℕ) :
    orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY s) N =
      pathProduct (eulerDeletionWeightedJump 1 s) (eulerDeletionWeightedJump 2 s) N := by
  unfold pathProduct
  congr 1
  funext n
  exact source_factor_eq_chainExp s n

/-- The full weighted polynomial circulation of the actual pair of deletion paths. -/
def sourceSegment (s : ℂ) (n : ℕ) : ℂ :=
  segment (endpoint (eulerDeletionWeightedJump 1 s) n)
    (endpoint (eulerDeletionWeightedJump 2 s) n)
    (eulerDeletionWeightedJump 1 s n) (eulerDeletionWeightedJump 2 s n)

/-- A straight-segment bound keeps all four position factors and the actual jump. -/
theorem norm_segment_le (x y a b : ℂ) :
    ‖segment x y a b‖ ≤ (‖x‖+‖a‖)*(‖y‖+‖b‖)^3*‖a‖ := by
  have ht : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖(x+(t:ℂ)*a)*(y+(t:ℂ)*b)^3*a‖ ≤ (‖x‖+‖a‖)*(‖y‖+‖b‖)^3*‖a‖ := by
    intro t ht
    have hti : 0 < t ∧ t ≤ 1 := by simpa using ht
    have htn : ‖(t:ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hti.1] using hti.2
    have hx : ‖x+(t:ℂ)*a‖ ≤ ‖x‖+‖a‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      nlinarith [norm_nonneg a]
    have hy : ‖y+(t:ℂ)*b‖ ≤ ‖y‖+‖b‖ := by
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      nlinarith [norm_nonneg b]
    simp only [norm_mul, norm_pow]
    gcongr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const ht
  simpa only [segment, sub_zero, abs_one, mul_one] using h

/-- Source-derived fifth-power decay at zeros; no frozen coefficient or sign replacement. -/
theorem norm_sourceSegment_le_at_zero {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) (n : ℕ) :
    ‖sourceSegment s n‖ ≤
      (eulerDeletionAbelTailConstant 1 s+1)*(eulerDeletionAbelTailConstant 2 s+2)^3 *
        ((n:ℝ)+1)^(-5*s.re) := by
  have hx := norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero 1 n hs hs1 hz
  have hy := norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero 2 n hs hs1 hz
  have ha := norm_eulerDeletionWeightedJump_le (q := 1) (by omega) s n
  have hb := norm_eulerDeletionWeightedJump_le (q := 2) (by omega) s n
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at ha hb
  have hA : 0 ≤ eulerDeletionAbelTailConstant 1 s := by unfold eulerDeletionAbelTailConstant; positivity
  have hB : 0 ≤ eulerDeletionAbelTailConstant 2 s := by unfold eulerDeletionAbelTailConstant; positivity
  calc
    ‖sourceSegment s n‖ ≤
      (‖endpoint (eulerDeletionWeightedJump 1 s) n‖+‖eulerDeletionWeightedJump 1 s n‖)*
      (‖endpoint (eulerDeletionWeightedJump 2 s) n‖+‖eulerDeletionWeightedJump 2 s n‖)^3*
        ‖eulerDeletionWeightedJump 1 s n‖ := norm_segment_le _ _ _ _
    _ ≤ (eulerDeletionAbelTailConstant 1 s*((n:ℝ)+1)^(-s.re)+1*((n:ℝ)+1)^(-s.re))*
      (eulerDeletionAbelTailConstant 2 s*((n:ℝ)+1)^(-s.re)+2*((n:ℝ)+1)^(-s.re))^3*
        (1*((n:ℝ)+1)^(-s.re)) := by
      dsimp only [endpoint]
      gcongr
    _ = (eulerDeletionAbelTailConstant 1 s+1)*(eulerDeletionAbelTailConstant 2 s+2)^3 *
        (((n:ℝ)+1)^(-s.re))^5 := by ring
    _ = _ := by
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      norm_num
      ring

/-- At every source zero beyond one fifth, the literal circulation is absolutely summable. -/
theorem sourceSegment_summable_at_zero {s : ℂ} (hs : (1:ℝ)/5 < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    Summable (fun n => ‖sourceSegment s n‖) := by
  have hp : Summable (fun n : ℕ => (n:ℝ)^(-5*s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hh := (summable_nat_add_iff (f := fun n : ℕ => (n:ℝ)^(-5*s.re)) 1).2 hp
  have hh := hh.mul_left
    ((eulerDeletionAbelTailConstant 1 s+1)*(eulerDeletionAbelTailConstant 2 s+2)^3)
  simp only [Nat.cast_add, Nat.cast_one] at hh
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_sourceSegment_le_at_zero (by linarith) hs1 hz) hh

/-- The actual fifth chronological word at a zero is an absolutely convergent complex circulation. -/
theorem source_fifth_word_at_zero {s : ℂ} (hs : (1:ℝ)/5 < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∃ U : A, IsUnit U ∧
      Tendsto (orderedProduct (DeletionJointProduct.sourceFactor generatorX generatorY s))
        atTop (nhds U) ∧
      Summable (fun n => ‖sourceSegment s n‖) ∧
      U 0 5 = -(∑' n, sourceSegment s n)/6 := by
  obtain ⟨U,hunit,hU⟩ := DeletionJointProduct.sourceProduct_converges_to_unit
    generatorX generatorY hs
  have hsum := sourceSegment_summable_at_zero hs hs1 hz
  refine ⟨U,hunit,hU,hsum,?_⟩
  have hP : Tendsto (pathProduct (eulerDeletionWeightedJump 1 s)
      (eulerDeletionWeightedJump 2 s)) atTop (nhds U) := by
    exact hU.congr (fun N => source_product_eq_pathProduct s N)
  have ha : Tendsto (endpoint (eulerDeletionWeightedJump 1 s)) atTop (nhds 0) :=
    tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero 1 (by linarith) hs1 hz
  have hb : Tendsto (endpoint (eulerDeletionWeightedJump 2 s)) atTop (nhds 0) :=
    tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero 2 (by linarith) hs1 hz
  have ht : Tendsto (fun N => ∑ n ∈ Finset.range N, sourceSegment s n) atTop
      (nhds (-6*U 0 5)) := circulation_limit_of_closed_endpoints hP ha hb
  have he := tendsto_nhds_unique ht hsum.of_norm.hasSum.tendsto_sum_nat
  linear_combination -he/6


/-- Polynomial multiplier of the actual first-coordinate increment. -/
def segmentResponse (x y a b : ℂ) : ℂ :=
  x*y^3 + (a*y^3+3*x*y^2*b)/2 + (3*a*y^2*b+3*x*y*b^2)/3 +
    (3*a*y*b^2+x*b^3)/4 + a*b^3/5

theorem segment_eq_mul_response (x y a b : ℂ) :
    segment x y a b = a*segmentResponse x y a b := by
  rw [segment_eq, segmentResponse]
  ring

theorem segmentResponse_tendsto {x y a b : ℕ → ℂ} {X Y : ℂ}
    (hx : Tendsto x atTop (nhds X)) (hy : Tendsto y atTop (nhds Y))
    (ha : Tendsto a atTop (nhds 0)) (hb : Tendsto b atTop (nhds 0)) :
    Tendsto (fun n => segmentResponse (x n) (y n) (a n) (b n)) atTop (nhds (X*Y^3)) := by
  have hc : Continuous (fun v : (ℂ × ℂ) × (ℂ × ℂ) =>
      segmentResponse v.1.1 v.1.2 v.2.1 v.2.2) := by unfold segmentResponse; fun_prop
  simpa only [Function.comp_def, segmentResponse, zero_mul, mul_zero, zero_div,
    zero_pow (by omega : 2 ≠ 0), zero_pow (by omega : 3 ≠ 0), add_zero] using
      (hc.tendsto ((X,Y),(0,0))).comp ((hx.prodMk_nhds hy).prodMk_nhds (ha.prodMk_nhds hb))

/-- The modulus-two coefficient has unit norm at every arithmetic index. -/
theorem norm_two_jump (s : ℂ) (n : ℕ) :
    ‖eulerDeletionWeightedJump 1 s n‖ = ((n:ℝ)+1)^(-s.re) := by
  rw [eulerDeletionWeightedJump, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  have h : ‖eulerDeletionDirichletCoefficient 1 n‖ = 1 := by
    by_cases hd : 2 ∣ n+1 <;>
      norm_num [eulerDeletionDirichletCoefficient, blockDeletionCoefficient, hd]
  rw [h, one_mul]

/-- Actual endpoint convergence, without assuming it vanishes. -/
theorem source_endpoint_tendsto (q : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (endpoint (eulerDeletionWeightedJump q s)) atTop
      (nhds (eulerDeletionDirichletSum q s)) := by
  have ht := GaloisForLFunctions.RHTower.tendsto_dirichletSum
    (eulerDeletionDirichlet_convergesAt (q := q) hs)
  change Tendsto (fun N => ∑ n ∈ Finset.range N, eulerDeletionWeightedJump q s n) atTop _
  simpa only [GaloisForLFunctions.RHTower.dirichletPartialSum,
    eulerDeletionWeightedJump, eulerDeletionDirichletSum] using ht

private theorem source_jump_tendsto (q : ℕ) (hq : 0 < q) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (eulerDeletionWeightedJump q s) atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => ((n:ℝ)+1)^(-s.re)) atTop (nhds 0) := by
    have hw := (arithmeticDirichletWeight_tendsto_zero hs).norm
    simpa only [norm_zero] using hw.congr (fun n => by
      rw [arithmeticDirichletWeight, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.neg_re])
  apply squeeze_zero_norm (fun n => norm_eulerDeletionWeightedJump_le hq s n)
  simpa only [mul_zero] using hp.const_mul (q:ℝ)

/-- The normalized segment multiplier retains the actual nonzero endpoint product off zeros. -/
theorem source_response_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n => segmentResponse
      (endpoint (eulerDeletionWeightedJump 1 s) n)
      (endpoint (eulerDeletionWeightedJump 2 s) n)
      (eulerDeletionWeightedJump 1 s n) (eulerDeletionWeightedJump 2 s n)) atTop
      (nhds (eulerDeletionDirichletSum 1 s*(eulerDeletionDirichletSum 2 s)^3)) :=
    segmentResponse_tendsto (source_endpoint_tendsto 1 hs) (source_endpoint_tendsto 2 hs)
      (source_jump_tendsto 1 (by omega) hs) (source_jump_tendsto 2 (by omega) hs)

/-- Absolute circulation below exponent one forces its actual endpoint multiplier to vanish. -/
theorem endpoint_product_eq_zero_of_summable {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 1)
    (habs : Summable (fun n => ‖sourceSegment s n‖)) :
    eulerDeletionDirichletSum 1 s*(eulerDeletionDirichletSum 2 s)^3 = 0 := by
  by_contra hne
  let L := eulerDeletionDirichletSum 1 s*(eulerDeletionDirichletSum 2 s)^3
  have hL : 0 < ‖L‖ := norm_pos_iff.mpr hne
  have he := (source_response_tendsto hs).norm.eventually
    (eventually_gt_nhds (show ‖L‖/2 < ‖L‖ by linarith))
  have hh : Summable (fun n : ℕ => ((n:ℝ)+1)^(-s.re)) := by
    apply Summable.of_norm_bounded_eventually_nat (habs.mul_left (2/‖L‖))
    filter_upwards [he] with n hn
    have hpow : 0 ≤ ((n:ℝ)+1)^(-s.re) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpow]
    rw [sourceSegment, segment_eq_mul_response]
    simp only [norm_mul, norm_two_jump]
    change ((n:ℝ)+1)^(-s.re) ≤ (2/‖L‖)*_
    have h := mul_le_mul_of_nonneg_left hn.le hpow
    calc
      ((n:ℝ)+1)^(-s.re) ≤
        (2*(((n:ℝ)+1)^(-s.re)*‖segmentResponse
          (endpoint (eulerDeletionWeightedJump 1 s) n)
          (endpoint (eulerDeletionWeightedJump 2 s) n)
          (eulerDeletionWeightedJump 1 s n) (eulerDeletionWeightedJump 2 s n)‖))/‖L‖ := by
            apply (le_div_iff₀ hL).mpr
            nlinarith
      _ = _ := by ring
  have hh0 : Summable (fun n : ℕ => (n:ℝ)^(-s.re)) :=
    (summable_nat_add_iff 1).1 (by simpa only [Nat.cast_add, Nat.cast_one] using hh)
  have := Real.summable_nat_rpow.mp hh0
  linarith


/-- Removing the known pole factor gives the full endpoint value, without a zero premise. -/
theorem source_endpoint_value (q : ℕ) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    eulerDeletionDirichletSum q s =
      (1-complexEulerDilationFactor (q+1) s)*riemannZeta s := by
  have hh := poleCleared_eulerDeletionDirichletSum_eq q hs
  rw [(zetaResidueUnit_eventuallyEq hs1).eq_of_nhds] at hh
  apply mul_left_cancel₀ (sub_ne_zero.mpr hs1)
  calc
    (s-1)*eulerDeletionDirichletSum q s = _ := hh
    _ = (s-1)*((1-complexEulerDilationFactor (q+1) s)*riemannZeta s) := by ring

/-- Inside the open critical strip, the elementary deletion factor cannot vanish. -/
theorem one_sub_dilation_ne_zero {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : s.re < 1) :
    1-complexEulerDilationFactor p s ≠ 0 := by
  intro he
  have heq : complexEulerDilationFactor p s = 1 := (sub_eq_zero.mp he).symm
  have hn := congrArg norm heq
  have hpR : (1:ℝ) < p := by exact_mod_cast hp
  rw [complexEulerDilationFactor, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < p),
    Complex.neg_re, norm_one] at hn
  have hpow : (p:ℝ)*(p:ℝ)^(-s.re) = (p:ℝ)^(1-s.re) := by
    nth_rewrite 1 [← Real.rpow_one (p:ℝ)]
    rw [← Real.rpow_add (by linarith : (0:ℝ) < p), sub_eq_add_neg]
  have ht := Real.one_lt_rpow hpR (sub_pos.mpr hs)
  rw [← hpow, hn] at ht
  exact (lt_irrefl 1) ht

/-- In the open strip above one fifth, actual absolute circulation is exactly a zeta-zero test. -/
theorem sourceSegment_summable_iff_zero (s : {z : ℂ // (1:ℝ)/5 < z.re ∧ z.re < 1}) :
    Summable (fun n => ‖sourceSegment s.val n‖) ↔ riemannZeta s.val = 0 := by
  have hs : 0 < s.val.re := by linarith [s.property.1]
  have hs1 : s.val ≠ 1 := by
    intro h
    have hh := s.property.2
    rw [h, Complex.one_re] at hh
    exact lt_irrefl 1 hh
  constructor
  · intro hsum
    have hh := endpoint_product_eq_zero_of_summable hs s.property.2.le hsum
    by_contra hz
    have h1 : eulerDeletionDirichletSum 1 s.val ≠ 0 := by
      rw [source_endpoint_value 1 hs hs1]
      exact mul_ne_zero (one_sub_dilation_ne_zero (by omega) s.property.2) hz
    have h2 : eulerDeletionDirichletSum 2 s.val ≠ 0 := by
      rw [source_endpoint_value 2 hs hs1]
      exact mul_ne_zero (one_sub_dilation_ne_zero (by omega) s.property.2) hz
    exact (mul_ne_zero h1 (pow_ne_zero 3 h2)) hh
  · exact sourceSegment_summable_at_zero s.property.1 hs1

end
end RHTower.DeletionJointCirculation
