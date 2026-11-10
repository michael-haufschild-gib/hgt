import GaloisForLFunctions.HyperbolicArakelovTheory.TheMinimalBranchOfTheAdelicGreenKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The prime walk has the sharp tempered spectral edge

The exact Green diagonal has a nonzero derivative where its spectral parameter
has a stationary point. Consequently critical return occupation has infinite
first moment, and occupation below the tempered edge diverges. Truncated walk
columns then supply finite nonnegative charges approaching the edge.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSpectralEdge
open FullAdelic AdelicGreen PrimeWalk MinimalGreen
variable (p : {p : ℕ // p.Prime})

private theorem prime_pos : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
private theorem prime_gt_one : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt

private theorem rpow_derivative (s : ℝ) :
    HasDerivAt (fun t : ℝ => (p.1 : ℝ) ^ t) ((p.1 : ℝ) ^ s * Real.log p.1) s := by
  simpa only [id_eq, mul_one, one_mul, mul_comm] using
    HasDerivAt.const_rpow (prime_pos p) (hasDerivAt_id s)

private theorem edge_derivative :
    HasDerivAt (treeEigen p.1) 0 (1 / 2 : ℝ) := by
  have h := (rpow_derivative p (1 / 2)).add
    ((rpow_derivative p (1 - 1 / 2)).comp (1 / 2) ((hasDerivAt_id (1 / 2 : ℝ)).const_sub 1))
  have hh : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  convert! h using 1
  simp only [hh, mul_neg_one, add_neg_cancel]

private theorem diagonal_derivative (x : LocalVertex p) :
    HasDerivAt (fun s => localGreen p s x x)
      (-(Real.sqrt p.1 * Real.log p.1 * ((p.1 : ℝ) + 1)) / ((p.1 : ℝ) - 1) ^ 2)
      (1 / 2 : ℝ) := by
  have hn : (p.1 : ℝ) - 1 ≠ 0 := (sub_pos.mpr (prime_gt_one p)).ne'
  have hh : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have hb := ((rpow_derivative p (2 * (1 / 2))).comp (1 / 2)
    ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2)).sub_const 1
  have h := (rpow_derivative p (1 / 2)).div hb
    (by simpa only [hh, Real.rpow_one, Function.comp_def] using hn)
  convert! h using 1
  · funext s
    rw [localGreen_self]
    simp only [treeGreen, pow_zero, mul_one, Pi.div_apply, Function.comp_def]
  · simp only [Function.comp_def, hh, Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring

private theorem diagonal_derivative_neg :
    -(Real.sqrt p.1 * Real.log p.1 * ((p.1 : ℝ) + 1)) / ((p.1 : ℝ) - 1) ^ 2 < 0 := by
  have hp := prime_gt_one p
  exact div_neg_of_neg_of_pos
    (neg_neg_of_pos (mul_pos (mul_pos (Real.sqrt_pos.mpr (prime_pos p)) (Real.log_pos hp)) (by positivity)))
    (sq_pos_of_ne_zero (sub_pos.mpr hp).ne')

private theorem one_sub_pow_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    1 - q ^ n ≤ (n : ℝ) * (1 - q) := by
  induction n with
  | zero => simp only [pow_zero, sub_self, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    have hpow : 0 ≤ q ^ n := pow_nonneg hq0 n
    have hpow1 : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith only [ih, mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hpow1)]

private theorem term_scale {ell mu : ℝ} (hell : ell ≠ 0) (hmu : mu ≠ 0)
    (N : ℕ) (x y : LocalVertex p) :
    weightedTerm p mu N x y = (ell / mu) ^ (N + 1) * weightedTerm p ell N x y := by
  unfold weightedTerm walkWeight
  rw [pow_succ, div_pow, div_pow, div_pow]
  field_simp

private theorem eigen_pos (s : ℝ) : 0 < treeEigen p.1 s :=
  add_pos (Real.rpow_pos_of_pos (prime_pos p) s)
    (Real.rpow_pos_of_pos (prime_pos p) (1 - s))

private theorem eigen_edge_le (s : ℝ) :
    treeEigen p.1 (1 / 2) ≤ treeEigen p.1 s := by
  rw [(treeEigen_eq_iff (prime_gt_one p) (1 / 2)).mpr rfl]
  exact two_sqrt_le_treeEigen (prime_pos p) s

/-- At the tempered endpoint, total occupation is finite but its time-weighted return mass
is infinite. The branch-point derivative forces this without a shell-counting assumption. -/
theorem not_summable_critical_return_moment (x : LocalVertex p) :
    ¬ Summable (fun N : ℕ => ((N : ℝ) + 1) *
      weightedTerm p (treeEigen p.1 (1 / 2)) N x x) := by
  intro hm
  let e := treeEigen p.1 (1 / 2)
  let M := ∑' N : ℕ, ((N : ℝ) + 1) * weightedTerm p e N x x
  have hbound (s : ℝ) (hs : 1 / 2 < s) :
      localGreen p (1 / 2) x x - localGreen p s x x ≤
        (1 - e / treeEigen p.1 s) * M := by
    have he0 : 0 < e := eigen_pos p _
    have hq0 : 0 ≤ e / treeEigen p.1 s := (div_pos he0 (eigen_pos p s)).le
    have hq1 : e / treeEigen p.1 s ≤ 1 :=
      (div_le_one (eigen_pos p s)).mpr (eigen_edge_le p s)
    have hc := hasSum_critical p x x
    have hs' := hasSum_kernel p hs.le x x
    have h := Summable.tsum_le_tsum (fun N => ?_)
      (hc.summable.sub hs'.summable) (hm.mul_left (1 - e / treeEigen p.1 s))
    · simpa only [hc.tsum_eq, hs'.tsum_eq, Summable.tsum_sub hc.summable hs'.summable,
        tsum_mul_left, M] using h
    · rw [term_scale p he0.ne' (eigen_pos p s).ne']
      have hterm := mul_le_mul_of_nonneg_right (one_sub_pow_bound hq0 hq1 (N + 1))
        (weightedTerm_nonneg p he0 N x x)
      simp only [Nat.cast_add, Nat.cast_one] at hterm
      nlinarith only [hterm]
  let d : ℝ := -(Real.sqrt p.1 * Real.log p.1 * ((p.1 : ℝ) + 1)) /
    ((p.1 : ℝ) - 1) ^ 2
  let D : ℝ → ℝ := fun s => (1 - e / treeEigen p.1 s) * M -
    (localGreen p (1 / 2) x x - localGreen p s x x)
  have hd : HasDerivAt D d (1 / 2 : ℝ) := by
    have hr := ((hasDerivAt_const (1 / 2 : ℝ) e).div (edge_derivative p)
      (eigen_pos p (1 / 2)).ne').const_sub 1
    have hg := (diagonal_derivative p x).const_sub (localGreen p (1 / 2) x x)
    convert! (hr.mul_const M).sub hg using 1
    simp only [zero_mul, mul_zero, sub_zero, zero_div, neg_zero, zero_sub, neg_neg, d]
  have hD0 : D (1 / 2) = 0 := by
    dsimp only [D, e]
    rw [div_self (eigen_pos p (1 / 2)).ne', sub_self, zero_mul, sub_self, sub_self]
  have hlim := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  have hnonneg : 0 ≤ d := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field, hD0, sub_zero]
    exact div_nonneg (sub_nonneg.mpr (hbound s hs)) (sub_pos.mpr hs).le
  exact (not_le_of_gt (diagonal_derivative_neg p)) hnonneg

private theorem geometric_time_summable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * q ^ (n + 1)) := by
  have hq : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have h := ((summable_pow_mul_geometric_of_norm_lt_one 1 hq).add
    (summable_geometric_of_norm_lt_one hq)).mul_right q
  simpa only [pow_one, pow_succ, pow_zero, add_mul, one_mul, mul_assoc] using h

/-- Return occupation converges exactly at and above the tempered spectral edge. -/
theorem summable_return_iff {ell : ℝ} (hell : 0 < ell) (x : LocalVertex p) :
    Summable (fun n => weightedTerm p ell n x x) ↔ treeEigen p.1 (1 / 2) ≤ ell := by
  constructor
  · intro h
    by_contra he
    have he' : ell < treeEigen p.1 (1 / 2) := lt_of_not_ge he
    let q := ell / treeEigen p.1 (1 / 2)
    have hq0 : 0 ≤ q := (div_pos hell (eigen_pos p _)).le
    have hq1 : q < 1 := (div_lt_one (eigen_pos p _)).mpr he'
    have hg := geometric_time_summable hq0 hq1
    let M := ∑' n : ℕ, ((n : ℝ) + 1) * q ^ (n + 1)
    have hb (n : ℕ) : ((n : ℝ) + 1) * q ^ (n + 1) ≤ M :=
      hg.le_tsum n (fun k _ => mul_nonneg (by positivity) (pow_nonneg hq0 _))
    apply not_summable_critical_return_moment p x
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (by positivity) (weightedTerm_nonneg p (eigen_pos p _) n x x))
      (fun n => ?_) (h.mul_left M)
    rw [term_scale p hell.ne' (eigen_pos p _).ne']
    simpa only [q, mul_assoc] using
      mul_le_mul_of_nonneg_right (hb n) (weightedTerm_nonneg p hell n x x)
  · intro he
    apply Summable.of_nonneg_of_le (fun n => weightedTerm_nonneg p hell n x x)
      (fun n => ?_) (hasSum_critical p x x).summable
    rw [term_scale p (eigen_pos p _).ne' hell.ne']
    exact mul_le_of_le_one_left (weightedTerm_nonneg p (eigen_pos p _) n x x)
      (pow_le_one₀ (div_nonneg (eigen_pos p _).le hell.le) ((div_le_one hell).mpr he))

/-- Below the tempered edge no nonnegative point-source supersolution exists. -/
theorem supersolutions_empty_below_edge {ell : ℝ} (hell : 0 < ell)
    (he : ell < treeEigen p.1 (1 / 2)) (x : LocalVertex p) :
    supersolutions p ell x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hs : Summable (fun n => weightedTerm p ell n x x) := by
    apply summable_of_sum_range_le (fun n => weightedTerm_nonneg p hell n x x)
    intro N
    exact weightedPartial_le p hell x hu N x
  exact (not_le_of_gt he) ((summable_return_iff p hell x).mp hs)

open AdelicAdjacency
open scoped Classical

private def walkSupport (x : LocalVertex p) : ℕ → Finset (LocalVertex p)
  | 0 => {x}
  | n + 1 => (walkSupport x n).biUnion (neighbors p)

private theorem walkMass_zero_off_support (x y : LocalVertex p) (n : ℕ)
    (hy : y ∉ walkSupport p x n) : walkMass p n x y = 0 := by
  induction n generalizing y with
  | zero =>
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hy (Finset.mem_singleton_self x)
    simp only [walkMass, pow_zero, Module.End.one_apply, pointMass, if_neg hxy]
  | succ n ih =>
    rw [walkMass, pow_succ', Module.End.mul_apply]
    change (∑ w ∈ neighbors p y, walkMass p n x w) / ((p.1 : ℝ) + 1) = 0
    rw [Finset.sum_eq_zero, zero_div]
    intro w hw
    apply ih w
    intro hws
    apply hy
    exact Finset.mem_biUnion.mpr ⟨w, hws,
      (mem_neighbors p w y).mpr (adjacent_symm p y w ((mem_neighbors p y w).mp hw))⟩

private def partialSupport (x : LocalVertex p) (N : ℕ) : Finset (LocalVertex p) :=
  (Finset.range N).biUnion (walkSupport p x)

private theorem weightedPartial_zero_off_support (ell : ℝ) (x y : LocalVertex p) (N : ℕ)
    (hy : y ∉ partialSupport p x N) : weightedPartial p ell x N y = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hyk : y ∉ walkSupport p x k := fun h => hy (Finset.mem_biUnion.mpr ⟨k, hk, h⟩)
  simp only [weightedTerm, walkMass_zero_off_support p x y k hyk, mul_zero, zero_div]

private def partialCharge (ell : ℝ) (x : LocalVertex p) (N : ℕ) : LocalVertex p →₀ ℝ :=
  Finsupp.onFinset (partialSupport p x N) (weightedPartial p ell x N)
    (fun y hy => Classical.byContradiction fun h =>
      hy (weightedPartial_zero_off_support p ell x y N h))

private theorem partialCharge_apply (ell : ℝ) (x y : LocalVertex p) (N : ℕ) :
    partialCharge p ell x N y = weightedPartial p ell x N y := rfl

private theorem weightedTerm_succ {ell : ℝ} (hell : 0 < ell)
    (x y : LocalVertex p) (n : ℕ) :
    ell * weightedTerm p ell (n + 1) x y =
      ∑ w ∈ neighbors p y, weightedTerm p ell n x w := by
  simp only [weightedTerm, walkMass, pow_succ', Module.End.mul_apply]
  change ell * ((walkWeight p ell * walkWeight p ell ^ n) *
    ((∑ w ∈ neighbors p y, ((walkStep p) ^ n) (pointMass p x) w) /
      ((p.1 : ℝ) + 1)) / ell) = _
  rw [← Finset.sum_div, ← Finset.mul_sum]
  unfold walkWeight
  have hd : (p.1 : ℝ) + 1 ≠ 0 := (by positivity : (0 : ℝ) < p.1 + 1).ne'
  field_simp

private theorem weightedPartial_source_le {ell : ℝ} (hell : 0 < ell)
    (x y : LocalVertex p) (N : ℕ) :
    ell * weightedPartial p ell x N y -
      (∑ w ∈ neighbors p y, weightedPartial p ell x N w) ≤ pointMass p x y := by
  have hid : ell * weightedPartial p ell x N y -
      (∑ w ∈ neighbors p y, weightedPartial p ell x N w) =
        pointMass p x y - ell * weightedTerm p ell N x y := by
    unfold weightedPartial
    rw [Finset.mul_sum, Finset.sum_comm, ← Finset.sum_sub_distrib]
    simp_rw [← weightedTerm_succ p hell x y]
    rw [Finset.sum_range_sub']
    simp only [weightedTerm, walkMass, pow_zero, one_mul, Module.End.one_apply,
      mul_div_cancel₀ _ hell.ne']
  rw [hid]
  exact sub_le_self _ (mul_nonneg hell.le (weightedTerm_nonneg p hell N x y))

/-- Finite nonnegative charges approach the local tempered edge from below. -/
theorem exists_finite_charge_above (c : ℝ) (hc : c < treeEigen p.1 (1 / 2)) :
    ∃ f : LocalVertex p →₀ ℝ, (∀ y, 0 ≤ f y) ∧
      c * (∑ y ∈ f.support, f y ^ 2) <
        ∑ y ∈ f.support, f y * (∑ w ∈ neighbors p y, f w) := by
  by_contra h
  push Not at h
  obtain ⟨ell, hcl, hle⟩ := exists_between (max_lt hc (eigen_pos p (1 / 2)))
  have hell : 0 < ell := (le_max_right c 0).trans_lt hcl
  have hce : c < ell := (le_max_left c 0).trans_lt hcl
  have hdelta : 0 < ell - c := sub_pos.mpr hce
  let x := baseVertex p
  have hbounded (N : ℕ) : weightedPartial p ell x N x ≤ 1 / (ell - c) := by
    let f := partialCharge p ell x N
    have hf (y : LocalVertex p) : 0 ≤ f y := by
      change 0 ≤ ∑ n ∈ Finset.range N, weightedTerm p ell n x y
      exact Finset.sum_nonneg fun n _ => weightedTerm_nonneg p hell n x y
    have hform := h f hf
    have hsource := Finset.sum_le_sum (s := f.support) (fun y _ =>
      mul_le_mul_of_nonneg_left (weightedPartial_source_le p hell x y N) (hf y))
    change (∑ y ∈ f.support, f y * (ell * f y - ∑ w ∈ neighbors p y, f w)) ≤
      ∑ y ∈ f.support, f y * pointMass p x y at hsource
    have hdiag : (∑ y ∈ f.support, f y * pointMass p x y) = f x := by
      simp only [pointMass, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
      split_ifs with hx
      · rfl
      · exact (Finsupp.notMem_support_iff.mp hx).symm
    have hsq : f x ^ 2 ≤ ∑ y ∈ f.support, f y ^ 2 := by
      by_cases hx : x ∈ f.support
      · exact Finset.single_le_sum (fun y _ => sq_nonneg (f y)) hx
      · rw [Finsupp.notMem_support_iff.mp hx, zero_pow (by decide : 2 ≠ 0)]
        exact Finset.sum_nonneg fun y _ => sq_nonneg (f y)
    have hid : (∑ y ∈ f.support, f y * (ell * f y - ∑ w ∈ neighbors p y, f w)) =
        ell * (∑ y ∈ f.support, f y ^ 2) -
          ∑ y ∈ f.support, f y * (∑ w ∈ neighbors p y, f w) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [hid, hdiag] at hsource
    have hquad : (ell - c) * (f x) ^ 2 ≤ f x := by
      have hh := mul_le_mul_of_nonneg_left hsq hdelta.le
      nlinarith only [hh, hsource, hform]
    have hxbound : f x ≤ 1 / (ell - c) := by
      apply (le_div_iff₀ hdelta).mpr
      by_cases hx : f x = 0
      · rw [hx, zero_mul]
        exact zero_le_one
      · have hxpos : 0 < f x := lt_of_le_of_ne (hf x) (Ne.symm hx)
        nlinarith only [hquad, hxpos]
    exact hxbound
  have hs : Summable (fun n => weightedTerm p ell n x x) :=
    summable_of_sum_range_le (fun n => weightedTerm_nonneg p hell n x x) hbounded
  exact (not_le_of_gt hle) ((summable_return_iff p hell x).mp hs)

#print axioms not_summable_critical_return_moment
#print axioms summable_return_iff
#print axioms supersolutions_empty_below_edge
#print axioms exists_finite_charge_above

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSpectralEdge
