import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Extremal
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Analytic nondegeneracy from the absence of an identical affine relation

Kleinbock--Margulis nondegeneracy at a point asks that the derivatives of `F` of order `1, …, l`
span the target.  For a *real-analytic* `F` on a preconnected open set this is equivalent to a
purely global statement about the image:

> `F` is nondegenerate at some finite order at every point **iff** no nonzero covector `w` makes
> `w · F` constant on the whole set.

The nontrivial direction is proved here.  If nondegeneracy fails at every order at one point, the
unit covectors killing the first `l` derivatives form a nested sequence of nonempty compacts, so
some single `w` kills *every* positive-order derivative; analyticity then makes `w · F` locally
constant, and the identity theorem propagates that over the preconnected set.

Combined with `theoremA_simultaneous_allOrders` this turns Theorem A into a statement whose only
hypothesis is that the image of `F` is not contained in an affine hyperplane.
-/

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d n : ℕ}

/-- An analytic function all of whose positive-order derivatives vanish at a point is constant
near that point. -/
theorem eventuallyEq_const_of_iteratedFDeriv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x : E} (hg : AnalyticAt ℝ g x)
    (hd : ∀ k : ℕ, 1 ≤ k → iteratedFDeriv ℝ k g x = 0) :
    g =ᶠ[𝓝 x] fun _ => g x := by
  obtain ⟨p, r, hp⟩ := hg
  have hball : ∀ y : E, y ∈ Metric.eball (0 : E) r → g (x + y) = g x := by
    intro y hy
    have hsum := hp.hasSum hy
    have hfun : (fun k => (p k) fun _ => y) = fun k => if k = 0 then g x else 0 := by
      funext k
      by_cases hk : k = 0
      · subst hk
        simp [hp.coeff_zero]
      · have hfact := hp.factorial_smul y k
        rw [hd k (Nat.one_le_iff_ne_zero.mpr hk)] at hfact
        simp only [zero_apply] at hfact
        have hne : (k.factorial : ℝ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero k
        have hzero : ((p k) fun _ => y) = 0 := by
          have hmul : (k.factorial : ℝ) * ((p k) fun _ => y) = 0 := by
            rw [← nsmul_eq_mul]
            exact hfact
          exact (mul_eq_zero.mp hmul).resolve_left hne
        simp [hk, hzero]
    rw [hfun] at hsum
    exact hsum.unique (hasSum_ite_eq (0 : ℕ) (g x))
  filter_upwards [Metric.eball_mem_nhds x hp.r_pos] with z hz
  have hz0 : z - x ∈ Metric.eball (0 : E) r := by
    have hd : edist (z - x) (0 : E) = edist z x := by
      simp [edist_eq_enorm_sub]
    show edist (z - x) (0 : E) < r
    rw [hd]
    exact hz
  have hzx : x + (z - x) = z := by abel
  have hval := hball (z - x) hz0
  rw [hzx] at hval
  exact hval

/-- **Nondegeneracy from the absence of an identical relation.**  On a preconnected open set, an
analytic map none of whose nonzero component combinations is constant is nondegenerate at some
finite order at every point. -/
theorem exists_nondegAt_of_no_constant_combination
    {U : Set (Fin d → ℝ)} (hUc : IsPreconnected U)
    {F : (Fin d → ℝ) → (Fin n → ℝ)} (hF : AnalyticOnNhd ℝ F U)
    (hrel : ∀ w : Fin n → ℝ,
      (∀ x ∈ U, ∀ y ∈ U, ∑ i, w i * F x i = ∑ i, w i * F y i) → w = 0)
    {x : Fin d → ℝ} (hx : x ∈ U) :
    ∃ l : ℕ, 1 ≤ l ∧ NondegAt l F x := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exact ⟨1, le_rfl, fun w _ => Subsingleton.elim w 0⟩
  by_contra hcon
  have hno : ∀ l : ℕ, 1 ≤ l → ¬ NondegAt l F x := fun l hl hnd => hcon ⟨l, hl, hnd⟩
  set S : ℕ → Set (Fin n → ℝ) := fun l =>
    {w | ‖w‖ = 1 ∧ ∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ m : Fin j → (Fin d → ℝ),
      ∑ i, w i * (iteratedFDeriv ℝ j F x m) i = 0} with hS
  have hmono : ∀ l, S (l + 1) ⊆ S l := by
    intro l w hw
    exact ⟨hw.1, fun j hj1 hjl m => hw.2 j hj1 (by omega) m⟩
  have hSclosed : ∀ l, IsClosed (S l) := by
    intro l
    have hrw : S l = {w : Fin n → ℝ | ‖w‖ = 1} ∩
        ⋂ (j : ℕ) (_ : 1 ≤ j) (_ : j ≤ l) (m : Fin j → (Fin d → ℝ)),
          {w : Fin n → ℝ | ∑ i, w i * (iteratedFDeriv ℝ j F x m) i = 0} := by
      ext w
      simp only [hS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [hrw]
    refine IsClosed.inter (isClosed_eq continuous_norm continuous_const) ?_
    refine isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun m => ?_
    exact isClosed_eq (by fun_prop) continuous_const
  have hSne' : ∀ l, 1 ≤ l → (S l).Nonempty := by
    intro l hl
    have hex : ∃ w : Fin n → ℝ,
        (∀ j : ℕ, 1 ≤ j → j ≤ l → ∀ m : Fin j → (Fin d → ℝ),
          ∑ i, w i * (iteratedFDeriv ℝ j F x m) i = 0) ∧ w ≠ 0 := by
      by_contra hc
      refine hno l hl fun w hw => ?_
      by_contra hw0
      exact hc ⟨w, hw, hw0⟩
    obtain ⟨w, hw, hw0⟩ := hex
    have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm]
    · intro j hj1 hjl m
      have hz := hw j hj1 hjl m
      have hsplit : ∑ i, (‖w‖⁻¹ • w) i * (iteratedFDeriv ℝ j F x m) i
          = ‖w‖⁻¹ * ∑ i, w i * (iteratedFDeriv ℝ j F x m) i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [hsplit, hz, mul_zero]
  have hSne : ∀ l, (S l).Nonempty := by
    intro l
    rcases Nat.eq_zero_or_pos l with hl0 | hl
    · subst hl0
      obtain ⟨w, hw⟩ := hSne' 1 le_rfl
      exact ⟨w, hmono 0 hw⟩
    · exact hSne' l hl
  have hcompact : IsCompact (S 0) := by
    refine Metric.isCompact_of_isClosed_isBounded (hSclosed 0) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset ?_
    intro w hw
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq hw.1
  obtain ⟨w, hwmem⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hSne hcompact hSclosed
  rw [Set.mem_iInter] at hwmem
  have hw1 : ‖w‖ = 1 := (hwmem 0).1
  have hwker : ∀ j : ℕ, 1 ≤ j → ∀ m : Fin j → (Fin d → ℝ),
      ∑ i, w i * (iteratedFDeriv ℝ j F x m) i = 0 :=
    fun j hj m => (hwmem j).2 j hj le_rfl m
  have hcombAnalytic : AnalyticOnNhd ℝ (comb w F) U := by
    intro z hz
    rw [comb_eq]
    exact ((dotCLM w).analyticAt (F z)).comp (hF z hz)
  have hderiv : ∀ k : ℕ, 1 ≤ k → iteratedFDeriv ℝ k (comb w F) x = 0 := by
    intro k hk
    refine ContinuousMultilinearMap.ext fun m => ?_
    rw [iteratedFDeriv_comb ((hF x hx).contDiffAt (n := (k : ℕ))) w m]
    simpa using hwker k hk m
  have heq := eventuallyEq_const_of_iteratedFDeriv_eq_zero (hcombAnalytic x hx) hderiv
  have hconst : Set.EqOn (comb w F) (fun _ => comb w F x) U :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hcombAnalytic analyticOnNhd_const hUc hx heq
  have hw0 : w = 0 := by
    refine hrel w fun y hy z hz => ?_
    have h1 := hconst hy
    have h2 := hconst hz
    simp only [comb] at h1 h2
    rw [h1, h2]
  rw [hw0] at hw1
  simp at hw1

/-- **Theorem A for a real-analytic family, in itsusable form.**  If `F` is analytic on a
preconnected open set and no nonzero combination of its components is constant there, then almost
every parameter is not simultaneously very well approximable: the simultaneous Diophantine
exponent of `F x` is exactly `1/n` for almost every `x ∈ U`. -/
theorem theoremA_analytic [NeZero d] (hn : 0 < n) {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : (Fin d → ℝ) → (Fin n → ℝ)} (hF : AnalyticOnNhd ℝ F U)
    (hrel : ∀ w : Fin n → ℝ,
      (∀ x ∈ U, ∀ y ∈ U, ∑ i, w i * F x i = ∑ i, w i * F y i) → w = 0) :
    volume {x ∈ U | VWA fun i => F x i} = 0 := by
  refine theoremA_simultaneous_allOrders hn hU (fun y hy l => (hF y hy).contDiffAt) ?_
  have hempty : {x ∈ U | ∀ l : ℕ, 1 ≤ l → ¬ NondegAt l F x} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨hxU, hall⟩
    obtain ⟨l, hl, hnd⟩ := exists_nondegAt_of_no_constant_combination hUc hF hrel hxU
    exact hall l hl hnd
  rw [hempty, measure_empty]

/-- The multiplicative (dual) form of the same statement. -/
theorem theoremA_analytic_multiplicative [NeZero d] {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : (Fin d → ℝ) → (Fin n → ℝ)} (hF : AnalyticOnNhd ℝ F U)
    (hrel : ∀ w : Fin n → ℝ,
      (∀ x ∈ U, ∀ y ∈ U, ∑ i, w i * F x i = ∑ i, w i * F y i) → w = 0) :
    volume {x ∈ U | VWMA fun i => F x i} = 0 := by
  refine theoremA_allOrders hU (fun y hy l => (hF y hy).contDiffAt) ?_
  have hempty : {x ∈ U | ∀ l : ℕ, 1 ≤ l → ¬ NondegAt l F x} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨hxU, hall⟩
    obtain ⟨l, hl, hnd⟩ := exists_nondegAt_of_no_constant_combination hUc hF hrel hxU
    exact hall l hl hnd
  rw [hempty, measure_empty]

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
