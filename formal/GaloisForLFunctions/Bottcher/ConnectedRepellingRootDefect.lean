/-
# Connected repelling event route with bounded fixed-root deficit

The no-multiplier-one route recovers separability of `fixedPointPoly c p`, hence the exact distinct
root count `2^p`.  That is too narrow near parabolic parameters.  This file replaces separability by
a bounded distinct-root deficit: it is enough that the number of distinct fixed roots is at least
`2^p - D` eventually, because every other contribution to the squarefree budget is bounded while
`2^p` grows.
-/
import GaloisForLFunctions.Bottcher.DenominatorContent
import GaloisForLFunctions.Bottcher.LocalParabolicMultiplicity

open Polynomial Finset Filter Topology

namespace Bottcher

/-- The analytic order of a nonzero polynomial evaluation germ equals the algebraic root
multiplicity. -/
theorem analyticOrderAt_polynomial_eval_eq_rootMultiplicity {P : Polynomial ℂ} (hP : P ≠ 0)
    (z : ℂ) :
    analyticOrderAt (fun y : ℂ => P.eval y) z = (P.rootMultiplicity z : ℕ∞) := by
  let n := P.rootMultiplicity z
  have hPan : AnalyticAt ℂ (fun y : ℂ => P.eval y) z := by
    simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) z).aeval_polynomial P
  rw [hPan.analyticOrderAt_eq_natCast]
  obtain ⟨s, hps, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP z
  have hs_ne : s.eval z ≠ 0 := by
    intro hs
    exact hnd ((Polynomial.dvd_iff_isRoot).mpr hs)
  refine ⟨fun y : ℂ => s.eval y, ?_, hs_ne, Filter.Eventually.of_forall ?_⟩
  · simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) z).aeval_polynomial s
  · intro y
    have h := congrArg (fun Q : Polynomial ℂ => Q.eval y) hps
    simpa [n, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, smul_eq_mul] using h

/-- For nonzero fixed-point polynomials, analytic order at `z` is the root count at `z`. -/
theorem analyticOrderAt_fixedPointPoly_eval_eq_roots_count
    (c : ℂ) {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z =
      (((fixedPointPoly c p).roots.count z : ℕ) : ℕ∞) := by
  rw [analyticOrderAt_polynomial_eval_eq_rootMultiplicity (fixedPointPoly_ne_zero c hp)]
  simp [Polynomial.count_roots]

/-- An eventual analytic-order bound for the fixed-point-polynomial germ gives the pointwise
duplicate-excess bound consumed by the active hRigid endpoint. -/
theorem eventually_duplicateBound_of_eventually_analyticOrderAt_fixedPointPoly_eval_le
    (c z : ℂ) (L : ℕ)
    (hord : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z ≤ ((L + 1 : ℕ) : ℕ∞)) :
    ∀ᶠ p : ℕ in atTop,
      ∀ _hzroot : z ∈ (fixedPointPoly c p).roots.toFinset,
        (fixedPointPoly c p).roots.count z - 1 ≤ L :=
  hord.mono fun p hp _hzroot => by
    have hle := hp.2
    rw [analyticOrderAt_fixedPointPoly_eval_eq_roots_count c hp.1 z] at hle
    have hcount : (fixedPointPoly c p).roots.count z ≤ L + 1 := by
      exact_mod_cast hle
    omega

/-- Period-`p` fixed roots whose period-`p` multiplier is exactly `1`. -/
noncomputable def multiplierOneFixedPointRoots (c : ℂ) (p : ℕ) : Finset ℂ := by
  classical
  exact (fixedPointPoly c p).roots.toFinset.filter fun z =>
    (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (1 : ℂ)

theorem mem_multiplierOneFixedPointRoots {c z : ℂ} {p : ℕ} :
    z ∈ multiplierOneFixedPointRoots c p ↔
      z ∈ (fixedPointPoly c p).roots.toFinset ∧
        (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (1 : ℂ) := by
  classical
  simp [multiplierOneFixedPointRoots]

/-- If `z` is fixed by `f_c^[p]` but its period-`p` multiplier is not `1`, then the
fixed-point-polynomial germ has simple order at `z`. -/
theorem analyticOrderAt_fixedPointPoly_eval_eq_one_of_fixed_multiplier_ne_one
    (c z : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hfix : (quadratic c)^[p] z = z)
    (hmul_ne : (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) ≠ (1 : ℂ)) :
    analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z = (1 : ℕ∞) := by
  have hP0 : fixedPointPoly c p ≠ 0 := fixedPointPoly_ne_zero c hp
  have hzrootPoly : (fixedPointPoly c p).IsRoot z :=
    (fixedPointPoly_isRoot_iff c p z).mpr hfix
  have hzroot : z ∈ (fixedPointPoly c p).roots.toFinset := by
    exact Multiset.mem_toFinset.mpr ((mem_roots hP0).mpr hzrootPoly)
  have hcount_pos : 0 < (fixedPointPoly c p).roots.count z :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzroot)
  have hder_ne : (derivative (fixedPointPoly c p)).eval z ≠ 0 := by
    rw [eval_deriv_fixedPointPoly]
    exact sub_ne_zero.mpr hmul_ne
  have hcount_not : ¬ 1 < (fixedPointPoly c p).roots.count z := by
    intro hlt
    have hmult : 1 < (fixedPointPoly c p).rootMultiplicity z := by
      simpa [Polynomial.count_roots] using hlt
    have hboth := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hP0).mp hmult
    exact hder_ne hboth.2
  have hcount_eq : (fixedPointPoly c p).roots.count z = 1 := by omega
  rw [analyticOrderAt_fixedPointPoly_eval_eq_roots_count c hp z, hcount_eq]
  norm_num

/-- A separable fixed-point polynomial has no multiplier-one fixed roots. -/
theorem multiplierOneFixedPointRoots_eq_empty_of_fixedPointPoly_separable
    (c : ℂ) {p : ℕ} (hp : 1 ≤ p) (hsep : (fixedPointPoly c p).Separable) :
    multiplierOneFixedPointRoots c p = ∅ := by
  classical
  ext z
  constructor
  · intro hz
    have hz' := (mem_multiplierOneFixedPointRoots).mp hz
    have hzroot : (fixedPointPoly c p).IsRoot z :=
      (mem_roots (fixedPointPoly_ne_zero c hp)).mp (Multiset.mem_toFinset.mp hz'.1)
    have hderiv_ne := eval_derivative_ne_zero_of_separable hsep hzroot
    rw [eval_deriv_fixedPointPoly, hz'.2, sub_self] at hderiv_ne
    exact (hderiv_ne rfl).elim
  · intro hz
    simp at hz

/-- Eventual fixed-point separability supplies the multiplier-one support payload with empty support
and zero duplicate-excess budget. -/
theorem eventually_multiplierOne_empty_duplicateBound_of_eventually_fixedPointPoly_separable
    (c : ℂ)
    (hsep : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable) :
    ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ ∅ ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ (∅ : Finset ℂ) →
        (fixedPointPoly c p).roots.count z - 1 ≤ 0) :=
  hsep.mono fun _ hp =>
    ⟨hp.1,
      by
        intro z hz
        rw [multiplierOneFixedPointRoots_eq_empty_of_fixedPointPoly_separable c hp.1 hp.2] at hz
        simp at hz,
      by
        intro _ _ hzempty
        simp at hzempty⟩

/-- Pointwise eventual duplicate-excess bounds on a finite support combine into one uniform eventual
duplicate-excess bound on that support. -/
theorem exists_eventually_duplicateBound_on_finset_of_pointwise
    (c : ℂ) (F : Finset ℂ)
    (hbound : ∀ z ∈ F, ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      ∀ _hzroot : z ∈ (fixedPointPoly c p).roots.toFinset,
        (fixedPointPoly c p).roots.count z - 1 ≤ L) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L := by
  classical
  induction F using Finset.induction with
  | empty =>
      refine ⟨0, Filter.Eventually.of_forall ?_⟩
      intro _ z _ hzF
      simp at hzF
  | insert a F ha ih =>
      obtain ⟨La, haev⟩ := hbound a (by simp)
      have hboundF : ∀ z ∈ F, ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
          ∀ _hzroot : z ∈ (fixedPointPoly c p).roots.toFinset,
            (fixedPointPoly c p).roots.count z - 1 ≤ L := by
        intro z hzF
        exact hbound z (Finset.mem_insert_of_mem hzF)
      obtain ⟨LF, hFev⟩ := ih hboundF
      refine ⟨max La LF, (haev.and hFev).mono ?_⟩
      intro p hp z hzroot hzF
      rcases (Finset.mem_insert.mp hzF) with rfl | hzF'
      · exact le_trans (hp.1 hzroot) (Nat.le_max_left La LF)
      · exact le_trans (hp.2 z hzroot hzF') (Nat.le_max_right La LF)

/-- Eventual finite support for multiplier-one roots plus pointwise finite duplicate-excess bounds
on that support supplies the active multiplier-one payload. -/
theorem eventually_multiplierOne_payload_of_eventually_support_and_pointwise_duplicateBounds
    (c : ℂ) (F : Finset ℂ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F)
    (hbound : ∀ z ∈ F, ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      ∀ _hzroot : z ∈ (fixedPointPoly c p).roots.toFinset,
        (fixedPointPoly c p).roots.count z - 1 ≤ L) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L) := by
  obtain ⟨L, hL⟩ := exists_eventually_duplicateBound_on_finset_of_pointwise c F hbound
  exact ⟨L, (hmultiplierOne.and hL).mono fun _ hp => ⟨hp.1.1, hp.1.2, hp.2⟩⟩

/-- Eventual finite support for multiplier-one roots plus pointwise analytic-order bounds on that
support supplies the active multiplier-one payload.  This is the parabolic local-multiplicity bridge:
callers can prove bounded analytic order of the fixed-point-polynomial germ, and Lean converts that
bound to duplicate-root excess. -/
theorem eventually_multiplierOne_payload_of_eventually_support_and_pointwise_analyticOrderBounds
    (c : ℂ) (F : Finset ℂ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F)
    (hbound : ∀ z ∈ F, ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
        analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z ≤
          ((L + 1 : ℕ) : ℕ∞)) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L) := by
  apply eventually_multiplierOne_payload_of_eventually_support_and_pointwise_duplicateBounds
    c F hmultiplierOne
  intro z hzF
  obtain ⟨L, hL⟩ := hbound z hzF
  exact ⟨L, eventually_duplicateBound_of_eventually_analyticOrderAt_fixedPointPoly_eval_le c z L hL⟩

/-- Finite multiplier-one support plus exact-period tangent-to-identity local data supplies the
active multiplier-one payload.  This is the direct bridge from local parabolic normal form to the
root-defect machinery: the local theorem bounds analytic order at each support point, then the
existing payload takes the finite maximum and converts analytic order to duplicate-root excess. -/
theorem eventually_multiplierOne_payload_of_eventually_support_and_exactPeriod_tangentToId
    (c : ℂ) (F : Finset ℂ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F)
    (hdata : ∀ z ∈ F, ∃ (q r : ℕ) (u : ℂ → ℂ),
      (∀ p : ℕ, (quadratic c)^[p] z = z → q ∣ p) ∧
      2 ≤ r ∧
      AnalyticAt ℂ u z ∧
      u z ≠ 0 ∧
      (fun y : ℂ => (quadratic c)^[q] y - y) =ᶠ[𝓝 z]
        fun y => (y - z) ^ r * u y) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L) := by
  apply eventually_multiplierOne_payload_of_eventually_support_and_pointwise_analyticOrderBounds
    c F hmultiplierOne
  intro z hzF
  obtain ⟨q, r, u, hexact, hr, hu, hu_ne, hfac⟩ := hdata z hzF
  exact ⟨r, eventually_analyticOrderAt_fixedPointPoly_eval_le_of_exact_period_tangentToId
    (c := c) (z := z) (q := q) (r := r) (u := u) hexact hr hu hu_ne hfac⟩

/-- Finite multiplier-one support plus exact-period return-order data supplies the active
multiplier-one payload.  This is the current sharp local-data bridge: for each support point, callers
only need exact-period divisibility and the finite analytic order of the first-return displacement. -/
theorem eventually_multiplierOne_payload_of_eventually_support_and_exactPeriod_returnOrder
    (c : ℂ) (F : Finset ℂ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F)
    (hdata : ∀ z ∈ F, ∃ (q r : ℕ),
      (∀ p : ℕ, (quadratic c)^[p] z = z → q ∣ p) ∧
      2 ≤ r ∧
      analyticOrderAt (fun y : ℂ => (quadratic c)^[q] y - y) z = (r : ℕ∞)) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L) := by
  apply eventually_multiplierOne_payload_of_eventually_support_and_pointwise_analyticOrderBounds
    c F hmultiplierOne
  intro z hzF
  obtain ⟨q, r, hexact, hr, horder⟩ := hdata z hzF
  exact ⟨r, eventually_analyticOrderAt_fixedPointPoly_eval_le_of_exact_period_returnOrder
    (c := c) (z := z) (q := q) (r := r) hexact hr horder⟩

/-- Multiplier-one-period exactness is enough for the local analytic-order bound.  If `q` divides
every multiplier-one return time of `z`, then periods not divisible by `q` either do not fix `z`, or
fix it with multiplier different from `1` and hence contribute only a simple root. -/
theorem eventually_analyticOrderAt_fixedPointPoly_eval_le_of_multiplierOne_period_returnOrder
    (c z : ℂ) {q r : ℕ}
    (hmultExact : ∀ p : ℕ, z ∈ multiplierOneFixedPointRoots c p → q ∣ p)
    (hr : 2 ≤ r)
    (horder : analyticOrderAt (fun y : ℂ => (quadratic c)^[q] y - y) z = (r : ℕ∞)) :
    ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
        analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z ≤
          ((r + 1 : ℕ) : ℕ∞) := by
  filter_upwards [eventually_ge_atTop 1] with p hp
  refine ⟨hp, ?_⟩
  by_cases hzmult : z ∈ multiplierOneFixedPointRoots c p
  · obtain ⟨n, hn⟩ := hmultExact p hzmult
    subst p
    have hnpos : 1 ≤ n := by
      by_contra hn0
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos (by simpa using hn0)
      subst n
      simp at hp
    exact analyticOrderAt_fixedPointPoly_eval_mul_le_of_returnOrder
      (c := c) (z := z) (q := q) (r := r) (n := n) hr horder hnpos
  · by_cases hfix : (quadratic c)^[p] z = z
    · have hP0 : fixedPointPoly c p ≠ 0 := fixedPointPoly_ne_zero c hp
      have hzroot : z ∈ (fixedPointPoly c p).roots.toFinset := by
        exact Multiset.mem_toFinset.mpr
          ((mem_roots hP0).mpr ((fixedPointPoly_isRoot_iff c p z).mpr hfix))
      have hmul_ne : (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) ≠ (1 : ℂ) := by
        intro hmul
        exact hzmult ((mem_multiplierOneFixedPointRoots).mpr ⟨hzroot, hmul⟩)
      have hone :=
        analyticOrderAt_fixedPointPoly_eval_eq_one_of_fixed_multiplier_ne_one
          c z hp hfix hmul_ne
      rw [hone]
      exact_mod_cast (by omega : (1 : ℕ) ≤ r + 1)
    · have han : AnalyticAt ℂ (fun y : ℂ => (fixedPointPoly c p).eval y) z := by
        simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) z).aeval_polynomial
          (fixedPointPoly c p)
      have hne : (fixedPointPoly c p).eval z ≠ 0 := by
        rw [fixedPointPoly_eval]
        exact sub_ne_zero.mpr hfix
      have hzero : analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z = 0 :=
        han.analyticOrderAt_eq_zero.mpr hne
      rw [hzero]
      simp

/-- Finite multiplier-one support plus multiplier-one-period return-order data supplies the active
multiplier-one payload.  This handles rationally indifferent/parabolic cycles whose first
multiplier-one return may be a multiple of the minimal fixed period. -/
theorem eventually_multiplierOne_payload_of_eventually_support_and_multiplierOnePeriod_returnOrder
    (c : ℂ) (F : Finset ℂ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F)
    (hdata : ∀ z ∈ F, ∃ (q r : ℕ),
      (∀ p : ℕ, z ∈ multiplierOneFixedPointRoots c p → q ∣ p) ∧
      2 ≤ r ∧
      analyticOrderAt (fun y : ℂ => (quadratic c)^[q] y - y) z = (r : ℕ∞)) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L) := by
  apply eventually_multiplierOne_payload_of_eventually_support_and_pointwise_analyticOrderBounds
    c F hmultiplierOne
  intro z hzF
  obtain ⟨q, r, hmultExact, hr, horder⟩ := hdata z hzF
  exact ⟨r, eventually_analyticOrderAt_fixedPointPoly_eval_le_of_multiplierOne_period_returnOrder
    (c := c) (z := z) (q := q) (r := r) hmultExact hr horder⟩

/-- A multiplier-one exact return has return displacement order at least two.  Algebraically, the
point is a root of `fixedPointPoly c q` and multiplier one makes the derivative vanish there, so the
root multiplicity, equivalently the analytic order of `f^[q] y - y`, is at least two. -/
theorem exists_returnOrder_two_le_of_multiplierOne_return
    (c z : ℂ) {q : ℕ} (hq : 1 ≤ q)
    (hfix : (quadratic c)^[q] z = z)
    (hmul : (∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z) = (1 : ℂ)) :
    ∃ r : ℕ,
      2 ≤ r ∧
        analyticOrderAt (fun y : ℂ => (quadratic c)^[q] y - y) z = (r : ℕ∞) := by
  have hroot : (fixedPointPoly c q).IsRoot z :=
    (fixedPointPoly_isRoot_iff c q z).mpr hfix
  have hderroot : (derivative (fixedPointPoly c q)).IsRoot z := by
    rw [Polynomial.IsRoot.def, eval_deriv_fixedPointPoly, hmul, sub_self]
  have hmult : 1 < (fixedPointPoly c q).rootMultiplicity z :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot (fixedPointPoly_ne_zero c hq)).mpr
      ⟨hroot, hderroot⟩
  let r := (fixedPointPoly c q).roots.count z
  have hr : 2 ≤ r := by
    have hcount : 1 < (fixedPointPoly c q).roots.count z := by
      simpa [Polynomial.count_roots] using hmult
    omega
  have hcongr : (fun y : ℂ => (quadratic c)^[q] y - y) =ᶠ[𝓝 z]
      fun y : ℂ => (fixedPointPoly c q).eval y := by
    exact Filter.Eventually.of_forall fun y => by simp [fixedPointPoly_eval]
  have horder : analyticOrderAt (fun y : ℂ => (quadratic c)^[q] y - y) z = (r : ℕ∞) := by
    rw [analyticOrderAt_congr hcongr]
    exact analyticOrderAt_fixedPointPoly_eval_eq_roots_count c hq z
  exact ⟨r, hr, horder⟩

/-- Finite multiplier-one support plus exact-period multiplier-one return data supplies the active
multiplier-one payload.  This removes explicit local order data from the caller: derivative
degeneracy creates the return order, and the exact-period bridge controls all periods. -/
theorem eventually_multiplierOne_payload_of_eventually_support_and_exactPeriod_multiplierOneReturn
    (c : ℂ) (F : Finset ℂ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F)
    (hdata : ∀ z ∈ F, ∃ q : ℕ,
      1 ≤ q ∧
      (∀ p : ℕ, (quadratic c)^[p] z = z → q ∣ p) ∧
      (quadratic c)^[q] z = z ∧
      (∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z) = (1 : ℂ)) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L) := by
  apply eventually_multiplierOne_payload_of_eventually_support_and_exactPeriod_returnOrder
    c F hmultiplierOne
  intro z hzF
  obtain ⟨q, hq, hexact, hfix, hmul⟩ := hdata z hzF
  obtain ⟨r, hr, horder⟩ := exists_returnOrder_two_le_of_multiplierOne_return
    c z hq hfix hmul
  exact ⟨q, r, hexact, hr, horder⟩

/-- Membership in `multiplierOneFixedPointRoots c q` supplies return displacement order at least
two.  This packages the root and multiplier equations hidden in the finite support predicate. -/
theorem exists_returnOrder_two_le_of_mem_multiplierOneFixedPointRoots
    (c : ℂ) {z : ℂ} {q : ℕ} (hq : 1 ≤ q)
    (hz : z ∈ multiplierOneFixedPointRoots c q) :
    ∃ r : ℕ,
      2 ≤ r ∧
        analyticOrderAt (fun y : ℂ => (quadratic c)^[q] y - y) z = (r : ℕ∞) := by
  have hz' := (mem_multiplierOneFixedPointRoots).mp hz
  have hfix : (quadratic c)^[q] z = z := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hq)).mp (Multiset.mem_toFinset.mp hz'.1)
  exact exists_returnOrder_two_le_of_multiplierOne_return c z hq hfix hz'.2

/-- Finite multiplier-one support plus exact-period membership in `multiplierOneFixedPointRoots`
supplies the active multiplier-one payload.  This is the lowest local-data bridge currently proved:
for each support point, callers give an exact period `q` and membership in the period-`q`
multiplier-one locus. -/
theorem eventually_multiplierOne_payload_of_eventually_support_and_exactPeriod_memMultiplierOne
    (c : ℂ) (F : Finset ℂ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F)
    (hdata : ∀ z ∈ F, ∃ q : ℕ,
      1 ≤ q ∧
      z ∈ multiplierOneFixedPointRoots c q ∧
      (∀ p : ℕ, (quadratic c)^[p] z = z → q ∣ p)) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L) := by
  apply eventually_multiplierOne_payload_of_eventually_support_and_exactPeriod_returnOrder
    c F hmultiplierOne
  intro z hzF
  obtain ⟨q, hq, hzmult, hexact⟩ := hdata z hzF
  obtain ⟨r, hr, horder⟩ := exists_returnOrder_two_le_of_mem_multiplierOneFixedPointRoots
    c hq hzmult
  exact ⟨q, r, hexact, hr, horder⟩

/-- Finite multiplier-one support plus multiplier-one-period membership supplies the active
multiplier-one payload.  This is the root-of-unity-safe support bridge: exactness is required only
among multiplier-one returns, not among all returns fixing the point. -/
theorem eventually_multiplierOne_payload_of_eventually_support_and_multiplierOnePeriod_memMultiplierOne
    (c : ℂ) (F : Finset ℂ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F)
    (hdata : ∀ z ∈ F, ∃ q : ℕ,
      1 ≤ q ∧
      z ∈ multiplierOneFixedPointRoots c q ∧
      (∀ p : ℕ, z ∈ multiplierOneFixedPointRoots c p → q ∣ p)) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L) := by
  apply eventually_multiplierOne_payload_of_eventually_support_and_multiplierOnePeriod_returnOrder
    c F hmultiplierOne
  intro z hzF
  obtain ⟨q, hq, hzmult, hmultExact⟩ := hdata z hzF
  obtain ⟨r, hr, horder⟩ := exists_returnOrder_two_le_of_mem_multiplierOneFixedPointRoots
    c hq hzmult
  exact ⟨q, r, hmultExact, hr, horder⟩

/-- Finite multiplier-one support plus minimal-period membership in
`multiplierOneFixedPointRoots` supplies the active multiplier-one payload.  The divisibility of all
return periods is derived internally from mathlib's `minimalPeriod` theorem. -/
theorem eventually_multiplierOne_payload_of_eventually_support_and_minimalPeriod_memMultiplierOne
    (c : ℂ) (F : Finset ℂ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F)
    (hdata : ∀ z ∈ F, ∃ q : ℕ,
      1 ≤ q ∧
      z ∈ multiplierOneFixedPointRoots c q ∧
      Function.minimalPeriod (quadratic c) z = q) :
    ∃ L : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ F ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
        (fixedPointPoly c p).roots.count z - 1 ≤ L) := by
  apply eventually_multiplierOne_payload_of_eventually_support_and_exactPeriod_memMultiplierOne
    c F hmultiplierOne
  intro z hzF
  obtain ⟨q, hq, hzmult, hmin⟩ := hdata z hzF
  exact ⟨q, hq, hzmult, exactPeriod_dvd_of_quadratic_minimalPeriod_eq c z hmin⟩

/-- Multiple roots of the fixed-point polynomial are exactly in the multiplier-one locus needed for
the root-defect route.  This is the local algebraic bridge from repeated fixed roots to parabolic
period-`p` multiplier behavior. -/
theorem mem_multiplierOneFixedPointRoots_of_one_lt_roots_count
    (c : ℂ) {p : ℕ} (hp : 1 ≤ p) {z : ℂ}
    (hcount : 1 < (fixedPointPoly c p).roots.count z) :
    z ∈ multiplierOneFixedPointRoots c p := by
  have hrootMult :
      1 < (fixedPointPoly c p).rootMultiplicity z := by
    simpa [Polynomial.count_roots] using hcount
  have hboth :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot (fixedPointPoly_ne_zero c hp)).mp hrootMult
  have hzroot : z ∈ (fixedPointPoly c p).roots.toFinset := by
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (by omega))
  have hprod : (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (1 : ℂ) := by
    have hder := hboth.2
    rw [Polynomial.IsRoot.def, eval_deriv_fixedPointPoly] at hder
    exact sub_eq_zero.mp hder
  exact (mem_multiplierOneFixedPointRoots).mpr ⟨hzroot, hprod⟩

/-- A multiset's cardinality is its number of distinct elements plus the total duplicate excess. -/
theorem multiset_card_eq_toFinset_card_add_count_excess {α : Type*} [DecidableEq α]
    (s : Multiset α) :
    s.card = s.toFinset.card + ∑ x ∈ s.toFinset, (s.count x - 1) := by
  rw [← Multiset.toFinset_sum_count_eq s, Finset.card_eq_sum_ones,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hpos : 0 < s.count x := by
    rw [Multiset.count_pos]
    exact Multiset.mem_toFinset.mp hx
  omega

/-- If all duplicate elements of a multiset lie in `E`, and each duplicate excess on `E` is at most
`L`, then the total duplicate excess is at most `E.card * L`. -/
theorem multiset_count_excess_le_card_mul_of_multiple_support {α : Type*} [DecidableEq α]
    (s : Multiset α) (E : Finset α) (L : ℕ)
    (hsimple_off : ∀ x ∈ s.toFinset, x ∉ E → s.count x ≤ 1)
    (hexcess_on : ∀ x ∈ s.toFinset, x ∈ E → s.count x - 1 ≤ L) :
    (∑ x ∈ s.toFinset, (s.count x - 1)) ≤ E.card * L := by
  classical
  let T : Finset α := s.toFinset.filter fun x => x ∈ E
  have hsplit :
      (∑ x ∈ s.toFinset, (s.count x - 1)) =
        (∑ x ∈ T, (s.count x - 1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not s.toFinset (fun x => x ∈ E)]
    have hzero : (∑ x ∈ s.toFinset.filter (fun x => ¬x ∈ E), (s.count x - 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxroot : x ∈ s.toFinset := (Finset.mem_filter.mp hx).1
      have hxE : x ∉ E := (Finset.mem_filter.mp hx).2
      have hle := hsimple_off x hxroot hxE
      omega
    simp [T, hzero]
  rw [hsplit]
  have hsum_le : (∑ x ∈ T, (s.count x - 1)) ≤ T.card * L := by
    simpa [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul T (fun x => s.count x - 1) L (by
        intro x hx
        exact hexcess_on x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
  exact hsum_le.trans (Nat.mul_le_mul_right L (Finset.card_le_card (by
    intro x hx
    exact (Finset.mem_filter.mp hx).2)))

/-- A bound on duplicate excess gives a lower bound on the number of distinct roots. -/
theorem fixedPointPoly_rootDefect_bound_of_roots_count_excess_le
    (c : ℂ) {p D : ℕ} (hp : 1 ≤ p)
    (hD : (∑ z ∈ (fixedPointPoly c p).roots.toFinset,
      ((fixedPointPoly c p).roots.count z - 1)) ≤ D) :
    2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D := by
  have hroots_card : (fixedPointPoly c p).roots.card = 2 ^ p := by
    rw [IsAlgClosed.card_roots_eq_natDegree, fixedPointPoly_natDegree c hp]
  rw [← hroots_card]
  calc
    (fixedPointPoly c p).roots.card =
        (fixedPointPoly c p).roots.toFinset.card +
          ∑ z ∈ (fixedPointPoly c p).roots.toFinset,
            ((fixedPointPoly c p).roots.count z - 1) :=
      multiset_card_eq_toFinset_card_add_count_excess _
    _ ≤ (fixedPointPoly c p).roots.toFinset.card + D :=
      Nat.add_le_add_left hD _

/-- Eventual duplicate-excess bounds supply the eventual root-defect input consumed by the active
root-defect hRigid route. -/
theorem eventually_fixedPointPoly_rootDefect_bound_of_eventually_roots_count_excess_le
    (c : ℂ) (D : ℕ)
    (hD : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      (∑ z ∈ (fixedPointPoly c p).roots.toFinset,
        ((fixedPointPoly c p).roots.count z - 1)) ≤ D) :
    ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D :=
  hD.mono fun _ hp =>
    fixedPointPoly_rootDefect_bound_of_roots_count_excess_le c hp.1 hp.2

/-- A finite set containing all multiple fixed roots, with bounded local duplicate excess, supplies a
root-defect bound. -/
theorem fixedPointPoly_rootDefect_bound_of_multiple_roots_subset
    (c : ℂ) {p L : ℕ} (hp : 1 ≤ p) (E : Finset ℂ)
    (hsimple_off : ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
      (fixedPointPoly c p).roots.count z ≤ 1)
    (hexcess_on : ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ E →
      (fixedPointPoly c p).roots.count z - 1 ≤ L) :
    2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + E.card * L :=
  fixedPointPoly_rootDefect_bound_of_roots_count_excess_le c hp
    (multiset_count_excess_le_card_mul_of_multiple_support
      (fixedPointPoly c p).roots E L hsimple_off hexcess_on)

/-- If a finite set contains the multiplier-one fixed roots, then it contains all multiple fixed roots.
Together with a local duplicate-excess bound on that finite set, this supplies root defect. -/
theorem fixedPointPoly_rootDefect_bound_of_multiplierOne_subset
    (c : ℂ) {p L : ℕ} (hp : 1 ≤ p) (E : Finset ℂ)
    (hE : multiplierOneFixedPointRoots c p ⊆ E)
    (hexcess_on : ∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ E →
      (fixedPointPoly c p).roots.count z - 1 ≤ L) :
    2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + E.card * L :=
  fixedPointPoly_rootDefect_bound_of_multiple_roots_subset c hp E
    (by
      intro z _hzroot hzE
      by_contra hle
      exact hzE (hE (mem_multiplierOneFixedPointRoots_of_one_lt_roots_count c hp (not_le.mp hle))))
    hexcess_on

/-- Eventual finite support for multiple fixed roots supplies the eventual root-defect input consumed
by the active hRigid route. -/
theorem eventually_fixedPointPoly_rootDefect_bound_of_eventually_multiple_roots_subset
    (c : ℂ) (E : Finset ℂ) (L : ℕ)
    (hmultiple : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∉ E →
        (fixedPointPoly c p).roots.count z ≤ 1) ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ E →
        (fixedPointPoly c p).roots.count z - 1 ≤ L)) :
    ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + E.card * L :=
  hmultiple.mono fun _ hp =>
    fixedPointPoly_rootDefect_bound_of_multiple_roots_subset c hp.1 E hp.2.1 hp.2.2

/-- Eventual finite support for multiplier-one fixed roots supplies the eventual root-defect input
consumed by the active hRigid route. -/
theorem eventually_fixedPointPoly_rootDefect_bound_of_eventually_multiplierOne_subset
    (c : ℂ) (E : Finset ℂ) (L : ℕ)
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      multiplierOneFixedPointRoots c p ⊆ E ∧
      (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ E →
        (fixedPointPoly c p).roots.count z - 1 ≤ L)) :
    ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + E.card * L :=
  hmultiplierOne.mono fun _ hp =>
    fixedPointPoly_rootDefect_bound_of_multiplierOne_subset c hp.1 E hp.2.1 hp.2.2

/-- If the no-extra budget plus the non-strong root count is below the number of distinct fixed roots,
then the strong-root pool beats the budget.  This is the separability-free replacement for
`squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt`. -/
theorem squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt_roots
    (c : ℂ) (p : ℕ) (P : Polynomial (Polynomial ℂ)) (e : Polynomial ℂ)
    (B : Finset (Polynomial ℂ))
    (hbound :
      squarefreeBadDegreeBudget P e B + (nonStrongFixedPointRoots c p).card <
        (fixedPointPoly c p).roots.toFinset.card) :
    squarefreeBadDegreeBudget P e B < (strongFixedPointRoots c p).card := by
  have hsplit :=
    strongFixedPointRoots_card_add_nonStrongFixedPointRoots_card_eq_roots_card c p
  omega

/-- **Bounded-root-defect period selector with explicit denominator witnesses.**

Assume the distinct fixed-root deficit is eventually bounded by `D`, all non-strong roots are
eventually contained in a finite set `E`, and an explicit denominator witness has eventually bounded
degree.  Then some large period has enough strong distinct roots to beat the squarefree budget. -/
theorem exists_period_denominator_of_eventually_nonStrong_subset_of_bounded_rootDefect_denominator_witness
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (E : Finset ℂ) (D M : ℕ)
    (hrootDefect : ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D)
    (hE : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)
    (hdenom : ∀ᶠ p : ℕ in atTop,
      ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
        e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M) :
    ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
      e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
      squarefreeBadDegreeBudget P e ∅ < (strongFixedPointRoots c p).card := by
  have htwo : Tendsto (fun p : ℕ => 2 ^ p) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)
  obtain ⟨p, hdef, hEsub, hdenp, hbig⟩ :=
    (hrootDefect.and (hE.and (hdenom.and
      (htwo.eventually_gt_atTop ((M + squarefreeStaticDegreeBudget P) + E.card + D))))).exists
  obtain ⟨e, S, he0, hPS, hdeg⟩ := hdenp
  refine ⟨p, e, S, he0, hPS, ?_⟩
  have hbudget : squarefreeBadDegreeBudget P e ∅ ≤ M + squarefreeStaticDegreeBudget P :=
    le_trans (squarefreeBadDegreeBudget_empty_le_natDegree_add_static P e)
      (Nat.add_le_add_right hdeg (squarefreeStaticDegreeBudget P))
  have hcard : (nonStrongFixedPointRoots c p).card ≤ E.card := Finset.card_le_card hEsub
  have hlt_roots :
      squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card <
        (fixedPointPoly c p).roots.toFinset.card := by
    have hlt_with_defect :
        squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card + D <
          (fixedPointPoly c p).roots.toFinset.card + D := by
      omega
    omega
  exact
    squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt_roots
      c p P e ∅ hlt_roots

/-- **Bounded-root-defect period selector with non-strong count bound.**

This is the finite-support-free form of the selector above.  The proof only needs eventual bounded
cardinality of the non-strong locus, not containment in one fixed finite set. -/
theorem exists_period_denominator_of_eventually_nonStrong_card_le_of_bounded_rootDefect_denominator_witness
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (N D M : ℕ)
    (hrootDefect : ∀ᶠ p : ℕ in atTop,
      2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D)
    (hN : ∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ N)
    (hdenom : ∀ᶠ p : ℕ in atTop,
      ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
        e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M) :
    ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
      e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
      squarefreeBadDegreeBudget P e ∅ < (strongFixedPointRoots c p).card := by
  have htwo : Tendsto (fun p : ℕ => 2 ^ p) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)
  obtain ⟨p, hdef, hNcard, hdenp, hbig⟩ :=
    (hrootDefect.and (hN.and (hdenom.and
      (htwo.eventually_gt_atTop ((M + squarefreeStaticDegreeBudget P) + N + D))))).exists
  obtain ⟨e, S, he0, hPS, hdeg⟩ := hdenp
  refine ⟨p, e, S, he0, hPS, ?_⟩
  have hbudget : squarefreeBadDegreeBudget P e ∅ ≤ M + squarefreeStaticDegreeBudget P :=
    le_trans (squarefreeBadDegreeBudget_empty_le_natDegree_add_static P e)
      (Nat.add_le_add_right hdeg (squarefreeStaticDegreeBudget P))
  have hlt_roots :
      squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card <
        (fixedPointPoly c p).roots.toFinset.card := by
    have hlt_with_defect :
        squarefreeBadDegreeBudget P e ∅ + (nonStrongFixedPointRoots c p).card + D <
          (fixedPointPoly c p).roots.toFinset.card + D := by
      omega
    omega
  exact
    squarefreeBadDegreeBudget_lt_strongFixedPointRoots_card_of_add_nonStrong_lt_roots
      c p P e ∅ hlt_roots

/-- **Unbounded strong-root-card period selector with explicit denominator witnesses.**

If the strong fixed-root pool is frequently larger than every finite threshold, then the bounded
denominator witness and static squarefree budget can be beaten directly.  This avoids any finite
support or bounded-cardinality hypothesis on the non-strong locus. -/
theorem exists_period_denominator_of_frequently_strongFixedPointRoots_card_gt_of_bounded_denominator_witness
    (c : ℂ) (P : Polynomial (Polynomial ℂ)) (M : ℕ)
    (hstrong : ∀ A : ℕ,
      ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card)
    (hdenom : ∀ᶠ p : ℕ in atTop,
      ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
        e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧ e.natDegree ≤ M) :
    ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
      e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
      squarefreeBadDegreeBudget P e ∅ < (strongFixedPointRoots c p).card := by
  obtain ⟨p, hstrongp, hdenp⟩ :=
    ((hstrong (M + squarefreeStaticDegreeBudget P)).and_eventually hdenom).exists
  obtain ⟨e, S, he0, hPS, hdeg⟩ := hdenp
  refine ⟨p, e, S, he0, hPS, ?_⟩
  have hbudget : squarefreeBadDegreeBudget P e ∅ ≤ M + squarefreeStaticDegreeBudget P :=
    le_trans (squarefreeBadDegreeBudget_empty_le_natDegree_add_static P e)
      (Nat.add_le_add_right hdeg (squarefreeStaticDegreeBudget P))
  exact lt_of_le_of_lt hbudget hstrongp

/-- **Explicit-denominator strong-root-card input for absolute connected `φ_c` transcendence.**

This is the strong-root analogue of the chosen-denominator no-extra interface, but the denominator is
supplied explicitly together with the period.  It does not require fixed-point separability. -/
theorem phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_denominatorWitness_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)),
          e ≠ 0 ∧ (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
          squarefreeBadDegreeBudget P e ∅ < (strongFixedPointRoots c p).card) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_chosen_denominator_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, e, S, he0, hPS, hcard⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨hlead, hderivLead, hres, hconst⟩ :=
    minimal_relation_squarefree_bad_polys_ne_zero
      hUo hUc c hU P hP0 hdeg hPrel hPmin hconst_poly
  have hA0 : ∀ q ∈ squarefreeBadFamily P e ∅, q ≠ 0 :=
    squarefreeBadFamily_ne_zero he0 hlead hderivLead hres hconst (by simp)
  obtain ⟨z₀, hzroot, havoid, hnorm⟩ :=
    exists_strong_fixedPoint_avoiding_squarefreeBadFamily_of_budget_card c p P e ∅ hA0 hcard
  have hp : 1 ≤ p := by
    cases p with
    | zero =>
      have hzero : (strongFixedPointRoots c 0).card = 0 := by
        simp [strongFixedPointRoots]
      rw [hzero] at hcard
      omega
    | succ k => omega
  have hFz : (quadratic c)^[p] z₀ = z₀ := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp (Multiset.mem_toFinset.mp hzroot)
  refine ⟨p, e, S, ∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z₀, z₀,
    he0, hPS, hFz, hasDerivAt_quadratic_iterate c z₀ p, hnorm,
    havoid e (mem_squarefreeBadFamily_denominator P e ∅),
    ?_,
    havoid P.leadingCoeff (mem_squarefreeBadFamily_leadingCoeff P e ∅),
    havoid (P.coeff 0) (mem_squarefreeBadFamily_constCoeff P e ∅)⟩
  exact separable_specialization_of_avoids_squarefree_bad_locus P
    (mem_squarefreeBadFamily_leadingCoeff P e ∅)
    (mem_squarefreeBadFamily_derivative_leadingCoeff P e ∅)
    (mem_squarefreeBadFamily_resultant P e ∅)
    havoid

/-- **Unbounded strong-root-card content-denominator input for absolute connected `φ_c`
transcendence.**

This is the leanest current hRigid reduction: once the dynamical side proves that the number of
strong period-`p` fixed roots is frequently unbounded, the content denominator and finite
squarefree budget are beaten internally. -/
theorem phiMero_transcendental_of_repelling_frequently_strongFixedPointRoots_card_gt_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hstrong : ∀ A : ℕ,
      ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply
    phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_denominatorWitness_noExtra_input
      hUo hUc hUne hUinf c hU
  intro P hP0 _hdeg hPrel hPmin _hcount _hconst_poly
  exact
    exists_period_denominator_of_frequently_strongFixedPointRoots_card_gt_of_bounded_denominator_witness
      c P P.content.natDegree hstrong
      (eventually_content_compRelPoly_denominatorWitness_of_minimal
        hUo hUne c hU P hP0 hPrel hPmin)

/-- **Bounded-root-defect content-denominator input for absolute connected `φ_c` transcendence.**

For each minimal relation, the caller supplies only a finite eventual exceptional set for non-strong
roots and an eventual bound on the distinct fixed-root deficit.  The denominator is created
internally from `P.content`, and separability/no-multiplier-one is not required. -/
theorem phiMero_transcendental_of_repelling_eventually_rootDefect_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E : Finset ℂ) (D : ℕ),
          (∀ᶠ p : ℕ in atTop,
            2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply
    phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_denominatorWitness_noExtra_input
      hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, D, hrootDefect, hE⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact
    exists_period_denominator_of_eventually_nonStrong_subset_of_bounded_rootDefect_denominator_witness
      c P E D P.content.natDegree hrootDefect hE
      (eventually_content_compRelPoly_denominatorWitness_of_minimal
        hUo hUne c hU P hP0 hPrel hPmin)

/-- **Bounded-root-defect/card-bound content-denominator input for absolute connected `φ_c`
transcendence.**

This is the finite-support-free version of
`phiMero_transcendental_of_repelling_eventually_rootDefect_contentDenominator_noExtra_input`:
the caller only needs an eventual cardinality bound for non-strong fixed roots. -/
theorem phiMero_transcendental_of_repelling_eventually_rootDefect_cardBound_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (N D : ℕ),
          (∀ᶠ p : ℕ in atTop,
            2 ^ p ≤ (fixedPointPoly c p).roots.toFinset.card + D) ∧
          (∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ N)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply
    phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_denominatorWitness_noExtra_input
      hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨N, D, hrootDefect, hN⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact
    exists_period_denominator_of_eventually_nonStrong_card_le_of_bounded_rootDefect_denominator_witness
      c P N D P.content.natDegree hrootDefect hN
      (eventually_content_compRelPoly_denominatorWitness_of_minimal
        hUo hUne c hU P hP0 hPrel hPmin)

/-- **Multiplier-one content-denominator input for absolute connected `φ_c` transcendence.**

This is the active hRigid surface: instead of asking for an abstract fixed-root deficit bound, the
caller supplies a finite eventual support for multiplier-one fixed roots and a uniform local bound
for duplicate root excess on that support.  Lean proves that all multiple fixed roots lie in the
multiplier-one locus and converts the input to the root-defect inequality internally. -/
theorem phiMero_transcendental_of_repelling_eventually_multiplierOne_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E F : Finset ℂ) (L : ℕ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧
            multiplierOneFixedPointRoots c p ⊆ F ∧
            (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
              (fixedPointPoly c p).roots.count z - 1 ≤ L)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_eventually_rootDefect_contentDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, F, L, hmultiplierOne, hE⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact ⟨E, F.card * L,
    eventually_fixedPointPoly_rootDefect_bound_of_eventually_multiplierOne_subset
      c F L hmultiplierOne,
    hE⟩

/-- **Multiplier-one/card-bound content-denominator input for absolute connected `φ_c`
transcendence.**

This is the active hRigid surface with the non-strong hypothesis weakened from eventual finite
support to eventual bounded cardinality. -/
theorem phiMero_transcendental_of_repelling_eventually_multiplierOne_cardBound_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (N : ℕ) (F : Finset ℂ) (L : ℕ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧
            multiplierOneFixedPointRoots c p ⊆ F ∧
            (∀ z ∈ (fixedPointPoly c p).roots.toFinset, z ∈ F →
              (fixedPointPoly c p).roots.count z - 1 ≤ L)) ∧
          (∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ N)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply
    phiMero_transcendental_of_repelling_eventually_rootDefect_cardBound_contentDenominator_noExtra_input
      hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨N, F, L, hmultiplierOne, hN⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  exact ⟨N, F.card * L,
    eventually_fixedPointPoly_rootDefect_bound_of_eventually_multiplierOne_subset
      c F L hmultiplierOne,
    hN⟩

/-- **Pointwise multiplier-one content-denominator input for absolute connected `φ_c`
transcendence.**

This is the local-multiplicity version of the active hRigid surface.  The caller supplies a finite
eventual support for multiplier-one roots and, for each point of that support, an eventual local
duplicate-excess bound.  Lean takes the maximum over the finite support and feeds the active
multiplier-one route. -/
theorem phiMero_transcendental_of_repelling_eventually_multiplierOne_pointwiseDuplicate_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E F : Finset ℂ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F) ∧
          (∀ z ∈ F, ∃ Lz : ℕ, ∀ᶠ p : ℕ in atTop,
            ∀ _hzroot : z ∈ (fixedPointPoly c p).roots.toFinset,
              (fixedPointPoly c p).roots.count z - 1 ≤ Lz) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_eventually_multiplierOne_contentDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, F, hmultiplierOne, hpointwise, hE⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨L, hpayload⟩ :=
    eventually_multiplierOne_payload_of_eventually_support_and_pointwise_duplicateBounds
      c F hmultiplierOne hpointwise
  exact ⟨E, F, L, hpayload, hE⟩

/--
Same hRigid endpoint as
`phiMero_transcendental_of_repelling_eventually_multiplierOne_pointwiseDuplicate_contentDenominator_noExtra_input`,
but the local input is stated in the analytic order that a parabolic normal-form proof naturally
produces.  The root-count duplicate-excess arithmetic is discharged internally. -/
theorem phiMero_transcendental_of_repelling_eventually_multiplierOne_pointwiseAnalyticOrder_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E F : Finset ℂ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F) ∧
          (∀ z ∈ F, ∃ Lz : ℕ, ∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧
              analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z ≤
                ((Lz + 1 : ℕ) : ℕ∞)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_eventually_multiplierOne_contentDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨E, F, hmultiplierOne, hpointwise, hE⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨L, hpayload⟩ :=
    eventually_multiplierOne_payload_of_eventually_support_and_pointwise_analyticOrderBounds
      c F hmultiplierOne hpointwise
  exact ⟨E, F, L, hpayload, hE⟩

end Bottcher
