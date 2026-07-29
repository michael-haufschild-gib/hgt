/-
# Local multiplicity stability for tangent-to-identity germs

This file proves the local parabolic brick needed by the connected hRigid path: if an analytic germ
has first nonzero displacement term of order `r ≥ 2`, then every positive iterate has the same
vanishing order.  The proof tracks the leading unit through iteration; the unit after `n` iterates has
value `n • u z`, so characteristic zero prevents cancellation.
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic
import GaloisForLFunctions.Bottcher.IndexFormula

open Polynomial Filter Topology
open scoped Topology

namespace Bottcher

private lemma analyticAt_iterate_of_fixed
    {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) (hFz : F z = z) :
    ∀ n : ℕ, AnalyticAt ℂ (F^[n]) z := by
  intro n
  induction n with
  | zero =>
      simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) z)
  | succ n ih =>
      have hFn_at : AnalyticAt ℂ (F^[n]) (F z) := by
        simpa [hFz] using ih
      have hcomp : AnalyticAt ℂ (fun y => (F^[n]) (F y)) z := hFn_at.comp hF
      simpa only [Function.iterate_succ_apply] using! hcomp

/-- If `F y - y = (y - z)^r u y` near `z`, then the displacement of `F^[n]` has the
same factor, with leading unit value `n * u z`. -/
theorem exists_iterate_tangentToId_factor
    {F u : ℂ → ℂ} {z : ℂ} {r : ℕ}
    (hr : 2 ≤ r)
    (hF : AnalyticAt ℂ F z)
    (hu : AnalyticAt ℂ u z)
    (hfac : (fun y : ℂ => F y - y) =ᶠ[𝓝 z] fun y => (y - z) ^ r * u y) :
    ∀ n : ℕ, ∃ u_n : ℂ → ℂ,
      AnalyticAt ℂ u_n z ∧
      u_n z = (n : ℂ) * u z ∧
      (fun y : ℂ => (F^[n]) y - y) =ᶠ[𝓝 z] fun y => (y - z) ^ r * u_n y := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hFz : F z = z := by
    have hz := hfac.eq_of_nhds
    exact sub_eq_zero.mp (by simpa [hrpos.ne'] using hz)
  intro n
  induction n with
  | zero =>
      refine ⟨fun _ => 0, analyticAt_const, ?_, ?_⟩
      · simp
      · filter_upwards with y
        simp
  | succ n ih =>
      obtain ⟨u_n, hun, hunz, hfacn⟩ := ih
      have hFn_an : AnalyticAt ℂ (F^[n]) z := analyticAt_iterate_of_fixed hF hFz n
      have hFnz : (F^[n]) z = z := Function.iterate_fixed hFz n
      let v : ℂ → ℂ := fun y => 1 + (y - z) ^ (r - 1) * u_n y
      have hv_an : AnalyticAt ℂ v z := by
        dsimp [v]
        fun_prop
      have hvz : v z = 1 := by
        have hrpred : 0 < r - 1 := by omega
        simp [v, hrpred.ne']
      have hFn_sub_z : (fun y : ℂ => (F^[n]) y - z) =ᶠ[𝓝 z]
          fun y => (y - z) * v y := by
        filter_upwards [hfacn] with y hy
        have hpow : (y - z) ^ r = (y - z) * (y - z) ^ (r - 1) := by
          calc
            (y - z) ^ r = (y - z) ^ (1 + (r - 1)) := by
              congr 1
              omega
            _ = (y - z) * (y - z) ^ (r - 1) := by rw [pow_add, pow_one]
        calc
          (F^[n]) y - z = (y - z) + ((F^[n]) y - y) := by ring
          _ = (y - z) + (y - z) ^ r * u_n y := by rw [hy]
          _ = (y - z) * v y := by
            dsimp [v]
            rw [hpow]
            ring
      have hHcomp : (fun y : ℂ => F ((F^[n]) y) - (F^[n]) y) =ᶠ[𝓝 z]
          fun y => (((F^[n]) y) - z) ^ r * u ((F^[n]) y) := by
        have hFn_tendsto : Tendsto (F^[n]) (𝓝 z) (𝓝 z) := by
          simpa [hFnz] using hFn_an.continuousAt.tendsto
        simpa [Function.comp_def] using hfac.comp_tendsto hFn_tendsto
      have hHcomp' : (fun y : ℂ => F ((F^[n]) y) - (F^[n]) y) =ᶠ[𝓝 z]
          fun y => (y - z) ^ r * (v y ^ r * u ((F^[n]) y)) := by
        filter_upwards [hHcomp, hFn_sub_z] with y h1 h2
        rw [h1, h2, mul_pow]
        ring
      let u_next : ℂ → ℂ := fun y => v y ^ r * u ((F^[n]) y) + u_n y
      refine ⟨u_next, ?_, ?_, ?_⟩
      · dsimp [u_next]
        have hu_at : AnalyticAt ℂ u ((F^[n]) z) := by
          simpa [hFnz] using hu
        exact ((hv_an.pow r).mul (hu_at.comp hFn_an)).add hun
      · dsimp [u_next]
        rw [hvz, hFnz, hunz, Nat.cast_add, Nat.cast_one]
        ring
      · filter_upwards [hHcomp', hfacn] with y h1 h2
        rw [Function.iterate_succ_apply']
        calc
          F ((F^[n]) y) - y =
              (F ((F^[n]) y) - (F^[n]) y) + ((F^[n]) y - y) := by
            ring
          _ = (y - z) ^ r * (v y ^ r * u ((F^[n]) y)) + (y - z) ^ r * u_n y := by
            rw [h1, h2]
          _ = (y - z) ^ r * u_next y := by
            dsimp [u_next]
            ring

/-- A tangent-to-identity analytic germ has all positive iterates with the same local vanishing
order as the first displacement term. -/
theorem analyticOrderAt_iterate_sub_self_of_tangentToId
    {F u : ℂ → ℂ} {z : ℂ} {r n : ℕ}
    (hr : 2 ≤ r)
    (hF : AnalyticAt ℂ F z)
    (hu : AnalyticAt ℂ u z)
    (hu_ne : u z ≠ 0)
    (hfac : (fun y : ℂ => F y - y) =ᶠ[𝓝 z] fun y => (y - z) ^ r * u y)
    (hn : 1 ≤ n) :
    analyticOrderAt (fun y : ℂ => (F^[n]) y - y) z = (r : ℕ∞) := by
  obtain ⟨u_n, hun, hunz, hfacn⟩ :=
    exists_iterate_tangentToId_factor (F := F) (u := u) (z := z) (r := r) hr hF hu hfac n
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hFz : F z = z := by
    have hz := hfac.eq_of_nhds
    exact sub_eq_zero.mp (by simpa [hrpos.ne'] using hz)
  have hFn_an : AnalyticAt ℂ (F^[n]) z := analyticAt_iterate_of_fixed hF hFz n
  have han : AnalyticAt ℂ (fun y : ℂ => (F^[n]) y - y) z := hFn_an.sub analyticAt_id
  rw [han.analyticOrderAt_eq_natCast]
  refine ⟨u_n, hun, ?_, ?_⟩
  · rw [hunz]
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    exact mul_ne_zero (by exact_mod_cast hnpos.ne') hu_ne
  · simpa [smul_eq_mul] using! hfacn

/-- Fixed-point-polynomial form of local parabolic multiplicity stability.  If the first-return
germ `f_c^[q]` has displacement `(y - z)^r u y` with `r ≥ 2` and `u z ≠ 0`, then every positive
multiple period `q * n` has the same analytic order at `z`. -/
theorem analyticOrderAt_fixedPointPoly_eval_mul_of_tangentToId
    (c z : ℂ) {q r n : ℕ} {u : ℂ → ℂ}
    (hr : 2 ≤ r)
    (hu : AnalyticAt ℂ u z)
    (hu_ne : u z ≠ 0)
    (hfac : (fun y : ℂ => (quadratic c)^[q] y - y) =ᶠ[𝓝 z]
      fun y => (y - z) ^ r * u y)
    (hn : 1 ≤ n) :
    analyticOrderAt (fun y : ℂ => (fixedPointPoly c (q * n)).eval y) z = (r : ℕ∞) := by
  have hF : AnalyticAt ℂ ((quadratic c)^[q]) z := by
    have hpoly : AnalyticAt ℂ (fun y : ℂ => (quadraticPolyIterate c q).eval y) z := by
      simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) z).aeval_polynomial
        (quadraticPolyIterate c q)
    have hev : (fun y : ℂ => (quadratic c)^[q] y) =
        fun y : ℂ => (quadraticPolyIterate c q).eval y := by
      funext y
      rw [quadraticPolyIterate_eval]
    simpa [hev] using hpoly
  have hmain := analyticOrderAt_iterate_sub_self_of_tangentToId
    (F := (quadratic c)^[q]) (u := u) (z := z) (r := r) (n := n) hr hF hu hu_ne hfac hn
  have hcongr : (fun y : ℂ => (fixedPointPoly c (q * n)).eval y) =ᶠ[𝓝 z]
      fun y : ℂ => (((quadratic c)^[q])^[n]) y - y := by
    filter_upwards with y
    rw [fixedPointPoly_eval]
    have hiter := congrFun (Function.iterate_mul (f := quadratic c) q n) y
    rw [hiter]
  exact (analyticOrderAt_congr hcongr).trans hmain

/-- Exact-period form of the local parabolic bound consumed by the hRigid endpoint.  If every
period fixing `z` is a multiple of `q`, and the `q`-return germ is tangent to identity with first
nonzero displacement order `r`, then all sufficiently large fixed-point polynomials have analytic
order at most `r + 1` at `z`.  Multiples of `q` use the local iteration theorem; nonmultiples do not
vanish at `z`, so their analytic order is zero. -/
theorem eventually_analyticOrderAt_fixedPointPoly_eval_le_of_exact_period_tangentToId
    (c z : ℂ) {q r : ℕ} {u : ℂ → ℂ}
    (hexact : ∀ p : ℕ, (quadratic c)^[p] z = z → q ∣ p)
    (hr : 2 ≤ r)
    (hu : AnalyticAt ℂ u z)
    (hu_ne : u z ≠ 0)
    (hfac : (fun y : ℂ => (quadratic c)^[q] y - y) =ᶠ[𝓝 z]
      fun y => (y - z) ^ r * u y) :
    ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
        analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z ≤
          ((r + 1 : ℕ) : ℕ∞) := by
  filter_upwards [eventually_ge_atTop 1] with p hp
  refine ⟨hp, ?_⟩
  by_cases hfix : (quadratic c)^[p] z = z
  · obtain ⟨n, hn⟩ := hexact p hfix
    subst p
    have hnpos : 1 ≤ n := by
      by_contra hn0
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos (by simpa using hn0)
      subst n
      simp at hp
    have horder := analyticOrderAt_fixedPointPoly_eval_mul_of_tangentToId
      (c := c) (z := z) (q := q) (r := r) (n := n) (u := u) hr hu hu_ne hfac hnpos
    rw [horder]
    exact_mod_cast Nat.le_succ r
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

/-- Exact-period form using analytic order of the first-return displacement instead of an explicit
unit factor.  This is usually the most convenient local parabolic input: once the return displacement
has finite order `r ≥ 2`, the endpoint's eventual fixed-point-polynomial order bound follows. -/
theorem eventually_analyticOrderAt_fixedPointPoly_eval_le_of_exact_period_returnOrder
    (c z : ℂ) {q r : ℕ}
    (hexact : ∀ p : ℕ, (quadratic c)^[p] z = z → q ∣ p)
    (hr : 2 ≤ r)
    (horder : analyticOrderAt (fun y : ℂ => (quadratic c)^[q] y - y) z = (r : ℕ∞)) :
    ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
        analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z ≤
          ((r + 1 : ℕ) : ℕ∞) := by
  have hF : AnalyticAt ℂ ((quadratic c)^[q]) z := by
    have hpoly : AnalyticAt ℂ (fun y : ℂ => (quadraticPolyIterate c q).eval y) z := by
      simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) z).aeval_polynomial
        (quadraticPolyIterate c q)
    have hev : (fun y : ℂ => (quadratic c)^[q] y) =
        fun y : ℂ => (quadraticPolyIterate c q).eval y := by
      funext y
      rw [quadraticPolyIterate_eval]
    simpa [hev] using hpoly
  have han : AnalyticAt ℂ (fun y : ℂ => (quadratic c)^[q] y - y) z := hF.sub analyticAt_id
  obtain ⟨u, hu, hu_ne, hfac_smul⟩ := (han.analyticOrderAt_eq_natCast).mp horder
  have hfac : (fun y : ℂ => (quadratic c)^[q] y - y) =ᶠ[𝓝 z]
      fun y => (y - z) ^ r * u y := by
    filter_upwards [hfac_smul] with y hy
    simpa [smul_eq_mul] using hy
  exact eventually_analyticOrderAt_fixedPointPoly_eval_le_of_exact_period_tangentToId
    (c := c) (z := z) (q := q) (r := r) (u := u) hexact hr hu hu_ne hfac

end Bottcher

namespace Bottcher

/-- Exact-period divisibility from mathlib's `minimalPeriod`: if `q` is the minimal return time,
then every return time is a multiple of `q`. -/
theorem exactPeriod_dvd_of_minimalPeriod_eq {α : Type*} {f : α → α} {z : α} {q : ℕ}
    (hq : Function.minimalPeriod f z = q) :
    ∀ p : ℕ, f^[p] z = z → q ∣ p := by
  intro p hp
  rw [← hq]
  exact Function.IsPeriodicPt.minimalPeriod_dvd hp

/-- Quadratic-family spelling of `exactPeriod_dvd_of_minimalPeriod_eq`. -/
theorem exactPeriod_dvd_of_quadratic_minimalPeriod_eq (c z : ℂ) {q : ℕ}
    (hq : Function.minimalPeriod (quadratic c) z = q) :
    ∀ p : ℕ, (quadratic c)^[p] z = z → q ∣ p :=
  exactPeriod_dvd_of_minimalPeriod_eq hq

end Bottcher

namespace Bottcher

/-- Multiple-period order bound from finite return order, without requiring that the multiplier-one
return is the minimal dynamical period. -/
theorem analyticOrderAt_fixedPointPoly_eval_mul_le_of_returnOrder
    (c z : ℂ) {q r n : ℕ}
    (hr : 2 ≤ r)
    (horder : analyticOrderAt (fun y : ℂ => (quadratic c)^[q] y - y) z = (r : ℕ∞))
    (hn : 1 ≤ n) :
    analyticOrderAt (fun y : ℂ => (fixedPointPoly c (q * n)).eval y) z ≤
      ((r + 1 : ℕ) : ℕ∞) := by
  have hF : AnalyticAt ℂ ((quadratic c)^[q]) z := by
    have hpoly : AnalyticAt ℂ (fun y : ℂ => (quadraticPolyIterate c q).eval y) z := by
      simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) z).aeval_polynomial
        (quadraticPolyIterate c q)
    have hev : (fun y : ℂ => (quadratic c)^[q] y) =
        fun y : ℂ => (quadraticPolyIterate c q).eval y := by
      funext y
      rw [quadraticPolyIterate_eval]
    simpa [hev] using hpoly
  have han : AnalyticAt ℂ (fun y : ℂ => (quadratic c)^[q] y - y) z := hF.sub analyticAt_id
  obtain ⟨u, hu, hu_ne, hfac_smul⟩ := (han.analyticOrderAt_eq_natCast).mp horder
  have hfac : (fun y : ℂ => (quadratic c)^[q] y - y) =ᶠ[𝓝 z]
      fun y => (y - z) ^ r * u y := by
    filter_upwards [hfac_smul] with y hy
    simpa [smul_eq_mul] using hy
  have hmul := analyticOrderAt_fixedPointPoly_eval_mul_of_tangentToId
    (c := c) (z := z) (q := q) (r := r) (n := n) (u := u) hr hu hu_ne hfac hn
  rw [hmul]
  exact_mod_cast Nat.le_succ r

end Bottcher
