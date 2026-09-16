import GaloisForLFunctions.RHTower.PrimeLogCubicLaplaceGraphFormation

/-!
# Literal cubic-clock covariance on the prime-log graph core

`PrimeLogCubicLaplaceGraphFormation` supplies the unregularized finite-prime synthesis whose
canonical closure is the critical source graph.  This file proves its missing **source-side**
cubic-clock identity on the literal finite core.

For the feature

```text
phi_p(t) = 2 t log(p)^2 p^(-1/2) exp(-t log(p)),
```

the forced Euler differential expression `-d/dt + 1/t` has `phi_p` as an eigenfeature of
eigenvalue `log p`.  The identity is deliberately proved as a positive-time germ: the expression
has its genuine singular endpoint at zero, precisely where the unbounded graph problem lives.
Consequently the third iterate on every literal finite-prime core is the unmodified
`(log p)^3` source-clock action.

This is not a theta quotient, an extension lift, a Calderón class, or a boundary-index theorem.
It supplies the exact source graph covariance required before a theta-side cubic morphism can be
constructed.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

/-- The Euler differential expression forced by the `t exp(-t log p)` source shape. -/
def primeLogCriticalLaplaceEuler (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  -deriv f t + f t / (t : ℂ)

private theorem hasDerivAt_primeLogCriticalLaplaceFeatureC
    (p : Nat.Primes) (t : ℝ) :
    HasDerivAt (primeLogCriticalLaplaceFeatureC p)
      (((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ)) *
        (1 - t * Real.log (p : ℝ)) *
        Real.exp (-(Real.log (p : ℝ) * t)) : ℝ) : ℂ) t := by
  let c : ℝ := 2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ)
  let a : ℝ := Real.log (p : ℝ)
  have hlin : HasDerivAt (fun s : ℝ => -(a * s)) (-a) t := by
    simpa only [id_eq, mul_one, neg_mul] using
      ((hasDerivAt_id t).const_mul (-a))
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(a * s)))
      (Real.exp (-(a * t)) * (-a)) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-(a * t))).comp t hlin
  have hct : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul c)
  have hmul := hct.mul hexp
  have hreal : HasDerivAt (primeLogCriticalLaplaceFeature p)
      (c * (1 - t * a) * Real.exp (-(a * t))) t := by
    have hshape : primeLogCriticalLaplaceFeature p =
        fun s : ℝ => c * s * Real.exp (-(a * s)) := by
      funext s
      simp only [primeLogCriticalLaplaceFeature, c, a]
      ring
    rw [hshape]
    have hderiv : c * Real.exp (-(a * t)) +
        (c * t) * (Real.exp (-(a * t)) * (-a)) =
        c * (1 - t * a) * Real.exp (-(a * t)) := by
      ring
    rw [← hderiv]
    exact hmul
  exact hreal.ofReal_comp

/-- One literal feature is an Euler eigenfeature away from the source endpoint. -/
theorem primeLogCriticalLaplaceEuler_feature
    (p : Nat.Primes) {t : ℝ} (ht : t ≠ 0) :
    primeLogCriticalLaplaceEuler (primeLogCriticalLaplaceFeatureC p) t =
      (Real.log (p : ℝ) : ℂ) * primeLogCriticalLaplaceFeatureC p t := by
  rw [primeLogCriticalLaplaceEuler,
    (hasDerivAt_primeLogCriticalLaplaceFeatureC p t).deriv]
  unfold primeLogCriticalLaplaceFeatureC primeLogCriticalLaplaceFeature
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  field_simp [htC]
  push_cast
  ring

private theorem primeLogCriticalLaplaceEuler_const_feature
    (p : Nat.Primes) (z : ℂ) {t : ℝ} (ht : t ≠ 0) :
    primeLogCriticalLaplaceEuler (fun s => z * primeLogCriticalLaplaceFeatureC p s) t =
      z * (Real.log (p : ℝ) : ℂ) * primeLogCriticalLaplaceFeatureC p t := by
  rw [primeLogCriticalLaplaceEuler,
    ((hasDerivAt_primeLogCriticalLaplaceFeatureC p t).const_mul z).deriv]
  unfold primeLogCriticalLaplaceFeatureC primeLogCriticalLaplaceFeature
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  field_simp [htC]
  push_cast
  ring

/-- Iteration of the genuine Euler expression, kept as a function so its positive-time germ is
available without installing a false value at the singular endpoint. -/
def primeLogCriticalLaplaceEulerIterate : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, f => f
  | n + 1, f => fun t =>
      primeLogCriticalLaplaceEuler (primeLogCriticalLaplaceEulerIterate n f) t

/-- Each iterated positive-time germ retains the exact literal prime clock. -/
theorem primeLogCriticalLaplaceEulerIterate_feature
    (n : ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    primeLogCriticalLaplaceEulerIterate n (primeLogCriticalLaplaceFeatureC p) t =
      (Real.log (p : ℝ) : ℂ) ^ n * primeLogCriticalLaplaceFeatureC p t := by
  induction n generalizing t with
  | zero => simp [primeLogCriticalLaplaceEulerIterate]
  | succ n ih =>
      have hlocal : primeLogCriticalLaplaceEulerIterate n
          (primeLogCriticalLaplaceFeatureC p) =ᶠ[𝓝 t]
          fun s => (Real.log (p : ℝ) : ℂ) ^ n *
            primeLogCriticalLaplaceFeatureC p s := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ih (show 0 < s from hs)
      change primeLogCriticalLaplaceEuler
        (primeLogCriticalLaplaceEulerIterate n
          (primeLogCriticalLaplaceFeatureC p)) t = _
      rw [primeLogCriticalLaplaceEuler, hlocal.deriv_eq, hlocal.self_of_nhds]
      change primeLogCriticalLaplaceEuler
        (fun s => (Real.log (p : ℝ) : ℂ) ^ n *
          primeLogCriticalLaplaceFeatureC p s) t = _
      rw [primeLogCriticalLaplaceEuler_const_feature p _ ht.ne']
      ring

/-- The literal finite-prime core with the `n`-th unmodified source-clock weight. -/
def primeLogCriticalLaplaceClockedMass
    (n : ℕ) (l : Nat.Primes →₀ ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ l.support, l p * (Real.log (p : ℝ) : ℂ) ^ n *
    primeLogCriticalLaplaceFeatureC p t

private theorem primeLogCriticalLaplaceEuler_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (t : ℝ)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) t) :
    primeLogCriticalLaplaceEuler (fun x => ∑ i ∈ s, f i x) t =
      ∑ i ∈ s, primeLogCriticalLaplaceEuler (f i) t := by
  unfold primeLogCriticalLaplaceEuler
  have hsum := HasDerivAt.sum (u := s)
    (fun i hi => (hf i hi).hasDerivAt)
  have hfun : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x
    simp
  rw [hfun]
  rw [hsum.deriv]
  rw [← Finset.sum_neg_distrib]
  simp only [Finset.sum_apply]
  rw [Finset.sum_div, ← Finset.sum_add_distrib]

/-- The literal Euler expression raises exactly one source-clock degree on every finite core. -/
theorem primeLogCriticalLaplaceEuler_clockedMass
    (n : ℕ) (l : Nat.Primes →₀ ℂ) {t : ℝ} (ht : 0 < t) :
    primeLogCriticalLaplaceEuler (primeLogCriticalLaplaceClockedMass n l) t =
      primeLogCriticalLaplaceClockedMass (n + 1) l t := by
  unfold primeLogCriticalLaplaceClockedMass
  rw [primeLogCriticalLaplaceEuler_finset_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [primeLogCriticalLaplaceEuler_const_feature p _ ht.ne']
    ring
  · intro p hp
    exact ((hasDerivAt_primeLogCriticalLaplaceFeatureC p t).const_mul
      (l p * (Real.log (p : ℝ) : ℂ) ^ n)).differentiableAt

/-- The exact iterated Euler clock acts on the literal finite graph core by the corresponding
prime-log power, as a positive-time germ. -/
theorem primeLogCriticalLaplaceEulerIterate_clockedMass
    (n : ℕ) (l : Nat.Primes →₀ ℂ) {t : ℝ} (ht : 0 < t) :
    primeLogCriticalLaplaceEulerIterate n
      (primeLogCriticalLaplaceClockedMass 0 l) t =
      primeLogCriticalLaplaceClockedMass n l t := by
  induction n generalizing t with
  | zero => simp [primeLogCriticalLaplaceEulerIterate]
  | succ n ih =>
      have hlocal : primeLogCriticalLaplaceEulerIterate n
          (primeLogCriticalLaplaceClockedMass 0 l) =ᶠ[𝓝 t]
          primeLogCriticalLaplaceClockedMass n l := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ih (show 0 < s from hs)
      change primeLogCriticalLaplaceEuler
        (primeLogCriticalLaplaceEulerIterate n
          (primeLogCriticalLaplaceClockedMass 0 l)) t = _
      rw [primeLogCriticalLaplaceEuler, hlocal.deriv_eq, hlocal.self_of_nhds]
      change primeLogCriticalLaplaceEuler
        (primeLogCriticalLaplaceClockedMass n l) t = _
      simpa [Nat.succ_eq_add_one] using
        primeLogCriticalLaplaceEuler_clockedMass n l ht

/-- **Cubic source covariance.**  The third literal Euler clock on the exact finite graph core
is precisely the unmodified `(log p)^3` prime-clock action. -/
theorem primeLogCriticalLaplaceEuler_cubic_clockedMass
    (l : Nat.Primes →₀ ℂ) {t : ℝ} (ht : 0 < t) :
    primeLogCriticalLaplaceEulerIterate 3
      (primeLogCriticalLaplaceClockedMass 0 l) t =
      primeLogCriticalLaplaceClockedMass 3 l t := by
  exact primeLogCriticalLaplaceEulerIterate_clockedMass 3 l ht

end

end RHTower
