import GaloisForLFunctions.HTGeometry.EntireCascade
import GaloisForLFunctions.HTGeometry.PolyaFreeBasePoint

/-!
# Clearing the chain-rule denominator

The first-order equation for a constituent, evaluated at the previous state, involves that
constituent's derivative *at the previous state*.  The chain rule expresses it as a quotient of the
new state's derivative by the previous one's.  Multiplying through by the appropriate power of the
denominator turns the equation into a polynomial relation among the states and their derivatives —
which is what a relation among the states means.

This is the algebraic half of the passage from a differential relation for the last state to a
polynomial relation among all of them.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **Clearing the denominator of a top-degree relation.**  A vanishing polynomial in `w/t` of degree
at most `d` becomes, after multiplying by `t^d`, a vanishing polynomial in `w` and `t`. -/
theorem sum_mul_div_pow_eq_zero {A : ℕ → ℂ} {d : ℕ} {w t : ℂ} (ht : t ≠ 0)
    (h : ∑ c ∈ Finset.range (d + 1), A c * (w / t) ^ c = 0) :
    ∑ c ∈ Finset.range (d + 1), A c * w ^ c * t ^ (d - c) = 0 := by
  have hkey : ∀ c ∈ Finset.range (d + 1),
      A c * (w / t) ^ c * t ^ d = A c * w ^ c * t ^ (d - c) := by
    intro c hc
    have hcd : c ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
    have hsplit : t ^ d = t ^ c * t ^ (d - c) := by
      rw [← pow_add]
      congr 1
      omega
    have htc : (t : ℂ) ^ c ≠ 0 := pow_ne_zero _ ht
    rw [hsplit, div_pow]
    field_simp
  calc ∑ c ∈ Finset.range (d + 1), A c * w ^ c * t ^ (d - c)
      = ∑ c ∈ Finset.range (d + 1), A c * (w / t) ^ c * t ^ d :=
        (Finset.sum_congr rfl hkey).symm
    _ = (∑ c ∈ Finset.range (d + 1), A c * (w / t) ^ c) * t ^ d := by
        rw [Finset.sum_mul]
    _ = 0 := by rw [h, zero_mul]

/-- **The chain-rule substitution.**  At a point where the previous state's derivative does not
vanish, the constituent's derivative at that state is the quotient of the two states' derivatives. -/
theorem deriv_eq_div_of_cascade {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (n : ℕ) {z : ℂ}
    (hz : deriv (entireCascade f n) z ≠ 0) :
    deriv (f n) (entireCascade f n z)
      = deriv (entireCascade f (n + 1)) z / deriv (entireCascade f n) z := by
  rw [deriv_entireCascade_succ hf n z]
  field_simp

/-- **The cleared relation along the cascade.**  A first-order equation for the constituent, written
in the coefficients `A c` of its derivative, becomes a polynomial relation among the two states'
derivatives. -/
theorem cascade_relation_cleared {f : ℕ → ℂ → ℂ} {A : ℕ → ℂ} {d n : ℕ} {z : ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hz : deriv (entireCascade f n) z ≠ 0)
    (h : ∑ c ∈ Finset.range (d + 1), A c * (deriv (f n) (entireCascade f n z)) ^ c = 0) :
    ∑ c ∈ Finset.range (d + 1),
        A c * (deriv (entireCascade f (n + 1)) z) ^ c
          * (deriv (entireCascade f n) z) ^ (d - c) = 0 := by
  refine sum_mul_div_pow_eq_zero hz ?_
  rw [← deriv_eq_div_of_cascade hf n hz]
  exact h

/-! ## Non-constancy along the cascade

The clearing step needs the previous state's derivative to be nonzero, which holds off a discrete set
provided the state is non-constant.  Non-constancy propagates: a non-constant entire inner function
has open image, and an entire outer function constant on an open set is constant everywhere. -/

/-- **Non-constancy is preserved by composition.** -/
theorem exists_ne_comp {g h : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) (hh : AnalyticOnNhd ℂ h Set.univ)
    (hgnc : ∃ w₀ w₁ : ℂ, g w₀ ≠ g w₁) (hhnc : ∃ z₀ z₁ : ℂ, h z₀ ≠ h z₁) :
    ∃ z₀ z₁ : ℂ, g (h z₀) ≠ g (h z₁) := by
  by_contra hcon
  have hconst : ∀ z₀ z₁ : ℂ, g (h z₀) = g (h z₁) := by
    intro z₀ z₁
    by_contra hne
    exact hcon ⟨z₀, z₁, hne⟩
  -- the inner function is an open map
  have hopen : IsOpenMap h := by
    rcases hh.is_constant_or_isOpenMap with hc | ho
    · exfalso
      obtain ⟨w, hw⟩ := hc
      obtain ⟨z₀, z₁, hz⟩ := hhnc
      exact hz ((hw z₀).trans (hw z₁).symm)
    · exact ho
  have hUopen : IsOpen (h '' Set.univ) := hopen Set.univ isOpen_univ
  have hmem : h 0 ∈ h '' Set.univ := ⟨0, Set.mem_univ 0, rfl⟩
  -- the outer function is constant on that open set, hence everywhere
  have hev : (fun w => g w - g (h 0)) =ᶠ[nhds (h 0)] 0 := by
    filter_upwards [hUopen.mem_nhds hmem] with w hw
    obtain ⟨z, _, hz⟩ := hw
    simp only [Pi.zero_apply, sub_eq_zero]
    rw [← hz]
    exact hconst z 0
  have hshift : AnalyticOnNhd ℂ (fun w => g w - g (h 0)) Set.univ :=
    hg.sub analyticOnNhd_const
  have heq := hshift.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ (h 0)) hev
  obtain ⟨w₀, w₁, hw⟩ := hgnc
  have h₀ : g w₀ = g (h 0) := by
    have := heq (Set.mem_univ w₀)
    simpa using sub_eq_zero.mp this
  have h₁ : g w₁ = g (h 0) := by
    have := heq (Set.mem_univ w₁)
    simpa using sub_eq_zero.mp this
  exact hw (h₀.trans h₁.symm)

/-- **Every cascade state is non-constant** when every constituent is. -/
theorem exists_ne_entireCascade {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hnc : ∀ i : ℕ, ∃ w₀ w₁ : ℂ, f i w₀ ≠ f i w₁) (n : ℕ) :
    ∃ z₀ z₁ : ℂ, entireCascade f n z₀ ≠ entireCascade f n z₁ := by
  induction n with
  | zero => exact ⟨0, 1, by simp [entireCascade]⟩
  | succ n ih =>
      exact exists_ne_comp (g := f n) (h := entireCascade f n) (hf n)
        (analyticOnNhd_entireCascade hf n) (hnc n) ih

/-! ## The derivative is nowhere locally zero

A non-constant entire function has a derivative that is entire and not identically zero, hence
nowhere locally zero — which is the hypothesis shape the minimum modulus and the codiscrete
selection both consume. -/

/-- **The derivative of a non-constant entire function is nowhere locally zero.** -/
theorem not_eventually_deriv_eq_zero {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    (hnc : ∃ w₀ w₁ : ℂ, g w₀ ≠ g w₁) (a : ℂ) :
    ¬ ∀ᶠ z in nhds a, deriv g z = 0 := by
  intro hcon
  have hderiv : AnalyticOnNhd ℂ (deriv g) Set.univ := hg.deriv
  have hev : deriv g =ᶠ[nhds a] 0 := by
    filter_upwards [hcon] with z hz
    exact hz
  have heq := hderiv.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ a) hev
  have hzero : ∀ z : ℂ, deriv g z = 0 := fun z => heq (Set.mem_univ z)
  have hdiff : Differentiable ℂ g := fun z => (hg z (Set.mem_univ z)).differentiableAt
  obtain ⟨w₀, w₁, hw⟩ := hnc
  exact hw (is_const_of_deriv_eq_zero hdiff hzero w₀ w₁)

/-- **The cascade states' derivatives are nowhere locally zero.** -/
theorem not_eventually_deriv_entireCascade_eq_zero {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hnc : ∀ i : ℕ, ∃ w₀ w₁ : ℂ, f i w₀ ≠ f i w₁) (n : ℕ) (a : ℂ) :
    ¬ ∀ᶠ z in nhds a, deriv (entireCascade f n) z = 0 :=
  not_eventually_deriv_eq_zero (analyticOnNhd_entireCascade hf n)
    (exists_ne_entireCascade hf hnc n) a

/-- **The cascade states are nowhere locally constant.**  The shape the grouped-coefficient and
minimum-modulus arguments consume. -/
theorem not_eventually_entireCascade_eq_const {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hnc : ∀ i : ℕ, ∃ w₀ w₁ : ℂ, f i w₀ ≠ f i w₁) (n : ℕ) (a : ℂ) :
    ¬ ∀ᶠ z in nhds a, entireCascade f n z = entireCascade f n a := by
  obtain ⟨w₀, w₁, hw⟩ := exists_ne_entireCascade hf hnc n
  exact not_eventually_const_of_ne (analyticOnNhd_entireCascade hf n) hw a

/-! ## Higher derivatives along the cascade

Iterating the chain rule expresses every derivative of a state through the constituents' derivatives
at the previous state and the previous state's own derivatives.  The second derivative shows the
pattern: no new transcendental data enters, only further derivatives of the same objects. -/

/-- **The second derivative along the cascade.** -/
theorem deriv2_entireCascade_succ {f : ℕ → ℂ → ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (n : ℕ) (z : ℂ) :
    deriv (deriv (entireCascade f (n + 1))) z
      = deriv (deriv (f n)) (entireCascade f n z) * (deriv (entireCascade f n) z) ^ 2
        + deriv (f n) (entireCascade f n z) * deriv (deriv (entireCascade f n)) z := by
  have hFan : AnalyticOnNhd ℂ (entireCascade f n) Set.univ := analyticOnNhd_entireCascade hf n
  have hfun : deriv (entireCascade f (n + 1))
      = fun w => deriv (f n) (entireCascade f n w) * deriv (entireCascade f n) w := by
    funext w
    exact deriv_entireCascade_succ hf n w
  rw [hfun]
  have hinner : HasDerivAt (entireCascade f n) (deriv (entireCascade f n) z) z :=
    (hFan z (Set.mem_univ z)).differentiableAt.hasDerivAt
  have houter : HasDerivAt (deriv (f n)) (deriv (deriv (f n)) (entireCascade f n z))
      (entireCascade f n z) :=
    (((hf n).deriv) _ (Set.mem_univ _)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun w => deriv (f n) (entireCascade f n w))
      (deriv (deriv (f n)) (entireCascade f n z) * deriv (entireCascade f n) z) z :=
    houter.comp z hinner
  have h2 : HasDerivAt (deriv (entireCascade f n))
      (deriv (deriv (entireCascade f n)) z) z :=
    ((hFan.deriv) z (Set.mem_univ z)).differentiableAt.hasDerivAt
  have hprod : HasDerivAt
      (fun w => deriv (f n) (entireCascade f n w) * deriv (entireCascade f n) w)
      (deriv (deriv (f n)) (entireCascade f n z) * deriv (entireCascade f n) z
          * deriv (entireCascade f n) z
        + deriv (f n) (entireCascade f n z) * deriv (deriv (entireCascade f n)) z) z :=
    h1.mul h2
  rw [hprod.deriv]
  ring

end GaloisForLFunctions.HTGeometry
