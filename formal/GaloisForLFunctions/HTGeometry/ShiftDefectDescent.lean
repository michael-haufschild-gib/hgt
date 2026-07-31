import GaloisForLFunctions.HTGeometry.ShiftTwistDescent
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

/-!
# Descent of a shift defect through a simple transcendental extension

Let `K` carry an automorphism `sigma`, let `E` be a subfield preserved by `sigma`, and let `y` be
transcendental over `E` with

`sigma y = y + c`,   `c` in `E`.

An element of `E(y)` whose `sigma`-defect lies in `E` is severely restricted: its denominator is
twist-fixed, hence trivial, and its numerator is affine in `y`.  Consequently the defect itself
lies in the span of the previously admissible defects together with `c`.

This is the inductive step of a Hölder-style descent run over a base larger than the rational
function field.  Its hypotheses are exactly the two facts that propagate up such a tower:

* `hfix`  — the `sigma`-invariants of `E` are the constants;
* `hdefect` — every `sigma`-defect of `E` lying in the span `T` of admissible inhomogeneities
  already lies in the smaller span `W`.

The conclusion reproduces both statements one level up, which is what makes the tower induct.
-/

open Polynomial

namespace HTGeometry

variable {Cst E K : Type*} [Field Cst] [Field E] [Field K] [Algebra Cst E] [Algebra E K]

/-- A compatible pair of automorphisms transports a polynomial value by the twist. -/
theorem sigma_aeval_eq {sigma : K ≃+* K} {sigmaE : E ≃+* E}
    (hcompat : ∀ a : E, sigma (algebraMap E K a) = algebraMap E K (sigmaE a))
    {y : K} {c : E} (hsy : sigma y = y + algebraMap E K c) (P : E[X]) :
    sigma (aeval y P) = aeval y (shiftTwist sigmaE c P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, shiftTwist_add, hp, hq]
  | monomial n a =>
      have hm : shiftTwist sigmaE c (Polynomial.monomial n a)
          = Polynomial.C (sigmaE a) * (X + Polynomial.C c) ^ n := by
        rw [shiftTwist, Polynomial.map_monomial]
        simp [← Polynomial.C_mul_X_pow_eq_monomial, mul_comp, pow_comp]
      rw [hm]
      simp only [Polynomial.aeval_monomial, map_mul, map_pow, hsy, map_add, Polynomial.aeval_C,
        Polynomial.aeval_X, hcompat]

/-- Transcendence makes polynomial evaluation injective. -/
theorem aeval_injective_of_transcendental {y : K} (htr : Transcendental E y) :
    Function.Injective (fun P : E[X] => aeval y P) := by
  intro P Q h
  by_contra hne
  refine htr ⟨P - Q, sub_ne_zero.mpr hne, ?_⟩
  simp only [map_sub]
  simp only at h
  rw [h, sub_self]

section Step

variable {sigma : K ≃+* K} {sigmaE : E ≃+* E} {y : K} {c : E}

/-- If a nonzero constant multiple of `c` lies in `W`, then so does `c`. -/
private theorem mem_of_scalar_mem {W : Submodule Cst E} {a : Cst} (ha : a ≠ 0)
    (h : algebraMap Cst E a * c ∈ W) : c ∈ W := by
  have hc : c = a⁻¹ • (algebraMap Cst E a * c) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  rw [hc]
  exact W.smul_mem _ h

set_option maxHeartbeats 1600000 in
/-- **One descent step.**  An element of `E(y)` whose `sigma`-defect `w` lies in the admissible
span `T` has trivial denominator and affine numerator, and `w` lies in `W` together with `c`. -/
theorem descentStep [CharZero Cst]
    (hcompat : ∀ a : E, sigma (algebraMap E K a) = algebraMap E K (sigmaE a))
    (hsy : sigma y = y + algebraMap E K c)
    (htr : Transcendental E y)
    {T W : Submodule Cst E}
    (hfix : ∀ u : E, sigmaE u = u → ∃ a : Cst, u = algebraMap Cst E a)
    (hdefect : ∀ u : E, ∀ v ∈ T, sigmaE u - u = v → v ∈ W)
    (hcT : c ∈ T) (hcW : c ∉ W)
    {N D : E[X]} (hD : D.Monic) (hcop : IsCoprime N D)
    {w : E} (hwT : w ∈ T)
    (hdef : sigma (aeval y N / aeval y D) - aeval y N / aeval y D = algebraMap E K w) :
    ∃ a1 : Cst, D = 1 ∧
      N = Polynomial.C (algebraMap Cst E a1) * X + Polynomial.C (N.coeff 0) ∧
      w - algebraMap Cst E a1 * c ∈ W := by
  classical
  have hinj := aeval_injective_of_transcendental (E := E) htr
  have hDne : D ≠ 0 := hD.ne_zero
  have hdK : aeval y D ≠ 0 := fun h => hDne (hinj (by simpa using h))
  have htDm : (shiftTwist sigmaE c D).Monic := shiftTwist_monic hD
  have htdK : aeval y (shiftTwist sigmaE c D) ≠ 0 := fun h =>
    htDm.ne_zero (hinj (by simpa using h))
  -- Clear denominators and use transcendence to get an identity of polynomials.
  have hpoly : shiftTwist sigmaE c N * D = (N + Polynomial.C w * D) * shiftTwist sigmaE c D := by
    apply hinj
    have hsN := sigma_aeval_eq (sigma := sigma) hcompat hsy N
    have hsD := sigma_aeval_eq (sigma := sigma) hcompat hsy D
    have hdiv : sigma (aeval y N / aeval y D)
        = aeval y (shiftTwist sigmaE c N) / aeval y (shiftTwist sigmaE c D) := by
      rw [map_div₀, hsN, hsD]
    rw [hdiv] at hdef
    have hexp : aeval y (shiftTwist sigmaE c N) * aeval y D
        = (aeval y N + algebraMap E K w * aeval y D) * aeval y (shiftTwist sigmaE c D) := by
      field_simp at hdef
      linear_combination hdef
    simpa [map_mul, map_add, Polynomial.aeval_C] using hexp
  obtain ⟨hfixD, hfixN⟩ := shiftTwist_denom_fixed hD hcop hpoly
  -- Step 1: the denominator is trivial.
  have hDone : D = 1 := by
    by_contra hne
    have hdpos : 0 < D.natDegree := by
      rcases Nat.eq_zero_or_pos D.natDegree with h0 | h
      · exfalso
        refine hne ?_
        have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
        have hc1 : D.coeff 0 = 1 := by rw [← h0]; exact hD.coeff_natDegree
        rw [hC, hc1, Polynomial.C_1]
      · exact h
    have hcoeff := defect_coeff_of_shiftTwist_eq hD hfixD rfl hdpos
    have hcast : (D.natDegree : E) * c = algebraMap Cst E (D.natDegree : Cst) * c := by
      rw [map_natCast]
    have hmemT : -((D.natDegree : E) * c) ∈ T := by
      rw [hcast]
      exact T.neg_mem (by simpa [Algebra.smul_def] using T.smul_mem ((D.natDegree : Cst)) hcT)
    have hmemW := hdefect _ _ hmemT hcoeff
    have hmemW' : algebraMap Cst E (D.natDegree : Cst) * c ∈ W := by
      have h := W.neg_mem hmemW
      rw [hcast] at h
      simpa using h
    exact hcW (mem_of_scalar_mem (Nat.cast_ne_zero.mpr (by omega)) hmemW')
  subst hDone
  rw [mul_one] at hfixN
  -- Step 2: the numerator is affine in `y`.
  have hdeg : N.natDegree ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have hm2 : 2 ≤ N.natDegree := hlt
    have hNne : N ≠ 0 := fun h => by simp [h] at hm2
    have hlead : sigmaE N.leadingCoeff = N.leadingCoeff := by
      have h1 : (shiftTwist sigmaE c N).leadingCoeff = sigmaE N.leadingCoeff :=
        shiftTwist_leadingCoeff _ _ _
      have h2 : (shiftTwist sigmaE c N).coeff N.natDegree = sigmaE N.leadingCoeff := by
        rw [← h1, Polynomial.leadingCoeff, shiftTwist_natDegree]
      rw [hfixN, Polynomial.coeff_add, Polynomial.coeff_C] at h2
      have hz : N.natDegree ≠ 0 := by omega
      simp only [hz, if_false, add_zero] at h2
      exact h2.symm
    obtain ⟨a, ha⟩ := hfix _ hlead
    have haNe : a ≠ 0 := by
      intro h
      exact hNne (Polynomial.leadingCoeff_eq_zero.mp (by rw [ha, h, map_zero]))
    have hcoeff := shiftTwist_coeff_sub_one (sigma := sigmaE) (c := c) (P := N) rfl (by omega)
    rw [hfixN, Polynomial.coeff_add, Polynomial.coeff_C] at hcoeff
    have hz1 : N.natDegree - 1 ≠ 0 := by omega
    simp only [hz1, if_false, add_zero] at hcoeff
    have haC : N.coeff N.natDegree = algebraMap Cst E a := ha
    have hL : sigmaE (N.coeff N.natDegree) = N.coeff N.natDegree := hlead
    have hdefeq : sigmaE (N.coeff (N.natDegree - 1)) - N.coeff (N.natDegree - 1)
        = -((N.natDegree : E) * c * N.coeff N.natDegree) := by
      linear_combination -hcoeff - (N.natDegree : E) * c * hL
    have hval : (N.natDegree : E) * c * N.coeff N.natDegree
        = algebraMap Cst E ((N.natDegree : Cst) * a) * c := by
      rw [haC, map_mul, map_natCast]; ring
    have hmemT : -((N.natDegree : E) * c * N.coeff N.natDegree) ∈ T := by
      rw [hval]
      exact T.neg_mem
        (by simpa [Algebra.smul_def] using T.smul_mem ((N.natDegree : Cst) * a) hcT)
    have hmemW := hdefect _ _ hmemT hdefeq
    have hmemW' : algebraMap Cst E ((N.natDegree : Cst) * a) * c ∈ W := by
      have h := W.neg_mem hmemW
      rw [hval] at h
      simpa using h
    exact hcW (mem_of_scalar_mem
      (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) haNe) hmemW')
  -- Step 3: read off the defect from the affine numerator.
  have hNeq : N = Polynomial.C (N.coeff 1) * X + Polynomial.C (N.coeff 0) := by
    ext n
    match n with
    | 0 => simp
    | 1 => simp
    | (k + 2) =>
        have hk : N.natDegree < k + 2 := by omega
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hk]
  have htN : shiftTwist sigmaE c N
      = Polynomial.C (sigmaE (N.coeff 1)) * X
        + Polynomial.C (sigmaE (N.coeff 1) * c + sigmaE (N.coeff 0)) := by
    conv_lhs => rw [hNeq]
    rw [shiftTwist_add, shiftTwist_mul, shiftTwist_C, shiftTwist_C, shiftTwist_X]
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring
  rw [htN] at hfixN
  conv_rhs at hfixN => rw [hNeq]
  have hc1 : sigmaE (N.coeff 1) = N.coeff 1 := by
    have h := congrArg (fun p : E[X] => p.coeff 1) hfixN
    simpa [Polynomial.coeff_C] using h
  have hc0 : sigmaE (N.coeff 1) * c + sigmaE (N.coeff 0) = N.coeff 0 + w := by
    have h := congrArg (fun p : E[X] => p.coeff 0) hfixN
    simpa [Polynomial.coeff_C] using h
  obtain ⟨a1, ha1⟩ := hfix _ hc1
  have hdefeq : sigmaE (N.coeff 0) - N.coeff 0 = w - algebraMap Cst E a1 * c := by
    rw [← ha1]; linear_combination hc0 - c * hc1
  have hmemT : w - algebraMap Cst E a1 * c ∈ T :=
    T.sub_mem hwT (by simpa [Algebra.smul_def] using T.smul_mem a1 hcT)
  have hmemW := hdefect _ _ hmemT hdefeq
  exact ⟨a1, rfl, by rw [← ha1]; exact hNeq, hmemW⟩

/-- The defect lies in the span of the old admissible defects together with `c`.  This is the
`hdefect` hypothesis reproduced one level up the tower. -/
theorem descentStep_defect_mem [CharZero Cst]
    (hcompat : ∀ a : E, sigma (algebraMap E K a) = algebraMap E K (sigmaE a))
    (hsy : sigma y = y + algebraMap E K c)
    (htr : Transcendental E y)
    {T W : Submodule Cst E}
    (hfix : ∀ u : E, sigmaE u = u → ∃ a : Cst, u = algebraMap Cst E a)
    (hdefect : ∀ u : E, ∀ v ∈ T, sigmaE u - u = v → v ∈ W)
    (hcT : c ∈ T) (hcW : c ∉ W)
    {N D : E[X]} (hD : D.Monic) (hcop : IsCoprime N D)
    {w : E} (hwT : w ∈ T)
    (hdef : sigma (aeval y N / aeval y D) - aeval y N / aeval y D = algebraMap E K w) :
    w ∈ W ⊔ Submodule.span Cst {c} := by
  obtain ⟨a1, -, -, hmemW⟩ :=
    descentStep (sigma := sigma) hcompat hsy htr hfix hdefect hcT hcW hD hcop hwT hdef
  have hsplit : w = (w - algebraMap Cst E a1 * c) + a1 • c := by
    rw [Algebra.smul_def]; ring
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hmemW)
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)))

/-- A `sigma`-invariant element of `E(y)` is a constant.  This is the `hfix` hypothesis reproduced
one level up the tower. -/
theorem descentStep_fixed [CharZero Cst]
    (hcompat : ∀ a : E, sigma (algebraMap E K a) = algebraMap E K (sigmaE a))
    (hsy : sigma y = y + algebraMap E K c)
    (htr : Transcendental E y)
    {T W : Submodule Cst E}
    (hfix : ∀ u : E, sigmaE u = u → ∃ a : Cst, u = algebraMap Cst E a)
    (hdefect : ∀ u : E, ∀ v ∈ T, sigmaE u - u = v → v ∈ W)
    (hcT : c ∈ T) (hcW : c ∉ W)
    {N D : E[X]} (hD : D.Monic) (hcop : IsCoprime N D)
    (hdef : sigma (aeval y N / aeval y D) = aeval y N / aeval y D) :
    ∃ a : Cst, aeval y N / aeval y D = algebraMap E K (algebraMap Cst E a) := by
  have hdef0 : sigma (aeval y N / aeval y D) - aeval y N / aeval y D
      = algebraMap E K (0 : E) := by rw [hdef, sub_self, map_zero]
  obtain ⟨a1, hD1, hN, hmemW⟩ :=
    descentStep (sigma := sigma) hcompat hsy htr hfix hdefect hcT hcW hD hcop
      (Submodule.zero_mem T) hdef0
  -- The linear coefficient must vanish, since otherwise `c` would lie in `W`.
  have ha1 : a1 = 0 := by
    by_contra hne
    have hmem : algebraMap Cst E a1 * c ∈ W := by
      have h := W.neg_mem hmemW
      simpa using h
    exact hcW (mem_of_scalar_mem hne hmem)
  subst hD1
  subst ha1
  rw [map_zero, Polynomial.C_0, zero_mul, zero_add] at hN
  have hval : aeval y N / aeval y (1 : E[X]) = algebraMap E K (N.coeff 0) := by
    rw [hN]; simp
  rw [hval] at hdef ⊢
  have hE : sigmaE (N.coeff 0) = N.coeff 0 := by
    have h := hdef
    rw [hcompat] at h
    exact (algebraMap E K).injective h
  obtain ⟨a, ha⟩ := hfix _ hE
  exact ⟨a, by rw [ha]⟩

end Step

end HTGeometry
