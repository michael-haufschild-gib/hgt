import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-!
# The shift-twisted translation operator on a polynomial ring

Let `E` be a field carrying an automorphism `sigma`, and let `c` be an element of `E`.  The operator

`shiftTwist sigma c P = (P.map sigma).comp (X + C c)`

is the ring endomorphism of `E[X]` which applies `sigma` to the coefficients and translates the
variable by `c`.  It is the algebraic shadow of a difference operator acting on a polynomial
relation: if `sigma` is a shift of the argument and `y` is a function with `sigma y = y + c`, then
applying `sigma` to the identity `P(y) = 0` produces `(shiftTwist sigma c P)(y) = 0`.

The file records that `shiftTwist` preserves degree, monicity and coprimality, computes its effect
on the subleading coefficient of a monic polynomial, and derives the rigidity consequences used by a
descent: a monic polynomial fixed by `shiftTwist` has a subleading coefficient whose `sigma`-defect
is `-(deg) * c`, and a fraction whose `shiftTwist`-defect lies in the base field has a
`shiftTwist`-fixed denominator.
-/

open Polynomial

namespace HTGeometry

variable {E : Type*} [Field E]

/-- Apply `sigma` to the coefficients of `P` and translate the variable by `c`. -/
noncomputable def shiftTwist (sigma : E ≃+* E) (c : E) (P : E[X]) : E[X] :=
  (P.map (sigma : E →+* E)).comp (X + C c)

theorem shiftTwist_def (sigma : E ≃+* E) (c : E) (P : E[X]) :
    shiftTwist sigma c P = (P.map (sigma : E →+* E)).comp (X + C c) := rfl

@[simp] theorem shiftTwist_zero (sigma : E ≃+* E) (c : E) :
    shiftTwist sigma c 0 = 0 := by simp [shiftTwist]

@[simp] theorem shiftTwist_one (sigma : E ≃+* E) (c : E) :
    shiftTwist sigma c 1 = 1 := by simp [shiftTwist]

theorem shiftTwist_add (sigma : E ≃+* E) (c : E) (P Q : E[X]) :
    shiftTwist sigma c (P + Q) = shiftTwist sigma c P + shiftTwist sigma c Q := by
  simp [shiftTwist, Polynomial.map_add, add_comp]

theorem shiftTwist_mul (sigma : E ≃+* E) (c : E) (P Q : E[X]) :
    shiftTwist sigma c (P * Q) = shiftTwist sigma c P * shiftTwist sigma c Q := by
  simp [shiftTwist, Polynomial.map_mul, mul_comp]

@[simp] theorem shiftTwist_C (sigma : E ≃+* E) (c a : E) :
    shiftTwist sigma c (C a) = C (sigma a) := by
  simp [shiftTwist]

/-- `shiftTwist` as a ring homomorphism. -/
noncomputable def shiftTwistHom (sigma : E ≃+* E) (c : E) : E[X] →+* E[X] where
  toFun := shiftTwist sigma c
  map_one' := shiftTwist_one sigma c
  map_mul' := shiftTwist_mul sigma c
  map_zero' := shiftTwist_zero sigma c
  map_add' := shiftTwist_add sigma c

@[simp] theorem shiftTwistHom_apply (sigma : E ≃+* E) (c : E) (P : E[X]) :
    shiftTwistHom sigma c P = shiftTwist sigma c P := rfl

/-- Translating the variable does not change the degree. -/
theorem shiftTwist_natDegree (sigma : E ≃+* E) (c : E) (P : E[X]) :
    (shiftTwist sigma c P).natDegree = P.natDegree := by
  rw [shiftTwist, ← Polynomial.taylor_apply, Polynomial.natDegree_taylor,
    Polynomial.natDegree_map_eq_of_injective (sigma : E →+* E).injective]

/-- The leading coefficient is transported by `sigma`; in particular monicity is preserved. -/
theorem shiftTwist_monic {sigma : E ≃+* E} {c : E} {P : E[X]} (hP : P.Monic) :
    (shiftTwist sigma c P).Monic := by
  have hmap : (P.map (sigma : E →+* E)).Monic := hP.map _
  exact hmap.comp (Polynomial.monic_X_add_C c) (by simp)

/-- A ring homomorphism preserves coprimality. -/
theorem isCoprime_shiftTwist {sigma : E ≃+* E} {c : E} {N D : E[X]} (h : IsCoprime N D) :
    IsCoprime (shiftTwist sigma c N) (shiftTwist sigma c D) := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨shiftTwist sigma c a, shiftTwist sigma c b, by
    rw [← shiftTwist_mul, ← shiftTwist_mul, ← shiftTwist_add, hab, shiftTwist_one]⟩

/-- **Subleading coefficient under the twist.**  For a monic `P` of degree `d > 0`, translating the
variable by `c` adds `d * c` to the `sigma`-image of the subleading coefficient. -/
theorem shiftTwist_coeff_sub_one {sigma : E ≃+* E} {c : E} {P : E[X]}
    {d : ℕ} (hd : P.natDegree = d) (hdpos : 0 < d) :
    (shiftTwist sigma c P).coeff (d - 1)
      = sigma (P.coeff (d - 1)) + (d : E) * c * sigma (P.coeff d) := by
  set f : E[X] := P.map (sigma : E →+* E) with hf
  have hfd : f.natDegree = d := by
    rw [hf, Polynomial.natDegree_map_eq_of_injective (sigma : E →+* E).injective, hd]
  have hkey : (shiftTwist sigma c P).coeff (d - 1)
      = (Polynomial.hasseDeriv (d - 1) f).eval c := by
    rw [shiftTwist, ← hf, ← Polynomial.taylor_apply, Polynomial.taylor_coeff]
  rw [hkey]
  -- `hasseDeriv (d-1) f` has degree at most one; compute its two coefficients.
  set g : E[X] := Polynomial.hasseDeriv (d - 1) f with hg
  have hg0 : g.coeff 0 = f.coeff (d - 1) := by
    rw [hg, Polynomial.hasseDeriv_coeff]
    simp
  have hg1 : g.coeff 1 = (d : E) * sigma (P.coeff d) := by
    rw [hg, Polynomial.hasseDeriv_coeff]
    have h1 : 1 + (d - 1) = d := by omega
    rw [h1]
    have hcf : f.coeff d = sigma (P.coeff d) := by
      rw [hf, Polynomial.coeff_map]; rfl
    rw [hcf]
    have hchoose : d.choose (d - 1) = d := by
      have hsymm := Nat.choose_symm (show d - 1 ≤ d by omega)
      have h2 : d - (d - 1) = 1 := by omega
      rw [h2] at hsymm
      rw [← hsymm, Nat.choose_one_right]
    rw [hchoose]
  have hgdeg : g.natDegree ≤ 1 := by
    have h := Polynomial.natDegree_hasseDeriv_le f (d - 1)
    rw [← hg, hfd] at h
    omega
  have heval : g.eval c = g.coeff 0 + g.coeff 1 * c := by
    have hg2 : ∀ n, 2 ≤ n → g.coeff n = 0 := fun n hn =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    simp [Finset.sum_range_succ]
  rw [heval, hg0, hg1]
  have hcf1 : f.coeff (d - 1) = sigma (P.coeff (d - 1)) := by
    rw [hf, Polynomial.coeff_map]; rfl
  rw [hcf1]
  ring

/-- Monic specialisation: the twist adds exactly `d * c` to the subleading coefficient. -/
theorem shiftTwist_coeff_sub_one_monic {sigma : E ≃+* E} {c : E} {P : E[X]} (hP : P.Monic)
    {d : ℕ} (hd : P.natDegree = d) (hdpos : 0 < d) :
    (shiftTwist sigma c P).coeff (d - 1) = sigma (P.coeff (d - 1)) + (d : E) * c := by
  have hcd : P.coeff d = 1 := by rw [← hd]; exact hP.coeff_natDegree
  rw [shiftTwist_coeff_sub_one hd hdpos, hcd]
  simp

@[simp] theorem shiftTwist_X (sigma : E ≃+* E) (c : E) :
    shiftTwist sigma c (X : E[X]) = X + C c := by
  simp [shiftTwist]

/-- With the identity automorphism the twist is plain translation of the variable. -/
@[simp] theorem shiftTwist_refl (c : E) (P : E[X]) :
    shiftTwist (RingEquiv.refl E) c P = P.comp (X + C c) := by
  rw [shiftTwist]
  congr 1
  simp

/-- The twist transports the leading coefficient by `sigma`. -/
theorem shiftTwist_leadingCoeff (sigma : E ≃+* E) (c : E) (P : E[X]) :
    (shiftTwist sigma c P).leadingCoeff = sigma P.leadingCoeff := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  rw [shiftTwist, Polynomial.leadingCoeff_comp (by simp), Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
  · simp [Polynomial.monic_X_add_C c]
  · simpa using fun h => hP (Polynomial.leadingCoeff_eq_zero.mp h)

/-- **Rigidity of a twist-fixed monic polynomial.**  If a monic `D` of degree `d` satisfies
`shiftTwist sigma c D = D`, then its subleading coefficient has `sigma`-defect `-(d * c)`. -/
theorem defect_coeff_of_shiftTwist_eq {sigma : E ≃+* E} {c : E} {D : E[X]} (hD : D.Monic)
    (hfix : shiftTwist sigma c D = D) {d : ℕ} (hd : D.natDegree = d) (hdpos : 0 < d) :
    sigma (D.coeff (d - 1)) - D.coeff (d - 1) = -((d : E) * c) := by
  have := shiftTwist_coeff_sub_one_monic (sigma := sigma) (c := c) hD hd hdpos
  rw [hfix] at this
  linear_combination -this

/-- **The denominator is twist-fixed.**  If `N / D` is in lowest terms with `D` monic, and the
twist changes it by an element `w` of the base field, then the twist fixes `D` and moves `N` by
`w * D`.

This is the exact algebraic content of "a `sigma`-defect lying in the base field cannot see the
denominator": it is what lets a descent stay inside the polynomial ring. -/
theorem shiftTwist_denom_fixed {sigma : E ≃+* E} {c w : E} {N D : E[X]}
    (hD : D.Monic) (hcop : IsCoprime N D)
    (hrel : shiftTwist sigma c N * D = (N + C w * D) * shiftTwist sigma c D) :
    shiftTwist sigma c D = D ∧ shiftTwist sigma c N = N + C w * D := by
  have hDne : D ≠ 0 := hD.ne_zero
  have htD : (shiftTwist sigma c D).Monic := shiftTwist_monic hD
  have htDne : shiftTwist sigma c D ≠ 0 := htD.ne_zero
  -- `shiftTwist D` divides `shiftTwist N * D`, and is coprime to `shiftTwist N`.
  have hcop' : IsCoprime (shiftTwist sigma c N) (shiftTwist sigma c D) := isCoprime_shiftTwist hcop
  have h1 : shiftTwist sigma c D ∣ D := by
    have hdvd : shiftTwist sigma c D ∣ shiftTwist sigma c N * D := ⟨N + C w * D, by linear_combination hrel⟩
    exact (hcop'.symm.dvd_of_dvd_mul_left hdvd)
  -- Conversely `D` divides `shiftTwist D * N`, and is coprime to `N`.
  have h2 : D ∣ shiftTwist sigma c D := by
    have hdvd : D ∣ shiftTwist sigma c D * N := by
      refine ⟨shiftTwist sigma c N - C w * shiftTwist sigma c D, ?_⟩
      linear_combination -hrel
    exact (hcop.symm.dvd_of_dvd_mul_right hdvd)
  have hfix : shiftTwist sigma c D = D :=
    Polynomial.eq_of_monic_of_associated htD hD (associated_of_dvd_dvd h1 h2)
  refine ⟨hfix, ?_⟩
  rw [hfix] at hrel
  exact mul_right_cancel₀ hDne hrel

end HTGeometry
