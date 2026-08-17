import Mathlib

/-!
# Formal germ composition and inversion: the contact-order layer

Congruences modulo `X^M` are preserved by substitution in either argument, and hence by
compositional inversion of germs tangent to the identity.  This is the "local-germ
composition/inversion layer" needed to state finite-jet shadow theorems unconditionally.
-/

namespace GaloisForLFunctions.FormalGerm

open PowerSeries

noncomputable section

/-! ## Congruences under substitution -/

/-- Substitution of a positive-order germ preserves divisibility by `X^M`. -/
theorem X_pow_dvd_subst {a : ℂ⟦X⟧} (ha : constantCoeff a = 0) {M : ℕ} {D : ℂ⟦X⟧}
    (h : (X : ℂ⟦X⟧) ^ M ∣ D) : (X : ℂ⟦X⟧) ^ M ∣ subst a D := by
  have hsub : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  obtain ⟨E, hE⟩ := h
  have hval : subst a D = a ^ M * subst a E := by
    rw [hE, subst_mul hsub, subst_pow hsub, subst_X hsub]
  rw [hval]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (X_dvd_iff.mpr ha) M) _

/-- Congruent series have congruent substitutions. -/
theorem X_pow_dvd_subst_sub_outer {a : ℂ⟦X⟧} (ha : constantCoeff a = 0) {M : ℕ}
    {P Q : ℂ⟦X⟧} (h : (X : ℂ⟦X⟧) ^ M ∣ (P - Q)) :
    (X : ℂ⟦X⟧) ^ M ∣ (subst a P - subst a Q) := by
  have hsub : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  rw [← subst_sub hsub]
  exact X_pow_dvd_subst ha h

theorem X_pow_dvd_sub_trunc (M : ℕ) (P : ℂ⟦X⟧) :
    (X : ℂ⟦X⟧) ^ M ∣ (P - ((trunc M P : Polynomial ℂ) : ℂ⟦X⟧)) := by
  refine X_pow_dvd_iff.mpr (fun n hn => ?_)
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hn, sub_self]

/-- Congruent substituted germs give congruent substitutions. -/
theorem X_pow_dvd_subst_sub_inner {a b : ℂ⟦X⟧} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) {M : ℕ} (hab : (X : ℂ⟦X⟧) ^ M ∣ (a - b)) (P : ℂ⟦X⟧) :
    (X : ℂ⟦X⟧) ^ M ∣ (subst a P - subst b P) := by
  have hsa : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  have hsb : HasSubst b := HasSubst.of_constantCoeff_zero' hb
  set p : Polynomial ℂ := trunc M P with hp
  have hsplit : P = ((p : Polynomial ℂ) : ℂ⟦X⟧) + (P - ((p : Polynomial ℂ) : ℂ⟦X⟧)) := by ring
  have hpoly : (X : ℂ⟦X⟧) ^ M ∣ (subst a ((p : Polynomial ℂ) : ℂ⟦X⟧)
      - subst b ((p : Polynomial ℂ) : ℂ⟦X⟧)) := by
    rw [subst_coe hsa, subst_coe hsb]
    have hmap : ∀ x : ℂ⟦X⟧, (Polynomial.aeval x) p
        = Polynomial.eval x (p.map (algebraMap ℂ ℂ⟦X⟧)) := by
      intro x
      rw [Polynomial.eval_map, Polynomial.aeval_def]
    rw [hmap, hmap]
    exact dvd_trans hab (Polynomial.sub_dvd_eval_sub a b (p.map (algebraMap ℂ ℂ⟦X⟧)))
  have htail : (X : ℂ⟦X⟧) ^ M ∣ (P - ((p : Polynomial ℂ) : ℂ⟦X⟧)) := X_pow_dvd_sub_trunc M P
  have htaila : (X : ℂ⟦X⟧) ^ M ∣ subst a (P - ((p : Polynomial ℂ) : ℂ⟦X⟧)) :=
    X_pow_dvd_subst ha htail
  have htailb : (X : ℂ⟦X⟧) ^ M ∣ subst b (P - ((p : Polynomial ℂ) : ℂ⟦X⟧)) :=
    X_pow_dvd_subst hb htail
  have hexp : subst a P - subst b P
      = (subst a ((p : Polynomial ℂ) : ℂ⟦X⟧) - subst b ((p : Polynomial ℂ) : ℂ⟦X⟧))
        + (subst a (P - ((p : Polynomial ℂ) : ℂ⟦X⟧))
          - subst b (P - ((p : Polynomial ℂ) : ℂ⟦X⟧))) := by
    conv_lhs => rw [hsplit]
    rw [subst_add hsa, subst_add hsb]
    ring
  rw [hexp]
  exact dvd_add hpoly (dvd_sub htaila htailb)

end

end GaloisForLFunctions.FormalGerm

namespace GaloisForLFunctions.FormalGerm

open PowerSeries

noncomputable section

theorem constantCoeff_subst_eq_zero {a f : ℂ⟦X⟧} (ha : constantCoeff a = 0)
    (hf : constantCoeff f = 0) : constantCoeff (subst a f) = 0 := by
  have h1 : (X : ℂ⟦X⟧) ^ 1 ∣ f := by rw [pow_one]; exact X_dvd_iff.mpr hf
  have h2 := X_pow_dvd_subst ha h1
  rw [pow_one, X_dvd_iff] at h2
  exact h2

/-! ## Compositional inversion of germs tangent to the identity -/

/-- The compositional inverse of a germ with invertible linear coefficient. -/
def tangentInv (f : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  if h : (coeff 1 f) ≠ 0 then @PowerSeries.substInv ℂ _ f (invertibleOfNonzero h) else 0

theorem tangentInv_apply {f : ℂ⟦X⟧} (h : coeff 1 f ≠ 0) :
    tangentInv f = @PowerSeries.substInv ℂ _ f (invertibleOfNonzero h) := dif_pos h

/-- `f ∘ f⁻¹ = X`. -/
theorem subst_tangentInv {f : ℂ⟦X⟧} (h0 : constantCoeff f = 0) (h : coeff 1 f ≠ 0) :
    subst (tangentInv f) f = X := by
  rw [tangentInv_apply h]
  exact @subst_substInv_right ℂ _ f h0 (invertibleOfNonzero h)

/-- `f⁻¹ ∘ f = X`. -/
theorem tangentInv_subst {f : ℂ⟦X⟧} (h0 : constantCoeff f = 0) (h : coeff 1 f ≠ 0) :
    subst f (tangentInv f) = X := by
  rw [tangentInv_apply h]
  exact @subst_substInv_left ℂ _ f h0 (invertibleOfNonzero h)

theorem coeff_one_tangentInv {f : ℂ⟦X⟧} (h : coeff 1 f ≠ 0) :
    coeff 1 (tangentInv f) = (coeff 1 f)⁻¹ := by
  rw [tangentInv_apply h, @coeff_one_substInv ℂ _ f (invertibleOfNonzero h)]
  rfl

theorem constantCoeff_tangentInv {f : ℂ⟦X⟧} (h : coeff 1 f ≠ 0) :
    constantCoeff (tangentInv f) = 0 := by
  rw [tangentInv_apply h]
  exact @constantCoeff_substInv ℂ _ f (invertibleOfNonzero h)

end

end GaloisForLFunctions.FormalGerm

namespace GaloisForLFunctions.FormalGerm

open PowerSeries

noncomputable section

/-- **The contact-order lemma.**  Two germs with invertible linear coefficient that agree to order
`M` have compositional inverses that agree to order `M`. -/
theorem X_pow_dvd_tangentInv_sub {A B : ℂ⟦X⟧} (hA0 : constantCoeff A = 0) (hA1 : coeff 1 A ≠ 0)
    (hB0 : constantCoeff B = 0) (hB1 : coeff 1 B ≠ 0) {M : ℕ}
    (h : (X : ℂ⟦X⟧) ^ M ∣ (A - B)) :
    (X : ℂ⟦X⟧) ^ M ∣ (tangentInv A - tangentInv B) := by
  have hU0 : constantCoeff (tangentInv A) = 0 := constantCoeff_tangentInv hA1
  have hV0 : constantCoeff (tangentInv B) = 0 := constantCoeff_tangentInv hB1
  have hsU : HasSubst (tangentInv A) := HasSubst.of_constantCoeff_zero' hU0
  have hsV : HasSubst (tangentInv B) := HasSubst.of_constantCoeff_zero' hV0
  have hsA : HasSubst A := HasSubst.of_constantCoeff_zero' hA0
  have hAU : subst (tangentInv A) A = X := subst_tangentInv hA0 hA1
  have hBV : subst (tangentInv B) B = X := subst_tangentInv hB0 hB1
  have hUA : subst A (tangentInv A) = X := tangentInv_subst hA0 hA1
  -- `A ∘ V ≡ B ∘ V = X = A ∘ U` modulo `X^M`
  have hEq : subst (tangentInv B) B = subst (tangentInv A) A := by rw [hBV, hAU]
  have h1 : (X : ℂ⟦X⟧) ^ M ∣ (subst (tangentInv B) A - subst (tangentInv A) A) := by
    have h0 := X_pow_dvd_subst_sub_outer hV0 h
    rwa [hEq] at h0
  -- apply `U` to both sides
  have hc1 : constantCoeff (subst (tangentInv B) A) = 0 := constantCoeff_subst_eq_zero hV0 hA0
  have hc2 : constantCoeff (subst (tangentInv A) A) = 0 := constantCoeff_subst_eq_zero hU0 hA0
  have h2 : (X : ℂ⟦X⟧) ^ M ∣
      (subst (subst (tangentInv B) A) (tangentInv A) - subst (subst (tangentInv A) A) (tangentInv A)) :=
    X_pow_dvd_subst_sub_inner hc1 hc2 h1 (tangentInv A)
  have hleft : subst (subst (tangentInv B) A) (tangentInv A) = tangentInv B := by
    rw [← subst_comp_subst_apply hsA hsV, hUA, subst_X hsV]
  have hright : subst (subst (tangentInv A) A) (tangentInv A) = tangentInv A := by
    rw [hAU, X_subst]
  rw [hleft, hright] at h2
  have := dvd_neg.mpr h2
  simpa using this

end

end GaloisForLFunctions.FormalGerm

namespace GaloisForLFunctions.FormalGerm

open PowerSeries

noncomputable section

theorem X_pow_dvd_rescale_sub (lam : ℂ) {M : ℕ} {A B : ℂ⟦X⟧} (h : (X : ℂ⟦X⟧) ^ M ∣ (A - B)) :
    (X : ℂ⟦X⟧) ^ M ∣ (rescale lam A - rescale lam B) := by
  refine X_pow_dvd_iff.mpr (fun n hn => ?_)
  have := (X_pow_dvd_iff.mp h) n hn
  rw [map_sub] at this ⊢
  rw [coeff_rescale, coeff_rescale, ← mul_sub, this, mul_zero]

theorem X_pow_dvd_derivativeFun_sub {M : ℕ} {A B : ℂ⟦X⟧}
    (h : (X : ℂ⟦X⟧) ^ (M + 1) ∣ (A - B)) :
    (X : ℂ⟦X⟧) ^ M ∣ (derivativeFun A - derivativeFun B) := by
  refine X_pow_dvd_iff.mpr (fun n hn => ?_)
  have hcoeff := (X_pow_dvd_iff.mp h) (n + 1) (by omega)
  rw [map_sub] at hcoeff
  rw [map_sub, coeff_derivativeFun, coeff_derivativeFun, ← sub_mul, hcoeff, zero_mul]

theorem constantCoeff_derivativeFun (f : ℂ⟦X⟧) :
    constantCoeff (derivativeFun f) = coeff 1 f := by
  rw [← coeff_zero_eq_constantCoeff, coeff_derivativeFun]
  simp

end

end GaloisForLFunctions.FormalGerm

namespace GaloisForLFunctions.FiniteJetShadow

open PowerSeries GaloisForLFunctions.FormalGerm

noncomputable section

/-! ## The RG map and the exact beta field of a germ -/

/-- The renormalization step map conjugated by the germ `g`: `R_g(t) = g(λ·g⁻¹(t))`. -/
def rgMap (g : ℂ⟦X⟧) (lam : ℂ) : ℂ⟦X⟧ := subst (tangentInv g) (rescale lam g)

/-- The exact local beta field of the germ `g`: `β_g = L·g⁻¹/(g⁻¹)'`. -/
def betaField (g : ℂ⟦X⟧) (L : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.C L * (tangentInv g * (derivativeFun (tangentInv g))⁻¹)

/-- The truncated germ: the Taylor polynomial of `g` through degree `N+1`. -/
def truncGerm (g : ℂ⟦X⟧) (N : ℕ) : Polynomial ℂ := trunc (N + 2) g

theorem constantCoeff_truncGerm {g : ℂ⟦X⟧} (hg0 : constantCoeff g = 0) (N : ℕ) :
    constantCoeff ((truncGerm g N : Polynomial ℂ) : ℂ⟦X⟧) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, truncGerm, coeff_trunc,
    if_pos (by omega), coeff_zero_eq_constantCoeff, hg0]

theorem coeff_one_truncGerm (g : ℂ⟦X⟧) (N : ℕ) :
    coeff 1 ((truncGerm g N : Polynomial ℂ) : ℂ⟦X⟧) = coeff 1 g := by
  rw [Polynomial.coeff_coe, truncGerm, coeff_trunc, if_pos (by omega)]

theorem X_pow_dvd_truncGerm_sub (g : ℂ⟦X⟧) (N : ℕ) :
    (X : ℂ⟦X⟧) ^ (N + 2) ∣ (((truncGerm g N : Polynomial ℂ) : ℂ⟦X⟧) - g) := by
  have h := X_pow_dvd_sub_trunc (N + 2) g
  have hneg := dvd_neg.mpr h
  simpa [truncGerm] using hneg

/-- **The inverse germs agree to order `N+2`.**  This is the contact-order step `(7)`. -/
theorem X_pow_dvd_tangentInv_truncGerm_sub {g : ℂ⟦X⟧} (hg0 : constantCoeff g = 0)
    (hg1 : coeff 1 g ≠ 0) (N : ℕ) :
    (X : ℂ⟦X⟧) ^ (N + 2) ∣ (tangentInv ((truncGerm g N : Polynomial ℂ) : ℂ⟦X⟧) - tangentInv g) := by
  refine X_pow_dvd_tangentInv_sub (constantCoeff_truncGerm hg0 N) ?_ hg0 hg1
    (X_pow_dvd_truncGerm_sub g N)
  rw [coeff_one_truncGerm]
  exact hg1

/-- **Step-map jet agreement `(8)`.** -/
theorem X_pow_dvd_rgMap_truncGerm_sub {g : ℂ⟦X⟧} (hg0 : constantCoeff g = 0)
    (hg1 : coeff 1 g ≠ 0) (lam : ℂ) (N : ℕ) :
    (X : ℂ⟦X⟧) ^ (N + 2) ∣
      (rgMap ((truncGerm g N : Polynomial ℂ) : ℂ⟦X⟧) lam - rgMap g lam) := by
  set p : ℂ⟦X⟧ := ((truncGerm g N : Polynomial ℂ) : ℂ⟦X⟧) with hp
  have hp0 : constantCoeff p = 0 := constantCoeff_truncGerm hg0 N
  have hp1 : coeff 1 p ≠ 0 := by rw [hp, coeff_one_truncGerm]; exact hg1
  have hQ0 : constantCoeff (tangentInv p) = 0 := constantCoeff_tangentInv hp1
  have hK0 : constantCoeff (tangentInv g) = 0 := constantCoeff_tangentInv hg1
  have hstep1 : (X : ℂ⟦X⟧) ^ (N + 2) ∣
      (subst (tangentInv p) (rescale lam p) - subst (tangentInv p) (rescale lam g)) :=
    X_pow_dvd_subst_sub_outer hQ0 (X_pow_dvd_rescale_sub lam (X_pow_dvd_truncGerm_sub g N))
  have hstep2 : (X : ℂ⟦X⟧) ^ (N + 2) ∣
      (subst (tangentInv p) (rescale lam g) - subst (tangentInv g) (rescale lam g)) :=
    X_pow_dvd_subst_sub_inner hQ0 hK0
      (X_pow_dvd_tangentInv_truncGerm_sub hg0 hg1 N) (rescale lam g)
  have hsum := dvd_add hstep1 hstep2
  rw [rgMap, rgMap]
  have hEq : subst (tangentInv p) (rescale lam p) - subst (tangentInv g) (rescale lam g)
      = (subst (tangentInv p) (rescale lam p) - subst (tangentInv p) (rescale lam g))
        + (subst (tangentInv p) (rescale lam g) - subst (tangentInv g) (rescale lam g)) := by
    ring
  rw [hEq]
  exact hsum

/-- **The exact conjugacy `(6)`.**  `R_g ∘ g = λ·g` for every germ `g` with invertible linear
coefficient — in particular for the truncated germ, where `R_g` is the algebraic shadow. -/
theorem subst_rgMap {g : ℂ⟦X⟧} (hg0 : constantCoeff g = 0) (hg1 : coeff 1 g ≠ 0) (lam : ℂ) :
    subst g (rgMap g lam) = rescale lam g := by
  have hsg : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
  have hsi : HasSubst (tangentInv g) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_tangentInv hg1)
  rw [rgMap, subst_comp_subst_apply hsi hsg, tangentInv_subst hg0 hg1, X_subst]

end

end GaloisForLFunctions.FiniteJetShadow

namespace GaloisForLFunctions.FiniteJetShadow

open PowerSeries GaloisForLFunctions.FormalGerm

noncomputable section

theorem coeff_eq_of_X_pow_dvd_sub {M : ℕ} {A B : ℂ⟦X⟧} (h : (X : ℂ⟦X⟧) ^ M ∣ (A - B))
    {n : ℕ} (hn : n < M) : coeff n A = coeff n B := by
  have := (X_pow_dvd_iff.mp h) n hn
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem constantCoeff_derivativeFun_tangentInv {g : ℂ⟦X⟧} (hg1 : coeff 1 g ≠ 0) :
    constantCoeff (derivativeFun (tangentInv g)) ≠ 0 := by
  rw [constantCoeff_derivativeFun, coeff_one_tangentInv hg1]
  exact inv_ne_zero hg1

/-- **Beta-field jet agreement `(9)`.** -/
theorem X_pow_dvd_betaField_truncGerm_sub {g : ℂ⟦X⟧} (hg0 : constantCoeff g = 0)
    (hg1 : coeff 1 g ≠ 0) (L : ℂ) (N : ℕ) :
    (X : ℂ⟦X⟧) ^ (N + 2) ∣
      (betaField ((truncGerm g N : Polynomial ℂ) : ℂ⟦X⟧) L - betaField g L) := by
  set p : ℂ⟦X⟧ := ((truncGerm g N : Polynomial ℂ) : ℂ⟦X⟧) with hp
  have hp1 : coeff 1 p ≠ 0 := by rw [hp, coeff_one_truncGerm]; exact hg1
  set Q : ℂ⟦X⟧ := tangentInv p with hQ
  set K : ℂ⟦X⟧ := tangentInv g with hK
  set u : ℂ⟦X⟧ := derivativeFun Q with hu
  set v : ℂ⟦X⟧ := derivativeFun K with hv
  have hu0 : constantCoeff u ≠ 0 := constantCoeff_derivativeFun_tangentInv hp1
  have hv0 : constantCoeff v ≠ 0 := constantCoeff_derivativeFun_tangentInv hg1
  have huinv : u * u⁻¹ = 1 := PowerSeries.mul_inv_cancel u hu0
  have hvinv : v * v⁻¹ = 1 := PowerSeries.mul_inv_cancel v hv0
  have hQK : (X : ℂ⟦X⟧) ^ (N + 2) ∣ (Q - K) := X_pow_dvd_tangentInv_truncGerm_sub hg0 hg1 N
  have huv : (X : ℂ⟦X⟧) ^ (N + 1) ∣ (u - v) := X_pow_dvd_derivativeFun_sub hQK
  have hXK : (X : ℂ⟦X⟧) ∣ K := X_dvd_iff.mpr (constantCoeff_tangentInv hg1)
  have hnum : (X : ℂ⟦X⟧) ^ (N + 2) ∣ (Q * v - K * u) := by
    have hsplit : Q * v - K * u = (Q - K) * v - K * (u - v) := by ring
    rw [hsplit]
    refine dvd_sub (Dvd.dvd.mul_right hQK v) ?_
    have : (X : ℂ⟦X⟧) ^ (N + 2) = (X : ℂ⟦X⟧) * (X : ℂ⟦X⟧) ^ (N + 1) := by ring
    rw [this]
    exact mul_dvd_mul hXK huv
  have hid : Q * u⁻¹ - K * v⁻¹ = (Q * v - K * u) * (u⁻¹ * v⁻¹) := by
    calc Q * u⁻¹ - K * v⁻¹
        = (Q * u⁻¹) * (v * v⁻¹) - (K * v⁻¹) * (u * u⁻¹) := by rw [huinv, hvinv]; ring
      _ = (Q * v - K * u) * (u⁻¹ * v⁻¹) := by ring
  have hbeta : betaField p L - betaField g L
      = PowerSeries.C L * ((Q * v - K * u) * (u⁻¹ * v⁻¹)) := by
    rw [betaField, betaField, ← hQ, ← hK, ← hu, ← hv, ← mul_sub, hid]
  rw [hbeta]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hnum _) _

end

end GaloisForLFunctions.FiniteJetShadow

namespace GaloisForLFunctions.FiniteJetShadow

open PowerSeries GaloisForLFunctions.FormalGerm

noncomputable section

/-- **The truncated-germ inverse is algebraic.**  `P_N(Q_N) = X` is a nonzero polynomial relation
over `ℂ[X]`, so `Q_N` is algebraic over `ℂ(X)`. -/
theorem isAlgebraic_tangentInv_truncGerm {g : ℂ⟦X⟧} (hg0 : constantCoeff g = 0)
    (hg1 : coeff 1 g ≠ 0) (N : ℕ) :
    IsAlgebraic (Polynomial ℂ) (tangentInv ((truncGerm g N : Polynomial ℂ) : ℂ⟦X⟧)) := by
  set q : Polynomial ℂ := truncGerm g N with hq
  set p : ℂ⟦X⟧ := (q : ℂ⟦X⟧) with hp
  have hp0 : constantCoeff p = 0 := constantCoeff_truncGerm hg0 N
  have hp1 : coeff 1 p ≠ 0 := by rw [hp, coeff_one_truncGerm]; exact hg1
  have hQsub : subst (tangentInv p) p = X := subst_tangentInv hp0 hp1
  have hsQ : HasSubst (tangentInv p) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_tangentInv hp1)
  have haeval : Polynomial.aeval (tangentInv p) q = (X : ℂ⟦X⟧) := by
    rw [← subst_coe hsQ q]
    exact hQsub
  refine ⟨q.map (algebraMap ℂ (Polynomial ℂ)) - Polynomial.C (Polynomial.X), ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (fun r : Polynomial (Polynomial ℂ) => r.coeff 1) hzero
    simp only [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C,
      Polynomial.coeff_zero] at hcoeff
    norm_num at hcoeff
    have hq1 : q.coeff 1 = coeff 1 g := by
      rw [hq, truncGerm, coeff_trunc, if_pos (by omega)]
    rw [hq1] at hcoeff
    exact hg1 hcoeff
  · rw [map_sub, Polynomial.aeval_map_algebraMap, haeval, Polynomial.aeval_C]
    have hX : algebraMap (Polynomial ℂ) ℂ⟦X⟧ (Polynomial.X : Polynomial ℂ) = (X : ℂ⟦X⟧) := by
      rw [PowerSeries.algebraMap_apply']
      simp
    rw [hX, sub_self]

end

end GaloisForLFunctions.FiniteJetShadow

namespace GaloisForLFunctions.FiniteJetShadow

open PowerSeries GaloisForLFunctions.FormalGerm

noncomputable section

/-- **The algebraic shadow theorem.**

For every germ `g` with `g(0) = 0` and invertible linear coefficient, every dilation ratio `lam`,
every branch constant `L` of `log lam`, and every jet order `N`, the Taylor polynomial `p` of `g`
through degree `N+1` is an *algebraic* germ whose induced renormalization map and exact beta field
have the same `(N+1)`-jet as those of `g`, and which satisfies the exact conjugacy
`R_p ∘ p = lam · p`.  Consequently no finite collection of Taylor coefficients of the RG map or of
the beta field can distinguish an algebraically generated flow from a hypertranscendentally
generated one. -/
theorem algebraic_shadow (g : ℂ⟦X⟧) (hg0 : constantCoeff g = 0) (hg1 : coeff 1 g ≠ 0)
    (lam L : ℂ) (N : ℕ) :
    ∃ p : Polynomial ℂ,
      (∀ n ≤ N + 1, coeff n ((p : Polynomial ℂ) : ℂ⟦X⟧) = coeff n g) ∧
      constantCoeff ((p : Polynomial ℂ) : ℂ⟦X⟧) = 0 ∧
      coeff 1 ((p : Polynomial ℂ) : ℂ⟦X⟧) = coeff 1 g ∧
      IsAlgebraic (Polynomial ℂ) (tangentInv ((p : Polynomial ℂ) : ℂ⟦X⟧)) ∧
      subst ((p : Polynomial ℂ) : ℂ⟦X⟧) (rgMap ((p : Polynomial ℂ) : ℂ⟦X⟧) lam)
        = rescale lam ((p : Polynomial ℂ) : ℂ⟦X⟧) ∧
      (∀ n ≤ N + 1, coeff n (rgMap ((p : Polynomial ℂ) : ℂ⟦X⟧) lam) = coeff n (rgMap g lam)) ∧
      (∀ n ≤ N + 1, coeff n (betaField ((p : Polynomial ℂ) : ℂ⟦X⟧) L)
        = coeff n (betaField g L)) := by
  refine ⟨truncGerm g N, ?_, constantCoeff_truncGerm hg0 N, coeff_one_truncGerm g N,
    isAlgebraic_tangentInv_truncGerm hg0 hg1 N, ?_, ?_, ?_⟩
  · intro n hn
    rw [Polynomial.coeff_coe, truncGerm, coeff_trunc, if_pos (by omega)]
  · refine subst_rgMap (constantCoeff_truncGerm hg0 N) ?_ lam
    rw [coeff_one_truncGerm]
    exact hg1
  · intro n hn
    exact coeff_eq_of_X_pow_dvd_sub (X_pow_dvd_rgMap_truncGerm_sub hg0 hg1 lam N) (by omega)
  · intro n hn
    exact coeff_eq_of_X_pow_dvd_sub (X_pow_dvd_betaField_truncGerm_sub hg0 hg1 L N) (by omega)

end

end GaloisForLFunctions.FiniteJetShadow
