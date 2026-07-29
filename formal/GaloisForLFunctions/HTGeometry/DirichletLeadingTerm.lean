import GaloisForLFunctions.HTGeometry.ShiftDefectRationalPole
import Mathlib

/-!
# Leading terms of Dirichlet-type series and shift defects

A ring `D` of Dirichlet series `sum_{m >= 1} A_m(s) m^(-s)` with polynomial coefficients carries a
least index `ord` and a leading coefficient `lead`, both multiplicative, and the shift `s -> s+1`
acts by

`ord (sigma f) = ord f`,   `(ord f) * lead (sigma f) = (lead f)(X + 1)`.

`DirichletLead` axiomatises exactly this behaviour together with the effect of subtraction on the
least index.  From it one extracts the central fact: if `P / Q` has a rational shift defect, then
the ratio of the two leading coefficients is a genuine rational function with the *same* defect.
Combined with the pole obstruction for rational functions this settles both the shift invariants and
the shift defects of the fraction field, with no asymptotic analysis anywhere.
-/

open Polynomial

namespace HTGeometry

/-- Least-index and leading-coefficient data on a ring of Dirichlet-type series. -/
structure DirichletLead (D : Type*) [CommRing D] where
  /-- The shift `s ↦ s + 1`. -/
  sigma : D ≃+* D
  /-- The least index carrying a nonzero coefficient. -/
  ord : D → ℕ
  /-- The coefficient at the least index. -/
  lead : D → ℂ[X]
  /-- Embedding of the index-one part. -/
  emb : ℂ[X] →+* D
  lead_zero : lead 0 = 0
  ord_pos : ∀ {f : D}, f ≠ 0 → 0 < ord f
  lead_ne_zero : ∀ {f : D}, f ≠ 0 → lead f ≠ 0
  ord_mul : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord (f * g) = ord f * ord g
  lead_mul : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → lead (f * g) = lead f * lead g
  sigma_ne_zero : ∀ {f : D}, f ≠ 0 → sigma f ≠ 0
  ord_sigma : ∀ {f : D}, f ≠ 0 → ord (sigma f) = ord f
  lead_sigma : ∀ {f : D}, f ≠ 0 →
    Polynomial.C ((ord f : ℂ)) * lead (sigma f) = (lead f).comp (X + 1)
  /-- Subtraction never lowers the least index. -/
  le_ord_sub : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord f = ord g → f - g ≠ 0 →
    ord f ≤ ord (f - g)
  /-- With no cancellation the leading coefficients subtract. -/
  lead_sub : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord f = ord g → ord (f - g) = ord f →
    lead (f - g) = lead f - lead g
  /-- A strict rise of the index means the leading coefficients agreed. -/
  lead_eq_of_ord_lt : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord f = ord g → ord f < ord (f - g) →
    lead f = lead g
  sigma_emb : ∀ p : ℂ[X], sigma (emb p) = emb (p.comp (X + 1))
  emb_ne_zero : ∀ {p : ℂ[X]}, p ≠ 0 → emb p ≠ 0
  ord_emb : ∀ {p : ℂ[X]}, p ≠ 0 → ord (emb p) = 1
  lead_emb : ∀ {p : ℂ[X]}, p ≠ 0 → lead (emb p) = p

namespace DirichletLead

variable {D : Type*} [CommRing D] (Dat : DirichletLead D)

theorem mul_ne_zero' (Dat : DirichletLead D) {f g : D} (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  intro h
  have hl := Dat.lead_mul hf hg
  rw [h, Dat.lead_zero] at hl
  exact (mul_ne_zero (Dat.lead_ne_zero hf) (Dat.lead_ne_zero hg)) hl.symm

/-- Shifting a polynomial preserves its leading coefficient. -/
theorem leadingCoeff_comp_X_add_one (p : ℂ[X]) :
    (p.comp (X + 1)).leadingCoeff = p.leadingCoeff := by
  have := shiftTwist_leadingCoeff (RingEquiv.refl ℂ) 1 p
  rw [shiftTwist_refl, Polynomial.C_1] at this
  simpa using this

/-- Shifting a polynomial preserves its degree. -/
theorem natDegree_comp_X_add_one (p : ℂ[X]) :
    (p.comp (X + 1)).natDegree = p.natDegree := by
  have := shiftTwist_natDegree (RingEquiv.refl ℂ) 1 p
  rw [shiftTwist_refl, Polynomial.C_1] at this
  simpa using this

/-- If `k * (A(X+1) * B) = l * (A * B(X+1))` with `A`, `B` nonzero, the two scalars agree. -/
theorem nat_eq_of_scaled_shift_eq {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0) {k l : ℕ}
    (h : Polynomial.C ((k : ℂ)) * (A.comp (X + 1) * B)
       = Polynomial.C ((l : ℂ)) * (A * B.comp (X + 1))) :
    (k : ℂ) = (l : ℂ) := by
  have hAs : A.comp (X + 1) ≠ 0 := by
    intro h0
    exact hA (Polynomial.leadingCoeff_eq_zero.mp
      (by rw [← leadingCoeff_comp_X_add_one A, h0, Polynomial.leadingCoeff_zero]))
  have hBs : B.comp (X + 1) ≠ 0 := by
    intro h0
    exact hB (Polynomial.leadingCoeff_eq_zero.mp
      (by rw [← leadingCoeff_comp_X_add_one B, h0, Polynomial.leadingCoeff_zero]))
  have hdegL : (A.comp (X + 1) * B).natDegree = A.natDegree + B.natDegree := by
    rw [Polynomial.natDegree_mul hAs hB, natDegree_comp_X_add_one]
  have hdegR : (A * B.comp (X + 1)).natDegree = A.natDegree + B.natDegree := by
    rw [Polynomial.natDegree_mul hA hBs, natDegree_comp_X_add_one]
  have hcL : (A.comp (X + 1) * B).coeff (A.natDegree + B.natDegree)
      = A.leadingCoeff * B.leadingCoeff := by
    rw [← hdegL, ← Polynomial.leadingCoeff, Polynomial.leadingCoeff_mul,
      leadingCoeff_comp_X_add_one]
  have hcR : (A * B.comp (X + 1)).coeff (A.natDegree + B.natDegree)
      = A.leadingCoeff * B.leadingCoeff := by
    rw [← hdegR, ← Polynomial.leadingCoeff, Polynomial.leadingCoeff_mul,
      leadingCoeff_comp_X_add_one]
  have hco := congrArg (fun p : ℂ[X] => p.coeff (A.natDegree + B.natDegree)) h
  simp only [Polynomial.coeff_C_mul, hcL, hcR] at hco
  have hprod : A.leadingCoeff * B.leadingCoeff ≠ 0 :=
    mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hA) (Polynomial.leadingCoeff_ne_zero.mpr hB)
  exact mul_right_cancel₀ hprod hco

/-- **The indices of numerator and denominator agree.** -/
theorem ord_eq_of_rel
    {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0)
    {rn rd : ℂ[X]} (hrd : rd ≠ 0)
    (hrel : Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb rn * (Dat.sigma Q * Q)) :
    Dat.ord P = Dat.ord Q := by
  classical
  set m0 := Dat.ord P with hm0
  set m1 := Dat.ord Q with hm1
  have hm0pos : 0 < m0 := Dat.ord_pos hP
  have hm1pos : 0 < m1 := Dat.ord_pos hQ
  have hsP : Dat.sigma P ≠ 0 := Dat.sigma_ne_zero hP
  have hsQ : Dat.sigma Q ≠ 0 := Dat.sigma_ne_zero hQ
  have hL1 : Dat.sigma P * Q ≠ 0 := Dat.mul_ne_zero' hsP hQ
  have hL2 : P * Dat.sigma Q ≠ 0 := Dat.mul_ne_zero' hP hsQ
  have hordL1 : Dat.ord (Dat.sigma P * Q) = m0 * m1 := by
    rw [Dat.ord_mul hsP hQ, Dat.ord_sigma hP]
  have hordL2 : Dat.ord (P * Dat.sigma Q) = m0 * m1 := by
    rw [Dat.ord_mul hP hsQ, Dat.ord_sigma hQ]
  have hordeq : Dat.ord (Dat.sigma P * Q) = Dat.ord (P * Dat.sigma Q) := by
    rw [hordL1, hordL2]
  -- the two leading coefficients, scaled
  have hleadL1 : Polynomial.C ((m0 : ℂ)) * Dat.lead (Dat.sigma P * Q)
      = (Dat.lead P).comp (X + 1) * Dat.lead Q := by
    rw [Dat.lead_mul hsP hQ, ← mul_assoc, Dat.lead_sigma hP]
  have hleadL2 : Polynomial.C ((m1 : ℂ)) * Dat.lead (P * Dat.sigma Q)
      = Dat.lead P * (Dat.lead Q).comp (X + 1) := by
    rw [Dat.lead_mul hP hsQ, mul_comm (Dat.lead P) (Dat.lead (Dat.sigma Q)), ← mul_assoc,
      Dat.lead_sigma hQ, mul_comm]
  have hAne : Dat.lead P ≠ 0 := Dat.lead_ne_zero hP
  have hBne : Dat.lead Q ≠ 0 := Dat.lead_ne_zero hQ
  -- cancellation of the two leading terms forces the indices to agree
  have hcancel : Dat.lead (Dat.sigma P * Q) = Dat.lead (P * Dat.sigma Q) → m0 = m1 := by
    intro hc
    have h1 : Polynomial.C ((m1 : ℂ)) * (Polynomial.C ((m0 : ℂ)) * Dat.lead (Dat.sigma P * Q))
        = Polynomial.C ((m0 : ℂ)) * (Polynomial.C ((m1 : ℂ)) * Dat.lead (P * Dat.sigma Q)) := by
      rw [hc]; ring
    rw [hleadL1, hleadL2] at h1
    exact Nat.cast_injective (nat_eq_of_scaled_shift_eq hAne hBne h1).symm
  by_cases hu : Dat.sigma P * Q - P * Dat.sigma Q = 0
  · refine hcancel ?_
    have heq : Dat.sigma P * Q = P * Dat.sigma Q := by
      have := sub_eq_zero.mp hu
      exact this
    rw [heq]
  · have hrdu : Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q) ≠ 0 :=
      Dat.mul_ne_zero' (Dat.emb_ne_zero hrd) hu
    have hrn : rn ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hrel
      exact hrdu hrel
    have hQQ : Dat.sigma Q * Q ≠ 0 := Dat.mul_ne_zero' hsQ hQ
    have hordu : Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) = m1 * m1 := by
      have hl : Dat.ord (Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q))
          = Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) := by
        rw [Dat.ord_mul (Dat.emb_ne_zero hrd) hu, Dat.ord_emb hrd, one_mul]
      have hr : Dat.ord (Dat.emb rn * (Dat.sigma Q * Q)) = m1 * m1 := by
        rw [Dat.ord_mul (Dat.emb_ne_zero hrn) hQQ, Dat.ord_emb hrn, one_mul,
          Dat.ord_mul hsQ hQ, Dat.ord_sigma hQ]
      rw [← hl, hrel, hr]
    have hge : m0 * m1 ≤ m1 * m1 := by
      have := Dat.le_ord_sub hL1 hL2 hordeq hu
      rw [hordL1, hordu] at this
      exact this
    have hle : m0 ≤ m1 := Nat.le_of_mul_le_mul_right hge hm1pos
    rcases lt_or_eq_of_le hle with hlt | heq
    · exfalso
      have hstrict : Dat.ord (Dat.sigma P * Q) < Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) := by
        rw [hordL1, hordu]
        exact Nat.mul_lt_mul_of_lt_of_le hlt (le_refl m1) hm1pos
      exact absurd (hcancel (Dat.lead_eq_of_ord_lt hL1 hL2 hordeq hstrict)) (by omega)
    · exact heq

/-- **The leading coefficients inherit the shift defect.**  If `P / Q` has shift defect `rn / rd`,
then the ratio of leading coefficients is a rational function with the same defect. -/
theorem lead_shift_identity
    {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0)
    {rn rd : ℂ[X]} (hrd : rd ≠ 0)
    (hrel : Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb rn * (Dat.sigma Q * Q)) :
    ((Dat.lead P).comp (X + 1) * Dat.lead Q - Dat.lead P * (Dat.lead Q).comp (X + 1)) * rd
      = rn * ((Dat.lead Q).comp (X + 1) * Dat.lead Q) := by
  classical
  have hordPQ : Dat.ord P = Dat.ord Q := ord_eq_of_rel Dat hP hQ hrd hrel
  set m := Dat.ord Q with hm
  have hmpos : 0 < m := Dat.ord_pos hQ
  have hsP : Dat.sigma P ≠ 0 := Dat.sigma_ne_zero hP
  have hsQ : Dat.sigma Q ≠ 0 := Dat.sigma_ne_zero hQ
  have hL1 : Dat.sigma P * Q ≠ 0 := Dat.mul_ne_zero' hsP hQ
  have hL2 : P * Dat.sigma Q ≠ 0 := Dat.mul_ne_zero' hP hsQ
  have hQQ : Dat.sigma Q * Q ≠ 0 := Dat.mul_ne_zero' hsQ hQ
  have hordL1 : Dat.ord (Dat.sigma P * Q) = m * m := by
    rw [Dat.ord_mul hsP hQ, Dat.ord_sigma hP, hordPQ]
  have hordL2 : Dat.ord (P * Dat.sigma Q) = m * m := by
    rw [Dat.ord_mul hP hsQ, Dat.ord_sigma hQ, hordPQ]
  have hordeq : Dat.ord (Dat.sigma P * Q) = Dat.ord (P * Dat.sigma Q) := by
    rw [hordL1, hordL2]
  have hleadL1 : Polynomial.C ((m : ℂ)) * Dat.lead (Dat.sigma P * Q)
      = (Dat.lead P).comp (X + 1) * Dat.lead Q := by
    have hs := Dat.lead_sigma hP
    rw [hordPQ] at hs
    rw [Dat.lead_mul hsP hQ, ← mul_assoc, hs]
  have hleadL2 : Polynomial.C ((m : ℂ)) * Dat.lead (P * Dat.sigma Q)
      = Dat.lead P * (Dat.lead Q).comp (X + 1) := by
    rw [Dat.lead_mul hP hsQ, mul_comm (Dat.lead P) (Dat.lead (Dat.sigma Q)), ← mul_assoc,
      Dat.lead_sigma hQ, mul_comm]
  have hleadR : Polynomial.C ((m : ℂ)) * Dat.lead (Dat.sigma Q * Q)
      = (Dat.lead Q).comp (X + 1) * Dat.lead Q := by
    rw [Dat.lead_mul hsQ hQ, ← mul_assoc, Dat.lead_sigma hQ]
  by_cases hu : Dat.sigma P * Q - P * Dat.sigma Q = 0
  · have hrn : rn = 0 := by
      by_contra hne
      rw [hu, mul_zero] at hrel
      exact (Dat.mul_ne_zero' (Dat.emb_ne_zero hne) hQQ) hrel.symm
    have hc : Dat.lead (Dat.sigma P * Q) = Dat.lead (P * Dat.sigma Q) := by
      rw [sub_eq_zero.mp hu]
    have hCm : Polynomial.C ((m : ℂ)) ≠ 0 := by
      simpa using (Nat.cast_ne_zero.mpr (by omega) : ((m : ℂ)) ≠ 0)
    have hAB : (Dat.lead P).comp (X + 1) * Dat.lead Q
        = Dat.lead P * (Dat.lead Q).comp (X + 1) := by
      rw [← hleadL1, ← hleadL2, hc]
    rw [hrn, hAB]
    ring
  · have hordu : Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) = m * m := by
      have hrn : rn ≠ 0 := by
        intro h0
        rw [h0, map_zero, zero_mul] at hrel
        exact (Dat.mul_ne_zero' (Dat.emb_ne_zero hrd) hu) hrel
      have hl : Dat.ord (Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q))
          = Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) := by
        rw [Dat.ord_mul (Dat.emb_ne_zero hrd) hu, Dat.ord_emb hrd, one_mul]
      have hr : Dat.ord (Dat.emb rn * (Dat.sigma Q * Q)) = m * m := by
        rw [Dat.ord_mul (Dat.emb_ne_zero hrn) hQQ, Dat.ord_emb hrn, one_mul,
          Dat.ord_mul hsQ hQ, Dat.ord_sigma hQ]
      rw [← hl, hrel, hr]
    have hleadu : Dat.lead (Dat.sigma P * Q - P * Dat.sigma Q)
        = Dat.lead (Dat.sigma P * Q) - Dat.lead (P * Dat.sigma Q) :=
      Dat.lead_sub hL1 hL2 hordeq (by rw [hordu, hordL1])
    have hmain : rd * Dat.lead (Dat.sigma P * Q - P * Dat.sigma Q)
        = rn * Dat.lead (Dat.sigma Q * Q) := by
      have hrn : rn ≠ 0 := by
        intro h0
        rw [h0, map_zero, zero_mul] at hrel
        exact (Dat.mul_ne_zero' (Dat.emb_ne_zero hrd) hu) hrel
      have := congrArg Dat.lead hrel
      rwa [Dat.lead_mul (Dat.emb_ne_zero hrd) hu, Dat.lead_emb hrd,
        Dat.lead_mul (Dat.emb_ne_zero hrn) hQQ, Dat.lead_emb hrn] at this
    have hscaled := congrArg (fun p : ℂ[X] => Polynomial.C ((m : ℂ)) * p) hmain
    calc ((Dat.lead P).comp (X + 1) * Dat.lead Q
            - Dat.lead P * (Dat.lead Q).comp (X + 1)) * rd
        = rd * (Polynomial.C ((m : ℂ)) *
            (Dat.lead (Dat.sigma P * Q) - Dat.lead (P * Dat.sigma Q))) := by
          rw [mul_sub, hleadL1, hleadL2]; ring
      _ = rn * (Polynomial.C ((m : ℂ)) * Dat.lead (Dat.sigma Q * Q)) := by
          rw [← hleadu]; linear_combination hscaled
      _ = rn * ((Dat.lead Q).comp (X + 1) * Dat.lead Q) := by rw [hleadR]

/-- **Transport of the leading-term interface along an injective ring homomorphism.**  If `phi`
embeds `D` into a ring carrying the interface, intertwining the shifts and the index-one
embeddings, then `D` inherits it. -/
noncomputable def comap {D E : Type*} [CommRing D] [CommRing E] (Dat : DirichletLead E)
    (phi : D →+* E) (hinj : Function.Injective phi)
    (sigmaD : D ≃+* D) (hsig : ∀ x, phi (sigmaD x) = Dat.sigma (phi x))
    (embD : ℂ[X] →+* D) (hemb : ∀ p, phi (embD p) = Dat.emb p) : DirichletLead D where
  sigma := sigmaD
  ord x := Dat.ord (phi x)
  lead x := Dat.lead (phi x)
  emb := embD
  lead_zero := by simpa using Dat.lead_zero
  ord_pos hf := Dat.ord_pos (fun h => hf (hinj (by simpa using h)))
  lead_ne_zero hf := Dat.lead_ne_zero (fun h => hf (hinj (by simpa using h)))
  ord_mul hf hg := by
    rw [map_mul]
    exact Dat.ord_mul (fun h => hf (hinj (by simpa using h)))
      (fun h => hg (hinj (by simpa using h)))
  lead_mul hf hg := by
    rw [map_mul]
    exact Dat.lead_mul (fun h => hf (hinj (by simpa using h)))
      (fun h => hg (hinj (by simpa using h)))
  sigma_ne_zero hf h := hf (sigmaD.injective (by simpa using h))
  ord_sigma hf := by
    rw [hsig]
    exact Dat.ord_sigma (fun h => hf (hinj (by simpa using h)))
  lead_sigma hf := by
    rw [hsig]
    exact Dat.lead_sigma (fun h => hf (hinj (by simpa using h)))
  le_ord_sub hf hg hord hsub := by
    rw [map_sub]
    exact Dat.le_ord_sub (fun h => hf (hinj (by simpa using h)))
      (fun h => hg (hinj (by simpa using h))) hord
      (fun h => hsub (hinj (by simpa [map_sub] using h)))
  lead_sub hf hg hord hsubord := by
    rw [map_sub] at hsubord ⊢
    exact Dat.lead_sub (fun h => hf (hinj (by simpa using h)))
      (fun h => hg (hinj (by simpa using h))) hord hsubord
  lead_eq_of_ord_lt hf hg hord hlt := by
    rw [map_sub] at hlt
    exact Dat.lead_eq_of_ord_lt (fun h => hf (hinj (by simpa using h)))
      (fun h => hg (hinj (by simpa using h))) hord hlt
  sigma_emb p := by
    apply hinj
    rw [hsig, hemb, hemb, Dat.sigma_emb]
  emb_ne_zero hp h := Dat.emb_ne_zero hp (by rw [← hemb]; simpa using congrArg phi h)
  ord_emb hp := by rw [hemb]; exact Dat.ord_emb hp
  lead_emb hp := by rw [hemb]; exact Dat.lead_emb hp

end DirichletLead

/-- Normalise a shift-defect identity to a coprime pair with monic denominator. -/
theorem exists_coprime_monic_shift_identity {A B rn rd : ℂ[X]} (_hA : A ≠ 0) (hB : B ≠ 0)
    (h : (A.comp (X + 1) * B - A * B.comp (X + 1)) * rd = rn * (B.comp (X + 1) * B)) :
    ∃ A' B' : ℂ[X], B'.Monic ∧ IsCoprime A' B' ∧
      (A'.comp (X + 1) * B' - A' * B'.comp (X + 1)) * rd = rn * (B'.comp (X + 1) * B') := by
  classical
  set g : ℂ[X] := GCDMonoid.gcd A B with hg
  have hgne : g ≠ 0 := gcd_ne_zero_of_right hB
  set A1 : ℂ[X] := A / g with hA1
  set B1 : ℂ[X] := B / g with hB1
  have hcop1 : IsCoprime A1 B1 := isCoprime_div_gcd_div_gcd hB
  have hAg : A1 * g = A := by
    rw [hA1, mul_comm]; exact EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left A B)
  have hBg : B1 * g = B := by
    rw [hB1, mul_comm]; exact EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right A B)
  have hB1ne : B1 ≠ 0 := fun h0 => hB (by rw [← hBg, h0, zero_mul])
  have hgs : g.comp (X + 1) ≠ 0 := by
    intro h0
    exact hgne (Polynomial.leadingCoeff_eq_zero.mp
      (by rw [← DirichletLead.leadingCoeff_comp_X_add_one g, h0, Polynomial.leadingCoeff_zero]))
  -- cancel the common factor
  have hid1 : (A1.comp (X + 1) * B1 - A1 * B1.comp (X + 1)) * rd
      = rn * (B1.comp (X + 1) * B1) := by
    refine mul_left_cancel₀ (mul_ne_zero hgne hgs) ?_
    rw [← hAg, ← hBg] at h
    simp only [Polynomial.mul_comp] at h
    linear_combination h
  -- scale the denominator to be monic
  set u : ℂ := (B1.leadingCoeff)⁻¹ with hu
  have hlead : B1.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB1ne
  have hune : u ≠ 0 := inv_ne_zero hlead
  refine ⟨A1 * Polynomial.C u, B1 * Polynomial.C u, ?_, ?_, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hu,
      mul_inv_cancel₀ hlead]
  · obtain ⟨p, q, hpq⟩ := hcop1
    refine ⟨p * Polynomial.C u⁻¹, q * Polynomial.C u⁻¹, ?_⟩
    have hCu : (Polynomial.C u⁻¹) * (Polynomial.C u) = (1 : ℂ[X]) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hune, Polynomial.C_1]
    calc p * Polynomial.C u⁻¹ * (A1 * Polynomial.C u)
          + q * Polynomial.C u⁻¹ * (B1 * Polynomial.C u)
        = (p * A1 + q * B1) * (Polynomial.C u⁻¹ * Polynomial.C u) := by ring
      _ = 1 := by rw [hCu, hpq, mul_one]
  · simp only [Polynomial.mul_comp, Polynomial.C_comp]
    linear_combination (Polynomial.C u * Polynomial.C u) * hid1

/-- **No shift defect with a single pole.**  If `P / Q` in the fraction field of a Dirichlet-lead
ring has shift defect `q / X ^ m` with `q` nonzero of degree below `m`, a contradiction follows. -/
theorem DirichletLead.no_pole_defect {D : Type*} [CommRing D] (Dat : DirichletLead D)
    {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0) {q : ℂ[X]} {m : ℕ}
    (hq : q ≠ 0) (hqdeg : q.natDegree < m)
    (hrel : Dat.emb (X ^ m) * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb q * (Dat.sigma Q * Q)) :
    False := by
  have hXm : (X : ℂ[X]) ^ m ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hid := Dat.lead_shift_identity hP hQ hXm hrel
  obtain ⟨A', B', hmon, hcop, hid'⟩ :=
    exists_coprime_monic_shift_identity (Dat.lead_ne_zero hP) (Dat.lead_ne_zero hQ) hid
  exact no_rational_shift_antiderivative hmon hcop hq hqdeg hid'

/-- A shift-invariant ratio of polynomials is a constant multiple. -/
theorem eq_const_mul_of_shift_ratio_fixed {A B : ℂ[X]} (hB : B ≠ 0)
    (h : A.comp (X + 1) * B = A * B.comp (X + 1)) :
    ∃ a : ℂ, A = Polynomial.C a * B := by
  classical
  rcases eq_or_ne A 0 with rfl | hA
  · exact ⟨0, by simp⟩
  set g : ℂ[X] := GCDMonoid.gcd A B with hg
  have hgne : g ≠ 0 := gcd_ne_zero_of_right hB
  set A1 : ℂ[X] := A / g with hA1
  set B1 : ℂ[X] := B / g with hB1
  have hcop1 : IsCoprime A1 B1 := isCoprime_div_gcd_div_gcd hB
  have hAg : A1 * g = A := by
    rw [hA1, mul_comm]; exact EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left A B)
  have hBg : B1 * g = B := by
    rw [hB1, mul_comm]; exact EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right A B)
  have hB1ne : B1 ≠ 0 := fun h0 => hB (by rw [← hBg, h0, zero_mul])
  have hgs : g.comp (X + 1) ≠ 0 := by
    intro h0
    exact hgne (Polynomial.leadingCoeff_eq_zero.mp
      (by rw [← DirichletLead.leadingCoeff_comp_X_add_one g, h0, Polynomial.leadingCoeff_zero]))
  have hid1 : A1.comp (X + 1) * B1 = A1 * B1.comp (X + 1) := by
    refine mul_left_cancel₀ (mul_ne_zero hgne hgs) ?_
    rw [← hAg, ← hBg] at h
    simp only [Polynomial.mul_comp] at h
    linear_combination h
  set u : ℂ := (B1.leadingCoeff)⁻¹ with hu
  have hlead : B1.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB1ne
  have hune : u ≠ 0 := inv_ne_zero hlead
  have hmon : (B1 * Polynomial.C u).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hu,
      mul_inv_cancel₀ hlead]
  have hcop2 : IsCoprime (A1 * Polynomial.C u) (B1 * Polynomial.C u) := by
    obtain ⟨p, q, hpq⟩ := hcop1
    refine ⟨p * Polynomial.C u⁻¹, q * Polynomial.C u⁻¹, ?_⟩
    have hCu : (Polynomial.C u⁻¹) * (Polynomial.C u) = (1 : ℂ[X]) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hune, Polynomial.C_1]
    calc p * Polynomial.C u⁻¹ * (A1 * Polynomial.C u)
          + q * Polynomial.C u⁻¹ * (B1 * Polynomial.C u)
        = (p * A1 + q * B1) * (Polynomial.C u⁻¹ * Polynomial.C u) := by ring
      _ = 1 := by rw [hCu, hpq, mul_one]
  have hid2 : (A1 * Polynomial.C u).comp (X + 1) * (B1 * Polynomial.C u)
      = (A1 * Polynomial.C u) * (B1 * Polynomial.C u).comp (X + 1) := by
    simp only [Polynomial.mul_comp, Polynomial.C_comp]
    linear_combination (Polynomial.C u * Polynomial.C u) * hid1
  obtain ⟨hB2, hA2⟩ := shift_invariant_rational_constant hmon hcop2 hid2
  have hB1u : B1 = Polynomial.C u⁻¹ := by
    calc B1 = B1 * Polynomial.C u * Polynomial.C u⁻¹ := by
              rw [mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hune, Polynomial.C_1, mul_one]
      _ = Polynomial.C u⁻¹ := by rw [hB2, one_mul]
  have hA1C : A1 * Polynomial.C u = Polynomial.C ((A1 * Polynomial.C u).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hA2
  refine ⟨(A1 * Polynomial.C u).coeff 0, ?_⟩
  have hgB : g = Polynomial.C u * B := by
    rw [← hBg, hB1u, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hune,
      Polynomial.C_1, one_mul]
  calc A = A1 * g := hAg.symm
    _ = (A1 * Polynomial.C u) * B := by rw [hgB]; ring
    _ = Polynomial.C ((A1 * Polynomial.C u).coeff 0) * B := by conv_lhs => rw [hA1C]

/-- **Shift invariants of the fraction field are constants.**  If `sigma P * Q = P * sigma Q`,
then `P` is a constant multiple of `Q`. -/
theorem DirichletLead.eq_const_mul_of_sigma_fixed {D : Type*} [CommRing D]
    (Dat : DirichletLead D) {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : Dat.sigma P * Q = P * Dat.sigma Q) :
    ∃ a : ℂ, P = Dat.emb (Polynomial.C a) * Q := by
  classical
  have hrel' : Dat.emb (1 : ℂ[X]) * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb (0 : ℂ[X]) * (Dat.sigma Q * Q) := by
    rw [sub_eq_zero.mpr hrel, map_zero, mul_zero, zero_mul]
  have hid := Dat.lead_shift_identity hP hQ one_ne_zero hrel'
  rw [mul_one, zero_mul] at hid
  have hAB : (Dat.lead P).comp (X + 1) * Dat.lead Q
      = Dat.lead P * (Dat.lead Q).comp (X + 1) := by
    linear_combination hid
  obtain ⟨a, ha⟩ := eq_const_mul_of_shift_ratio_fixed (Dat.lead_ne_zero hQ) hAB
  have hane : a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at ha
    exact Dat.lead_ne_zero hP ha
  have hCa : (Polynomial.C a : ℂ[X]) ≠ 0 := by
    simpa using hane
  set e : D := Dat.emb (Polynomial.C a) with he
  have hene : e ≠ 0 := Dat.emb_ne_zero hCa
  have hse : Dat.sigma e = e := by
    rw [he, Dat.sigma_emb, Polynomial.C_comp]
  have heQ : e * Q ≠ 0 := Dat.mul_ne_zero' hene hQ
  have hordP : Dat.ord P = Dat.ord Q := ord_eq_of_rel Dat hP hQ one_ne_zero hrel'
  have hordeQ : Dat.ord (e * Q) = Dat.ord P := by
    rw [Dat.ord_mul hene hQ, Dat.ord_emb hCa, one_mul, hordP]
  have hleadeQ : Dat.lead (e * Q) = Dat.lead P := by
    rw [Dat.lead_mul hene hQ, Dat.lead_emb hCa, ha]
  refine ⟨a, ?_⟩
  by_contra hne
  set R : D := P - e * Q with hR
  have hRne : R ≠ 0 := fun h0 => hne (by
    have := sub_eq_zero.mp h0
    exact this)
  -- `R` has the same shift relation
  have hrelR : Dat.emb (1 : ℂ[X]) * (Dat.sigma R * Q - R * Dat.sigma Q)
      = Dat.emb (0 : ℂ[X]) * (Dat.sigma Q * Q) := by
    have hsR : Dat.sigma R = Dat.sigma P - e * Dat.sigma Q := by
      rw [hR, map_sub, map_mul, hse]
    rw [map_zero, zero_mul, hsR]
    have : (Dat.sigma P - e * Dat.sigma Q) * Q - (P - e * Q) * Dat.sigma Q
        = Dat.sigma P * Q - P * Dat.sigma Q := by ring
    rw [this, sub_eq_zero.mpr hrel, mul_zero]
  have hordR : Dat.ord R = Dat.ord Q := ord_eq_of_rel Dat hRne hQ one_ne_zero hrelR
  have hleadR : Dat.lead R = Dat.lead P - Dat.lead (e * Q) :=
    Dat.lead_sub hP heQ hordeQ.symm (by rw [← hR, hordR, hordP])
  rw [hleadeQ, sub_self] at hleadR
  exact Dat.lead_ne_zero hRne hleadR

/-- **A shift-invariant ratio has constant leading quotient.** -/
theorem DirichletLead.lead_ratio_const_of_fixed {D : Type*} [CommRing D] (Dat : DirichletLead D)
    {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hrel : Dat.sigma P * Q = P * Dat.sigma Q) :
    ∃ A' B' : ℂ[X], B' = 1 ∧ A'.natDegree = 0 ∧
      (A'.comp (X + 1) * B' - A' * B'.comp (X + 1)) = 0 := by
  have hrel' : Dat.emb (1 : ℂ[X]) * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb (0 : ℂ[X]) * (Dat.sigma Q * Q) := by
    rw [sub_eq_zero.mpr hrel, map_zero, mul_zero, zero_mul]
  have hid := Dat.lead_shift_identity hP hQ one_ne_zero hrel'
  rw [mul_one, zero_mul] at hid
  obtain ⟨A', B', hmon, hcop, hid'⟩ :=
    exists_coprime_monic_shift_identity (Dat.lead_ne_zero hP) (Dat.lead_ne_zero hQ)
      (by rw [mul_one, zero_mul]; exact hid)
  rw [mul_one, zero_mul] at hid'
  obtain ⟨hB1, hA0⟩ := shift_invariant_rational_constant hmon hcop (by
    linear_combination hid')
  exact ⟨A', B', hB1, hA0, by linear_combination hid'⟩

end HTGeometry
