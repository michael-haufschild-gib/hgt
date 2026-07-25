import GaloisForLFunctions.HTGeometry.RelativeShiftJetTower
import Mathlib

/-!
# Leading-term inertness over an arbitrary field of invariants

The graded shift ring of `GradedShiftInertness` with the coefficient field of the leading terms left
free.  When the ambient difference field carries shift-invariant elements beyond the scalars -- a
field `C` of `1`-periodic functions, say -- the leading coefficient of an element naturally takes its
values in `C[X]` rather than in the scalars, and the character of the frequency group is
`C`-valued.  The frequency directions killed by the character are exactly the invariant ones, and
they are absorbed into `C`; on the quotient group the character is again injective.

The conclusion is the same retraction: a `C`-rational function which is a translation defect of the
fraction field is already a translation defect of `C(x)`.
-/

open Polynomial

namespace HTGeometry.Rel

variable {C : Type*} [Field C]
variable {Λ : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]

/-- Least-frequency and leading-coefficient data with values in `C[X]`, graded by a linearly
ordered abelian group `Λ`, the shift acting through a `C`-valued character. -/
structure GradedLeadOver (C : Type*) [Field C]
    (Λ : Type*) [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (D : Type*) [CommRing D] where
  /-- The unit shift. -/
  sigma : D ≃+* D
  /-- The least frequency carrying a nonzero coefficient. -/
  ord : D → Λ
  /-- The coefficient at the least frequency. -/
  lead : D → C[X]
  /-- Embedding of the frequency-zero part. -/
  emb : C[X] →+* D
  /-- The character through which the shift acts on leading coefficients. -/
  chi : Λ → C
  chi_zero : chi 0 = 1
  chi_add : ∀ a b : Λ, chi (a + b) = chi a * chi b
  chi_ne_zero : ∀ a : Λ, chi a ≠ 0
  /-- No nonconstant monomial is shift-invariant modulo the invariants. -/
  chi_injective : Function.Injective chi
  lead_zero : lead 0 = 0
  lead_ne_zero : ∀ {f : D}, f ≠ 0 → lead f ≠ 0
  ord_mul : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord (f * g) = ord f + ord g
  lead_mul : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → lead (f * g) = lead f * lead g
  sigma_ne_zero : ∀ {f : D}, f ≠ 0 → sigma f ≠ 0
  ord_sigma : ∀ {f : D}, f ≠ 0 → ord (sigma f) = ord f
  lead_sigma : ∀ {f : D}, f ≠ 0 →
    Polynomial.C (chi (ord f)) * lead (sigma f) = (lead f).comp (X + 1)
  le_ord_sub : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord f = ord g → f - g ≠ 0 →
    ord f ≤ ord (f - g)
  lead_sub : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord f = ord g → ord (f - g) = ord f →
    lead (f - g) = lead f - lead g
  lead_eq_of_ord_lt : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord f = ord g → ord f < ord (f - g) →
    lead f = lead g
  sigma_emb : ∀ p : C[X], sigma (emb p) = emb (p.comp (X + 1))
  emb_ne_zero : ∀ {p : C[X]}, p ≠ 0 → emb p ≠ 0
  ord_emb : ∀ {p : C[X]}, p ≠ 0 → ord (emb p) = 0
  lead_emb : ∀ {p : C[X]}, p ≠ 0 → lead (emb p) = p

theorem natDegree_X_add_one (C : Type*) [Field C] : ((X + 1 : C[X])).natDegree = 1 := by
  have h : (X + 1 : C[X]) = X + Polynomial.C 1 := by simp
  rw [h, Polynomial.natDegree_X_add_C]

theorem leadingCoeff_X_add_one (C : Type*) [Field C] : ((X + 1 : C[X])).leadingCoeff = 1 := by
  have h : (X + 1 : C[X]) = X + Polynomial.C 1 := by simp
  rw [h]
  exact Polynomial.monic_X_add_C 1

/-- Shifting a polynomial preserves its leading coefficient. -/
theorem leadingCoeff_comp_X_add_one (p : C[X]) :
    (p.comp (X + 1)).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff_comp (by rw [natDegree_X_add_one]; omega),
    leadingCoeff_X_add_one, one_pow, mul_one]

/-- Shifting a polynomial preserves its degree. -/
theorem natDegree_comp_X_add_one (p : C[X]) :
    (p.comp (X + 1)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp, natDegree_X_add_one, mul_one]

theorem comp_X_add_one_ne_zero {p : C[X]} (hp : p ≠ 0) : p.comp (X + 1) ≠ 0 := by
  intro h0
  exact hp (Polynomial.leadingCoeff_eq_zero.mp
    (by rw [← leadingCoeff_comp_X_add_one p, h0, Polynomial.leadingCoeff_zero]))

/-- If `k * (A(X+1) * B) = l * (A * B(X+1))` with `A`, `B` nonzero, the two scalars agree. -/
theorem scalar_eq_of_scaled_shift_eq {A B : C[X]} (hA : A ≠ 0) (hB : B ≠ 0) {k l : C}
    (h : Polynomial.C k * (A.comp (X + 1) * B) = Polynomial.C l * (A * B.comp (X + 1))) :
    k = l := by
  have hAs : A.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hA
  have hBs : B.comp (X + 1) ≠ 0 := comp_X_add_one_ne_zero hB
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
  have hco := congrArg (fun p : C[X] => p.coeff (A.natDegree + B.natDegree)) h
  simp only [Polynomial.coeff_C_mul, hcL, hcR] at hco
  exact mul_right_cancel₀
    (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hA) (Polynomial.leadingCoeff_ne_zero.mpr hB))
    hco

namespace GradedLeadOver

variable {D : Type*} [CommRing D]

theorem mul_ne_zero' (Dat : GradedLeadOver C Λ D) {f g : D} (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  intro h
  have hl := Dat.lead_mul hf hg
  rw [h, Dat.lead_zero] at hl
  exact (mul_ne_zero (Dat.lead_ne_zero hf) (Dat.lead_ne_zero hg)) hl.symm

/-- **The frequencies of numerator and denominator agree.** -/
theorem ord_eq_of_rel (Dat : GradedLeadOver C Λ D)
    {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0)
    {rn rd : C[X]} (hrd : rd ≠ 0)
    (hrel : Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb rn * (Dat.sigma Q * Q)) :
    Dat.ord P = Dat.ord Q := by
  classical
  set m0 := Dat.ord P with hm0
  set m1 := Dat.ord Q with hm1
  have hsP : Dat.sigma P ≠ 0 := Dat.sigma_ne_zero hP
  have hsQ : Dat.sigma Q ≠ 0 := Dat.sigma_ne_zero hQ
  have hL1 : Dat.sigma P * Q ≠ 0 := Dat.mul_ne_zero' hsP hQ
  have hL2 : P * Dat.sigma Q ≠ 0 := Dat.mul_ne_zero' hP hsQ
  have hordL1 : Dat.ord (Dat.sigma P * Q) = m0 + m1 := by
    rw [Dat.ord_mul hsP hQ, Dat.ord_sigma hP]
  have hordL2 : Dat.ord (P * Dat.sigma Q) = m0 + m1 := by
    rw [Dat.ord_mul hP hsQ, Dat.ord_sigma hQ]
  have hordeq : Dat.ord (Dat.sigma P * Q) = Dat.ord (P * Dat.sigma Q) := by
    rw [hordL1, hordL2]
  have hleadL1 : Polynomial.C (Dat.chi m0) * Dat.lead (Dat.sigma P * Q)
      = (Dat.lead P).comp (X + 1) * Dat.lead Q := by
    rw [Dat.lead_mul hsP hQ, ← mul_assoc, Dat.lead_sigma hP]
  have hleadL2 : Polynomial.C (Dat.chi m1) * Dat.lead (P * Dat.sigma Q)
      = Dat.lead P * (Dat.lead Q).comp (X + 1) := by
    rw [Dat.lead_mul hP hsQ, mul_comm (Dat.lead P) (Dat.lead (Dat.sigma Q)), ← mul_assoc,
      Dat.lead_sigma hQ, mul_comm]
  have hAne : Dat.lead P ≠ 0 := Dat.lead_ne_zero hP
  have hBne : Dat.lead Q ≠ 0 := Dat.lead_ne_zero hQ
  have hcancel : Dat.lead (Dat.sigma P * Q) = Dat.lead (P * Dat.sigma Q) → m0 = m1 := by
    intro hc
    have h1 : Polynomial.C (Dat.chi m1) * (Polynomial.C (Dat.chi m0) * Dat.lead (Dat.sigma P * Q))
        = Polynomial.C (Dat.chi m0) * (Polynomial.C (Dat.chi m1) * Dat.lead (P * Dat.sigma Q)) := by
      rw [hc]; ring
    rw [hleadL1, hleadL2] at h1
    exact Dat.chi_injective (scalar_eq_of_scaled_shift_eq hAne hBne h1).symm
  by_cases hu : Dat.sigma P * Q - P * Dat.sigma Q = 0
  · exact hcancel (by rw [sub_eq_zero.mp hu])
  · have hrdu : Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q) ≠ 0 :=
      Dat.mul_ne_zero' (Dat.emb_ne_zero hrd) hu
    have hrn : rn ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hrel
      exact hrdu hrel
    have hQQ : Dat.sigma Q * Q ≠ 0 := Dat.mul_ne_zero' hsQ hQ
    have hordu : Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) = m1 + m1 := by
      have hl : Dat.ord (Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q))
          = Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) := by
        rw [Dat.ord_mul (Dat.emb_ne_zero hrd) hu, Dat.ord_emb hrd, zero_add]
      have hr : Dat.ord (Dat.emb rn * (Dat.sigma Q * Q)) = m1 + m1 := by
        rw [Dat.ord_mul (Dat.emb_ne_zero hrn) hQQ, Dat.ord_emb hrn, zero_add,
          Dat.ord_mul hsQ hQ, Dat.ord_sigma hQ]
      rw [← hl, hrel, hr]
    have hge : m0 + m1 ≤ m1 + m1 := by
      have := Dat.le_ord_sub hL1 hL2 hordeq hu
      rw [hordL1, hordu] at this
      exact this
    rcases lt_or_eq_of_le (le_of_add_le_add_right hge) with hlt | heq
    · exfalso
      have hstrict : Dat.ord (Dat.sigma P * Q) < Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) := by
        rw [hordL1, hordu]
        gcongr
      exact absurd (hcancel (Dat.lead_eq_of_ord_lt hL1 hL2 hordeq hstrict)) (ne_of_lt hlt)
    · exact heq

/-- **The leading coefficients inherit the shift defect.** -/
theorem lead_shift_identity (Dat : GradedLeadOver C Λ D)
    {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0)
    {rn rd : C[X]} (hrd : rd ≠ 0)
    (hrel : Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb rn * (Dat.sigma Q * Q)) :
    ((Dat.lead P).comp (X + 1) * Dat.lead Q - Dat.lead P * (Dat.lead Q).comp (X + 1)) * rd
      = rn * ((Dat.lead Q).comp (X + 1) * Dat.lead Q) := by
  classical
  have hordPQ : Dat.ord P = Dat.ord Q := ord_eq_of_rel Dat hP hQ hrd hrel
  set m := Dat.ord Q with hm
  have hsP : Dat.sigma P ≠ 0 := Dat.sigma_ne_zero hP
  have hsQ : Dat.sigma Q ≠ 0 := Dat.sigma_ne_zero hQ
  have hL1 : Dat.sigma P * Q ≠ 0 := Dat.mul_ne_zero' hsP hQ
  have hL2 : P * Dat.sigma Q ≠ 0 := Dat.mul_ne_zero' hP hsQ
  have hQQ : Dat.sigma Q * Q ≠ 0 := Dat.mul_ne_zero' hsQ hQ
  have hordL1 : Dat.ord (Dat.sigma P * Q) = m + m := by
    rw [Dat.ord_mul hsP hQ, Dat.ord_sigma hP, hordPQ]
  have hordL2 : Dat.ord (P * Dat.sigma Q) = m + m := by
    rw [Dat.ord_mul hP hsQ, Dat.ord_sigma hQ, hordPQ]
  have hordeq : Dat.ord (Dat.sigma P * Q) = Dat.ord (P * Dat.sigma Q) := by
    rw [hordL1, hordL2]
  have hleadL1 : Polynomial.C (Dat.chi m) * Dat.lead (Dat.sigma P * Q)
      = (Dat.lead P).comp (X + 1) * Dat.lead Q := by
    have hs := Dat.lead_sigma hP
    rw [hordPQ] at hs
    rw [Dat.lead_mul hsP hQ, ← mul_assoc, hs]
  have hleadL2 : Polynomial.C (Dat.chi m) * Dat.lead (P * Dat.sigma Q)
      = Dat.lead P * (Dat.lead Q).comp (X + 1) := by
    rw [Dat.lead_mul hP hsQ, mul_comm (Dat.lead P) (Dat.lead (Dat.sigma Q)), ← mul_assoc,
      Dat.lead_sigma hQ, mul_comm]
  have hleadR : Polynomial.C (Dat.chi m) * Dat.lead (Dat.sigma Q * Q)
      = (Dat.lead Q).comp (X + 1) * Dat.lead Q := by
    rw [Dat.lead_mul hsQ hQ, ← mul_assoc, Dat.lead_sigma hQ]
  by_cases hu : Dat.sigma P * Q - P * Dat.sigma Q = 0
  · have hrn : rn = 0 := by
      by_contra hne
      rw [hu, mul_zero] at hrel
      exact (Dat.mul_ne_zero' (Dat.emb_ne_zero hne) hQQ) hrel.symm
    have hc : Dat.lead (Dat.sigma P * Q) = Dat.lead (P * Dat.sigma Q) := by
      rw [sub_eq_zero.mp hu]
    have hAB : (Dat.lead P).comp (X + 1) * Dat.lead Q
        = Dat.lead P * (Dat.lead Q).comp (X + 1) := by
      rw [← hleadL1, ← hleadL2, hc]
    rw [hrn, hAB]
    ring
  · have hrn : rn ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hrel
      exact (Dat.mul_ne_zero' (Dat.emb_ne_zero hrd) hu) hrel
    have hordu : Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) = m + m := by
      have hl : Dat.ord (Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q))
          = Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) := by
        rw [Dat.ord_mul (Dat.emb_ne_zero hrd) hu, Dat.ord_emb hrd, zero_add]
      have hr : Dat.ord (Dat.emb rn * (Dat.sigma Q * Q)) = m + m := by
        rw [Dat.ord_mul (Dat.emb_ne_zero hrn) hQQ, Dat.ord_emb hrn, zero_add,
          Dat.ord_mul hsQ hQ, Dat.ord_sigma hQ]
      rw [← hl, hrel, hr]
    have hleadu : Dat.lead (Dat.sigma P * Q - P * Dat.sigma Q)
        = Dat.lead (Dat.sigma P * Q) - Dat.lead (P * Dat.sigma Q) :=
      Dat.lead_sub hL1 hL2 hordeq (by rw [hordu, hordL1])
    have hmain : rd * Dat.lead (Dat.sigma P * Q - P * Dat.sigma Q)
        = rn * Dat.lead (Dat.sigma Q * Q) := by
      have := congrArg Dat.lead hrel
      rwa [Dat.lead_mul (Dat.emb_ne_zero hrd) hu, Dat.lead_emb hrd,
        Dat.lead_mul (Dat.emb_ne_zero hrn) hQQ, Dat.lead_emb hrn] at this
    have hscaled := congrArg (fun p : C[X] => Polynomial.C (Dat.chi m) * p) hmain
    simp only at hscaled
    calc ((Dat.lead P).comp (X + 1) * Dat.lead Q
            - Dat.lead P * (Dat.lead Q).comp (X + 1)) * rd
        = rd * (Polynomial.C (Dat.chi m) *
            (Dat.lead (Dat.sigma P * Q) - Dat.lead (P * Dat.sigma Q))) := by
          rw [mul_sub, hleadL1, hleadL2]; ring
      _ = rn * (Polynomial.C (Dat.chi m) * Dat.lead (Dat.sigma Q * Q)) := by
          rw [← hleadu]; linear_combination hscaled
      _ = rn * ((Dat.lead Q).comp (X + 1) * Dat.lead Q) := by rw [hleadR]

end GradedLeadOver

section Base

variable {K : Type*} [Field K] [Algebra C K]

/-- The `C`-rational functions in the shift coordinate. -/
noncomputable def coordBaseOver (C : Type*) [Field C] [Algebra C K] (x : K) :
    IntermediateField C K := IntermediateField.adjoin C {x}

theorem aeval_injective_of_transcendental {x : K} (hx : Transcendental C x) :
    Function.Injective (fun P : C[X] => Polynomial.aeval x P) := by
  intro P Q h
  by_contra hne
  exact hx ⟨P - Q, sub_ne_zero.mpr hne, by simpa [sub_eq_zero] using congrArg id h⟩

theorem aeval_ne_zero_of_transcendental {x : K} (hx : Transcendental C x) {p : C[X]}
    (hp : p ≠ 0) : Polynomial.aeval x p ≠ 0 := by
  intro h
  exact hp (aeval_injective_of_transcendental hx (by simpa using h))

theorem sigma_aeval_coordOver (sigma : K ≃ₐ[C] K) {x : K} (hsig : sigma x = x + 1) (P : C[X]) :
    sigma (Polynomial.aeval x P) = Polynomial.aeval x (P.comp (X + Polynomial.C 1)) := by
  rw [Polynomial.aeval_comp]
  simp only [map_add, Polynomial.aeval_X, map_one]
  rw [← hsig]
  exact (Polynomial.aeval_algHom_apply (sigma.toAlgHom) x P).symm

theorem aeval_mem_coordBaseOver (x : K) (p : C[X]) :
    Polynomial.aeval x p ∈ coordBaseOver C x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact mul_mem ((coordBaseOver C x).algebraMap_mem a)
        (pow_mem (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)) n)

/-- **Leading-term inertness over the invariant field.**  A `C`-rational function that is the
translation defect of a quotient from a graded shift ring is already the translation defect of a
`C`-rational function. -/
theorem graded_defect_inert_over {x : K} (hx : Transcendental C x)
    (sigma : K ≃ₐ[C] K) (hsig : sigma x = x + 1)
    {D : Type*} [CommRing D] (Dat : GradedLeadOver C Λ D)
    (phi : D →+* K) (hinj : Function.Injective phi)
    (hphisigma : ∀ f : D, phi (Dat.sigma f) = sigma (phi f))
    (hphiemb : ∀ p : C[X], phi (Dat.emb p) = Polynomial.aeval x p)
    {P Q : D} (hQ : Q ≠ 0) {v : K} (hv : v ∈ coordBaseOver C x)
    (hdef : sigma (phi P / phi Q) - phi P / phi Q = v) :
    ∃ R ∈ coordBaseOver C x, sigma R - R = v := by
  classical
  obtain ⟨rn, rd, hrv⟩ := (IntermediateField.mem_adjoin_simple_iff C v).mp hv
  rcases eq_or_ne rd 0 with rfl | hrd
  · exact ⟨0, zero_mem _, by rw [hrv]; simp⟩
  rcases eq_or_ne P 0 with rfl | hP
  · refine ⟨0, zero_mem _, ?_⟩
    rw [map_zero, zero_div, map_zero, sub_zero] at hdef
    rw [← hdef]
    simp
  have hphiQ : phi Q ≠ 0 := fun h => hQ (hinj (by simpa using h))
  have hsQ : Dat.sigma Q ≠ 0 := Dat.sigma_ne_zero hQ
  have hrdK : Polynomial.aeval x rd ≠ 0 := aeval_ne_zero_of_transcendental hx hrd
  have hsigphiQ : sigma (phi Q) ≠ 0 := by
    intro h
    exact hphiQ (sigma.injective (h.trans (map_zero sigma).symm))
  have hclear : phi (Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q))
      = phi (Dat.emb rn * (Dat.sigma Q * Q)) := by
    simp only [map_mul, map_sub, hphiemb, hphisigma]
    rw [map_div₀] at hdef
    rw [hrv] at hdef
    field_simp at hdef
    linear_combination hdef
  have hlead := Dat.lead_shift_identity hP hQ hrd (hinj hclear)
  set A : C[X] := Dat.lead P with hA
  set B : C[X] := Dat.lead Q with hB
  have hBne : B ≠ 0 := Dat.lead_ne_zero hQ
  have hBsne : B.comp (X + Polynomial.C 1) ≠ 0 := by
    have h1 : (X + Polynomial.C 1 : C[X]) = X + 1 := by simp
    rw [h1]
    exact comp_X_add_one_ne_zero hBne
  have hBK : Polynomial.aeval x B ≠ 0 := aeval_ne_zero_of_transcendental hx hBne
  have hBsK : Polynomial.aeval x (B.comp (X + Polynomial.C 1)) ≠ 0 :=
    aeval_ne_zero_of_transcendental hx hBsne
  refine ⟨Polynomial.aeval x A / Polynomial.aeval x B, ?_, ?_⟩
  · exact div_mem (aeval_mem_coordBaseOver x A) (aeval_mem_coordBaseOver x B)
  · rw [hrv, map_div₀, sigma_aeval_coordOver sigma hsig, sigma_aeval_coordOver sigma hsig]
    have hK := congrArg (fun p : C[X] => Polynomial.aeval x p) hlead
    simp only [map_mul, map_sub] at hK
    simp only [Polynomial.C_1] at hBsK hK ⊢
    rw [div_sub_div _ _ hBsK hBK, div_eq_div_iff (mul_ne_zero hBsK hBK) hrdK]
    linear_combination hK

end Base

end HTGeometry.Rel
