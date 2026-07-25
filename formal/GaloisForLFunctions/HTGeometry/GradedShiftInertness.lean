import GaloisForLFunctions.HTGeometry.DirichletLeadingTerm
import Mathlib

/-!
# Graded shift rings and leading-term inertness

A ring of exponential sums `sum_lambda P_lambda (s) e ^ (- lambda * s)` carries a least frequency
`ord` and a leading coefficient `lead`.  Both are multiplicative, and the unit shift acts on the
leading coefficient through a character `chi` of the frequency group:

`ord (sigma f) = ord f`,   `chi (ord f) * lead (sigma f) = (lead f) (X + 1)`.

`GradedLead` axiomatises exactly this.  The frequency group is an arbitrary linearly ordered abelian
group and `chi` is required to be injective; injectivity says precisely that no nonconstant monomial
is fixed by the shift.  Ordinary Dirichlet series are the case of frequency group `R`, frequencies
`log m`, and `chi = exp`.

The consequence extracted here is that a ratio with a rational shift defect forces the ratio of the
two leading coefficients to be a rational function with the *same* defect.  No asymptotic analysis
enters; the character does all the work.
-/

open Polynomial

namespace HTGeometry

variable {Λ : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]

/-- Least-frequency and leading-coefficient data on a ring of exponential-sum type, graded by a
linearly ordered abelian group `Λ` with the shift acting through the character `chi`. -/
structure GradedLead (Λ : Type*) [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (D : Type*) [CommRing D] where
  /-- The unit shift. -/
  sigma : D ≃+* D
  /-- The least frequency carrying a nonzero coefficient. -/
  ord : D → Λ
  /-- The coefficient at the least frequency. -/
  lead : D → ℂ[X]
  /-- Embedding of the frequency-zero part. -/
  emb : ℂ[X] →+* D
  /-- The character through which the shift acts on leading coefficients. -/
  chi : Λ → ℂ
  chi_zero : chi 0 = 1
  chi_add : ∀ a b : Λ, chi (a + b) = chi a * chi b
  chi_ne_zero : ∀ a : Λ, chi a ≠ 0
  /-- No nonconstant monomial is shift-invariant. -/
  chi_injective : Function.Injective chi
  lead_zero : lead 0 = 0
  lead_ne_zero : ∀ {f : D}, f ≠ 0 → lead f ≠ 0
  ord_mul : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord (f * g) = ord f + ord g
  lead_mul : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → lead (f * g) = lead f * lead g
  sigma_ne_zero : ∀ {f : D}, f ≠ 0 → sigma f ≠ 0
  ord_sigma : ∀ {f : D}, f ≠ 0 → ord (sigma f) = ord f
  lead_sigma : ∀ {f : D}, f ≠ 0 →
    Polynomial.C (chi (ord f)) * lead (sigma f) = (lead f).comp (X + 1)
  /-- Subtraction never lowers the least frequency. -/
  le_ord_sub : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord f = ord g → f - g ≠ 0 →
    ord f ≤ ord (f - g)
  /-- With no cancellation the leading coefficients subtract. -/
  lead_sub : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord f = ord g → ord (f - g) = ord f →
    lead (f - g) = lead f - lead g
  /-- A strict rise of the frequency means the leading coefficients agreed. -/
  lead_eq_of_ord_lt : ∀ {f g : D}, f ≠ 0 → g ≠ 0 → ord f = ord g → ord f < ord (f - g) →
    lead f = lead g
  sigma_emb : ∀ p : ℂ[X], sigma (emb p) = emb (p.comp (X + 1))
  emb_ne_zero : ∀ {p : ℂ[X]}, p ≠ 0 → emb p ≠ 0
  ord_emb : ∀ {p : ℂ[X]}, p ≠ 0 → ord (emb p) = 0
  lead_emb : ∀ {p : ℂ[X]}, p ≠ 0 → lead (emb p) = p

/-- If `k * (A(X+1) * B) = l * (A * B(X+1))` with `A`, `B` nonzero, the two scalars agree. -/
theorem complex_eq_of_scaled_shift_eq {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0) {k l : ℂ}
    (h : Polynomial.C k * (A.comp (X + 1) * B) = Polynomial.C l * (A * B.comp (X + 1))) :
    k = l := by
  have hAs : A.comp (X + 1) ≠ 0 := by
    intro h0
    exact hA (Polynomial.leadingCoeff_eq_zero.mp
      (by rw [← DirichletLead.leadingCoeff_comp_X_add_one A, h0, Polynomial.leadingCoeff_zero]))
  have hBs : B.comp (X + 1) ≠ 0 := by
    intro h0
    exact hB (Polynomial.leadingCoeff_eq_zero.mp
      (by rw [← DirichletLead.leadingCoeff_comp_X_add_one B, h0, Polynomial.leadingCoeff_zero]))
  have hdegL : (A.comp (X + 1) * B).natDegree = A.natDegree + B.natDegree := by
    rw [Polynomial.natDegree_mul hAs hB, DirichletLead.natDegree_comp_X_add_one]
  have hdegR : (A * B.comp (X + 1)).natDegree = A.natDegree + B.natDegree := by
    rw [Polynomial.natDegree_mul hA hBs, DirichletLead.natDegree_comp_X_add_one]
  have hcL : (A.comp (X + 1) * B).coeff (A.natDegree + B.natDegree)
      = A.leadingCoeff * B.leadingCoeff := by
    rw [← hdegL, ← Polynomial.leadingCoeff, Polynomial.leadingCoeff_mul,
      DirichletLead.leadingCoeff_comp_X_add_one]
  have hcR : (A * B.comp (X + 1)).coeff (A.natDegree + B.natDegree)
      = A.leadingCoeff * B.leadingCoeff := by
    rw [← hdegR, ← Polynomial.leadingCoeff, Polynomial.leadingCoeff_mul,
      DirichletLead.leadingCoeff_comp_X_add_one]
  have hco := congrArg (fun p : ℂ[X] => p.coeff (A.natDegree + B.natDegree)) h
  simp only [Polynomial.coeff_C_mul, hcL, hcR] at hco
  have hprod : A.leadingCoeff * B.leadingCoeff ≠ 0 :=
    mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hA) (Polynomial.leadingCoeff_ne_zero.mpr hB)
  exact mul_right_cancel₀ hprod hco

namespace GradedLead

variable {D : Type*} [CommRing D] (Dat : GradedLead Λ D)

theorem mul_ne_zero' (Dat : GradedLead Λ D) {f g : D} (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 := by
  intro h
  have hl := Dat.lead_mul hf hg
  rw [h, Dat.lead_zero] at hl
  exact (mul_ne_zero (Dat.lead_ne_zero hf) (Dat.lead_ne_zero hg)) hl.symm

/-- **The frequencies of numerator and denominator agree.** -/
theorem ord_eq_of_rel
    {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0)
    {rn rd : ℂ[X]} (hrd : rd ≠ 0)
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
    exact Dat.chi_injective (complex_eq_of_scaled_shift_eq hAne hBne h1).symm
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
    have hle : m0 ≤ m1 := le_of_add_le_add_right hge
    rcases lt_or_eq_of_le hle with hlt | heq
    · exfalso
      have hstrict : Dat.ord (Dat.sigma P * Q) < Dat.ord (Dat.sigma P * Q - P * Dat.sigma Q) := by
        rw [hordL1, hordu]
        gcongr
      exact absurd (hcancel (Dat.lead_eq_of_ord_lt hL1 hL2 hordeq hstrict)) (ne_of_lt hlt)
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
    have hscaled := congrArg (fun p : ℂ[X] => Polynomial.C (Dat.chi m) * p) hmain
    simp only at hscaled
    calc ((Dat.lead P).comp (X + 1) * Dat.lead Q
            - Dat.lead P * (Dat.lead Q).comp (X + 1)) * rd
        = rd * (Polynomial.C (Dat.chi m) *
            (Dat.lead (Dat.sigma P * Q) - Dat.lead (P * Dat.sigma Q))) := by
          rw [mul_sub, hleadL1, hleadL2]; ring
      _ = rn * (Polynomial.C (Dat.chi m) * Dat.lead (Dat.sigma Q * Q)) := by
          rw [← hleadu]; linear_combination hscaled
      _ = rn * ((Dat.lead Q).comp (X + 1) * Dat.lead Q) := by rw [hleadR]

/-- **Transport of the graded interface along an injective ring homomorphism.** -/
noncomputable def comap {D E : Type*} [CommRing D] [CommRing E] (Dat : GradedLead Λ E)
    (phi : D →+* E) (hinj : Function.Injective phi)
    (sigmaD : D ≃+* D) (hsig : ∀ x, phi (sigmaD x) = Dat.sigma (phi x))
    (embD : ℂ[X] →+* D) (hemb : ∀ p, phi (embD p) = Dat.emb p) : GradedLead Λ D where
  sigma := sigmaD
  ord x := Dat.ord (phi x)
  lead x := Dat.lead (phi x)
  emb := embD
  chi := Dat.chi
  chi_zero := Dat.chi_zero
  chi_add := Dat.chi_add
  chi_ne_zero := Dat.chi_ne_zero
  chi_injective := Dat.chi_injective
  lead_zero := by simpa using Dat.lead_zero
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

end GradedLead

/-- Positive naturals with equal logarithms are equal. -/
theorem natPos_eq_of_log_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.log ((a : ℕ) : ℝ) = Real.log ((b : ℕ) : ℝ)) : a = b := by
  have hra : ((a : ℕ) : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by exact_mod_cast ha)
  have hrb : ((b : ℕ) : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by exact_mod_cast hb)
  exact_mod_cast Real.log_injOn_pos hra hrb h

/-- **Ordinary Dirichlet series are the graded case with frequency group `R`, frequencies
`log m` and character `exp`.**  The multiplicative least index `m` becomes the additive least
frequency `log m`, and the shift scalar `m` becomes `exp (log m)`. -/
noncomputable def DirichletLead.toGradedLead {D : Type*} [CommRing D] (Dat : DirichletLead D) :
    GradedLead ℝ D where
  sigma := Dat.sigma
  ord f := Real.log ((Dat.ord f : ℕ) : ℝ)
  lead := Dat.lead
  emb := Dat.emb
  chi t := (Real.exp t : ℂ)
  chi_zero := by simp
  chi_add a b := by push_cast [Real.exp_add]; ring
  chi_ne_zero a := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.exp_ne_zero a
  chi_injective := by
    intro a b h
    simp only [Complex.ofReal_inj] at h
    exact Real.exp_injective h
  lead_zero := Dat.lead_zero
  lead_ne_zero := Dat.lead_ne_zero
  ord_mul := @fun f g hf hg => by
    rw [Dat.ord_mul hf hg]
    push_cast
    exact Real.log_mul (Nat.cast_ne_zero.mpr (Dat.ord_pos hf).ne')
      (Nat.cast_ne_zero.mpr (Dat.ord_pos hg).ne')
  lead_mul := Dat.lead_mul
  sigma_ne_zero := Dat.sigma_ne_zero
  ord_sigma := @fun f hf => by rw [Dat.ord_sigma hf]
  lead_sigma := @fun f hf => by
    have hpos : (0 : ℝ) < ((Dat.ord f : ℕ) : ℝ) := by
      exact_mod_cast Dat.ord_pos hf
    have hexp : (Real.exp (Real.log ((Dat.ord f : ℕ) : ℝ)) : ℂ) = ((Dat.ord f : ℕ) : ℂ) := by
      rw [Real.exp_log hpos]
      push_cast
      ring
    rw [hexp]
    exact Dat.lead_sigma hf
  le_ord_sub := @fun f g hf hg hord hsub => by
    have hordn : Dat.ord f = Dat.ord g :=
      natPos_eq_of_log_eq (Dat.ord_pos hf) (Dat.ord_pos hg) hord
    have hle := Dat.le_ord_sub hf hg hordn hsub
    have hposf : (0 : ℝ) < ((Dat.ord f : ℕ) : ℝ) := by exact_mod_cast Dat.ord_pos hf
    exact Real.log_le_log hposf (by exact_mod_cast hle)
  lead_sub := @fun f g hf hg hord hsubord => by
    rcases eq_or_ne (f - g) 0 with h0 | hsub
    · rw [h0, Dat.lead_zero, sub_eq_zero.mp h0, sub_self]
    · have hordn : Dat.ord f = Dat.ord g :=
        natPos_eq_of_log_eq (Dat.ord_pos hf) (Dat.ord_pos hg) hord
      exact Dat.lead_sub hf hg hordn
        (natPos_eq_of_log_eq (Dat.ord_pos hsub) (Dat.ord_pos hf) hsubord)
  lead_eq_of_ord_lt := @fun f g hf hg hord hlt => by
    rcases eq_or_ne (f - g) 0 with h0 | hsub
    · rw [sub_eq_zero.mp h0]
    · have hordn : Dat.ord f = Dat.ord g :=
        natPos_eq_of_log_eq (Dat.ord_pos hf) (Dat.ord_pos hg) hord
      have hposf : (0 : ℝ) < ((Dat.ord f : ℕ) : ℝ) := by exact_mod_cast Dat.ord_pos hf
      have hpossub : (0 : ℝ) < ((Dat.ord (f - g) : ℕ) : ℝ) := by
        exact_mod_cast Dat.ord_pos hsub
      exact Dat.lead_eq_of_ord_lt hf hg hordn
        (by exact_mod_cast (Real.log_lt_log_iff hposf hpossub).mp hlt)
  sigma_emb := Dat.sigma_emb
  emb_ne_zero := Dat.emb_ne_zero
  ord_emb := @fun p hp => by rw [Dat.ord_emb hp]; simp
  lead_emb := Dat.lead_emb

end HTGeometry
