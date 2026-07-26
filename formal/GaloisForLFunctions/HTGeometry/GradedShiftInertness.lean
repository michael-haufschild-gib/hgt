import GaloisForLFunctions.HTGeometry.DirichletLeadingTerm
import Mathlib
import GaloisForLFunctions.HTGeometry.RelativeGradedInertness

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
linearly ordered abelian group `Λ` with the shift acting through the character `chi`.  This is the
`ℂ`-coefficient case of `HTGeometry.Rel.GradedLeadOver`. -/
abbrev GradedLead (Λ : Type*) [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    (D : Type*) [CommRing D] :=
  Rel.GradedLeadOver ℂ Λ D

/-- Two scalars that rescale the same shifted polynomial product agree.  This is
`HTGeometry.Rel.scalar_eq_of_scaled_shift_eq` over `ℂ`. -/
theorem complex_eq_of_scaled_shift_eq {A B : ℂ[X]} (hA : A ≠ 0) (hB : B ≠ 0) {k l : ℂ}
    (h : Polynomial.C k * (A.comp (X + 1) * B) = Polynomial.C l * (A * B.comp (X + 1))) :
    k = l :=
  Rel.scalar_eq_of_scaled_shift_eq hA hB h


namespace GradedLead

variable {D : Type*} [CommRing D] (Dat : GradedLead Λ D)

theorem mul_ne_zero' (Dat : GradedLead Λ D) {f g : D} (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 :=
  Rel.GradedLeadOver.mul_ne_zero' Dat hf hg

/-- **The frequencies of numerator and denominator agree.** -/
theorem ord_eq_of_rel
    {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0)
    {rn rd : ℂ[X]} (hrd : rd ≠ 0)
    (hrel : Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb rn * (Dat.sigma Q * Q)) :
    Dat.ord P = Dat.ord Q :=
  Rel.GradedLeadOver.ord_eq_of_rel Dat hP hQ hrd hrel

/-- **The leading-coefficient shift identity carried by a first-order relation.** -/
theorem lead_shift_identity
    {P Q : D} (hP : P ≠ 0) (hQ : Q ≠ 0)
    {rn rd : ℂ[X]} (hrd : rd ≠ 0)
    (hrel : Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb rn * (Dat.sigma Q * Q)) :
    ((Dat.lead P).comp (X + 1) * Dat.lead Q - Dat.lead P * (Dat.lead Q).comp (X + 1)) * rd
      = rn * ((Dat.lead Q).comp (X + 1) * Dat.lead Q) :=
  Rel.GradedLeadOver.lead_shift_identity Dat hP hQ hrd hrel

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
