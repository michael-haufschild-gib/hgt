import GaloisForLFunctions.HTGeometry.EllipticGammaJetSourceDivisor
import GaloisForLFunctions.HTGeometry.TripticCornerAccumulation
import GaloisForLFunctions.HTGeometry.TripticGermConstraint

/-!
# The orbital divisor is linear on sources with finite orbit support

The boundary function of a mixed-constraint source has `1`- and `τ`-invariant negative Laurent
coefficients, so on every `σ`-orbit only finitely many of them are nonzero.  On such sources the
orbital divisor is additive and commutes with constant multiples — the two facts a normal-form
correction needs in order to be assembled slot by slot.

* `laurentCoeff_boundary_periodic_one`, `laurentCoeff_boundary_periodic_tau`;
* `finite_support_orbitalDivisorTerm`;
* `additiveOrbitalDivisorAt_add`, `additiveOrbitalDivisorAt_sub`,
  `additiveOrbitalDivisorAt_const_mul`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Scalar multiples pass through the Laurent transform. -/
theorem laurentCoeff_const_mul {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (c : ℂ) (ℓ : ℤ) :
    laurentCoeff (fun z ↦ c * f z) a ℓ = c * laurentCoeff f a ℓ := by
  have h := laurentCoeff_sum (Finset.univ : Finset (Fin 1)) (fun _ ↦ f) (fun _ ↦ c) a ℓ
    (fun _ _ ↦ hf)
  simpa using h

/-- The boundary function of a germ-periodic source is germ-periodic. -/
theorem laurentCoeff_boundary_periodic_one {F : ℂ → ℂ} {σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ)) (hper : PeriodicOneGerm F) (ℓ : ℤ) (z : ℂ) :
    laurentCoeff (fun w ↦ F (w + σ) - F w) (z + 1) ℓ
      = laurentCoeff (fun w ↦ F (w + σ) - F w) z ℓ := by
  have hUmero : MeromorphicOn (fun w ↦ F (w + σ) - F w) (Set.univ : Set ℂ) := fun y _ ↦
    (meromorphicAt_comp_add.mpr (hF (y + σ) (Set.mem_univ _))).sub (hF y (Set.mem_univ y))
  have hmero : MeromorphicAt (fun w ↦ F (w + 1 + σ) - F (w + 1)) z :=
    meromorphicAt_comp_add.mpr (hUmero (z + 1) (Set.mem_univ _))
  calc laurentCoeff (fun w ↦ F (w + σ) - F w) (z + 1) ℓ
      = laurentCoeff (fun w ↦ F (w + 1 + σ) - F (w + 1)) z ℓ :=
        (laurentCoeff_comp_add (fun w ↦ F (w + σ) - F w) z 1 ℓ).symm
    _ = laurentCoeff (fun w ↦ F (w + σ) - F w) z ℓ :=
        laurentCoeff_congr hmero (eventuallyEq_boundary_shift_one hper σ z) ℓ

/-- A `τ`-step changes the boundary function of a mixed-constraint source by the mixed constant, so
it moves no Laurent coefficient of negative index. -/
theorem laurentCoeff_boundary_periodic_tau {F : ℂ → ℂ} {τ σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ))
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    {ℓ : ℤ} (hℓ : ℓ < 0) (z : ℂ) :
    laurentCoeff (fun w ↦ F (w + σ) - F w) (z + τ) ℓ
      = laurentCoeff (fun w ↦ F (w + σ) - F w) z ℓ := by
  have hUmero : MeromorphicOn (fun w ↦ F (w + σ) - F w) (Set.univ : Set ℂ) := fun y _ ↦
    (meromorphicAt_comp_add.mpr (hF (y + σ) (Set.mem_univ _))).sub (hF y (Set.mem_univ y))
  have hmero : MeromorphicAt (fun w ↦ F (w + τ + σ) - F (w + τ)) z :=
    meromorphicAt_comp_add.mpr (hUmero (z + τ) (Set.mem_univ _))
  calc laurentCoeff (fun w ↦ F (w + σ) - F w) (z + τ) ℓ
      = laurentCoeff (fun w ↦ F (w + τ + σ) - F (w + τ)) z ℓ :=
        (laurentCoeff_comp_add (fun w ↦ F (w + σ) - F w) z τ ℓ).symm
    _ = laurentCoeff (fun w ↦ (F (w + σ) - F w) + Cst) z ℓ :=
        laurentCoeff_congr hmero (eventuallyEq_boundary_shift_tau hmixed z) ℓ
    _ = laurentCoeff (fun w ↦ F (w + σ) - F w) z ℓ :=
        laurentCoeff_add_const (hUmero z (Set.mem_univ z)) Cst hℓ

/-- **Only finitely many points of a `σ`-orbit carry a nonzero boundary coefficient.** -/
theorem finite_support_orbitalDivisorTerm {F : ℂ → ℂ} {τ σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ)) (hper : PeriodicOneGerm F)
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im)
    (hindep : ∀ m n j : ℤ, (m : ℂ) * σ + (n : ℂ) * τ + (j : ℂ) = 0 → m = 0 ∧ n = 0 ∧ j = 0)
    (p : ℂ) {ℓ : ℤ} (hℓ : ℓ < 0) :
    {m : ℤ | laurentCoeff (fun w ↦ F (w + σ) - F w) (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite := by
  have hUmero : MeromorphicOn (fun w ↦ F (w + σ) - F w) (Set.univ : Set ℂ) := fun y _ ↦
    (meromorphicAt_comp_add.mpr (hF (y + σ) (Set.mem_univ _))).sub (hF y (Set.mem_univ y))
  exact finite_setOf_laurentCoeff_ne_zero_orbit hUmero hℓ hτ
    (laurentCoeff_boundary_periodic_one hF hper ℓ)
    (laurentCoeff_boundary_periodic_tau hF hmixed hℓ) hindep p

/-- **The orbital divisor is additive** on sources whose orbit terms have finite support. -/
theorem additiveOrbitalDivisorAt_add {F G : ℂ → ℂ} {σ p : ℂ} {ℓ : ℤ}
    (hFm : MeromorphicOn F (Set.univ : Set ℂ)) (hGm : MeromorphicOn G (Set.univ : Set ℂ))
    (hFs : {m : ℤ | laurentCoeff (fun w ↦ F (w + σ) - F w) (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite)
    (hGs : {m : ℤ | laurentCoeff (fun w ↦ G (w + σ) - G w) (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite) :
    additiveOrbitalDivisorAt (F + G) σ p ℓ
      = additiveOrbitalDivisorAt F σ p ℓ + additiveOrbitalDivisorAt G σ p ℓ := by
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z ↦ (F + G) (z + σ) - (F + G) z) (p + (m : ℂ) * σ) ℓ
        = laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ
          + laurentCoeff (fun z ↦ G (z + σ) - G z) (p + (m : ℂ) * σ) ℓ := by
    intro m
    have hFa : MeromorphicAt (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) :=
      (meromorphicAt_comp_add.mpr (hFm _ (Set.mem_univ _))).sub (hFm _ (Set.mem_univ _))
    have hGa : MeromorphicAt (fun z ↦ G (z + σ) - G z) (p + (m : ℂ) * σ) :=
      (meromorphicAt_comp_add.mpr (hGm _ (Set.mem_univ _))).sub (hGm _ (Set.mem_univ _))
    rw [← laurentCoeff_add hFa hGa]
    congr 1
    funext z
    simp only [Pi.add_apply]
    ring
  rw [additiveOrbitalDivisorAt, additiveOrbitalDivisorAt, additiveOrbitalDivisorAt,
    finsum_congr hterm]
  exact finsum_add_distrib hFs hGs

/-- **The orbital divisor commutes with constant multiples.** -/
theorem additiveOrbitalDivisorAt_const_mul {F : ℂ → ℂ} (hFm : MeromorphicOn F (Set.univ : Set ℂ))
    (c : ℂ) (σ p : ℂ) (ℓ : ℤ) :
    additiveOrbitalDivisorAt (fun z ↦ c * F z) σ p ℓ = c * additiveOrbitalDivisorAt F σ p ℓ := by
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z ↦ c * F (z + σ) - c * F z) (p + (m : ℂ) * σ) ℓ
        = c * laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ := by
    intro m
    have hFa : MeromorphicAt (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) :=
      (meromorphicAt_comp_add.mpr (hFm _ (Set.mem_univ _))).sub (hFm _ (Set.mem_univ _))
    rw [← laurentCoeff_const_mul hFa c ℓ]
    congr 1
    funext z
    ring
  rw [additiveOrbitalDivisorAt, additiveOrbitalDivisorAt, finsum_congr hterm]
  exact (mul_finsum _ _).symm

/-- **The orbital divisor is subtractive** on sources whose orbit terms have finite support. -/
theorem additiveOrbitalDivisorAt_sub {F G : ℂ → ℂ} {σ p : ℂ} {ℓ : ℤ}
    (hFm : MeromorphicOn F (Set.univ : Set ℂ)) (hGm : MeromorphicOn G (Set.univ : Set ℂ))
    (hFs : {m : ℤ | laurentCoeff (fun w ↦ F (w + σ) - F w) (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite)
    (hGs : {m : ℤ | laurentCoeff (fun w ↦ G (w + σ) - G w) (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite) :
    additiveOrbitalDivisorAt (fun z ↦ F z - G z) σ p ℓ
      = additiveOrbitalDivisorAt F σ p ℓ - additiveOrbitalDivisorAt G σ p ℓ := by
  have hneg : additiveOrbitalDivisorAt (fun z ↦ (-1 : ℂ) * G z) σ p ℓ
      = (-1 : ℂ) * additiveOrbitalDivisorAt G σ p ℓ :=
    additiveOrbitalDivisorAt_const_mul hGm (-1) σ p ℓ
  have hnegm : MeromorphicOn (fun z ↦ (-1 : ℂ) * G z) (Set.univ : Set ℂ) := fun y _ ↦
    (analyticAt_const (x := y)).meromorphicAt.mul (hGm y (Set.mem_univ y))
  have hnegs : {m : ℤ | laurentCoeff (fun w ↦ (-1 : ℂ) * G (w + σ) - (-1 : ℂ) * G w)
      (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite := by
    refine hGs.subset fun m hm ↦ ?_
    simp only [Set.mem_setOf_eq] at hm ⊢
    intro hzero
    apply hm
    have hFa : MeromorphicAt (fun z ↦ G (z + σ) - G z) (p + (m : ℂ) * σ) :=
      (meromorphicAt_comp_add.mpr (hGm _ (Set.mem_univ _))).sub (hGm _ (Set.mem_univ _))
    have hcm : laurentCoeff (fun z ↦ (-1 : ℂ) * G (z + σ) - (-1 : ℂ) * G z)
        (p + (m : ℂ) * σ) ℓ
        = (-1 : ℂ) * laurentCoeff (fun z ↦ G (z + σ) - G z) (p + (m : ℂ) * σ) ℓ := by
      rw [← laurentCoeff_const_mul hFa (-1) ℓ]
      congr 1
      funext z
      ring
    rw [hcm, hzero, mul_zero]
  have hadd := additiveOrbitalDivisorAt_add (F := F) (G := fun z ↦ (-1 : ℂ) * G z)
    hFm hnegm hFs hnegs
  have hfun : (fun z ↦ F z - G z) = F + fun z ↦ (-1 : ℂ) * G z := by
    funext z
    simp only [Pi.add_apply]
    ring
  rw [hfun, hadd, hneg]
  ring

end

end GaloisForLFunctions.HTGeometry
