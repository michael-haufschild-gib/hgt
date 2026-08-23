import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Finite orbits force integrality over the invariants

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), the integrality input
for Theorem 1.4 and Corollary 1.5(1).

If a group acts on a commutative ring with all orbits finite, then every element is integral over
the subring of invariants: the orbit polynomial `∏_{c ∈ orbit b} (X - c)` is monic, kills `b`, and
has invariant coefficients because the group permutes the orbit.

This replaces the profinite-topology hypothesis by the elementary finiteness of orbits, which for
an algebraic field extension is automatic.
-/

namespace RHTower

open Polynomial

variable {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]

/-- The orbit polynomial of an element with finite orbit. -/
noncomputable def deningerOrbitPolynomial (hfin : ∀ b : B, (MulAction.orbit G b).Finite) (b : B) :
    Polynomial B :=
  ∏ c ∈ (hfin b).toFinset, (Polynomial.X - Polynomial.C c)

theorem deningerOrbitPolynomial_monic (hfin : ∀ b : B, (MulAction.orbit G b).Finite) (b : B) :
    (deningerOrbitPolynomial hfin b).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C c

theorem deningerOrbitPolynomial_eval (hfin : ∀ b : B, (MulAction.orbit G b).Finite) (b : B) :
    (deningerOrbitPolynomial hfin b).eval b = 0 := by
  classical
  have hb : b ∈ (hfin b).toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact MulAction.mem_orbit_self b
  rw [deningerOrbitPolynomial, Polynomial.eval_prod]
  refine Finset.prod_eq_zero hb ?_
  simp

/-- The group permutes the orbit, hence fixes the orbit polynomial. -/
theorem deningerOrbitPolynomial_smul (hfin : ∀ b : B, (MulAction.orbit G b).Finite) (b : B)
    (σ : G) :
    (deningerOrbitPolynomial hfin b).map (MulSemiringAction.toRingHom G B σ)
      = deningerOrbitPolynomial hfin b := by
  classical
  have himage : ((hfin b).toFinset).image (fun c => σ • c) = (hfin b).toFinset := by
    ext c
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨τ, rfl⟩ := hd
      exact ⟨σ * τ, by show (σ * τ) • b = σ • (τ • b); rw [mul_smul]⟩
    · intro hc
      refine ⟨σ⁻¹ • c, ?_, by rw [smul_inv_smul]⟩
      obtain ⟨τ, rfl⟩ := hc
      exact ⟨σ⁻¹ * τ, by show (σ⁻¹ * τ) • b = σ⁻¹ • (τ • b); rw [mul_smul]⟩
  have hinj : Set.InjOn (fun c : B => σ • c) ((hfin b).toFinset : Set B) :=
    fun a _ c _ h => by
      have := congrArg (fun x : B => σ⁻¹ • x) h
      simpa [inv_smul_smul] using this
  rw [deningerOrbitPolynomial, Polynomial.map_prod]
  have hterm : ∀ c ∈ (hfin b).toFinset,
      (Polynomial.X - Polynomial.C c).map (MulSemiringAction.toRingHom G B σ)
        = Polynomial.X - Polynomial.C (σ • c) := by
    intro c _
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hprod : ∏ c ∈ ((hfin b).toFinset).image (fun c => σ • c),
        (Polynomial.X - Polynomial.C c)
      = ∏ x ∈ (hfin b).toFinset, (Polynomial.X - Polynomial.C (σ • x)) :=
    Finset.prod_image (fun a ha c hc h => hinj ha hc h)
  rw [Finset.prod_congr rfl hterm, ← hprod, himage]

/-- **Integrality over the invariants from finite orbits.** -/
theorem deningerIsIntegral_of_finite_orbits [Nontrivial B]
    (hfin : ∀ b : B, (MulAction.orbit G b).Finite)
    (b : B) : IsIntegral (FixedPoints.subring B G) b := by
  classical
  have hcoeff : ∀ n : ℕ, (deningerOrbitPolynomial hfin b).coeff n ∈ FixedPoints.subring B G := by
    intro n σ
    have h := deningerOrbitPolynomial_smul hfin b σ
    have := congrArg (fun p : Polynomial B => p.coeff n) h
    simpa [Polynomial.coeff_map] using this
  have hlifts : deningerOrbitPolynomial hfin b
      ∈ Polynomial.lifts (algebraMap (FixedPoints.subring B G) B) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨(deningerOrbitPolynomial hfin b).coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨q, hq, -, hqmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts (deningerOrbitPolynomial_monic hfin b)
  refine ⟨q, hqmonic, ?_⟩
  have : Polynomial.eval₂ (algebraMap (FixedPoints.subring B G) B) b q
      = (deningerOrbitPolynomial hfin b).eval b := by
    rw [← hq, Polynomial.eval_map]
  rw [this]
  exact deningerOrbitPolynomial_eval hfin b

end RHTower
