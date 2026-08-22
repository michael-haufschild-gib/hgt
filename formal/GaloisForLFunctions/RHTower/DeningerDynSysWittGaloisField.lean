import GaloisForLFunctions.RHTower.DeningerDynSysWittGaloisFiniteOrbits
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.Content

/-!
# Galois descent of rational Witt vectors over a field

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.2(b)
(`t21n`), field case: for a group `G` acting on a field `K` by field automorphisms,

`W_rat (K ^ G) = W_rat (K) ^ G`.

A rational Witt vector is recorded as a power series `F` with a normalized presentation
`Q · F = P` by polynomials with constant coefficient one (`DeningerIsRationalSeries`).

The mechanism is the source's:  pass to the coprime normalized presentation `P₂ / Q₂` obtained by
dividing out `gcd (P, Q)` and rescaling by its constant coefficient.  Bézout `a P₂ + b Q₂ = 1`
together with the cross relation `σ P₂ · Q₂ = σ Q₂ · P₂` gives `P₂ ∣ σ P₂`; since `σ` preserves
degrees and constant coefficients, `σ P₂ = P₂`, and cancelling `P₂` gives `σ Q₂ = Q₂`.

`deningerCrossRelation` and `deningerCrossRelation_poly` isolate the cross relation, which holds
over an arbitrary commutative ring.
-/

namespace RHTower

variable {G K : Type*} [Group G] [Field K] [MulSemiringAction G K]

/-- The cross relation `σP · Q = σQ · P` attached to a `G`-invariant normalized fraction. -/
theorem deningerCrossRelation {A : Type*} [CommRing A] [MulSemiringAction G A]
    {F : PowerSeries A} (hF : ∀ (σ : G) (n : ℕ), σ • PowerSeries.coeff n F = PowerSeries.coeff n F)
    {P Q : Polynomial A} (hPQ : (Q : PowerSeries A) * F = (P : PowerSeries A)) (σ : G) :
    ((deningerPolyAct σ Q : Polynomial A) : PowerSeries A) * F
      = ((deningerPolyAct σ P : Polynomial A) : PowerSeries A) := by
  have hFmap : PowerSeries.map (MulSemiringAction.toRingHom G A σ) F = F := by
    ext n
    simpa using hF σ n
  have h := congrArg (PowerSeries.map (MulSemiringAction.toRingHom G A σ)) hPQ
  rw [map_mul, hFmap] at h
  have e1 : ((deningerPolyAct σ Q : Polynomial A) : PowerSeries A)
      = PowerSeries.map (MulSemiringAction.toRingHom G A σ) (Q : PowerSeries A) := by
    simp [deningerPolyAct, Polynomial.coe_mapRingHom, Polynomial.polynomial_map_coe]
  have e2 : ((deningerPolyAct σ P : Polynomial A) : PowerSeries A)
      = PowerSeries.map (MulSemiringAction.toRingHom G A σ) (P : PowerSeries A) := by
    simp [deningerPolyAct, Polynomial.coe_mapRingHom, Polynomial.polynomial_map_coe]
  rw [e1, e2]
  exact h

theorem deningerCrossRelation_poly {A : Type*} [CommRing A] [MulSemiringAction G A]
    {F : PowerSeries A} (hF : ∀ (σ : G) (n : ℕ), σ • PowerSeries.coeff n F = PowerSeries.coeff n F)
    {P Q : Polynomial A} (hPQ : (Q : PowerSeries A) * F = (P : PowerSeries A)) (σ : G) :
    deningerPolyAct σ P * Q = deningerPolyAct σ Q * P := by
  apply Polynomial.coe_injective A
  push_cast
  rw [← deningerCrossRelation hF hPQ σ, ← hPQ]
  ring

/-- **Deninger, Proposition 1.2(b) (`t21n`), field case.**  For a group acting on a field `K` by
field automorphisms, every `G`-invariant rational Witt vector over `K` has a normalized
presentation with `G`-invariant coefficients. -/
theorem deningerRationalSeries_galoisDescent_field (F : PowerSeries K)
    (hF : ∀ (σ : G) (n : ℕ), σ • PowerSeries.coeff n F = PowerSeries.coeff n F)
    (hrat : DeningerIsRationalSeries F) :
    ∃ α β : Polynomial K,
      (∀ (σ : G) (n : ℕ), σ • α.coeff n = α.coeff n) ∧
      (∀ (σ : G) (n : ℕ), σ • β.coeff n = β.coeff n) ∧
      α.coeff 0 = 1 ∧ β.coeff 0 = 1 ∧ (β : PowerSeries K) * F = (α : PowerSeries K) := by
  classical
  obtain ⟨P, Q, hP0, hQ0, hPQ⟩ := hrat
  have hQne : Q ≠ 0 := by
    intro h
    rw [h] at hQ0
    simp at hQ0
  have hPne : P ≠ 0 := by
    intro h
    rw [h] at hP0
    simp at hP0
  set d : Polynomial K := GCDMonoid.gcd P Q with hddef
  have hdne : d ≠ 0 := gcd_ne_zero_of_right hQne
  set P₁ : Polynomial K := P / d with hP1def
  set Q₁ : Polynomial K := Q / d with hQ1def
  have hPd : d * P₁ = P := EuclideanDomain.mul_div_cancel' hdne (gcd_dvd_left P Q)
  have hQd : d * Q₁ = Q := EuclideanDomain.mul_div_cancel' hdne (gcd_dvd_right P Q)
  obtain ⟨a, b, hab⟩ : IsCoprime P₁ Q₁ := isCoprime_div_gcd_div_gcd hQne
  have hc1 : d.coeff 0 * P₁.coeff 0 = 1 := by
    rw [← Polynomial.mul_coeff_zero, hPd, hP0]
  have hc2 : d.coeff 0 * Q₁.coeff 0 = 1 := by
    rw [← Polynomial.mul_coeff_zero, hQd, hQ0]
  set c : K := d.coeff 0 with hcdef
  have hcne : c ≠ 0 := left_ne_zero_of_mul_eq_one hc1
  set P₂ : Polynomial K := Polynomial.C c * P₁ with hP2def
  set Q₂ : Polynomial K := Polynomial.C c * Q₁ with hQ2def
  have hP20 : P₂.coeff 0 = 1 := by rw [hP2def, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero]
                                   exact hc1
  have hQ20 : Q₂.coeff 0 = 1 := by rw [hQ2def, Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero]
                                   exact hc2
  have hP2ne : P₂ ≠ 0 := fun h => by rw [h] at hP20; simp at hP20
  have hQ2ne : Q₂ ≠ 0 := fun h => by rw [h] at hQ20; simp at hQ20
  -- Bézout for the normalized pair
  have hab2 : (Polynomial.C c⁻¹ * a) * P₂ + (Polynomial.C c⁻¹ * b) * Q₂ = 1 := by
    rw [hP2def, hQ2def]
    have : Polynomial.C c⁻¹ * Polynomial.C c = 1 := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hcne, Polynomial.C_1]
    calc Polynomial.C c⁻¹ * a * (Polynomial.C c * P₁)
          + Polynomial.C c⁻¹ * b * (Polynomial.C c * Q₁)
        = (Polynomial.C c⁻¹ * Polynomial.C c) * (a * P₁ + b * Q₁) := by ring
      _ = 1 := by rw [this, hab, one_mul]
  -- the normalized presentation of `F`
  have hPQ2 : (Q₂ : PowerSeries K) * F = (P₂ : PowerSeries K) := by
    have hcancel : ((d : Polynomial K) : PowerSeries K) * ((Q₁ : PowerSeries K) * F)
        = ((d : Polynomial K) : PowerSeries K) * (P₁ : PowerSeries K) := by
      have h1 : ((d * Q₁ : Polynomial K) : PowerSeries K) * F
          = ((d * P₁ : Polynomial K) : PowerSeries K) := by rw [hPd, hQd]; exact hPQ
      push_cast at h1
      rw [mul_assoc] at h1
      exact h1
    have hdne' : ((d : Polynomial K) : PowerSeries K) ≠ 0 := by
      simpa using fun h => hdne (Polynomial.coe_injective K (by simpa using h))
    have h2 : (Q₁ : PowerSeries K) * F = (P₁ : PowerSeries K) :=
      mul_left_cancel₀ hdne' hcancel
    rw [hP2def, hQ2def]
    push_cast
    rw [mul_assoc, h2]
  -- invariance of the numerator
  have hnum : ∀ σ : G, deningerPolyAct σ P₂ = P₂ := by
    intro σ
    have hcross := deningerCrossRelation_poly hF hPQ2 σ
    have hdvd : P₂ ∣ deningerPolyAct σ P₂ := by
      refine ⟨Polynomial.C c⁻¹ * a * deningerPolyAct σ P₂
        + Polynomial.C c⁻¹ * b * deningerPolyAct σ Q₂, ?_⟩
      calc deningerPolyAct σ P₂
          = deningerPolyAct σ P₂ * ((Polynomial.C c⁻¹ * a) * P₂
              + (Polynomial.C c⁻¹ * b) * Q₂) := by rw [hab2, mul_one]
        _ = (Polynomial.C c⁻¹ * a) * (deningerPolyAct σ P₂ * P₂)
              + (Polynomial.C c⁻¹ * b) * (deningerPolyAct σ P₂ * Q₂) := by ring
        _ = (Polynomial.C c⁻¹ * a) * (deningerPolyAct σ P₂ * P₂)
              + (Polynomial.C c⁻¹ * b) * (deningerPolyAct σ Q₂ * P₂) := by rw [hcross]
        _ = P₂ * (Polynomial.C c⁻¹ * a * deningerPolyAct σ P₂
              + Polynomial.C c⁻¹ * b * deningerPolyAct σ Q₂) := by ring
    obtain ⟨e, he⟩ := hdvd
    have hσne : deningerPolyAct σ P₂ ≠ 0 := by
      intro h
      apply hP2ne
      exact deningerPolyAct_injective σ (by rw [h, map_zero])
    have hene : e ≠ 0 := by
      intro h
      rw [h, mul_zero] at he
      exact hσne he
    have hdegσ : (deningerPolyAct σ P₂).natDegree = P₂.natDegree := by
      rw [deningerPolyAct]
      exact Polynomial.natDegree_map_eq_of_injective
        (MulSemiringAction.toRingHom G K σ).injective P₂
    have hdege : e.natDegree = 0 := by
      have := hdegσ
      rw [he, Polynomial.natDegree_mul hP2ne hene] at this
      omega
    have heC : e = Polynomial.C (e.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdege
    have hcoeff0 : (deningerPolyAct σ P₂).coeff 0 = 1 := by
      rw [deningerPolyAct_coeff, hP20, smul_one]
    have he0 : e.coeff 0 = 1 := by
      rw [he, Polynomial.mul_coeff_zero, hP20, one_mul] at hcoeff0
      exact hcoeff0
    rw [he, heC, he0, Polynomial.C_1, mul_one]
  -- invariance of the denominator
  have hden : ∀ σ : G, deningerPolyAct σ Q₂ = Q₂ := by
    intro σ
    have hcross := deningerCrossRelation_poly hF hPQ2 σ
    rw [hnum σ] at hcross
    have h2 : Q₂ * P₂ = deningerPolyAct σ Q₂ * P₂ := by rw [mul_comm Q₂ P₂]; exact hcross
    exact (mul_right_cancel₀ hP2ne h2).symm
  refine ⟨P₂, Q₂, ?_, ?_, hP20, hQ20, hPQ2⟩
  · intro σ n
    have h : (deningerPolyAct σ P₂).coeff n = P₂.coeff n := by rw [hnum σ]
    rwa [deningerPolyAct_coeff] at h
  · intro σ n
    have h : (deningerPolyAct σ Q₂).coeff n = Q₂.coeff n := by rw [hden σ]
    rwa [deningerPolyAct_coeff] at h

end RHTower
