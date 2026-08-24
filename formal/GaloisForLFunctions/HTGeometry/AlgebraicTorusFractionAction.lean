import GaloisForLFunctions.HTGeometry.MvPolynomialDiagonalScaleDomain
import GaloisForLFunctions.HTGeometry.FractionFieldFunctorial
import GaloisForLFunctions.HTGeometry.TorusInvariantField

/-!
# Algebraic torus action on a rational function field

Coordinatewise multiplication by nonzero constants defines an algebra
automorphism of a multivariate rational function field.  A minimal-denominator
argument then shows that every rational function fixed by a family of such
scalings has a numerator and denominator supported in one common character
class.  Unlike the differential-torsor action, this construction applies to
coordinates satisfying diagonal first-order differential equations.
-/

open scoped nonZeroDivisors

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Field C] {r : ℕ}

/-- Coordinatewise unit scaling on a multivariate polynomial ring. -/
def mvPolynomialUnitScaleEquiv (u : Fin r → Cˣ) :
    MvPolynomial (Fin r) C ≃ₐ[C] MvPolynomial (Fin r) C where
  toFun := GaloisForLFunctions.mvPolynomialDiagonalScaleRing fun i => (u i : C)
  invFun := GaloisForLFunctions.mvPolynomialDiagonalScaleRing fun i => ((u i)⁻¹ : C)
  left_inv P := by
    simpa using GaloisForLFunctions.mvPolynomialDiagonalScaleRing_inv_apply
      (fun i => (u i : C)) (fun i => (u i).ne_zero) P
  right_inv P := by
    simpa using GaloisForLFunctions.mvPolynomialDiagonalScaleRing_inv_apply
      (fun i => ((u i)⁻¹ : C)) (fun i => inv_ne_zero (Units.ne_zero (u i))) P
  map_add' := map_add _
  map_mul' := map_mul _
  commutes' := (GaloisForLFunctions.mvPolynomialDiagonalScaleRing _).commutes

@[simp] theorem mvPolynomialUnitScaleEquiv_apply (u : Fin r → Cˣ)
    (P : MvPolynomial (Fin r) C) :
    mvPolynomialUnitScaleEquiv u P =
      GaloisForLFunctions.mvPolynomialDiagonalScaleRing (fun i => (u i : C)) P := rfl

@[simp] theorem mvPolynomialUnitScaleEquiv_X (u : Fin r → Cˣ) (i : Fin r) :
    mvPolynomialUnitScaleEquiv u (MvPolynomial.X i) =
      MvPolynomial.C (u i : C) * MvPolynomial.X i := by
  simp [mvPolynomialUnitScaleEquiv, GaloisForLFunctions.mvPolynomialDiagonalScaleRing]

/-- Coordinatewise unit scaling extended to the rational function field. -/
def rationalTorusScaleEquiv (u : Fin r → Cˣ) :
    FractionRing (MvPolynomial (Fin r) C) ≃ₐ[C]
      FractionRing (MvPolynomial (Fin r) C) where
  toRingEquiv := fracRingEquiv (mvPolynomialUnitScaleEquiv u).toRingEquiv
  commutes' c := by
    change fracRingEquiv (mvPolynomialUnitScaleEquiv u).toRingEquiv
      (algebraMap (MvPolynomial (Fin r) C)
        (FractionRing (MvPolynomial (Fin r) C)) (MvPolynomial.C c)) =
      algebraMap (MvPolynomial (Fin r) C)
        (FractionRing (MvPolynomial (Fin r) C)) (MvPolynomial.C c)
    rw [fracRingEquiv_algebraMap]
    change algebraMap (MvPolynomial (Fin r) C)
      (FractionRing (MvPolynomial (Fin r) C))
        (mvPolynomialUnitScaleEquiv u (MvPolynomial.C c)) = _
    simp [mvPolynomialUnitScaleEquiv,
      GaloisForLFunctions.mvPolynomialDiagonalScaleRing]

/-- Canonical coordinate in the multivariate rational function field. -/
def rationalTorusCoordinate (i : Fin r) :
    FractionRing (MvPolynomial (Fin r) C) :=
  algebraMap (MvPolynomial (Fin r) C)
    (FractionRing (MvPolynomial (Fin r) C)) (MvPolynomial.X i)

@[simp] theorem rationalTorusScaleEquiv_coordinate
    (u : Fin r → Cˣ) (i : Fin r) :
    rationalTorusScaleEquiv u (rationalTorusCoordinate i) =
      algebraMap C (FractionRing (MvPolynomial (Fin r) C)) (u i : C) *
        rationalTorusCoordinate i := by
  change fracRingEquiv (mvPolynomialUnitScaleEquiv u).toRingEquiv
      (algebraMap (MvPolynomial (Fin r) C)
        (FractionRing (MvPolynomial (Fin r) C)) (MvPolynomial.X i)) = _
  rw [fracRingEquiv_algebraMap]
  change algebraMap (MvPolynomial (Fin r) C)
      (FractionRing (MvPolynomial (Fin r) C))
        (mvPolynomialUnitScaleEquiv u (MvPolynomial.X i)) = _
  rw [mvPolynomialUnitScaleEquiv_X, map_mul]
  rfl

theorem rationalTorusCoordinate_ne_zero (i : Fin r) :
    rationalTorusCoordinate (C := C) i ≠ 0 := by
  intro h
  have hX : (MvPolynomial.X i : MvPolynomial (Fin r) C) ≠ 0 :=
    MvPolynomial.X_ne_zero i
  apply hX
  apply IsFractionRing.injective (MvPolynomial (Fin r) C)
    (FractionRing (MvPolynomial (Fin r) C))
  simpa [rationalTorusCoordinate] using h

@[simp] theorem aeval_rationalTorusCoordinate_eq_algebraMap
    (P : MvPolynomial (Fin r) C) :
    MvPolynomial.aeval (rationalTorusCoordinate (C := C) (r := r)) P =
      algebraMap (MvPolynomial (Fin r) C)
        (FractionRing (MvPolynomial (Fin r) C)) P := by
  let φ : MvPolynomial (Fin r) C →ₐ[C]
      FractionRing (MvPolynomial (Fin r) C) :=
    { toRingHom := algebraMap (MvPolynomial (Fin r) C)
        (FractionRing (MvPolynomial (Fin r) C))
      commutes' := fun c => by rfl }
  have hφ : MvPolynomial.aeval
      (rationalTorusCoordinate (C := C) (r := r)) = φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [rationalTorusCoordinate, φ]
  rw [hφ]
  rfl

/-- Canonical rational-function coordinates are algebraically independent. -/
theorem algebraicIndependent_rationalTorusCoordinate :
    AlgebraicIndependent C (rationalTorusCoordinate (C := C) (r := r)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro P Q hPQ
  exact (IsFractionRing.injective (MvPolynomial (Fin r) C)
    (FractionRing (MvPolynomial (Fin r) C))) (by simpa using hPQ)

theorem scaleMvPolynomial_eq_mvPolynomialDiagonalScaleRing
    (a : Fin r → C) (P : MvPolynomial (Fin r) C) :
    scaleMvPolynomial a P =
      GaloisForLFunctions.mvPolynomialDiagonalScaleRing a P := by
  have h := aeval_scaleMvPolynomial a
    (MvPolynomial.X : Fin r → MvPolynomial (Fin r) C) P
  simpa [GaloisForLFunctions.mvPolynomialDiagonalScaleRing] using h

theorem rationalTorusScaleEquiv_aeval (u : Fin r → Cˣ)
    (P : MvPolynomial (Fin r) C) :
    rationalTorusScaleEquiv u
        (MvPolynomial.aeval (rationalTorusCoordinate (C := C) (r := r)) P) =
      MvPolynomial.aeval (rationalTorusCoordinate (C := C) (r := r))
        (scaleMvPolynomial (fun i => (u i : C)) P) := by
  have hcomp := MvPolynomial.comp_aeval_apply
    (rationalTorusCoordinate (C := C) (r := r))
    (rationalTorusScaleEquiv u).toAlgHom P
  change (rationalTorusScaleEquiv u).toAlgHom
      (MvPolynomial.aeval (rationalTorusCoordinate (C := C) (r := r)) P) = _
  rw [hcomp, aeval_scaleMvPolynomial]
  apply congrArg (fun y => MvPolynomial.aeval y P)
  funext i
  exact rationalTorusScaleEquiv_coordinate u i

/-- Character of a natural exponent under coordinate scaling. -/
def rationalScaleChar (u : Fin r → Cˣ) (e : Fin r →₀ ℕ) : C :=
  ∏ i, (u i : C) ^ e i

/-- A rational function fixed by a set of coordinate scalings has a numerator
and denominator supported in one common character class. -/
theorem exists_rationalTorusScale_eigen_representation
    {S : Set (Fin r → Cˣ)}
    {z : FractionRing (MvPolynomial (Fin r) C)}
    (hfix : ∀ u ∈ S, rationalTorusScaleEquiv u z = z) :
    ∃ (d : Fin r →₀ ℕ) (P Q : MvPolynomial (Fin r) C),
      d ∈ Q.support ∧
      z * MvPolynomial.aeval
          (rationalTorusCoordinate (C := C) (r := r)) Q =
        MvPolynomial.aeval
          (rationalTorusCoordinate (C := C) (r := r)) P ∧
      (∀ e ∈ Q.support, ∀ u ∈ S,
        rationalScaleChar u e = rationalScaleChar u d) ∧
      (∀ e ∈ P.support, ∀ u ∈ S,
        rationalScaleChar u e = rationalScaleChar u d) := by
  classical
  let x := rationalTorusCoordinate (C := C) (r := r)
  have haeval0 : ∀ W : MvPolynomial (Fin r) C,
      MvPolynomial.aeval x W = 0 → W = 0 :=
    algebraicIndependent_iff.mp
      (algebraicIndependent_rationalTorusCoordinate (C := C) (r := r))
  obtain ⟨P₀, Q₀, hQ₀mem, hfrac⟩ :=
    IsFractionRing.div_surjective (MvPolynomial (Fin r) C) z
  have hQ₀poly : Q₀ ≠ 0 := by
    intro h
    subst Q₀
    simpa using hQ₀mem
  have hQ₀ : MvPolynomial.aeval x Q₀ ≠ 0 := by
    intro h
    exact hQ₀poly (haeval0 Q₀ h)
  have hPQ₀ : z * MvPolynomial.aeval x Q₀ = MvPolynomial.aeval x P₀ := by
    rw [aeval_rationalTorusCoordinate_eq_algebraMap,
      aeval_rationalTorusCoordinate_eq_algebraMap]
    rw [← hfrac, div_mul_cancel₀]
    simpa [x] using hQ₀
  have hexists : ∃ n, ∃ P Q : MvPolynomial (Fin r) C,
      Q ≠ 0 ∧ Q.support.card = n ∧
        z * MvPolynomial.aeval x Q = MvPolynomial.aeval x P :=
    ⟨Q₀.support.card, P₀, Q₀, hQ₀poly, rfl, hPQ₀⟩
  obtain ⟨P, Q, hQne, hQcard, hPQeq⟩ := Nat.find_spec hexists
  have hmin : ∀ m, m < Nat.find hexists →
      ¬ ∃ P' Q' : MvPolynomial (Fin r) C,
        Q' ≠ 0 ∧ Q'.support.card = m ∧
          z * MvPolynomial.aeval x Q' = MvPolynomial.aeval x P' :=
    fun m hm => Nat.find_min hexists hm
  have hQsupp : Q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hQne (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨d, hd⟩ := hQsupp
  let twist : (Fin r → Cˣ) → MvPolynomial (Fin r) C →
      MvPolynomial (Fin r) C := fun u W =>
    scaleMvPolynomial (fun i => (u i : C)) W -
      MvPolynomial.C (rationalScaleChar u d) * W
  have hcoeff_twist : ∀ (u : Fin r → Cˣ) (W : MvPolynomial (Fin r) C)
      (e : Fin r →₀ ℕ),
      MvPolynomial.coeff e (twist u W) =
        (rationalScaleChar u e - rationalScaleChar u d) *
          MvPolynomial.coeff e W := by
    intro u W e
    simp only [twist, MvPolynomial.coeff_sub, coeff_scaleMvPolynomial,
      MvPolynomial.coeff_C_mul, rationalScaleChar]
    ring
  have haeval_twist : ∀ (u : Fin r → Cˣ) (W : MvPolynomial (Fin r) C),
      MvPolynomial.aeval x (twist u W) =
        rationalTorusScaleEquiv u (MvPolynomial.aeval x W) -
          algebraMap C (FractionRing (MvPolynomial (Fin r) C))
              (rationalScaleChar u d) * MvPolynomial.aeval x W := by
    intro u W
    rw [show twist u W = scaleMvPolynomial (fun i => (u i : C)) W -
        MvPolynomial.C (rationalScaleChar u d) * W by rfl,
      map_sub, map_mul, MvPolynomial.aeval_C,
      rationalTorusScaleEquiv_aeval]
  have hden : ∀ (u : Fin r → Cˣ), u ∈ S →
      z * MvPolynomial.aeval x (twist u Q) =
        MvPolynomial.aeval x (twist u P) := by
    intro u hu
    rw [haeval_twist u Q, haeval_twist u P, mul_sub]
    have h1 : z * rationalTorusScaleEquiv u (MvPolynomial.aeval x Q) =
        rationalTorusScaleEquiv u (MvPolynomial.aeval x P) := by
      rw [← hfix u hu, ← map_mul, hPQeq]
    have h2 : z *
        (algebraMap C (FractionRing (MvPolynomial (Fin r) C))
            (rationalScaleChar u d) * MvPolynomial.aeval x Q) =
          algebraMap C (FractionRing (MvPolynomial (Fin r) C))
              (rationalScaleChar u d) * MvPolynomial.aeval x P := by
      linear_combination
        (algebraMap C (FractionRing (MvPolynomial (Fin r) C))
          (rationalScaleChar u d)) * hPQeq
    rw [h1, h2]
  have htwistQ : ∀ (u : Fin r → Cˣ), u ∈ S → twist u Q = 0 := by
    intro u hu
    by_contra hne
    have hsub : (twist u Q).support ⊆ Q.support.erase d := by
      intro e he
      rw [MvPolynomial.mem_support_iff, hcoeff_twist] at he
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · rintro rfl
        exact he (by rw [sub_self, zero_mul])
      · exact MvPolynomial.mem_support_iff.mpr fun h =>
          he (by rw [h, mul_zero])
    have hcard : (twist u Q).support.card < Nat.find hexists := by
      calc
        (twist u Q).support.card ≤ (Q.support.erase d).card :=
          Finset.card_le_card hsub
        _ < Q.support.card := Finset.card_erase_lt_of_mem hd
        _ = Nat.find hexists := hQcard
    exact hmin _ hcard ⟨twist u P, twist u Q, hne, rfl, hden u hu⟩
  have htwistP : ∀ (u : Fin r → Cˣ), u ∈ S → twist u P = 0 := by
    intro u hu
    apply haeval0
    rw [← hden u hu, htwistQ u hu, map_zero, mul_zero]
  have hsingle : ∀ W : MvPolynomial (Fin r) C,
      (∀ u ∈ S, twist u W = 0) →
      ∀ e ∈ W.support, ∀ u ∈ S,
        rationalScaleChar u e = rationalScaleChar u d := by
    intro W hW e he u hu
    have hc := congrArg (MvPolynomial.coeff e) (hW u hu)
    rw [hcoeff_twist, MvPolynomial.coeff_zero] at hc
    rcases mul_eq_zero.mp hc with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (MvPolynomial.mem_support_iff.mp he)
  exact ⟨d, P, Q, hd, hPQeq, hsingle Q htwistQ, hsingle P htwistP⟩

end

end GaloisForLFunctions.HTGeometry
