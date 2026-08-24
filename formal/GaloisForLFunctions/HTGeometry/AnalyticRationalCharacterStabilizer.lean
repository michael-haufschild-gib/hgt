import GaloisForLFunctions.HTGeometry.UnitCharacterStabilizerRank
import GaloisForLFunctions.HTGeometry.PolyannulusTorusUniqueness
import GaloisForLFunctions.HTGeometry.AlgebraicIndependenceFromDifferentials

/-!
# Active-character invariance of a rational analytic observable

A rational presentation regular on a polyannulus transports analytic Fourier
symmetry into the abstract multivariate rational function field.  Equality on
the polyannulus is cleared of denominators and then promoted to a polynomial
identity on the full affine space.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {r : ℕ}

/-- A rational presentation of an analytic polyannulus observable is fixed by
all unitary scalings annihilating its active Fourier support. -/
theorem rationalTorusScaleEquiv_fixed_of_analytic_presentation
    {ρ : Fin r → ℝ} (hρ : ∀ i, 0 < ρ i)
    {F : (Fin r → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ))
    (P Q : MvPolynomial (Fin r) ℂ)
    (hQ : ∀ z ∈ polyannulus ρ, MvPolynomial.aeval z Q ≠ 0)
    (hrep : ∀ z ∈ polyannulus ρ,
      F z = MvPolynomial.aeval z P / MvPolynomial.aeval z Q)
    {u : Fin r → ℂˣ} (hu : u ∈ unitCharacterStabilizer (activeSupport F)) :
    rationalTorusScaleEquiv u
        (MvPolynomial.aeval (rationalTorusCoordinate (C := ℂ) (r := r)) P /
          MvPolynomial.aeval (rationalTorusCoordinate (C := ℂ) (r := r)) Q) =
      MvPolynomial.aeval (rationalTorusCoordinate (C := ℂ) (r := r)) P /
        MvPolynomial.aeval (rationalTorusCoordinate (C := ℂ) (r := r)) Q := by
  classical
  let a : Fin r → ℂ := fun i => (u i : ℂ)
  obtain ⟨y, hy⟩ := unitTorus_subset_range_circleCoords hu.1
  have hchar : ∀ m ∈ activeSupport F, UnitAddTorus.mFourier m y = 1 := by
    intro m hm
    rw [← charPow_circleCoords, hy]
    exact hu.2 m hm
  have hinv : ∀ z ∈ polyannulus ρ, F (torusScale a z) = F z := by
    intro z hz
    have h := eqOn_comp_torusScale_of_mFourier_eq_one hρ hF hchar z hz
    simpa [a, hy] using h
  let R : MvPolynomial (Fin r) ℂ :=
    scaleMvPolynomial a P * Q - P * scaleMvPolynomial a Q
  have hRzero : R = 0 := by
    apply mvPolynomial_eq_zero_of_eqOn_zero_isOpen
      (isOpen_polyannulus ρ) (one_mem_polyannulus hρ)
    intro z hz
    have huz : torusScale a z ∈ polyannulus ρ :=
      torusScale_mem_polyannulus hu.1 hz
    have hdiv :
        MvPolynomial.aeval (torusScale a z) P /
            MvPolynomial.aeval (torusScale a z) Q =
          MvPolynomial.aeval z P / MvPolynomial.aeval z Q := by
      rw [← hrep (torusScale a z) huz, ← hrep z hz]
      exact hinv z hz
    have hcross := (div_eq_div_iff (hQ (torusScale a z) huz) (hQ z hz)).mp hdiv
    have hscaleP : MvPolynomial.aeval z (scaleMvPolynomial a P) =
        MvPolynomial.aeval (torusScale a z) P := by
      rw [aeval_scaleMvPolynomial]
      rfl
    have hscaleQ : MvPolynomial.aeval z (scaleMvPolynomial a Q) =
        MvPolynomial.aeval (torusScale a z) Q := by
      rw [aeval_scaleMvPolynomial]
      rfl
    have hzero : MvPolynomial.aeval z R = 0 := by
      rw [show R = scaleMvPolynomial a P * Q -
          P * scaleMvPolynomial a Q by rfl, map_sub, map_mul, map_mul,
        hscaleP, hscaleQ]
      exact sub_eq_zero.mpr hcross
    simpa [MvPolynomial.aeval_def] using hzero
  have hpoly : scaleMvPolynomial a P * Q = P * scaleMvPolynomial a Q := by
    exact sub_eq_zero.mp (by simpa [R] using hRzero)
  let x := rationalTorusCoordinate (C := ℂ) (r := r)
  have haeval0 : ∀ W : MvPolynomial (Fin r) ℂ,
      MvPolynomial.aeval x W = 0 → W = 0 :=
    algebraicIndependent_iff.mp
      (algebraicIndependent_rationalTorusCoordinate (C := ℂ) (r := r))
  have hQpoly : Q ≠ 0 := by
    intro h
    have := hQ (fun _ => (1 : ℂ)) (one_mem_polyannulus hρ)
    rw [h, map_zero] at this
    exact this rfl
  have hscaleQpoly : scaleMvPolynomial a Q ≠ 0 := by
    intro h
    apply hQpoly
    apply (mvPolynomialUnitScaleEquiv u).injective
    rw [map_zero]
    simpa [mvPolynomialUnitScaleEquiv_apply,
      scaleMvPolynomial_eq_mvPolynomialDiagonalScaleRing] using h
  have hxQ : MvPolynomial.aeval x Q ≠ 0 := fun h => hQpoly (haeval0 Q h)
  have hxscaleQ : MvPolynomial.aeval x (scaleMvPolynomial a Q) ≠ 0 :=
    fun h => hscaleQpoly (haeval0 (scaleMvPolynomial a Q) h)
  rw [map_div₀, rationalTorusScaleEquiv_aeval,
    rationalTorusScaleEquiv_aeval]
  apply (div_eq_div_iff hxscaleQ hxQ).mpr
  have := congrArg (MvPolynomial.aeval x) hpoly
  simpa only [map_mul] using this

end

end GaloisForLFunctions.HTGeometry
