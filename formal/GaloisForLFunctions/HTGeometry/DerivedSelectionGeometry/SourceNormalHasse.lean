import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.SourceNormalEquation

/-!
# Hasse quotient for the source normal equation

The identity-fibre source boundary is the anti-diagonal line.  Coordinate sum has precisely this
kernel and is surjective, so the quotient is canonically the residual global charge line.  Two
local source-coordinate pairs define the same global class exactly when their sums agree.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

universe u v

noncomputable section

variable {R : Type u} [CommRing R]

/-- Coordinate sum as the global residual-charge map on a pair of local source coordinates. -/
def pairCoordinateSum : (R × R) →ₗ[R] R where
  toFun x := x.1 + x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, mul_add]

@[simp] theorem pairCoordinateSum_apply (x : R × R) :
    pairCoordinateSum x = x.1 + x.2 := rfl

/-- Every global residual charge is realized by a pair of local source coordinates. -/
theorem pairCoordinateSum_surjective : Function.Surjective (pairCoordinateSum (R := R)) := by
  intro r
  exact ⟨(r, 0), by simp⟩

/-- The only locally invisible pair is the anti-diagonal boundary line. -/
theorem pairCoordinateSum_ker :
    LinearMap.ker (pairCoordinateSum (R := R)) =
      Submodule.span R {((-1 : R), (1 : R))} := by
  apply le_antisymm
  · intro x hx
    have hsum : x.1 + x.2 = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hfst : x.1 = -x.2 := by
      calc
        x.1 = x.1 + x.2 - x.2 := by abel
        _ = -x.2 := by rw [hsum]; simp
    have heq : x = x.2 • ((-1 : R), (1 : R)) := by
      ext <;> simp [hfst]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    change pairCoordinateSum ((-1 : R), (1 : R)) = 0
    simp

/-- Pair coordinates modulo the anti-diagonal boundary are exactly their global coordinate sum. -/
noncomputable def pairCoordinateSumQuotientEquiv :
    ((R × R) ⧸ Submodule.span R {((-1 : R), (1 : R))}) ≃ₗ[R] R :=
  (Submodule.quotEquivOfEq _ _ (pairCoordinateSum_ker (R := R)).symm).trans
    (LinearMap.quotKerEquivOfSurjective
      (pairCoordinateSum (R := R)) pairCoordinateSum_surjective)

/-- The coordinate-sum quotient equivalence is induced by coordinate sum. -/
@[simp] theorem pairCoordinateSumQuotientEquiv_mk (x : R × R) :
    pairCoordinateSumQuotientEquiv (R := R) (Submodule.Quotient.mk x) = x.1 + x.2 := by
  simp [pairCoordinateSumQuotientEquiv]

variable {S : Type v} [AddCommGroup S] [Module R S]
variable {tauS : S →ₗ[R] S} {eps : S →ₗ[R] R} {c : R}

/-- At the identity fibre, the literal source quotient is exactly the global coordinate-sum line. -/
noncomputable def srcBoundaryQuotientEquivCoordinateSum_of_eq_one
    (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hc : IsUnit c) :
    ((R × R) ⧸ srcBoundary tauS eps (1 : R) c) ≃ₗ[R] R :=
  (Submodule.quotEquivOfEq _ _
    (srcBoundary_eq_antidiagonal_of_eq_one hinv heps hc)).trans
      pairCoordinateSumQuotientEquiv

/-- The literal identity-fibre quotient equivalence sends a source pair to its coordinate sum. -/
@[simp] theorem srcBoundaryQuotientEquivCoordinateSum_of_eq_one_mk
    (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hc : IsUnit c) (x : R × R) :
    srcBoundaryQuotientEquivCoordinateSum_of_eq_one hinv heps hc
        (Submodule.Quotient.mk x) = x.1 + x.2 := by
  simp [srcBoundaryQuotientEquivCoordinateSum_of_eq_one]

/-- Identity-fibre source pairs are globally congruent exactly when their coordinate-sum charges
agree. -/
theorem srcBoundary_congr_hasse_iff_of_eq_one
    (hinv : ∀ x, eps (tauS x) = eps x)
    (heps : Function.Surjective eps) (hc : IsUnit c) (x y : R × R) :
    x - y ∈ srcBoundary tauS eps (1 : R) c ↔
      pairCoordinateSum x = pairCoordinateSum y := by
  rw [srcBoundary_eq_antidiagonal_of_eq_one hinv heps hc,
    ← pairCoordinateSum_ker]
  change pairCoordinateSum (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

end


end GaloisForLFunctions.HTGeometry.DerivedSelection
