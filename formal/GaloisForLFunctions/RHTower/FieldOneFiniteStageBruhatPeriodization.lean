import GaloisForLFunctions.RHTower.FieldOneFiniteStageBruhatOrbitSummability

/-!
# Descent of finite-stage Bruhat periodization to idele classes

The absolutely convergent `Q_S*`-orbit series is invariant under diagonal `S`-unit scaling.
It therefore descends from finite-stage ideles to the literal idele-class group `C_S`.  This is the
pointwise source map `Σ` in Connes--Marcolli Lemma 2.29 and Proposition 2.30, before multiplication
by the module half-density and the proof of `L²` landing.
-/

open scoped TensorProduct algebraMap

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

theorem fieldOneFiniteStageBruhatPureTensorOrbit_diagonal_mul
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (φ : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S)
    (r q : fieldOneSUnitSubgroup S) :
    fieldOneFiniteStageBruhatPureTensorOrbit S f φ
        (fieldOneFiniteStageDiagonalUnit S r.1 * u) q =
      fieldOneFiniteStageBruhatPureTensorOrbit S f φ u (q * r) := by
  simp only [fieldOneFiniteStageBruhatPureTensorOrbit]
  congr 2
  · change (((r.1 : ℚ) : ℝ) * (u.1 : ℝ)) * ((q.1 : ℚ) : ℝ) =
      (u.1 : ℝ) * ((((q * r).1 : ℚˣ) : ℚ) : ℝ)
    push_cast
    ring
  · funext v
    change algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          (algebraMap ℚ (v.1.adicCompletion ℚ) (r.1 : ℚ) *
            (u.2 v : v.1.adicCompletion ℚ)) =
      algebraMap ℚ (v.1.adicCompletion ℚ) ((q.1 : ℚ) * (r.1 : ℚ)) *
        (u.2 v : v.1.adicCompletion ℚ)
    rw [map_mul]
    ring

theorem fieldOneFiniteStageBruhatOrbit_diagonal_mul
    (S : Finset (HeightOneSpectrum ℤ))
    (t : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S)
    (r q : fieldOneSUnitSubgroup S) :
    fieldOneFiniteStageBruhatOrbit S t
        (fieldOneFiniteStageDiagonalUnit S r.1 * u) q =
      fieldOneFiniteStageBruhatOrbit S t u (q * r) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [fieldOneFiniteStageBruhatOrbit]
  | tmul f φ =>
      simpa only [fieldOneFiniteStageBruhatOrbit_tmul] using
        fieldOneFiniteStageBruhatPureTensorOrbit_diagonal_mul S f φ u r q
  | add x y hx hy =>
      change
        (TensorProduct.lift
          (fieldOneFiniteStageBruhatOrbitBilinear S
            (fieldOneFiniteStageDiagonalUnit S r.1 * u) q)) (x + y) =
          (TensorProduct.lift
            (fieldOneFiniteStageBruhatOrbitBilinear S u (q * r))) (x + y)
      rw [map_add, map_add]
      change
        (TensorProduct.lift
            (fieldOneFiniteStageBruhatOrbitBilinear S
              (fieldOneFiniteStageDiagonalUnit S r.1 * u) q)) x =
          (TensorProduct.lift
            (fieldOneFiniteStageBruhatOrbitBilinear S u (q * r))) x at hx
      change
        (TensorProduct.lift
            (fieldOneFiniteStageBruhatOrbitBilinear S
              (fieldOneFiniteStageDiagonalUnit S r.1 * u) q)) y =
          (TensorProduct.lift
            (fieldOneFiniteStageBruhatOrbitBilinear S u (q * r))) y at hy
      rw [hx, hy]

/-- The absolutely convergent periodization is invariant under diagonal `S`-unit scaling. -/
theorem fieldOneFiniteStageBruhatPeriodization_diagonal_mul
    (S : Finset (HeightOneSpectrum ℤ))
    (t : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S)
    (r : fieldOneSUnitSubgroup S) :
    fieldOneFiniteStageBruhatPeriodization S t
        (fieldOneFiniteStageDiagonalUnit S r.1 * u) =
      fieldOneFiniteStageBruhatPeriodization S t u := by
  rw [fieldOneFiniteStageBruhatPeriodization,
    fieldOneFiniteStageBruhatPeriodization]
  calc
    (∑' q, fieldOneFiniteStageBruhatOrbit S t
      (fieldOneFiniteStageDiagonalUnit S r.1 * u) q) =
        ∑' q, fieldOneFiniteStageBruhatOrbit S t u (q * r) := by
          apply tsum_congr
          exact fieldOneFiniteStageBruhatOrbit_diagonal_mul S t u r
    _ = ∑' q, fieldOneFiniteStageBruhatOrbit S t u q := by
      change (∑' q, fieldOneFiniteStageBruhatOrbit S t u
        ((Equiv.mulRight r) q)) = _
      exact (Equiv.mulRight r).tsum_eq
        (fieldOneFiniteStageBruhatOrbit S t u)

/-- The finite-stage periodization `Σ(t)` as a well-defined function on the literal idele-class
group `C_S`. -/
def fieldOneFiniteStageBruhatPeriodizationClass
    (S : Finset (HeightOneSpectrum ℤ))
    (t : FieldOneFiniteStageBruhatSchwartz S)
    (c : FieldOneFiniteStageIdeleClassGroup S) : ℂ :=
  Quotient.liftOn' c
    (fieldOneFiniteStageBruhatPeriodization S t)
    (by
      intro u v huv
      rw [QuotientGroup.leftRel_apply] at huv
      change u⁻¹ * v ∈ Subgroup.map
        (fieldOneFiniteStageDiagonalUnit S) (fieldOneSUnitSubgroup S) at huv
      rw [Subgroup.mem_map] at huv
      rcases huv with ⟨d, hrest⟩
      rcases hrest with ⟨hdS, hd⟩
      let q : fieldOneSUnitSubgroup S := ⟨d, hdS⟩
      have hd' : fieldOneFiniteStageDiagonalUnit S q.1 = u⁻¹ * v := hd
      have hv : v = fieldOneFiniteStageDiagonalUnit S q.1 * u := by
        calc
          v = u * (u⁻¹ * v) := by simp
          _ = u * fieldOneFiniteStageDiagonalUnit S q.1 := by rw [← hd']
          _ = fieldOneFiniteStageDiagonalUnit S q.1 * u := mul_comm _ _
      rw [hv, fieldOneFiniteStageBruhatPeriodization_diagonal_mul])

@[simp]
theorem fieldOneFiniteStageBruhatPeriodizationClass_mk
    (S : Finset (HeightOneSpectrum ℤ))
    (t : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageBruhatPeriodizationClass S t
        (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) u) =
      fieldOneFiniteStageBruhatPeriodization S t u :=
  rfl

end

end GaloisForLFunctions.RHTower
