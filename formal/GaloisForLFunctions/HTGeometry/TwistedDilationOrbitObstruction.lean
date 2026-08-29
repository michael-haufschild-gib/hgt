import GaloisForLFunctions.HTGeometry.DilatedCotModelOrbitObstruction

/-!
# The twisted multiplicative-orbit obstruction

The obstruction of `MultiplicativeOrbitNonSummability` says that a rational function with exactly
one pole on a multiplicative orbit is not a dilation coboundary `k(qX) - k(X)`.  The same orbit
argument applies verbatim to a *twisted* coboundary `γ k(qX) - k(X)` with a nonzero constant `γ`:
multiplication by a nonzero constant does not move poles, so the two-jump argument along the orbit
is unchanged.

The twisted form is what a first-order inhomogeneous `q`-difference equation with a nonconstant
multiplier produces after the multiplier is split off, and it is the shape in which the telescoping
hypothesis of the differential Ostrowski criterion has to be refuted for such an equation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

theorem algebraMap_ratFunc_eq_polynomialC' (x : K) :
    algebraMap K (RatFunc K) x = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C x) := by
  rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K), Polynomial.algebraMap_eq]

/-- A constant is regular everywhere. -/
theorem regularAt_algebraMap (γ w : K) : RegularAt (algebraMap K (RatFunc K) γ) w :=
  ⟨Polynomial.C γ, 1, by simp, by simp [algebraMap_ratFunc_eq_polynomialC']⟩

/-- Multiplying by a constant preserves regularity. -/
theorem regularAt_const_mul (γ : K) {f : RatFunc K} {w : K} (hf : RegularAt f w) :
    RegularAt (algebraMap K (RatFunc K) γ * f) w := by
  obtain ⟨p, q, hq, rfl⟩ := hf
  exact ⟨Polynomial.C γ * p, q, hq, by
    rw [map_mul, algebraMap_ratFunc_eq_polynomialC', mul_div_assoc]⟩

/-- Multiplying by a nonzero constant does not change regularity. -/
theorem regularAt_const_mul_iff {γ : K} (hγ : γ ≠ 0) (f : RatFunc K) (w : K) :
    RegularAt (algebraMap K (RatFunc K) γ * f) w ↔ RegularAt f w := by
  refine ⟨fun h => ?_, regularAt_const_mul γ⟩
  have h' := regularAt_const_mul γ⁻¹ h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hγ, map_one, one_mul] at h'

/-- **The twisted multiplicative-orbit obstruction.**  If `q` is not a root of unity and a rational
function `r` has a pole at `p₀ ≠ 0` and no other pole on the orbit `p₀ q^ℤ`, then the twisted
`q`-difference equation `r = γ k(qX) - k(X)` has no rational solution, for any nonzero constant
`γ`. -/
theorem not_twistedDilationTelescoped_of_unique_multOrbit_pole
    (q p₀ γ : K) (hq : q ≠ 0) (hp₀ : p₀ ≠ 0) (hγ : γ ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (r : RatFunc K) (hpole : ¬ RegularAt r p₀)
    (hunique : ∀ n : ℤ, n ≠ 0 → RegularAt r (p₀ * q ^ n)) :
    ¬ ∃ k : RatFunc K, r = algebraMap K (RatFunc K) γ * ratFuncScale q hq k - k := by
  rintro ⟨k, hr⟩
  refine not_telescoped_of_unique_orbit_pole_gen r (multOrbit q p₀)
    (multOrbit_injective hq hp₀ hqtor) (by simpa using hpole) (fun n hn => hunique n hn)
    ⟨k, algebraMap K (RatFunc K) γ * ratFuncScale q hq k, ?_, hr⟩
  intro n
  rw [regularAt_const_mul_iff hγ, regularAt_ratFuncScale, ← multOrbit_succ q p₀ hq n]

/-- **No twisted dilation coboundary is a constant differential character of the cotangent model.**
A nonzero Euler combination of the cotangent model has a pole at `1` and no other pole, so it stays
a single-orbit pole after adding any constant, and the twisted orbit obstruction applies. -/
theorem not_twistedDilationTelescoped_eulerCombination_cotModel [CharZero K]
    (q γ c γ₀ : K) (hq : q ≠ 0) (hγ : γ ≠ 0) (hc : c ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    (a : ℕ → K) (r : ℕ) (har : a r ≠ 0) :
    ¬ ∃ k : RatFunc K,
      eulerCombination a r (cotModel c) + algebraMap K (RatFunc K) γ₀
        = algebraMap K (RatFunc K) γ * ratFuncScale q hq k - k := by
  refine not_twistedDilationTelescoped_of_unique_multOrbit_pole q 1 γ hq one_ne_zero hγ hqtor _
    ?_ ?_
  · exact not_regularAt_add_left
      (not_regularAt_one_eulerCombination_cotModel a c hc r har) (regularAt_algebraMap γ₀ 1)
  · intro n hn
    rw [one_mul]
    exact (regularAt_of_ne_one_eulerCombination_cotModel a c r (hqtor n hn)).add
      (regularAt_algebraMap γ₀ _)

end

end GaloisForLFunctions.HTGeometry
