import GaloisForLFunctions.HTGeometry.DerivationIterateLeibniz
import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The Taylor morphism of a differential ring

For a differential ring containing the rationals, the exponential generating series of the jet
sequence of an element,

```text
τ a = Σ_n (δ^n a / n!) T^n,
```

is an injective ring homomorphism into the formal power series ring which turns the derivation into
formal differentiation.  It is the algebraic form of expanding a function in its Taylor series at
the origin: the jets of an element *are* a formal arc, and a polynomial relation among elements
holds exactly when the corresponding relation among their arcs holds.

The two structural consequences used later are that the arc of a polynomial expression is that
polynomial evaluated on the arcs, and that the elements killed by `δ^n` are exactly those whose arc
has no coefficient in degree `n` or beyond.
-/

open scoped Differential
open PowerSeries

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

/-! ### Elementary jet identities -/

theorem differentialJet_succ_apply (n : ℕ) (a : R) :
    differentialJet (n + 1) a = differentialJet n a′ := by
  rw [differentialJet_add n 1]
  rfl

@[simp] theorem differentialJet_zero_elt_differentialTaylorMorphism (n : ℕ) : differentialJet n (0 : R) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [differentialJet_succ, ih, map_zero]

theorem differentialJet_eq_zero_of_deriv_eq_zero {a : R} (ha : a′ = 0) {n : ℕ} (hn : 0 < n) :
    differentialJet n a = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [differentialJet_succ_apply, ha, differentialJet_zero_elt_differentialTaylorMorphism]

/-- Once a jet vanishes every later jet vanishes. -/
theorem differentialJet_eq_zero_of_le {a : R} {n : ℕ} (h : differentialJet n a = 0) {m : ℕ}
    (hm : n ≤ m) : differentialJet m a = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by ring, differentialJet_succ,
        ih (Nat.le_add_right n k), map_zero]

/-! ### The Taylor morphism -/

variable [Algebra ℚ R]

/-- The image of `1/n!` in a differential ℚ-algebra. -/
def invFactorialCast (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) : R :=
  algebraMap ℚ R ((n.factorial : ℚ)⁻¹)

omit [Differential R] in
@[simp] theorem invFactorialCast_zero : invFactorialCast R 0 = 1 := by
  simp [invFactorialCast]

omit [Differential R] in
@[simp] theorem invFactorialCast_one : invFactorialCast R 1 = 1 := by
  simp [invFactorialCast]

omit [Differential R] in
/-- The binomial identity in the form used by the Taylor product rule. -/
theorem invFactorialCast_mul_invFactorialCast {n k : ℕ} (h : k ≤ n) :
    invFactorialCast R k * invFactorialCast R (n - k)
      = (Nat.choose n k : R) * invFactorialCast R n := by
  have hq : ((k.factorial : ℚ))⁻¹ * (((n - k).factorial : ℚ))⁻¹
      = (Nat.choose n k : ℚ) * ((n.factorial : ℚ))⁻¹ := by
    have hkey : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ)
        = (n.factorial : ℚ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (Nat.choose_mul_factorial_mul_factorial h)
    have h1 : ((k.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (((n - k).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : ((n.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    linarith [hkey]
  unfold invFactorialCast
  rw [← map_mul, hq, map_mul, map_natCast]

/-- The exponential generating series of the jet sequence of an element. -/
def differentialTaylor (a : R) : PowerSeries R :=
  PowerSeries.mk fun n => invFactorialCast R n * differentialJet n a

@[simp] theorem coeff_differentialTaylor (n : ℕ) (a : R) :
    PowerSeries.coeff n (differentialTaylor a) = invFactorialCast R n * differentialJet n a :=
  PowerSeries.coeff_mk _ _

@[simp] theorem coeff_zero_differentialTaylor (a : R) :
    PowerSeries.coeff 0 (differentialTaylor a) = a := by
  simp

theorem differentialTaylor_add (a b : R) :
    differentialTaylor (a + b) = differentialTaylor a + differentialTaylor b := by
  ext n
  simp [differentialJet_add_apply, mul_add]

theorem differentialTaylor_zero : differentialTaylor (0 : R) = 0 := by
  ext n; simp

theorem differentialTaylor_one : differentialTaylor (1 : R) = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      have h1 : (1 : R)′ = 0 := Derivation.map_one_eq_zero _
      rw [coeff_differentialTaylor, differentialJet_eq_zero_of_deriv_eq_zero h1 (Nat.succ_pos n),
        mul_zero, PowerSeries.coeff_one]
      simp

theorem differentialTaylor_mul (a b : R) :
    differentialTaylor (a * b) = differentialTaylor a * differentialTaylor b := by
  ext n
  have hL : differentialJet n (a * b) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k) • (differentialJet k a * differentialJet (n - k) b) :=
    derivation_iterate_mul (Differential.deriv) a b n
  rw [coeff_differentialTaylor, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (differentialTaylor a) *
        PowerSeries.coeff j (differentialTaylor b)) n,
    hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [coeff_differentialTaylor, coeff_differentialTaylor, nsmul_eq_mul]
  have hcomb := invFactorialCast_mul_invFactorialCast (R := R) hk'
  linear_combination (-(differentialJet k a * differentialJet (n - k) b)) * hcomb

/-- The Taylor morphism as a ring homomorphism. -/
def differentialTaylorHom (R : Type*) [CommRing R] [Differential R] [Algebra ℚ R] :
    R →+* PowerSeries R where
  toFun := differentialTaylor
  map_one' := differentialTaylor_one
  map_mul' := differentialTaylor_mul
  map_zero' := differentialTaylor_zero
  map_add' := differentialTaylor_add

@[simp] theorem differentialTaylorHom_apply (a : R) :
    differentialTaylorHom R a = differentialTaylor a := rfl

theorem differentialTaylor_injective :
    Function.Injective (differentialTaylor : R → PowerSeries R) := by
  intro a b hab
  have := congrArg (PowerSeries.coeff 0) hab
  simpa using this

/-- The Taylor morphism turns the derivation into formal differentiation. -/
theorem derivative_differentialTaylor (a : R) :
    (d⁄dX R) (differentialTaylor a) = differentialTaylor a′ := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_differentialTaylor, coeff_differentialTaylor,
    differentialJet_succ_apply]
  have hfac : ((n + 1).factorial : ℚ) = (n + 1 : ℚ) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hn1 : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) := by
    rw [map_add, map_one, map_natCast]
  have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hfne : ((n.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hkey : invFactorialCast R (n + 1) * ((n : R) + 1) = invFactorialCast R n := by
    unfold invFactorialCast
    rw [hn1, ← map_mul]
    congr 1
    rw [hfac]
    field_simp
  calc invFactorialCast R (n + 1) * differentialJet n a′ * ((n : R) + 1)
      = (invFactorialCast R (n + 1) * ((n : R) + 1)) * differentialJet n a′ := by ring
    _ = invFactorialCast R n * differentialJet n a′ := by rw [hkey]

/-- Iterating the previous identity. -/
theorem iterate_derivative_differentialTaylor (n : ℕ) (a : R) :
    (⇑(d⁄dX R))^[n] (differentialTaylor a) = differentialTaylor (differentialJet n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, derivative_differentialTaylor, ih,
        differentialJet_succ_apply]

/-- The arc of a constant is constant. -/
theorem differentialTaylor_of_deriv_eq_zero {a : R} (ha : a′ = 0) :
    differentialTaylor a = PowerSeries.C a := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      rw [coeff_differentialTaylor, differentialJet_eq_zero_of_deriv_eq_zero ha (Nat.succ_pos n),
        mul_zero, PowerSeries.coeff_C]
      simp

/-- An element is killed by `δ^n` exactly when its arc has no coefficient in degree `≥ n`. -/
theorem differentialJet_eq_zero_iff_coeff_eq_zero (n : ℕ) (a : R) :
    differentialJet n a = 0 ↔ ∀ m, n ≤ m → PowerSeries.coeff m (differentialTaylor a) = 0 := by
  constructor
  · intro h m hm
    rw [coeff_differentialTaylor, differentialJet_eq_zero_of_le h hm, mul_zero]
  · intro h
    have hn := h n le_rfl
    rw [coeff_differentialTaylor] at hn
    have hfne : ((n.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hone : algebraMap ℚ R ((n.factorial : ℚ)) * invFactorialCast R n = 1 := by
      unfold invFactorialCast
      rw [← map_mul, mul_inv_cancel₀ hfne, map_one]
    calc differentialJet n a
        = (algebraMap ℚ R ((n.factorial : ℚ)) * invFactorialCast R n) * differentialJet n a := by
          rw [hone, one_mul]
      _ = algebraMap ℚ R ((n.factorial : ℚ)) * (invFactorialCast R n * differentialJet n a) := by
          ring
      _ = 0 := by rw [hn, mul_zero]

/-! ### Arcs of polynomial expressions -/

section Polynomial

variable {K σ : Type*} [CommRing K] [Algebra K R]

/-- **The arc of a polynomial expression is the polynomial evaluated on the arcs.**  The
coefficient ring is required to consist of constants. -/
theorem differentialTaylor_aeval (hK : ∀ c : K, ((algebraMap K R c)′ = 0)) (z : σ → R)
    (P : MvPolynomial σ K) :
    differentialTaylor (MvPolynomial.aeval z P)
      = MvPolynomial.aeval (fun i => differentialTaylor (z i)) P := by
  have hring : (differentialTaylorHom R).comp
        (MvPolynomial.aeval z : MvPolynomial σ K →ₐ[K] R).toRingHom
      = (MvPolynomial.aeval (fun i => differentialTaylor (z i)) :
          MvPolynomial σ K →ₐ[K] PowerSeries R).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.aeval_C, differentialTaylorHom_apply]
      rw [differentialTaylor_of_deriv_eq_zero (hK r), PowerSeries.algebraMap_apply]
    · simp
  exact congrArg (fun f : MvPolynomial σ K →+* PowerSeries R => f P) hring

/-- A polynomial relation among elements holds exactly when it holds among their arcs. -/
theorem aeval_eq_zero_iff_aeval_differentialTaylor_eq_zero
    (hK : ∀ c : K, ((algebraMap K R c)′ = 0)) (z : σ → R) (P : MvPolynomial σ K) :
    MvPolynomial.aeval z P = 0 ↔
      MvPolynomial.aeval (fun i => differentialTaylor (z i)) P = 0 := by
  rw [← differentialTaylor_aeval hK z P]
  constructor
  · intro h; rw [h, differentialTaylor_zero]
  · intro h
    exact differentialTaylor_injective (by rw [h, differentialTaylor_zero])

end Polynomial

end

end GaloisForLFunctions.HTGeometry
