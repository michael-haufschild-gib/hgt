import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Connes' periodization map: equivariance and the Fourier reflection

Formalization of §III (18)(19) and Appendix I (37)(38) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The whole construction of the Polya-Hilbert space rests on the periodization

  `E(f)(g) = |g|^{1/2} ∑_{q ∈ k^*} f(q g)`,

which intertwines the scaling action `U` on the adele class space with the regular representation
`V` of the idele class group up to the half-power of the module, and which is *anti-invariant*
under Fourier transform.

* `connesPeriodization_equivariance` - §III (19): `E U(a) = |a|^{1/2} V(a) E`.  Pure algebra of a
  commutative monoid and a multiplicative module; needs no summability at all, because the two
  index families are literally the same function.
* `connes_poisson_punctured` - Appendix I (37): removing the origin from a Poisson-type identity
  when both sides vanish there.  This is where `𝒮(A)₀ = {f : f(0) = 0, ∫ f = 0}` is used: the
  defect `δ = -|x| f(0) + ∫ f` of (37) vanishes exactly on `𝒮(A)₀`.
* `connesPeriodization_reflect` - Appendix I (38): `E(f)(x) = E(f̂)(x⁻¹)`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Connes' periodization `E(f)(g) = |g|^{1/2} ∑_{q ∈ Γ} f(q g)` of §III (18), for an index family
`ι : Γ → A` of scalars and a module function `mod`. -/
def connesPeriodization {A : Type*} [CommMonoid A] {Γ : Type*} (ι : Γ → A) (mod : A → ℝ)
    (f : A → ℂ) (g : A) : ℂ :=
  (Real.sqrt (mod g) : ℂ) * ∑' q : Γ, f (ι q * g)

/-- **§III (19).**  `E U(a) = |a|^{1/2} V(a) E`. -/
theorem connesPeriodization_equivariance {A : Type*} [CommMonoid A] {Γ : Type*} (ι : Γ → A)
    (mod : A → ℝ) (hmod : ∀ x y : A, mod (x * y) = mod x * mod y) (hmodnn : ∀ x : A, 0 ≤ mod x)
    (f : A → ℂ) (a : Aˣ) (g : A) :
    connesPeriodization ι mod (fun x => f (((a⁻¹ : Aˣ) : A) * x)) g
      = (Real.sqrt (mod ((a : Aˣ) : A)) : ℂ) *
          connesPeriodization ι mod f (((a⁻¹ : Aˣ) : A) * g) := by
  have hsum : ∀ q : Γ, (((a⁻¹ : Aˣ) : A) * (ι q * g)) = ι q * (((a⁻¹ : Aˣ) : A) * g) := by
    intro q; rw [mul_left_comm]
  have hg : mod g = mod ((a : Aˣ) : A) * mod (((a⁻¹ : Aˣ) : A) * g) := by
    rw [← hmod]
    congr 1
    rw [← mul_assoc]
    simp
  simp only [connesPeriodization]
  rw [hg, Real.sqrt_mul (hmodnn _)]
  push_cast
  rw [mul_assoc]
  congr 2
  exact tsum_congr fun q => by rw [hsum q]

/-- **Appendix I (37).**  If a Poisson-type identity holds over the full index and both sides
vanish at the distinguished index point, then the identity holds over the punctured index. -/
theorem connes_poisson_punctured {K : Type*} (o : K) (F G : K → ℂ)
    (hF : Summable F) (hG : Summable G) (m : ℂ)
    (hpoisson : m * ∑' q : K, F q = ∑' q : K, G q)
    (hFo : F o = 0) (hGo : G o = 0) :
    m * ∑' q : {q : K // q ≠ o}, F q = ∑' q : {q : K // q ≠ o}, G q := by
  have hsplitF : ∑' q : K, F q = ∑' q : {q : K // q ≠ o}, F q := by
    have h := hF.tsum_subtype_add_tsum_subtype_compl ({o} : Set K)
    rw [tsum_singleton o F] at h
    rw [hFo, zero_add] at h
    rw [← h]
    exact tsum_congr fun q => rfl
  have hsplitG : ∑' q : K, G q = ∑' q : {q : K // q ≠ o}, G q := by
    have h := hG.tsum_subtype_add_tsum_subtype_compl ({o} : Set K)
    rw [tsum_singleton o G] at h
    rw [hGo, zero_add] at h
    rw [← h]
    exact tsum_congr fun q => rfl
  rw [← hsplitF, ← hsplitG]
  exact hpoisson

/-- **Appendix I (38).**  `E(f)(x) = E(f̂)(x⁻¹)`: the periodization is anti-invariant under the
Fourier transform, once the punctured Poisson identity `|x| ∑_{k^*} f(qx) = ∑_{k^*} f̂(q x⁻¹)` is
available. -/
theorem connesPeriodization_reflect {A : Type*} [CommMonoid A] {Γ : Type*} (ι : Γ → A)
    (mod : A → ℝ) (f fhat : A → ℂ) (x : Aˣ)
    (hmodpos : 0 < mod ((x : Aˣ) : A))
    (hmodinv : mod (((x⁻¹ : Aˣ) : A)) = (mod ((x : Aˣ) : A))⁻¹)
    (hpunct : (mod ((x : Aˣ) : A) : ℂ) * ∑' q : Γ, f (ι q * ((x : Aˣ) : A))
      = ∑' q : Γ, fhat (ι q * (((x⁻¹ : Aˣ) : A)))) :
    connesPeriodization ι mod f ((x : Aˣ) : A)
      = connesPeriodization ι mod fhat (((x⁻¹ : Aˣ) : A)) := by
  have hsqrt : Real.sqrt (mod (((x⁻¹ : Aˣ) : A))) = (Real.sqrt (mod ((x : Aˣ) : A)))⁻¹ := by
    rw [hmodinv, Real.sqrt_inv]
  have hne : (Real.sqrt (mod ((x : Aˣ) : A)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hmodpos)
  simp only [connesPeriodization, hsqrt]
  push_cast
  rw [eq_comm, inv_mul_eq_iff_eq_mul₀ hne, ← mul_assoc]
  have hsq : (Real.sqrt (mod ((x : Aˣ) : A)) : ℂ) * (Real.sqrt (mod ((x : Aˣ) : A)) : ℂ)
      = (mod ((x : Aˣ) : A) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hmodpos)]
  rw [hsq]
  exact hpunct.symm

/-- **§VIII (22), support half.**  If `f` vanishes where the module exceeds `Λ`, so does its
periodization: every term of the orbit sum has the same module as `g`, because the elements of
`k^*` have module one (the product formula). -/
theorem connesPeriodization_eq_zero_of_lt {A : Type*} [CommMonoid A] {Γ : Type*} (ι : Γ → A)
    (mod : A → ℝ) (hmod : ∀ x y : A, mod (x * y) = mod x * mod y)
    (hunit : ∀ q : Γ, mod (ι q) = 1) (f : A → ℂ) {Λ : ℝ}
    (hf : ∀ x : A, Λ < mod x → f x = 0) {g : A} (hg : Λ < mod g) :
    connesPeriodization ι mod f g = 0 := by
  have hterm : ∀ q : Γ, f (ι q * g) = 0 := by
    intro q
    refine hf _ ?_
    rw [hmod, hunit q, one_mul]
    exact hg
  simp only [connesPeriodization, hterm, tsum_zero, mul_zero]

/-- **§VIII (22)/(23).**  If both `f` and its Fourier transform vanish where the module exceeds
`Λ`, the periodization `E(f)` is supported in the module window `[Λ^{-1}, Λ]`; this is the
inclusion `E(B_{Λ,0}) ⊆ S_Λ` that produces the operator inequality `Q'_{Λ,0} ≤ S_Λ`. -/
theorem connesPeriodization_support_window {A : Type*} [CommMonoid A] {Γ : Type*} (ι : Γ → A)
    (mod : A → ℝ) (hmod : ∀ x y : A, mod (x * y) = mod x * mod y)
    (hunit : ∀ q : Γ, mod (ι q) = 1) (f fhat : A → ℂ) {Λ : ℝ}
    (hf : ∀ x : A, Λ < mod x → f x = 0)
    (hfhat : ∀ x : A, Λ < mod x → fhat x = 0)
    (x : Aˣ)
    (hmodpos : 0 < mod ((x : Aˣ) : A))
    (hmodinv : mod (((x⁻¹ : Aˣ) : A)) = (mod ((x : Aˣ) : A))⁻¹)
    (hpunct : (mod ((x : Aˣ) : A) : ℂ) * ∑' q : Γ, f (ι q * ((x : Aˣ) : A))
      = ∑' q : Γ, fhat (ι q * (((x⁻¹ : Aˣ) : A))))
    (hout : Λ < mod ((x : Aˣ) : A) ∨ Λ < (mod ((x : Aˣ) : A))⁻¹) :
    connesPeriodization ι mod f ((x : Aˣ) : A) = 0 := by
  rcases hout with h | h
  · exact connesPeriodization_eq_zero_of_lt ι mod hmod hunit f hf h
  · rw [connesPeriodization_reflect ι mod f fhat x hmodpos hmodinv hpunct]
    refine connesPeriodization_eq_zero_of_lt ι mod hmod hunit fhat hfhat ?_
    rw [hmodinv]
    exact h

end

end GaloisForLFunctions.RHTower
