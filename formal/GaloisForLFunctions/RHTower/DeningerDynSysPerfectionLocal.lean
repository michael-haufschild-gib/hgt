import Mathlib.RingTheory.Perfection
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Locality of the tilt, and perfections along a quotient

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.14(2)
(`t1213`) and Proposition 14.7(c) (`t125`).

For a local ring `R` of characteristic `p` the tilt `R^♭ = lim_{()^p} R` (mathlib's `Perfection`)
is again local: an element is a unit exactly when its zeroth coefficient is, because
`(coeff n x) ^ p ^ n = coeff 0 x` and a power is a unit only if the element is.  The maximal ideal
is the preimage of `𝔪` under `coeff 0`, equivalently the set of elements all of whose coefficients
lie in `𝔪` (primality of `𝔪`), and when the Frobenius of `R` is surjective the induced map of
residue fields is bijective.

Proposition 14.7(c) says that for a ring `A` in which every element is a `p`-th power and a prime
`𝔭` with residue fraction field `κ`, surjectivity of `T_p μ (A) → T_p μ (κ)` forces
`lim_{()^p} A → lim_{()^p} A/𝔭` to be surjective.  The mechanism is `deningerPerfection_exists_ratio`:
two elements of a perfection over a group with zero having the same nonzero zeroth coefficient
differ by an element of the Tate module of roots of unity.
-/

namespace RHTower

open Perfection

/-! ## The ratio of two perfection elements with the same zeroth coefficient -/

/-- In a commutative group with zero, two elements of the perfection with the same nonzero zeroth
coefficient differ by an element of the Tate module of roots of unity, i.e. by an element whose
zeroth coefficient is `1`. -/
theorem deningerPerfection_exists_ratio {κ : Type*} [CommGroupWithZero κ] {p : ℕ} (hp : p ≠ 0)
    (x y : Perfection κ p) (h0 : coeffMonoidHom κ p 0 x = coeffMonoidHom κ p 0 y)
    (hne : coeffMonoidHom κ p 0 y ≠ 0) :
    ∃ ζ : Perfection κ p, coeffMonoidHom κ p 0 ζ = 1 ∧ x = ζ * y := by
  have hyne : ∀ n, coeffMonoidHom κ p n y ≠ 0 := by
    intro n hc
    apply hne
    have := coeffMonoidHom_pow_p_pow_self y n
    rw [hc, zero_pow (pow_ne_zero n hp)] at this
    exact this.symm
  refine ⟨⟨fun n => coeffMonoidHom κ p n x / coeffMonoidHom κ p n y, ?_⟩, ?_, ?_⟩
  · intro n
    rw [div_pow, coeffMonoidHom_pow_p' x n, coeffMonoidHom_pow_p' y n]
  · show coeffMonoidHom κ p 0 x / coeffMonoidHom κ p 0 y = 1
    rw [h0, div_self hne]
  · apply extMonoid
    intro n
    show coeffMonoidHom κ p n x
      = (coeffMonoidHom κ p n x / coeffMonoidHom κ p n y) * coeffMonoidHom κ p n y
    rw [div_mul_cancel₀ _ (hyne n)]

/-! ## The perfection of a local ring of characteristic `p` -/

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime] [CharP R p]

/-- An element of the perfection is a unit exactly when its zeroth coefficient is. -/
theorem deningerPerfection_isUnit_iff [IsLocalRing R] (x : Perfection R p) :
    IsUnit x ↔ IsUnit (Perfection.coeff R p 0 x) := by
  refine ⟨fun h => h.map _, fun h => ?_⟩
  classical
  have hunit : ∀ n, IsUnit (Perfection.coeff R p n x) := by
    intro n
    have hpow : (Perfection.coeff R p n x) ^ p ^ n = Perfection.coeff R p 0 x :=
      coeffMonoidHom_pow_p_pow_self x n
    have hu : IsUnit ((Perfection.coeff R p n x) ^ p ^ n) := hpow ▸ h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    refine isUnit_iff_exists_inv.mpr ⟨(Perfection.coeff R p n x) ^ (p ^ n - 1) * b, ?_⟩
    have hk : 1 + (p ^ n - 1) = p ^ n := by
      have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.1.pos
      omega
    calc Perfection.coeff R p n x * ((Perfection.coeff R p n x) ^ (p ^ n - 1) * b)
        = (Perfection.coeff R p n x) ^ (1 + (p ^ n - 1)) * b := by
          rw [pow_add, pow_one, mul_assoc]
      _ = (Perfection.coeff R p n x) ^ (p ^ n) * b := by rw [hk]
      _ = 1 := hb
  have hinv : ∀ n, ∃ b : R, Perfection.coeff R p n x * b = 1 :=
    fun n => isUnit_iff_exists_inv.mp (hunit n)
  choose u hu using hinv
  have hcompat : ∀ n, u (n + 1) ^ p = u n := by
    intro n
    have h1 : u (n + 1) ^ p * Perfection.coeff R p n x = 1 := by
      rw [← Perfection.coeff_pow_p' x n, ← mul_pow, mul_comm (u (n + 1)), hu (n + 1), one_pow]
    calc u (n + 1) ^ p
        = u (n + 1) ^ p * (Perfection.coeff R p n x * u n) := by rw [hu n, mul_one]
      _ = (u (n + 1) ^ p * Perfection.coeff R p n x) * u n := by ring
      _ = u n := by rw [h1, one_mul]
  refine isUnit_iff_exists_inv.mpr ⟨⟨u, hcompat⟩, ?_⟩
  apply Perfection.ext
  intro n
  show Perfection.coeff R p n x * u n = 1
  exact hu n

/-- **Deninger, Proposition 14.14(2) (`t1213`).**  The tilt of a local ring of characteristic `p`
is again a local ring. -/
instance deningerPerfection_isLocalRing [IsLocalRing R] : IsLocalRing (Perfection R p) := by
  haveI : Nontrivial (Perfection R p) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg (Perfection.coeff R p 0) h)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self ?_
  intro x
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Perfection.coeff R p 0 x) with h | h
  · exact Or.inl ((deningerPerfection_isUnit_iff x).mpr h)
  · refine Or.inr ((deningerPerfection_isUnit_iff (1 - x)).mpr ?_)
    rwa [map_sub, map_one]

instance deningerPerfection_coeffZero_isLocalHom [IsLocalRing R] :
    IsLocalHom (Perfection.coeff R p 0) :=
  ⟨fun _ h => (deningerPerfection_isUnit_iff _).mpr h⟩

/-- The maximal ideal of the tilt is the preimage of the maximal ideal under the zeroth
coefficient. -/
theorem deningerPerfection_mem_maximalIdeal_iff [IsLocalRing R] (x : Perfection R p) :
    x ∈ IsLocalRing.maximalIdeal (Perfection R p)
      ↔ Perfection.coeff R p 0 x ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, deningerPerfection_isUnit_iff]

/-- Equivalently, the maximal ideal of the tilt is the perfection of the maximal ideal: an element
lies in it exactly when all of its coefficients do. -/
theorem deningerPerfection_mem_maximalIdeal_iff_forall [IsLocalRing R] (x : Perfection R p) :
    x ∈ IsLocalRing.maximalIdeal (Perfection R p)
      ↔ ∀ n, Perfection.coeff R p n x ∈ IsLocalRing.maximalIdeal R := by
  rw [deningerPerfection_mem_maximalIdeal_iff]
  constructor
  · intro h n
    have hpow : (Perfection.coeff R p n x) ^ p ^ n = Perfection.coeff R p 0 x :=
      coeffMonoidHom_pow_p_pow_self x n
    have hprime : (IsLocalRing.maximalIdeal R).IsPrime := Ideal.IsMaximal.isPrime inferInstance
    exact hprime.mem_of_pow_mem (p ^ n) (by rw [hpow]; exact h)
  · intro h
    exact h 0

/-- **Deninger, Proposition 14.14(2), residue fields.**  If the Frobenius of `R` is surjective, the
zeroth coefficient induces an isomorphism of residue fields `A^♭ / 𝔪^♭ ≅ A / 𝔪`. -/
theorem deningerPerfection_residueField_bijective [IsLocalRing R]
    (hfrob : Function.Surjective (frobenius R p)) :
    Function.Bijective (IsLocalRing.ResidueField.map (Perfection.coeff R p 0)) := by
  refine ⟨(IsLocalRing.ResidueField.map (Perfection.coeff R p 0)).injective, ?_⟩
  intro y
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) y
  obtain ⟨x, hx⟩ := Perfection.coeff_surjective hfrob 0 r
  refine ⟨IsLocalRing.residue _ x, ?_⟩
  rw [IsLocalRing.ResidueField.map_residue, hx]

/-! ## Surjectivity of the perfection along a quotient -/

/-- If every element of a commutative monoid is a `p`-th power, the zeroth coefficient of the
perfection is surjective. -/
theorem deningerPerfection_coeffZero_surjective {M : Type*} [CommMonoid M] {p : ℕ}
    (hpow : ∀ a : M, ∃ b : M, b ^ p = a) : Function.Surjective (coeffMonoidHom M p 0) := by
  classical
  intro a
  choose root hroot using hpow
  refine ⟨⟨fun n => root^[n] a, ?_⟩, rfl⟩
  intro n
  show (root^[n + 1] a) ^ p = root^[n] a
  rw [Function.iterate_succ_apply']
  exact hroot _

theorem deningerPerfection_mapMonoidHom_injective {M N : Type*} [CommMonoid M] [CommMonoid N]
    {p : ℕ} (φ : M →* N) (hφ : Function.Injective φ) :
    Function.Injective (Perfection.mapMonoidHom p φ) := by
  intro x y h
  apply extMonoid
  intro n
  apply hφ
  have hn := congrArg (coeffMonoidHom N p n) h
  rwa [coeffMonoidHom_mapMonoidHom, coeffMonoidHom_mapMonoidHom] at hn

/-- An element of the Tate module of roots of unity in a group with zero is invertible. -/
theorem deningerPerfection_tateMu_exists_inv {κ : Type*} [CommGroupWithZero κ] {p : ℕ}
    (hp : p ≠ 0) (ζ : Perfection κ p) (hζ : coeffMonoidHom κ p 0 ζ = 1) :
    ∃ ζ' : Perfection κ p, coeffMonoidHom κ p 0 ζ' = 1 ∧ ζ * ζ' = 1 := by
  have hne : ∀ n, coeffMonoidHom κ p n ζ ≠ 0 := by
    intro n hc
    have hpow := coeffMonoidHom_pow_p_pow_self ζ n
    rw [hc, zero_pow (pow_ne_zero n hp), hζ] at hpow
    exact zero_ne_one hpow
  refine ⟨⟨fun n => (coeffMonoidHom κ p n ζ)⁻¹, ?_⟩, ?_, ?_⟩
  · intro n
    show ((coeffMonoidHom κ p (n + 1)) ζ)⁻¹ ^ p = ((coeffMonoidHom κ p n) ζ)⁻¹
    rw [inv_pow, coeffMonoidHom_pow_p' ζ n]
  · show (coeffMonoidHom κ p 0 ζ)⁻¹ = 1
    rw [hζ, inv_one]
  · apply extMonoid
    intro n
    show coeffMonoidHom κ p n ζ * (coeffMonoidHom κ p n ζ)⁻¹ = 1
    rw [mul_inv_cancel₀ (hne n)]

/-- **Deninger, Proposition 14.7(c) (`t125`).**  Let `A` be a commutative ring in which every
element is a `p`-th power and let `𝔭` be a prime ideal with residue fraction field `κ`.  If the
Tate module of roots of unity of `A` surjects onto that of `κ`, then the perfection of `A`
surjects onto the perfection of `A / 𝔭`. -/
theorem deningerPerfection_quotient_surjective
    {A : Type*} [CommRing A] {p : ℕ} (hp : p ≠ 0) (𝔭 : Ideal A) [𝔭.IsPrime]
    {κ : Type*} [Field κ] [Algebra (A ⧸ 𝔭) κ] [IsFractionRing (A ⧸ 𝔭) κ]
    (hpow : ∀ a : A, ∃ b : A, b ^ p = a)
    (hmu : ∀ ζ : Perfection κ p, coeffMonoidHom κ p 0 ζ = 1 →
      ∃ η : Perfection A p, coeffMonoidHom A p 0 η = 1 ∧
        Perfection.mapMonoidHom p
          ((((algebraMap (A ⧸ 𝔭) κ) : (A ⧸ 𝔭) →* κ)).comp
            ((Ideal.Quotient.mk 𝔭 : A →+* A ⧸ 𝔭) : A →* A ⧸ 𝔭)) η = ζ) :
    Function.Surjective
      (Perfection.mapMonoidHom p ((Ideal.Quotient.mk 𝔭 : A →+* A ⧸ 𝔭) : A →* A ⧸ 𝔭)) := by
  classical
  intro α
  set qm : A →* A ⧸ 𝔭 := ((Ideal.Quotient.mk 𝔭 : A →+* A ⧸ 𝔭) : A →* A ⧸ 𝔭) with hqm
  set jm : (A ⧸ 𝔭) →* κ := ((algebraMap (A ⧸ 𝔭) κ) : (A ⧸ 𝔭) →* κ) with hjm
  have hjinj : Function.Injective jm := IsFractionRing.injective (A ⧸ 𝔭) κ
  by_cases hα : coeffMonoidHom (A ⧸ 𝔭) p 0 α = 0
  · refine ⟨⟨fun _ => 0, fun _ => zero_pow hp⟩, ?_⟩
    apply extMonoid
    intro n
    rw [coeffMonoidHom_mapMonoidHom]
    have hz : coeffMonoidHom A p n ⟨fun _ => (0 : A), fun _ => zero_pow hp⟩ = 0 := rfl
    rw [hz, hqm]
    have hcn : coeffMonoidHom (A ⧸ 𝔭) p n α = 0 := by
      have hpow' := coeffMonoidHom_pow_p_pow_self α n
      rw [hα] at hpow'
      exact pow_eq_zero_iff (pow_ne_zero n hp) |>.mp hpow'
    rw [hcn]
    simp
  · obtain ⟨a, ha⟩ : ∃ a : A, qm a = coeffMonoidHom (A ⧸ 𝔭) p 0 α :=
      ⟨(Ideal.Quotient.mk_surjective (coeffMonoidHom (A ⧸ 𝔭) p 0 α)).choose,
        (Ideal.Quotient.mk_surjective (coeffMonoidHom (A ⧸ 𝔭) p 0 α)).choose_spec⟩
    obtain ⟨y, hy⟩ := deningerPerfection_coeffZero_surjective (M := A) (p := p) hpow a
    set x : Perfection κ p := Perfection.mapMonoidHom p (jm.comp qm) y with hx
    set z : Perfection κ p := Perfection.mapMonoidHom p jm α with hz
    have hx0 : coeffMonoidHom κ p 0 x = coeffMonoidHom κ p 0 z := by
      rw [hx, hz, coeffMonoidHom_mapMonoidHom, coeffMonoidHom_mapMonoidHom]
      show jm (qm (coeffMonoidHom A p 0 y)) = jm (coeffMonoidHom (A ⧸ 𝔭) p 0 α)
      rw [hy, ha]
    have hz0 : coeffMonoidHom κ p 0 z ≠ 0 := by
      rw [hz, coeffMonoidHom_mapMonoidHom]
      intro hc
      apply hα
      apply hjinj
      rw [hc, hjm]
      exact (map_zero (algebraMap (A ⧸ 𝔭) κ)).symm
    obtain ⟨ζ, hζ1, hζ2⟩ := deningerPerfection_exists_ratio hp x z hx0 hz0
    obtain ⟨ζ', hζ'1, hζ'2⟩ := deningerPerfection_tateMu_exists_inv hp ζ hζ1
    obtain ⟨η, hη1, hη2⟩ := hmu ζ' hζ'1
    refine ⟨η * y, ?_⟩
    apply deningerPerfection_mapMonoidHom_injective jm hjinj
    have hcomp : Perfection.mapMonoidHom p jm (Perfection.mapMonoidHom p qm (η * y))
        = Perfection.mapMonoidHom p (jm.comp qm) (η * y) := by
      apply extMonoid
      intro n
      simp [coeffMonoidHom_mapMonoidHom]
    rw [hcomp, map_mul, hη2, ← hz]
    rw [← hx, hζ2, ← mul_assoc, mul_comm ζ' ζ, hζ'2, one_mul]

end RHTower
