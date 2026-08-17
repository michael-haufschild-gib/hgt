import Mathlib

/-!
# A Bézout constant for monic polynomials without a common factor

Over a unique factorization domain `A` two monic polynomials with no common monic factor of
positive degree generate an ideal of `A[X]` that meets `A` in a nonzero element:

`α·F + β·G = c`,  `c ∈ A`, `c ≠ 0`.

The proof is Gauss' lemma in its integrally closed form.  A greatest common divisor computed in
`K[X]`, `K = Frac A`, can be normalised to be monic, and a monic divisor of a monic polynomial of
`A[X]` computed over `K` already has coefficients in `A`
(`IsIntegrallyClosed.eq_map_mul_C_of_dvd`), so a common factor over `K` descends to a common factor
over `A`.  Hence the two polynomials are coprime over `K`, and clearing the denominators of a Bézout
identity there leaves a constant on the right.

This is the algebraic half of the statement that coprimality of analytic germs propagates to nearby
points: for a Weierstrass pair the constant is a nonzero holomorphic function of the parameters that
vanishes wherever the two distinguished polynomials share a root.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

/-- **A monic divisor over the fraction field comes from the ring.**  If `D` is monic over
`K = Frac A` and divides the image of a monic `F ∈ A[X]`, then `D` is the image of a monic divisor
of `F` in `A[X]`. -/
theorem exists_preimage_monic_of_map_dvd {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {F : A[X]} (hF : F.Monic) {D : K[X]} (hD : D.Monic) (hdvd : D ∣ F.map (algebraMap A K)) :
    ∃ D' : A[X], D'.Monic ∧ D'.map (algebraMap A K) = D ∧ D' ∣ F := by
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hF hdvd
  rw [hD.leadingCoeff, map_one, mul_one] at hg
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hgmonic : g.Monic := by
    have h1 : (algebraMap A K) g.leadingCoeff = 1 := by
      have h2 : (g.map (algebraMap A K)).leadingCoeff = 1 := by rw [hg]; exact hD
      rwa [Polynomial.leadingCoeff_map_of_injective hinj g] at h2
    exact hinj (by rw [h1, map_one])
  exact ⟨g, hgmonic, hg, hF.dvd_of_fraction_map_dvd_fraction_map hgmonic (by rw [hg]; exact hdvd)⟩

/-- **Two monic polynomials without a common monic factor of positive degree are coprime over the
fraction field.** -/
theorem isCoprime_map_of_no_common_monic_factor {K : Type*} [Field K] [Algebra A K]
    [IsFractionRing A K] {F G : A[X]} (hF : F.Monic) (hG : G.Monic)
    (hno : ∀ D : A[X], D.Monic → 0 < D.natDegree → D ∣ F → ¬ D ∣ G) :
    IsCoprime (F.map (algebraMap A K)) (G.map (algebraMap A K)) := by
  classical
  set Fm := F.map (algebraMap A K) with hFm
  set Gm := G.map (algebraMap A K) with hGm
  set D := EuclideanDomain.gcd Fm Gm with hD
  have hFmM : Fm.Monic := hF.map _
  have hFm0 : Fm ≠ 0 := hFmM.ne_zero
  have hD0 : D ≠ 0 := fun h => hFm0 ((EuclideanDomain.gcd_eq_zero_iff.mp h).1)
  have hlc0 : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD0
  have hDu : IsUnit D := by
    by_contra hcon
    have hdegpos : 0 < D.natDegree := by
      rcases Nat.eq_zero_or_pos D.natDegree with h0 | h
      · exfalso
        have hC : D = Polynomial.C (D.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
        have hc0 : D.coeff 0 ≠ 0 := fun h => hD0 (by rw [hC, h, map_zero])
        exact hcon (by rw [hC]; exact (Polynomial.isUnit_C).mpr (isUnit_iff_ne_zero.mpr hc0))
      · exact h
    set D₁ : K[X] := Polynomial.C (D.leadingCoeff)⁻¹ * D with hD₁
    have hsplit : D = D₁ * Polynomial.C D.leadingCoeff := by
      rw [hD₁, mul_comm, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hlc0, map_one, one_mul]
    have hD₁M : D₁.Monic := by
      rw [hD₁, Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact inv_mul_cancel₀ hlc0
    have hD₁deg : D₁.natDegree = D.natDegree := by
      rw [hD₁, Polynomial.natDegree_C_mul (inv_ne_zero hlc0)]
    have hD₁F : D₁ ∣ Fm := dvd_trans ⟨Polynomial.C D.leadingCoeff, hsplit⟩
      (EuclideanDomain.gcd_dvd_left Fm Gm)
    have hD₁G : D₁ ∣ Gm := dvd_trans ⟨Polynomial.C D.leadingCoeff, hsplit⟩
      (EuclideanDomain.gcd_dvd_right Fm Gm)
    obtain ⟨D', hD'M, hD'map, hD'F⟩ := exists_preimage_monic_of_map_dvd hF hD₁M hD₁F
    obtain ⟨D'', hD''M, hD''map, hD''G⟩ := exists_preimage_monic_of_map_dvd hG hD₁M hD₁G
    have heq : D' = D'' :=
      Polynomial.map_injective _ (IsFractionRing.injective A K) (by rw [hD'map, hD''map])
    refine hno D' hD'M ?_ hD'F (heq ▸ hD''G)
    have hdeg : D'.natDegree = D.natDegree := by
      rw [← Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective A K) D', hD'map,
        hD₁deg]
    omega
  obtain ⟨u, hu⟩ := hDu
  refine ⟨((u⁻¹ : K[X]ˣ) : K[X]) * EuclideanDomain.gcdA Fm Gm,
    ((u⁻¹ : K[X]ˣ) : K[X]) * EuclideanDomain.gcdB Fm Gm, ?_⟩
  have hb := EuclideanDomain.gcd_eq_gcd_ab Fm Gm
  rw [← hD] at hb
  have hone : ((u⁻¹ : K[X]ˣ) : K[X]) * D = 1 := by
    rw [← hu]
    exact u.inv_mul
  calc ((u⁻¹ : K[X]ˣ) : K[X]) * EuclideanDomain.gcdA Fm Gm * Fm
        + ((u⁻¹ : K[X]ˣ) : K[X]) * EuclideanDomain.gcdB Fm Gm * Gm
      = ((u⁻¹ : K[X]ˣ) : K[X]) * (Fm * EuclideanDomain.gcdA Fm Gm
          + Gm * EuclideanDomain.gcdB Fm Gm) := by ring
    _ = ((u⁻¹ : K[X]ˣ) : K[X]) * D := by rw [← hb]
    _ = 1 := hone

omit [IsDomain A] [UniqueFactorizationMonoid A] in
/-- Scalar multiplication by a ring element on polynomials over the fraction field. -/
theorem smul_eq_C_mul_of_fraction {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (b : A) (p : K[X]) : b • p = Polynomial.C (algebraMap A K b) * p := by
  rw [Algebra.smul_def, Polynomial.algebraMap_apply]

/-- **The Bézout constant.**  Two monic polynomials over a unique factorization domain with no
common monic factor of positive degree admit a combination equal to a nonzero constant. -/
theorem exists_bezout_const {F G : A[X]} (hF : F.Monic) (hG : G.Monic)
    (hno : ∀ D : A[X], D.Monic → 0 < D.natDegree → D ∣ F → ¬ D ∣ G) :
    ∃ (α β : A[X]) (c : A), c ≠ 0 ∧ α * F + β * G = Polynomial.C c := by
  classical
  set K := FractionRing A
  set φ := algebraMap A K with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective A K
  obtain ⟨a, b, hab⟩ := isCoprime_map_of_no_common_monic_factor (K := K) hF hG hno
  obtain ⟨c₁, hc₁M, hc₁⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors A) (S := K) a
  obtain ⟨c₂, hc₂M, hc₂⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors A) (S := K) b
  set α₀ := IsLocalization.integerNormalization (nonZeroDivisors A) (S := K) a with hα₀
  set β₀ := IsLocalization.integerNormalization (nonZeroDivisors A) (S := K) b with hβ₀
  have hc₁0 : c₁ ≠ 0 := nonZeroDivisors.ne_zero hc₁M
  have hc₂0 : c₂ ≠ 0 := nonZeroDivisors.ne_zero hc₂M
  refine ⟨Polynomial.C c₂ * α₀, Polynomial.C c₁ * β₀, c₁ * c₂, mul_ne_zero hc₁0 hc₂0, ?_⟩
  refine Polynomial.map_injective φ hinj ?_
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, hc₁, hc₂,
    smul_eq_C_mul_of_fraction, smul_eq_C_mul_of_fraction, map_mul]
  calc Polynomial.C (φ c₂) * (Polynomial.C (φ c₁) * a) * Polynomial.map φ F
        + Polynomial.C (φ c₁) * (Polynomial.C (φ c₂) * b) * Polynomial.map φ G
      = (Polynomial.C (φ c₁) * Polynomial.C (φ c₂))
          * (a * Polynomial.map φ F + b * Polynomial.map φ G) := by ring
    _ = Polynomial.C (φ c₁) * Polynomial.C (φ c₂) := by rw [hab, mul_one]
    _ = Polynomial.C (φ c₁ * φ c₂) := by rw [Polynomial.C_mul]

end GaloisForLFunctions.HTGeometry
