import GaloisForLFunctions.HTGeometry.HyperexponentialTranscendence
import Mathlib.RingTheory.EuclideanDomain

/-!
# No primitive of a hyperexponential element inside its own extension

Let `t` be transcendental over a derivation-closed field `K` with `D t = u · t`, `u ∈ K`.  If none
of the homogeneous equations `D w = k · u · w` (`k ≥ 1`) has a nonzero solution in `K` and the
inhomogeneous equation `D w + u · w = 1` has no solution in `K`, then no element of `K(t)` has
derivative `t`.

Writing a candidate as a coprime quotient `A / B` with `B` monic and clearing denominators, the
denominator divides its own twisted derivative, so it is a power of `t`; the numerator equation then
produces a solution of the excluded inhomogeneous equation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

section Representation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **A coprime representation with monic denominator.**  Every element of a simple transcendental
extension is a quotient of two coprime polynomials in the generator with monic denominator. -/
theorem exists_coprime_monic_repr {t y : L} (htr : Transcendental K t)
    (hy : y ∈ IntermediateField.adjoin K ({t} : Set L)) :
    ∃ A B : K[X], B.Monic ∧ IsCoprime A B ∧ y * aeval t B = aeval t A := by
  classical
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff (F := K) (α := t) (x := y)).mp hy
  have hinj : Function.Injective (Polynomial.aeval t : K[X] →ₐ[K] L) :=
    transcendental_iff_injective.mp htr
  by_cases hs : s = 0
  · refine ⟨0, 1, monic_one, isCoprime_zero_left.mpr isUnit_one, ?_⟩
    rw [hrs, hs]
    simp
  · obtain ⟨g, a, b, hg0, hdvdl, hdvdr, hbez⟩ :
        ∃ g a b : K[X], g ≠ 0 ∧ g ∣ r ∧ g ∣ s ∧ g = r * a + s * b := by
      refine ⟨EuclideanDomain.gcd r s, EuclideanDomain.gcdA r s, EuclideanDomain.gcdB r s, ?_,
        EuclideanDomain.gcd_dvd_left r s, EuclideanDomain.gcd_dvd_right r s,
        EuclideanDomain.gcd_eq_gcd_ab r s⟩
      intro h
      exact hs (EuclideanDomain.gcd_eq_zero_iff.mp h).2
    obtain ⟨A₀, hA₀⟩ := hdvdl
    obtain ⟨B₀, hB₀⟩ := hdvdr
    have hB₀0 : B₀ ≠ 0 := by
      intro h
      exact hs (by rw [hB₀, h, mul_zero])
    have hcop : IsCoprime A₀ B₀ := by
      refine ⟨a, b, ?_⟩
      refine mul_left_cancel₀ hg0 ?_
      rw [mul_one]
      calc g * (a * A₀ + b * B₀) = (g * A₀) * a + (g * B₀) * b := by ring
        _ = r * a + s * b := by rw [← hA₀, ← hB₀]
        _ = g := hbez.symm
    -- normalise the denominator to be monic
    set c : K := (B₀.leadingCoeff)⁻¹ with hc
    have hlc : B₀.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB₀0
    have hc0 : c ≠ 0 := inv_ne_zero hlc
    refine ⟨Polynomial.C c * A₀, Polynomial.C c * B₀, ?_, ?_, ?_⟩
    · have hlead : (Polynomial.C c * B₀).leadingCoeff = c * B₀.leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      show (Polynomial.C c * B₀).leadingCoeff = 1
      rw [hlead, hc, inv_mul_cancel₀ hlc]
    · obtain ⟨x, z, hxz⟩ := hcop
      refine ⟨Polynomial.C c⁻¹ * x, Polynomial.C c⁻¹ * z, ?_⟩
      have hcc : Polynomial.C c⁻¹ * Polynomial.C c = 1 := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hc0, Polynomial.C_1]
      calc Polynomial.C c⁻¹ * x * (Polynomial.C c * A₀)
            + Polynomial.C c⁻¹ * z * (Polynomial.C c * B₀)
          = (Polynomial.C c⁻¹ * Polynomial.C c) * (x * A₀ + z * B₀) := by ring
        _ = 1 := by rw [hcc, hxz, one_mul]
    · have hgne : aeval t g ≠ 0 := fun h => hg0 (hinj (by simpa using h))
      have hB₀ne : aeval t B₀ ≠ 0 := fun h => hB₀0 (hinj (by simpa using h))
      have hsne : aeval t s ≠ 0 := by
        rw [hB₀, map_mul]
        exact mul_ne_zero hgne hB₀ne
      have hyval : y * aeval t s = aeval t r := by
        rw [hrs]
        field_simp
      have h2 : aeval t g * (y * aeval t B₀) = aeval t g * aeval t A₀ := by
        have hleft : aeval t g * (y * aeval t B₀) = y * aeval t s := by
          rw [hB₀, map_mul]
          ring
        rw [hleft, hyval, hA₀, map_mul]
      have h3 : y * aeval t B₀ = aeval t A₀ := mul_left_cancel₀ hgne h2
      simp only [map_mul, aeval_C]
      linear_combination (algebraMap K L c) * h3

end Representation

section Twist

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- The ambient derivation restricted to a derivation-closed intermediate field. -/
def restrictDerivation (D : Derivation C L L) (K : IntermediateField C L)
    (hDK : ∀ v ∈ K, D v ∈ K) : Derivation C ↥K ↥K where
  toFun v := ⟨D (v : L), hDK (v : L) v.2⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)
  map_one_eq_zero' := Subtype.ext (by simp)
  leibniz' a b := Subtype.ext (by simp)

@[simp]
theorem restrictDerivation_coe (D : Derivation C L L) (K : IntermediateField C L)
    (hDK : ∀ v ∈ K, D v ∈ K) (v : ↥K) :
    ((restrictDerivation D K hDK v : ↥K) : L) = D (v : L) := rfl

/-- The twisted derivative of a polynomial: coefficientwise differentiation together with the
weight `j · u` carried by the `j`-th power of a hyperexponential generator. -/
def twistPoly (D : Derivation C L L) (K : IntermediateField C L) (hDK : ∀ v ∈ K, D v ∈ K)
    (u : ↥K) (A : (↥K)[X]) : (↥K)[X] :=
  derivMapCoeffs (restrictDerivation D K hDK) A + Polynomial.C u * (Polynomial.X * derivative A)

theorem coeff_twistPoly (D : Derivation C L L) (K : IntermediateField C L)
    (hDK : ∀ v ∈ K, D v ∈ K) (u : ↥K) (A : (↥K)[X]) (j : ℕ) :
    (twistPoly D K hDK u A).coeff j
      = restrictDerivation D K hDK (A.coeff j) + (j : ↥K) * u * A.coeff j := by
  rw [twistPoly, coeff_add, coeff_derivMapCoeffs, coeff_C_mul, coeff_X_mul_derivative]
  ring

theorem natDegree_twistPoly_le (D : Derivation C L L) (K : IntermediateField C L)
    (hDK : ∀ v ∈ K, D v ∈ K) (u : ↥K) (A : (↥K)[X]) :
    (twistPoly D K hDK u A).natDegree ≤ A.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_twistPoly, coeff_eq_zero_of_natDegree_lt hm, map_zero, mul_zero, add_zero]

/-- The twisted derivative computes the ambient derivative of the evaluated polynomial. -/
theorem deriv_aeval_eq_aeval_twistPoly (D : Derivation C L L) (K : IntermediateField C L)
    (hDK : ∀ v ∈ K, D v ∈ K) {u : ↥K} {t : L} (htD : D t = (u : L) * t) (A : (↥K)[X]) :
    D (aeval t A) = aeval t (twistPoly D K hDK u A) := by
  have hmapcoeff : derivMapCoeffs D (A.map (algebraMap ↥K L))
      = (derivMapCoeffs (restrictDerivation D K hDK) A).map (algebraMap ↥K L) := by
    ext i
    rw [coeff_derivMapCoeffs, coeff_map, coeff_map, coeff_derivMapCoeffs]
    rfl
  have hchain := derivation_aeval_eq D t (A.map (algebraMap ↥K L))
  rw [aeval_map_algebraMap, hmapcoeff, Polynomial.derivative_map, aeval_map_algebraMap,
    aeval_map_algebraMap, htD] at hchain
  have hcoe : algebraMap ↥K L u = (u : L) := rfl
  rw [hchain, twistPoly, map_add, map_mul, map_mul, aeval_C, aeval_X, hcoe]
  ring

end Twist

section Main

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- **No primitive of a hyperexponential generator inside its own extension.** -/
theorem not_deriv_eq_of_hyperexponential (D : Derivation C L L) (K : IntermediateField C L)
    (hDK : ∀ v ∈ K, D v ∈ K) {t : L} {u : ↥K} (htr : Transcendental ↥K t)
    (htD : D t = (u : L) * t)
    (hker : ∀ k : ℕ, 1 ≤ k → ∀ w : ↥K,
      restrictDerivation D K hDK w = (k : ↥K) * u * w → w = 0)
    (hinhom : ∀ w : ↥K, restrictDerivation D K hDK w + u * w ≠ 1)
    {y : L} (hy : y ∈ IntermediateField.adjoin ↥K ({t} : Set L)) :
    D y ≠ t := by
  classical
  intro hDy
  have hinj : Function.Injective (Polynomial.aeval t : (↥K)[X] →ₐ[↥K] L) :=
    transcendental_iff_injective.mp htr
  obtain ⟨A, B, hBmonic, hcop, hrepr⟩ := exists_coprime_monic_repr htr hy
  have hB0 : B ≠ 0 := hBmonic.ne_zero
  -- differentiate the cleared identity
  have hd : y * aeval t (twistPoly D K hDK u B) + aeval t B * t
      = aeval t (twistPoly D K hDK u A) := by
    have h := congrArg (fun w : L => D w) hrepr
    simp only [Derivation.leibniz, smul_eq_mul] at h
    rw [hDy, deriv_aeval_eq_aeval_twistPoly D K hDK htD,
      deriv_aeval_eq_aeval_twistPoly D K hDK htD] at h
    exact h
  have hpoly : aeval t (twistPoly D K hDK u A * B - A * twistPoly D K hDK u B)
      = aeval t (Polynomial.X * B ^ (2 : ℕ)) := by
    simp only [map_sub, map_mul, map_pow, aeval_X]
    linear_combination (aeval t (twistPoly D K hDK u B)) * hrepr - (aeval t B) * hd
  have hid : twistPoly D K hDK u A * B - A * twistPoly D K hDK u B = Polynomial.X * B ^ (2 : ℕ) :=
    hinj hpoly
  -- the denominator divides its own twisted derivative
  have hdvd : B ∣ A * twistPoly D K hDK u B := by
    refine ⟨twistPoly D K hDK u A - Polynomial.X * B, ?_⟩
    linear_combination -hid
  have hdvd' : B ∣ twistPoly D K hDK u B := (hcop.symm).dvd_of_dvd_mul_left hdvd
  set m : ℕ := B.natDegree with hm
  set R : (↥K)[X] := twistPoly D K hDK u B - Polynomial.C ((m : ↥K) * u) * B with hR
  have hRtop : ∀ j : ℕ, m ≤ j → R.coeff j = 0 := by
    intro j hj
    rw [hR, coeff_sub, coeff_twistPoly, coeff_C_mul]
    rcases eq_or_lt_of_le hj with rfl | hlt
    · rw [hBmonic.coeff_natDegree, (restrictDerivation D K hDK).map_one_eq_zero]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt hlt, map_zero]
      ring
  have hBdvdR : B ∣ R := dvd_sub hdvd' (Dvd.intro_left _ rfl)
  have hR0 : R = 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hBeq : B = 1 := Polynomial.eq_one_of_monic_natDegree_zero hBmonic hm0
      have htw1 : twistPoly D K hDK u 1 = 0 := by
        ext j
        rw [coeff_twistPoly]
        rcases j with _ | j
        · simp [Polynomial.coeff_one, (restrictDerivation D K hDK).map_one_eq_zero]
        · simp [Polynomial.coeff_one]
      rw [hR, hBeq, htw1, hm0]
      simp
    · have hle : R.natDegree ≤ m - 1 := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro j hj
        exact hRtop j (by omega)
      exact Polynomial.eq_zero_of_dvd_of_natDegree_lt hBdvdR (by omega)
  have htwB : twistPoly D K hDK u B = Polynomial.C ((m : ↥K) * u) * B := by
    rw [← sub_eq_zero, ← hR]
    exact hR0
  -- the denominator is a pure power of the generator
  have hBcoeff : ∀ j : ℕ, j < m → B.coeff j = 0 := by
    intro j hj
    have hc := congrArg (fun P : (↥K)[X] => P.coeff j) htwB
    simp only [coeff_twistPoly, coeff_C_mul] at hc
    refine hker (m - j) (by omega) (B.coeff j) ?_
    have hcast : ((m - j : ℕ) : ↥K) = (m : ↥K) - (j : ↥K) := by
      rw [Nat.cast_sub (le_of_lt hj)]
    rw [hcast]
    linear_combination hc
  have hBeq : B = Polynomial.X ^ m := by
    ext i
    rw [Polynomial.coeff_X_pow]
    rcases lt_trichotomy i m with hlt | rfl | hgt
    · rw [hBcoeff i hlt, if_neg (by omega)]
    · rw [hBmonic.coeff_natDegree, if_pos rfl]
    · rw [coeff_eq_zero_of_natDegree_lt hgt, if_neg (by omega)]
  -- the numerator equation produces a solution of the excluded inhomogeneous equation
  have hcancel : twistPoly D K hDK u A - Polynomial.C ((m : ↥K) * u) * A
      = Polynomial.X ^ (m + 1) := by
    have hXm : (Polynomial.X : (↥K)[X]) ^ m ≠ 0 := pow_ne_zero m Polynomial.X_ne_zero
    refine mul_right_cancel₀ hXm ?_
    have hid' := hid
    rw [htwB, hBeq] at hid'
    calc (twistPoly D K hDK u A - Polynomial.C ((m : ↥K) * u) * A) * Polynomial.X ^ m
        = twistPoly D K hDK u A * Polynomial.X ^ m
          - A * (Polynomial.C ((m : ↥K) * u) * Polynomial.X ^ m) := by ring
      _ = Polynomial.X * (Polynomial.X ^ m) ^ (2 : ℕ) := hid'
      _ = Polynomial.X ^ (m + 1) * Polynomial.X ^ m := by ring
  have hfinal := congrArg (fun P : (↥K)[X] => P.coeff (m + 1)) hcancel
  simp only [coeff_sub, coeff_twistPoly, coeff_C_mul, Polynomial.coeff_X_pow, if_true] at hfinal
  refine hinhom (A.coeff (m + 1)) ?_
  have hcast : ((m + 1 : ℕ) : ↥K) = (m : ↥K) + 1 := by push_cast; ring
  rw [hcast] at hfinal
  linear_combination hfinal

end Main

end

end GaloisForLFunctions.HTGeometry
