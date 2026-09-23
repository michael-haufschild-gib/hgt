import GaloisForLFunctions.HTGeometry.SpectrumGenericity
import GaloisForLFunctions.RHTower.FunctionFieldSpectralClosureUniversalityLaw

/-!
# Generic spectra fracture every rational weighted reciprocal functional equation

Function-field spectral closure forces the top elementary-symmetric coordinate to obey a quadratic
equation over the weight field.  Finite DSS genericity makes that same coordinate transcendental.
The two mechanisms are therefore mutually exclusive over every characteristic-zero field, and the
universal generic secular spectrum realizes the obstruction in its fraction field.
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- Homogeneity of multiset elementary-symmetric functions over an arbitrary field. -/
theorem multiset_esymm_map_mul_field
    {F : Type*} [Field F] (q : F) (S : Multiset F) (k : ℕ) :
    (S.map fun z => q * z).esymm k = q ^ k * S.esymm k := by
  simpa only [smul_eq_mul] using
    (Multiset.pow_smul_esymm q k S).symm

/-- Arbitrary-field form of function-field coefficient completeness: weighted reciprocal
spectral closure is equivalent to the complete weighted elementary-symmetric relation. -/
theorem weightedReciprocal_spectralClosure_iff_esymm_FE
    {F : Type*} [Field F] (q : F) (S : Multiset F) :
    S.map (fun omega => q / omega) = S ↔
      ∀ k : ℕ, S.esymm k = q ^ k * (S.map (fun omega => omega⁻¹)).esymm k := by
  constructor
  · intro hclosed k
    have hmap :
        S.map (fun omega => q / omega) =
          (S.map (fun omega => omega⁻¹)).map (fun z => q * z) := by
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro omega _
      rw [Function.comp_apply, div_eq_mul_inv]
    conv_lhs => rw [← hclosed, hmap]
    rw [multiset_esymm_map_mul_field]
  · intro hcoeff
    let T : Multiset F := S.map (fun omega => q / omega)
    have hcard : S.card = T.card := by simp [T]
    have hscaled (k : ℕ) :
        T.esymm k = q ^ k * (S.map (fun omega => omega⁻¹)).esymm k := by
      have h := multiset_esymm_map_mul_field
        q (S.map (fun omega => omega⁻¹)) k
      rw [Multiset.map_map] at h
      simpa only [T, Function.comp_apply, div_eq_mul_inv] using h
    have hST : S = T := multiset_eq_of_esymm_eq hcard (fun k _ => by
      rw [hcoeff k, hscaled k])
    exact hST.symm

/-- **Algebraically independent spectral packets fracture rational weighted reciprocal
closure.**  A fixed rational functional-equation weight would make the top symmetric coordinate
quadratic over `ℚ`, contradicting its transcendence. -/
theorem algebraicallyIndependentSpectrum_not_fixedRationalWeightedReciprocal
    {F : Type*} [Field F] [Algebra ℚ F]
    {n : ℕ} (hn : 0 < n) (S : Multiset F) (hcard : S.card = n)
    (hAI : AlgebraicIndependent ℚ (fun i : Fin n => S.esymm (i.1 + 1)))
    (q : ℚ) :
    S.map (fun omega => algebraMap ℚ F q / omega) ≠ S := by
  intro hclosed
  let top : Fin n := ⟨n - 1, by omega⟩
  have htop : top.1 + 1 = n := by
    dsimp [top]
    omega
  let eTop : F := S.esymm (top.1 + 1)
  have htrans : Transcendental ℚ eTop := hAI.transcendental top
  have heTopNe : eTop ≠ 0 := by
    intro he
    apply htrans
    refine ⟨Polynomial.X, Polynomial.X_ne_zero, ?_⟩
    simpa [eTop] using he
  have hFE :=
    (weightedReciprocal_spectralClosure_iff_esymm_FE
      (algebraMap ℚ F q) S).mp hclosed n
  have heProd : eTop = S.prod := by
    change S.esymm (top.1 + 1) = S.prod
    rw [htop, ← hcard]
    simp [Multiset.esymm]
  have hInvTop :
      (S.map (fun omega => omega⁻¹)).esymm n = S.prod⁻¹ := by
    have hcardInv : (S.map (fun omega => omega⁻¹)).card = S.card := by simp
    rw [← hcard, ← hcardInv]
    calc
      (S.map (fun omega => omega⁻¹)).esymm
          (S.map (fun omega => omega⁻¹)).card =
        (S.map (fun omega => omega⁻¹)).prod := by
          rw [Multiset.esymm, Multiset.powersetCard_self]
          simp
      _ = S.prod⁻¹ := Multiset.prod_map_inv' S
  have hsquare : eTop ^ (2 : ℕ) = algebraMap ℚ F (q ^ n) := by
    have hFE' : eTop = algebraMap ℚ F q ^ n * S.prod⁻¹ := by
      change S.esymm (top.1 + 1) = _
      rw [htop]
      simpa only [hInvTop] using hFE
    calc
      eTop ^ (2 : ℕ) = eTop * eTop := pow_two eTop
      _ = (algebraMap ℚ F q ^ n * S.prod⁻¹) * eTop := by rw [hFE']
      _ = (algebraMap ℚ F q ^ n * S.prod⁻¹) * S.prod := by rw [heProd]
      _ = algebraMap ℚ F q ^ n := by
        rw [mul_assoc, inv_mul_cancel₀]
        · rw [mul_one]
        · rwa [← heProd]
      _ = algebraMap ℚ F (q ^ n) := by rw [map_pow]
  apply htrans
  refine ⟨Polynomial.X ^ (2 : ℕ) - Polynomial.C (q ^ n),
    Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 2) (q ^ n), ?_⟩
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [hsquare, map_pow, sub_self]

/-- Fraction field carrying the universal `n`-point secular spectrum. -/
abbrev genericSecularSpectrumField (n : ℕ) :=
  FractionRing (MvPolynomial (Fin n) ℚ)

/-- Universal secular spectrum whose roots are the independent polynomial variables. -/
def genericSecularSpectrum (n : ℕ) : Multiset (genericSecularSpectrumField n) :=
  Finset.univ.val.map fun i : Fin n =>
    algebraMap (MvPolynomial (Fin n) ℚ) (genericSecularSpectrumField n)
      (MvPolynomial.X i)

/-- **Generic-spectrum functional-equation fracture universality law.**  No nonempty universal
generic secular spectrum is fixed by weighted reciprocal duality for any rational constant
weight. -/
theorem genericSecularSpectrum_not_fixedRationalWeightedReciprocal
    (n : ℕ) (hn : 0 < n) (q : ℚ) :
    (genericSecularSpectrum n).map
        (fun omega => algebraMap ℚ (genericSecularSpectrumField n) q / omega) ≠
      genericSecularSpectrum n := by
  let R := MvPolynomial (Fin n) ℚ
  let L := genericSecularSpectrumField n
  let S : Multiset L := genericSecularSpectrum n
  have hcard : S.card = n := by simp [S, genericSecularSpectrum]
  let phi : R →ₐ[ℚ] L := IsScalarTower.toAlgHom ℚ R L
  have hphi :
      (MvPolynomial.aeval (fun i : Fin n => phi (MvPolynomial.X i)) :
        R →ₐ[ℚ] L) = phi := by
    ext i
    rw [MvPolynomial.aeval_X]
  have hfamily :
      (fun i : Fin n => S.esymm (i.1 + 1)) =
        (fun i : Fin n =>
          algebraMap R L (MvPolynomial.esymm (Fin n) ℚ (i.1 + 1))) := by
    funext i
    change (genericSecularSpectrum n).esymm (i.1 + 1) =
      algebraMap (MvPolynomial (Fin n) ℚ) (genericSecularSpectrumField n)
        (MvPolynomial.esymm (Fin n) ℚ (i.1 + 1))
    calc
      (genericSecularSpectrum n).esymm (i.1 + 1) =
          MvPolynomial.aeval
            (fun j : Fin n => phi (MvPolynomial.X j))
            (MvPolynomial.esymm (Fin n) ℚ (i.1 + 1)) := by
        rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
        rfl
      _ = phi (MvPolynomial.esymm (Fin n) ℚ (i.1 + 1)) := by rw [hphi]
      _ = _ := rfl
  have hAI :
      AlgebraicIndependent ℚ
        (fun i : Fin n => S.esymm (i.1 + 1)) := by
    rw [hfamily]
    exact (spectrum_esymm_algIndep n).map'
      (f := IsScalarTower.toAlgHom ℚ R L)
      (IsFractionRing.injective
        (MvPolynomial (Fin n) ℚ)
        (FractionRing (MvPolynomial (Fin n) ℚ)))
  exact algebraicallyIndependentSpectrum_not_fixedRationalWeightedReciprocal
    hn S hcard hAI q

end

end GaloisForLFunctions
