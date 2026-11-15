import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFinitePlaceCenters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityPlace

/-!
# Classification of places with a coordinate pole

Inverting the coordinate puts every pole place on the infinity chart.
Its center lies over the origin there, whose unique extension identifies
the original valuation ring with the canonical infinity place.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry.ValuationInertia

/-- Inverting the Kummer coordinate exchanges the two affine parameters. -/
theorem kummerInfinityFieldEquiv_symm_coordinate {K : Type*} [Field K]
    (c : Kˣ) (b R n : ℕ) :
    (kummerInfinityFieldEquiv c b R n).symm
      (algebraMap K[X] (KummerInfinityField c b R n) X) =
      (algebraMap K[X] (KummerBranchField c b R n) X)⁻¹ := by
  apply (kummerInfinityFieldEquiv c b R n).injective
  rw [AlgEquiv.apply_symm_apply, map_inv₀, kummerInfinityFieldEquiv_coordinate, inv_inv]

/-- Every proper constant valuation ring where the original coordinate has a pole is the unique infinity place. -/
theorem squareKummer_infinityPlace_of_coordinate_notMem
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
    (W : ValuationSubring (SquareKummerField p s c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r))) (hW : W ≠ ⊤)
    (hK : ∀ a : SquareConstantField p s, algebraMap (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) a ∈ W)
    (hX : algebraMap (SquareConstantField p s)[X]
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X ∉ W) :
    W = ((squareKummerInfinityPlace p s c d r).valuation
      (KummerInfinityField c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)))).valuationSubring.comap
        (kummerInfinityFieldEquiv c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
          (p ^ (s + 1))).toRingHom := by
  let K := SquareConstantField p s
  let b := p ^ (d + 1) - 2
  let R := kummerExponent (p ^ (d + 1)) r
  let L := SquareKummerField p s c b R
  let L' := KummerInfinityField c b R (p ^ (s + 1))
  let B := SquareKummerInfinityNormalization p s c b R
  let e := kummerInfinityFieldEquiv c b R (p ^ (s + 1))
  let W' := W.comap e.symm.toRingHom
  have hW' : W' ≠ ⊤ := by
    intro h
    apply hW
    apply top_unique
    intro x _
    have hx : e x ∈ W' := by rw [h]; trivial
    change e.symm (e x) ∈ W at hx
    simpa only [e.symm_apply_apply] using hx
  have hK' : ∀ a : K, algebraMap K L' a ∈ W' := by
    intro a
    change e.symm (algebraMap K L' a) ∈ W
    rw [e.symm.commutes]
    exact hK a
  have hX' : algebraMap K[X] L' X ∈ W' := by
    change e.symm (algebraMap K[X] L' X) ∈ W
    rw [kummerInfinityFieldEquiv_symm_coordinate]
    exact (W.mem_or_inv_mem _).resolve_left hX
  have hA := polynomial_algebraMap_mem_valuationSubring W' hK' hX'
  have hB : ∀ a : B, algebraMap B L' a ∈ W' := integralClosure_mem_of_base_mem W' hA
  let P := centerPrime W' hB
  have hxP : algebraMap K[X] B X ∈ P := by
    by_contra hx
    have hi := inv_mem_of_notMem_centerPrime W' hB hx
    rw [← IsScalarTower.algebraMap_apply K[X] B L'] at hi
    change e.symm ((algebraMap K[X] L' X)⁻¹) ∈ W at hi
    rw [map_inv₀, kummerInfinityFieldEquiv_symm_coordinate, inv_inv] at hi
    exact hX hi
  have hmax : (Ideal.span {(X : K[X])}).IsMaximal :=
    (kummerInfinityBasePlace (K := K)).isPrime.isMaximal (kummerInfinityBasePlace (K := K)).ne_bot
  have hproper : P.under K[X] ≠ ⊤ := by
    intro h
    have h1 : (1 : K[X]) ∈ P.under K[X] := by rw [h]; trivial
    change algebraMap K[X] B 1 ∈ P at h1
    rw [map_one] at h1
    exact (show P.IsPrime from inferInstance).ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  have hover : P.LiesOver (Ideal.span {(X : K[X])}) := by
    apply (Ideal.liesOver_iff P _).mpr
    apply hmax.eq_of_le hproper
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hxP
  obtain ⟨P₀, _, huniq⟩ := squareKummerInfinity_unique p s c d r
  have hP : P = squareKummerInfinityIdeal p s c d r :=
    (huniq P ⟨inferInstance, hover⟩).trans (huniq _ ⟨inferInstance, inferInstance⟩).symm
  have hw : centerHeightOne W' hB hW' = squareKummerInfinityPlace p s c d r :=
    HeightOneSpectrum.ext hP
  have hval := valuationSubringAtPrime_eq W' hB hW'
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, hw] at hval
  change W = ((squareKummerInfinityPlace p s c d r).valuation L').valuationSubring.comap e.toRingHom
  rw [hval]
  ext x
  change x ∈ W ↔ e.symm (e x) ∈ W
  rw [e.symm_apply_apply]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
