import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Zeta.MaximalPointCountSeries
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementPolynomial
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.HyperplaneTateTrace

/-!
# Local zeta factors from polynomial point counts

In the local argument of Andrusov's Proposition 49, a term `a X^j` in the
count polynomial contributes the signed power `(1-q^j T)^(-a)`.
The formal logarithmic derivative recovers every positive-degree extension
count, for both coordinate arrangements and normalized torus hyperplanes.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open PowerSeries Finset
open ArithmeticHarmonicAnalysis.Codes ArithmeticKunnethTheory.WeightFamilies
noncomputable section

/-- A positive multiplicity gives a pole and a negative multiplicity gives a zero. -/
def signedTateFactor (a : ℂ) : ℤ → PowerSeries ℂ
  | .ofNat n => geom a ^ n
  | .negSucc n => (1 - C a * X) ^ (n+1)

private theorem signedTateFactor_hasGhost (a : ℂ) (m : ℤ) :
    HasGhost (signedTateFactor a m) (m • geomTail a) := by
  cases m with
  | ofNat n => exact_mod_cast hasGhost_pow (hasGhost_geom a) n
  | negSucc n =>
    simpa only [signedTateFactor, negSucc_zsmul, nsmul_eq_mul, mul_neg] using
      hasGhost_pow (hasGhost_one_sub a) (n+1)

/-- Finite Euler factor attached to an integral counting polynomial. -/
def polynomialCountZeta (P : Polynomial ℤ) (q : ℂ) : PowerSeries ℂ :=
  ∏ j ∈ P.support, signedTateFactor (q^j) (P.coeff j)

/-- Ghost sequence whose positive coefficients are the extension counts. -/
def polynomialCountSeries (P : Polynomial ℤ) (q : ℂ) : PowerSeries ℂ :=
  mk fun n => if n = 0 then 0 else P.eval₂ (Int.castRingHom ℂ) (q^n)

theorem polynomialCountZeta_constant (P : Polynomial ℤ) (q : ℂ) :
    constantCoeff (polynomialCountZeta P q) = 1 := by
  rw [polynomialCountZeta, map_prod]
  apply prod_eq_one
  intro j _
  cases P.coeff j <;> simp [signedTateFactor, geom]

/-- All extension counts are realized by the signed finite Euler product. -/
theorem polynomialCountZeta_hasGhost (P : Polynomial ℤ) (q : ℂ) :
    HasGhost (polynomialCountZeta P q) (polynomialCountSeries P q) := by
  have h := hasGhost_prod P.support (fun j => signedTateFactor (q^j) (P.coeff j))
    (fun j => P.coeff j • geomTail (q^j)) (fun j _ => signedTateFactor_hasGhost _ _)
  have he : (∑ j ∈ P.support, P.coeff j • geomTail (q^j)) = polynomialCountSeries P q := by
    ext n
    simp only [polynomialCountSeries, coeff_mk, map_sum, map_zsmul, geomTail]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [if_neg hn, zsmul_eq_mul, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      refine sum_congr rfl fun j _ => ?_
      rw [← pow_mul, ← pow_mul, Nat.mul_comm j n]
      rfl
  exact he ▸ h

/-- Normalization at the constant term makes the point-count Euler factor unique. -/
theorem polynomialCountZeta_eq_iff (Z : PowerSeries ℂ) (P : Polynomial ℤ) (q : ℂ) :
    Z = polynomialCountZeta P q ↔ constantCoeff Z = 1 ∧ HasGhost Z (polynomialCountSeries P q) := by
  constructor
  · rintro rfl
    exact ⟨polynomialCountZeta_constant _ _, polynomialCountZeta_hasGhost _ _⟩
  · rintro ⟨h0,hZ⟩
    exact eq_of_hasGhost hZ (polynomialCountZeta_hasGhost _ _)
      (h0.trans (polynomialCountZeta_constant _ _).symm) (by simp [polynomialCountSeries])

/-- Addition of count polynomials multiplies their local factors, including cancellations
of coefficients of opposite sign. -/
theorem polynomialCountZeta_add (P Q : Polynomial ℤ) (q : ℂ) :
    polynomialCountZeta (P+Q) q = polynomialCountZeta P q * polynomialCountZeta Q q := by
  symm
  apply (polynomialCountZeta_eq_iff _ _ _).mpr
  refine ⟨by simp [polynomialCountZeta_constant], ?_⟩
  have he : polynomialCountSeries (P+Q) q = polynomialCountSeries P q + polynomialCountSeries Q q := by
    ext n
    by_cases h : n = 0 <;> simp [h, polynomialCountSeries]
  rw [he]
  exact hasGhost_mul (polynomialCountZeta_hasGhost _ _) (polynomialCountZeta_hasGhost _ _)

/-- A single local Euler factor recovers the entire integral count polynomial.
Its ghost sequence evaluates the polynomial on an infinite geometric progression. -/
theorem polynomialCountZeta_injective (q : ℕ) :
    Function.Injective (fun P => polynomialCountZeta P ((Int.castRingHom ℂ) ((q:ℤ)+2))) := by
  let b : ℤ := (q:ℤ)+2
  let f := Int.castRingHom ℂ
  intro P Q h
  change polynomialCountZeta P (f b) = polynomialCountZeta Q (f b) at h
  have hne : polynomialCountZeta Q (f b) ≠ 0 := by
    intro hz
    have h0 := polynomialCountZeta_constant Q (f b)
    rw [hz, map_zero] at h0
    exact zero_ne_one h0
  have hP := polynomialCountZeta_hasGhost P (f b)
  rw [h] at hP
  have hQ := polynomialCountZeta_hasGhost Q (f b)
  have hg : polynomialCountSeries P (f b) = polynomialCountSeries Q (f b) :=
    mul_left_cancel₀ hne (hP.symm.trans hQ)
  have hb : 1 < b := by dsimp [b]; omega
  have hinj : Function.Injective (fun n : ℕ => b^(n+1)) :=
    (pow_right_strictMono₀ hb).injective.comp Nat.succ_injective
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n,rfl⟩
  have hn := congrArg (coeff (n+1)) hg
  simp only [polynomialCountSeries,coeff_mk,Nat.succ_ne_zero,if_false] at hn
  rw [← map_pow, Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply] at hn
  exact Int.cast_injective hn

/-- At every fixed field order, arrangements have identical local zeta factors
exactly when every codimension layer has the same size. -/
theorem arrangementZeta_eq_iff {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℕ)
    (K : Finset (Finset ι)) (L : Finset (Finset κ)) :
    polynomialCountZeta (arrangementPolynomial K) ((Int.castRingHom ℂ) ((q:ℤ)+2)) =
      polynomialCountZeta (arrangementPolynomial L) ((Int.castRingHom ℂ) ((q:ℤ)+2)) ↔
      ∀ d, (K.filter fun s : Finset ι => Fintype.card ι - s.card = d).card =
        (L.filter fun s : Finset κ => Fintype.card κ - s.card = d).card :=
  (polynomialCountZeta_injective q).eq_iff.trans (arrangementPolynomial_eq_iff K L)

/-- Over a finite extension, the ghost coefficient is the actual coordinate-arrangement count. -/
theorem arrangementCountSeries_extension {ι F E : Type*} [Fintype ι] [Field F] [Fintype F]
    [Field E] [Fintype E] [Algebra F E] (K : Finset (Finset ι)) :
    coeff (Module.finrank F E) (polynomialCountSeries (arrangementPolynomial K) (Fintype.card F : ℂ)) =
      ((arrangementWords (fun _ : ι => ({0} : Finset E)) K).card : ℂ) := by
  have hn := (Module.finrank_pos (R := F) (M := E)).ne'
  rw [polynomialCountSeries, coeff_mk, if_neg hn, ← Nat.cast_pow,
    ← Module.card_eq_pow_finrank (K := F) (V := E)]
  have he := Polynomial.eval₂_at_apply (p := arrangementPolynomial K)
      (Int.castRingHom ℂ) (Fintype.card E : ℤ)
  simpa only [Int.coe_castRingHom, Int.cast_natCast, eval_arrangementPolynomial] using he

/-- The normalized Kloosterman torus hyperplanes have the same finite-product law. -/
theorem hyperplaneCountSeries_extension (m : ℕ) (F E : Type*) [Field F] [Fintype F] [Field E]
    [Fintype E] [DecidableEq E] [Algebra F E] :
    coeff (Module.finrank F E) (polynomialCountSeries (hyperplanePolynomial m) (Fintype.card F : ℂ)) =
      ((normalizedCoordinateZeroTorus (F := E) m).card : ℂ) := by
  rw [polynomialCountSeries, coeff_mk, if_neg (Module.finrank_pos (R := F) (M := E)).ne',
    ← hyperplaneTateTrace_eq_eval₂]
  exact hyperplaneTateTrace_extension_count (F := F) m E

#print axioms polynomialCountZeta_eq_iff
#print axioms polynomialCountZeta_add
#print axioms polynomialCountZeta_injective
#print axioms arrangementZeta_eq_iff
#print axioms arrangementCountSeries_extension
#print axioms hyperplaneCountSeries_extension

end
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
