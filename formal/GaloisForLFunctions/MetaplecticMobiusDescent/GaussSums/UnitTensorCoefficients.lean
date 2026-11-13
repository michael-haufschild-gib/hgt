/-
Unit tensor coefficients adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.HybridRows

/-!
# Unit tensor coefficients

Powerful ideal counts, column and cube weight bounds of the completed Gauss sum; unit tensor
coefficients of finite ray expansions and zero extensions of unit pairs.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open SchwartzPlanePoisson.CanonicalQuadraticSieve
open UniqueFactorizationMonoid
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
namespace CompletedGauss
theorem powerfulBase_norm_bound (I : Ideal O) (hI : PowerfulIdeal I) (X : ℝ)
    (hX : (Ideal.absNorm I:ℝ)≤ X) :
    1≤(Ideal.absNorm (quadraticSquarefreePart I):ℝ) ∧
    (Ideal.absNorm (quadraticSquarefreePart I):ℝ)≤ X ∧
    (Ideal.absNorm (powerfulBase I):ℝ)≤ Real.sqrt X/(Ideal.absNorm (quadraticSquarefreePart I):ℝ) := by
  have ha := (powerfulBase_spec I hI).1
  have hb := (quadraticSquarefreePart_squarefree I).ne_zero
  have ha1 : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => ha (Ideal.absNorm_eq_zero_iff.mp hz))
  have hb1 : 1≤(Ideal.absNorm (quadraticSquarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hb (Ideal.absNorm_eq_zero_iff.mp hz))
  have hnorm : (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (quadraticSquarefreePart I):ℝ)^3=(Ideal.absNorm I:ℝ) := by
    have h := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (powerfulBase_spec I hI).2
    simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h
  have hX0 : 0≤ X := (Nat.cast_nonneg _).trans hX
  have hb2 : (Ideal.absNorm (quadraticSquarefreePart I):ℝ)≤(Ideal.absNorm (quadraticSquarefreePart I):ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show (1:ℕ)≤3 by decide)
  have hab : ((Ideal.absNorm (powerfulBase I):ℝ)*(Ideal.absNorm (quadraticSquarefreePart I):ℝ))^2≤ X := by
    calc
      _ = (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (quadraticSquarefreePart I):ℝ)^2 := by ring
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (quadraticSquarefreePart I):ℝ)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by decide)) (sq_nonneg _)
      _ ≤ X := hnorm.trans_le hX
  have hbX : (Ideal.absNorm (quadraticSquarefreePart I):ℝ)≤ X := by
    calc
      _ ≤ (Ideal.absNorm (quadraticSquarefreePart I):ℝ)^3 := hb2
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (quadraticSquarefreePart I):ℝ)^3 :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ ha1)
      _ ≤ X := hnorm.trans_le hX
  refine ⟨hb1,hbX,?_⟩
  apply (le_div_iff₀ (by linarith : 0<(Ideal.absNorm (quadraticSquarefreePart I):ℝ))).mpr
  nlinarith [Real.sq_sqrt hX0,Real.sqrt_nonneg X]

theorem powerful_fiber_count (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤ X)
    (B : Ideal O) (hB : B∈S.image quadraticSquarefreePart) :
    ((S.filter (fun I => quadraticSquarefreePart I=B)).card:ℝ)≤128*Real.sqrt X/(Ideal.absNorm B:ℝ) := by
  obtain ⟨I,hI,hIB⟩ := Finset.mem_image.mp hB
  have hi := hS I hI
  have hnorm := powerfulBase_norm_bound I hi.1 X hi.2
  rw [hIB] at hnorm
  have hAb : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (powerfulBase_spec I hi.1).1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤ Real.sqrt X/(Ideal.absNorm B:ℝ) := hAb.trans hnorm.2.2
  let T := S.filter (fun I => quadraticSquarefreePart I=B)
  have hinj : Set.InjOn powerfulBase T := by
    intro J hJ lengthScale hL he
    exact powerfulBase_injective_on_fiber J lengthScale (hS J (Finset.mem_filter.mp hJ).1).1
      (hS lengthScale (Finset.mem_filter.mp hL).1).1
      ((Finset.mem_filter.mp hJ).2.trans (Finset.mem_filter.mp hL).2.symm) he
  have hcard : (T.image powerfulBase).card=T.card := Finset.card_image_iff.mpr hinj
  have hcount := EisensteinLatticeCount.finite_ideal_count_real (T.image powerfulBase)
    (Real.sqrt X/(Ideal.absNorm B:ℝ)) hscale (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      exact (powerfulBase_spec lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1).1) (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      have hp := powerfulBase_norm_bound lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1 X
        (hS lengthScale (Finset.mem_filter.mp hL).1).2
      simpa only [(Finset.mem_filter.mp hL).2] using hp.2.2)
  rw [hcard] at hcount
  simpa only [mul_div_assoc] using hcount

theorem powerful_ideal_count_log (S : Finset (Ideal O)) (X : ℝ) (hX : 1≤ X)
    (hS : ∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤ X) :
    (S.card:ℝ)≤32768*Real.sqrt X*(columnDyadicLength X+1:ℝ) := by
  let B := S.image quadraticSquarefreePart
  have hBn (J : Ideal O) (hJ : J∈B) : J≠0 ∧ (Ideal.absNorm J:ℝ)≤ X := by
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact ⟨(quadraticSquarefreePart_squarefree I).ne_zero,(powerfulBase_norm_bound I (hS I hI).1 X (hS I hI).2).2.1⟩
  have he : (S.card:ℝ)=∑J∈B,((S.filter (fun I => quadraticSquarefreePart I=J)).card:ℝ) := by
    calc
      _ = ∑_I∈S,(1:ℝ) := by simp
      _ = ∑J∈B,∑_I∈S.filter (fun I => quadraticSquarefreePart I=J),(1:ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem quadraticSquarefreePart hI) _).symm
      _ = _ := by simp
  rw [he]
  calc
    _ ≤ ∑J∈B,128*Real.sqrt X/(Ideal.absNorm J:ℝ) := Finset.sum_le_sum (fun J hJ => powerful_fiber_count S X hS J hJ)
    _ = (128*Real.sqrt X)*∑J∈B,1/(Ideal.absNorm J:ℝ) := by rw [Finset.mul_sum]; congr 1; ext J; ring
    _ ≤ (128*Real.sqrt X)*(256*(columnDyadicLength X+1:ℝ)) :=
      by
        have hh := InverseMoment.descent_finite_inverse_norm_sum B X
          (fun J hJ => (hBn J hJ).1) (fun J hJ => (hBn J hJ).2)
        norm_num only [show (2 : ℝ)*128=256 by norm_num] at hh
        exact mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem powerful_ideal_count (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ (S : Finset (Ideal O)) (X : ℝ), 1≤ X →
      (∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤ X) →
      (S.card:ℝ)≤ C*X^(1/2+ε) := by
  let C := 32768*(2+1/(ε*Real.log 2))
  have hC : 0< C := by have hl : 0< Real.log 2 := Real.log_pos (by norm_num); dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro S X hX hS
  apply (powerful_ideal_count_log S X hX hS).trans
  calc
    _ ≤ 32768*Real.sqrt X*((2+1/(ε*Real.log 2))*X^ε) :=
      mul_le_mul_of_nonneg_left (columnDyadicLength_small_power ε hε X hX) (by positivity)
    _ = C*X^(1/2+ε) := by
      rw [Real.rpow_add (by linarith : 0< X),←Real.sqrt_eq_rpow]
      dsimp [C]
      ring

end CompletedGauss

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical
namespace CompletedGauss

lemma columnWeight_div_sqrt_norm_le_one (Ψ : O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal O) :
    ‖columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ)‖≤1 := by
  by_cases hs : Squarefree I
  · by_cases hI : primaryIdealGenerator I = 0
    · rw [columnWeight, squarefreeGaussCoefficient_of_primary_zero I hI, zero_mul, zero_div, norm_zero]
      exact zero_le_one
    have hN : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI (by
        rw [Ideal.absNorm_eq_zero_iff.mp h]
        exact primaryIdealGenerator_zero))
    have hroot : 1≤Real.sqrt (Ideal.absNorm I:ℝ) := Real.one_le_sqrt.mpr hN
    rw [columnWeight, squarefreeGaussCoefficient, if_pos hs, norm_div, norm_mul,
      norm_mul, norm_star, norm_angularFactor _ hI,
      normalizedCubicUnitGauss_squarefree_norm I hI hs, one_mul, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_one (zero_lt_one.trans_le hroot)).mpr ((hΨ _).trans hroot)
  · simp only [columnWeight, squarefreeGaussCoefficient, if_neg hs, zero_mul, zero_div,
      norm_zero, zero_le_one]

lemma cubeWeight_norm_le_one (Ψ : O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal O) :
    ‖cubeWeight Ψ I‖≤1 := by
  by_cases hI : I=0
  · subst I; simp
  have hN : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : 0<(Ideal.absNorm I:ℝ) := lt_of_lt_of_le zero_lt_one hN
  change ‖star (angularFactor (primaryIdealGenerator I))^3 *
    Ψ (primaryIdealGenerator I)^3/(Ideal.absNorm I:ℂ)‖≤1
  rw [norm_div,norm_mul,norm_pow,norm_star,norm_pow,Complex.norm_natCast]
  apply (div_le_one hn).mpr
  apply le_trans _ hN
  calc
    _≤(1:ℝ)*1 := mul_le_mul
      (pow_le_one₀ (norm_nonneg _) (norm_angularFactor_le_one _))
      (pow_le_one₀ (norm_nonneg _) (hΨ _)) (pow_nonneg (norm_nonneg _) _) zero_le_one
    _=1 := one_mul _

end CompletedGauss
end

noncomputable section
open Eisenstein SchwartzPlanePoisson
open scoped BigOperators Classical
namespace FiniteRayExpansion
variable {R : Type*} [CommRing R] [Fintype R]
noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _
def unitTensorCoeff (f : Rˣ → Rˣ → ℂ) (χ η : MulChar R ℂ) : ℂ :=
  unitFourierCoeff (fun u => unitFourierCoeff (f u) η) χ

theorem unit_tensor_fourier_inversion (f : Rˣ → Rˣ → ℂ) (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ (u : R) * η (v : R)) = f u v := by
  calc
    _ = ∑ η : MulChar R ℂ,
        (∑ χ : MulChar R ℂ, unitTensorCoeff f χ η * χ (u : R)) * η (v : R) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = ∑ η : MulChar R ℂ, unitFourierCoeff (f u) η * η (v : R) := by
      apply Finset.sum_congr rfl
      intro η _
      change (∑ χ : MulChar R ℂ,
        unitFourierCoeff (fun a => unitFourierCoeff (f a) η) χ * χ (u : R)) * η (v : R) = _
      rw [unit_fourier_inversion]
    _ = _ := unit_fourier_inversion (f u) v

theorem unitTensorCoeff_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) (χ η : MulChar R ℂ) :
    ‖unitTensorCoeff f χ η‖ ≤ B :=
  unitFourierCoeff_norm_le _ B (fun u => unitFourierCoeff_norm_le (f u) B (hf u) η) χ

theorem unitTensorCoeff_sum_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      (Fintype.card Rˣ : ℝ) ^ 2 * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, ∑ _η : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun η _ => unitTensorCoeff_norm_le f B hf χ η))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]
      ring

theorem unitTensorCoeff_sum_norm_le_sum (f : Rˣ → Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      ∑ u : Rˣ, ∑ v : Rˣ, ‖f u v‖ := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ η : MulChar R ℂ, ∑ u : Rˣ, ‖unitFourierCoeff (f u) η‖ :=
      Finset.sum_le_sum (fun η _ => unitFourierCoeff_sum_norm_le_sum (fun u => unitFourierCoeff (f u) η))
    _ = ∑ u : Rˣ, ∑ η : MulChar R ℂ, ‖unitFourierCoeff (f u) η‖ := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun u _ => unitFourierCoeff_sum_norm_le_sum (f u))

def zeroExtendUnitPair (f : Rˣ → Rˣ → ℂ) (r s : R) : ℂ :=
  zeroExtendUnits (fun u => zeroExtendUnits (f u) s) r

theorem zeroExtendUnitPair_fourier (f : Rˣ → Rˣ → ℂ) (r s : R) :
    zeroExtendUnitPair f r s = ∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ r * η s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    by_cases hs : IsUnit s
    · obtain ⟨v, rfl⟩ := hs
      simp only [zeroExtendUnitPair, zeroExtendUnits_unit]
      exact (unit_tensor_fourier_inversion f u v).symm
    · simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_nonunit _ _ hs,
        MulChar.map_nonunit _ hs, mul_zero, Finset.sum_const_zero]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr,
      MulChar.map_nonunit _ hr, mul_zero, zero_mul, Finset.sum_const_zero]

theorem zeroExtendUnitPair_restrict (f : R → R → ℂ) (r s : R) :
    zeroExtendUnitPair (fun u v : Rˣ => f (u : R) (v : R)) r s =
      (if IsUnit r then 1 else 0) * (if IsUnit s then 1 else 0) * f r s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_restrict,
      u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]


end FiniteRayExpansion
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
