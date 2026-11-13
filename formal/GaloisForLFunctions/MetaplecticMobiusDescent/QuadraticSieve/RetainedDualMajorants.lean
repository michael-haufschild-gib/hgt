/-
Retained dual majorants adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.PrincipalMajorantsAndBadSectors
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.TruncatedPrincipalPoisson

/-!
# Retained dual majorants

The low squarefree source has the same principal, middle and error decomposition as the
full sum. Divisor estimates absorb the prime-mask terms in the truncation error; the retained
dual majorant `retainedDualMajorant` controls the principal differences dyadically.
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

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap

theorem symmetric_truncation_scales (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    0 < X ∧ 0 < X₀/T ∧ X₀/T ≤ X ∧ X ≤ T*X₀ ∧ 0 ≤ T^4 := by
  have hT0 : 0 < T := by linarith
  have hX : 0 < X := by linarith
  refine ⟨hX,div_pos hX₀ hT0,?_,?_,by positivity⟩
  · apply (div_le_iff₀ hT0).mpr
    nlinarith
  · nlinarith

theorem symmetric_truncation_scalar_bound (m : ℕ) (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    ((X₀/T)/X)^(m+3) + 1/(1+(T*X₀)/X)^(m+3) +
      (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤
      (2 : ℝ)^(m+10)/T^m := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 < X := by linarith
  have hY : 0 < X₀/T := div_pos hX₀ hT0
  have hratio : (X₀/T)/X ≤ 2/T := by
    apply (div_le_iff₀ hX).mpr
    calc
      X₀/T ≤ (2*X)/T := div_le_div_of_nonneg_right (by linarith) hT0.le
      _ = (2/T)*X := by ring
  have hinv : 1/(1+(T*X₀)/X) ≤ 2/T := by
    have hz : T/2 ≤ (T*X₀)/X := (le_div_iff₀ hX).mpr (by nlinarith)
    calc
      _ ≤ 1/(T/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = 2/T := by field_simp
  have hpow : (2/T)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hT0 m)
      (pow_le_pow_right₀ hT1 (by omega : m ≤ m+3))
  have h₁ : ((X₀/T)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m :=
    (pow_le_pow_left₀ (by positivity) hratio _).trans hpow
  have h₂ : 1/(1+(T*X₀)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    simpa only [div_pow,one_pow] using (pow_le_pow_left₀ (by positivity) hinv (m+3)).trans hpow
  have hnum : X/(X₀/T) ≤ 2*T := by
    apply (div_le_iff₀ hY).mpr
    have he : 2*T*(X₀/T) = 2*X₀ := by field_simp
    rw [he]
    exact hhi
  have hmin : 1/(2*T) ≤ min 1 (X/(T*X₀)) := by
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
      linarith
    · apply (le_div_iff₀ (mul_pos hT0 hX₀)).mpr
      have he : 1/(2*T)*(T*X₀)=X₀/2 := by field_simp
      rwa [he]
  have hfreq : T ≤ 1+X*T^4/(T*X₀) := by
    have ht2 : 2 ≤ T^2 := by nlinarith
    have ht4 : 2*T^2 ≤ T^4 := by nlinarith [sq_nonneg (T^2-2)]
    have hprod : T*(T*X₀) ≤ X*T^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sq_nonneg (T^2))]
    have hh := (le_div_iff₀ (mul_pos hT0 hX₀)).mpr hprod
    linarith
  have hden : (1/(2*T))^2*T^(m+3) ≤
      (min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3) := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hmin 2)
      (pow_le_pow_left₀ hT0.le hfreq (m+3)) (by positivity) (by positivity)
  have h₃ : (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤ 8/T^m := by
    calc
      _ ≤ (2*T)/((1/(2*T))^2*T^(m+3)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by rw [pow_add]; field_simp; ring
  have hc : 2*(2 : ℝ)^(m+3)+8 ≤ (2 : ℝ)^(m+10) := by
    have hm : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
    rw [pow_add,pow_add]
    norm_num
    nlinarith
  calc
    _ ≤ (2 : ℝ)^(m+3)/T^m + (2 : ℝ)^(m+3)/T^m + 8/T^m := add_le_add (add_le_add h₁ h₂) h₃
    _ = (2*(2 : ℝ)^(m+3)+8)/T^m := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

theorem truncationError_symmetric_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖truncationError P S W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_bound (m + 3)
  refine ⟨s, C * 2 ^ (m + 10), by positivity, ?_⟩
  intro ι _ P _ hinj S W X₀ X T hX₀ hlo hhi hT
  obtain ⟨hX, hY, hYX, hXZ, hL⟩ := symmetric_truncation_scales X₀ X T hX₀ hlo hhi hT
  have hp := hb P hinj S W X (X₀ / T) (T * X₀) (T ^ 4) hX hY hYX hXZ hL
  have hs := symmetric_truncation_scalar_bound m X₀ X T hX₀ hlo hhi hT
  calc
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (((X₀ / T) / X) ^ (m + 3) + 1 / (1 + (T * X₀) / X) ^ (m + 3) +
          (X / (X₀ / T)) / ((min 1 (X / (T * X₀))) ^ 2 * (1 + X * T ^ 4 / (T * X₀)) ^ (m + 3))) := hp
    _ ≤ (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * (2 ^ (m + 10) / T ^ m) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace TruncatedPrincipalPoisson
open Eisenstein SchwartzPlanePoisson MeasureTheory UniqueFactorizationMonoid
open scoped SchwartzMap

/-- The low squarefree source has the same exact principal, middle, and error decomposition. -/
theorem quadraticLowPrincipalIdeal_truncated (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ))
    (X Y Z L : ℝ) (hX : 0 < X) :
    (Nat.card Oˣ : ℂ) * quadraticLowPrincipalIdeal I J W X =
      principalTruncation (fun P : primeSupport (quadraticMaskIdeal (I.val * J.val)) => P.val)
        Finset.univ (quadraticSquareProfile W) X Z +
      middleTruncation (fun P : primeSupport (quadraticMaskIdeal (I.val * J.val)) => P.val)
        Finset.univ (quadraticSquareProfile W) X Y Z L +
      truncationError (fun P : primeSupport (quadraticMaskIdeal (I.val * J.val)) => P.val)
        Finset.univ (quadraticSquareProfile W) X Y Z L := by
  rw [← quadraticLowPrincipalLattice_eq I J W X hX]
  unfold truncationError quadraticLowPrincipalLattice
  have he (z : O) :
      rowCoprimeMask (fun P : primeSupport (quadraticMaskIdeal (I.val * J.val)) => P.val) Finset.univ z =
      primeCoprimeMask cubicIdealGenerator (quadraticMaskPrimes (I.val * J.val)) z := by
    simp only [rowCoprimeMask, primeCoprimeMask]
    rw [Finset.prod_coe_sort (s := primeSupport (quadraticMaskIdeal (I.val * J.val)))
      (f := fun P : Ideal O => (1 : ℂ) - if cubicIdealGenerator P ∣ z then 1 else 0),
      primeSupport_quadraticMaskIdeal]
  simp_rw [he]
  have hz (z : O) :
      primeCoprimeMask cubicIdealGenerator (quadraticMaskPrimes (I.val * J.val)) z *
        (if z = 0 then 0 else quadraticSquareProfile W (‖ringComplex z‖ ^ 2 / X)) =
      primeCoprimeMask cubicIdealGenerator (quadraticMaskPrimes (I.val * J.val)) z *
        W ((‖ringComplex z‖ ^ 2 / X) ^ 2) := by
    by_cases h : z = 0
    · subst z
      rw [primeCoprimeMask_zero cubicIdealGenerator (quadraticMaskPrimes (I.val * J.val))
        ⟨ramifiedIdeal, Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩]
      simp only [zero_mul]
    · rw [if_neg h, quadraticSquareProfile_apply]
  simp_rw [hz]
  ring

end TruncatedPrincipalPoisson

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap

lemma squarefree_primeSupport_card (G : Ideal O) (hG : Squarefree G) :
    (2 : ℝ) ^ (primeSupport G).card = (idealDivisors G).card := by
  have h := squarefree_ideal_divisor_sum G hG (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powerset] at h
  exact_mod_cast h.symm

/-- Divisor estimates absorb the number of prime-mask terms in the truncation error. -/
theorem squarefree_truncation_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (G : Ideal O), Squarefree G →
        ∀ (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
          0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
          ‖truncationError (fun P : primeSupport G => P.val) Finset.univ W
            X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
            (divisorConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε) *
              (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_symmetric_bound m
  refine ⟨s, C, hC, ?_⟩
  intro ε hε G hG W X₀ X T hX₀ hlo hhi hT
  letI : ∀ P : primeSupport G, P.val.IsMaximal := fun P =>
    (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal (support_prime P.property).ne_zero
  have hh := hb (fun P : primeSupport G => P.val) Subtype.val_injective Finset.univ W
    X₀ X T hX₀ hlo hhi hT
  simp only [Finset.card_univ, Fintype.card_coe, squarefree_primeSupport_card G hG] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 G hG.ne_zero

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap

lemma primeSupport_card_le_divisor_card (G : Ideal O) (hG : G ≠ 0) :
    (2 : ℝ) ^ (primeSupport G).card ≤ (idealDivisors G).card := by
  have hi : Set.InjOn (fun S : Finset (Ideal O) => ∏ P ∈ S, P) (primeSupport G).powerset := by
    intro S hS T hT h
    exact support_product_injective (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) h
  have hle := Finset.card_le_card (show (idealDivisors G).filter Squarefree ⊆ idealDivisors G from
    fun _ h => (Finset.mem_filter.mp h).1)
  rw [squarefree_divisors_eq_image G hG, Finset.card_image_iff.mpr hi, Finset.card_powerset] at hle
  exact_mod_cast hle

/-- Arbitrary conductor multiplicities are absorbed by the native ideal-divisor estimate. -/
theorem primeSupport_truncation_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (G : Ideal O), G ≠ 0 →
        ∀ (W : 𝓢(ℝ, ℂ)) (X₀ X T : ℝ),
          0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
          ‖truncationError (fun P : primeSupport G => P.val) Finset.univ W
            X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
            (divisorConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε) *
              (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_symmetric_bound m
  refine ⟨s, C, hC, ?_⟩
  intro ε hε G hG W X₀ X T hX₀ hlo hhi hT
  letI : ∀ P : primeSupport G, P.val.IsMaximal := fun P =>
    (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal (support_prime P.property).ne_zero
  have hh := hb (fun P : primeSupport G => P.val) Subtype.val_injective Finset.univ W
    X₀ X T hX₀ hlo hhi hT
  simp only [Finset.card_univ, Fintype.card_coe] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact (primeSupport_card_le_divisor_card G hG).trans
    ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 G hG)

/-- Source principal truncation uses the fixed mask and the square profile. -/
def lowPrincipalError (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ)) (X Y Z L : ℝ) : ℂ :=
  truncationError (fun P : primeSupport (quadraticMaskIdeal (I.val * J.val)) => P.val)
    Finset.univ (quadraticSquareProfile W) X Y Z L

theorem lowPrincipal_symmetric_error_bound (m : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (I J : QuadraticIdeal) (W : 𝓢(ℝ, ℂ))
        (N X₀ X T : ℝ), 1 ≤ N → (Ideal.absNorm I.val : ℝ) ≤ N → (Ideal.absNorm J.val : ℝ) ≤ N →
        0 < X₀ → X₀ / 2 ≤ X → X ≤ 2 * X₀ → 4 ≤ T →
        ‖lowPrincipalError I J W X (X₀ / T) (T * X₀) (T ^ 4)‖ ≤
          (divisorConstant ε hε * (Ideal.absNorm (quadraticMaskIdeal 1) : ℝ) ^ ε * (N*N) ^ ε) *
            (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ m := by
  obtain ⟨s, C, hC, hb⟩ := primeSupport_truncation_error_bound m
  refine ⟨s, C, hC, ?_⟩
  intro ε hε I J W N X₀ X T hN hI hJ hX₀ hlo hhi hT
  have hsI : quadraticSupported I.val := ⟨I.property.1, I.property.2.2⟩
  have hsJ : quadraticSupported J.val := ⟨J.property.1, J.property.2.2⟩
  have hn : (Ideal.absNorm (quadraticMaskIdeal (I.val * J.val)) : ℝ) ≤
      (Ideal.absNorm (quadraticMaskIdeal 1) : ℝ) * (N*N) := by
    apply (quadraticMaskIdeal_norm_bound _ ((quadraticSupported_mul _ _).mpr ⟨hsI, hsJ⟩)).trans
    rw [map_mul, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hI hJ (Nat.cast_nonneg _) (by linarith)) (Nat.cast_nonneg _)
  have hh := hb ε hε (quadraticMaskIdeal (I.val * J.val)) (quadraticMaskIdeal_squarefree _).ne_zero
    (quadraticSquareProfile W) X₀ X T hX₀ hlo hhi hT
  change ‖lowPrincipalError I J W X (X₀/T) (T*X₀) (T^4)‖ ≤ _ at hh
  apply hh.trans
  have hd := (divisorConstant_pos ε hε).le
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg _) hn hε.le
  rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity : 0 ≤ N*N)] at hp
  have hc : divisorConstant ε hε * (Ideal.absNorm (quadraticMaskIdeal (I.val * J.val)) : ℝ)^ε ≤
      divisorConstant ε hε * (Ideal.absNorm (quadraticMaskIdeal 1) : ℝ)^ε * (N*N)^ε := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hd
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap

variable {m n : Type*} [Fintype m] [Fintype n]

def lowPrincipalErrorSum (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    lowPrincipalError (cols j) (cols k) W
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)))
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) / T)
      (T * Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) (T ^ 4)

theorem lowPrincipal_actual_error_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n],
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 4 ≤ T →
        ∀ (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal),
          Function.Injective rows → Function.Injective cols →
          (∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ B) →
          (∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖lowPrincipalErrorSum rows cols a W M T‖ ≤
            (diagonalControl sieveCutoff) ^ 2 * B * N *
              ((divisorConstant ε hε * (Ideal.absNorm (quadraticMaskIdeal 1) : ℝ) ^ ε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ l) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := lowPrincipal_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro m n _ _ ε hε B N M T hB hN hM hT rows cols hr hc hrows hcols a W
  let E := (divisorConstant ε hε * (Ideal.absNorm (quadraticMaskIdeal 1) : ℝ) ^ ε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    lowPrincipalError (cols j) (cols k) W
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)))
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) / T)
      (T * Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) (T ^ 4)
  have hsc := (divisorConstant_pos ε hε).le
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ E := by
    have hi : 0 < (Ideal.absNorm (rows i).val : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal _ (rows i).property.1))
    have hX : 0 < Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) := Real.sqrt_pos.mpr (div_pos hM hi)
    have hh := hb ε hε (cols j) (cols k) W N _ _ T hN (hcols j) (hcols k) hX
      (show Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) / 2 ≤ Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) by linarith)
      (show Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) ≤ 2 * Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) by linarith) hT
    change ‖error i j k‖ ≤ _ at hh
    exact hh
  exact original_pair_error_ideal_bound rows cols hr hc B N hB hN hrows hcols a E hE error herr

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap

theorem sqrt_product_column_shell (N i j : ℝ) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    N / 2 ≤ Real.sqrt (i * j) ∧ Real.sqrt (i * j) ≤ N := by
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hlo : (N / 2) ^ 2 ≤ i * j := by
    simpa only [pow_two] using mul_le_mul hi.1 hj.1 (by linarith : 0 ≤ N / 2) hi0.le
  have hhi : i * j ≤ N ^ 2 := by
    simpa only [pow_two] using mul_le_mul hi.2 hj.2 hj0.le hN.le
  have hs := Real.sq_sqrt (mul_pos hi0 hj0).le
  have hp := Real.sqrt_nonneg (i * j)
  constructor <;> nlinarith

theorem dual_truncation_reference_bounds (M F b N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    0 < N * Real.sqrt (F / (M * b)) ∧
      (N * Real.sqrt (F / (M * b))) / 2 ≤ Real.sqrt (F * i * j / (M * b)) ∧
      Real.sqrt (F * i * j / (M * b)) ≤ 2 * (N * Real.sqrt (F / (M * b))) := by
  have hr : 0 < Real.sqrt (F / (M * b)) := Real.sqrt_pos.mpr (by positivity)
  have he : Real.sqrt (F * i * j / (M * b)) = Real.sqrt (F / (M * b)) * Real.sqrt (i * j) := by
    rw [← Real.sqrt_mul (show 0 ≤ F / (M * b) by positivity)]
    congr 1
    ring
  obtain ⟨hlo, hhi⟩ := sqrt_product_column_shell N i j hN hi hj
  refine ⟨mul_pos hN hr, ?_, ?_⟩
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hlo hr.le]
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hhi hr.le, mul_pos hN hr]

theorem dual_truncation_prefactor_bound (M F N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    M / (Real.sqrt (i * j) * F) ≤ 2 * M / (F * N) := by
  obtain ⟨hlo, _⟩ := sqrt_product_column_shell N i j hN hi hj
  calc
    _ ≤ M / ((N / 2) * F) := div_le_div_of_nonneg_left hM.le (by positivity)
      (mul_le_mul_of_nonneg_right hlo hF.le)
    _ = _ := by field_simp

theorem unrestricted_pair_error_ideal_bound {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (B N : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hrows : ∀ i, (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (a : n → ℂ) (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (he : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ ≤
      (diagonalControl sieveCutoff) ^ 2 * B * N * E * ∑ j, ‖a j‖ ^ 2 := by
  have hcr := finite_ideal_family_card_bound rows hr B hB hrows
  have hcc := finite_ideal_family_card_bound (fun j => (cols j).val)
    (Subtype.val_injective.comp hc) N hN hcols
  have hd := diagonalControl_nonneg sieveCutoff
  apply (finite_pair_error_bound (unrestrictedPairTerm rows cols cols a a) error a E hE
    (unrestrictedPairTerm_norm_le rows cols cols a a) he).trans
  calc
    _ ≤ (diagonalControl sieveCutoff * B) * (diagonalControl sieveCutoff * N) * E * ∑ j, ‖a j‖ ^ 2 := by
      gcongr
    _ = _ := by ring

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def unrestrictedDualPrincipalErrorSum (rows : m → Ideal O) (cols : n → QuadraticIdeal) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M F N T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (cols j).val : ℝ) * (Ideal.absNorm (cols k).val : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primeSupport ((cols j).val * (cols k).val) => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j).val : ℝ) * (Ideal.absNorm (cols k).val : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))

theorem unrestrictedDualPrincipal_actual_error_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n],
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M F T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 0 < F → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → QuadraticIdeal),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, N / 2 ≤ (Ideal.absNorm (cols j).val : ℝ) ∧ (Ideal.absNorm (cols j).val : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖unrestrictedDualPrincipalErrorSum rows cols a W M F N T‖ ≤
            (diagonalControl sieveCutoff) ^ 2 * B * N *
              ((2 * M / (F * N)) * ((divisorConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l)) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := primeSupport_truncation_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro m n _ _ ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols a W
  let E₀ := (divisorConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    (((M / (Real.sqrt ((Ideal.absNorm (cols j).val : ℝ) * (Ideal.absNorm (cols k).val : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primeSupport ((cols j).val * (cols k).val) => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j).val : ℝ) * (Ideal.absNorm (cols k).val : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))
  have hsc := (divisorConstant_pos ε hε).le
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ (2 * M / (F * N)) * E₀ := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    obtain ⟨hX₀, hlo, hhi⟩ := dual_truncation_reference_bounds M F (Ideal.absNorm (rows i)) N
      (Ideal.absNorm (cols j).val) (Ideal.absNorm (cols k).val) hM hF hi (by linarith) (hcols j) (hcols k)
    have hh := hb ε hε ((cols j).val * (cols k).val) (mul_ne_zero (primaryIdealGenerator_ne_zero_ideal _ (cols j).property.1)
      (primaryIdealGenerator_ne_zero_ideal _ (cols k).property.1)) W
      _ _ T hX₀ hlo hhi hT
    simp only [map_mul, Nat.cast_mul] at hh
    have he : ‖truncationError (fun P : primeSupport ((cols j).val * (cols k).val) => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j).val : ℝ) * (Ideal.absNorm (cols k).val : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4)‖ ≤ E₀ := by
      apply hh.trans
      dsimp only [E₀]
      gcongr
      · exact (hcols j).2
      · exact (hcols k).2
    dsimp only [error]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul
      (dual_truncation_prefactor_bound M F N (Ideal.absNorm (cols j).val) (Ideal.absNorm (cols k).val)
        hM hF (by linarith) (hcols j) (hcols k)) he (norm_nonneg _) (by positivity)
  exact unrestricted_pair_error_ideal_bound rows cols hr hc B N hB hN (fun i => (hrows i).2)
    (fun j => (hcols j).2) a _ (by positivity) error herr

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap

theorem sum_two_finite_subtypes {α β A : Type*} [AddCommMonoid A]
    (S : Finset α) (T : Finset β) (f : α → β → A) :
    (∑ a : S, ∑ b : T, f a.val b.val) = ∑ a ∈ S, ∑ b ∈ T, f a b := by
  rw [Finset.sum_coe_sort S (fun a => ∑ b : T, f a b.val)]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_coe_sort T (f a))

theorem finite_middle_triangle
    {m n p H D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype H] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → H → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d‖ ≤
      ∑ h, ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k h d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d) =
      ∑ h, ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k h d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset m)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro h hh
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

theorem finite_nonzero_frequency_sum_le (H : Finset O) (hH : ∀ h ∈ H, h ≠ 0)
    (f : O → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hs : Summable (fun h : {h : O // h ≠ 0} => f h.val)) :
    (∑ h ∈ H, f h) ≤ ∑' h : {h : O // h ≠ 0}, f h.val := by
  classical
  let e : H → {h : O // h ≠ 0} := fun h => ⟨h.val, hH h.val h.property⟩
  have he : Function.Injective e := by
    intro h k hh
    apply Subtype.ext
    exact congrArg (fun x : {h : O // h ≠ 0} => x.val) hh
  have hsH : Summable (fun h : H => f h.val) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  have hb := hsH.tsum_le_tsum_of_inj e he (fun h _ => hf h.val) (fun _ => le_rfl) hs
  rw [tsum_fintype, Finset.sum_coe_sort H f] at hb
  exact hb

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap

theorem norm_double_sum_real_factor_fun {n p : Type*} [Fintype n] [Fintype p]
    (u z : n → p → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z j k)‖ = c * ‖∑ j, ∑ k, u j k * z j k‖ := by
  have he : (∑ j, ∑ k, u j k * ((c : ℂ) * z j k)) =
      (c : ℂ) * ∑ j, ∑ k, u j k * z j k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → QuadraticIdeal)
    (left : n → QuadraticIdeal) (right : p → QuadraticIdeal) (M F : ℝ) (h : O)
    (d : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  ((Real.sqrt ((M / F) / (Ideal.absNorm (rows i).val : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
      (M * (Ideal.absNorm (rows i).val : ℝ))) * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def dualProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ (left j).val * (right k).val then
      originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualProductDivisorMiddleAt W K rows left right a b M F P h := by
  classical
  unfold dualProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0)
    (hS : ∀ j D, D ∣ (left j).val → D ∈ S) (hT : ∀ k E, E ∣ (right k).val → E ∈ T) :
    dualProductDivisorMiddleAt W K rows left right a b M F P h ≤
      dualMiddleWindowAt W S T rows left right a b M F (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i j k => dualPrincipalKernel W rows left right M F h d i j k)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [dualMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold dualPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor_fun _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.dual_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i).val : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool (fun j => (left j).val)
  let T := columnDivisorPool (fun k => (right k).val)
  have hl0 : ∀ j, (left j).val ≠ 0 := fun j => primaryIdealGenerator_ne_zero_ideal _ (left j).property.1
  have hr0 : ∀ k, (right k).val ≠ 0 := fun k => primaryIdealGenerator_ne_zero_ideal _ (right k).property.1
  have hs := hexp.dual_middle_pool deltaLoss hδ ε hε S T B N M F U hB hN hM hF hU
    (columnDivisorPool_norm_bounds (fun j => (left j).val) hl0 N (fun j => (hleft j).2))
    (columnDivisorPool_norm_bounds (fun k => (right k).val) hr0 N (fun k => (hright k).2))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := dualProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M F P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd (fun j => (left j).val) hl0) (mem_columnDivisorPool_of_dvd (fun k => (right k).val) hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => dualProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M F P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primeSupport ((left j).val * (right k).val) => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) (Y i) (Z i) lengthScale

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem original_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
     
    (hK : ∀ j k d, d ∣ (left j).val * (right k).val → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      middleTruncation (fun P : primeSupport ((left j).val * (right k).val) => P.val) Finset.univ W
        (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) (Y i) (Z i) lengthScale =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ (left j).val * (right k).val then
            originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ (left j).val * (right k).val then
          originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
        else 0 else 0))]
  by_cases hc : (left j).val ⊔ (right k).val = ⊤
  · have hsq : Squarefree ((left j).val * (right k).val) :=
      squarefree_mul_iff.mpr ⟨(Ideal.isCoprime_iff_sup_eq.mpr hc).isRelPrime, (left j).property.2.1, (right k).property.2.1⟩
    rw [middleTruncation_eq_ideal_frequencies _ hsq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← divisorPool_filter K ((left j).val * (right k).val) hsq.ne_zero (hK j k), Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ (left j).val * (right k).val
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, originalPrincipalKernel]
        ring
      · simp only [hdv, hp, ite_true, ite_false, mul_zero]
    · simp only [hdv, ite_false, ite_self, mul_zero]
  · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
    simp only [hz, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
     
    (hK : ∀ j k d, d ∣ (left j).val * (right k).val → d ∈ K) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ (left j).val * (right k).val then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
      else 0 else 0
  have he : originalTruncatedMiddle W rows left right a b M Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold originalTruncatedMiddle
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact original_truncated_pair_expansion W K rows left right a b M Y Z lengthScale hK i j k
  rw [he]
  apply (finite_middle_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    (fun d => norm_ideal_moebius_le_one d.val) A).trans_eq
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ (left j).val * (right k).val then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d.val i
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold originalProductDivisorMiddleAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ (left j).val * (right k).val then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i <;>
    simp only [hp, and_self, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.original_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  let pairCols : n × p → Ideal O := fun x => (left x.1).val * (right x.2).val
  let K := columnDivisorPool pairCols
  have hPair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (primaryIdealGenerator_ne_zero_ideal _ (left x.1).property.1) (primaryIdealGenerator_ne_zero_ideal _ (right x.2).property.1)
  have hK (j : n) (k : p) (d : Ideal O) (hd : d ∣ (left j).val * (right k).val) : d ∈ K :=
    mem_columnDivisorPool_of_dvd pairCols hPair (j, k) d hd
  let P : Ideal O → m → Prop := fun d i =>
    Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
  have hb := hexp.original_product_divisor_middle deltaLoss hδ ε hε K B N M U hB hN hM hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  have hH (h : O) (hh : h ∈ rowNormDisk ⌊lengthScale⌋₊) : h ≠ 0 := by
    intro hz
    have hn := ((mem_rowNormDisk _ h).mp hh).1
    simp [hz] at hn
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M P h :=
      originalTruncatedMiddle_le_product_divisors W K rows left right a b M Y Z lengthScale
        hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, originalProductDivisorMiddleAt W K rows left right a b M P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => originalProductDivisorMiddleAt_nonneg W K rows left right a b M P h) hb.1
    _ ≤ _ := hb.2

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap

theorem scaled_middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Y Z lengthScale : ℝ) :
    (c : ℂ) * middleTruncation (fun P : primeSupport (G) => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            ((((c * X) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_frequencies G hG]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hp, and_self, ite_true]
    push_cast
    ring
  · simp only [hp, ite_false, mul_zero]

theorem dual_normalized_middle_expansion (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (M F b i j Y Z lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    ((M / (Real.sqrt (i * j) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primeSupport (G) => P.val) Finset.univ W
        (Real.sqrt (F * i * j / (M * b))) Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((Real.sqrt ((M / F) / b) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W
                (Real.sqrt (F * i * j / (M * b)) * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  rw [scaled_middleTruncation_eq_ideal_frequencies G hG,
    dual_principal_prefactor_identity M F b i j hM hF hb hi hj]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primeSupport ((left j).val * (right k).val) => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
          (M * (Ideal.absNorm (rows i).val : ℝ)))) (Y i) (Z i) lengthScale)

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dual_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) 
     
    (hK : ∀ j k d, d ∣ (left j).val * (right k).val → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      (((M / (Real.sqrt ((Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ)) * F) : ℝ) : ℂ) *
        middleTruncation (fun P : primeSupport ((left j).val * (right k).val) => P.val) Finset.univ W
          (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
            (M * (Ideal.absNorm (rows i).val : ℝ)))) (Y i) (Z i) lengthScale) =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ (left j).val * (right k).val then
            originalTerm rows left right a b 1 1 i j k *
              dualPrincipalKernel W rows left right M F h.val d.val i j k
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ (left j).val * (right k).val then
          originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
        else 0 else 0))]
  by_cases hc : (left j).val ⊔ (right k).val = ⊤
  · have hsq : Squarefree ((left j).val * (right k).val) :=
      squarefree_mul_iff.mpr ⟨(Ideal.isCoprime_iff_sup_eq.mpr hc).isRelPrime, (left j).property.2.1, (right k).property.2.1⟩
    have hpos (I : QuadraticIdeal) : 0 < (Ideal.absNorm I.val : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryIdealGenerator_ne_zero_ideal _ I.property.1))
    rw [dual_normalized_middle_expansion _ hsq _ _ _ _ _ _ _ _ _ hM hF
      (hpos (rows i)) (hpos (left j)) (hpos (right k)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← divisorPool_filter K ((left j).val * (right k).val) hsq.ne_zero (hK j k), Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ (left j).val * (right k).val
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, dualPrincipalKernel]
        ring
      · simp only [hdv, hp, ite_true, ite_false, mul_zero]
    · simp only [hdv, ite_false, ite_self, mul_zero]
  · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
    simp only [hz, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) 
     
    (hK : ∀ j k d, d ∣ (left j).val * (right k).val → d ∈ K) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ (left j).val * (right k).val then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h.val d.val i j k
      else 0 else 0
  have he : dualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold dualTruncatedMiddle
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact dual_truncated_pair_expansion W K rows left right a b M F Y Z lengthScale hM hF hK i j k
  rw [he]
  apply (finite_middle_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    (fun d => norm_ideal_moebius_le_one d.val) A).trans_eq
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ (left j).val * (right k).val then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d.val i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold dualProductDivisorMiddleAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ (left j).val * (right k).val then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i <;>
    simp only [hp, and_self, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i).val : ℝ))))) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let pairCols : n × p → Ideal O := fun x => (left x.1).val * (right x.2).val
  let K := columnDivisorPool pairCols
  have hPair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (primaryIdealGenerator_ne_zero_ideal _ (left x.1).property.1) (primaryIdealGenerator_ne_zero_ideal _ (right x.2).property.1)
  have hK (j : n) (k : p) (d : Ideal O) (hd : d ∣ (left j).val * (right k).val) : d ∈ K :=
    mem_columnDivisorPool_of_dvd pairCols hPair (j, k) d hd
  let P : Ideal O → m → Prop := fun d i =>
    Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
  have hb := hexp.dual_product_divisor_middle deltaLoss hδ ε hε K B N M F U hB hN hM hF hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  have hH (h : O) (hh : h ∈ rowNormDisk ⌊lengthScale⌋₊) : h ≠ 0 := by
    intro hz
    have hn := ((mem_rowNormDisk _ h).mp hh).1
    simp [hz] at hn
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F P h :=
      dualTruncatedMiddle_le_product_divisors W K rows left right a b M F Y Z lengthScale hM hF hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, dualProductDivisorMiddleAt W K rows left right a b M F P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => dualProductDivisorMiddleAt_nonneg W K rows left right a b M F P h) hb.1
    _ ≤ _ := hb.2

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedDualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primeSupport ((left j).val * (right k).val) => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualTruncatedMiddle_sector
    (W : 𝓢(ℝ, ℂ)) (rows : m → {I : Ideal O // Squarefree I}) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
      
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (E : idealDivisors (quadraticMaskIdeal 1)) (hE : ∀ i, quadraticBadSector (rows i) = E)
    (hQ : E.val ≠ 0) :
    unrestrictedDualTruncatedMiddle W (fun i => (rows i).val) left right a b M F Y Z lengthScale =
      ((1 / (Ideal.absNorm (E.val) : ℝ) : ℝ) : ℂ) *
        dualTruncatedMiddle W (fun i => quadraticGoodRow (rows i)) left right
          (fun j => a j * canonicalQuadraticRow (left j) (cubicIdealGenerator (E.val)))
          (fun k => b k * canonicalQuadraticRow (right k) (cubicIdealGenerator (E.val)))
          (M * (Ideal.absNorm (E.val) : ℝ)) F Y Z lengthScale := by
  classical
  have hQn : (Ideal.absNorm (E.val) : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm (E.val) ≠ 0 from fun h => hQ (Ideal.absNorm_eq_zero_iff.mp h))
  unfold unrestrictedDualTruncatedMiddle dualTruncatedMiddle
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [unrestrictedPairTerm_sector rows left right a b hray E hE i j k]
  have hn : (Ideal.absNorm (rows i).val : ℝ) =
      (Ideal.absNorm (E.val) : ℝ) * (Ideal.absNorm (quadraticGoodRow (rows i)).val : ℝ) := by
    have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
      (quadraticBadSector_good_product (rows i))
    rw [hE i] at hi
    simpa only [map_mul, Nat.cast_mul] using hi.symm
  rw [hn]
  have harg : F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
      (M * ((Ideal.absNorm (E.val) : ℝ) * (Ideal.absNorm (quadraticGoodRow (rows i)).val : ℝ))) =
    F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
      ((M * (Ideal.absNorm (E.val) : ℝ)) * (Ideal.absNorm (quadraticGoodRow (rows i)).val : ℝ)) := by ring
  rw [harg]
  have hs : (M / (Real.sqrt ((Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ)) * F) : ℝ) =
      (1 / (Ideal.absNorm (E.val) : ℝ)) *
        ((M * (Ideal.absNorm (E.val) : ℝ)) /
          (Real.sqrt ((Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ)) * F)) := by
    field_simp [hQn]
  rw [hs, Complex.ofReal_mul]
  ring

def dualMiddleMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) : ℝ :=
  ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
    ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
      divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)))

lemma dualMiddleMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ))
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  have hc := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold dualMiddleMajorant
  positivity

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.dual_truncated_middle_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → {I : Ideal O // Squarefree I}) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i).val : ℝ)))))
    (E : idealDivisors (quadraticMaskIdeal 1)) (hE : ∀ i, quadraticBadSector (rows i) = E) :
    ‖unrestrictedDualTruncatedMiddle W (fun i => (rows i).val) left right a b M F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedDualTruncatedMiddle, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b W (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm E.val
    let good := fun i => quadraticGoodRow (rows i)
    let a' := fun j => a j * canonicalQuadraticRow (left j) (cubicIdealGenerator E.val)
    let b' := fun k => b k * canonicalQuadraticRow (right k) (cubicIdealGenerator E.val)
    have hQ : 1 ≤ Q := quadraticBadSector_norm_ge_one E
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i).val : ℝ) = Q*(Ideal.absNorm (good i).val : ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
        (quadraticBadSector_good_product (rows i))
      rw [hE i] at hi
      simpa only [map_mul, Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (quadraticGoodRow_injective_on_sector _ _ ((hE i).trans (hE k).symm) h)
    have hg (i : m) : (B/Q)/2 ≤ (Ideal.absNorm (good i).val : ℝ) ∧
        (Ideal.absNorm (good i).val : ℝ) ≤ B/Q := by
      constructor
      · rw [show B/Q/2 = (B/2)/Q by ring]
        apply (div_le_iff₀ hQp).mpr
        have hx := (hrows i).1
        rw [hn i] at hx
        nlinarith only [hx]
      · exact (le_div_iff₀ hQp).mpr (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2)
    have hgoodpos (i : m) : 0 < (Ideal.absNorm (good i).val : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryIdealGenerator_ne_zero_ideal _ (good i).property.1))
    have hBQ : 1 ≤ B/Q := by
      have hh : (1 : ℝ) ≤ Ideal.absNorm (good i₀).val := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
          (primaryIdealGenerator_ne_zero_ideal _ (good i₀).property.1))
      exact hh.trans (hg i₀).2
    have hZa (i : m) : Z i ≤ U * (N * Real.sqrt (F / ((M * Q) * (Ideal.absNorm (good i).val : ℝ)))) := by
      simpa only [hn i, mul_assoc] using hZ i
    have hbnd := hexp.dual_truncated_middle deltaLoss hδ ε hε (B / Q) N (M * Q) F U hBQ hN
      (by positivity) hF hU good left right hgr hl hri hg a' b' W Y Z lengthScale hleft hright hZa
    change ‖dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε (B / Q) N (M * Q) F U a' b' W at hbnd
    have htr := unrestrictedDualTruncatedMiddle_sector W rows left right a b M F Y Z lengthScale
      hray E hE (quadraticBadSector_ne_zero E)
    change unrestrictedDualTruncatedMiddle W (fun i => (rows i).val) left right a b M F Y Z lengthScale =
      ((1 / Q : ℝ) : ℂ) * dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale at htr
    rw [htr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / Q)]
    apply (mul_le_mul_of_nonneg_left hbnd (by positivity)).trans
    have hae (j : n) : ‖a' j‖ ≤ ‖a j‖ := by
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _)
    have hbe (k : p) : ‖b' k‖ ≤ ‖b k‖ := by
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _)
    have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' hae hbe
    have hp : ((B / Q) * N) ^ deltaLoss ≤ (B * N) ^ deltaLoss := by
      apply Real.rpow_le_rpow (by positivity) _ hδ.le
      exact mul_le_mul_of_nonneg_right (div_le_self (by linarith) hQ) (by linarith)
    have hs := dual_bad_sector_scale M F B Q U α hM hF (by linarith) hQ hU hα
    have hc := nonzeroLatticeEnvelopeConstant_nonneg
    have hW := dualMiddleDecayConstant_nonneg W
    have hea := divisorEnergyFactor_nonneg ε hε N a' b'
    have heb := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    unfold dualMiddleMajorant
    calc
      _ = ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a' b' * (divisorExponentConstant hexp deltaLoss hδ * ((B / Q) * N) ^ deltaLoss) *
            ((1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)))) := by ring
      _ ≤ _ := by gcongr


variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.unrestricted_dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → {I : Ideal O // Squarefree I}) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i).val : ℝ))))) :
    ‖unrestrictedDualTruncatedMiddle W (fun i => (rows i).val) left right a b M F Y Z lengthScale‖ ≤
      ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ) * dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  let σ := fun i => quadraticBadSector (rows i)
  have hs : unrestrictedDualTruncatedMiddle W (fun i => (rows i).val) left right a b M F Y Z lengthScale =
      ∑ E : idealDivisors (quadraticMaskIdeal 1),
        unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => (rows i.val).val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale := by
    unfold unrestrictedDualTruncatedMiddle
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : idealDivisors (quadraticMaskIdeal 1)) :
      ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => (rows i.val).val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ ≤
        dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
    apply hexp.dual_truncated_middle_sector hα deltaLoss hδ ε hε B N M F U hB hN hM hF hU
      (fun i : {i // σ i = E} => rows i.val) left right
      (fun i k h => Subtype.ext (hr h)) hl hri (fun i => hrows i.val) a b W
      (fun i => Y i.val) (fun i => Z i.val) lengthScale hleft hright hray (fun i => hZ i.val) E
    exact fun i => i.property
  rw [hs]
  calc
    _ ≤ ∑ E : idealDivisors (quadraticMaskIdeal 1),
        ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => (rows i.val).val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ := norm_sum_le _ _
    _ ≤ ∑ _E : idealDivisors (quadraticMaskIdeal 1), dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap

theorem middleTruncation_coprime_common_mask
    (G C : Ideal O) (hG : Squarefree G) (hC : Squarefree C) (hGC : IsCoprime G C)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primeSupport (G * C) => P.val) Finset.univ W X Y Z lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        middleTruncation (fun P : primeSupport (C) => P.val) Finset.univ W
          (X / (Ideal.absNorm q : ℝ)) (Y / (Ideal.absNorm q : ℝ)) (Z / (Ideal.absNorm q : ℝ)) lengthScale := by
  classical
  have hprod : Squarefree (G * C) := squarefree_mul_iff.mpr ⟨hGC.isRelPrime, hG, hC⟩
  rw [middleTruncation_eq_ideal_frequencies _ hprod]
  simp_rw [middleTruncation_eq_ideal_frequencies C hC]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := idealDivisors G) (t := rowNormDisk ⌊lengthScale⌋₊)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product G C hG.ne_zero hC.ne_zero hGC]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro d hd
  have hqG := (mem_idealDivisors hG.ne_zero).mp hq
  have hdC := (mem_idealDivisors hC.ne_zero).mp hd
  have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
  have hNq : 0 < (Ideal.absNorm q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
  have hqd := (hGC.mono hqG hdC).isRelPrime
  have hlow : Y < (Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ) ↔
      Y / (Ideal.absNorm q : ℝ) < (Ideal.absNorm d : ℝ) := by
    constructor
    · intro hy
      apply (div_lt_iff₀ hNq).mpr
      simpa only [mul_comm] using hy
    · intro hy
      simpa only [mul_comm] using (div_lt_iff₀ hNq).mp hy
  have hhigh : (Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ) ≤ Z ↔
      (Ideal.absNorm d : ℝ) ≤ Z / (Ideal.absNorm q : ℝ) := by
    constructor
    · intro hz
      apply (le_div_iff₀ hNq).mpr
      simpa only [mul_comm] using hz
    · intro hz
      simpa only [mul_comm] using (le_div_iff₀ hNq).mp hz
  simp only [map_mul, Nat.cast_mul, hlow, hhigh, hqd.moebius_mul, Int.cast_mul]
  by_cases hp : Y / (Ideal.absNorm q : ℝ) < (Ideal.absNorm d : ℝ) ∧
      (Ideal.absNorm d : ℝ) ≤ Z / (Ideal.absNorm q : ℝ)
  · simp only [hp, and_self, ite_true]
    have harg : X * ‖ringComplex h‖ ^ 2 / ((Ideal.absNorm q : ℝ) * (Ideal.absNorm d : ℝ)) =
        (X / (Ideal.absNorm q : ℝ)) * ‖ringComplex h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  · simp only [hp, ite_false, mul_zero]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMaskedTruncatedMiddle (G : Ideal O) (W : 𝓢(ℝ, ℂ))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primeSupport (G * ((left j).val * (right k).val)) => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) (Y i) (Z i) lengthScale

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMaskedTruncatedMiddle_eq_divisors
    (G : Ideal O) (hG : Squarefree G) (W : 𝓢(ℝ, ℂ))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (hM : 0 ≤ M) (Y Z : m → ℝ) (lengthScale : ℝ)
     
    (hGl : ∀ j, IsCoprime G (left j).val) (hGr : ∀ k, IsCoprime G (right k).val) :
    originalMaskedTruncatedMiddle G W rows left right a b M Y Z lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
          (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale := by
  classical
  have hp (i : m) (j : n) (k : p) :
      originalTerm rows left right a b 1 1 i j k *
        middleTruncation (fun P : primeSupport (G * ((left j).val * (right k).val)) => P.val) Finset.univ W
          (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) (Y i) (Z i) lengthScale =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q : ℂ) *
        (originalTerm rows left right a b 1 1 i j k *
          middleTruncation (fun P : primeSupport ((left j).val * (right k).val) => P.val) Finset.univ W
            (Real.sqrt ((M / (Ideal.absNorm q : ℝ) ^ 2) / (Ideal.absNorm (rows i).val : ℝ)))
            (Y i / (Ideal.absNorm q : ℝ)) (Z i / (Ideal.absNorm q : ℝ)) lengthScale) := by
    by_cases hc : (left j).val ⊔ (right k).val = ⊤
    · have hsq : Squarefree ((left j).val * (right k).val) :=
        squarefree_mul_iff.mpr ⟨(Ideal.isCoprime_iff_sup_eq.mpr hc).isRelPrime, (left j).property.2.1, (right k).property.2.1⟩
      rw [middleTruncation_coprime_common_mask G _ hG hsq ((hGl j).mul_right (hGr k)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hqG := (mem_idealDivisors hG.ne_zero).mp hq
      have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
      have hNq : 0 < (Ideal.absNorm q : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
      rw [sqrt_norm_divisor_scale M _ _ hM (Nat.cast_nonneg _) hNq]
      ring
    · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
      simp only [hz, zero_mul, mul_zero, Finset.sum_const_zero]
  unfold originalMaskedTruncatedMiddle
  simp_rw [hp]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ : Finset m)) (t := idealDivisors G)]
  simp only [originalTruncatedMiddle, Finset.mul_sum]

theorem HasSieveExponent.original_masked_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (G : Ideal O) (hG : Squarefree G)
    (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hGl : ∀ j, IsCoprime G (left j).val) (hGr : ∀ k, IsCoprime G (right k).val)
    (hZ : ∀ i, Z i ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) :
    ‖originalMaskedTruncatedMiddle G W rows left right a b M Y Z lengthScale‖ ≤
      (idealDivisors G).card * (((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)))) := by
  let V := ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)))
  have hqbound (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ‖originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
        (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale‖ ≤ V := by
    have hqG := (mem_idealDivisors hG.ne_zero).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he, zero_dvd_iff] at hqG; exact hG.ne_zero hqG
    have hq1 : (1 : ℝ) ≤ Ideal.absNorm q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    have hqpos : (0 : ℝ) < Ideal.absNorm q := by linarith
    have hZq (i : m) : Z i / (Ideal.absNorm q : ℝ) ≤
        U * Real.sqrt ((M / (Ideal.absNorm q : ℝ) ^ 2) / (Ideal.absNorm (rows i).val : ℝ)) := by
      calc
        _ ≤ (U * Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) / (Ideal.absNorm q : ℝ) :=
          div_le_div_of_nonneg_right (hZ i) hqpos.le
        _ = U * (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) / (Ideal.absNorm q : ℝ)) := by ring
        _ = _ := by rw [sqrt_norm_divisor_scale M _ _ hM.le (Nat.cast_nonneg _) hqpos]
    have hb := hexp.original_truncated_middle deltaLoss hδ ε hε B N (M / (Ideal.absNorm q : ℝ) ^ 2) U
      hB hN (by positivity) hU rows left right hr hl hri hrows a b W
      (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale hleft hright hZq
    apply hb.trans
    dsimp only [V]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a b
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    gcongr
    exact div_le_self hM.le (one_le_pow₀ hq1)
  rw [originalMaskedTruncatedMiddle_eq_divisors G hG W rows left right a b M hM.le Y Z lengthScale
    hGl hGr]
  calc
    _ ≤ ∑ q ∈ idealDivisors G,
        ‖(UniqueFactorizationMonoid.moebius q : ℂ) *
          originalTruncatedMiddle W rows left right a b (M / (Ideal.absNorm q : ℝ) ^ 2)
            (fun i => Y i / (Ideal.absNorm q : ℝ)) (fun i => Z i / (Ideal.absNorm q : ℝ)) lengthScale‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ idealDivisors G, V := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (norm_ideal_moebius_le_one q)).trans (hqbound q hq)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, V]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedPrincipalDensity
    (rows : m → Ideal O) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (R : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ((Real.sqrt (R/(Ideal.absNorm (rows i):ℝ)):ℝ):ℂ)*primeSupportDensity ((left j).val*(right k).val)

def unrestrictedDualPrincipalTruncation (W : ℝ → ℂ)
    (rows : m → Ideal O) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M/(Real.sqrt ((Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ))*F):ℝ):ℂ) *
      principalTruncation (fun P : primeSupport ((left j).val*(right k).val) => P.val) Finset.univ W
        (Real.sqrt (F*(Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ)))) (Z i))

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualPrincipalTruncation_eq
    (W : ℝ → ℂ) (rows : m → Ideal O) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, rows i ≠ 0)   :
    unrestrictedDualPrincipalTruncation W rows left right a b M F Z =
      paperRadialFourier W 0*unrestrictedPrincipalDensity rows left right a b (M/F) -
      paperRadialFourier W 0*unrestrictedLargePrincipalSum rows left right a b M F Z -
      W 0*unrestrictedSmallPrincipalSum rows left right a b M F (fun d i => (Ideal.absNorm d:ℝ) ≤ Z i) := by
  classical
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have ht (i : m) (j : n) (k : p) :
      unrestrictedPairTerm rows left right a b i j k *
        (((M/(Real.sqrt ((Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ))*F):ℝ):ℂ) *
          principalTruncation (fun P : primeSupport ((left j).val*(right k).val) => P.val) Finset.univ W
            (Real.sqrt (F*(Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ)/
              (M*(Ideal.absNorm (rows i):ℝ)))) (Z i)) =
      paperRadialFourier W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ)):ℝ):ℂ)*primeSupportDensity ((left j).val*(right k).val)) -
      paperRadialFourier W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ∑ d ∈ idealDivisors ((left j).val*(right k).val), if Z i < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) -
      W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ∑ d ∈ idealDivisors ((left j).val*(right k).val), if (Ideal.absNorm d:ℝ) ≤ Z i then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((M/(Real.sqrt ((Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ))*F):ℝ):ℂ) else 0) := by
    by_cases hc : (left j).val ⊔ (right k).val = ⊤
    · have hsq : Squarefree ((left j).val*(right k).val) :=
        squarefree_mul_iff.mpr ⟨(Ideal.isCoprime_iff_sup_eq.mpr hc).isRelPrime,(left j).property.2.1,(right k).property.2.1⟩
      rw [principalTruncation_scaled _ hsq,dual_principal_prefactor_identity M F (Ideal.absNorm (rows i))
        (Ideal.absNorm (left j).val) (Ideal.absNorm (right k).val) hM hF
        (hpos _ (hrows i)) (hpos _ (primaryIdealGenerator_ne_zero_ideal _ (left j).property.1)) (hpos _ (primaryIdealGenerator_ne_zero_ideal _ (right k).property.1))]
      ring
    · have hz : unrestrictedPairTerm rows left right a b i j k = 0 := by
        simp only [unrestrictedPairTerm,hc,ite_false]
      simp only [hz,zero_mul,mul_zero,sub_zero]
  unfold unrestrictedDualPrincipalTruncation
  simp_rw [ht]
  simp only [unrestrictedPrincipalDensity,unrestrictedLargePrincipalSum,unrestrictedSmallPrincipalSum,
    Finset.sum_sub_distrib,Finset.mul_sum]

def retainedDualPrincipalSum (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → QuadraticIdeal) (a : n → ℂ) (M F : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k *
    (((M/(Real.sqrt ((Ideal.absNorm (cols j).val:ℝ)*(Ideal.absNorm (cols k).val:ℝ))*F):ℝ):ℂ) *
      quadraticDualPrincipalIdeal (cols j) (cols k) W
        (Real.sqrt (F*(Ideal.absNorm (cols j).val:ℝ)*(Ideal.absNorm (cols k).val:ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ)))))

omit [DecidableEq m] [DecidableEq n] in
theorem retainedDualPrincipalSum_symmetric_truncation
    (W : 𝓢(ℝ,ℂ)) (rows : m → Ideal O) (cols : n → QuadraticIdeal) (a : n → ℂ)
    (M F N T : ℝ) (hM : 0<M) (hF : 0<F)
    (hrows : ∀ i, rows i ≠ 0)  :
    (Nat.card Oˣ : ℂ)*retainedDualPrincipalSum W rows cols a M F =
      unrestrictedDualPrincipalTruncation W rows cols cols a a M F
        (fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) +
      unrestrictedDualTruncatedMiddle W rows cols cols a a M F
        (fun i => (N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))/T)
        (fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) (T^4) +
      unrestrictedDualPrincipalErrorSum rows cols a W M F N T := by
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  unfold retainedDualPrincipalSum unrestrictedDualPrincipalTruncation
    unrestrictedDualTruncatedMiddle unrestrictedDualPrincipalErrorSum
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hi := hpos _ (hrows i)
  have hj := hpos _ (primaryIdealGenerator_ne_zero_ideal _ (cols j).property.1)
  have hk := hpos _ (primaryIdealGenerator_ne_zero_ideal _ (cols k).property.1)
  have hX : 0 < Real.sqrt
      (F*(Ideal.absNorm (cols j).val:ℝ)*(Ideal.absNorm (cols k).val:ℝ)/(M*(Ideal.absNorm (rows i):ℝ))) :=
    Real.sqrt_pos.mpr (by positivity)
  have htr := quadraticDualPrincipalIdeal_truncated_all_conductors (cols j) (cols k) W
    (Real.sqrt (F*(Ideal.absNorm (cols j).val:ℝ)*(Ideal.absNorm (cols k).val:ℝ)/
      (M*(Ideal.absNorm (rows i):ℝ))))
    ((N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))/T)
    (T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) (T^4) hX
  calc
      _ = unrestrictedPairTerm rows cols cols a a i j k *
          (((M/(Real.sqrt ((Ideal.absNorm (cols j).val:ℝ)*(Ideal.absNorm (cols k).val:ℝ))*F):ℝ):ℂ) *
            ((Nat.card Oˣ : ℂ) * quadraticDualPrincipalIdeal (cols j) (cols k) W
              (Real.sqrt (F*(Ideal.absNorm (cols j).val:ℝ)*(Ideal.absNorm (cols k).val:ℝ)/
                (M*(Ideal.absNorm (rows i):ℝ)))))) := by ring
      _ = _ := by rw [htr]; ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap

lemma norm_four_correction_terms (A B C D : ℂ) :
    ‖-A-B+C+D‖ ≤ ‖A‖+‖B‖+‖C‖+‖D‖ := by
  have hab := norm_sub_le (-A) B
  have habc := norm_add_le (-A-B) C
  have habcd := norm_add_le (-A-B+C) D
  simp only [norm_neg] at hab
  linarith

theorem retained_dual_principal_difference (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        {α : ℝ} (hexp : HasSieveExponent α), 1/2 ≤ α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ),
        1≤B → 1≤N → 0<M → 0<F → 4≤T →
      ∀ (rows : m → {I : Ideal O // Squarefree I}) (cols : n → QuadraticIdeal),
        Function.Injective rows → Function.Injective cols →
        (∀ i, B/2 ≤ (Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ) ≤ B) →
        (∀ j, N/2 ≤ (Ideal.absNorm (cols j).val:ℝ) ∧ (Ideal.absNorm (cols j).val:ℝ) ≤ N) →
        (∀ j k, quadraticColumnRay (cols j)=quadraticColumnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖(Nat.card Oˣ : ℂ)*retainedDualPrincipalSum W (fun i => (rows i).val) cols a M F -
          paperRadialFourier W 0*unrestrictedPrincipalDensity (fun i => (rows i).val) cols cols a a (M/F)‖ ≤
        ‖paperRadialFourier W 0‖*(((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a a) +
        ‖W 0‖*(((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F T a a) +
        ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F T a a W +
        (diagonalControl sieveCutoff)^2*B*N*((2*M/(F*N))*((divisorConstant ε hε*(N*N)^ε)*
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l))*∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,herr⟩ := unrestrictedDualPrincipal_actual_error_sum_bound l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ α hexp hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols hray a W
  let Z := fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i).val:ℝ))))
  let Y := fun i => (N*Real.sqrt (F/(M*(Ideal.absNorm (rows i).val:ℝ))))/T
  have hT0 : 0≤T := by linarith
  have hmain := unrestrictedDualPrincipalTruncation_eq W (fun i => (rows i).val) cols cols a a M F Z hM hF
    (fun i => (rows i).property.ne_zero)
  have hsplit := retainedDualPrincipalSum_symmetric_truncation W (fun i => (rows i).val) cols a M F N T hM hF
    (fun i => (rows i).property.ne_zero)
  change (Nat.card Oˣ : ℂ)*retainedDualPrincipalSum W (fun i => (rows i).val) cols a M F =
    unrestrictedDualPrincipalTruncation W (fun i => (rows i).val) cols cols a a M F Z +
    unrestrictedDualTruncatedMiddle W (fun i => (rows i).val) cols cols a a M F Y Z (T^4) +
    unrestrictedDualPrincipalErrorSum (fun i => (rows i).val) cols a W M F N T at hsplit
  have heq : (Nat.card Oˣ : ℂ)*retainedDualPrincipalSum W (fun i => (rows i).val) cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity (fun i => (rows i).val) cols cols a a (M/F) =
      -(paperRadialFourier W 0*unrestrictedLargePrincipalSum (fun i => (rows i).val) cols cols a a M F Z) -
      (W 0*unrestrictedSmallPrincipalSum (fun i => (rows i).val) cols cols a a M F (fun d i => (Ideal.absNorm d:ℝ)≤Z i)) +
      unrestrictedDualTruncatedMiddle W (fun i => (rows i).val) cols cols a a M F Y Z (T^4) +
      unrestrictedDualPrincipalErrorSum (fun i => (rows i).val) cols a W M F N T := by
    rw [hsplit,hmain]
    ring
  have hl := hexp.unrestricted_large_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
    rows cols cols hr hc hc hrows (fun j => (hcols j).2)
    (fun k => (hcols k).2) hray a a Z (fun _ => le_rfl)
  have hs := hexp.unrestricted_small_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows hcols hcols hray a a (fun d i => (Ideal.absNorm d:ℝ)≤Z i)
    (fun _ _ h => h)
  have hm := hexp.unrestricted_dual_truncated_middle hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows a a W Y Z (T^4) hcols hcols hray (fun _ => le_rfl)
  have he := herr ε hε B N M F T hB hN hM hF hT (fun i => (rows i).val) cols (Subtype.val_injective.comp hr) hc
    (fun i => ⟨(rows i).property.ne_zero,(hrows i).2⟩) hcols a W
  rw [heq]
  apply (norm_four_correction_terms _ _ _ _).trans
  rw [norm_mul,norm_mul]
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hl (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) hm) he

lemma sum_ideal_subtype_dyadic {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (K : ℝ) (f : Ideal O → A) :
    (∑ I : S, f I.val) = ∑ j : Fin (columnDyadicLength K+1),
      ∑ I : divisorDyadicBin S K j, f I.val := by
  classical
  rw [Finset.sum_coe_sort S f,sum_divisorDyadicBins S K f]
  exact Finset.sum_congr rfl (fun j _ => (Finset.sum_coe_sort (divisorDyadicBin S K j) f).symm)

def retainedDualMajorant {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ‖paperRadialFourier W 0‖*(((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a a) +
  ‖W 0‖*(((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F T a a) +
  ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F T a a W +
  (diagonalControl sieveCutoff)^2*B*N*((2*M/(F*N))*((divisorConstant ε hε*(N*N)^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l))*∑ j, ‖a j‖^2

lemma retainedDualMajorant_nonneg {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0≤N) (hM : 0≤M) (hF : 0≤F) (hT : 0≤T) :
    0≤retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a W := by
  have hs0 := smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F (1/2) a a hB hN hM hF (by norm_num)
  have hs1 := smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F T a a hB hN hM hF hT
  have hm := dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F T a a W hB hN hM hF hT
  have hc := (divisorConstant_pos ε hε).le
  unfold retainedDualMajorant
  positivity

lemma retainedDualMajorant_mono {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B' B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB' : 0≤B') (hB : B'≤B) (hN : 0≤N) (hM : 0≤M) (hF : 0≤F) (hT : 0≤T) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B' N M F T a W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a W := by
  have hB0 := hB'.trans hB
  have hα0 : 0≤α-1/2 := by linarith
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (divisorConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  gcongr

lemma retainedDualPrincipalDifference_dyadic {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (S : Finset (Ideal O)) (K : ℝ) (cols : n → QuadraticIdeal) (a : n → ℂ) (M F : ℝ) :
    (Nat.card Oˣ : ℂ)*retainedDualPrincipalSum W (fun I : S => I.val) cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity (fun I : S => I.val) cols cols a a (M/F) =
    ∑ j : Fin (columnDyadicLength K+1),
      ((Nat.card Oˣ : ℂ)*retainedDualPrincipalSum W (fun I : divisorDyadicBin S K j => I.val) cols a M F -
        paperRadialFourier W 0*unrestrictedPrincipalDensity
          (fun I : divisorDyadicBin S K j => I.val) cols cols a a (M/F)) := by
  classical
  have h := sum_ideal_subtype_dyadic (A := ℂ) S K (fun I =>
    (Nat.card Oˣ : ℂ)*retainedDualPrincipalSum W (fun _ : Unit => I) cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity (fun _ : Unit => I) cols cols a a (M/F))
  simpa only [retainedDualPrincipalSum,unrestrictedPrincipalDensity,unrestrictedPairTerm,
    Finset.mul_sum,←Finset.sum_sub_distrib,Fintype.sum_unique] using h

theorem retained_dual_principal_global (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (K N M F T : ℝ),
        1≤K → 1≤N → 0<M → 0<F → 4≤T →
      ∀ (cols : n → QuadraticIdeal), Function.Injective cols →
        (∀ j, N/2≤(Ideal.absNorm (cols j).val:ℝ) ∧ (Ideal.absNorm (cols j).val:ℝ)≤N) →
        (∀ j k, quadraticColumnRay (cols j)=quadraticColumnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖(Nat.card Oˣ : ℂ)*retainedDualPrincipalSum W (fun I : squarefreeIdealBall K => I.val) cols a M F -
          paperRadialFourier W 0*unrestrictedPrincipalDensity
            (fun I : squarefreeIdealBall K => I.val) cols cols a a (M/F)‖ ≤
        (columnDyadicLength K+1:ℕ)*retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M F T a W := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_difference l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε K N M F T hK hN hM hF hT cols hc hcols hray a W
  classical
  let S := squarefreeIdealBall K
  let R := retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M F T a W
  have hS (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K := by
    have hi := mem_squarefreeIdealBall.mp hI
    refine ⟨?_,hi.2⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hi.1.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
  have hR : 0≤R := retainedDualMajorant_nonneg s C hC.le l hexp deltaLoss hδ ε hε (2*K) N M F T a W
    (by linarith) (by linarith) hM.le hF.le (by linarith)
  have hb (j : Fin (columnDyadicLength K+1)) :
      ‖(Nat.card Oˣ : ℂ)*retainedDualPrincipalSum W (fun I : divisorDyadicBin S K j => I.val) cols a M F -
        paperRadialFourier W 0*unrestrictedPrincipalDensity
          (fun I : divisorDyadicBin S K j => I.val) cols cols a a (M/F)‖ ≤ R := by
    by_cases hj : (divisorDyadicBin S K j).Nonempty
    · let B := 2*divisorDyadicScale j.val
      have hB : 1≤B := by dsimp only [B]; linarith [divisorDyadicScale_ge_one j.val]
      have hBK : B≤2*K := by
        dsimp only [B]
        exact mul_le_mul_of_nonneg_left (divisorDyadicBin_scale_le S K hS j hj) (by norm_num)
      have hrows (I : divisorDyadicBin S K j) : Squarefree I.val ∧
          B/2≤(Ideal.absNorm I.val:ℝ) ∧ (Ideal.absNorm I.val:ℝ)≤B := by
        have hi := divisorDyadicBin_bounds S K hS j I.val I.property
        refine ⟨(mem_squarefreeIdealBall.mp (Finset.mem_filter.mp I.property).1).1,?_,hi.2⟩
        dsimp only [B]
        linarith
      have hh := hbound hexp hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
        (fun I : divisorDyadicBin S K j => (⟨I.val,(hrows I).1⟩ : {I : Ideal O // Squarefree I}))
        cols (fun I J h => Subtype.ext (congrArg (fun K : {I : Ideal O // Squarefree I} => K.val) h)) hc (fun I => (hrows I).2) hcols hray a W
      apply hh.trans
      exact retainedDualMajorant_mono s C hC.le l hexp hα deltaLoss hδ ε hε B (2*K) N M F T a W
        (by linarith) hBK (by linarith) hM.le hF.le (by linarith)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hj
      have : IsEmpty (divisorDyadicBin S K j) := by
        refine ⟨fun I => ?_⟩
        have hi := I.property
        simp only [he,Finset.notMem_empty] at hi
      simpa only [retainedDualPrincipalSum,unrestrictedPrincipalDensity,Finset.univ_eq_empty,
        Finset.sum_empty,mul_zero,sub_zero,norm_zero] using hR
  rw [retainedDualPrincipalDifference_dyadic W (squarefreeIdealBall K) K cols a M F]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength K+1), R := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,R]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
