/-
Hybrid rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CubicSieveNorm

/-!
# Hybrid rows

Quotient supports, the inverse cubic kernel and hybrid rows with their inner products; hybrid
grid supports and the reduction of fixed hybrid blocks to the cubic sieve norm.
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
open Eisenstein CompletedGauss CanonicalRowCompletion
open scoped BigOperators Classical
namespace InverseMoment

theorem inverse_eq_square_of_fourth_eq {z : ℂ} (hz : z ^ 4 = z) :
    z⁻¹ = z ^ 2 := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hcube : z ^ 3 = 1 := by
    apply mul_left_cancel₀ hzero
    calc
      z * z ^ 3 = z ^ 4 := by ring
      _ = z := hz
      _ = z * 1 := by ring
  calc
    z⁻¹ = z⁻¹ * z ^ 3 := by rw [hcube, mul_one]
    _ = z ^ 2 := by field_simp

/-- The inverse cubic character in the ideal denominator, evaluated at the primary numerator. -/
def inverseCubicKernel (P n : Ideal O) : ℂ :=
  star (CubicSieve.idealKernel P n)

theorem inverseCubicKernel_eq_inverse_square (P n : Ideal O) :
    inverseCubicKernel P n = (idealRowHom (primaryIdealGenerator n) P)⁻¹ ^ 2 := by
  rw [inv_pow, idealRowHom_square,
    inverse_eq_square_of_fourth_eq (CubicSieve.idealSymbol_fourth P _)]
  exact (CubicSieve.idealKernel_square_eq_star P n).symm

theorem inverseCubicKernel_norm_le_one (P n : Ideal O) :
    ‖inverseCubicKernel P n‖ ≤ 1 := by
  simpa only [inverseCubicKernel, norm_star] using CubicSieve.idealKernel_norm_le_one P n

theorem inverseCubicKernel_mul_left (R P n : Ideal O) :
    inverseCubicKernel (R * P) n = inverseCubicKernel R n * inverseCubicKernel P n := by
  simp only [inverseCubicKernel, CubicSieve.idealKernel, CubicJacobi.idealSymbol_mul,
    map_mul, star_mul]
  ring

theorem inverseCubicKernel_mul_right (P n m : Ideal O)
    (hP : primaryIdealGenerator P ≠ 0) :
    inverseCubicKernel P (n * m) = inverseCubicKernel P n * inverseCubicKernel P m := by
  change star (CubicSieve.idealNumeratorHom P hP (n * m)) =
    star (CubicSieve.idealNumeratorHom P hP n) * star (CubicSieve.idealNumeratorHom P hP m)
  rw [map_mul, star_mul]
  ring

theorem inverseCubicKernel_quotients (R P' r c' m : Ideal O)
    (hP' : primaryIdealGenerator P' ≠ 0) :
    inverseCubicKernel (R * P') ((r * c') * m) =
      inverseCubicKernel R ((r * c') * m) * inverseCubicKernel P' r *
        inverseCubicKernel P' (c' * m) := by
  rw [inverseCubicKernel_mul_left, mul_assoc r c' m,
    inverseCubicKernel_mul_right P' r (c' * m) hP']
  ring

theorem inverseCubicKernel_eq_zero_of_not_coprime (P n : Ideal O)
    (hP : primaryIdealGenerator P ≠ 0) (hn : primaryIdealGenerator n ≠ 0)
    (hcop : ¬ IsCoprime P n) : inverseCubicKernel P n = 0 := by
  have hc := CubicSieve.idealSymbol_cube_mask P (primaryIdealGenerator n) hP
  rw [(primaryIdealGenerator_spec n hn).1, if_neg hcop] at hc
  have hz := (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hc
  simp only [inverseCubicKernel, CubicSieve.idealKernel, hz, star_zero]

theorem inverse_cube_square_eq_sixth {z : ℂ} (h : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    ((z ^ 3)⁻¹) ^ 2 = z ^ 6 := by
  rw [← inv_pow, ← pow_mul]
  norm_num
  rcases h with h | h <;> rw [h] <;> norm_num

theorem inverse_square_cube_mask {M : Type*} [Monoid M]
    (ψ : M →* ℂ) (n b : M) (h : ψ b ^ 6 = 0 ∨ ψ b ^ 6 = 1) :
    (ψ (n * b ^ 3))⁻¹ ^ 2 = (ψ n)⁻¹ ^ 2 * ψ b ^ 6 := by
  rw [map_mul, map_pow, mul_inv_rev, mul_pow, inverse_cube_square_eq_sixth h]
  ring

end InverseMoment
end

noncomputable section
open Eisenstein CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical
namespace InverseMoment

lemma descentAdmissible_of_dvd {I J : Ideal O}
    (hI : CanonicalQuadraticSieve.Admissible I) (hJ : J ∣ I) :
    CanonicalQuadraticSieve.Admissible J :=
  (CanonicalQuadraticSieve.admissible_iff_native J).mpr
    (quadraticIdealAdmissible_of_dvd
      ((CanonicalQuadraticSieve.admissible_iff_native I).mp hI) hJ)

lemma descentQuadratic_conductor_mul (I J : Ideal O)
    (h : CanonicalQuadraticSieve.Admissible (I * J)) (z : O) :
    canonicalQuadraticRowOfIdeal (I * J) z =
      canonicalQuadraticRowOfIdeal I z * canonicalQuadraticRowOfIdeal J z := by
  have hn := (CanonicalQuadraticSieve.admissible_iff_native _).mp h
  simp only [canonicalQuadraticRowOfIdeal, dif_pos hn,
    dif_pos (quadraticIdealAdmissible_of_dvd hn (dvd_mul_right I J)),
    dif_pos (quadraticIdealAdmissible_of_dvd hn (dvd_mul_left J I))]
  exact canonicalQuadraticRow_conductor_mul I J hn z

lemma hybrid_quadratic_square_mask (k n b c m h t : Ideal O)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : primaryIdealGenerator (c * t) ≠ 0) :
    canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (n * b)) =
      (if IsCoprime k (c * t) then 1 else 0) *
        canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (m * h)) := by
  have hk' := (CanonicalQuadraticSieve.admissible_iff_native k).mp hk
  have he : n * b = (m * h) * (c * t) ^ 2 := by rw [hn,hb]; ring
  simp only [canonicalQuadraticRowOfIdeal,dif_pos hk',he,
    canonicalQuadraticRow_squarefree_argument,quadraticIdealMask_indicator,
    (primaryIdealGenerator_spec (c*t) hct).1]
  rw [isCoprime_comm]
  exact mul_comm _ _

lemma descentIdealNorm_pos {I : Ideal O} (hI : I ≠ 0) :
    0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma descentIdealNorm_one_le {I : Ideal O} (hI : I ≠ 0) :
    1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma descentIdealNorm_le_of_dvd {I J : Ideal O} (hI : I ≠ 0) (hJI : J ∣ I) :
    (Ideal.absNorm J : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)) (map_dvd Ideal.absNorm hJI)

end InverseMoment
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
noncomputable section
theorem hybrid_double_mask_mobius
    (k P c : Ideal Eisenstein.O) (hk : k ≠ 0) :
    (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors k, ∑ r ∈ idealDivisors k,
        if R ∣ P ∧ r ∣ c then (moebius R : ℂ) * (moebius r : ℂ) else 0 := by
  have hsplit : (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      (if IsCoprime k P then 1 else 0) * (if IsCoprime k c then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hP : IsCoprime k P <;> by_cases hc : IsCoprime k c <;> simp [hP, hc]
  rw [hsplit, ideal_coprime_mobius k P hk, ideal_coprime_mobius k c hk,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hP : R ∣ P <;> by_cases hc : r ∣ c <;> simp [hP, hc]

theorem hybrid_column_decomposition
    (n b : Ideal Eisenstein.O) (hn : Squarefree n) (hb : b ≠ 0) :
    ∃ c m h t : Ideal Eisenstein.O,
      n = c * m ∧ b = (c * h) * t ^ 2 ∧
      Squarefree c ∧ Squarefree m ∧ Squarefree h ∧
      IsRelPrime c m ∧ IsRelPrime c h ∧ IsCoprime m h ∧ t ≠ 0 := by
  let g := quadraticSquarefreePart b
  let t := quadraticSquarePart b
  let c := gcd n g
  let m := quadraticIdealQuotient c n
  let h := quadraticIdealQuotient c g
  have hg : Squarefree g := quadraticSquarefreePart_squarefree b
  have hcn : c ∣ n := gcd_dvd_left n g
  have hcg : c ∣ g := gcd_dvd_right n g
  have hc : c ≠ 0 := ne_zero_of_dvd_ne_zero hn.ne_zero hcn
  have hnm : n = c * m := (quadraticIdeal_mul_quotient hcn).symm
  have hgh : g = c * h := (quadraticIdeal_mul_quotient hcg).symm
  have hbgt : b = g * t ^ 2 := by
    exact (quadraticParts_mul_square b hb).symm
  obtain ⟨hcm, hcs, hms⟩ := squarefree_mul_iff.mp (hnm ▸ hn)
  obtain ⟨hch, _, hhs⟩ := squarefree_mul_iff.mp (hgh ▸ hg)
  have hmh : IsCoprime m h :=
    (CubicSieve.gcd_eq_iff_quotient_coprime c n g hc hcn hcg).mp rfl
  exact ⟨c, m, h, t, hnm, by rw [hbgt, hgh], hcs, hms, hhs, hcm, hch, hmh,
    quadraticSquarePart_ne_zero b⟩

theorem scaled_product_fiber_card
    (pairs : Finset (Ideal Eisenstein.O × Ideal Eisenstein.O))
    (B J : Ideal Eisenstein.O) (hJ : J ≠ 0) :
    ((pairs.filter (fun p => p.2 * (B * p.1) = J)).card) ≤ (idealDivisors J).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hJ).mpr
    refine ⟨p.2 * B, ?_⟩
    rw [← (Finset.mem_filter.mp hp).2]
    ring
  · intro p hp q hq hpq
    have hep := (Finset.mem_filter.mp hp).2
    have heq := (Finset.mem_filter.mp hq).2
    have hBm : B * p.1 ≠ 0 := by
      intro hz
      apply hJ
      rw [← hep, hz, mul_zero]
    apply Prod.ext hpq
    apply mul_right_cancel₀ hBm
    rw [hep, hpq, heq]

end

end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment

open scoped BigOperators
noncomputable section

theorem bounded_finset_coefficient_sum_sq {C : Type*} (s : Finset C)
    (b f : C → ℂ) (hb : ∀ c ∈ s, ‖b c‖ ≤ 1) :
    ‖∑ c ∈ s, b c * f c‖ ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖f c‖ ^ 2 := by
  classical
  have h := finite_expansion_energy ({()} : Finset Unit) s
    (fun _ => s) (fun _ => b) (fun _ => f) (s.card : ℝ)
    (by simp) (by simpa using hb) (by simp)
  simpa using h

theorem bounded_coefficient_sum_sq {C : Type*} [Fintype C]
    (b f : C → ℂ) (hb : ∀ c, ‖b c‖ ≤ 1) :
    ‖∑ c, b c * f c‖ ^ 2 ≤ (Fintype.card C : ℝ) * ∑ c, ‖f c‖ ^ 2 := by
  classical
  simpa using bounded_finset_coefficient_sum_sq Finset.univ b f (by simpa using hb)

theorem positive_triple_enlarge {M H C : Type*}
    [DecidableEq M] [DecidableEq H] [DecidableEq C]
    (pairs : Finset (M × H)) (cset : M → Finset C)
    (hs : Finset H) (mc : Finset (M × C)) (E : H → M → C → ℝ)
    (hh : ∀ p ∈ pairs, p.2 ∈ hs)
    (hm : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc)
    (hE : ∀ h m c, 0 ≤ E h m c) :
    (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      ∑ h ∈ hs, ∑ u ∈ mc, E h u.1 u.2 := by
  let f : (Σ _p : M × H, C) → H × (M × C) := fun p => (p.1.2, (p.1.1, p.2))
  have hf : Function.Injective f := by
    have hi : Function.LeftInverse
        (fun u : H × (M × C) => (⟨(u.2.1, u.1), u.2.2⟩ : Σ _p : M × H, C)) f := by
      rintro ⟨⟨m, h⟩, c⟩
      rfl
    exact hi.injective
  have hmapped : ((pairs.sigma (fun p => cset p.1)).image f) ⊆ hs ×ˢ mc := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    have hp' := Finset.mem_sigma.mp hp
    exact Finset.mem_product.mpr ⟨hh p.1 hp'.1, hm p.1 hp'.1 p.2 hp'.2⟩
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hmapped
    (fun u _ _ => hE u.1 u.2.1 u.2.2)
  rw [Finset.sum_image (fun _ _ _ _ h => hf h)] at hb
  simpa only [Finset.sum_sigma, Finset.sum_product, f] using hb


end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment

noncomputable section

open scoped BigOperators Classical
open Eisenstein UniqueFactorizationMonoid 

local notation "Eis" => Eisenstein.O

def hybridCubicCoefficient (R r h t : Ideal Eis) (a : Ideal Eis → ℂ)
    (P : Ideal Eis) : ℂ :=
  (a (R * P) * inverseCubicKernel P r * (if IsCoprime P (h * t) then 1 else 0)) /
    (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)

theorem dyadic_normalized_coefficient_energy
    (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a P‖ ≤ 1) :
    (∑ P ∈ S, ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2) ≤ 256 := by
  have hL0 : 0 < L := by linarith
  have hP0 (P : Ideal Eis) (hP : P ∈ S) : 0 < (Ideal.absNorm P : ℝ) :=
    hL0.trans_le (hS P hP).1
  have hcount : (S.card : ℝ) ≤ 128 * (2 * L) := by
    apply EisensteinLatticeCount.finite_ideal_count_real S (2 * L) (by linarith)
    · intro P hP hz
      have hn := hP0 P hP
      simp [hz] at hn
    · intro P hP
      exact (hS P hP).2
  have hterm (P : Ideal Eis) (hP : P ∈ S) :
      ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2 ≤ 1 / L := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    calc
      _ ≤ 1 / (Ideal.absNorm P : ℝ) :=
        div_le_div_of_nonneg_right
          (by simpa using pow_le_pow_left₀ (norm_nonneg _) (ha P hP) 2) (hP0 P hP).le
      _ ≤ _ := one_div_le_one_div_of_le hL0 (hS P hP).1
  calc
    _ ≤ ∑ _P ∈ S, (1 / L : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) / L := by simp [div_eq_mul_inv]
    _ ≤ (128 * (2 * L)) / L := div_le_div_of_nonneg_right hcount hL0.le
    _ = 256 := by field_simp; ring

theorem hybridCubicCoefficient_energy
    (R r h t : Ideal Eis) (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a (R * P)‖ ≤ 1) :
    (∑ P ∈ S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply dyadic_normalized_coefficient_energy S L hL hS
  intro P hP
  by_cases hc : IsCoprime P (h * t)
  · simp only [hc, if_pos, mul_one, norm_mul]
    exact (mul_le_mul (ha P hP) (inverseCubicKernel_norm_le_one P r)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · simp [hc]

theorem hybrid_cubic_column_mask
    (P n b c m h t : Ideal Eis)
    (hP : primaryIdealGenerator P ≠ 0)
    (hngen : primaryIdealGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2) :
    inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) =
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  by_cases hc : IsCoprime P c
  · have he : IsCoprime P b ↔ IsCoprime P (h * t) := by
      rw [hb]
      simp only [IsCoprime.mul_right_iff, IsCoprime.pow_right_iff (by decide : 0 < 2),
        hc, true_and]
    simp only [he]
  · have hPn : ¬ IsCoprime P n := by
      rw [hn, IsCoprime.mul_right_iff]
      exact fun hcop => hc hcop.1
    rw [inverseCubicKernel_eq_zero_of_not_coprime P n hP hngen hPn]
    simp

theorem hybrid_original_kernel_decomposition
    (k P n b c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hP : primaryIdealGenerator P ≠ 0)
    (hngen : primaryIdealGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : primaryIdealGenerator (c * t) ≠ 0) :
    canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (n * b)) *
      inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) *
      (if IsCoprime k P then 1 else 0) =
    (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) *
      canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (m * h)) *
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  have hm : ((if IsCoprime k P then (1 : ℂ) else 0) *
      (if IsCoprime k (c * t) then 1 else 0)) =
      (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hkp : IsCoprime k P <;> by_cases hkc : IsCoprime k c <;>
      by_cases hkt : IsCoprime k t <;> simp [hkp, hkc, hkt]
  calc
    _ = ((if IsCoprime k P then 1 else 0) * (if IsCoprime k (c * t) then 1 else 0)) *
        canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (m * h)) *
        (inverseCubicKernel P n * (if IsCoprime P b then 1 else 0)) := by
      rw [hybrid_quadratic_square_mask k n b c m h t hk hn hb hct]
      ring
    _ = _ := by rw [hm, hybrid_cubic_column_mask P n b c m h t hP hngen hn hb]; ring

theorem hybrid_kernel_quotients (R r k' P' c' m h : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : primaryIdealGenerator P' ≠ 0) :
    canonicalQuadraticRowOfIdeal ((R * r) * k')
        (primaryIdealGenerator (m * h)) *
      inverseCubicKernel (R * P') ((r * c') * m) =
    (canonicalQuadraticRowOfIdeal (R * r)
        (primaryIdealGenerator (m * h)) *
      inverseCubicKernel R ((r * c') * m)) *
      inverseCubicKernel P' r *
      canonicalQuadraticRowOfIdeal k'
        (primaryIdealGenerator (m * h)) *
      inverseCubicKernel P' (c' * m) := by
  rw [descentQuadratic_conductor_mul (R * r) k' hk,
    inverseCubicKernel_quotients R P' r c' m hP']
  ring

def hybridColumnCoefficient (R r : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (c m h : Ideal Eis) : ℂ :=
  beta (r * c) m h *
    canonicalQuadraticRowOfIdeal (R * r) (primaryIdealGenerator (m * h)) *
    inverseCubicKernel R ((r * c) * m)

theorem hybridColumnCoefficient_norm_le_one (R r c m h : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (hb : ‖beta (r * c) m h‖ ≤ 1) :
    ‖hybridColumnCoefficient R r beta c m h‖ ≤ 1 := by
  simp only [hybridColumnCoefficient, norm_mul]
  have hfirst : ‖beta (r * c) m h‖ *
      ‖canonicalQuadraticRowOfIdeal (R * r)
        (primaryIdealGenerator (m * h))‖ ≤ 1 := by
    exact (mul_le_mul hb (canonicalQuadraticRowOfIdeal_norm_le_one _ _)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (mul_le_mul hfirst (inverseCubicKernel_norm_le_one R ((r * c) * m))
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem normalized_ideal_product_weight (R P : Ideal Eis) (z : ℂ) :
    z / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        (z / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)) := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hybrid_extracted_block_identity
    (R r k' P' c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : primaryIdealGenerator P' ≠ 0)
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    a (R * P') / (Real.sqrt (Ideal.absNorm (R * P') : ℝ) : ℂ) *
      beta (r * c) m h *
      (canonicalQuadraticRowOfIdeal ((R * r) * k')
          (primaryIdealGenerator (m * h)) *
        inverseCubicKernel (R * P') ((r * c) * m)) *
      (if IsCoprime P' (h * t) then 1 else 0) =
    (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
      hybridColumnCoefficient R r beta c m h *
      canonicalQuadraticRowOfIdeal k' (primaryIdealGenerator (m * h)) *
      hybridCubicCoefficient R r h t a P' * inverseCubicKernel P' (c * m) := by
  rw [normalized_ideal_product_weight, hybrid_kernel_quotients R r k' P' c m h hk hP']
  simp only [hybridColumnCoefficient, hybridCubicCoefficient, div_eq_mul_inv]
  ring

def hybridInner (nset bset : Finset (Ideal Eis))
    (beta : Ideal Eis → Ideal Eis → ℂ) (k P : Ideal Eis) : ℂ :=
  ∑ n ∈ nset, ∑ b ∈ bset,
    beta n b * canonicalQuadraticRowOfIdeal k
      (primaryIdealGenerator (n * b)) * inverseCubicKernel P n *
        (if IsCoprime P b then 1 else 0)

def hybridRow (Pset nset bset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) : ℂ :=
  ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    (if IsCoprime k P then 1 else 0) * hybridInner nset bset beta k P

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
noncomputable section
local notation "Eis" => Eisenstein.O

structure HybridColumnData where
  common : Ideal Eis
  residualN : Ideal Eis
  residualB : Ideal Eis
  square : Ideal Eis
  n_squarefree : Squarefree (common * residualN)
  g_squarefree : Squarefree (common * residualB)
  residual_coprime : IsCoprime residualN residualB
  square_ne_zero : square ≠ 0

def HybridColumnData.reconstruct (d : HybridColumnData) : Ideal Eis × Ideal Eis :=
  (d.common * d.residualN, (d.common * d.residualB) * d.square ^ 2)

theorem HybridColumnData.common_ne_zero (d : HybridColumnData) : d.common ≠ 0 :=
  ne_zero_of_dvd_ne_zero d.n_squarefree.ne_zero (dvd_mul_right _ _)

theorem HybridColumnData.common_eq_gcd (d : HybridColumnData) :
    d.common = gcd (d.common * d.residualN) (d.common * d.residualB) := by
  rw [gcd_mul_left, normalize_eq, Ideal.isCoprime_iff_gcd.mp d.residual_coprime, mul_one]

theorem HybridColumnData.residual_product_squarefree (d : HybridColumnData) :
    Squarefree (d.residualN * d.residualB) := by
  have hm := (squarefree_mul_iff.mp d.n_squarefree).2.2
  have hh := (squarefree_mul_iff.mp d.g_squarefree).2.2
  exact squarefree_mul_iff.mpr ⟨d.residual_coprime.isRelPrime, hm, hh⟩

theorem HybridColumnData.primary_factors (d : HybridColumnData)
    (hn : primaryIdealGenerator (d.common * d.residualN) ≠ 0)
    (hb : primaryIdealGenerator ((d.common * d.residualB) * d.square ^ 2) ≠ 0) :
    primaryIdealGenerator d.common ≠ 0 ∧
    primaryIdealGenerator d.residualN ≠ 0 ∧
    primaryIdealGenerator d.residualB ≠ 0 ∧
    primaryIdealGenerator d.square ≠ 0 ∧
    primaryIdealGenerator (d.common * d.square) ≠ 0 := by
  rw [primaryIdealGenerator_mul] at hn
  have hpow : primaryIdealGenerator (d.square ^ 2) =
      primaryIdealGenerator d.square ^ 2 :=
    primaryIdealGenerator_pow d.square 2
  rw [primaryIdealGenerator_mul, primaryIdealGenerator_mul, hpow] at hb
  have hc := (mul_ne_zero_iff.mp hn).1
  have hm := (mul_ne_zero_iff.mp hn).2
  have hch := (mul_ne_zero_iff.mp hb).1
  have hh := (mul_ne_zero_iff.mp hch).2
  have ht : primaryIdealGenerator d.square ≠ 0 := by
    intro hz
    apply (mul_ne_zero_iff.mp hb).2
    simp [hz]
  refine ⟨hc, hm, hh, ht, ?_⟩
  rw [primaryIdealGenerator_mul]
  exact mul_ne_zero hc ht

theorem HybridColumnData.residual_norm_identity (d : HybridColumnData) :
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) =
      ((Ideal.absNorm (d.common * d.residualN) : ℝ) *
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ)) /
      ((Ideal.absNorm d.common : ℝ) ^ 2 * (Ideal.absNorm d.square : ℝ) ^ 2) := by
  have hc : (Ideal.absNorm d.common : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => d.common_ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  have ht : (Ideal.absNorm d.square : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => d.square_ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  field_simp

theorem HybridColumnData.residual_norm_bounds (d : HybridColumnData)
    (N B C T : ℝ) (hN : 0 ≤ N) (_hB : 0 ≤ B) (hC : 0 < C) (hT : 0 < T)
    (hn : (Ideal.absNorm (d.common * d.residualN) : ℝ) ≤ N)
    (hb : (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B)
    (hc : C ≤ (Ideal.absNorm d.common : ℝ))
    (ht : T ≤ (Ideal.absNorm d.square : ℝ)) :
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  have hn' := hn
  have hb' := hb
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hn' hb'
  have hm : (Ideal.absNorm d.residualN : ℝ) ≤ N / C := by
    apply (le_div_iff₀ hC).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualN : ℝ) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc
          (Nat.cast_nonneg (Ideal.absNorm d.residualN))
      _ ≤ N := hn'
  have hh : (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) := by
    apply (le_div_iff₀ (mul_pos hC (sq_pos_of_pos hT))).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualB : ℝ) *
          (Ideal.absNorm d.square : ℝ) ^ 2 := by
        calc
          _ = C * (Ideal.absNorm d.residualB : ℝ) * T ^ 2 := by ring
          _ ≤ _ := by gcongr
      _ ≤ B := hb'
  refine ⟨hm, hh, ?_⟩
  calc
    _ = (Ideal.absNorm d.residualN : ℝ) * (Ideal.absNorm d.residualB : ℝ) := by
      rw [map_mul, Nat.cast_mul]
    _ ≤ (N / C) * (B / (C * T ^ 2)) :=
      mul_le_mul hm hh (Nat.cast_nonneg _) (div_nonneg hN hC.le)
    _ = N * B / (C ^ 2 * T ^ 2) := by ring

theorem HybridColumnData.reconstruct_injective :
    Function.Injective HybridColumnData.reconstruct := by
  intro d e he
  have hn : d.common * d.residualN = e.common * e.residualN := congrArg Prod.fst he
  have hb : d.square ^ 2 * (d.common * d.residualB) =
      e.square ^ 2 * (e.common * e.residualB) := by
    simpa only [HybridColumnData.reconstruct, mul_comm] using congrArg Prod.snd he
  have hb' : (d.common * d.residualB) * d.square^2 = (e.common * e.residualB) * e.square^2 := by
    simpa only [mul_comm] using hb
  obtain ⟨hg, ht⟩ := squarefree_square_decomposition_unique
    d.square_ne_zero e.square_ne_zero d.g_squarefree e.g_squarefree hb' 
  have hc : d.common = e.common := by
    calc
      _ = gcd (d.common * d.residualN) (d.common * d.residualB) := d.common_eq_gcd
      _ = gcd (e.common * e.residualN) (e.common * e.residualB) := by rw [hn, hg]
      _ = e.common := e.common_eq_gcd.symm
  rw [hc] at hn hg
  have hm := mul_left_cancel₀ e.common_ne_zero hn
  have hh := mul_left_cancel₀ e.common_ne_zero hg
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl

def HybridColumnData.toOriginal (d : HybridColumnData) :
    {p : Ideal Eis × Ideal Eis // Squarefree p.1 ∧ p.2 ≠ 0} :=
  ⟨d.reconstruct, d.n_squarefree,
    mul_ne_zero d.g_squarefree.ne_zero (pow_ne_zero 2 d.square_ne_zero)⟩

theorem HybridColumnData.toOriginal_bijective : Function.Bijective HybridColumnData.toOriginal := by
  constructor
  · intro d e he
    exact reconstruct_injective (congrArg Subtype.val he)
  · intro p
    obtain ⟨c, m, h, t, hn, hb, hcs, hms, hhs, hcm, hch, hmh, ht⟩ :=
      hybrid_column_decomposition p.val.1 p.val.2 p.property.1 p.property.2
    refine ⟨⟨c, m, h, t, ?_, ?_, hmh, ht⟩, ?_⟩
    · exact hn ▸ p.property.1
    · exact squarefree_mul_iff.mpr ⟨hch, hcs, hhs⟩
    · apply Subtype.ext
      exact Prod.ext hn.symm hb.symm

def hybridColumnEquiv : HybridColumnData ≃
    {p : Ideal Eis × Ideal Eis // Squarefree p.1 ∧ p.2 ≠ 0} :=
  Equiv.ofBijective HybridColumnData.toOriginal HybridColumnData.toOriginal_bijective

theorem hybrid_column_reindex (f : Ideal Eis → Ideal Eis → ℂ) :
    (∑' p : {p : Ideal Eis × Ideal Eis // Squarefree p.1 ∧ p.2 ≠ 0}, f p.val.1 p.val.2) =
      ∑' d : HybridColumnData,
        f (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) := by
  exact (hybridColumnEquiv.tsum_eq (fun p => f p.val.1 p.val.2)).symm

def hybridColumnSupport (S : Finset (Ideal Eis × Ideal Eis)) : Finset HybridColumnData :=
  S.preimage HybridColumnData.reconstruct HybridColumnData.reconstruct_injective.injOn

@[simp] theorem mem_hybridColumnSupport (S : Finset (Ideal Eis × Ideal Eis))
    (d : HybridColumnData) :
    d ∈ hybridColumnSupport S ↔ d.reconstruct ∈ S := Finset.mem_preimage

theorem hybrid_finite_column_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal Eis × Ideal Eis))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ 0)
    (f : Ideal Eis × Ideal Eis → A) :
    (∑ p ∈ S, f p) = ∑ d ∈ hybridColumnSupport S, f d.reconstruct := by
  symm
  apply Finset.sum_preimage
  intro p hp hn
  obtain ⟨d, hd⟩ := HybridColumnData.toOriginal_bijective.surjective ⟨p, hS p hp⟩
  exact (hn ⟨d, congrArg Subtype.val hd⟩).elim

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

def supportedHybridRow (S : Finset (Ideal Eis × Ideal Eis)) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) : ℂ :=
  ∑ p ∈ S, ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta p.1 p.2 *
    (canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (p.1 * p.2)) * inverseCubicKernel P p.1 *
      (if IsCoprime P p.2 then 1 else 0) * (if IsCoprime k P then 1 else 0))

theorem supportedHybridRow_product (nset bset Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    supportedHybridRow (nset ×ˢ bset) Pset a beta k = hybridRow Pset nset bset a beta k := by
  simp only [supportedHybridRow, hybridRow, hybridInner, Finset.sum_product,
    Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext n
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

def reconstructedHybridTerm (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) (P : Ideal Eis)
    (d : HybridColumnData) : ℂ :=
  a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) *
    ((if IsCoprime k d.square then 1 else 0) *
      (if IsCoprime k (P * d.common) then 1 else 0) *
      canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (d.residualN * d.residualB)) *
      inverseCubicKernel P (d.common * d.residualN) *
      (if IsCoprime P (d.residualB * d.square) then 1 else 0))

theorem supportedHybridRow_reconstruct
    (S : Finset (Ideal Eis × Ideal Eis)) (Pset : Finset (Ideal Eis))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ 0 ∧
      primaryIdealGenerator p.1 ≠ 0 ∧ primaryIdealGenerator p.2 ≠ 0)
    (hP : ∀ P ∈ Pset, primaryIdealGenerator P ≠ 0)
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ)
    (k : Ideal Eis) (hk : Admissible k) :
    supportedHybridRow S Pset a beta k =
      ∑ d ∈ hybridColumnSupport S, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d := by
  unfold supportedHybridRow
  rw [hybrid_finite_column_reindex S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdS := (mem_hybridColumnSupport S d).mp hd
  have hdprim := hS d.reconstruct hdS
  have hct := (d.primary_factors hdprim.2.2.1 hdprim.2.2.2).2.2.2.2
  apply Finset.sum_congr rfl
  intro P hPP
  unfold reconstructedHybridTerm
  exact congrArg
    (fun z : ℂ => a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
      beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) * z)
    (hybrid_original_kernel_decomposition k P
    (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2)
    d.common d.residualN d.residualB d.square hk (hP P hPP) hdprim.2.2.1 rfl rfl hct)

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

def hybridSquarePool (S : Finset (Ideal Eis × Ideal Eis)) : Finset (Ideal Eis) :=
  (hybridColumnSupport S).image HybridColumnData.square

def hybridCommonBlock (S : Finset (Ideal Eis × Ideal Eis)) (N : ℝ)
    (i : Fin (columnDyadicLength N + 1)) (t : Ideal Eis) : Finset HybridColumnData :=
  (hybridColumnSupport S).filter fun d =>
    d.square = t ∧ divisorDyadicLabel N d.common = i

theorem hybrid_dyadic_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal Eis × Ideal Eis)) (N B : ℝ) (f : HybridColumnData → A) :
    (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ j : Fin (columnDyadicLength B + 1),
        ∑ i : Fin (columnDyadicLength N + 1),
          ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
            ∑ d ∈ hybridCommonBlock S N i t, f d := by
  have ht : (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ t ∈ hybridSquarePool S, ∑ d ∈ hybridColumnSupport S with d.square = t, f d := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun d hd => Finset.mem_image.mpr ⟨d, hd, rfl⟩) f
  rw [ht, sum_divisorDyadicBins (hybridSquarePool S) B]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hi := Finset.sum_fiberwise
    ((hybridColumnSupport S).filter fun d => d.square = t)
    (fun d => divisorDyadicLabel N d.common) f
  simpa only [Finset.filter_filter, hybridCommonBlock] using hi.symm

theorem hybridSquarePool_bounds (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (t : Ideal Eis) (ht : t ∈ hybridSquarePool S) :
    1 ≤ (Ideal.absNorm t : ℝ) ∧ (Ideal.absNorm t : ℝ) ≤ B := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
  have hb0 : (d.common * d.residualB) * d.square ^ 2 ≠ 0 :=
    mul_ne_zero d.g_squarefree.ne_zero (pow_ne_zero _ d.square_ne_zero)
  refine ⟨descentIdealNorm_one_le d.square_ne_zero, ?_⟩
  apply (descentIdealNorm_le_of_dvd hb0 ?_).trans
    (hS d.reconstruct ((mem_hybridColumnSupport S d).mp hd))
  exact dvd_mul_of_dvd_right (dvd_pow_self d.square (by norm_num : 2 ≠ 0)) _

theorem hybridSquarePool_bin_count (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) :
    ((divisorDyadicBin (hybridSquarePool S) B j).card : ℝ) ≤
      256 * divisorDyadicScale j.val := by
  have hscale := divisorDyadicScale_ge_one j.val
  have hb := divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B hS) j
  have hc := EisensteinLatticeCount.finite_ideal_count_real
    (divisorDyadicBin (hybridSquarePool S) B j) (2 * divisorDyadicScale j.val)
    (by linarith) (fun t ht hz => by
      have hp := (hb t ht).1
      simp [hz] at hp
      linarith) (fun t ht => (hb t ht).2)
  linarith

theorem hybridCommonBlock_bounds
    (S : Finset (Ideal Eis × Ideal Eis)) (N B : ℝ) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B)
    (i : Fin (columnDyadicLength N + 1)) (j : Fin (columnDyadicLength B + 1))
    (t : Ideal Eis) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j)
    (d : HybridColumnData) (hd : d ∈ hybridCommonBlock S N i t) :
    let C := divisorDyadicScale i.val
    let T := divisorDyadicScale j.val
    C ≤ (Ideal.absNorm d.common : ℝ) ∧ (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
  have hs := hS d.reconstruct ((mem_hybridColumnSupport S d).mp hdS)
  have hc1 := descentIdealNorm_one_le d.common_ne_zero
  have hcn : (Ideal.absNorm d.common : ℝ) ≤ N :=
    (descentIdealNorm_le_of_dvd d.n_squarefree.ne_zero (dvd_mul_right _ _)).trans hs.1
  have hcb := divisorDyadicLabel_bounds N d.common hc1 hcn
  rw [hdi] at hcb
  have hcLow : divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) :=
    max_le hc1 hcb.1.le
  have hcHigh : (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val := by
    have hh : (2 : ℝ) ^ i.val / 2 ≤ divisorDyadicScale i.val := le_max_right _ _
    linarith [hcb.2]
  have htLow := (divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B (fun p hp => (hS p hp).2)) j t ht).1
  rw [← hdt] at htLow
  refine ⟨hcLow, hcHigh, ?_⟩
  exact d.residual_norm_bounds N B (divisorDyadicScale i.val) (divisorDyadicScale j.val)
    hN hB (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val]) hs.1 hs.2 hcLow htLow

theorem hybrid_square_dyad_energy
    (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) (rows : Finset (Ideal Eis))
    (F : Ideal Eis → Ideal Eis → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      (∑ k ∈ rows, ‖F t k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j, F t k‖ ^ 2) ≤
      (256 * divisorDyadicScale j.val) ^ 2 * E := by
  let Tset := divisorDyadicBin (hybridSquarePool S) B j
  have hc := hybridSquarePool_bin_count S B hS j
  calc
    _ ≤ (Tset.card : ℝ) * ∑ t ∈ Tset, ∑ k ∈ rows, ‖F t k‖ ^ 2 := by
      calc
        _ ≤ ∑ k ∈ rows, (Tset.card : ℝ) * ∑ t ∈ Tset, ‖F t k‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          simpa using bounded_finset_coefficient_sum_sq Tset (fun _ => 1) (fun t => F t k)
            (by simp)
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Tset.card : ℝ) * ∑ _t ∈ Tset, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (Nat.cast_nonneg _)
    _ = (Tset.card : ℝ) ^ 2 * E := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) hE

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

section FiniteGrid
variable {M H C A : Type*} [DecidableEq M] [DecidableEq H] [DecidableEq C] [AddCommMonoid A]

def gridCommonSupport (T : Finset ((M × H) × C)) (m : M) : Finset C :=
  (T.filter fun u => u.1.1 = m).image Prod.snd

theorem finite_triple_support_reindex (T : Finset ((M × H) × C))
    (f : (M × H) × C → A) :
    (∑ u ∈ T, f u) = ∑ p ∈ T.image Prod.fst,
      ∑ c ∈ gridCommonSupport T p.1, if (p, c) ∈ T then f (p, c) else 0 := by
  have hp := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image Prod.fst) (g := Prod.fst)
    (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) f
  rw [← hp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => u.2)
  · intro u hu
    obtain ⟨huT, hup⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huT, congrArg Prod.fst hup⟩, rfl⟩
    · simpa only [← hup, Prod.eta] using huT
  · intro u hu v hv he
    apply Prod.ext
    · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    · exact he
  · intro c hc
    have hpc := (Finset.mem_filter.mp hc).2
    exact ⟨(p, c), Finset.mem_filter.mpr ⟨hpc, rfl⟩, rfl⟩
  · intro u hu
    have hup := (Finset.mem_filter.mp hu).2
    simp only [← hup, Prod.eta]

end FiniteGrid

def HybridColumnData.gridIndex (d : HybridColumnData) :
    (Ideal Eis × Ideal Eis) × Ideal Eis := ((d.residualN, d.residualB), d.common)

theorem HybridColumnData.gridIndex_injective_on_square (t : Ideal Eis) :
    Set.InjOn HybridColumnData.gridIndex {d | d.square = t} := by
  intro d hd e he hg
  have hm : d.residualN = e.residualN := congrArg (fun u => u.1.1) hg
  have hh : d.residualB = e.residualB := congrArg (fun u => u.1.2) hg
  have hc : d.common = e.common := congrArg Prod.snd hg
  have ht : d.square = e.square := hd.trans he.symm
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl

def hybridGridSupport (D : Finset HybridColumnData) :
    Finset ((Ideal Eis × Ideal Eis) × Ideal Eis) := D.image HybridColumnData.gridIndex

theorem hybrid_grid_reindex (D : Finset HybridColumnData) (t : Ideal Eis)
    (hD : ∀ d ∈ D, d.square = t) (f : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ p ∈ (hybridGridSupport D).image Prod.fst,
        ∑ c ∈ gridCommonSupport (hybridGridSupport D) p.1,
          if (p, c) ∈ hybridGridSupport D then f c p.1 p.2 else 0 := by
  have he : (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ u ∈ hybridGridSupport D, f u.2 u.1.1 u.1.2 := by
    symm
    apply Finset.sum_image
    intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg
  rw [he]
  exact finite_triple_support_reindex (hybridGridSupport D) _

theorem gridCommonSupport_origin (D : Finset HybridColumnData) (m c : Ideal Eis)
    (hc : c ∈ gridCommonSupport (hybridGridSupport D) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = c := by
  obtain ⟨u, hu, huc⟩ := Finset.mem_image.mp hc
  obtain ⟨huT, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp huT
  exact ⟨d, hd, hum, huc⟩

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

def quotientSupport (D : Ideal Eis) (S : Finset (Ideal Eis)) : Finset (Ideal Eis) :=
  (S.filter (fun I => D ∣ I)).image (quadraticIdealQuotient D)

@[simp] theorem mem_quotientSupport (D J : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) :
    J ∈ quotientSupport D S ↔ D * J ∈ S := by
  constructor
  · intro hJ
    obtain ⟨I, hI, he⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIS, hDI⟩ := Finset.mem_filter.mp hI
    rw [← he, quadraticIdeal_mul_quotient hDI]
    exact hIS
  · intro hJ
    refine Finset.mem_image.mpr ⟨D * J, Finset.mem_filter.mpr ⟨hJ, dvd_mul_right _ _⟩, ?_⟩
    exact mul_left_cancel₀ hD (quadraticIdeal_mul_quotient (dvd_mul_right D J))

theorem sum_quotientSupport {A : Type*} [AddCommMonoid A]
    (D : Ideal Eis) (S : Finset (Ideal Eis)) (f : Ideal Eis → A) :
    (∑ I ∈ S with D ∣ I, f I) = ∑ J ∈ quotientSupport D S, f (D * J) := by
  rw [quotientSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [quadraticIdeal_mul_quotient (Finset.mem_filter.mp hI).2]
  · intro I hI J hJ he
    exact quadraticIdealQuotient_injective D (Finset.mem_filter.mp hI).2
      (Finset.mem_filter.mp hJ).2 he

theorem quotientSupport_nonzero (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, I ≠ 0)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) : J ≠ 0 := by
  have h := hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)
  exact (mul_ne_zero_iff.mp h).2

theorem quotientSupport_quadratic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CanonicalQuadraticSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CanonicalQuadraticSieve.Admissible J :=
  descentAdmissible_of_dvd (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ))
    (dvd_mul_left _ _)

theorem quotientSupport_cubic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CubicSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CubicSieve.Admissible J :=
  CubicSieve.cubic_admissible_of_dvd
    (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)) (dvd_mul_left _ _)

theorem quotientSupport_norm_le (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (N : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0) (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ N)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J : ℝ) ≤ N := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hn : Ideal.absNorm J ≤ Ideal.absNorm (D * J) := by
    apply Nat.le_of_dvd
    · exact Nat.pos_of_ne_zero (fun hz => hS0 _ hDJ (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact map_dvd Ideal.absNorm (dvd_mul_left J D)
  exact (Nat.cast_le.mpr hn).trans (hS _ hDJ)

theorem quotientSupport_shell (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    max 1 (L / (Ideal.absNorm D : ℝ)) ≤ (Ideal.absNorm J : ℝ) ∧
      (Ideal.absNorm J : ℝ) ≤ 2 * max 1 (L / (Ideal.absNorm D : ℝ)) := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hnD : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hJ0 := quotientSupport_nonzero D hD S hS0 J hJ
  have hnJ : 1 ≤ (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hJ0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs := hS (D * J) hDJ
  simp only [map_mul, Nat.cast_mul] at hs
  constructor
  · refine max_le hnJ ((div_le_iff₀ hnD).mpr ?_)
    simpa only [mul_comm] using hs.1
  · have hj : (Ideal.absNorm J : ℝ) ≤ 2 * (L / (Ideal.absNorm D : ℝ)) := by
      have hj := (le_div_iff₀ hnD).mpr (show
          (Ideal.absNorm J : ℝ) * (Ideal.absNorm D : ℝ) ≤ 2 * L by
        simpa only [mul_comm] using hs.2)
      simpa only [mul_div_assoc] using hj
    exact hj.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

theorem quotient_hybridCubicCoefficient_energy
    (R r h t : Ideal Eis) (hR : R ≠ 0) (S : Finset (Ideal Eis)) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ I ∈ S, ‖a I‖ ≤ 1) :
    (∑ P ∈ quotientSupport R S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply hybridCubicCoefficient_energy R r h t (quotientSupport R S)
    (max 1 (L / (Ideal.absNorm R : ℝ))) (le_max_left _ _)
  · exact quotientSupport_shell R hR S L hS0 hS
  · intro P hP
    exact ha (R * P) ((mem_quotientSupport R P hR S).mp hP)

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss 
noncomputable section
local notation "Eis" => Eisenstein.O

theorem inverseCubicKernel_divisor_overlap_zero (R r P c m : Ideal Eis)
    (hP : primaryIdealGenerator P ≠ 0) (hcm : primaryIdealGenerator (c * m) ≠ 0)
    (hRP : R ∣ P) (hrc : r ∣ c) (hRr : ¬ IsCoprime R r) :
    inverseCubicKernel P (c * m) = 0 := by
  apply inverseCubicKernel_eq_zero_of_not_coprime P (c * m) hP hcm
  intro hcop
  have hPc := hcop.of_isCoprime_of_dvd_right (dvd_mul_right c m)
  exact hRr ((hPc.of_isCoprime_of_dvd_left hRP).of_isCoprime_of_dvd_right hrc)

theorem double_divisor_row_reindex {A : Type*} [AddCommMonoid A]
    (rows : Finset (Ideal Eis)) (hrows : ∀ k ∈ rows, k ≠ 0)
    (R r : Ideal Eis) (hRr : IsCoprime R r) (F : Ideal Eis → A) :
    (∑ k ∈ rows, if (R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k) then F k else 0) =
      ∑ k ∈ quotientSupport (R * r) rows, F ((R * r) * k) := by
  have hsel (k : Ideal Eis) (hk : k ∈ rows) :
      ((R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k)) ↔ R * r ∣ k := by
    rw [Finset.mem_product, mem_idealDivisors (hrows k hk), mem_idealDivisors (hrows k hk)]
    exact ⟨fun h => hRr.mul_dvd h.1 h.2,
      fun h => ⟨dvd_trans (dvd_mul_right R r) h, dvd_trans (dvd_mul_left r R) h⟩⟩
  calc
    _ = ∑ k ∈ rows, if R * r ∣ k then F k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hsel k hk]
    _ = ∑ k ∈ rows with R * r ∣ k, F k := (Finset.sum_filter _ _).symm
    _ = _ := sum_quotientSupport (R * r) rows F

theorem double_column_divisor_reindex {A : Type*} [AddCommMonoid A]
    (Pset cset : Finset (Ideal Eis)) (R r : Ideal Eis)
    (F : Ideal Eis → Ideal Eis → A) :
    (∑ P ∈ Pset, ∑ c ∈ cset, if R ∣ P ∧ r ∣ c then F P c else 0) =
      ∑ P ∈ quotientSupport R Pset, ∑ c ∈ quotientSupport r cset, F (R * P) (r * c) := by
  calc
    _ = ∑ P ∈ Pset with R ∣ P, ∑ c ∈ cset with r ∣ c, F P c := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : R ∣ P
      · simp only [hd, true_and, ite_true]
      · simp [hd]
    _ = ∑ P ∈ quotientSupport R Pset, ∑ c ∈ cset with r ∣ c, F (R * P) c :=
      sum_quotientSupport R Pset (fun P => ∑ c ∈ cset with r ∣ c, F P c)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      exact sum_quotientSupport r cset (F (R * P))

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O
local notation "Grid" => Finset ((Ideal Eis × Ideal Eis) × Ideal Eis)

def quotientGridSupport (r : Ideal Eis) (T : Grid) : Grid :=
  (T.filter fun u => r ∣ u.2).image fun u => (u.1, quadraticIdealQuotient r u.2)

@[simp] theorem mem_quotientGridSupport (r : Ideal Eis) (hr : r ≠ 0)
    (T : Grid) (p : Ideal Eis × Ideal Eis) (c : Ideal Eis) :
    (p, c) ∈ quotientGridSupport r T ↔ (p, r * c) ∈ T := by
  constructor
  · intro hu
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hu
    obtain ⟨huT, hru⟩ := Finset.mem_filter.mp hu
    have hp : u.1 = p := congrArg Prod.fst he
    have hc : quadraticIdealQuotient r u.2 = c := congrArg Prod.snd he
    have hec : r * c = u.2 := by rw [← hc, quadraticIdeal_mul_quotient hru]
    simpa only [← hp, hec, Prod.eta] using huT
  · intro hu
    refine Finset.mem_image.mpr ⟨(p, r * c), Finset.mem_filter.mpr ⟨hu, dvd_mul_right _ _⟩, ?_⟩
    refine Prod.ext (show p = p from rfl) ?_
    exact mul_left_cancel₀ hr (quadraticIdeal_mul_quotient (dvd_mul_right r c))

theorem sum_quotientGridSupport {A : Type*} [AddCommMonoid A]
    (r : Ideal Eis) (T : Grid) (f : (Ideal Eis × Ideal Eis) × Ideal Eis → A) :
    (∑ u ∈ T, if r ∣ u.2 then f u else 0) =
      ∑ u ∈ quotientGridSupport r T, f (u.1, r * u.2) := by
  rw [← Finset.sum_filter, quotientGridSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [quadraticIdeal_mul_quotient (Finset.mem_filter.mp hu).2]
  · intro u hu v hv he
    apply Prod.ext
    · simpa only using congrArg Prod.fst he
    · exact quadraticIdealQuotient_injective r (Finset.mem_filter.mp hu).2
        (Finset.mem_filter.mp hv).2 (congrArg Prod.snd he)

theorem quotientGridSupport_origin (r : Ideal Eis) (hr : r ≠ 0)
    (D : Finset HybridColumnData) (p : Ideal Eis × Ideal Eis) (c : Ideal Eis)
    (hu : (p, c) ∈ quotientGridSupport r (hybridGridSupport D)) :
    ∃ d ∈ D, (d.residualN, d.residualB) = p ∧ d.common = r * c := by
  have hm := (mem_quotientGridSupport r hr (hybridGridSupport D) p c).mp hu
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hm
  exact ⟨d, hd, congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem quotientGridCommonSupport_origin (r : Ideal Eis) (hr : r ≠ 0)
    (D : Finset HybridColumnData) (m c : Ideal Eis)
    (hc : c ∈ gridCommonSupport (quotientGridSupport r (hybridGridSupport D)) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = r * c := by
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hc
  obtain ⟨huQ, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, hp, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 huQ
  refine ⟨d, hd, (congrArg Prod.fst hp).trans hum, ?_⟩
  simpa only [he] using hdc

def extractedGridCoefficient (T : Grid) (R t : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (c m h : Ideal Eis) : ℂ :=
  if ((m, h), c) ∈ T then beta c m h * (if IsCoprime R (h * t) then 1 else 0) else 0

theorem extractedGridCoefficient_norm_le_one (T : Grid) (R t : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (hb : ∀ u ∈ T, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1)
    (c m h : Ideal Eis) : ‖extractedGridCoefficient T R t beta c m h‖ ≤ 1 := by
  unfold extractedGridCoefficient
  split_ifs with hu hcop
  · simpa using hb ((m, h), c) hu
  · simp
  · simp

def gridDivisorHybridBlock (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) : ℂ :=
  ∑ u ∈ T, if r ∣ u.2 then ∑ P ∈ Pset, if R ∣ P then
    a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta u.2 u.1.1 u.1.2 *
      (canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (u.1.1 * u.1.2)) * inverseCubicKernel P (u.2 * u.1.1)) *
        (if IsCoprime P (u.1.2 * t) then 1 else 0)
    else 0 else 0

theorem gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hQ : quotientGridSupport r T = ∅) :
    gridDivisorHybridBlock T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport, hQ]
  exact Finset.sum_empty

theorem gridDivisorHybridBlock_extract
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hR : R ≠ 0) (hr : r ≠ 0)
    (hk : Admissible ((R * r) * k))
    (hP : ∀ P ∈ Pset, CubicSieve.Admissible P) :
    gridDivisorHybridBlock T Pset a beta t ((R * r) * k) R r =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        ∑ p ∈ (quotientGridSupport r T).image Prod.fst,
          canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (p.1 * p.2)) *
            ∑ c ∈ gridCommonSupport (quotientGridSupport r T) p.1,
              hybridColumnCoefficient R r (extractedGridCoefficient T R t beta) c p.1 p.2 *
                ∑ P ∈ quotientSupport R Pset,
                  hybridCubicCoefficient R r p.2 t a P * inverseCubicKernel P (c * p.1) := by
  have hmask (P h : Ideal Eis) :
      (if IsCoprime (R * P) (h * t) then (1 : ℂ) else 0) =
      (if IsCoprime R (h * t) then 1 else 0) *
        (if IsCoprime P (h * t) then 1 else 0) := by
    simp only [IsCoprime.mul_left_iff]
    split_ifs <;> simp_all
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport]
  have hinner (u : (Ideal Eis × Ideal Eis) × Ideal Eis) :
      (∑ P ∈ Pset, if R ∣ P then
        a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (canonicalQuadraticRowOfIdeal ((R * r) * k) (primaryIdealGenerator (u.1.1 * u.1.2)) *
            inverseCubicKernel P ((r * u.2) * u.1.1)) *
              (if IsCoprime P (u.1.2 * t) then 1 else 0) else 0) =
      ∑ P ∈ quotientSupport R Pset,
        a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (canonicalQuadraticRowOfIdeal ((R * r) * k) (primaryIdealGenerator (u.1.1 * u.1.2)) *
            inverseCubicKernel (R * P) ((r * u.2) * u.1.1)) *
              (if IsCoprime (R * P) (u.1.2 * t) then 1 else 0) := by
    rw [← Finset.sum_filter]
    exact sum_quotientSupport R Pset _
  simp_rw [hinner]
  rw [finite_triple_support_reindex]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hu : (p, c) ∈ quotientGridSupport r T
  · have huc := (mem_quotientGridSupport r hr T p c).mp hu
    simp only [hu, ite_true]
    apply Finset.sum_congr rfl
    intro P hPP
    have hpgen := (quotientSupport_cubic_admissible R hR Pset hP P hPP).2
    have hid := hybrid_extracted_block_identity R r k P c p.1 p.2 t hk hpgen a
      (extractedGridCoefficient T R t beta)
    simp only [extractedGridCoefficient, huc, ite_true] at hid
    rw [hmask]
    calc
      _ = a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) *
          (beta (r * c) p.1 p.2 * (if IsCoprime R (p.2 * t) then 1 else 0)) *
          (canonicalQuadraticRowOfIdeal ((R * r) * k) (primaryIdealGenerator (p.1 * p.2)) *
            inverseCubicKernel (R * P) ((r * c) * p.1)) *
          (if IsCoprime P (p.2 * t) then 1 else 0) := by ring
      _ = _ := by rw [hid]; ring
  · have huc : (p, r * c) ∉ T := (mem_quotientGridSupport r hr T p c).not.mp hu
    simp [hu, hybridColumnCoefficient, extractedGridCoefficient, huc]

end
end InverseMoment

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss  UniqueFactorizationMonoid
noncomputable section
local notation "Eis" => Eisenstein.O
local notation "Grid" => Finset ((Ideal Eis × Ideal Eis) × Ideal Eis)

def maskedGridHybridRow (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k : Ideal Eis) : ℂ :=
  ∑ u ∈ T, ∑ P ∈ Pset, (if IsCoprime k (P * u.2) then 1 else 0) *
    (a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta u.2 u.1.1 u.1.2 *
      (canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (u.1.1 * u.1.2)) * inverseCubicKernel P (u.2 * u.1.1)) *
        (if IsCoprime P (u.1.2 * t) then 1 else 0))

theorem maskedGridHybridRow_mobius (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k : Ideal Eis) (hk : k ≠ 0) :
    maskedGridHybridRow T Pset a beta t k =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        ((moebius D.1 : ℂ) * (moebius D.2 : ℂ)) *
          gridDivisorHybridBlock T Pset a beta t k D.1 D.2 := by
  have hm (P c : Ideal Eis) :
      (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        if D.1 ∣ P ∧ D.2 ∣ c then (moebius D.1 : ℂ) * (moebius D.2 : ℂ) else 0 := by
    rw [hybrid_double_mask_mobius k P c hk, Finset.sum_product]
  unfold maskedGridHybridRow
  simp_rw [hm, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  unfold gridDivisorHybridBlock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hrc : D.2 ∣ u.2
  · simp only [hrc, ite_true, and_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hRP : D.1 ∣ P <;> simp [hRP]
  · simp [hrc]

theorem gridDivisorHybridBlock_zero_of_not_coprime
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hRr : ¬ IsCoprime R r)
    (hP : ∀ P ∈ Pset, primaryIdealGenerator P ≠ 0)
    (hT : ∀ u ∈ T, primaryIdealGenerator (u.2 * u.1.1) ≠ 0) :
    gridDivisorHybridBlock T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hrc : r ∣ u.2
  · simp only [hrc, ite_true]
    apply Finset.sum_eq_zero
    intro P hPP
    by_cases hRP : R ∣ P
    · simp only [hRP, ite_true]
      rw [inverseCubicKernel_divisor_overlap_zero R r P u.2 u.1.1
        (hP P hPP) (hT u hu) hRP hrc hRr]
      simp
    · simp only [hRP, ite_false]
  · simp only [hrc, ite_false]

theorem maskedGridHybridRow_divisor_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
    ∀ (rows : Finset (Ideal Eis)) (T : Grid) (Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (t : Ideal Eis),
      (∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∑ k ∈ rows, ‖maskedGridHybridRow T Pset a beta t k‖ ^ 2) ≤
        C * K ^ ε *
          ∑ D ∈ rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)),
            ∑ k ∈ rows, if D ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
              ‖gridDivisorHybridBlock T Pset a beta t k D.1 D.2‖ ^ 2 else 0 := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro K hK rows T Pset a beta t hrows
  have he (k : Ideal Eis) (hk : k ∈ rows) :=
    maskedGridHybridRow_mobius T Pset a beta t k (hrows k hk).1
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he k hk))]
  apply finite_expansion_energy rows
    (rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)))
    (fun k => (idealDivisors k) ×ˢ (idealDivisors k))
    (fun _ D => (moebius D.1 : ℂ) * (moebius D.2 : ℂ))
    (fun k D => gridDivisorHybridBlock T Pset a beta t k D.1 D.2) (C ^ 2 * K ^ ε)
  · intro k hk D hD
    exact Finset.mem_biUnion.mpr ⟨k, hk, hD⟩
  · intro k hk D hD
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (IdealCoprimeBilinearSieve.moebius_norm_le_one D.1)
        (IdealCoprimeBilinearSieve.moebius_norm_le_one D.2) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro k hk
    have hd := (hdiv k (hrows k hk).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 (by positivity)) hC.le)
    calc
      _ = ((idealDivisors k).card : ℝ) ^ 2 := by simp [Finset.card_product, pow_two]
      _ ≤ (C * K ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = C ^ 2 * K ^ ε := by
        rw [mul_pow, pow_two (K ^ (ε / 2)), ← Real.rpow_add (by linarith : 0 < K)]
        congr 1
        congr 1
        ring

end
end InverseMoment

end

noncomputable section
open Eisenstein CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators Classical
namespace InverseMoment

theorem descent_quadratic_fixed_factor_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal O)) (pairs : Finset (Ideal O × Ideal O)),
      (∀ k ∈ rows, CanonicalQuadraticSieve.Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal O) (a : Ideal O × Ideal O → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C,hC,hb⟩ :=
    SchwartzPlanePoisson.CanonicalQuadraticSieve.quadratic_squarefree_product_energy_fixed_factor ε hε
  refine ⟨C,hC,?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  let lift : rows → QuadraticIdeal := fun k =>
    ⟨k.val,(CanonicalQuadraticSieve.admissible_iff_native k.val).mp (hrows k.val k.property).1⟩
  have hinj : Function.Injective lift := by
    intro i j h
    exact Subtype.ext (congrArg (fun I : QuadraticIdeal => I.val) h)
  let R := rows.attach.map ⟨lift,hinj⟩
  have hR (k : QuadraticIdeal) (hk : k ∈ R) : (Ideal.absNorm k.val : ℝ) ≤ K := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hk
    exact (hrows i.val i.property).2
  have he := hb K X hK hX R pairs hR hpairs B a
  have hsum : (∑ k ∈ R, ‖∑ p ∈ pairs,
      canonicalQuadraticRow k (primaryIdealGenerator (B * (p.1 * p.2))) * a p‖^2) =
      ∑ k ∈ rows, ‖∑ p ∈ pairs,
        canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (B * (p.1 * p.2))) * a p‖^2 := by
    rw [Finset.sum_map]
    calc
      _ = ∑ k ∈ rows.attach, ‖∑ p ∈ pairs,
          canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (B * (p.1 * p.2))) * a p‖^2 := by
        apply Finset.sum_congr rfl
        intro k hk
        change ‖∑ p ∈ pairs, canonicalQuadraticRow (lift k)
          (primaryIdealGenerator (B * (p.1 * p.2))) * a p‖^2 = _
        have hk' : quadraticIdealAdmissible k.val := (lift k).property
        simp only [canonicalQuadraticRowOfIdeal,dif_pos hk']
        rfl
      _ = _ := Finset.sum_attach rows (fun k => ‖∑ p ∈ pairs,
        canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (B * (p.1 * p.2))) * a p‖^2)
  rw [hsum] at he
  exact he

end InverseMoment
end

noncomputable section
open Eisenstein SchwartzPlanePoisson
open SchwartzPlanePoisson.CanonicalQuadraticSieve
open scoped BigOperators Classical
namespace InverseMoment
theorem descent_finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0) (hH : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (∑ I ∈ S, 1/(Ideal.absNorm I : ℝ)) ≤
      (2*(128 : ℝ))*(columnDyadicLength H+1 : ℝ) := by
  have hpos (I : Ideal O) (hI : I ∈ S) : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑ I ∈ divisorDyadicBin S H j, 1/(Ideal.absNorm I : ℝ)) ≤ 2*(128 : ℝ) := by
    have hp : 0 < (2 : ℝ) ^ j.val := by positivity
    have hone : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card : ℝ) ≤ (128 : ℝ)*(2 : ℝ) ^ j.val := by
      apply EisensteinLatticeCount.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I ∈ divisorDyadicBin S H j) :
        1/(Ideal.absNorm I : ℝ) ≤ 2/(2 : ℝ) ^ j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith only [hb]
    calc
      _ ≤ ∑ _I ∈ divisorDyadicBin S H j, 2/(2 : ℝ) ^ j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card : ℝ)*(2/(2 : ℝ) ^ j.val) := by simp
      _ ≤ ((128 : ℝ)*(2 : ℝ) ^ j.val)*(2/(2 : ℝ) ^ j.val) := by gcongr
      _ = _ := by field_simp
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength H+1), 2*(128 : ℝ) :=
      Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring

end InverseMoment
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open UniqueFactorizationMonoid
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength columnDyadicLength_small_power divisorDyadicLabel divisorDyadicLabel_bounds divisorDyadicScale divisorDyadicScale_ge_one divisorDyadicBin divisorDyadicBin_bounds sum_divisorDyadicBins)
open scoped BigOperators Classical
namespace InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O

theorem finite_inverse_cubic_energy
    (Jset Pset : Finset (Ideal Eis)) (N L : ℝ)
    (hJ : ∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N)
    (hP : ∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L)
    (a : Ideal Eis → ℂ) :
    (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
      CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  let A : Matrix Jset Pset ℂ := fun J P => CubicSieve.idealKernel P.val J.val
  have hnorm : CubicSieve.squaredNorm (fun J P => star (A J P)) =
      CubicSieve.squaredNorm A :=
    congrArg (fun z : ℝ => z ^ 2) (FiniteSieveOperator.operator_conjugate_norm A)
  have hfamily : CubicSieve.squaredNorm A ≤ CubicSieve.sieveNorm N L :=
    CubicSieve.family_squared_norm_le
      (fun J : Jset => J.val) (fun P : Pset => P.val)
      Subtype.val_injective Subtype.val_injective N L
      (fun J => hJ J.val J.property) (fun P => hP P.val P.property)
  have he := CubicSieve.energy_le_squaredNorm (fun J P => star (A J P)) (fun P => a P.val)
  rw [hnorm] at he
  have he' := he.trans (mul_le_mul_of_nonneg_right hfamily
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hinner (J : Jset) :
      (∑ P : Pset, star (A J P) * a P.val) =
        ∑ P ∈ Pset, a P * inverseCubicKernel P J.val := by
    simp only [A, inverseCubicKernel, CubicSieve.idealKernel, mul_comm]
    exact Finset.sum_coe_sort Pset
      (fun P => a P * star (ringComplex
        (CubicJacobi.idealSymbol P (primaryIdealGenerator J.val))))
  simp_rw [hinner] at he'
  rw [Finset.sum_coe_sort Jset
    (fun J => ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2),
    Finset.sum_coe_sort Pset (fun P => ‖a P‖ ^ 2)] at he'
  exact he'

theorem hybrid_quadratic_reduction (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (Pset : Finset (Ideal Eis)) (coef : Ideal Eis → Ideal Eis → ℂ)
      (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (Cbound : ℝ),
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * Cbound *
        ∑ p ∈ pairs, ∑ c ∈ cset p.1,
          ‖∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))‖ ^ 2 := by
  obtain ⟨C, hC, hquadratic⟩ := descent_quadratic_fixed_factor_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta Cbound hcount hbeta
  let F (p : Ideal Eis × Ideal Eis) (c : Ideal Eis) :=
    ∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))
  have he := hquadratic K X hK hX rows pairs hrows hpairs B
    (fun p => ∑ c ∈ cset p.1, beta c p.1 p.2 * F p c)
  apply he.trans
  have hlocal (p : Ideal Eis × Ideal Eis) (hp : p ∈ pairs) :
      ‖∑ c ∈ cset p.1, beta c p.1 p.2 * F p c‖ ^ 2 ≤
        Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
    exact (bounded_finset_coefficient_sum_sq (cset p.1)
      (fun c => beta c p.1 p.2) (F p) (hbeta p hp)).trans
        (mul_le_mul_of_nonneg_right (hcount p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    _ ≤ C * (K * X) ^ ε * (K + X) *
        ∑ p ∈ pairs, Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlocal)
      positivity
    _ = _ := by rw [← Finset.mul_sum]; simp only [F]; ring

theorem cubic_product_row_bound_of_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis) (S : ℝ),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ a : Ideal Eis → ℂ,
        (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
          S * ∑ P ∈ Pset, ‖a P‖ ^ 2) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * S * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro N hN pairs Jset Pset mBad S hmap hJset hcubic a
  let E (J : Ideal Eis) := ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2
  have hfiber (J : Ideal Eis) (hJ : J ∈ Jset) :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤ D * N ^ ε := by
    have hJ0 := (hJset J hJ).1.1.ne_zero
    have hc : ((pairs.filter (fun p => p.2 * (mBad * p.1) = J)).card : ℝ) ≤
        ((idealDivisors J).card : ℝ) :=
      Nat.cast_le.mpr (scaled_product_fiber_card pairs mBad J hJ0)
    have hd := (hdiv J hJ0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hJset J hJ).2 hε.le) hD.le)
    exact (by simpa using hc :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤
        ((idealDivisors J).card : ℝ)).trans hd
  have hf := fiber_energy_bound pairs Jset (fun p => p.2 * (mBad * p.1))
    (fun _ => 1) (fun _ => D * N ^ ε) E hmap (fun _ _ => sq_nonneg _) hfiber
  simp only [one_mul, ← Finset.mul_sum] at hf
  apply hf.trans
  calc
    _ ≤ (D * N ^ ε) * (S * ∑ P ∈ Pset, ‖a P‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hcubic a) (by positivity)
    _ = _ := by ring

theorem cubic_product_row_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N L : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hb⟩ := cubic_product_row_bound_of_sieve ε hε
  refine ⟨D, hD, ?_⟩
  intro N L hN pairs Jset Pset mBad hmap hJ hP a
  exact hb N hN pairs Jset Pset mBad (CubicSieve.sieveNorm N L) hmap hJ
    (finite_inverse_cubic_energy Jset Pset N L hJ hP) a

theorem hybrid_fixed_block_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L : ℝ, 1 ≤ K → 1 ≤ X → 1 ≤ N →
    ∀ (rows : Finset (Ideal Eis)) (pairs cubicPairs : Finset (Ideal Eis × Ideal Eis))
      (Hset Jset Pset : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (coef : Ideal Eis → Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
      (Cbound Ebound : ℝ), 0 ≤ Cbound →
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∀ p ∈ pairs, p.2 ∈ Hset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ cubicPairs) →
      (∀ u ∈ cubicPairs, u.2 * (mBad * u.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      (∀ h ∈ Hset, (∑ P ∈ Pset, ‖coef h P‖ ^ 2) ≤ Ebound) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * Cbound * (Hset.card : ℝ) *
        CubicSieve.sieveNorm N L * Ebound := by
  obtain ⟨Cq, hCq, hquad⟩ := hybrid_quadratic_reduction ε hε
  obtain ⟨D, hD, hcube⟩ := cubic_product_row_sieve_norm ε hε
  refine ⟨Cq * D, mul_pos hCq hD, ?_⟩
  intro K X N L hK hX hN rows pairs cubicPairs Hset Jset Pset hrows hpairs
    B mBad cset coef beta Cbound Ebound hCbound hcount hbeta hH hmc hmap hJ hP hcoef
  let E (h m c : Ideal Eis) := ‖∑ P ∈ Pset,
    coef h P * inverseCubicKernel P (c * (mBad * m))‖ ^ 2
  have hnorm : 0 ≤ CubicSieve.sieveNorm N L := sq_nonneg _
  have he := hquad K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta
    Cbound hcount hbeta
  have hpos := positive_triple_enlarge pairs cset Hset cubicPairs E hH hmc
    (fun _ _ _ => sq_nonneg _)
  have htotal : (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      (Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound) := by
    apply hpos.trans
    calc
      _ ≤ ∑ _h ∈ Hset, D * N ^ ε * CubicSieve.sieveNorm N L * Ebound := by
        apply Finset.sum_le_sum
        intro h hh
        apply (hcube N L hN cubicPairs Jset Pset mBad hmap hJ hP (coef h)).trans
        exact mul_le_mul_of_nonneg_left (hcoef h hh)
          (mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)) hnorm)
      _ = _ := by simp
  apply he.trans
  calc
    _ ≤ (Cq * (K * X) ^ ε * (K + X) * Cbound) *
        ((Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound)) := by
      apply mul_le_mul_of_nonneg_left htotal
      positivity
    _ = _ := by
      rw [Real.mul_rpow (show 0 ≤ K * X by positivity) (show 0 ≤ N by linarith)]
      ring

end
end InverseMoment

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
