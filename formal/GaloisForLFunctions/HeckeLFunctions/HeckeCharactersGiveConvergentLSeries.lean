import GaloisForLFunctions.HeckeLFunctions.TheRayClassGroupIsFinite
import GaloisForLFunctions.ArtinMertens.TheSoftMertensTheoremForPrimeIdeals

/-!
# Hecke characters give convergent L-series

A **Hecke character** of finite order and modulus `𝔪` is a character `ψ : Cl_𝔪 → ℂˣ` of the ray
class group. On integral ideals it is `ψ(𝔞) = ψ([𝔞])` for `𝔞` prime to `𝔪` and `0` otherwise
(`heckeValue`); it is completely multiplicative (`heckeValue_mul`) with `|ψ(𝔞)| ≤ 1`. Its
**Hecke L-series** is `L(s, ψ) = Σ_𝔞 ψ(𝔞) N𝔞^{−s} = Σ_n a_ψ(n) n^{−s}`, `a_ψ(n) = Σ_{N𝔞 = n} ψ(𝔞)`
(`heckeL`), and it converges absolutely for `Re s > 1` (`lSeriesSummable_heckeCoeff`), since the
ideals of norm `≤ x` number `O(x)` (`exists_idealCount_le_mul`).
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal Filter
  Asymptotics Finset
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.HeckeLFunctions

open GaloisForLFunctions.ArtinMertens

variable {K : Type*} [Field K] [NumberField K]

/-- The unit fractional ideal of a non-zero integral ideal. -/
def idealUnit {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩

theorem coe_idealUnit {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (idealUnit hI : FractionalIdeal (𝓞 K)⁰ K) = I :=
  FractionalIdeal.coe_mk0 K _

theorem idealUnit_mul {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealUnit (mul_ne_zero hI hJ) = idealUnit hI * idealUnit hJ :=
  Units.ext (by rw [Units.val_mul, coe_idealUnit, coe_idealUnit, coe_idealUnit, coeIdeal_mul])

theorem count_idealUnit_nonneg {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ count K v (idealUnit hI : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [coe_idealUnit, count_coe K v hI]
  exact Int.natCast_nonneg _

/-- A product of integral ideals is prime to `𝔪` iff both factors are. -/
theorem idealUnit_mul_mem_iff (𝔪 : Modulus K) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealUnit (mul_ne_zero hI hJ) ∈ idealGroup 𝔪 ↔
      idealUnit hI ∈ idealGroup 𝔪 ∧ idealUnit hJ ∈ idealGroup 𝔪 := by
  rw [idealUnit_mul hI hJ]
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have h1 := h v hv
      rw [Units.val_mul, count_mul K v (idealUnit hI).ne_zero (idealUnit hJ).ne_zero] at h1
      linarith [count_idealUnit_nonneg hI v, count_idealUnit_nonneg hJ v]
    · have h1 := h v hv
      rw [Units.val_mul, count_mul K v (idealUnit hI).ne_zero (idealUnit hJ).ne_zero] at h1
      linarith [count_idealUnit_nonneg hI v, count_idealUnit_nonneg hJ v]
  · exact fun h => (idealGroup 𝔪).mul_mem h.1 h.2

variable (𝔪 : Modulus K)

/-- A **Hecke character** of finite order: a character of the ray class group `Cl_𝔪`. -/
abbrev HeckeCharacter : Type _ := RayClassGroup 𝔪 →* ℂˣ

/-- The value `ψ(𝔞)` on an integral ideal: `ψ([𝔞])` if `𝔞` is prime to `𝔪`, else `0`. -/
def heckeValue (ψ : HeckeCharacter 𝔪) (I : Ideal (𝓞 K)) : ℂ :=
  if h : ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪 then
    (ψ (rayClass 𝔪 ⟨_, h.choose_spec⟩) : ℂ) else 0

theorem heckeValue_of_mem (ψ : HeckeCharacter 𝔪) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hm : idealUnit hI ∈ idealGroup 𝔪) :
    heckeValue 𝔪 ψ I = ψ (rayClass 𝔪 ⟨_, hm⟩) := by
  rw [heckeValue, dif_pos ⟨hI, hm⟩]

theorem heckeValue_of_not_mem (ψ : HeckeCharacter 𝔪) {I : Ideal (𝓞 K)}
    (h : ¬ ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪) : heckeValue 𝔪 ψ I = 0 := by
  rw [heckeValue, dif_neg h]

/-- Characters of a finite group take values on the unit circle. -/
theorem norm_char_eq_one {G : Type*} [Group G] [Finite G] (ψ : G →* ℂˣ) (g : G) :
    ‖(ψ g : ℂ)‖ = 1 := by
  have h : (ψ g : ℂ) ^ Nat.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h' := congrArg norm h
  rw [norm_pow, norm_one] at h'
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Nat.card_pos.ne').mp h'

theorem norm_heckeValue_le_one (ψ : HeckeCharacter 𝔪) (I : Ideal (𝓞 K)) :
    ‖heckeValue 𝔪 ψ I‖ ≤ 1 := by
  rw [heckeValue]
  split_ifs
  · exact (norm_char_eq_one ψ _).le
  · simp

/-- **Complete multiplicativity**: `ψ(𝔞𝔟) = ψ(𝔞) ψ(𝔟)`. -/
theorem heckeValue_mul (ψ : HeckeCharacter 𝔪) (I J : Ideal (𝓞 K)) :
    heckeValue 𝔪 ψ (I * J) = heckeValue 𝔪 ψ I * heckeValue 𝔪 ψ J := by
  by_cases hI : I = ⊥
  · rw [hI, Submodule.bot_mul, heckeValue_of_not_mem 𝔪 ψ (fun h => h.1 rfl), zero_mul]
  by_cases hJ : J = ⊥
  · rw [hJ, Submodule.mul_bot, heckeValue_of_not_mem 𝔪 ψ (fun h => h.1 rfl), mul_zero]
  by_cases hm : idealUnit hI ∈ idealGroup 𝔪 ∧ idealUnit hJ ∈ idealGroup 𝔪
  · have hm' := (idealUnit_mul_mem_iff 𝔪 hI hJ).mpr hm
    rw [heckeValue_of_mem 𝔪 ψ (mul_ne_zero hI hJ) hm', heckeValue_of_mem 𝔪 ψ hI hm.1,
      heckeValue_of_mem 𝔪 ψ hJ hm.2, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 3
    exact Subtype.ext (idealUnit_mul hI hJ)
  · rw [heckeValue_of_not_mem 𝔪 ψ (fun ⟨h0, h⟩ => hm ((idealUnit_mul_mem_iff 𝔪 hI hJ).mp h))]
    by_cases hmI : idealUnit hI ∈ idealGroup 𝔪
    · have hmJ : idealUnit hJ ∉ idealGroup 𝔪 := fun h => hm ⟨hmI, h⟩
      rw [heckeValue_of_not_mem 𝔪 ψ (I := J) (fun ⟨h0, h⟩ => hmJ h), mul_zero]
    · rw [heckeValue_of_not_mem 𝔪 ψ (I := I) (fun ⟨h0, h⟩ => hmI h), zero_mul]

variable (K) in
/-- The ideals of norm `n`. -/
def idealsOfNorm (n : ℕ) : Finset (Ideal (𝓞 K)) := (Ideal.finite_setOf_absNorm_eq n).toFinset

theorem mem_idealsOfNorm {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ idealsOfNorm K n ↔ Ideal.absNorm I = n := by
  simp [idealsOfNorm]

/-- The Dirichlet coefficients `a_ψ(n) = Σ_{N𝔞 = n} ψ(𝔞)`. -/
def heckeCoeff (ψ : HeckeCharacter 𝔪) (n : ℕ) : ℂ := ∑ I ∈ idealsOfNorm K n, heckeValue 𝔪 ψ I

/-- The **Hecke L-series** `L(s, ψ) = Σ_𝔞 ψ(𝔞) N𝔞^{−s}`. -/
def heckeL (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ := LSeries (heckeCoeff 𝔪 ψ) s

theorem norm_heckeCoeff_le (ψ : HeckeCharacter 𝔪) (n : ℕ) :
    ‖heckeCoeff 𝔪 ψ n‖ ≤ (idealsOfNorm K n).card :=
  (norm_sum_le _ _).trans (by
    simpa using sum_le_sum fun I (_ : I ∈ idealsOfNorm K n) => norm_heckeValue_le_one 𝔪 ψ I)

/-- The ideals of norm in `[1, n]` are the non-zero ideals of norm `≤ n`. -/
theorem sum_card_idealsOfNorm (n : ℕ) :
    ∑ k ∈ Icc 1 n, ((idealsOfNorm K k).card : ℝ) = idealCount K n := by
  rw [idealCount]
  have hmaps : ∀ I ∈ idealsLe K n, Ideal.absNorm I ∈ Icc 1 n := by
    intro I hI
    rw [mem_idealsLe] at hI
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr fun h => hI.1 (Ideal.absNorm_eq_zero_iff.mp h),
      hI.2⟩
  rw [card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  refine sum_congr rfl fun k hk => ?_
  congr 2
  ext I
  rw [mem_idealsOfNorm, mem_filter, mem_idealsLe]
  constructor
  · intro h
    refine ⟨⟨fun h0 => ?_, h ▸ (mem_Icc.mp hk).2⟩, h⟩
    rw [h0, Ideal.absNorm_bot] at h
    exact absurd h (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hk).1).symm
  · exact fun h => h.2

/-- The coefficient sums are `O(x)`. -/
theorem sum_norm_heckeCoeff_isBigO (ψ : HeckeCharacter 𝔪) :
    (fun n ↦ ∑ k ∈ Icc 1 n, ‖heckeCoeff 𝔪 ψ k‖) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
  obtain ⟨B, hB0, hB⟩ := exists_idealCount_le_mul (K := K)
  refine IsBigO.of_bound B (Eventually.of_forall fun n => ?_)
  rw [Real.norm_of_nonneg (sum_nonneg fun _ _ => norm_nonneg _), Real.rpow_one,
    Real.norm_of_nonneg (Nat.cast_nonneg n)]
  calc ∑ k ∈ Icc 1 n, ‖heckeCoeff 𝔪 ψ k‖ ≤ ∑ k ∈ Icc 1 n, ((idealsOfNorm K k).card : ℝ) :=
        sum_le_sum fun k _ => norm_heckeCoeff_le 𝔪 ψ k
    _ = idealCount K n := sum_card_idealsOfNorm n
    _ ≤ B * n := hB n

/-- **Absolute convergence** of `L(s, ψ)` for `Re s > 1`. -/
theorem lSeriesSummable_heckeCoeff (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (heckeCoeff 𝔪 ψ) s :=
  LSeriesSummable_of_sum_norm_bigO (sum_norm_heckeCoeff_isBigO 𝔪 ψ) zero_le_one hs

end GaloisForLFunctions.HeckeLFunctions
