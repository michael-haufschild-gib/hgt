import GaloisForLFunctions.HeckeLFunctions.HeckeCharactersSatisfyMertensBounds
import GaloisForLFunctions.ArtinMertens.TheFrobeniusDensityTheoremWithBoundedError
import GaloisForLFunctions.RHTower.Artin.ArtinIdempotentsOfAnAbelianNormalSubgroup
import GaloisForLFunctions.RHTower.Artin.ArtinEulerProductOfAnInducedRepresentation

/-!
# Ray classes below degree-one primes have index at most the degree

Let `L/K` be an extension of number fields of degree `n`, `𝔪` a modulus of `K` and
`π : Cl_𝔪 → Q` a homomorphism of the ray class group onto a finite abelian group that is trivial
on the class of `P ∩ K` for every prime `P` of `L` with `N(P) = N(P ∩ K)` and `P ∩ K` prime to
`𝔪`. Then

`|Q| ≤ [L : K]` (`card_le_finrank_of_forall_degreeOne_eq_one`).

These classes are norms from `L`, so for `Q = I^𝔪 / P_𝔪 N(I_L^𝔪)` this is the norm index
inequality `[I^𝔪 : P_𝔪 N(I_L^𝔪)] ≤ [L : K]`. No Galois hypothesis is used.

Proof, with `w(𝔞) = log N(𝔞) / N(𝔞)`:

* `K`-side (`exists_card_mul_classMertensSum_le`). The characters of `Q` composed with `π` are
  ray class characters. Their Mertens sums add up to `|Q| · Σ_{N(v) ≤ x, π[v] = 1} w(v)` by
  orthogonality (`sum_heckePrimeMertensSum_comp`); the trivial character gives `log x + O(1)`
  and the others `O(1)`.
* `L`-side (`degreeOneMertens_le_finrank_mul`). A prime of `L` of prime norm `p` lies above a
  prime of `K` of norm `p`, and at most `n` primes lie above a prime of `K`. So the Mertens sum
  of the degree-one primes of `L`, which is `log x + O(1)`, is at most `n` times the sum of
  `w(v)` over the primes `v` of `K` below them.
* The primes `v` below degree-one primes have trivial class or divide `𝔪`
  (`degreeOneBelowMertensSum_le`). Hence `log x ≤ (n / |Q|) log x + O(1)`.
-/

open scoped Classical BigOperators NumberField
open Finset Ideal IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

open HeckeLFunctions ArtinMertens

attribute [local instance] finiteLinearCharacter fintypeLinearCharacter

variable {K : Type u} [Field K] [NumberField K]

/-- The Mertens weight of an ideal: `log N(𝔞) / N(𝔞)`. -/
def mertensWeight (I : Ideal (𝓞 K)) : ℝ := Real.log (absNorm I) / absNorm I

theorem mertensWeight_nonneg (I : Ideal (𝓞 K)) : 0 ≤ mertensWeight I :=
  div_nonneg (log_absNorm_nonneg I) (Nat.cast_nonneg _)

/-! ### The primes with trivial class in a quotient -/

section ClassSide

variable (𝔪 : Modulus K) {Q : Type*} [CommGroup Q] [Finite Q] (π : RayClassGroup 𝔪 →* Q)

/-- The integral ideal `I` is prime to `𝔪` and `π` is trivial on its ray class. -/
def ClassTrivial (I : Ideal (𝓞 K)) : Prop :=
  ∃ (hI : I ≠ ⊥) (hm : idealUnit hI ∈ idealGroup 𝔪), π (rayClass 𝔪 ⟨_, hm⟩) = 1

/-- The Mertens sum of the prime ideals on whose class `π` is trivial. -/
def classMertensSum (N : ℕ) : ℝ :=
  ∑ P ∈ (idealsLe K N).filter (fun P => P.IsPrime ∧ ClassTrivial 𝔪 π P), mertensWeight P

/-- **Orthogonality on ideals**: the characters of `Q` composed with `π` sum to `|Q|` on the
ideals with trivial class and to `0` on the others. -/
theorem sum_heckeValue_comp (I : Ideal (𝓞 K)) :
    ∑ χ : LinearCharacter Q, heckeValue 𝔪 (χ.comp π) I =
      if ClassTrivial 𝔪 π I then (Nat.card Q : ℂ) else 0 := by
  haveI : Fintype Q := Fintype.ofFinite Q
  by_cases h : ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪
  · obtain ⟨hI, hm⟩ := h
    have h1 : ∀ χ : LinearCharacter Q, heckeValue 𝔪 (χ.comp π) I =
        ((χ (π (rayClass 𝔪 ⟨_, hm⟩)) : ℂˣ) : ℂ) := fun χ => heckeValue_of_mem 𝔪 _ hI hm
    have hiff : π (rayClass 𝔪 ⟨_, hm⟩) = 1 ↔ ClassTrivial 𝔪 π I :=
      ⟨fun hc => ⟨hI, hm, hc⟩, fun ⟨_, _, hc⟩ => hc⟩
    rw [Finset.sum_congr rfl fun χ _ => h1 χ, sum_linearCharacter_apply]
    simp only [hiff]
  · have h1 : ∀ χ : LinearCharacter Q, heckeValue 𝔪 (χ.comp π) I = 0 :=
      fun χ => heckeValue_of_not_mem 𝔪 _ h
    rw [Finset.sum_congr rfl fun χ _ => h1 χ, Finset.sum_const_zero, if_neg]
    rintro ⟨hI, hm, -⟩
    exact h ⟨hI, hm⟩

/-- The Mertens sums of the characters of `Q` add up to `|Q|` times the Mertens sum of the
primes with trivial class. -/
theorem sum_heckePrimeMertensSum_comp (N : ℕ) :
    ∑ χ : LinearCharacter Q, heckePrimeMertensSum 𝔪 (χ.comp π) N =
      (Nat.card Q : ℂ) * (classMertensSum 𝔪 π N : ℂ) := by
  unfold heckePrimeMertensSum classMertensSum
  rw [Finset.sum_comm]
  have h1 : ∀ P ∈ (idealsLe K N).filter (fun P => P.IsPrime),
      ∑ χ : LinearCharacter Q, heckeValue 𝔪 (χ.comp π) P *
          ((Real.log (absNorm P) / absNorm P : ℝ) : ℂ) =
        if ClassTrivial 𝔪 π P then (Nat.card Q : ℂ) * ((mertensWeight P : ℝ) : ℂ) else 0 := by
    intro P _
    rw [← Finset.sum_mul, sum_heckeValue_comp, ite_mul, zero_mul]
    rfl
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.filter_filter, ← Finset.mul_sum,
    Complex.ofReal_sum]

/-- **The primes with trivial class have Mertens sum at most `(log x + O(1)) / |Q|`**, for `π`
onto `Q`. -/
theorem exists_card_mul_classMertensSum_le (hπ : Function.Surjective π) :
    ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N → (Nat.card Q : ℝ) * classMertensSum 𝔪 π N ≤ Real.log N + B := by
  -- the Mertens bound of each character
  have hχ : ∀ χ : LinearCharacter Q, ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      ‖heckePrimeMertensSum 𝔪 (χ.comp π) N - (if χ = 1 then (Real.log N : ℂ) else 0)‖ ≤ B := by
    intro χ
    by_cases h : χ = 1
    · subst h
      obtain ⟨B, hB⟩ := exists_norm_heckePrimeMertensSum_one_sub_log_le 𝔪
      refine ⟨B, fun N hN => ?_⟩
      rw [if_pos rfl, MonoidHom.one_comp]
      exact hB N hN
    · have hne : χ.comp π ≠ 1 := fun h1 => h <| MonoidHom.ext fun x => by
        obtain ⟨c, rfl⟩ := hπ x
        exact DFunLike.congr_fun h1 c
      obtain ⟨B, hB⟩ := exists_norm_heckePrimeMertensSum_le 𝔪 hne
      refine ⟨B, fun N _ => ?_⟩
      rw [if_neg h, sub_zero]
      exact hB N
  choose Bf hBf using hχ
  refine ⟨∑ χ, Bf χ, fun N hN => ?_⟩
  have hsum : ∑ χ : LinearCharacter Q, (heckePrimeMertensSum 𝔪 (χ.comp π) N -
        (if χ = 1 then (Real.log N : ℂ) else 0)) =
      (((Nat.card Q : ℝ) * classMertensSum 𝔪 π N - Real.log N : ℝ) : ℂ) := by
    rw [Finset.sum_sub_distrib, sum_heckePrimeMertensSum_comp, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
    push_cast
    rfl
  have hnorm := norm_sum_le Finset.univ fun χ : LinearCharacter Q =>
    heckePrimeMertensSum 𝔪 (χ.comp π) N - (if χ = 1 then (Real.log N : ℂ) else 0)
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at hnorm
  have h := (le_abs_self _).trans (hnorm.trans (Finset.sum_le_sum fun χ _ => hBf χ N hN))
  linarith

end ClassSide

/-! ### The primes below degree-one primes -/

section ExtensionSide

variable (K) (L : Type u) [Field L] [NumberField L] [Algebra K L]

/-- The ideal `v` of `K` lies below a prime of `L` of the same norm. -/
def IsBelowDegreeOne (v : Ideal (𝓞 K)) : Prop :=
  ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.under (𝓞 K) = v ∧ absNorm P = absNorm v

/-- The Mertens sum of the primes of `K` below a prime of `L` of the same norm. -/
def degreeOneBelowMertensSum (N : ℕ) : ℝ :=
  ∑ v ∈ (idealsLe K N).filter (fun v => v.IsPrime ∧ IsBelowDegreeOne K L v), mertensWeight v

variable {K L}

/-- At most `[L : K]` primes of `L` lie above a prime of `K`. -/
theorem card_filter_under_eq_le_finrank {v : Ideal (𝓞 K)} (hv : v.IsPrime) (hv0 : v ≠ ⊥)
    (s : Finset (Ideal (𝓞 L))) (hs : ∀ P ∈ s, P.IsPrime) :
    (s.filter fun P => P.under (𝓞 K) = v).card ≤ Module.finrank K L := by
  haveI : v.IsMaximal := hv.isMaximal hv0
  haveI : NoZeroSMulDivisors (𝓞 K) (𝓞 L) := ⟨fun h => smul_eq_zero.mp h⟩
  refine (Finset.card_le_card fun P hP => ?_).trans
    (Ideal.card_primesOverFinset_le_finrank (𝓞 L) K L hv0)
  obtain ⟨hPs, hPv⟩ := Finset.mem_filter.mp hP
  exact (IsDedekindDomain.mem_primesOverFinset_iff hv0 _).mpr ⟨hs P hPs, ⟨hPv.symm⟩⟩

/-- A prime of `L` of prime norm `p` lies above a prime of `K` of norm `p`. -/
theorem absNorm_under_eq_of_absNorm_eq_prime {P : Ideal (𝓞 L)} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hN : absNorm P = p) : absNorm (P.under (𝓞 K)) = p := by
  have h := absNorm_eq_absNorm_under_pow_inertiaDeg (K := K) (⟨P, hP, hP0⟩ : HeightOneSpectrum (𝓞 L))
  rw [hN] at h
  exact (hp.pow_eq_iff.mp h.symm).1

/-- The number of primes of `L` of norm `p` is at most `[L : K]` times the number of primes of
`K` of norm `p` below them. -/
theorem degreeOneCount_le_finrank_mul_card {p : ℕ} (hp : p.Prime) :
    degreeOneCount L p ≤ Module.finrank K L *
      ((idealsLe K p).filter fun v =>
        (v.IsPrime ∧ IsBelowDegreeOne K L v) ∧ absNorm v = p).card := by
  rw [degreeOneCount]
  have hmem : ∀ P ∈ (idealsLe L p).filter (fun P => P.IsPrime ∧ absNorm P = p),
      P.IsPrime ∧ P ≠ ⊥ ∧ absNorm P = p := fun P hP =>
    ⟨(Finset.mem_filter.mp hP).2.1, (mem_idealsLe.mp (Finset.mem_filter.mp hP).1).1,
      (Finset.mem_filter.mp hP).2.2⟩
  have hunder : ∀ P ∈ (idealsLe L p).filter (fun P => P.IsPrime ∧ absNorm P = p),
      (P.under (𝓞 K)).IsPrime ∧ P.under (𝓞 K) ≠ ⊥ ∧ absNorm (P.under (𝓞 K)) = p := by
    intro P hP
    obtain ⟨hPp, hP0, hPN⟩ := hmem P hP
    have hN := absNorm_under_eq_of_absNorm_eq_prime (K := K) hPp hP0 hp hPN
    refine ⟨Ideal.IsPrime.under (𝓞 K) P, fun h0 => hp.ne_zero ?_, hN⟩
    rw [← hN, h0, Ideal.absNorm_bot]
  refine (Finset.card_le_mul_card_image (f := fun P : Ideal (𝓞 L) => P.under (𝓞 K)) _
    (Module.finrank K L) fun v hv => ?_).trans
    (Nat.mul_le_mul_left _ (Finset.card_le_card fun v hv => ?_))
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hvp, hv0, -⟩ := hunder P hP
    exact card_filter_under_eq_le_finrank hvp hv0 _ fun P' hP' => (hmem P' hP').1
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hvp, hv0, hvN⟩ := hunder P hP
    obtain ⟨hPp, -, hPN⟩ := hmem P hP
    exact Finset.mem_filter.mpr ⟨mem_idealsLe.mpr ⟨hv0, hvN.le⟩,
      ⟨hvp, P, hPp, rfl, hPN.trans hvN.symm⟩, hvN⟩

/-- **The degree-one primes of `L` are carried by the primes of `K` below them**, with
multiplicity at most `[L : K]`. -/
theorem degreeOneMertens_le_finrank_mul (N : ℕ) :
    degreeOneMertens L N ≤ (Module.finrank K L : ℝ) * degreeOneBelowMertensSum K L N := by
  rw [degreeOneMertens, degreeOneBelowMertensSum]
  -- the primes of `K` of prime norm below degree-one primes, grouped by their norm
  have hmaps : ∀ v ∈ (idealsLe K N).filter (fun v =>
      (v.IsPrime ∧ IsBelowDegreeOne K L v) ∧ (absNorm v).Prime),
      absNorm v ∈ (Icc 1 N).filter Nat.Prime := fun v hv => by
    obtain ⟨hv1, -, hvp⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hvp.one_lt.le, (mem_idealsLe.mp hv1).2⟩, hvp⟩
  calc ∑ p ∈ (Icc 1 N).filter Nat.Prime, (degreeOneCount L p : ℝ) * (Real.log p / p)
      ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, (Module.finrank K L : ℝ) *
          ∑ v ∈ ((idealsLe K N).filter (fun v =>
            (v.IsPrime ∧ IsBelowDegreeOne K L v) ∧ (absNorm v).Prime)).filter
              (fun v => absNorm v = p), mertensWeight v := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hpN, hpp⟩ := Finset.mem_filter.mp hp
        have hw : ∀ v ∈ ((idealsLe K N).filter (fun v =>
            (v.IsPrime ∧ IsBelowDegreeOne K L v) ∧ (absNorm v).Prime)).filter
              (fun v => absNorm v = p), mertensWeight v = Real.log p / p := fun v hv => by
          rw [mertensWeight, (Finset.mem_filter.mp hv).2]
        rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_
          (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
        have h1 := degreeOneCount_le_finrank_mul_card (K := K) (L := L) hpp
        have h2 : ((idealsLe K p).filter fun v =>
            (v.IsPrime ∧ IsBelowDegreeOne K L v) ∧ absNorm v = p).card ≤
            (((idealsLe K N).filter (fun v =>
              (v.IsPrime ∧ IsBelowDegreeOne K L v) ∧ (absNorm v).Prime)).filter
                (fun v => absNorm v = p)).card := by
          refine Finset.card_le_card fun v hv => ?_
          obtain ⟨hv1, hv2, hv3⟩ := Finset.mem_filter.mp hv
          obtain ⟨hv0, hvle⟩ := mem_idealsLe.mp hv1
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨mem_idealsLe.mpr ⟨hv0, hvle.trans (Finset.mem_Icc.mp hpN).2⟩, hv2, hv3 ▸ hpp⟩, hv3⟩
        exact_mod_cast h1.trans (Nat.mul_le_mul_left _ h2)
    _ = (Module.finrank K L : ℝ) * ∑ v ∈ (idealsLe K N).filter (fun v =>
          (v.IsPrime ∧ IsBelowDegreeOne K L v) ∧ (absNorm v).Prime), mertensWeight v := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmaps]
    _ ≤ (Module.finrank K L : ℝ) * ∑ v ∈ (idealsLe K N).filter (fun v =>
          v.IsPrime ∧ IsBelowDegreeOne K L v), mertensWeight v := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => ?_)
          fun v _ _ => mertensWeight_nonneg v) (Nat.cast_nonneg _)
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2.1⟩

variable (𝔪 : Modulus K) {Q : Type*} [CommGroup Q] [Finite Q] (π : RayClassGroup 𝔪 →* Q)

/-- The arithmetic of the comparison: from `D = ℓ + O(1)`, `D ≤ n S'`, `S' ≤ S + c` and
`q S ≤ ℓ + B`, the quantity `(q − n) ℓ` is bounded. -/
theorem mertens_chain_le {q n ℓ C B S S' D c : ℝ} (hn : 0 ≤ n) (hq : 0 ≤ q)
    (h1 : |D - ℓ| ≤ C) (h2 : D ≤ n * S') (h3 : S' ≤ S + c) (h4 : q * S ≤ ℓ + B) :
    (q - n) * ℓ ≤ q * C + n * B + n * (q * c) := by
  have h5 : ℓ - C ≤ n * (S + c) := by
    have := mul_le_mul_of_nonneg_left h3 hn
    linarith [(abs_le.mp h1).1]
  have h6 := mul_le_mul_of_nonneg_left h5 hq
  have h7 := mul_le_mul_of_nonneg_left h4 hn
  linarith

omit [Finite Q] in
/-- **A prime below a degree-one prime has trivial class or divides the modulus.** -/
theorem degreeOneBelowMertensSum_le
    (hH : ∀ P : Ideal (𝓞 L), P.IsPrime → absNorm P = absNorm (P.under (𝓞 K)) →
      ∀ (h0 : P.under (𝓞 K) ≠ ⊥) (hm : idealUnit h0 ∈ idealGroup 𝔪),
        π (rayClass 𝔪 ⟨_, hm⟩) = 1)
    (N : ℕ) :
    degreeOneBelowMertensSum K L N ≤ classMertensSum 𝔪 π N +
      ∑ v ∈ (idealsLe K (absNorm 𝔪.fin)).filter (fun v => v.IsPrime), mertensWeight v := by
  rw [degreeOneBelowMertensSum, classMertensSum,
    ← Finset.sum_filter_add_sum_filter_not _ (fun v => ClassTrivial 𝔪 π v)]
  refine add_le_add
    (Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) fun v _ _ => mertensWeight_nonneg v)
    (Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) fun v _ _ => mertensWeight_nonneg v)
  · obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    obtain ⟨hv3, hv4, -⟩ := Finset.mem_filter.mp hv1
    exact Finset.mem_filter.mpr ⟨hv3, hv4, hv2⟩
  · obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    obtain ⟨hv3, hvp, P, hPp, rfl, hPN⟩ := Finset.mem_filter.mp hv1
    have hv0 := (mem_idealsLe.mp hv3).1
    -- `v` is not prime to `𝔪`, so it divides `𝔪₀`
    have hnot : ¬ idealUnit hv0 ∈ idealGroup 𝔪 := fun hm => hv2 ⟨hv0, hm, hH P hPp hPN hv0 hm⟩
    rw [idealUnit_mem_idealGroup_iff] at hnot
    haveI hmax : (P.under (𝓞 K)).IsMaximal := hvp.isMaximal hv0
    have hle : 𝔪.fin ≤ P.under (𝓞 K) := by
      have h := hmax.eq_of_le hnot le_sup_left
      exact h ▸ le_sup_right
    have hpos : 0 < absNorm 𝔪.fin :=
      Nat.pos_of_ne_zero fun h => 𝔪.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact Finset.mem_filter.mpr ⟨mem_idealsLe.mpr
      ⟨hv0, Nat.le_of_dvd hpos (Ideal.absNorm_dvd_absNorm_of_le hle)⟩, hvp⟩

/-- **The norm index inequality.** A quotient of the ray class group in which the classes of
the primes of `K` below the degree-one primes of `L` are trivial has at most `[L : K]`
elements. -/
theorem card_le_finrank_of_forall_degreeOne_eq_one (hπ : Function.Surjective π)
    (hH : ∀ P : Ideal (𝓞 L), P.IsPrime → absNorm P = absNorm (P.under (𝓞 K)) →
      ∀ (h0 : P.under (𝓞 K) ≠ ⊥) (hm : idealUnit h0 ∈ idealGroup 𝔪),
        π (rayClass 𝔪 ⟨_, hm⟩) = 1) :
    Nat.card Q ≤ Module.finrank K L := by
  by_contra hlt
  obtain ⟨B, hB⟩ := exists_card_mul_classMertensSum_le 𝔪 π hπ
  obtain ⟨C, hC⟩ := exists_abs_degreeOneMertens_sub_log_le L
  have hqn : (Module.finrank K L : ℝ) < (Nat.card Q : ℝ) := Nat.cast_lt.mpr (not_le.mp hlt)
  -- `(|Q| − [L : K]) log N` is bounded
  obtain ⟨R, key⟩ : ∃ R : ℝ, ∀ N : ℕ, 2 ≤ N →
      ((Nat.card Q : ℝ) - Module.finrank K L) * Real.log N ≤ R :=
    ⟨_, fun N hN => mertens_chain_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (hC N hN)
      (degreeOneMertens_le_finrank_mul N) (degreeOneBelowMertensSum_le 𝔪 π hH N) (hB N hN)⟩
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hNbig, hN2⟩ := ((hlog.eventually_gt_atTop
    (R / ((Nat.card Q : ℝ) - Module.finrank K L))).and (Filter.eventually_ge_atTop 2)).exists
  have h := key N hN2
  rw [div_lt_iff₀ (sub_pos.mpr hqn)] at hNbig
  linarith

end ExtensionSide

end GaloisForLFunctions
