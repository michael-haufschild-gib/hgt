import GaloisForLFunctions.RHTower.Artin.RayClassesBelowDegreeOnePrimesHaveIndexAtMostTheDegree

/-!
# An extension in which almost all primes split completely is trivial

Let `M/K` be an extension of number fields and `B` a bound such that every prime `P` of `M`
above a prime `v` of `K` with `N(v) > B` is unramified with `N(P) = N(v)`. Then `M = K`:

`[M : K] = 1` (`finrank_eq_one_of_forall_split`).

Proof. Above such a `v` lie exactly `[M : K]` primes of `M`, by `Σ e f = [M : K]`
(`card_primesOverFinset_eq_finrank`), all of the norm of `v`. So `M` has at least `[M : K]`
times as many primes of norm `p` as `K`, for every rational prime `p > B`
(`finrank_mul_degreeOneCount_le`). The Mertens sums of the degree-one primes of `K` and of `M`
are both `log x + O(1)`; hence `[M : K] log x ≤ log x + O(1)`.
-/

open scoped Classical BigOperators NumberField
open Finset Ideal IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

open ArtinMertens

variable {K : Type u} [Field K] [NumberField K] {M : Type u} [Field M] [NumberField M]
  [Algebra K M]

/-- **Exactly `[M : K]` primes lie above a prime that splits completely.** -/
theorem card_primesOverFinset_eq_finrank {v : Ideal (𝓞 K)} [v.IsMaximal] (hv0 : v ≠ ⊥)
    (h : ∀ P : Ideal (𝓞 M), P.IsPrime → P.under (𝓞 K) = v →
      P.ramificationIdx (𝓞 K) = 1 ∧ absNorm P = absNorm v) :
    (IsDedekindDomain.primesOverFinset v (𝓞 M)).card = Module.finrank K M := by
  rw [← Ideal.sum_ramification_inertia (𝓞 M) K M hv0, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hPp, hPv⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 _).mp hP
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P
  haveI : P.IsMaximal := hPp.isMaximal hP0
  have hunder : P.under (𝓞 K) = v := (P.over_def v).symm
  obtain ⟨he, hN⟩ := h P hPp hunder
  -- `N(P) = N(v)^f` and `N(P) = N(v)` give `f = 1`
  have hf : P.inertiaDeg (𝓞 K) = 1 := by
    have hpow : absNorm P = absNorm (P.under (𝓞 K)) ^ P.inertiaDeg (𝓞 K) :=
      absNorm_eq_absNorm_under_pow_inertiaDeg (K := K) (⟨P, hPp, hP0⟩ : HeightOneSpectrum (𝓞 M))
    rw [hunder, hN] at hpow
    exact (Nat.pow_right_injective (two_le_absNorm_of_isPrime inferInstance hv0)
      (hpow.symm.trans (pow_one _).symm))
  rw [ramificationIdx'_eq_ramificationIdx v P hv0, inertiaDeg'_eq_inertiaDeg v P, he, hf]

variable {B : ℕ}

/-- **`M` has `[M : K]` times as many primes of norm `p` as `K`**, for a rational prime
`p > B`. -/
theorem finrank_mul_degreeOneCount_le
    (h : ∀ P : Ideal (𝓞 M), P.IsPrime → P ≠ ⊥ → B < absNorm (P.under (𝓞 K)) →
      P.ramificationIdx (𝓞 K) = 1 ∧ absNorm P = absNorm (P.under (𝓞 K)))
    {p : ℕ} (hp : p.Prime) (hB : B < p) :
    Module.finrank K M * degreeOneCount K p ≤ degreeOneCount M p := by
  rw [degreeOneCount, degreeOneCount]
  -- a prime of `M` of norm `p` lies above a prime of `K` of norm `p`
  have hmaps : ∀ P ∈ (idealsLe M p).filter (fun P => P.IsPrime ∧ absNorm P = p),
      P.under (𝓞 K) ∈ (idealsLe K p).filter (fun v => v.IsPrime ∧ absNorm v = p) := by
    intro P hP
    obtain ⟨hP1, hPp, hPN⟩ := Finset.mem_filter.mp hP
    have hN := absNorm_under_eq_of_absNorm_eq_prime (K := K) hPp (mem_idealsLe.mp hP1).1 hp hPN
    refine Finset.mem_filter.mpr ⟨mem_idealsLe.mpr ⟨fun h0 => hp.ne_zero ?_, hN.le⟩,
      Ideal.IsPrime.under (𝓞 K) P, hN⟩
    rw [← hN, h0, Ideal.absNorm_bot]
  calc Module.finrank K M * ((idealsLe K p).filter fun v => v.IsPrime ∧ absNorm v = p).card
      = ∑ _v ∈ (idealsLe K p).filter (fun v => v.IsPrime ∧ absNorm v = p),
          Module.finrank K M := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ v ∈ (idealsLe K p).filter (fun v => v.IsPrime ∧ absNorm v = p),
          (((idealsLe M p).filter fun P => P.IsPrime ∧ absNorm P = p).filter
            fun P => P.under (𝓞 K) = v).card := by
        refine Finset.sum_le_sum fun v hv => ?_
        obtain ⟨hv1, hvp, hvN⟩ := Finset.mem_filter.mp hv
        have hv0 := (mem_idealsLe.mp hv1).1
        haveI : v.IsMaximal := hvp.isMaximal hv0
        -- the primes of `M` above `v` have norm `p`
        have hsplit : ∀ P : Ideal (𝓞 M), P.IsPrime → P.under (𝓞 K) = v →
            P.ramificationIdx (𝓞 K) = 1 ∧ absNorm P = absNorm v := by
          intro P hPp hPv
          have hP0 : P ≠ ⊥ := fun h0 => hv0 (by rw [← hPv, h0, Ideal.under_bot])
          have := h P hPp hP0 (by rw [hPv, hvN]; exact hB)
          rwa [hPv] at this
        rw [← card_primesOverFinset_eq_finrank hv0 hsplit]
        refine Finset.card_le_card fun P hP => ?_
        obtain ⟨hPp, hPv⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 _).mp hP
        have hunder : P.under (𝓞 K) = v := (P.over_def v).symm
        have hPN : absNorm P = p := (hsplit P hPp hunder).2.trans hvN
        have hP0 : P ≠ ⊥ := fun h0 => hp.ne_zero (by rw [← hPN, h0, Ideal.absNorm_bot])
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨mem_idealsLe.mpr ⟨hP0, hPN.le⟩, hPp, hPN⟩, hunder⟩
    _ = ((idealsLe M p).filter fun P => P.IsPrime ∧ absNorm P = p).card :=
        (Finset.card_eq_sum_card_fiberwise hmaps).symm

/-- **The degree-one Mertens sums**: `[M : K] · D_K(x) ≤ D_M(x) + [M : K] · D_K(B)`. -/
theorem finrank_mul_degreeOneMertens_le
    (h : ∀ P : Ideal (𝓞 M), P.IsPrime → P ≠ ⊥ → B < absNorm (P.under (𝓞 K)) →
      P.ramificationIdx (𝓞 K) = 1 ∧ absNorm P = absNorm (P.under (𝓞 K)))
    (N : ℕ) :
    (Module.finrank K M : ℝ) * degreeOneMertens K N ≤
      degreeOneMertens M N + Module.finrank K M * degreeOneMertens K B := by
  rw [degreeOneMertens, degreeOneMertens, degreeOneMertens]
  have hw : ∀ p : ℕ, 0 ≤ Real.log p / p := fun p =>
    div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  -- the primes `p ≤ B` are put aside, the others are compared termwise
  have hterm : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      (Module.finrank K M : ℝ) * ((degreeOneCount K p : ℝ) * (Real.log p / p)) ≤
        (degreeOneCount M p : ℝ) * (Real.log p / p) + Module.finrank K M *
          (if p ≤ B then (degreeOneCount K p : ℝ) * (Real.log p / p) else 0) := by
    intro p hp
    by_cases hB : p ≤ B
    · rw [if_pos hB]
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (degreeOneCount M p)) (hw p)
      linarith
    · rw [if_neg hB, mul_zero, add_zero, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (hw p)
      exact_mod_cast finrank_mul_degreeOneCount_le h (Finset.mem_filter.mp hp).2 (not_le.mp hB)
  have hsub : ∑ p ∈ (Icc 1 N).filter Nat.Prime,
      (if p ≤ B then (degreeOneCount K p : ℝ) * (Real.log p / p) else 0) ≤
        ∑ p ∈ (Icc 1 B).filter Nat.Prime, (degreeOneCount K p : ℝ) * (Real.log p / p) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
      fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (hw p)
    obtain ⟨hp1, hpB⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp2, hpp⟩ := Finset.mem_filter.mp hp1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp2).1, hpB⟩, hpp⟩
  calc (Module.finrank K M : ℝ) *
        ∑ p ∈ (Icc 1 N).filter Nat.Prime, (degreeOneCount K p : ℝ) * (Real.log p / p)
      = ∑ p ∈ (Icc 1 N).filter Nat.Prime,
          (Module.finrank K M : ℝ) * ((degreeOneCount K p : ℝ) * (Real.log p / p)) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, ((degreeOneCount M p : ℝ) * (Real.log p / p) +
          Module.finrank K M *
            (if p ≤ B then (degreeOneCount K p : ℝ) * (Real.log p / p) else 0)) :=
        Finset.sum_le_sum hterm
    _ = ∑ p ∈ (Icc 1 N).filter Nat.Prime, (degreeOneCount M p : ℝ) * (Real.log p / p) +
          Module.finrank K M * ∑ p ∈ (Icc 1 N).filter Nat.Prime,
            (if p ≤ B then (degreeOneCount K p : ℝ) * (Real.log p / p) else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _))

/-- **An extension in which almost all primes split completely is trivial.** -/
theorem finrank_eq_one_of_forall_split
    (h : ∀ P : Ideal (𝓞 M), P.IsPrime → P ≠ ⊥ → B < absNorm (P.under (𝓞 K)) →
      P.ramificationIdx (𝓞 K) = 1 ∧ absNorm P = absNorm (P.under (𝓞 K))) :
    Module.finrank K M = 1 := by
  have hpos : 0 < Module.finrank K M := Module.finrank_pos
  by_contra hne
  have h2 : (2 : ℝ) ≤ Module.finrank K M := by
    exact_mod_cast (by omega : 2 ≤ Module.finrank K M)
  obtain ⟨CK, hCK⟩ := exists_abs_degreeOneMertens_sub_log_le K
  obtain ⟨CM, hCM⟩ := exists_abs_degreeOneMertens_sub_log_le M
  -- `log N` is bounded
  have key : ∀ N : ℕ, 2 ≤ N → Real.log N ≤
      CM + Module.finrank K M * degreeOneMertens K B + Module.finrank K M * CK := by
    intro N hN
    have h1 := finrank_mul_degreeOneMertens_le h N
    have h3 := (abs_le.mp (hCK N hN)).1
    have h4 := (abs_le.mp (hCM N hN)).2
    have h5 : (Module.finrank K M : ℝ) * (Real.log N - CK) ≤
        Module.finrank K M * degreeOneMertens K N :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have h6 := mul_nonneg (sub_nonneg.mpr h2) (Real.log_natCast_nonneg N)
    linarith
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hNbig, hN2⟩ := ((hlog.eventually_gt_atTop
    (CM + Module.finrank K M * degreeOneMertens K B + Module.finrank K M * CK)).and
      (Filter.eventually_ge_atTop 2)).exists
  exact absurd (key N hN2) (not_le.mpr hNbig)

end GaloisForLFunctions
