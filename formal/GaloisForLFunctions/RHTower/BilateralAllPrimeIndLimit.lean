import GaloisForLFunctions.RHTower.BilateralPrimeAnglePacketSewing

/-!
# The strict all-prime Ind-limit: rigidity of moderate simultaneous sewing solutions

The finite-gauge layer is exact (packet dichotomy, exact Stokes cocycle).  This file passes to
the strict countable-prime Ind-limit: bilateral families over **finitely supported**
multi-indices `E : ℕ →₀ ℤ` — the Fourier lattice of the full prime-angle torus — with
polynomial growth measured in the total degree `Σ_p |E_p|`.

Results, all unconditional:

* `allPrimeModerate_conormalFamily_iff` — the canonical all-prime conormal family
  `E ↦ Π_p λ_p(s)^(-E_p)` is moderate iff `Re s = 1/2`.  Off the line moderation already
  fails on the single axis `p = 2`; on the line every coefficient has modulus at most one.
  The moderation selector suffers **no countable-product loss**.
* `allPrimeSewing_single_step` and `allPrimeSewing_rigidity` — **Ind-limit rigidity**: any
  family satisfying the sewing recursion at every prime is determined on prime-supported
  multi-indices by its value at the origin, as that value times the canonical conormal
  family.  The simultaneous solution space of the strict all-prime gauge is one-dimensional.
* `re_eq_half_of_allPrime_moderate_sewing` — **the strict all-prime selector**: a moderate
  simultaneous sewing solution with nonzero origin value forces `Re s = 1/2`.

Together with the finite layers this closes the card's "pass to the strict countable-prime
Ind-limit" gate: the limit neither loses the selector nor creates spurious solutions — the
first possible nonzero class beyond this rigid moderate layer must come from the enhanced
(non-moderate) sector, which is where the card's open arithmetic sewing conjecture lives.

No zeta value, zero datum, or positivity premise occurs anywhere.
-/

noncomputable section

open Complex

namespace RHTower

/-- Total Fourier degree of a finitely supported multi-index. -/
def allPrimeDegree (E : ℕ →₀ ℤ) : ℕ :=
  E.sum fun _ e => e.natAbs

/-- Polynomial growth of an all-prime multi-index family in the total degree. -/
def allPrimeModerate (c : (ℕ →₀ ℤ) → ℂ) : Prop :=
  ∃ (C : ℝ) (m : ℕ), ∀ E : ℕ →₀ ℤ,
    ‖c E‖ ≤ C * (1 + (allPrimeDegree E : ℝ)) ^ m

/-- The canonical all-prime conormal family `E ↦ Π_p λ_p(s)^(-E_p)`: the Ind-limit bilateral
eigenfamily of the simultaneous sewing recursion. -/
def allPrimeConormalFamily (s : ℂ) (E : ℕ →₀ ℤ) : ℂ :=
  E.prod fun p e => bilateralHalfDensityCharacter p s ^ (-e)

/-- Moderation is invariant under Fourier reflection. -/
theorem bilateralModerate_comp_neg {c : ℤ → ℂ} :
    bilateralModerate (fun e => c (-e)) ↔ bilateralModerate c := by
  constructor
  · rintro ⟨C, m, hC⟩
    refine ⟨C, m, fun e => ?_⟩
    have := hC (-e)
    simpa using this
  · rintro ⟨C, m, hC⟩
    refine ⟨C, m, fun e => ?_⟩
    have := hC (-e)
    simpa using this

/-- Every character power has modulus at most one on the critical line — including the junk
indices `p = 0, 1`, so the bound needs no support hypothesis. -/
theorem norm_char_zpow_le_one_of_re_eq_half (p : ℕ) {s : ℂ}
    (h : s.re = 1 / 2) (e : ℤ) :
    ‖bilateralHalfDensityCharacter p s ^ e‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst hp0
    rw [bilateralHalfDensityCharacter]
    by_cases hw : (((1 / 2 : ℝ) : ℂ) - s) = 0
    · rw [hw, Complex.cpow_zero, one_zpow, norm_one]
    · rw [show ((0 : ℕ) : ℂ) = 0 by norm_num, Complex.zero_cpow hw]
      rcases eq_or_ne e 0 with he | he
      · rw [he, zpow_zero, norm_one]
      · rw [zero_zpow e he, norm_zero]
        norm_num
  · rw [norm_zpow, norm_bilateralHalfDensityCharacter hp, h, sub_self,
      Real.rpow_zero, one_zpow]

/-- On the critical line the all-prime conormal family is bounded, hence moderate. -/
theorem allPrimeModerate_conormalFamily_of_re_eq_half {s : ℂ}
    (h : s.re = 1 / 2) :
    allPrimeModerate (allPrimeConormalFamily s) := by
  refine ⟨1, 0, fun E => ?_⟩
  rw [pow_zero, mul_one, allPrimeConormalFamily, Finsupp.prod, norm_prod]
  exact Finset.prod_le_one (fun q _ => norm_nonneg _)
    (fun q _ => norm_char_zpow_le_one_of_re_eq_half q h (-(E q)))

/-- Off the critical line the all-prime conormal family fails moderation on the `p = 2`
axis. -/
theorem not_allPrimeModerate_conormalFamily_of_re_ne_half {s : ℂ}
    (h : s.re ≠ 1 / 2) :
    ¬ allPrimeModerate (allPrimeConormalFamily s) := by
  rintro ⟨C, m, hC⟩
  have hmod2 : bilateralModerate
      (fun e : ℤ => bilateralHalfDensityCharacter 2 s ^ (-e)) := by
    refine ⟨C, m, fun e => ?_⟩
    have h1 := hC (Finsupp.single 2 e)
    rw [allPrimeConormalFamily,
      Finsupp.prod_single_index (by rw [neg_zero, zpow_zero])] at h1
    have hdeg : allPrimeDegree (Finsupp.single 2 e) = e.natAbs := by
      rw [allPrimeDegree, Finsupp.sum_single_index]
      rfl
    rw [hdeg] at h1
    exact h1
  have hmod2' : bilateralModerate
      (fun e : ℤ => bilateralHalfDensityCharacter 2 s ^ e) :=
    bilateralModerate_comp_neg.mp hmod2
  have hjet : bilateralJetFamily 2 s 0 =
      fun e : ℤ => bilateralHalfDensityCharacter 2 s ^ e := by
    funext e
    rw [bilateralJetFamily, pow_zero, one_mul]
  exact not_bilateralModerate_jetFamily_of_re_ne_half (le_refl 2) 0 h
    (hjet ▸ hmod2')

/-- **The all-prime moderation dichotomy**: the strict countable-prime conormal family is
moderate iff `s` lies on the critical line — no countable-product loss. -/
theorem allPrimeModerate_conormalFamily_iff (s : ℂ) :
    allPrimeModerate (allPrimeConormalFamily s) ↔ s.re = 1 / 2 := by
  constructor
  · intro hmod
    by_contra hne
    exact not_allPrimeModerate_conormalFamily_of_re_ne_half hne hmod
  · exact allPrimeModerate_conormalFamily_of_re_eq_half

/-- Transport of a simultaneous sewing solution along one coordinate: the recursion moves any
single Fourier coordinate to the base at the exact cost `λ_p^(-n)`. -/
theorem allPrimeSewing_single_step {s : ℂ} {c : (ℕ →₀ ℤ) → ℂ}
    (hsew : ∀ (p : ℕ), 2 ≤ p → ∀ E : ℕ →₀ ℤ,
      c (E - Finsupp.single p 1) = bilateralHalfDensityCharacter p s * c E)
    {p : ℕ} (hp : 2 ≤ p) (F : ℕ →₀ ℤ) (n : ℤ) :
    c (F + Finsupp.single p n) =
      bilateralHalfDensityCharacter p s ^ (-n) * c F := by
  have hp0 : 0 < p := lt_of_lt_of_le two_pos hp
  have hchar : bilateralHalfDensityCharacter p s ≠ 0 :=
    bilateralHalfDensityCharacter_ne_zero hp0 s
  induction n using Int.induction_on with
  | zero =>
      rw [Finsupp.single_zero, add_zero, neg_zero, zpow_zero, one_mul]
  | succ k ih =>
      have hidx : F + Finsupp.single p ((k : ℤ) + 1) - Finsupp.single p 1 =
          F + Finsupp.single p (k : ℤ) := by
        rw [add_sub_assoc, ← Finsupp.single_sub]
        norm_num
      have h := hsew p hp (F + Finsupp.single p ((k : ℤ) + 1))
      rw [hidx, ih] at h
      have hsolve : c (F + Finsupp.single p ((k : ℤ) + 1)) =
          (bilateralHalfDensityCharacter p s)⁻¹ *
            (bilateralHalfDensityCharacter p s ^ (-(k : ℤ)) * c F) := by
        apply mul_left_cancel₀ hchar
        rw [← h, mul_inv_cancel_left₀ hchar]
      rw [hsolve, show -((k : ℤ) + 1) = -(k : ℤ) - 1 by ring,
        zpow_sub_one₀ hchar]
      ring
  | pred k ih =>
      have hidx : F + Finsupp.single p (-(k : ℤ)) - Finsupp.single p 1 =
          F + Finsupp.single p (-(k : ℤ) - 1) := by
        rw [add_sub_assoc, ← Finsupp.single_sub]
      have h := hsew p hp (F + Finsupp.single p (-(k : ℤ)))
      rw [hidx, ih] at h
      rw [h, show -(-(k : ℤ) - 1) = (k : ℤ) + 1 by ring,
        show -(-(k : ℤ)) = (k : ℤ) by ring, zpow_add_one₀ hchar]
      ring

/-- **Ind-limit rigidity**: a simultaneous sewing solution is determined on prime-supported
multi-indices by its origin value, as that value times the canonical conormal family.  The
strict all-prime moderate solution space is one-dimensional. -/
theorem allPrimeSewing_rigidity {s : ℂ} {c : (ℕ →₀ ℤ) → ℂ}
    (hsew : ∀ (p : ℕ), 2 ≤ p → ∀ E : ℕ →₀ ℤ,
      c (E - Finsupp.single p 1) = bilateralHalfDensityCharacter p s * c E)
    (E : ℕ →₀ ℤ) (hE : ∀ p ∈ E.support, 2 ≤ p) :
    c E = allPrimeConormalFamily s E * c 0 := by
  suffices h : ∀ (n : ℕ) (E : ℕ →₀ ℤ), E.support.card = n →
      (∀ p ∈ E.support, 2 ≤ p) →
      c E = allPrimeConormalFamily s E * c 0 from h _ E rfl hE
  intro n
  induction n with
  | zero =>
      intro E hcard hE'
      have hzero : E = 0 :=
        Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp hcard)
      subst hzero
      rw [allPrimeConormalFamily, Finsupp.prod_zero_index, one_mul]
  | succ n ih =>
      intro E hcard hE'
      have hne : E.support.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨p, hp⟩ := hne
      have hp2 : 2 ≤ p := hE' p hp
      have hdec : Finsupp.erase p E + Finsupp.single p (E p) = E := by
        rw [add_comm]
        exact Finsupp.single_add_erase p E
      have hstep := allPrimeSewing_single_step hsew hp2
        (Finsupp.erase p E) (E p)
      rw [hdec] at hstep
      have hcard' : (Finsupp.erase p E).support.card = n := by
        rw [Finsupp.support_erase, Finset.card_erase_of_mem hp, hcard]
        omega
      have hprime' : ∀ q ∈ (Finsupp.erase p E).support, 2 ≤ q := by
        intro q hq
        rw [Finsupp.support_erase] at hq
        exact hE' q (Finset.mem_of_mem_erase hq)
      rw [hstep, ih _ hcard' hprime']
      have hconormal : allPrimeConormalFamily s E =
          bilateralHalfDensityCharacter p s ^ (-(E p)) *
            allPrimeConormalFamily s (Finsupp.erase p E) := by
        rw [allPrimeConormalFamily, allPrimeConormalFamily, Finsupp.prod,
          Finsupp.prod]
        rw [← Finset.mul_prod_erase E.support
          (fun q => bilateralHalfDensityCharacter q s ^ (-(E q))) hp]
        congr 1
        rw [Finsupp.support_erase]
        apply Finset.prod_congr rfl
        intro q hq
        rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hq)]
      rw [hconormal]
      ring

/-- **The strict all-prime selector**: a moderate simultaneous sewing solution with nonzero
origin value forces `Re s = 1/2`.  The countable-prime Ind-limit neither loses the selector
nor admits spurious moderate solutions. -/
theorem re_eq_half_of_allPrime_moderate_sewing {s : ℂ} {c : (ℕ →₀ ℤ) → ℂ}
    (hc0 : c 0 ≠ 0) (hmod : allPrimeModerate c)
    (hsew : ∀ (p : ℕ), 2 ≤ p → ∀ E : ℕ →₀ ℤ,
      c (E - Finsupp.single p 1) = bilateralHalfDensityCharacter p s * c E) :
    s.re = 1 / 2 := by
  by_contra hne
  have hc0pos : 0 < ‖c 0‖ := norm_pos_iff.mpr hc0
  have hax : ∀ e : ℤ, c (Finsupp.single 2 e) =
      bilateralHalfDensityCharacter 2 s ^ (-e) * c 0 := by
    intro e
    have h := allPrimeSewing_single_step hsew (le_refl 2) 0 e
    rwa [zero_add] at h
  obtain ⟨C, m, hC⟩ := hmod
  have hmod2 : bilateralModerate
      (fun e : ℤ => bilateralHalfDensityCharacter 2 s ^ (-e)) := by
    refine ⟨C / ‖c 0‖, m, fun e => ?_⟩
    have h1 := hC (Finsupp.single 2 e)
    rw [hax e, norm_mul] at h1
    have hdeg : allPrimeDegree (Finsupp.single 2 e) = e.natAbs := by
      rw [allPrimeDegree, Finsupp.sum_single_index]
      rfl
    rw [hdeg] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0pos]
    exact h1
  have hmod2' : bilateralModerate
      (fun e : ℤ => bilateralHalfDensityCharacter 2 s ^ e) :=
    bilateralModerate_comp_neg.mp hmod2
  have hjet : bilateralJetFamily 2 s 0 =
      fun e : ℤ => bilateralHalfDensityCharacter 2 s ^ e := by
    funext e
    rw [bilateralJetFamily, pow_zero, one_mul]
  exact not_bilateralModerate_jetFamily_of_re_ne_half (le_refl 2) 0 hne
    (hjet ▸ hmod2')

end RHTower
