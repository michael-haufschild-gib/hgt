import GaloisForLFunctions.RHTower.BilateralPrimeAngleModeration

/-!
# Finite-packet moderation and the exact Hardy–Stokes sewing at finite Euler gauge

Two layers of the bilateral prime-angle selector, both unconditional:

**The finite-packet dichotomy.**  For a nonempty finite packet `P` of primes, the multi-index
family `E ↦ Π_p λ_p(s)^(E_p)` has polynomial growth in `Σ_p |E_p|` iff `Re s = 1/2`: an
off-line character already fails on every one-prime axis, while on the line all coefficients
are unimodular.  This is the "no finite-packet loss" clause of the moderation selector.

**The exact Stokes cocycle of the two Hardy halves.**  For a character `λ ≠ 0`, the bilateral
eigenfamily `e ↦ λ^(-e)` of the sewing operator `c ↦ (e ↦ c(e-1) - λ c(e))` splits into the
positive Hardy half (supported on `e ≥ 0`) and the reflected negative half (supported on
`e < 0`).  Each half is annihilated by the sewing operator **except for an exactly opposite
boundary term** `∓ λ δ₀`: the transition/Stokes cocycle of the two chambers is exact, so no
divisor cohomology exists at finite gauge.  The regularity ledger is sharp:

* the positive half is moderate iff `‖λ‖ ≥ 1`;
* the negative half is moderate iff `‖λ‖ ≤ 1`;
* both halves sew inside moderate families iff `‖λ‖ = 1` iff (for `λ = λ_p(s)`)
  `Re s = 1/2`.

Off the line the two chiral halves exist in separate chambers and the only moderate bilateral
solution of the sewing equation is zero (the Koszul contraction of the parent module); on the
line both halves are moderate and the bilateral conormal survives.  This is the finite-gauge
half of the card's `(16)`: exact transition cocycle, no finite-packet divisor class.

No zeta value, zero datum, or positivity premise occurs anywhere.
-/

noncomputable section

open Complex

namespace RHTower

/-! ## The finite-packet dichotomy -/

/-- Polynomial growth of a finite-packet multi-index family in the total Fourier degree. -/
def packetModerate {P : Finset ℕ} (c : (↥P → ℤ) → ℂ) : Prop :=
  ∃ (C : ℝ) (m : ℕ), ∀ E : ↥P → ℤ,
    ‖c E‖ ≤ C * (1 + (∑ p : ↥P, ((E p).natAbs : ℝ))) ^ m

/-- The packet character family `E ↦ Π_p λ_p(s)^(E_p)`. -/
def bilateralPacketFamily (P : Finset ℕ) (s : ℂ) (E : ↥P → ℤ) : ℂ :=
  ∏ p : ↥P, bilateralHalfDensityCharacter (p : ℕ) s ^ (E p)

/-- The half-density character never vanishes. -/
theorem bilateralHalfDensityCharacter_ne_zero {p : ℕ} (hp : 0 < p) (s : ℂ) :
    bilateralHalfDensityCharacter p s ≠ 0 := by
  intro h
  have hn := norm_bilateralHalfDensityCharacter hp s
  rw [h, norm_zero] at hn
  exact absurd hn.symm
    (ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hp) _))

/-- On the critical line the packet family is unimodular, hence moderate. -/
theorem packetModerate_bilateralPacketFamily_of_re_eq_half {P : Finset ℕ}
    (hP : ∀ p ∈ P, 0 < p) {s : ℂ} (h : s.re = 1 / 2) :
    packetModerate (bilateralPacketFamily P s) := by
  refine ⟨1, 0, fun E => ?_⟩
  rw [pow_zero, mul_one, bilateralPacketFamily, norm_prod]
  have hone : ∀ p : ↥P,
      ‖bilateralHalfDensityCharacter (p : ℕ) s ^ (E p)‖ = 1 := by
    intro p
    rw [norm_zpow, norm_bilateralHalfDensityCharacter (hP p p.2), h,
      sub_self, Real.rpow_zero, one_zpow]
  rw [Finset.prod_congr rfl (fun p _ => hone p), Finset.prod_const_one]

/-- Off the critical line the packet family fails moderation already on one prime axis. -/
theorem not_packetModerate_bilateralPacketFamily_of_re_ne_half {P : Finset ℕ}
    {p₀ : ℕ} (hp₀ : p₀ ∈ P) (hp₂ : 2 ≤ p₀) {s : ℂ} (h : s.re ≠ 1 / 2) :
    ¬ packetModerate (bilateralPacketFamily P s) := by
  rintro ⟨C, m, hC⟩
  set a : ↥P := ⟨p₀, hp₀⟩ with ha
  -- the one-prime family is the axis restriction of the packet family
  have hax : ∀ e : ℤ,
      bilateralPacketFamily P s (fun q => if q = a then e else 0) =
        bilateralHalfDensityCharacter p₀ s ^ e := by
    intro e
    rw [bilateralPacketFamily]
    rw [Finset.prod_eq_single a (fun b _ hb => by
      simp [if_neg hb]) (fun hb => absurd (Finset.mem_univ a) hb)]
    simp [ha]
  have hsum : ∀ e : ℤ,
      (∑ q : ↥P, (((fun q => if q = a then e else 0) q).natAbs : ℝ)) =
        (e.natAbs : ℝ) := by
    intro e
    rw [Finset.sum_eq_single a (fun b _ hb => by
      simp [if_neg hb]) (fun hb => absurd (Finset.mem_univ a) hb)]
    simp
  -- so the one-prime jet family at grade zero is moderate — contradiction
  have hmod : bilateralModerate
      (fun e => bilateralHalfDensityCharacter p₀ s ^ e) := by
    refine ⟨C, m, fun e => ?_⟩
    have := hC (fun q => if q = a then e else 0)
    rw [hax e, hsum e] at this
    exact this
  have hjet : bilateralJetFamily p₀ s 0 =
      fun e => bilateralHalfDensityCharacter p₀ s ^ e := by
    funext e
    rw [bilateralJetFamily, pow_zero, one_mul]
  exact not_bilateralModerate_jetFamily_of_re_ne_half hp₂ 0 h
    (hjet ▸ hmod)

/-- **The finite-packet dichotomy** (card's `(10a)`): the packet family is moderate iff `s`
lies on the critical line. -/
theorem packetModerate_bilateralPacketFamily_iff {P : Finset ℕ} {p₀ : ℕ}
    (hp₀ : p₀ ∈ P) (hp₂ : 2 ≤ p₀) (hP : ∀ p ∈ P, 0 < p) (s : ℂ) :
    packetModerate (bilateralPacketFamily P s) ↔ s.re = 1 / 2 := by
  constructor
  · intro hmod
    by_contra hne
    exact not_packetModerate_bilateralPacketFamily_of_re_ne_half
      hp₀ hp₂ hne hmod
  · exact packetModerate_bilateralPacketFamily_of_re_eq_half hP

/-! ## The two Hardy halves and their exact Stokes cocycle -/

/-- The bilateral sewing operator `(z - λ)` in Fourier coordinates. -/
def bilateralSewing (lam : ℂ) (c : ℤ → ℂ) : ℤ → ℂ :=
  fun e => c (e - 1) - lam * c e

/-- The bilateral eigenfamily `e ↦ λ^(-e)`. -/
def bilateralEigenFamily (lam : ℂ) : ℤ → ℂ := fun e => lam ^ (-e)

/-- The completed positive Hardy half. -/
def hardyPositiveHalf (lam : ℂ) : ℤ → ℂ :=
  fun e => if 0 ≤ e then lam ^ (-e) else 0

/-- The reflected negative Hardy half. -/
def hardyNegativeHalf (lam : ℂ) : ℤ → ℂ :=
  fun e => if e < 0 then lam ^ (-e) else 0

/-- The two chiral halves reassemble the bilateral eigenfamily. -/
theorem hardyPositiveHalf_add_hardyNegativeHalf (lam : ℂ) :
    hardyPositiveHalf lam + hardyNegativeHalf lam =
      bilateralEigenFamily lam := by
  funext e
  simp only [Pi.add_apply, hardyPositiveHalf, hardyNegativeHalf,
    bilateralEigenFamily]
  by_cases h : (0 : ℤ) ≤ e
  · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
  · rw [if_neg h, if_pos (not_le.mp h), zero_add]

/-- The bilateral eigenfamily is annihilated by the sewing operator. -/
theorem bilateralSewing_eigenFamily {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralSewing lam (bilateralEigenFamily lam) = 0 := by
  funext e
  simp only [bilateralSewing, bilateralEigenFamily, Pi.zero_apply]
  have hstep : lam ^ (-(e - 1)) = lam * lam ^ (-e) := by
    rw [show -(e - 1) = 1 + -e by ring, zpow_add₀ hlam, zpow_one]
  rw [hstep]
  ring

/-- **The Stokes boundary term of the positive half**: the sewing operator kills it except for
`-λ` concentrated at the origin. -/
theorem bilateralSewing_hardyPositiveHalf {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralSewing lam (hardyPositiveHalf lam) =
      fun e => if e = 0 then -lam else 0 := by
  funext e
  simp only [bilateralSewing, hardyPositiveHalf]
  by_cases h1 : 1 ≤ e
  · rw [if_pos (by omega : (0 : ℤ) ≤ e - 1), if_pos (by omega : (0 : ℤ) ≤ e),
      if_neg (by omega : ¬ e = 0)]
    have hstep : lam ^ (-(e - 1)) = lam * lam ^ (-e) := by
      rw [show -(e - 1) = 1 + -e by ring, zpow_add₀ hlam, zpow_one]
    rw [hstep]
    ring
  · by_cases h0 : e = 0
    · subst h0
      rw [if_neg (by omega : ¬ (0 : ℤ) ≤ 0 - 1), if_pos le_rfl, if_pos rfl,
        neg_zero, zpow_zero]
      ring
    · rw [if_neg (by omega : ¬ (0 : ℤ) ≤ e - 1),
        if_neg (by omega : ¬ (0 : ℤ) ≤ e), if_neg h0]
      ring

/-- **The Stokes boundary term of the negative half**: exactly opposite, `+λ` at the origin.
The transition cocycle of the two chambers is exact — no divisor class at finite gauge. -/
theorem bilateralSewing_hardyNegativeHalf {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralSewing lam (hardyNegativeHalf lam) =
      fun e => if e = 0 then lam else 0 := by
  funext e
  simp only [bilateralSewing, hardyNegativeHalf]
  by_cases h0 : e = 0
  · subst h0
    rw [if_pos (by omega : (0 : ℤ) - 1 < 0), if_neg (by omega : ¬ (0 : ℤ) < 0),
      if_pos rfl, mul_zero, sub_zero]
    rw [show -((0 : ℤ) - 1) = 1 by ring, zpow_one]
  · by_cases hneg : e < 0
    · rw [if_pos (by omega : e - 1 < 0), if_pos hneg, if_neg h0]
      have hstep : lam ^ (-(e - 1)) = lam * lam ^ (-e) := by
        rw [show -(e - 1) = 1 + -e by ring, zpow_add₀ hlam, zpow_one]
      rw [hstep]
      ring
    · rw [if_neg (by omega : ¬ e - 1 < 0), if_neg hneg, if_neg h0]
      ring

/-- The two Stokes boundary terms cancel exactly. -/
theorem bilateralSewing_halves_cancel {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralSewing lam (hardyPositiveHalf lam) +
      bilateralSewing lam (hardyNegativeHalf lam) = 0 := by
  rw [bilateralSewing_hardyPositiveHalf hlam,
    bilateralSewing_hardyNegativeHalf hlam]
  funext e
  by_cases h : e = 0 <;> simp [h]

/-- The positive Hardy half is moderate iff the character modulus is at least one. -/
theorem bilateralModerate_hardyPositiveHalf_iff {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralModerate (hardyPositiveHalf lam) ↔ 1 ≤ ‖lam‖ := by
  have h0 : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  constructor
  · intro hmod
    by_contra hlt
    rw [not_le] at hlt
    have hrinv : 1 < ‖lam‖⁻¹ := (one_lt_inv₀ h0).mpr hlt
    refine not_bilateralModerate_of_growth hrinv (Or.inl rfl) ?_ hmod
    intro n hn1
    simp only [hardyPositiveHalf, one_mul]
    rw [if_pos (Int.natCast_nonneg n), norm_zpow, zpow_neg, zpow_natCast,
      inv_pow]
  · intro hone
    refine ⟨1, 0, fun e => ?_⟩
    rw [pow_zero, mul_one]
    by_cases h : (0 : ℤ) ≤ e
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, ((n : ℤ)) = e := ⟨e.toNat, Int.toNat_of_nonneg h⟩
      simp only [hardyPositiveHalf]
      rw [if_pos h, norm_zpow, zpow_neg, zpow_natCast]
      exact (inv_le_one₀ (pow_pos h0 n)).mpr (one_le_pow₀ hone)
    · simp only [hardyPositiveHalf]
      rw [if_neg h, norm_zero]
      norm_num

/-- The reflected negative Hardy half is moderate iff the character modulus is at most one. -/
theorem bilateralModerate_hardyNegativeHalf_iff {lam : ℂ} (hlam : lam ≠ 0) :
    bilateralModerate (hardyNegativeHalf lam) ↔ ‖lam‖ ≤ 1 := by
  have h0 : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  constructor
  · intro hmod
    by_contra hgt
    rw [not_le] at hgt
    refine not_bilateralModerate_of_growth hgt (Or.inr rfl) ?_ hmod
    intro n hn1
    simp only [hardyNegativeHalf, neg_one_mul]
    have hneg : (-(n : ℤ)) < 0 := by
      have hn0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn1
      omega
    rw [if_pos hneg, norm_zpow, neg_neg, zpow_natCast]
  · intro hone
    refine ⟨1, 0, fun e => ?_⟩
    rw [pow_zero, mul_one]
    by_cases h : e < 0
    · have hpos : (0 : ℤ) ≤ -e := by omega
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ((n : ℤ)) = -e := ⟨(-e).toNat,
        Int.toNat_of_nonneg hpos⟩
      simp only [hardyNegativeHalf]
      rw [if_pos h, norm_zpow, ← hn, zpow_natCast]
      exact pow_le_one₀ (le_of_lt h0) hone
    · simp only [hardyNegativeHalf]
      rw [if_neg h, norm_zero]
      norm_num

/-- **The sewing criterion**: both chiral Hardy halves are moderate iff the character is
unitary. -/
theorem hardyHalves_both_moderate_iff {lam : ℂ} (hlam : lam ≠ 0) :
    (bilateralModerate (hardyPositiveHalf lam) ∧
      bilateralModerate (hardyNegativeHalf lam)) ↔ ‖lam‖ = 1 := by
  rw [bilateralModerate_hardyPositiveHalf_iff hlam,
    bilateralModerate_hardyNegativeHalf_iff hlam]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h2 h1
  · intro h
    rw [h]
    exact ⟨le_rfl, le_rfl⟩

/-- **The finite-gauge sewing theorem for the prime half-density character** (card's `(16)`,
finite level): the two chiral Hardy halves of the FE-sewn bilateral boundary value sew inside
moderate families exactly on the critical line. -/
theorem hardyHalves_both_moderate_iff_re_eq_half {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    (bilateralModerate (hardyPositiveHalf (bilateralHalfDensityCharacter p s)) ∧
      bilateralModerate
        (hardyNegativeHalf (bilateralHalfDensityCharacter p s))) ↔
      s.re = 1 / 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le two_pos hp
  rw [hardyHalves_both_moderate_iff (bilateralHalfDensityCharacter_ne_zero hp0 s)]
  exact norm_bilateralHalfDensityCharacter_eq_one_iff hp s

end RHTower
