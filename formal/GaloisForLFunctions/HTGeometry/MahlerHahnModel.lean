import GaloisForLFunctions.HTGeometry.HahnDilation
import GaloisForLFunctions.HTGeometry.TwistedRatFuncLaurent
import GaloisForLFunctions.HTGeometry.RamifiedLaurentTransfer

/-!
# The Mahler operator on Hahn series with rational exponents

Substituting `w ↦ w^p` stretches exponents by `p`.  On Hahn series with rational exponents this is
a ring automorphism, and — unlike a dilation, which acts diagonally — it has no eigenvectors: a
series fixed by it would have a support closed under multiplication by `p` in both directions, and
any nonzero exponent then produces an infinite strictly decreasing chain in the support, which a
Hahn support cannot contain.

This is the ambient in which a Mahler equation `y(w) - c y(w^p) = r(w)` is analysed.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

noncomputable section

variable {k : Type*} [Field k]

/-- Stretching rational exponents by a positive natural number. -/
def qStretchHom (p : ℕ) : ℚ →+ ℚ := AddMonoidHom.mulLeft (p : ℚ)

@[simp]
theorem qStretchHom_apply (p : ℕ) (γ : ℚ) : qStretchHom p γ = (p : ℚ) * γ := rfl

theorem qStretchHom_injective {p : ℕ} (hp : 0 < p) : Function.Injective (qStretchHom p) := by
  intro γ δ h
  rw [qStretchHom_apply, qStretchHom_apply] at h
  exact mul_left_cancel₀ (by exact_mod_cast hp.ne') h

theorem qStretchHom_le_iff {p : ℕ} (hp : 0 < p) (γ δ : ℚ) :
    qStretchHom p γ ≤ qStretchHom p δ ↔ γ ≤ δ := by
  rw [qStretchHom_apply, qStretchHom_apply]
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hpQ
  · intro h
    exact mul_le_mul_of_nonneg_left h (le_of_lt hpQ)

/-- The Mahler operator `y(w) ↦ y(w^p)` on Hahn series with rational exponents. -/
def mahlerHom (p : ℕ) (hp : 0 < p) : HahnSeries ℚ k →+* HahnSeries ℚ k :=
  HahnSeries.embDomainRingHom (qStretchHom p) (qStretchHom_injective hp) (qStretchHom_le_iff hp)

@[simp]
theorem coeff_mahlerHom_mul (p : ℕ) (hp : 0 < p) (f : HahnSeries ℚ k) (γ : ℚ) :
    (mahlerHom p hp f).coeff ((p : ℚ) * γ) = f.coeff γ := by
  have := HahnSeries.embDomain_coeff (f := ⟨⟨qStretchHom p, qStretchHom_injective hp⟩,
    qStretchHom_le_iff hp _ _⟩) (x := f) (a := γ)
  simpa [mahlerHom] using this

theorem coeff_mahlerHom (p : ℕ) (hp : 1 < p) (f : HahnSeries ℚ k) (γ : ℚ) :
    (mahlerHom p (by omega) f).coeff γ = f.coeff (γ / (p : ℚ)) := by
  have hpQ : ((p : ℚ)) ≠ 0 := by
    have : 0 < p := by omega
    exact_mod_cast this.ne'
  have := coeff_mahlerHom_mul p (by omega : 0 < p) f (γ / (p : ℚ))
  rwa [mul_div_cancel₀ _ hpQ] at this

/-- **The Mahler operator has no nonconstant fixed series.**  A fixed series has a support stable
under multiplication by `p` in both directions, and a nonzero exponent then generates an infinite
strictly decreasing chain in the support. -/
theorem eq_C_of_mahlerHom_eq_self {p : ℕ} (hp : 1 < p) {f : HahnSeries ℚ k}
    (hf : mahlerHom p (by omega) f = f) : f = HahnSeries.C (f.coeff 0) := by
  have hpQ : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hp0 : (0 : ℚ) < (p : ℚ) := lt_trans zero_lt_one hpQ
  have hstep : ∀ γ : ℚ, f.coeff (γ / (p : ℚ)) = f.coeff γ := by
    intro γ
    have := congrArg (fun x : HahnSeries ℚ k => x.coeff γ) hf
    rw [coeff_mahlerHom p hp] at this
    exact this
  have hiter : ∀ (γ : ℚ) (n : ℕ), f.coeff (γ / (p : ℚ) ^ n) = f.coeff γ := by
    intro γ n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← div_div, hstep, ih]
  refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
  by_cases hγ : γ = 0
  · subst hγ
    simp [HahnSeries.C_apply]
  · have hzero : f.coeff γ = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hγ with hneg | hpos
      · have hmem : ∀ n : ℕ, γ * (p : ℚ) ^ n ∈ f.support := by
          intro n
          have hppos : (0 : ℚ) < (p : ℚ) ^ n := pow_pos hp0 n
          have hco : f.coeff (γ * (p : ℚ) ^ n) = f.coeff γ := by
            have h := hiter (γ * (p : ℚ) ^ n) n
            rw [mul_div_assoc, div_self (ne_of_gt hppos), mul_one] at h
            exact h.symm
          rw [HahnSeries.mem_support, hco]
          exact hne
        have hanti : StrictAnti (fun n : ℕ => γ * (p : ℚ) ^ n) := by
          refine strictAnti_nat_of_succ_lt fun n => ?_
          have hppos : (0 : ℚ) < (p : ℚ) ^ n := pow_pos hp0 n
          have hlt : γ * (p : ℚ) ^ n < 0 := mul_neg_of_neg_of_pos hneg hppos
          calc γ * (p : ℚ) ^ (n + 1) = (γ * (p : ℚ) ^ n) * (p : ℚ) := by ring
            _ < (γ * (p : ℚ) ^ n) * 1 := mul_lt_mul_of_neg_left hpQ hlt
            _ = γ * (p : ℚ) ^ n := by ring
        exact (Set.isWF_iff_no_descending_seq.mp f.isWF_support _ hanti) hmem
      · have hmem : ∀ n : ℕ, γ / (p : ℚ) ^ n ∈ f.support := by
          intro n
          rw [HahnSeries.mem_support, hiter γ n]
          exact hne
        have hanti : StrictAnti (fun n : ℕ => γ / (p : ℚ) ^ n) := by
          refine strictAnti_nat_of_succ_lt fun n => ?_
          have hppos : (0 : ℚ) < (p : ℚ) ^ n := pow_pos hp0 n
          have hnum : 0 < γ / (p : ℚ) ^ n := div_pos hpos hppos
          calc γ / (p : ℚ) ^ (n + 1) = (γ / (p : ℚ) ^ n) / (p : ℚ) := by
                rw [pow_succ, ← div_div]
            _ < γ / (p : ℚ) ^ n := by
                rw [div_lt_iff₀ hp0]
                nlinarith
        exact (Set.isWF_iff_no_descending_seq.mp f.isWF_support _ hanti) hmem
    simp [hzero, HahnSeries.C_apply, hγ]

/-- **The Mahler operator has no eigenvectors with eigenvalue other than one.**  The same support
argument: an eigenvector with a nonzero exponent generates an infinite strictly decreasing chain. -/
theorem eq_zero_of_mahlerHom_eq_smul {p : ℕ} (hp : 1 < p) {lam : k} (hlam : lam ≠ 1)
    {f : HahnSeries ℚ k} (hf : mahlerHom p (by omega) f = HahnSeries.C lam * f) : f = 0 := by
  have hpQ : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hp0 : (0 : ℚ) < (p : ℚ) := lt_trans zero_lt_one hpQ
  have hstep : ∀ γ : ℚ, f.coeff (γ / (p : ℚ)) = lam * f.coeff γ := by
    intro γ
    have h := congrArg (fun x : HahnSeries ℚ k => x.coeff γ) hf
    rw [coeff_mahlerHom p hp, coeff_C_mul_hahn] at h
    exact h
  by_cases hlam0 : lam = 0
  · refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
    have := hstep ((p : ℚ) * γ)
    rw [mul_div_cancel_left₀ _ (ne_of_gt hp0), hlam0, zero_mul] at this
    simpa using this
  · have hiter : ∀ (γ : ℚ) (n : ℕ), f.coeff (γ / (p : ℚ) ^ n) = lam ^ n * f.coeff γ := by
      intro γ n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, ← div_div, hstep, ih, pow_succ]
          ring
    refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
    by_cases hγ : γ = 0
    · subst hγ
      have h0 := hstep 0
      rw [zero_div] at h0
      have hz : (1 - lam) * f.coeff 0 = 0 := by
        rw [sub_mul, one_mul, ← h0, sub_self]
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd (sub_eq_zero.mp h).symm hlam
      · simpa using h
    · have hzero : f.coeff γ = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hγ with hneg | hpos
        · have hmem : ∀ n : ℕ, γ * (p : ℚ) ^ n ∈ f.support := by
            intro n
            have hppos : (0 : ℚ) < (p : ℚ) ^ n := pow_pos hp0 n
            have h := hiter (γ * (p : ℚ) ^ n) n
            rw [mul_div_assoc, div_self (ne_of_gt hppos), mul_one] at h
            rw [HahnSeries.mem_support]
            intro hzero
            rw [hzero, mul_zero] at h
            exact hne h
          have hanti : StrictAnti (fun n : ℕ => γ * (p : ℚ) ^ n) := by
            refine strictAnti_nat_of_succ_lt fun n => ?_
            have hppos : (0 : ℚ) < (p : ℚ) ^ n := pow_pos hp0 n
            have hlt : γ * (p : ℚ) ^ n < 0 := mul_neg_of_neg_of_pos hneg hppos
            calc γ * (p : ℚ) ^ (n + 1) = (γ * (p : ℚ) ^ n) * (p : ℚ) := by ring
              _ < (γ * (p : ℚ) ^ n) * 1 := mul_lt_mul_of_neg_left hpQ hlt
              _ = γ * (p : ℚ) ^ n := by ring
          exact (Set.isWF_iff_no_descending_seq.mp f.isWF_support _ hanti) hmem
        · have hmem : ∀ n : ℕ, γ / (p : ℚ) ^ n ∈ f.support := by
            intro n
            rw [HahnSeries.mem_support, hiter γ n]
            exact mul_ne_zero (pow_ne_zero n hlam0) hne
          have hanti : StrictAnti (fun n : ℕ => γ / (p : ℚ) ^ n) := by
            refine strictAnti_nat_of_succ_lt fun n => ?_
            have hppos : (0 : ℚ) < (p : ℚ) ^ n := pow_pos hp0 n
            have hnum : 0 < γ / (p : ℚ) ^ n := div_pos hpos hppos
            calc γ / (p : ℚ) ^ (n + 1) = (γ / (p : ℚ) ^ n) / (p : ℚ) := by
                  rw [pow_succ, ← div_div]
              _ < γ / (p : ℚ) ^ n := by
                  rw [div_lt_iff₀ hp0]
                  nlinarith
          exact (Set.isWF_iff_no_descending_seq.mp f.isWF_support _ hanti) hmem
      simpa using hzero

/-! ## The two-variable Mahler ambient -/

/-- The ambient field of a Mahler equation: Laurent series in the twisting coordinate `h` over
Hahn series in `w` with rational exponents. -/
abbrev MahlerAmbient (k : Type*) [Field k] := HahnSeries ℤ (HahnSeries ℚ k)

theorem C_inv_natCast_ne_zero [CharZero k] {p : ℕ} (hp : 1 < p) :
    (HahnSeries.C (((p : k))⁻¹) : HahnSeries ℚ k) ≠ 0 := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  intro h
  have := congrArg (fun x : HahnSeries ℚ k => x.coeff 0) h
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at this
  exact inv_ne_zero hpk this

/-- The Mahler substitution together with the twisting coordinate: `w ↦ w^p`, `h ↦ p⁻¹ h`. -/
def mahlerDilation [CharZero k] (p : ℕ) (hp : 1 < p) : MahlerAmbient k →+* MahlerAmbient k :=
  hahnTwistHom (mahlerHom p (by omega))
    (laurentChar (HahnSeries.C (((p : k))⁻¹) : HahnSeries ℚ k) (C_inv_natCast_ne_zero hp))

@[simp]
theorem coeff_mahlerDilation [CharZero k] (p : ℕ) (hp : 1 < p) (f : MahlerAmbient k) (n : ℤ) :
    (mahlerDilation p hp f).coeff n
      = (HahnSeries.C (((p : k))⁻¹) : HahnSeries ℚ k) ^ n * mahlerHom p (by omega) (f.coeff n) := by
  simp [mahlerDilation]

theorem natCast_zpow_ne_one [CharZero k] {p : ℕ} (hp : 1 < p) {n : ℤ} (hn : n ≠ 0) :
    ((p : k)) ^ n ≠ 1 := by
  have hpQ : ((p : ℚ)) ^ n ≠ 1 := by
    have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp
    intro h
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · have : ((p : ℚ)) ^ n < 1 := by
        refine zpow_lt_one_of_neg₀ hp1 hneg
      exact absurd h (ne_of_lt this)
    · have : (1 : ℚ) < ((p : ℚ)) ^ n := one_lt_zpow₀ hp1 hpos
      exact absurd h (ne_of_gt this)
  intro h
  refine hpQ ?_
  have hcast : (((((p : ℚ)) ^ n : ℚ)) : k) = ((1 : ℚ) : k) := by
    push_cast
    exact h
  exact_mod_cast hcast

/-- **The invariants of the two-variable Mahler ambient are the constants.** -/
theorem exists_C_C_of_mahlerDilation_eq_self [CharZero k] {p : ℕ} (hp : 1 < p)
    {f : MahlerAmbient k} (hf : mahlerDilation p hp f = f) :
    ∃ c : k, f = HahnSeries.C (HahnSeries.C c) := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  have hcoeff : ∀ n : ℤ, mahlerHom p (by omega : 0 < p) (f.coeff n)
      = HahnSeries.C (((p : k)) ^ n) * f.coeff n := by
    intro n
    have h := congrArg (fun x : MahlerAmbient k => x.coeff n) hf
    rw [coeff_mahlerDilation] at h
    have hunit : (HahnSeries.C (((p : k)) ^ n) : HahnSeries ℚ k)
        * (HahnSeries.C (((p : k))⁻¹) : HahnSeries ℚ k) ^ n = 1 := by
      rw [← map_zpow₀, ← map_mul, inv_zpow, mul_inv_cancel₀ (zpow_ne_zero n hpk), map_one]
    calc mahlerHom p (by omega : 0 < p) (f.coeff n)
        = 1 * mahlerHom p (by omega : 0 < p) (f.coeff n) := by rw [one_mul]
      _ = (HahnSeries.C (((p : k)) ^ n) * (HahnSeries.C (((p : k))⁻¹)) ^ n)
            * mahlerHom p (by omega : 0 < p) (f.coeff n) := by rw [hunit]
      _ = HahnSeries.C (((p : k)) ^ n)
            * ((HahnSeries.C (((p : k))⁻¹)) ^ n * mahlerHom p (by omega : 0 < p) (f.coeff n)) := by
          ring
      _ = HahnSeries.C (((p : k)) ^ n) * f.coeff n := by rw [h]
  refine ⟨(f.coeff 0).coeff 0, ?_⟩
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    have h0 := hcoeff 0
    rw [zpow_zero, map_one, one_mul] at h0
    rw [eq_C_of_mahlerHom_eq_self hp h0]
    simp [HahnSeries.C_apply]
  · have hzero : f.coeff n = 0 :=
      eq_zero_of_mahlerHom_eq_smul hp (natCast_zpow_ne_one hp hn) (hcoeff n)
    rw [hzero]
    simp [HahnSeries.C_apply, hn]

/-! ## Laurent series inside the Hahn field -/

theorem embDomain_comp {Γ Γ' Γ'' R : Type*} [PartialOrder Γ] [PartialOrder Γ'] [PartialOrder Γ'']
    [Zero R] (f : Γ ↪o Γ') (g : Γ' ↪o Γ'') (x : HahnSeries Γ R) :
    HahnSeries.embDomain g (HahnSeries.embDomain f x) = HahnSeries.embDomain (f.trans g) x := by
  ext c
  by_cases hc : ∃ a : Γ, g (f a) = c
  · obtain ⟨a, rfl⟩ := hc
    have h1 : (HahnSeries.embDomain g (HahnSeries.embDomain f x)).coeff (g (f a)) = x.coeff a := by
      rw [HahnSeries.embDomain_coeff, HahnSeries.embDomain_coeff]
    have h2 : (HahnSeries.embDomain (f.trans g) x).coeff (g (f a)) = x.coeff a := by
      show (HahnSeries.embDomain (f.trans g) x).coeff ((f.trans g) a) = x.coeff a
      rw [HahnSeries.embDomain_coeff]
    rw [h1, h2]
  · push Not at hc
    have hrhs : (HahnSeries.embDomain (f.trans g) x).coeff c = 0 := by
      refine HahnSeries.embDomain_notin_range ?_
      rintro ⟨a, ha⟩
      exact hc a ha
    rw [hrhs]
    by_cases hc' : ∃ b : Γ', g b = c
    · obtain ⟨b, rfl⟩ := hc'
      rw [HahnSeries.embDomain_coeff]
      refine HahnSeries.embDomain_notin_range ?_
      rintro ⟨a, ha⟩
      exact hc a (by rw [ha])
    · push Not at hc'
      refine HahnSeries.embDomain_notin_range ?_
      rintro ⟨b, hb⟩
      exact hc' b hb

theorem intCast_le_iff (m n : ℤ) : ((m : ℚ)) ≤ ((n : ℚ)) ↔ m ≤ n := by
  exact_mod_cast Iff.rfl

/-- The Laurent series in `w` sit inside the Hahn series with rational exponents. -/
def laurentToHahn : LaurentSeries k →+* HahnSeries ℚ k :=
  HahnSeries.embDomainRingHom (Int.castAddHom ℚ)
    (fun m n h => by
      have h' : ((m : ℚ)) = ((n : ℚ)) := h
      exact_mod_cast h')
    (fun m n => intCast_le_iff m n)

@[simp]
theorem coeff_laurentToHahn (f : LaurentSeries k) (n : ℤ) :
    (laurentToHahn f).coeff ((n : ℚ)) = f.coeff n := by
  have h := HahnSeries.embDomain_coeff
    (f := ⟨⟨Int.castAddHom ℚ, fun m n h => by
      have h' : ((m : ℚ)) = ((n : ℚ)) := h
      exact_mod_cast h'⟩, intCast_le_iff _ _⟩) (x := f) (a := n)
  simpa [laurentToHahn] using h

theorem coeff_laurentToHahn_of_not_int (f : LaurentSeries k) {γ : ℚ}
    (hγ : ∀ n : ℤ, ((n : ℚ)) ≠ γ) : (laurentToHahn f).coeff γ = 0 := by
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨n, hn⟩
  exact hγ n hn

/-- **Stretching integer exponents is the Mahler substitution.** -/
theorem laurentToHahn_ramify (p : ℕ) (hp : 1 < p) (f : LaurentSeries k) :
    laurentToHahn (ramify p (by omega) f) = mahlerHom p (by omega) (laurentToHahn f) := by
  show HahnSeries.embDomain _ (HahnSeries.embDomain _ f)
    = HahnSeries.embDomain _ (HahnSeries.embDomain _ f)
  rw [embDomain_comp, embDomain_comp]
  congr 1
  refine RelEmbedding.ext fun n => ?_
  show ((((p : ℤ) * n : ℤ) : ℚ)) = (p : ℚ) * ((n : ℤ) : ℚ)
  push_cast
  ring

/-! ## The derivation and its twisted commutation -/

/-- The Euler derivation of the Hahn field: multiply the coefficient of `w^γ` by `γ`. -/
def hahnQEuler [CharZero k] : HahnSeries ℚ k →+ HahnSeries ℚ k :=
  hahnGradeHom ((Rat.castHom k) : ℚ →+* k).toAddMonoidHom

@[simp]
theorem coeff_hahnQEuler [CharZero k] (f : HahnSeries ℚ k) (γ : ℚ) :
    (hahnQEuler f).coeff γ = ((γ : k)) * f.coeff γ := rfl

theorem hahnQEuler_leibniz [CharZero k] (x y : HahnSeries ℚ k) :
    hahnQEuler (x * y) = hahnQEuler x * y + x * hahnQEuler y :=
  hahnGrade_mul _ x y

/-- **The Euler derivation and the Mahler substitution commute up to the factor `p`.** -/
theorem hahnQEuler_mahlerHom [CharZero k] (p : ℕ) (hp : 1 < p) (f : HahnSeries ℚ k) :
    hahnQEuler (mahlerHom p (by omega) f)
      = HahnSeries.C ((p : k)) * mahlerHom p (by omega) (hahnQEuler f) := by
  have hpQ : ((p : ℚ)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this.ne'
  refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
  have hγ : (p : ℚ) * (γ / (p : ℚ)) = γ := by
    field_simp
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  rw [coeff_hahnQEuler, coeff_C_mul_hahn, coeff_mahlerHom p hp, coeff_mahlerHom p hp,
    coeff_hahnQEuler]
  rw [show ((γ : k)) = ((p : k)) * (((γ / (p : ℚ) : ℚ)) : k) from by
    push_cast
    field_simp]
  ring

/-- The derivation of the Mahler ambient: the Euler operator on the `w`-grading, with the twisting
coordinate `h` constant. -/
def mahlerAmbientDeriv [CharZero k] : MahlerAmbient k →+ MahlerAmbient k :=
  hahnCoeffMapHom hahnQEuler

@[simp]
theorem coeff_mahlerAmbientDeriv [CharZero k] (f : MahlerAmbient k) (n : ℤ) :
    (mahlerAmbientDeriv f).coeff n = hahnQEuler (f.coeff n) := rfl

theorem mahlerAmbientDeriv_leibniz [CharZero k] (x y : MahlerAmbient k) :
    mahlerAmbientDeriv (x * y)
      = mahlerAmbientDeriv x * y + x * mahlerAmbientDeriv y :=
  hahnCoeffMap_leibniz hahnQEuler hahnQEuler_leibniz x y

/-- The differential structure of the Mahler ambient. -/
@[reducible] def mahlerDifferential [CharZero k] : Differential (MahlerAmbient k) := by
  letI : Algebra ℤ (MahlerAmbient k) := Ring.toIntAlgebra _
  exact ⟨Derivation.mk' (mahlerAmbientDeriv (k := k)).toIntLinearMap (by
    intro x y
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul, mahlerAmbientDeriv_leibniz]
    ring)⟩

theorem mahlerDifferential_deriv [CharZero k] (f : MahlerAmbient k) :
    (mahlerDifferential (k := k)).deriv f = mahlerAmbientDeriv f := rfl

/-- **The Mahler substitution and the derivation commute up to the factor `p`.** -/
theorem mahlerAmbientDeriv_mahlerDilation [CharZero k] (p : ℕ) (hp : 1 < p) (f : MahlerAmbient k) :
    mahlerAmbientDeriv (mahlerDilation p hp f)
      = HahnSeries.C (HahnSeries.C ((p : k)))
        * mahlerDilation p hp (mahlerAmbientDeriv f) := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerAmbientDeriv, coeff_mahlerDilation, coeff_C_mul_hahn, coeff_mahlerDilation,
    coeff_mahlerAmbientDeriv]
  have hlin : ∀ (c : k) (g : HahnSeries ℚ k),
      hahnQEuler ((HahnSeries.C c : HahnSeries ℚ k) * g)
        = (HahnSeries.C c : HahnSeries ℚ k) * hahnQEuler g := by
    intro c g
    refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
    rw [coeff_hahnQEuler, coeff_C_mul_hahn, coeff_C_mul_hahn, coeff_hahnQEuler]
    ring
  have hconst : ∀ (n : ℤ) (g : HahnSeries ℚ k),
      hahnQEuler ((HahnSeries.C (((p : k))⁻¹) : HahnSeries ℚ k) ^ n * g)
        = (HahnSeries.C (((p : k))⁻¹) : HahnSeries ℚ k) ^ n * hahnQEuler g := by
    intro n g
    rw [← map_zpow₀]
    exact hlin ((((p : k))⁻¹) ^ n) g
  rw [hconst, hahnQEuler_mahlerHom p hp]
  ring

/-! ## The jets of a Mahler primitive -/

theorem mahlerAmbientDeriv_const_mul [CharZero k] (c : k) (g : MahlerAmbient k) :
    mahlerAmbientDeriv ((HahnSeries.C (HahnSeries.C c) : MahlerAmbient k) * g)
      = (HahnSeries.C (HahnSeries.C c) : MahlerAmbient k) * mahlerAmbientDeriv g := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerAmbientDeriv, coeff_C_mul_hahn, coeff_C_mul_hahn, coeff_mahlerAmbientDeriv]
  refine HahnSeries.coeff_inj.mp (funext fun γ => ?_)
  rw [coeff_hahnQEuler, coeff_C_mul_hahn, coeff_C_mul_hahn, coeff_hahnQEuler]
  ring

theorem mahlerAmbientDeriv_iterate_const_mul [CharZero k] (c : k) (n : ℕ) (g : MahlerAmbient k) :
    mahlerAmbientDeriv^[n] ((HahnSeries.C (HahnSeries.C c) : MahlerAmbient k) * g)
      = (HahnSeries.C (HahnSeries.C c) : MahlerAmbient k) * mahlerAmbientDeriv^[n] g := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        mahlerAmbientDeriv_const_mul, ih]

/-- **The substitution moves the jets by a scalar.**  `σ δⁿ = p^(-n) δⁿ σ`. -/
theorem mahlerDilation_deriv_iterate [CharZero k] (p : ℕ) (hp : 1 < p) (n : ℕ)
    (f : MahlerAmbient k) :
    mahlerDilation p hp (mahlerAmbientDeriv^[n] f)
      = (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k) ^ n
        * mahlerAmbientDeriv^[n] (mahlerDilation p hp f) := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  have hstep : ∀ g : MahlerAmbient k,
      mahlerDilation p hp (mahlerAmbientDeriv g)
        = (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k)
          * mahlerAmbientDeriv (mahlerDilation p hp g) := by
    intro g
    have h := mahlerAmbientDeriv_mahlerDilation p hp g
    have hinv : (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k)
        * HahnSeries.C (HahnSeries.C ((p : k))) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel₀ hpk, map_one, map_one]
    calc mahlerDilation p hp (mahlerAmbientDeriv g)
        = 1 * mahlerDilation p hp (mahlerAmbientDeriv g) := by rw [one_mul]
      _ = ((HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k)
            * HahnSeries.C (HahnSeries.C ((p : k))))
              * mahlerDilation p hp (mahlerAmbientDeriv g) := by rw [hinv]
      _ = (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k)
            * (HahnSeries.C (HahnSeries.C ((p : k)))
              * mahlerDilation p hp (mahlerAmbientDeriv g)) := by ring
      _ = (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k)
            * mahlerAmbientDeriv (mahlerDilation p hp g) := by rw [← h]
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih (mahlerAmbientDeriv f), hstep f,
        mahlerAmbientDeriv_iterate_const_mul, Function.iterate_succ_apply, pow_succ]
      ring

/-- The twisting coordinate of the Mahler ambient. -/
def mahlerCoord (k : Type*) [Field k] : MahlerAmbient k := HahnSeries.single 1 1

theorem mahlerCoord_ne_zero : (mahlerCoord k) ≠ 0 := by
  intro h
  have := congrArg (fun x : MahlerAmbient k => x.coeff 1) h
  rw [mahlerCoord, HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at this
  exact one_ne_zero this

theorem mahlerDilation_mahlerCoord [CharZero k] (p : ℕ) (hp : 1 < p) :
    mahlerDilation p hp (mahlerCoord k)
      = (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k) * mahlerCoord k := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerDilation, coeff_C_mul_hahn, mahlerCoord]
  by_cases h : n = 1
  · subst h
    simp
  · simp [HahnSeries.coeff_single_of_ne h]

theorem mahlerDilation_mahlerCoord_pow [CharZero k] (p : ℕ) (hp : 1 < p) (n : ℕ) :
    mahlerDilation p hp (mahlerCoord k ^ n)
      = (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k) ^ n * mahlerCoord k ^ n := by
  rw [map_pow, mahlerDilation_mahlerCoord, mul_pow]

theorem mahlerAmbientDeriv_iterate_add [CharZero k] (n : ℕ) (x y : MahlerAmbient k) :
    mahlerAmbientDeriv^[n] (x + y)
      = mahlerAmbientDeriv^[n] x + mahlerAmbientDeriv^[n] y := by
  induction n generalizing x y with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        map_add, ih]

/-- **The twisted jets of a Mahler primitive are simultaneous additive primitives.**  Dividing the
`n`-th jet by the `n`-th power of the twisting coordinate cancels the scalar `p^(-n)`. -/
theorem mahler_twistedJet_shift [CharZero k] (p : ℕ) (hp : 1 < p) (u b : MahlerAmbient k)
    (hshift : mahlerDilation p hp u = u + b) (n : ℕ) :
    mahlerDilation p hp (mahlerAmbientDeriv^[n] u / mahlerCoord k ^ n)
      = mahlerAmbientDeriv^[n] u / mahlerCoord k ^ n
        + mahlerAmbientDeriv^[n] b / mahlerCoord k ^ n := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  have hCne : (HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k) ≠ 0 := by
    intro hzero
    have := congrArg (fun x : MahlerAmbient k => (x.coeff 0).coeff 0) hzero
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_same, HahnSeries.C_apply,
      HahnSeries.coeff_single_same] at this
    simp only [HahnSeries.coeff_zero] at this
    exact inv_ne_zero hpk this
  have hCpow : ((HahnSeries.C (HahnSeries.C (((p : k))⁻¹)) : MahlerAmbient k)) ^ n ≠ 0 :=
    pow_ne_zero n hCne
  have hcoord : (mahlerCoord k) ^ n ≠ 0 := pow_ne_zero n mahlerCoord_ne_zero
  rw [map_div₀, mahlerDilation_deriv_iterate p hp n u, mahlerDilation_mahlerCoord_pow p hp n,
    hshift]
  rw [mahlerAmbientDeriv_iterate_add]
  rw [mul_div_mul_left _ _ hCpow, add_div]

end

end GaloisForLFunctions.HTGeometry
