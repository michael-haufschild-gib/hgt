import GaloisForLFunctions.HTGeometry.TaylorDefectProfileBound

/-!
# A polynomial exponent for the Taylor defect that does not grow with the truncation order

The bound `‖a_n‖ ≤ c (n+1)^A Θ(N+1) Θ(n−N−1)` for the Taylor defect at a truncation of order `N` is
only useful if the exponent `A` stays bounded as `N` grows: the gain over the leading Newton term is
`Θ(n−N−1)/Θ(n−ν) ≍ n^{−s(N+1−ν)}`, so it beats `n^A` only when `A` is fixed first and `N` is chosen
afterwards.

Tracking the exponent through the estimates shows that it is: a convergent series is dominated by
the profile with **no** polynomial factor at all, the jets of the tail carry an exponent that
depends on the order of the equation only, and the finite family that presents the defect depends on
the equation alone.  Every place where `N` enters contributes to the constant, never to the
exponent.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### Profile bounds with a named exponent -/

/-- A profile bound whose polynomial correction has a named exponent. -/
def HasProfileBoundExp (s β : ℝ) (a : ℕ) (A : PowerSeries ℂ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧
    ∀ k : ℕ, ‖PowerSeries.coeff k A‖ ≤ c * ((k : ℝ) + 1) ^ a * gammaProfile s β k

theorem HasProfileBoundExp.hasProfileBound {s β : ℝ} {a : ℕ} {A : PowerSeries ℂ}
    (h : HasProfileBoundExp s β a A) : HasProfileBound s β A := by
  obtain ⟨c, hc, hb⟩ := h
  exact ⟨c, a, hc, hb⟩

theorem HasProfileBoundExp.mono {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {a b : ℕ}
    {A : PowerSeries ℂ} (hab : a ≤ b) (h : HasProfileBoundExp s β a A) :
    HasProfileBoundExp s β b A := by
  obtain ⟨c, hc, hb⟩ := h
  refine ⟨c, hc, fun k => ?_⟩
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  refine le_trans (hb k) ?_
  refine mul_le_mul_of_nonneg_right ?_ (gammaProfile_pos hs.le hβ k).le
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk hab) hc

/-- The Cauchy product bound with both exponents named. -/
theorem norm_coeff_mul_le_poly {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {A B : PowerSeries ℂ}
    {cA cB : ℝ} {a b : ℕ} (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hA : ∀ k : ℕ, ‖PowerSeries.coeff k A‖ ≤ cA * ((k : ℝ) + 1) ^ a * gammaProfile s β k)
    (hB : ∀ k : ℕ, ‖PowerSeries.coeff k B‖ ≤ cB * ((k : ℝ) + 1) ^ b * gammaProfile s β k)
    (n : ℕ) :
    ‖PowerSeries.coeff n (A * B)‖
      ≤ cA * cB * ((n : ℝ) + 1) ^ (a + b + 1) * gammaProfile s β n := by
  classical
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hterm : ∀ p : ℕ × ℕ, p.1 + p.2 = n →
      ‖PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 B‖
        ≤ cA * cB * ((n : ℝ) + 1) ^ (a + b) * gammaProfile s β n := by
    intro p hp
    have hp1 : (p.1 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (p.1 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (by omega)
      linarith
    have hp2 : (p.2 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (p.2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (by omega)
      linarith
    have hΘ1 : (0 : ℝ) < gammaProfile s β p.1 := gammaProfile_pos hs.le hβ _
    have hΘ2 : (0 : ℝ) < gammaProfile s β p.2 := gammaProfile_pos hs.le hβ _
    have hsubmul : gammaProfile s β p.1 * gammaProfile s β p.2 ≤ gammaProfile s β n := by
      have h := gammaProfile_mul_le hs hβ p.1 p.2
      rwa [hp] at h
    have hbound1 : ‖PowerSeries.coeff p.1 A‖ ≤ cA * ((n : ℝ) + 1) ^ a * gammaProfile s β p.1 := by
      refine le_trans (hA p.1) ?_
      refine mul_le_mul_of_nonneg_right ?_ hΘ1.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp1 a) hcA
    have hbound2 : ‖PowerSeries.coeff p.2 B‖ ≤ cB * ((n : ℝ) + 1) ^ b * gammaProfile s β p.2 := by
      refine le_trans (hB p.2) ?_
      refine mul_le_mul_of_nonneg_right ?_ hΘ2.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp2 b) hcB
    rw [norm_mul]
    calc ‖PowerSeries.coeff p.1 A‖ * ‖PowerSeries.coeff p.2 B‖
        ≤ (cA * ((n : ℝ) + 1) ^ a * gammaProfile s β p.1) *
            (cB * ((n : ℝ) + 1) ^ b * gammaProfile s β p.2) :=
          mul_le_mul hbound1 hbound2 (norm_nonneg _) (by positivity)
      _ = (cA * cB * ((n : ℝ) + 1) ^ (a + b)) *
            (gammaProfile s β p.1 * gammaProfile s β p.2) := by
          rw [pow_add]; ring
      _ ≤ (cA * cB * ((n : ℝ) + 1) ^ (a + b)) * gammaProfile s β n :=
          mul_le_mul_of_nonneg_left hsubmul (by positivity)
      _ = cA * cB * ((n : ℝ) + 1) ^ (a + b) * gammaProfile s β n := by ring
  rw [PowerSeries.coeff_mul]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun p hp => hterm p (by simpa using hp))) ?_
  simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  have hexp : cA * cB * ((n : ℝ) + 1) ^ (a + b + 1) * gammaProfile s β n
      = ((n : ℝ) + 1) * (cA * cB * ((n : ℝ) + 1) ^ (a + b) * gammaProfile s β n) := by
    rw [pow_succ]
    ring
  rw [hexp]
  push_cast
  exact le_rfl

theorem HasProfileBoundExp.mul {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {a b : ℕ}
    {A B : PowerSeries ℂ} (hA : HasProfileBoundExp s β a A)
    (hB : HasProfileBoundExp s β b B) : HasProfileBoundExp s β (a + b + 1) (A * B) := by
  obtain ⟨cA, hcA, hA'⟩ := hA
  obtain ⟨cB, hcB, hB'⟩ := hB
  exact ⟨cA * cB, mul_nonneg hcA hcB,
    fun n => norm_coeff_mul_le_poly hs hβ hcA hcB hA' hB' n⟩

theorem hasProfileBoundExp_one {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    HasProfileBoundExp s β 0 (1 : PowerSeries ℂ) := by
  refine ⟨1, zero_le_one, fun k => ?_⟩
  have hΘ : (0 : ℝ) < gammaProfile s β k := gammaProfile_pos hs.le hβ _
  by_cases hk : k = 0
  · subst hk
    rw [PowerSeries.coeff_zero_one]
    simp only [pow_zero, one_mul, mul_one, norm_one]
    rw [gammaProfile]
    norm_num
  · rw [PowerSeries.coeff_one, if_neg hk, norm_zero]
    positivity

theorem HasProfileBoundExp.pow {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {a : ℕ} {A : PowerSeries ℂ}
    (hA : HasProfileBoundExp s β a A) : ∀ e : ℕ, HasProfileBoundExp s β (e * (a + 1)) (A ^ e)
  | 0 => by
      rw [pow_zero, Nat.zero_mul]
      exact hasProfileBoundExp_one hs hβ
  | (e + 1) => by
      rw [pow_succ, show (e + 1) * (a + 1) = e * (a + 1) + a + 1 from by ring]
      exact (HasProfileBoundExp.pow hs hβ hA e).mul hs hβ hA

/-- **Jet monomials, with an exponent that grows only with the degree.** -/
theorem HasProfileBoundExp.jetMonomialValue {ι : Type*} {s β : ℝ} (hs : 0 < s) (hβ : 0 < β)
    {a : ℕ} {L : ι → PowerSeries ℂ} (hL : ∀ i, HasProfileBoundExp s β a (L i)) (α : ι →₀ ℕ) :
    HasProfileBoundExp s β (jetDegree α * (a + 2)) (jetMonomialValue L α) := by
  classical
  refine Finsupp.induction α ?_ ?_
  · rw [jetMonomialValue_zero, show jetDegree (0 : ι →₀ ℕ) * (a + 2) = 0 from by
      rw [jetDegree_eq_zero_iff.mpr rfl, Nat.zero_mul]]
    exact hasProfileBoundExp_one hs hβ
  · intro i e f _ he ih
    rw [jetMonomialValue_add, jetMonomialValue_single_pow, jetDegree_add, jetDegree_single]
    have hstep := ((hL i).pow hs hβ e).mul hs hβ ih
    refine hstep.mono hs hβ ?_
    have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
    have hexp : (e + jetDegree f) * (a + 2) = e * (a + 1) + e + jetDegree f * (a + 2) := by ring
    rw [hexp]
    omega

/-! ### Convergent series have exponent zero -/

theorem hasProfileBoundExp_zero_of_isGevreySeries_zero {s β : ℝ} (hs : 0 < s)
    (hirr : Irrational s) (hβ : 0 < β) {A : PowerSeries ℂ} (hA : IsGevreySeries 0 A) :
    HasProfileBoundExp s β 0 A := by
  obtain ⟨C, L, hC, hL, hbd⟩ := hA
  have hprof := isRegularFactorialProfile_gammaProfile_of_irrational hs hirr hβ
  have hc₁ : 0 < β * (s + 1 - ((⌈s⌉₊ : ℕ) : ℝ)) ^ s := hprof.c₁_pos
  set c₁ : ℝ := β * (s + 1 - ((⌈s⌉₊ : ℕ) : ℝ)) ^ s with hc₁def
  have hlow : ∀ k : ℕ, c₁ ^ k * (((k ! : ℕ) : ℝ)) ^ s ≤ gammaProfile s β k := by
    intro k
    have h := hprof.block_lower (a := 0) (b := k) (Nat.zero_le k)
    rw [gammaProfile_zero, Nat.factorial_zero, Nat.sub_zero] at h
    simpa using h
  obtain ⟨c, hc, hpow⟩ := exists_pow_le_const_mul_factorial_rpow hs
    (M := L / c₁) (by positivity)
  refine ⟨C * c, by positivity, fun k => ?_⟩
  have hgeo : L ^ k = c₁ ^ k * (L / c₁) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hAk : ‖PowerSeries.coeff k A‖ ≤ C * L ^ k := by
    have h := hbd k
    simpa using h
  have hstep : C * L ^ k ≤ C * c * gammaProfile s β k := by
    rw [hgeo]
    have h1 : (L / c₁) ^ k ≤ c * (((k ! : ℕ) : ℝ)) ^ s := hpow k
    have h2 : c₁ ^ k * ((L / c₁) ^ k) ≤ c₁ ^ k * (c * (((k ! : ℕ) : ℝ)) ^ s) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : c₁ ^ k * (c * (((k ! : ℕ) : ℝ)) ^ s) = c * (c₁ ^ k * (((k ! : ℕ) : ℝ)) ^ s) := by
      ring
    have h4 : c * (c₁ ^ k * (((k ! : ℕ) : ℝ)) ^ s) ≤ c * gammaProfile s β k :=
      mul_le_mul_of_nonneg_left (hlow k) hc.le
    nlinarith [h2, h3, h4, hC.le]
  calc ‖PowerSeries.coeff k A‖ ≤ C * L ^ k := hAk
    _ ≤ C * c * gammaProfile s β k := hstep
    _ = C * c * ((k : ℝ) + 1) ^ (0 : ℕ) * gammaProfile s β k := by rw [pow_zero]; ring

/-! ### The defect term with a named exponent -/

/-- **A profile-bounded multiple of a jet monomial of degree at least two in a tail, with the
exponent read off from the data.** -/
theorem norm_coeff_mul_jetMonomialValue_le_exp {ι : Type*} [DecidableEq ι] {s β : ℝ}
    (hs : 0 < s) (hβ : 0 < β) {N : ℕ} {L : ι → PowerSeries ℂ} {D : PowerSeries ℂ}
    {d a q : ℕ}
    (hD : HasProfileBoundExp s β d D)
    (hL : ∀ i, HasProfileBoundExp s β a (L i))
    (hL0 : ∀ i, (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ L i)
    {α : ι →₀ ℕ} (hα : 2 ≤ jetDegree α) (hq : jetDegree α ≤ q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ,
      ‖PowerSeries.coeff n (D * jetMonomialValue L α)‖
        ≤ c * ((n : ℝ) + 1) ^ (a + (d + q * (a + 2) + 1) + 1) *
          (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
  classical
  have hαne : α ≠ 0 := by
    intro h
    rw [h] at hα
    rw [jetDegree] at hα
    simp at hα
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hαne
  have hαi : 1 ≤ α i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  set γ : ι →₀ ℕ := Finsupp.single i (α i - 1) + Finsupp.erase i α with hγ
  have hdecomp : α = Finsupp.single i 1 + γ := by
    rw [hγ, ← add_assoc, ← Finsupp.single_add, show 1 + (α i - 1) = α i from by omega,
      Finsupp.single_add_erase]
  have hdeg : jetDegree α = 1 + jetDegree γ := by
    conv_lhs => rw [hdecomp]
    rw [jetDegree_add, jetDegree_single]
  have hdegγ : 1 ≤ jetDegree γ := by omega
  have hdegγq : jetDegree γ ≤ q := by omega
  have hprod : D * jetMonomialValue L α = L i * (D * jetMonomialValue L γ) := by
    conv_lhs => rw [hdecomp]
    rw [jetMonomialValue_add, jetMonomialValue_single]
    ring
  have hdvdγ : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ D * jetMonomialValue L γ :=
    Dvd.dvd.mul_left (X_pow_dvd_jetMonomialValue hL0 (jetDegree γ) γ rfl hdegγ) _
  have hvanγ : ∀ k, k ≤ N → PowerSeries.coeff k (D * jetMonomialValue L γ) = 0 := by
    intro k hk
    exact (PowerSeries.X_pow_dvd_iff.mp hdvdγ) k (by omega)
  have hvani : ∀ k, k ≤ N → PowerSeries.coeff k (L i) = 0 := by
    intro k hk
    exact (PowerSeries.X_pow_dvd_iff.mp (hL0 i)) k (by omega)
  obtain ⟨cA, hcA, hA⟩ := hL i
  have hBexp : HasProfileBoundExp s β (d + q * (a + 2) + 1) (D * jetMonomialValue L γ) := by
    refine (hD.mul hs hβ (HasProfileBoundExp.jetMonomialValue hs hβ hL γ)).mono hs hβ ?_
    have : jetDegree γ * (a + 2) ≤ q * (a + 2) := Nat.mul_le_mul_right _ hdegγq
    omega
  obtain ⟨cB, hcB, hB⟩ := hBexp
  refine ⟨cA * cB, mul_nonneg hcA hcB, fun n => ?_⟩
  rw [hprod]
  exact norm_coeff_mul_le_of_vanishing_poly hs hβ hcA hcB hA hB hvani hvanγ n

/-! ### The defect -/

/-- **The Taylor defect at a truncation obeys a profile bound whose polynomial exponent is chosen
before the truncation order.**  The finite family presenting the defect is attached to the equation
alone, the coefficients evaluated at the base point are convergent and so carry no polynomial
factor, and the jets of the tail carry the exponent supplied in advance. -/
theorem exists_uniform_norm_coeff_taylorDefect_le {m : ℕ} {s β : ℝ} (hs : 0 < s)
    (hirr : Irrational s) (hβ : 0 < β)
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)) (hP : IsAnalyticDifferentialPolynomial P)
    (a : ℕ) :
    ∃ A : ℕ, ∀ (N : ℕ) (Y H : PowerSeries ℂ), IsGevreySeries 0 Y →
      (∀ j : Fin (m + 1), HasProfileBoundExp s β a (eulerJetVector (m := m) H j)) →
      (∀ j : Fin (m + 1),
        (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ eulerJetVector (m := m) H j) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ,
        ‖PowerSeries.coeff n
            (taylorDefect (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H) P)‖
          ≤ c * ((n : ℝ) + 1) ^ A *
            (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
  classical
  obtain ⟨T, hT2, hTco, hTsum⟩ :=
    hasTaylorDefectFamily (A := PowerSeries ℂ) convergentSubsemiring P
      (fun σ => (mem_convergentSubsemiring).mpr (hP σ))
  set q : ℕ := T.support.sup jetDegree with hqdef
  refine ⟨a + (0 + q * (a + 2) + 1) + 1, fun N Y H hY hHprof hH0 => ?_⟩
  have hex : ∀ α : (Fin (m + 1) →₀ ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ,
      (α ∈ T.support →
        ‖PowerSeries.coeff n
            (MvPolynomial.aeval (eulerJetVector (m := m) Y) (T α) *
              jetMonomialValue (eulerJetVector (m := m) H) α)‖
          ≤ c * ((n : ℝ) + 1) ^ (a + (0 + q * (a + 2) + 1) + 1) *
            (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1)))) := by
    intro α
    by_cases hα : α ∈ T.support
    · have hTα : IsAnalyticDifferentialPolynomial (T α) :=
        fun σ => (mem_convergentSubsemiring).mp (hTco α σ)
      have hDconv : IsGevreySeries 0
          (MvPolynomial.aeval (eulerJetVector (m := m) Y) (T α)) :=
        isGevreySeries_aeval_eulerJetVector le_rfl (T α) hTα hY
      have hD : HasProfileBoundExp s β 0
          (MvPolynomial.aeval (eulerJetVector (m := m) Y) (T α)) :=
        hasProfileBoundExp_zero_of_isGevreySeries_zero hs hirr hβ hDconv
      obtain ⟨c, hc, hb⟩ :=
        norm_coeff_mul_jetMonomialValue_le_exp hs hβ hD hHprof hH0 (hT2 α hα)
          (Finset.le_sup hα)
      exact ⟨c, hc, fun n _ => hb n⟩
    · exact ⟨0, le_rfl, fun n hn => absurd hn hα⟩
  choose c hc hb using hex
  refine ⟨∑ α ∈ T.support, c α, Finset.sum_nonneg fun α _ => hc α, fun n => ?_⟩
  rw [hTsum (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H), Finsupp.sum, map_sum]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun α hα => hb α n hα) ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]

end GaloisForLFunctions.HTGeometry
