import Mathlib
import GaloisForLFunctions.HTGeometry.SuperexponentialGrowth
import GaloisForLFunctions.HTGeometry.GapSeriesIrrational

/-!
# Balanced coefficient extraction from powers of a gap series

If a power series is supported on an exponent set `E` and the only representation of `D·e₀`
as a sum of `D` elements of `E` is the constant one, then the coefficient of `G^D` at
`D·e₀` is the pure `D`-th power `(coeff e₀ G)^D` (`coeff_pow_unique_rep`): in the
multinomial expansion the balanced diagonal term survives alone, with no interference from
any other exponent tuple.  In particular the coefficient is nonzero whenever the base
coefficient is (`coeff_pow_unique_rep_ne_zero`), so no power of the series can vanish at a
balanced exponent — the multiplicative non-collision mechanism for lacunary supports.
-/

namespace GaloisForLFunctions

/-- **Balanced coefficient extraction**: when the only way to write `D·e₀` as a sum of `D`
exponents from the support set `E` is `e₀ + ⋯ + e₀`, the coefficient of `G^D` at `D·e₀`
collapses to the single diagonal term `(coeff e₀ G)^D`. -/
theorem coeff_pow_unique_rep {R : Type*} [CommSemiring R] {G : PowerSeries R} {E : Set ℕ}
    (hsupp : ∀ k, PowerSeries.coeff k G ≠ 0 → k ∈ E) {D e₀ : ℕ}
    (huniq : ∀ e : Fin D → ℕ, (∀ i, e i ∈ E) → (∑ i, e i) = D * e₀ → ∀ i, e i = e₀) :
    PowerSeries.coeff (D * e₀) (G ^ D) = (PowerSeries.coeff e₀ G) ^ D := by
  classical
  rw [PowerSeries.coeff_pow]
  set l₀ : ℕ →₀ ℕ := Finsupp.onFinset (Finset.range D)
    (fun j => if j ∈ Finset.range D then e₀ else 0)
    (fun a ha => by by_contra hc; exact ha (if_neg hc)) with hl₀def
  have hl₀app : ∀ j ∈ Finset.range D, l₀ j = e₀ := fun j hj => by
    rw [hl₀def, Finsupp.onFinset_apply, if_pos hj]
  have hl₀mem : l₀ ∈ (Finset.range D).finsuppAntidiag (D * e₀) := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finsupp.support_onFinset_subset⟩
    show (∑ j ∈ Finset.range D, l₀ j) = D * e₀
    rw [Finset.sum_congr rfl hl₀app, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hkill : ∀ l ∈ (Finset.range D).finsuppAntidiag (D * e₀), l ≠ l₀ →
      (∏ i ∈ Finset.range D, PowerSeries.coeff (l i) G) = 0 := by
    intro l hl hne
    rw [Finset.mem_finsuppAntidiag] at hl
    by_cases hall : ∀ i ∈ Finset.range D, PowerSeries.coeff (l i) G ≠ 0
    · exfalso
      apply hne
      have he : ∀ i : Fin D, l (i : ℕ) = e₀ := by
        apply huniq (fun i => l (i : ℕ))
        · intro i
          exact hsupp _ (hall _ (Finset.mem_range.mpr i.isLt))
        · have hsum2 : (∑ i : Fin D, l (i : ℕ)) = ∑ j ∈ Finset.range D, l j :=
            Fin.sum_univ_eq_sum_range (fun j => l j) D
          show (∑ i : Fin D, l (i : ℕ)) = D * e₀
          rw [hsum2]
          exact hl.1
      ext j
      by_cases hj : j < D
      · have h1 : l j = e₀ := he ⟨j, hj⟩
        have h2 : l₀ j = e₀ := hl₀app j (Finset.mem_range.mpr hj)
        rw [h1, h2]
      · have h1 : l j = 0 := by
          by_contra hlj
          exact hj (Finset.mem_range.mp (hl.2 (Finsupp.mem_support_iff.mpr hlj)))
        have h2 : l₀ j = 0 := by
          rw [hl₀def, Finsupp.onFinset_apply,
            if_neg (fun hc => hj (Finset.mem_range.mp hc))]
        rw [h1, h2]
    · push Not at hall
      obtain ⟨i, hi, h0⟩ := hall
      exact Finset.prod_eq_zero hi h0
  have hsingle := Finset.sum_eq_single_of_mem l₀ hl₀mem hkill
  have hprod : (∏ i ∈ Finset.range D, PowerSeries.coeff (l₀ i) G)
      = (PowerSeries.coeff e₀ G) ^ D := by
    have h1 : ∀ j ∈ Finset.range D, PowerSeries.coeff (l₀ j) G = PowerSeries.coeff e₀ G :=
      fun j hj => by rw [hl₀app j hj]
    rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_range]
  rw [hsingle, hprod]

/-- At a balanced exponent with unique representation, no power of the series vanishes as
long as the base coefficient does not. -/
theorem coeff_pow_unique_rep_ne_zero {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    {G : PowerSeries R} {E : Set ℕ}
    (hsupp : ∀ k, PowerSeries.coeff k G ≠ 0 → k ∈ E) {D e₀ : ℕ}
    (huniq : ∀ e : Fin D → ℕ, (∀ i, e i ∈ E) → (∑ i, e i) = D * e₀ → ∀ i, e i = e₀)
    (h0 : PowerSeries.coeff e₀ G ≠ 0) :
    PowerSeries.coeff (D * e₀) (G ^ D) ≠ 0 := by
  rw [coeff_pow_unique_rep hsupp huniq]
  exact pow_ne_zero D h0

end GaloisForLFunctions

namespace GaloisForLFunctions

open Filter

/-- **Gap-power balanced coefficient law**: for an integer exponent sequence with divergent
ratio, past a per-degree threshold every series supported on the tail exponents has
`coeff (D·bnat m) (G^D) = (coeff (bnat m) G)^D` — the exponent-level uniqueness of the
balanced representation transfers along the cast and collapses the multinomial expansion
to its diagonal. -/
theorem eventually_coeff_pow_balanced_gap {R : Type*} [CommSemiring R] {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop) (D : ℕ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ G : PowerSeries R,
      (∀ k, PowerSeries.coeff k G ≠ 0 → ∃ n, N ≤ n ∧ k = bnat n) →
      PowerSeries.coeff (D * bnat m) (G ^ D) = (PowerSeries.coeff (bnat m) G) ^ D := by
  have hposR : ∀ᶠ n in atTop, 0 < ((bnat n : ℝ)) :=
    hpos.mono fun n h => Nat.cast_pos.mpr h
  obtain ⟨N, hrep⟩ := eventually_balanced_unique_rep hposR hratio D
  refine ⟨N, fun m hm G hsupp => ?_⟩
  refine coeff_pow_unique_rep (E := {k | ∃ n, N ≤ n ∧ k = bnat n}) hsupp ?_
  intro e he hsum
  choose t hNt hbt using fun i => (he i : ∃ n, N ≤ n ∧ e i = bnat n)
  have hsum' : (∑ i, bnat (t i)) = D * bnat m := by
    have h1 : ∀ i ∈ Finset.univ, bnat (t i) = e i := fun i _ => (hbt i).symm
    rw [Finset.sum_congr rfl h1]
    exact hsum
  have hcast : (∑ i, ((bnat (t i) : ℝ))) = (D : ℝ) * (bnat m : ℝ) := by
    exact_mod_cast hsum'
  have hall : ∀ i, t i = m := hrep m t hm hNt hcast
  intro i
  rw [hbt i, hall i]

/-- Past the threshold, powers of a series supported on the tail of a divergent-ratio
integer exponent sequence never vanish at balanced exponents when the base coefficient
does not: the balanced atom of `G^D` is protected. -/
theorem eventually_coeff_pow_balanced_gap_ne_zero {R : Type*} [CommSemiring R]
    [NoZeroDivisors R] {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop) (D : ℕ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ G : PowerSeries R,
      (∀ k, PowerSeries.coeff k G ≠ 0 → ∃ n, N ≤ n ∧ k = bnat n) →
      PowerSeries.coeff (bnat m) G ≠ 0 →
      PowerSeries.coeff (D * bnat m) (G ^ D) ≠ 0 := by
  obtain ⟨N, hN⟩ := eventually_coeff_pow_balanced_gap (R := R) hpos hratio D
  refine ⟨N, fun m hm G hsupp h0 => ?_⟩
  rw [hN m hm G hsupp]
  exact pow_ne_zero D h0

end GaloisForLFunctions

namespace GaloisForLFunctions

open Filter PowerSeries

/-- A nonzero coefficient of `G^D` is a sum of `D` exponents from the support of `G`. -/
theorem exists_rep_of_coeff_pow_ne_zero {R : Type*} [CommSemiring R] {G : PowerSeries R}
    {D k : ℕ} (h : PowerSeries.coeff k (G ^ D) ≠ 0) :
    ∃ e : Fin D → ℕ, (∀ i, PowerSeries.coeff (e i) G ≠ 0) ∧ (∑ i, e i) = k := by
  classical
  rw [PowerSeries.coeff_pow] at h
  obtain ⟨l, hl, hlne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_finsuppAntidiag] at hl
  refine ⟨fun i => l (i : ℕ), fun i h0 => ?_, ?_⟩
  · exact hlne (Finset.prod_eq_zero (Finset.mem_range.mpr i.isLt) h0)
  · have hsum2 : (∑ i : Fin D, l (i : ℕ)) = ∑ j ∈ Finset.range D, l j :=
      Fin.sum_univ_eq_sum_range (fun j => l j) D
    show (∑ i : Fin D, l (i : ℕ)) = k
    rw [hsum2]
    exact hl.1

/-- **Gap-power irrationality**: for an integer exponent sequence with divergent ratio and
any positive degree `D`, past a threshold every series supported on the tail exponents with
infinitely many nonzero exponent coefficients has an irrational `D`-th power — no relation
`q·G^D = p` with polynomials holds.  Balanced exponents of `G^D` carry nonzero coefficients
and are preceded by zero windows of any prescribed length, because every other achievable
exponent either overshoots past the ratio jump or undershoots below the window. -/
theorem eventually_gap_power_not_rational {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop)
    {D : ℕ} (hD : 0 < D) :
    ∃ N₀ : ℕ, ∀ G : ℂ⟦X⟧,
      (∀ k, PowerSeries.coeff k G ≠ 0 → ∃ n, N₀ ≤ n ∧ k = bnat n) →
      (∀ M, ∃ m, M ≤ m ∧ PowerSeries.coeff (bnat m) G ≠ 0) →
      ∀ p q : Polynomial ℂ, q ≠ 0 → (q : ℂ⟦X⟧) * G ^ D ≠ (p : ℂ⟦X⟧) := by
  obtain ⟨N₁, hN₁⟩ := eventually_coeff_pow_balanced_gap_ne_zero (R := ℂ) hpos hratio D
  have hDge : ∀ᶠ n in atTop, ((D : ℝ) + 1) ≤ (bnat (n + 1) : ℝ) / (bnat n : ℝ) :=
    hratio.eventually_ge_atTop _
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hpos.and hDge)
  have hcast : ∀ n, N₂ ≤ n → (D + 1) * bnat n ≤ bnat (n + 1) := by
    intro n hn
    obtain ⟨hb, hr⟩ := hN₂ n hn
    have hbR : (0 : ℝ) < (bnat n : ℝ) := by exact_mod_cast hb
    rw [le_div_iff₀ hbR] at hr
    have hR : (((D + 1) * bnat n : ℕ) : ℝ) ≤ ((bnat (n + 1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have hmono1 : ∀ n, N₂ ≤ n → bnat n < bnat (n + 1) := by
    intro n hn
    have h1 := hcast n hn
    have hb := (hN₂ n hn).1
    have h2 : 2 * bnat n ≤ (D + 1) * bnat n := Nat.mul_le_mul_right _ (by omega)
    omega
  have hmono : ∀ a, N₂ ≤ a → ∀ c, a ≤ c → bnat a ≤ bnat c := by
    intro a ha c
    induction c with
    | zero =>
      intro h
      have ha0 : a = 0 := Nat.le_zero.mp h
      rw [ha0]
    | succ c ihc =>
      intro h
      rcases Nat.lt_or_ge a (c + 1) with hlt | hge
      · have h1 := ihc (by omega)
        have h2 : bnat c < bnat (c + 1) := hmono1 c (by omega)
        omega
      · have he : a = c + 1 := by omega
        rw [he]
  have hstair : ∀ j, bnat N₂ + j ≤ bnat (N₂ + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ihj =>
      have h2 : bnat (N₂ + j) < bnat (N₂ + j + 1) := hmono1 _ (by omega)
      show bnat N₂ + (j + 1) ≤ bnat (N₂ + j + 1)
      omega
  have hjumpD : ∀ n, N₂ ≤ n → D * bnat n < bnat (n + 1) := by
    intro n hn
    have h1 := hcast n hn
    have hb := (hN₂ n hn).1
    have h2 : (D + 1) * bnat n = D * bnat n + bnat n := by rw [Nat.succ_mul]
    omega
  refine ⟨max N₁ N₂, fun G hsupp hinf p q hq => ?_⟩
  refine powerSeries_not_rational_of_gaps ?_ p q hq
  intro g M
  obtain ⟨m, hm, hmne⟩ := hinf (M + N₁ + N₂ + g + 2)
  have hmN₂ : N₂ ≤ m := by omega
  have hm1N₂ : N₂ ≤ m - 1 := by omega
  have hs := hstair (m - N₂)
  rw [show N₂ + (m - N₂) = m by omega] at hs
  have hs1 := hstair (m - 1 - N₂)
  rw [show N₂ + (m - 1 - N₂) = m - 1 by omega] at hs1
  have hDbm : bnat m ≤ D * bnat m := Nat.le_mul_of_pos_left _ hD
  refine ⟨D * bnat m, by omega, ?_, ?_⟩
  · refine hN₁ m (by omega) G (fun k hk => ?_) hmne
    obtain ⟨n, hn, he⟩ := hsupp k hk
    exact ⟨n, le_trans (le_max_left N₁ N₂) hn, he⟩
  · intro k hk1 hk2
    by_contra hkne
    obtain ⟨e, hene, hesum⟩ := exists_rep_of_coeff_pow_ne_zero hkne
    choose t hNt hbt using fun i => hsupp _ (hene i)
    have hNt2 : ∀ i, N₂ ≤ t i := fun i => le_trans (le_max_right N₁ N₂) (hNt i)
    have hksum : (∑ i, bnat (t i)) = k := by
      have h1 : ∀ i ∈ Finset.univ, bnat (t i) = e i := fun i _ => (hbt i).symm
      rw [Finset.sum_congr rfl h1]
      exact hesum
    have hall_le : ∀ i, t i ≤ m := by
      intro i
      by_contra hgt
      push Not at hgt
      have hb1 : bnat (m + 1) ≤ bnat (t i) := hmono (m + 1) (by omega) (t i) hgt
      have hb2 : D * bnat m < bnat (m + 1) := hjumpD m hmN₂
      have hb3 : bnat (t i) ≤ ∑ j, bnat (t j) :=
        Finset.single_le_sum (f := fun j => bnat (t j)) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega
    by_cases hbal : ∀ i, t i = m
    · have hkD : k = D * bnat m := by
        rw [← hksum, Finset.sum_congr rfl fun i _ => by rw [hbal i], Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    · push Not at hbal
      obtain ⟨i₀, hi₀⟩ := hbal
      have hi₀m : t i₀ ≤ m - 1 := by
        have := hall_le i₀
        omega
      have hsplit : bnat (t i₀) + ∑ i ∈ Finset.univ.erase i₀, bnat (t i)
          = ∑ i, bnat (t i) :=
        Finset.add_sum_erase _ (fun i => bnat (t i)) (Finset.mem_univ i₀)
      have herase : (∑ i ∈ Finset.univ.erase i₀, bnat (t i))
          ≤ (Finset.univ.erase i₀).card • bnat m :=
        Finset.sum_le_card_nsmul _ _ _ fun i _ => hmono (t i) (hNt2 i) m (hall_le i)
      rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
        Fintype.card_fin, smul_eq_mul] at herase
      have hi₀le : bnat (t i₀) ≤ bnat (m - 1) := hmono (t i₀) (hNt2 i₀) (m - 1) hi₀m
      have hsep : bnat (m - 1) + g < bnat m := by
        have hc := hcast (m - 1) hm1N₂
        rw [show m - 1 + 1 = m by omega] at hc
        have h2 : 2 * bnat (m - 1) ≤ (D + 1) * bnat (m - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hDm : (D - 1) * bnat m + bnat m = D * bnat m := by
        cases D with
        | zero => omega
        | succ d => simp [Nat.succ_mul]
      omega

end GaloisForLFunctions

namespace GaloisForLFunctions

open Filter PowerSeries

/-- Threshold package for a divergent-ratio integer exponent sequence: past `N₂` the
sequence is positive, grows by the factor `C + 2` at each step, is monotone, and dominates
the staircase `bnat N₂ + j` — the quantitative tail regularity every lacunary-support
argument consumes. -/
theorem exists_gap_threshold {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop) (C : ℕ) :
    ∃ N₂ : ℕ, (∀ n, N₂ ≤ n → 0 < bnat n) ∧
      (∀ n, N₂ ≤ n → (C + 2) * bnat n ≤ bnat (n + 1)) ∧
      (∀ a, N₂ ≤ a → ∀ c, a ≤ c → bnat a ≤ bnat c) ∧
      (∀ j, bnat N₂ + j ≤ bnat (N₂ + j)) := by
  have hCge : ∀ᶠ n in atTop, ((C : ℝ) + 2) ≤ (bnat (n + 1) : ℝ) / (bnat n : ℝ) :=
    hratio.eventually_ge_atTop _
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hpos.and hCge)
  have hbpos : ∀ n, N₂ ≤ n → 0 < bnat n := fun n hn => (hN₂ n hn).1
  have hcast : ∀ n, N₂ ≤ n → (C + 2) * bnat n ≤ bnat (n + 1) := by
    intro n hn
    obtain ⟨hb, hr⟩ := hN₂ n hn
    have hbR : (0 : ℝ) < (bnat n : ℝ) := by exact_mod_cast hb
    rw [le_div_iff₀ hbR] at hr
    have hR : (((C + 2) * bnat n : ℕ) : ℝ) ≤ ((bnat (n + 1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have hmono1 : ∀ n, N₂ ≤ n → bnat n < bnat (n + 1) := by
    intro n hn
    have h1 := hcast n hn
    have hb := hbpos n hn
    have h2 : 2 * bnat n ≤ (C + 2) * bnat n := Nat.mul_le_mul_right _ (by omega)
    omega
  have hmono : ∀ a, N₂ ≤ a → ∀ c, a ≤ c → bnat a ≤ bnat c := by
    intro a ha c
    induction c with
    | zero =>
      intro h
      have ha0 : a = 0 := Nat.le_zero.mp h
      rw [ha0]
    | succ c ihc =>
      intro h
      rcases Nat.lt_or_ge a (c + 1) with hlt | hge
      · have h1 := ihc (by omega)
        have h2 : bnat c < bnat (c + 1) := hmono1 c (by omega)
        omega
      · have he : a = c + 1 := by omega
        rw [he]
  refine ⟨N₂, hbpos, hcast, hmono, ?_⟩
  intro j
  induction j with
  | zero => simp
  | succ j ihj =>
    have h2 : bnat (N₂ + j) < bnat (N₂ + j + 1) := hmono1 _ (by omega)
    show bnat N₂ + (j + 1) ≤ bnat (N₂ + j + 1)
    omega

/-- **No polynomial relation for superlacunary gap series**: a power series supported on
the tail of a divergent-ratio integer exponent sequence, with infinitely many nonzero
exponent coefficients, annihilates no nontrivial polynomial vector — `∑ⱼ pⱼ·Gʲ ≠ 0`
whenever the top polynomial is nonzero.  Probing the coefficient at `τ + d·bnat m` for `m`
deep enough (`τ` the trailing degree of the top polynomial), lower powers cannot reach the
probe exponent at all, and inside the top power every non-balanced exponent tuple
undershoots it; the single survivor `trailingCoeff(p_d)·(coeff (bnat m) G)^d` is nonzero.
The series is therefore transcendental over the polynomial ring. -/
theorem gap_series_no_polynomial_relation {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop)
    {N₀ : ℕ} {G : ℂ⟦X⟧}
    (hsupp : ∀ k, PowerSeries.coeff k G ≠ 0 → ∃ n, N₀ ≤ n ∧ k = bnat n)
    (hinf : ∀ M, ∃ m, M ≤ m ∧ PowerSeries.coeff (bnat m) G ≠ 0)
    (d : ℕ) (p : Fin (d + 1) → Polynomial ℂ) (hpd : p (Fin.last d) ≠ 0) :
    (∑ j : Fin (d + 1), (p j : ℂ⟦X⟧) * G ^ (j : ℕ)) ≠ 0 := by
  intro heq
  obtain ⟨N₂, hbpos, hcast, hmono, hstair⟩ := exists_gap_threshold hpos hratio d
  set Δ : ℕ := Finset.univ.sup (fun j : Fin (d + 1) => (p j).natDegree) with hΔdef
  set τ : ℕ := (p (Fin.last d)).natTrailingDegree with hτdef
  set B₀ : ℕ := (Finset.range N₂).sup bnat with hB₀def
  obtain ⟨m, hm, hmne⟩ := hinf (N₂ + B₀ + Δ + τ + 2)
  have hs := hstair (m - N₂)
  rw [show N₂ + (m - N₂) = m by omega] at hs
  have hs1 := hstair (m - 1 - N₂)
  rw [show N₂ + (m - 1 - N₂) = m - 1 by omega] at hs1
  have hbm : B₀ + Δ + τ + 2 ≤ bnat m := by omega
  have hbm1 : Δ + τ + 1 ≤ bnat (m - 1) := by omega
  have hjump : (d + 2) * bnat m ≤ bnat (m + 1) := hcast m (by omega)
  have hjump1 : (d + 2) * bnat (m - 1) ≤ bnat m := by
    have hc := hcast (m - 1) (by omega)
    rwa [show m - 1 + 1 = m by omega] at hc
  have hd2 : (d + 2) * bnat m = d * bnat m + 2 * bnat m := by rw [Nat.add_mul]
  have hd21 : (d + 2) * bnat (m - 1) = d * bnat (m - 1) + 2 * bnat (m - 1) := by
    rw [Nat.add_mul]
  set K : ℕ := τ + d * bnat m with hKdef
  have hval : ∀ k, PowerSeries.coeff k G ≠ 0 → k ≤ K → k ≤ bnat m := by
    intro k hk hkK
    obtain ⟨n, hn, he⟩ := hsupp k hk
    rcases Nat.lt_or_ge n N₂ with hsm | hlg
    · have hB : bnat n ≤ B₀ := Finset.le_sup (Finset.mem_range.mpr hsm)
      omega
    · rcases Nat.lt_or_ge m n with hgt | hle
      · exfalso
        have h1 : bnat (m + 1) ≤ bnat n := hmono (m + 1) (by omega) n hgt
        omega
      · have h1 : bnat n ≤ bnat m := hmono n hlg m hle
        omega
  have hval2 : ∀ k, PowerSeries.coeff k G ≠ 0 → k ≤ K → k ≠ bnat m →
      k + Δ + τ < bnat m := by
    intro k hk hkK hkne
    obtain ⟨n, hn, he⟩ := hsupp k hk
    rcases Nat.lt_or_ge n N₂ with hsm | hlg
    · have hB : bnat n ≤ B₀ := Finset.le_sup (Finset.mem_range.mpr hsm)
      omega
    · have hnm : n ≤ m := by
        by_contra hgt
        push Not at hgt
        have h1 : bnat (m + 1) ≤ bnat n := hmono (m + 1) (by omega) n hgt
        omega
      have hnm' : n ≤ m - 1 := by
        rcases Nat.lt_or_ge n m with h | h
        · omega
        · exfalso
          have hnm2 : n = m := by omega
          rw [hnm2] at he
          exact hkne he
      have h1 : bnat n ≤ bnat (m - 1) := hmono n hlg (m - 1) hnm'
      omega
  have huniq : ∀ e : Fin d → ℕ, (∀ i, PowerSeries.coeff (e i) G ≠ 0) →
      (∑ i, e i) = d * bnat m → ∀ i, e i = bnat m := by
    intro e he hesum
    have hle : ∀ i, e i ≤ bnat m := by
      intro i
      have h1 : e i ≤ ∑ i', e i' :=
        Finset.single_le_sum (f := e) (fun i' _ => Nat.zero_le _) (Finset.mem_univ i)
      exact hval (e i) (he i) (by omega)
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne
    have h2 := hval2 (e i₀) (he i₀) (by
      have h1 : e i₀ ≤ ∑ i', e i' :=
        Finset.single_le_sum (f := e) (fun i' _ => Nat.zero_le _) (Finset.mem_univ i₀)
      omega) hi₀
    have hsplit : e i₀ + ∑ i ∈ Finset.univ.erase i₀, e i = ∑ i, e i :=
      Finset.add_sum_erase _ e (Finset.mem_univ i₀)
    have herase : (∑ i ∈ Finset.univ.erase i₀, e i)
        ≤ (Finset.univ.erase i₀).card • bnat m :=
      Finset.sum_le_card_nsmul _ _ _ fun i _ => hle i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at herase
    have hdm : (d - 1) * bnat m + bnat m = d * bnat m := by
      have hd1 : 0 < d := i₀.pos
      cases d with
      | zero => omega
      | succ d' => simp [Nat.succ_mul]
    omega
  have hlast_mem : Fin.last d ∈ (Finset.univ : Finset (Fin (d + 1))) := Finset.mem_univ _
  have hkill : ∀ j ∈ (Finset.univ : Finset (Fin (d + 1))), j ≠ Fin.last d →
      PowerSeries.coeff K ((p j : ℂ⟦X⟧) * G ^ (j : ℕ)) = 0 := by
    intro j _ hjne
    have hjd : (j : ℕ) < d := by
      rcases Nat.lt_or_ge (j : ℕ) d with h | h
      · exact h
      · exfalso
        apply hjne
        apply Fin.ext
        rw [Fin.val_last]
        have hjl := j.isLt
        omega
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨c, e'⟩ hce
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hce
    by_cases hpc : (p j).coeff c = 0
    · rw [Polynomial.coeff_coe, hpc, zero_mul]
    · by_cases hge : PowerSeries.coeff e' (G ^ (j : ℕ)) = 0
      · rw [hge, mul_zero]
      · exfalso
        have hcΔ : c ≤ Δ := le_trans (Polynomial.le_natDegree_of_ne_zero hpc)
          (Finset.le_sup (f := fun j : Fin (d + 1) => (p j).natDegree)
            (Finset.mem_univ j))
        obtain ⟨e, hene, hesum⟩ := exists_rep_of_coeff_pow_ne_zero hge
        have hle : ∀ i, e i ≤ bnat m := by
          intro i
          have h1 : e i ≤ ∑ i', e i' :=
            Finset.single_le_sum (f := e) (fun i' _ => Nat.zero_le _) (Finset.mem_univ i)
          exact hval (e i) (hene i) (by omega)
        have hsum_le : (∑ i, e i) ≤ (j : ℕ) * bnat m := by
          have h1 : (∑ i, e i) ≤ (Finset.univ : Finset (Fin (j : ℕ))).card • bnat m :=
            Finset.sum_le_card_nsmul _ _ _ fun i _ => hle i
          rwa [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
        have hmul : (j : ℕ) * bnat m + bnat m ≤ d * bnat m := by
          have h1 : (j : ℕ) + 1 ≤ d := hjd
          have h2 : ((j : ℕ) + 1) * bnat m ≤ d * bnat m := Nat.mul_le_mul_right _ h1
          rw [Nat.add_mul, one_mul] at h2
          exact h2
        omega
  have hlastval : PowerSeries.coeff K ((p (Fin.last d) : ℂ⟦X⟧) * G ^ ((Fin.last d) : ℕ))
      = (p (Fin.last d)).coeff τ * (PowerSeries.coeff (bnat m) G) ^ d := by
    rw [Fin.val_last]
    rw [PowerSeries.coeff_mul]
    have hmem : ((τ, d * bnat m) : ℕ × ℕ) ∈
        Finset.HasAntidiagonal.antidiagonal K := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [Finset.sum_eq_single_of_mem _ hmem ?_]
    · rw [Polynomial.coeff_coe,
        coeff_pow_unique_rep (E := {k | PowerSeries.coeff k G ≠ 0}) (fun k hk => hk) huniq]
    · rintro ⟨c, e'⟩ hce hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hce
      by_cases hpc : (p (Fin.last d)).coeff c = 0
      · rw [Polynomial.coeff_coe, hpc, zero_mul]
      · by_cases hge : PowerSeries.coeff e' (G ^ d) = 0
        · rw [hge, mul_zero]
        · exfalso
          have hcτ : τ ≤ c := by
            by_contra hlt
            push Not at hlt
            exact hpc (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt)
          have hcΔ : c ≤ Δ := le_trans (Polynomial.le_natDegree_of_ne_zero hpc)
            (Finset.le_sup (f := fun j : Fin (d + 1) => (p j).natDegree)
              (Finset.mem_univ (Fin.last d)))
          obtain ⟨e, hene, hesum⟩ := exists_rep_of_coeff_pow_ne_zero hge
          have hle : ∀ i, e i ≤ bnat m := by
            intro i
            have h1 : e i ≤ ∑ i', e i' :=
              Finset.single_le_sum (f := e) (fun i' _ => Nat.zero_le _)
                (Finset.mem_univ i)
            exact hval (e i) (hene i) (by omega)
          by_cases hball : ∀ i, e i = bnat m
          · apply hne
            have he' : e' = d * bnat m := by
              rw [← hesum, Finset.sum_congr rfl fun i _ => by rw [hball i],
                Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            have hcτ' : c = τ := by omega
            rw [hcτ', he']
          · push Not at hball
            obtain ⟨i₀, hi₀⟩ := hball
            have h2 := hval2 (e i₀) (hene i₀) (by
              have h1 : e i₀ ≤ ∑ i', e i' :=
                Finset.single_le_sum (f := e) (fun i' _ => Nat.zero_le _)
                  (Finset.mem_univ i₀)
              omega) hi₀
            have hsplit : e i₀ + ∑ i ∈ Finset.univ.erase i₀, e i = ∑ i, e i :=
              Finset.add_sum_erase _ e (Finset.mem_univ i₀)
            have herase : (∑ i ∈ Finset.univ.erase i₀, e i)
                ≤ (Finset.univ.erase i₀).card • bnat m :=
              Finset.sum_le_card_nsmul _ _ _ fun i _ => hle i
            rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
              Fintype.card_fin, smul_eq_mul] at herase
            have hdm : (d - 1) * bnat m + bnat m = d * bnat m := by
              have hd1 : 0 < d := i₀.pos
              cases d with
              | zero => omega
              | succ d' => simp [Nat.succ_mul]
            omega
  have hcoeffK := congrArg (PowerSeries.coeff K) heq
  rw [map_sum, map_zero] at hcoeffK
  have hsum_eq : (∑ j : Fin (d + 1), PowerSeries.coeff K ((p j : ℂ⟦X⟧) * G ^ (j : ℕ)))
      = (p (Fin.last d)).coeff τ * (PowerSeries.coeff (bnat m) G) ^ d := by
    rw [Finset.sum_eq_single_of_mem (Fin.last d) hlast_mem hkill]
    exact hlastval
  rw [hsum_eq] at hcoeffK
  have htc : (p (Fin.last d)).coeff τ ≠ 0 := fun h0 =>
    hpd (Polynomial.trailingCoeff_eq_zero.mp h0)
  exact (mul_ne_zero htc (pow_ne_zero d hmne)) hcoeffK

end GaloisForLFunctions
