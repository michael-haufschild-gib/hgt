import GaloisForLFunctions.BiarithmeticGaugeGeometry.PrimeGaugeTorusAndVacuumIntertwiners

/-!
# Log-cells fix the gauge

Profiles `q : ℕ → ℂ` on the integers can be read in two ways: as point masses at `log n` (the
*lattice*) or as step functions on the logarithmic cells `I_n = [log n, log(n + 1))` (the *cells*).
Dilation by `m` acts differently:

* on the lattice, `δ_a ↦ δ_{ma}`: `(D_m q)(n) = q(n/m)` if `m ∣ n`, else `0` (`latticeDilate`);
* on cells, `I_a + log m = ⊔_{r<m} I_{am+r}`: `(M_m q)(n) = q(⌊n/m⌋)` (`cellDilate`).

Both satisfy the Baumslag–Solitar relation of the `ax + b` semigroup with the successor shift
`(S q)(n) = q(n − 1)` (`cellDilate_succShift`, `latticeDilate_succShift`), and the cell dilation is
the lattice dilation spread over the successor orbit, `M_m = Σ_{r<m} S^r D_m`
(`cellDilate_eq_sum_succShift`). Under a gauge twist `(U_ω q)(n) = χ_ω(n) q(n)`:

* the lattice dilation is covariant at **every** gauge, `U_ω D_m = χ_ω(m) D_m U_ω`
  (`gaugeTwist_latticeDilate`) — lattice forms are gauge-blind;
* the dyadic cell dilation is covariant (up to any scalar) **only at the Euler gauge**
  (`cellDilate_two_covariant_iff`): `χ(2a) = cχ(a)` and `χ(2a + 1) = cχ(a)` force `c = 1` through
  `9 = 3²`, and then `χ ≡ 1` by induction;
* on a finite horizon the same holds with an explicit reach
  (`cellDilate_two_covariant_on_horizon_iff`):
  covariance on profiles supported on `[1, X]` (`X ≥ 4`) is equivalent to `ω(p) = 1` for every
  prime `p ≤ 2X + 1`, twice the reach of successor flatness on the same horizon.

So passing from the lattice to the cells turns a blind dilation into a gauge-fixing one: the cells
carry the successor holonomy that pins the arithmetic point `𝟏 ∈ Ω_𝒫`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open BiarithmeticGaugeGeometry

/-- Cell dilation: the profile on `I_{am+r}` (`r < m`) takes the value at `a`. -/
def cellDilate (m : ℕ) (q : ℕ → ℂ) (n : ℕ) : ℂ := q (n / m)

/-- Lattice dilation: the point mass at `a` moves to `ma`. -/
def latticeDilate (m : ℕ) (q : ℕ → ℂ) (n : ℕ) : ℂ := if m ∣ n then q (n / m) else 0

/-- The successor shift `(S q)(n) = q(n − 1)`, `(S q)(0) = 0`. -/
def succShift (q : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else q (n - 1)

theorem sub_div_self_eq (n m : ℕ) : (n - m) / m = n / m - 1 := by
  simpa using Nat.sub_mul_div n m 1

theorem succShift_iterate (k : ℕ) (q : ℕ → ℂ) (n : ℕ) :
    succShift^[k] q n = if n < k then 0 else q (n - k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', succShift]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn, ih]
      by_cases hk : n - 1 < k
      · rw [if_pos hk, if_pos (by omega)]
      · rw [if_neg hk, if_neg (by omega), show n - 1 - k = n - (k + 1) by omega]

/-- **Baumslag–Solitar on cells**: `M_m S = S^m M_m`. -/
theorem cellDilate_succShift {m : ℕ} (hm : 0 < m) (q : ℕ → ℂ) :
    cellDilate m (succShift q) = succShift^[m] (cellDilate m q) := by
  funext n
  rw [succShift_iterate, cellDilate, succShift]
  by_cases hn : n < m
  · rw [Nat.div_eq_of_lt hn, if_pos rfl, if_pos hn]
  · have h1 : n / m ≠ 0 := (Nat.div_pos (by omega) hm).ne'
    rw [if_neg h1, if_neg hn, cellDilate, sub_div_self_eq]

/-- **Baumslag–Solitar on the lattice**: `D_m S = S^m D_m`. -/
theorem latticeDilate_succShift {m : ℕ} (hm : 0 < m) (q : ℕ → ℂ) :
    latticeDilate m (succShift q) = succShift^[m] (latticeDilate m q) := by
  funext n
  rw [succShift_iterate, latticeDilate, latticeDilate, succShift]
  by_cases hn : n < m
  · rw [if_pos hn]
    by_cases hd : m ∣ n
    · have hn0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hn
      subst hn0
      simp
    · rw [if_neg hd]
  · rw [if_neg hn]
    have hdvd : m ∣ n ↔ m ∣ n - m := by
      constructor
      · intro h; exact Nat.dvd_sub h (dvd_refl m)
      · intro h
        have := Nat.dvd_add h (dvd_refl m)
        rwa [Nat.sub_add_cancel (by omega)] at this
    by_cases hd : m ∣ n
    · have h1 : n / m ≠ 0 := (Nat.div_pos (by omega) hm).ne'
      rw [if_pos hd, if_pos (hdvd.mp hd), if_neg h1, sub_div_self_eq]
    · rw [if_neg hd, if_neg (fun h => hd (hdvd.mpr h))]

/-- **Cells spread the lattice over the successor orbit**: `M_m q = Σ_{r<m} S^r D_m q`. -/
theorem cellDilate_eq_sum_succShift {m : ℕ} (hm : 0 < m) (q : ℕ → ℂ) :
    cellDilate m q = ∑ r ∈ range m, succShift^[r] (latticeDilate m q) := by
  funext n
  rw [Finset.sum_apply]
  simp only [succShift_iterate, latticeDilate]
  -- Exactly the residue `r = n mod m` survives.
  rw [sum_eq_single (n % m)]
  · rw [if_neg (by have := Nat.mod_le n m; omega), if_pos (Nat.dvd_sub_mod n),
      cellDilate, Nat.div_eq_sub_mod_div]
  · intro r hr hrne
    rw [mem_range] at hr
    by_cases hnr : n < r
    · rw [if_pos hnr]
    · rw [if_neg hnr]
      by_cases hd : m ∣ n - r
      · exfalso
        apply hrne
        obtain ⟨k, hk⟩ := hd
        have hn : n = r + m * k := by omega
        rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      · rw [if_neg hd]
  · intro h
    exact absurd (mem_range.mpr (Nat.mod_lt n hm)) h

/-! ### Gauge covariance -/

/-- **Lattice dilation is covariant at every gauge**: `U_ω D_m = χ_ω(m) D_m U_ω`. -/
theorem gaugeTwist_latticeDilate (ω : PrimeGauge) (m : ℕ) (q : ℕ → ℂ) :
    gaugeTwist ω (latticeDilate m q) = ω.gaugeChar m • latticeDilate m (gaugeTwist ω q) := by
  funext n
  simp only [gaugeTwist, latticeDilate, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Nat.mul_div_cancel_left k hm, PrimeGauge.gaugeChar_mul]
      ring
  · simp

/-- At the Euler gauge the cell dilation is covariant. -/
theorem gaugeTwist_cellDilate_euler (m : ℕ) {q : ℕ → ℂ} (hq : q 0 = 0) :
    gaugeTwist PrimeGauge.eulerGauge (cellDilate m q) =
      cellDilate m (gaugeTwist PrimeGauge.eulerGauge q) := by
  funext n
  simp only [gaugeTwist, cellDilate]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [PrimeGauge.gaugeChar_euler hn, one_mul]
    by_cases hd : n / m = 0
    · rw [hd, hq, mul_zero]
    · rw [PrimeGauge.gaugeChar_euler hd, one_mul]

/-- A character with `χ(2a) = χ(2a + 1) = χ(a)` for `a ≥ 1` is identically `1` on `n ≥ 1`. -/
theorem gaugeChar_eq_one_of_halving {ω : PrimeGauge}
    (h : ∀ n, 2 ≤ n → ω.gaugeChar n = ω.gaugeChar (n / 2)) :
    ∀ n, n ≠ 0 → ω.gaugeChar n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1; exact PrimeGauge.gaugeChar_one ω
    · rw [h n (by omega)]
      exact ih (n / 2) (Nat.div_lt_self (by omega) (by norm_num)) (by omega)

/-- **The dyadic cell dilation fixes the gauge.** The cell dilation by `2` is covariant under the
gauge twist up to a scalar iff the gauge is the Euler vacuum. -/
theorem cellDilate_two_covariant_iff (ω : PrimeGauge) :
    (∃ c : ℂ, ∀ q : ℕ → ℂ, q 0 = 0 →
      gaugeTwist ω (cellDilate 2 q) = c • cellDilate 2 (gaugeTwist ω q)) ↔
      ω = PrimeGauge.eulerGauge := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    -- Test on point masses: `χ(n) = c χ(⌊n/2⌋)` for `n ≥ 2`.
    have hrel : ∀ n, 2 ≤ n → ω.gaugeChar n = c * ω.gaugeChar (n / 2) := by
      intro n hn
      have h := congrFun (hc (fun k => if k = n / 2 then 1 else 0)
        (by simp; omega)) n
      simpa [gaugeTwist, cellDilate] using h
    have h2 : ω.gaugeChar 2 = c := by simpa using hrel 2 le_rfl
    have h3 : ω.gaugeChar 3 = c := by simpa using hrel 3 (by norm_num)
    have h9 : ω.gaugeChar 9 = c * ω.gaugeChar 4 := hrel 9 (by norm_num)
    have h4 : ω.gaugeChar 4 = c ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, PrimeGauge.gaugeChar_mul, h2, sq]
    have h9' : ω.gaugeChar 9 = c ^ 2 := by
      rw [show (9 : ℕ) = 3 * 3 by rfl, PrimeGauge.gaugeChar_mul, h3, sq]
    have hc0 : c ≠ 0 := by
      rw [← h2]
      exact PrimeGauge.gaugeChar_prime ω Nat.prime_two ▸ ω.val_ne_zero 2
    have hc1 : c = 1 := by
      rw [h9', h4] at h9
      have : c ^ 2 * (c - 1) = 0 := by linear_combination -h9
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hc0
      · exact sub_eq_zero.mp h
    subst hc1
    have hone := gaugeChar_eq_one_of_halving (ω := ω) fun n hn => by rw [hrel n hn, one_mul]
    ext p
    by_cases hp : p.Prime
    · rw [← PrimeGauge.gaugeChar_prime ω hp, hone p hp.ne_zero]
      rfl
    · rw [ω.nonprime_eq_one hp]
      rfl
  · rintro rfl
    exact ⟨1, fun q hq => by rw [one_smul, gaugeTwist_cellDilate_euler 2 hq]⟩

/-! ### Finite horizons -/

/-- A profile supported on the horizon `[1, X]`. -/
def SupportedOn (q : ℕ → ℂ) (X : ℕ) : Prop := ∀ n, q n ≠ 0 → 1 ≤ n ∧ n ≤ X

/-- Halving relations up to `B` force the character to be `1` up to `B`. -/
theorem gaugeChar_eq_one_of_halving_le {ω : PrimeGauge} {B : ℕ}
    (h : ∀ n, 2 ≤ n → n ≤ B → ω.gaugeChar n = ω.gaugeChar (n / 2)) :
    ∀ n, n ≠ 0 → n ≤ B → ω.gaugeChar n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnB
    by_cases h1 : n = 1
    · subst h1; exact PrimeGauge.gaugeChar_one ω
    · rw [h n (by omega) hnB]
      exact ih (n / 2) (Nat.div_lt_self (by omega) (by norm_num)) (by omega)
        (le_trans (Nat.div_le_self n 2) hnB)

/-- If every prime up to `B` has phase `1`, the character is `1` up to `B`. -/
theorem gaugeChar_eq_one_of_primes_le {ω : PrimeGauge} {B : ℕ}
    (h : ∀ p, p.Prime → p ≤ B → ω.val p = 1) : ∀ m, m ≠ 0 → m ≤ B → ω.gaugeChar m = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hmB
    by_cases h1 : m = 1
    · subst h1; exact PrimeGauge.gaugeChar_one ω
    · have hp := Nat.minFac_prime h1
      have hdvd := Nat.minFac_dvd m
      have hpm : m.minFac ≤ m := Nat.minFac_le (by omega)
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hm hk
      have hklt : k < m := by
        rw [hk]
        exact lt_mul_left (by omega) hp.one_lt
      rw [hk, PrimeGauge.gaugeChar_mul, PrimeGauge.gaugeChar_prime ω hp, h _ hp (by omega),
        one_mul]
      exact ih k hklt hk0 (by omega)

/-- **Finite-horizon gauge fixing.** On profiles supported on `[1, X]` (`X ≥ 4`), the dyadic cell
dilation is covariant up to a scalar iff every prime `p ≤ 2X + 1` has phase `1`. A cell profile of
horizon `X` sees the primes up to `2X + 1`; successor flatness on `[1, N]` sees those up to
`N + 1` (BGG `succConn_flat_iff_primes_eq_one`). -/
theorem cellDilate_two_covariant_on_horizon_iff (ω : PrimeGauge) {X : ℕ} (hX : 4 ≤ X) :
    (∃ c : ℂ, ∀ q : ℕ → ℂ, SupportedOn q X →
      gaugeTwist ω (cellDilate 2 q) = c • cellDilate 2 (gaugeTwist ω q)) ↔
      ∀ p, p.Prime → p ≤ 2 * X + 1 → ω.val p = 1 := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    -- Point masses at `a ∈ [1, X]` give `χ(n) = c χ(⌊n/2⌋)` for `2 ≤ n ≤ 2X + 1`.
    have hrel : ∀ n, 2 ≤ n → n ≤ 2 * X + 1 → ω.gaugeChar n = c * ω.gaugeChar (n / 2) := by
      intro n hn hnX
      have h := congrFun (hc (fun k => if k = n / 2 then 1 else 0) (fun k hk => by
        by_cases hkn : k = n / 2
        · subst hkn; omega
        · simp [hkn] at hk)) n
      simpa [gaugeTwist, cellDilate] using h
    have h2 : ω.gaugeChar 2 = c := by simpa using hrel 2 le_rfl (by omega)
    have h3 : ω.gaugeChar 3 = c := by simpa using hrel 3 (by norm_num) (by omega)
    have h9 : ω.gaugeChar 9 = c * ω.gaugeChar 4 := hrel 9 (by norm_num) (by omega)
    have h4 : ω.gaugeChar 4 = c ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, PrimeGauge.gaugeChar_mul, h2, sq]
    have h9' : ω.gaugeChar 9 = c ^ 2 := by
      rw [show (9 : ℕ) = 3 * 3 by rfl, PrimeGauge.gaugeChar_mul, h3, sq]
    have hc0 : c ≠ 0 := by
      rw [← h2]
      exact PrimeGauge.gaugeChar_prime ω Nat.prime_two ▸ ω.val_ne_zero 2
    have hc1 : c = 1 := by
      rw [h9', h4] at h9
      have : c ^ 2 * (c - 1) = 0 := by linear_combination -h9
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hc0
      · exact sub_eq_zero.mp h
    subst hc1
    have hone := gaugeChar_eq_one_of_halving_le (ω := ω) (B := 2 * X + 1)
      fun n hn hnX => by rw [hrel n hn hnX, one_mul]
    intro p hp hpX
    rw [← PrimeGauge.gaugeChar_prime ω hp]
    exact hone p hp.ne_zero hpX
  · intro h
    have hone := gaugeChar_eq_one_of_primes_le h
    refine ⟨1, fun q hq => funext fun n => ?_⟩
    simp only [gaugeTwist, cellDilate, one_smul]
    by_cases hqn : q (n / 2) = 0
    · rw [hqn, mul_zero, mul_zero]
    · obtain ⟨h1, h2⟩ := hq _ hqn
      rw [hone n (by omega) (by omega), hone (n / 2) (by omega) (by omega)]

/-- **Lattice forms are blind, cell forms fix the gauge.** Every gauge commutes with the lattice
dilation up to its character value; only the Euler gauge commutes with the dyadic cell dilation. -/
theorem lattice_blind_and_cells_fix_gauge :
    (∀ (ω : PrimeGauge) (m : ℕ) (q : ℕ → ℂ),
      gaugeTwist ω (latticeDilate m q) = ω.gaugeChar m • latticeDilate m (gaugeTwist ω q)) ∧
    (∀ ω : PrimeGauge, (∃ c : ℂ, ∀ q : ℕ → ℂ, q 0 = 0 →
      gaugeTwist ω (cellDilate 2 q) = c • cellDilate 2 (gaugeTwist ω q)) ↔
        ω = PrimeGauge.eulerGauge) :=
  ⟨gaugeTwist_latticeDilate, cellDilate_two_covariant_iff⟩

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
