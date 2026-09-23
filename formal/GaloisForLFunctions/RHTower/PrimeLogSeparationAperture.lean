import GaloisForLFunctions.RHTower.PrimeBarycentricCoefficientDivergence

/-!
# Exact prime-log separation and the aperture it forces

Distinct integers `m ≠ n` in `[1, N]` have logarithms separated by at least `1/N`, and the pair
`(N-1, N)` shows the exponent is exact.  In the other direction, `k` frequencies confined to an
interval of length `L` always contain a pair at distance at most `L/(k-1)`, so the prime logarithms
below `x` contain a pair separated by at most `log x / (π(x) - 1)`.

Consequently any uniform-gap Gram criterion of the form "aperture at least the number of
frequencies divided by their minimal separation" forces, for the prime-log family below `x`, an
aperture of at least `π(x)(π(x) - 1)/log x`.  Chebyshev's bound `π(x) ≥ θ(x)/log x` makes this
larger than `x` itself for all large `x`: at the mass caustic `x = e^H` the required aperture is
exponential in the vertical parameter, so a global mean-value estimate cannot be localized without
paying an exponential constant.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## Pigeonhole in an interval -/

/-- **Among `k` values in an interval of length `L` two distinct indices carry values at distance
at most `L/(k-1)`.** -/
theorem exists_pair_dist_le {ι : Type*} {S : Finset ι} {φ : ι → ℝ} {a b : ℝ}
    (hS : ∀ i ∈ S, φ i ∈ Set.Icc a b) (hcard : 2 ≤ S.card) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ |φ i - φ j| ≤ (b - a) / ((S.card : ℝ) - 1) := by
  classical
  obtain ⟨i₀, hi₀, j₀, hj₀, hij₀⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  have hab : a ≤ b := le_trans (hS i₀ hi₀).1 (hS i₀ hi₀).2
  set n : ℕ := S.card - 1 with hndef
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hcardR : ((S.card : ℝ) - 1) = (n : ℝ) := by
    have hcast : (S.card : ℝ) = (n : ℝ) + 1 := by
      rw [hndef, Nat.cast_sub (by omega : 1 ≤ S.card)]
      norm_num
    linarith
  rcases eq_or_lt_of_le hab with heq | hlt
  · refine ⟨i₀, hi₀, j₀, hj₀, hij₀, ?_⟩
    have h1 := hS i₀ hi₀
    have h2 := hS j₀ hj₀
    have hv1 : φ i₀ = a := le_antisymm (heq ▸ h1.2) h1.1
    have hv2 : φ j₀ = a := le_antisymm (heq ▸ h2.2) h2.1
    rw [hv1, hv2, sub_self, abs_zero, ← heq, sub_self, zero_div]
  · have hLpos : (0 : ℝ) < b - a := by linarith
    set bucket : ι → ℕ := fun i => min ⌊(φ i - a) * (n : ℝ) / (b - a)⌋₊ (n - 1) with hbdef
    have hmaps : Set.MapsTo bucket (S : Set ι) ((Finset.range n : Finset ℕ) : Set ℕ) := by
      intro i _
      rw [Finset.coe_range, Set.mem_Iio]
      calc bucket i ≤ n - 1 := min_le_right _ _
        _ < n := by omega
    have hlt' : (Finset.range n).card < S.card := by
      rw [Finset.card_range]
      omega
    obtain ⟨i, hi, j, hj, hij, heqb⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt' hmaps
    refine ⟨i, hi, j, hj, hij, ?_⟩
    have hbound : ∀ k ∈ S,
        ((bucket k : ℕ) : ℝ) ≤ (φ k - a) * (n : ℝ) / (b - a)
          ∧ (φ k - a) * (n : ℝ) / (b - a) ≤ ((bucket k : ℕ) : ℝ) + 1 := by
      intro k hk
      have hmem := hS k hk
      have hu0 : (0 : ℝ) ≤ (φ k - a) * (n : ℝ) / (b - a) := by
        have : (0 : ℝ) ≤ φ k - a := by linarith [hmem.1]
        positivity
      have hun : (φ k - a) * (n : ℝ) / (b - a) ≤ (n : ℝ) := by
        rw [div_le_iff₀ hLpos]
        have hle : φ k - a ≤ b - a := by linarith [hmem.2]
        nlinarith
      refine ⟨?_, ?_⟩
      · have hmin : ((bucket k : ℕ) : ℝ) ≤ ((⌊(φ k - a) * (n : ℝ) / (b - a)⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast min_le_left (⌊(φ k - a) * (n : ℝ) / (b - a)⌋₊) (n - 1)
        exact le_trans hmin (Nat.floor_le hu0)
      · by_cases hcase : ⌊(φ k - a) * (n : ℝ) / (b - a)⌋₊ ≤ n - 1
        · have hb : bucket k = ⌊(φ k - a) * (n : ℝ) / (b - a)⌋₊ := min_eq_left hcase
          rw [hb]
          exact le_of_lt (Nat.lt_floor_add_one _)
        · have hb : bucket k = n - 1 := min_eq_right (by omega)
          rw [hb]
          have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
            rw [Nat.cast_sub hn1]
            norm_num
          rw [hcast]
          exact hun
    obtain ⟨hi1, hi2⟩ := hbound i hi
    obtain ⟨hj1, hj2⟩ := hbound j hj
    rw [heqb] at hi1 hi2
    have hdiff : |(φ i - a) * (n : ℝ) / (b - a) - (φ j - a) * (n : ℝ) / (b - a)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hrewrite : (φ i - a) * (n : ℝ) / (b - a) - (φ j - a) * (n : ℝ) / (b - a)
        = (φ i - φ j) * (n : ℝ) / (b - a) := by
      field_simp
      ring
    rw [hrewrite, abs_div, abs_mul, abs_of_pos hLpos, abs_of_pos hnR,
      div_le_one hLpos] at hdiff
    rw [hcardR, le_div_iff₀ hnR]
    linarith

/-! ## Exact integer separation of logarithms -/

/-- The exact one-step logarithmic increment bound. -/
theorem log_succ_sub_log_ge {m : ℕ} (hm : 1 ≤ m) :
    1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hdiv : Real.log ((m : ℝ) / ((m : ℝ) + 1)) ≤ (m : ℝ) / ((m : ℝ) + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hmpos) (ne_of_gt hm1)] at hdiv
  have hval : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by
    field_simp
    ring
  rw [hval] at hdiv
  linarith

/-- **(24.22)** Distinct integers in `[1, N]` have logarithms separated by at least `1/N`, in the
ordered form. -/
theorem log_separation_of_lt {N m n : ℕ} (hm : 1 ≤ m) (hnN : n ≤ N) (hlt : m < n) :
    1 / (N : ℝ) ≤ Real.log n - Real.log m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hmn : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
  have hmono : Real.log ((m : ℝ) + 1) ≤ Real.log n := Real.log_le_log hm1 hmn
  have hstep := log_succ_sub_log_ge hm
  have hmNR : (m : ℝ) + 1 ≤ (N : ℝ) := le_trans hmn (by exact_mod_cast hnN)
  have hinv : 1 / (N : ℝ) ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le hm1 hmNR
  linarith

/-- **(24.22)** Distinct integers in `[1, N]` have logarithms separated by at least `1/N`. -/
theorem log_separation {N m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmN : m ≤ N) (hnN : n ≤ N)
    (hmn : m ≠ n) : 1 / (N : ℝ) ≤ |Real.log m - Real.log n| := by
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [abs_sub_comm]
    exact le_trans (log_separation_of_lt hm hnN h) (le_abs_self _)
  · exact le_trans (log_separation_of_lt hn hmN h) (le_abs_self _)

/-- The separation exponent in (24.22) is exact: the top pair achieves it. -/
theorem log_separation_sharp {N : ℕ} (hN : 2 ≤ N) :
    Real.log N - Real.log ((N : ℝ) - 1) ≤ 1 / ((N : ℝ) - 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hpos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hstep := Real.log_le_sub_one_of_pos (x := (N : ℝ) / ((N : ℝ) - 1)) (by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hpos)] at hstep
  have hval : (N : ℝ) / ((N : ℝ) - 1) - 1 = 1 / ((N : ℝ) - 1) := by
    field_simp
    ring
  rw [hval] at hstep
  exact hstep

/-! ## The prime-log family -/

theorem log_mem_Icc_of_mem_windowPrimes {x : ℝ} (hx : 0 ≤ x) {p : ℕ}
    (hp : p ∈ windowPrimes 1 x) : Real.log p ∈ Set.Icc (0 : ℝ) (Real.log x) := by
  rw [mem_windowPrimes (by norm_num) hx] at hp
  obtain ⟨_, hp1, hpx⟩ := hp
  refine ⟨Real.log_nonneg (le_of_lt hp1), Real.log_le_log (by linarith) hpx⟩

/-- **The prime logarithms below `x` contain a pair separated by at most `log x/(π(x) - 1)`.** -/
theorem exists_primeLog_gap_le {x : ℝ} (hx : 0 ≤ x)
    (hcard : 2 ≤ (windowPrimes 1 x).card) :
    ∃ p ∈ windowPrimes 1 x, ∃ q ∈ windowPrimes 1 x, p ≠ q ∧
      |Real.log p - Real.log q| ≤ Real.log x / (((windowPrimes 1 x).card : ℝ) - 1) := by
  obtain ⟨p, hp, q, hq, hpq, hle⟩ :=
    exists_pair_dist_le (φ := fun p : ℕ => Real.log p) (a := (0 : ℝ)) (b := Real.log x)
      (fun i hi => log_mem_Icc_of_mem_windowPrimes hx hi) hcard
  refine ⟨p, hp, q, hq, hpq, ?_⟩
  rwa [sub_zero] at hle

/-- **(24.23) The aperture forced by a uniform-gap criterion.**  If every pair of prime logarithms
below `x` is separated by at least `δ`, then the ratio of the number of frequencies to `δ` is at
least `π(x)(π(x) - 1)/log x`. -/
theorem primeLogAperture_lower {x delta : ℝ} (hx : 1 < x) (hdelta : 0 < delta)
    (hcard : 2 ≤ (windowPrimes 1 x).card)
    (hsep : ∀ p ∈ windowPrimes 1 x, ∀ q ∈ windowPrimes 1 x, p ≠ q →
      delta ≤ |Real.log p - Real.log q|) :
    ((windowPrimes 1 x).card : ℝ) * (((windowPrimes 1 x).card : ℝ) - 1) / Real.log x
      ≤ ((windowPrimes 1 x).card : ℝ) / delta := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hk1 : (1 : ℝ) < ((windowPrimes 1 x).card : ℝ) := by exact_mod_cast hcard
  have hkm1 : (0 : ℝ) < ((windowPrimes 1 x).card : ℝ) - 1 := by linarith
  obtain ⟨p, hp, q, hq, hpq, hgap⟩ := exists_primeLog_gap_le (le_of_lt (by linarith : (0:ℝ) < x)) hcard
  have hdle : delta ≤ Real.log x / (((windowPrimes 1 x).card : ℝ) - 1) :=
    le_trans (hsep p hp q hq hpq) hgap
  have hkpos : (0 : ℝ) < ((windowPrimes 1 x).card : ℝ) := by linarith
  rw [div_le_div_iff₀ hlogx hdelta]
  have hstep : delta * (((windowPrimes 1 x).card : ℝ) - 1) ≤ Real.log x := by
    rw [← le_div_iff₀ hkm1]
    exact hdle
  nlinarith

/-! ## The Chebyshev count makes the aperture exponential -/

/-- Chebyshev's lower bound for the prime count below `x`. -/
theorem chebyshevPrimeLower_div_log_le_card {x : ℝ} (hx : 2 ≤ x) :
    chebyshevPrimeLower x / Real.log x ≤ ((windowPrimes 1 x).card : ℝ) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have htheta : chebyshevPrimeLower x ≤ Chebyshev.theta x := by
    simpa [chebyshevPrimeLower] using Chebyshev.theta_ge' hx1
  have hsum : ∑ p ∈ windowPrimes 1 x, Real.log p = Chebyshev.theta x := by
    have h := sum_log_windowPrimes (x := (1 : ℝ)) (y := x) hx1
    rwa [Chebyshev.theta_one, sub_zero] at h
  have hterm : ∀ p ∈ windowPrimes 1 x, Real.log p ≤ Real.log x := fun p hp =>
    (log_mem_Icc_of_mem_windowPrimes (by linarith) hp).2
  have hcount : Chebyshev.theta x ≤ ((windowPrimes 1 x).card : ℝ) * Real.log x := by
    rw [← hsum]
    calc ∑ p ∈ windowPrimes 1 x, Real.log p
        ≤ ∑ _p ∈ windowPrimes 1 x, Real.log x := Finset.sum_le_sum hterm
      _ = ((windowPrimes 1 x).card : ℝ) * Real.log x := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [div_le_iff₀ hlogx]
  linarith

/-- The Chebyshev aperture profile. -/
def primeLogApertureBound (x : ℝ) : ℝ :=
  chebyshevPrimeLower x / Real.log x * (chebyshevPrimeLower x / Real.log x - 1) / Real.log x

theorem tendsto_primeLogApertureBound_div_id :
    Tendsto (fun x : ℝ => primeLogApertureBound x / x) atTop atTop := by
  have hinner : Tendsto
      (fun x : ℝ => -(1 / Real.log x ^ (2 : ℕ)) + chebyshevPrimeLower x / Real.log x ^ (3 : ℕ))
      atTop atTop := by
    have hzero : Tendsto (fun x : ℝ => -(1 / Real.log x ^ (2 : ℕ))) atTop (nhds 0) := by
      have hlog : Tendsto (fun x : ℝ => Real.log x ^ (2 : ℕ)) atTop atTop :=
        (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
      simpa using (hlog.inv_tendsto_atTop).neg
    exact hzero.add_atTop tendsto_chebyshevPrimeLower_div_log_cube_atTop
  have hmain := tendsto_chebyshevPrimeLower_div_id.pos_mul_atTop
    (Real.log_pos (by norm_num)) hinner
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  rw [primeLogApertureBound]
  field_simp
  ring

/-- **(24.23) The forced aperture eventually exceeds the whole frequency range.**  At the mass
caustic `x = e^H` this is an aperture exponential in the vertical parameter. -/
theorem eventually_le_primeLogApertureBound :
    ∀ᶠ x : ℝ in atTop, x ≤ primeLogApertureBound x := by
  have hlim := tendsto_primeLogApertureBound_div_id
  filter_upwards [hlim.eventually_ge_atTop 1, eventually_gt_atTop (0 : ℝ)] with x hge hpos
  rw [le_div_iff₀ hpos, one_mul] at hge
  exact hge

end

end RHTower
