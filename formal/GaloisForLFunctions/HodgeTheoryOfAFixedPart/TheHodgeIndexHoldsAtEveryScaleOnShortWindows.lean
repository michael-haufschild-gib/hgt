import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheNormalFormOfThePairingOfTheDegreePoints

/-!
# The Hodge index holds at every scale on short windows

The inequality of Castelnuovo and Severi `D·D ≤ 2 d₁ d₂` is proved in the corpus in the limit, on
the samples of a packet `f ∈ C²_c`. In the normal form it is a statement on real vectors at one
scale. This file proves it there, on windows of ratio at most `19/18`:

for every `N`, every `M` with `18 M ≤ N`, every set `S` of degree points in `(N, N + M]` and
every real divisor `D = Σ_{n ∈ S} c_n γ_n`,

  `2 d₁ d₂ − D·D ≥ (1/50) Σ c_n²`   (`combForm_ge_of_short`),

with no smoothness of `c` and no limit in `N`. The proof has three steps.

* **No contacts** (`contact_eq_zero_of_window`): two distinct degree points of a window of
  ratio at most `2` do not divide each other.
* **The potential is negative** (`combPotential_le_of_short`): the row of the jets at a point of
  the window is at most `H_M + M/(4N)`, and `H_M ≤ 1 + log M` is below the counterterm
  `log(N/2π)` by `log(9/π) − 1`. By Zariski's lemma the pairing is negative definite:
  `D·D ≤ −(1/40) Σ c_n²` (`combPairing_le_of_short`). No positive square lies in the span of the
  graphs of a short window.
* **The pole plane is almost nonnegative** (`neg_le_two_mul_degOne_mul_degTwo`): on a window
  the two degrees are proportional up to the ratio of the window, so
  `2 d₁ d₂ ≥ −(M³/(2N³)) Σ c_n²`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-! ### No contacts in a window of ratio at most two -/

/-- Two distinct degree points of a window of ratio at most `2` are not in contact. -/
theorem contact_eq_zero_of_window {N M m n : ℕ} (hM : M ≤ N) (hm : m ∈ Ioc N (N + M))
    (hn : n ∈ Ioc N (N + M)) (hmn : m ≠ n) : contact m n = 0 := by
  obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have key : ∀ a b : ℕ, N < a → N < b → b ≤ N + M → a ≠ b → ¬ a ∣ b := by
    rintro a b ha hb hb2 hab ⟨k, rfl⟩
    have hk1 : k ≠ 1 := fun h => hab (by rw [h, mul_one])
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have h2 : a * 2 ≤ a * k := Nat.mul_le_mul_left a (by omega)
    omega
  rw [contact, if_neg (key m n hm1 hn1 hn2 hmn), if_neg (key n m hn1 hm1 hm2 (Ne.symm hmn)),
    add_zero]

/-! ### The row of the jets in a window -/

/-- Reciprocals of distinct positive distances below `M` sum to at most `H_M`. -/
theorem sum_inv_le_harm {M : ℕ} (T : Finset ℕ) (φ : ℕ → ℕ) (hφ : ∀ m ∈ T, φ m < M)
    (hinj : ∀ x ∈ T, ∀ y ∈ T, φ x = φ y → x = y) :
    ∑ m ∈ T, 1 / ((φ m : ℝ) + 1) ≤ harm M := by
  rw [← Finset.sum_image (f := fun k : ℕ => 1 / ((k : ℝ) + 1)) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => by positivity
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
  exact Finset.mem_range.mpr (hφ m hm)

/-- The singular part of the row of the jets at a point of a window of `M` degree points is at
most `2 H_M`. -/
theorem sum_inv_abs_sub_erase_le {N M : ℕ} {S : Finset ℕ} (hS : S ⊆ Ioc N (N + M)) {n : ℕ}
    (hn : n ∈ S) : ∑ m ∈ S.erase n, 1 / |(m : ℝ) - n| ≤ 2 * harm M := by
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp (hS hn)
  rw [← Finset.sum_filter_add_sum_filter_not (S.erase n) (· < n)]
  have hlow : ∑ m ∈ (S.erase n).filter (· < n), 1 / |(m : ℝ) - n| ≤ harm M := by
    have hterm : ∀ m ∈ (S.erase n).filter (· < n),
        1 / |(m : ℝ) - n| = 1 / (((n - m - 1 : ℕ) : ℝ) + 1) := by
      intro m hm
      have hlt : m < n := (Finset.mem_filter.mp hm).2
      have hlt' : (m : ℝ) < n := by exact_mod_cast hlt
      rw [abs_of_neg (by linarith), Nat.cast_sub (by omega), Nat.cast_sub hlt.le]
      push_cast
      ring_nf
    rw [Finset.sum_congr rfl hterm]
    refine sum_inv_le_harm _ (fun m => n - m - 1) (fun m hm => ?_) fun x hx y hy hxy => ?_
    · have hlt : m < n := (Finset.mem_filter.mp hm).2
      have hmS := (Finset.mem_Ioc.mp
        (hS (Finset.mem_of_mem_erase (Finset.mem_filter.mp hm).1))).1
      omega
    · have hx' : x < n := (Finset.mem_filter.mp hx).2
      have hy' : y < n := (Finset.mem_filter.mp hy).2
      omega
  have hhigh : ∑ m ∈ (S.erase n).filter (fun m => ¬ m < n), 1 / |(m : ℝ) - n| ≤ harm M := by
    have hgt : ∀ m ∈ (S.erase n).filter (fun m => ¬ m < n), n < m := fun m hm => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hm
      exact lt_of_le_of_ne (not_lt.mp h2) (Ne.symm (Finset.ne_of_mem_erase h1))
    have hterm : ∀ m ∈ (S.erase n).filter (fun m => ¬ m < n),
        1 / |(m : ℝ) - n| = 1 / (((m - n - 1 : ℕ) : ℝ) + 1) := by
      intro m hm
      have hlt : n < m := hgt m hm
      have hlt' : (n : ℝ) < m := by exact_mod_cast hlt
      rw [abs_of_pos (by linarith), Nat.cast_sub (by omega), Nat.cast_sub hlt.le]
      push_cast
      ring_nf
    rw [Finset.sum_congr rfl hterm]
    refine sum_inv_le_harm _ (fun m => m - n - 1) (fun m hm => ?_) fun x hx y hy hxy => ?_
    · have hlt : n < m := hgt m hm
      have hmS := (Finset.mem_Ioc.mp
        (hS (Finset.mem_of_mem_erase (Finset.mem_filter.mp hm).1))).2
      omega
    · have hx' : n < x := hgt x hx
      have hy' : n < y := hgt y hy
      omega
  linarith

/-- **The row of the jets in a window**: at most `H_M + M/(4N)`. -/
theorem sum_jetKernel_erase_le {N M : ℕ} (hN : 0 < N) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) {n : ℕ} (hn : n ∈ S) :
    ∑ m ∈ S.erase n, jetKernel m n ≤ harm M + M / (4 * N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (N : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1
  have hcard : ((S.erase n).card : ℝ) ≤ M := by
    have h1 : (S.erase n).card ≤ S.card := Finset.card_le_card (Finset.erase_subset n S)
    have h2 : S.card ≤ (Ioc N (N + M)).card := Finset.card_le_card hS
    rw [Nat.card_Ioc] at h2
    exact_mod_cast (by omega : (S.erase n).card ≤ M)
  have hreg : ∑ m ∈ S.erase n, 1 / ((m : ℝ) + n) ≤ M / (2 * N) := by
    calc ∑ m ∈ S.erase n, 1 / ((m : ℝ) + n)
        ≤ ∑ _m ∈ S.erase n, 1 / (2 * (N : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm1 : (N : ℝ) < m := by
            exact_mod_cast (Finset.mem_Ioc.mp (hS (Finset.mem_of_mem_erase hm))).1
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = (S.erase n).card * (1 / (2 * (N : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * (1 / (2 * (N : ℝ))) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = M / (2 * N) := by ring
  have hsplit : ∑ m ∈ S.erase n, jetKernel m n =
      (∑ m ∈ S.erase n, 1 / |(m : ℝ) - n| + ∑ m ∈ S.erase n, 1 / ((m : ℝ) + n)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    rfl
  rw [hsplit]
  have hsing := sum_inv_abs_sub_erase_le hS hn
  have e : (M : ℝ) / (4 * N) = M / (2 * N) / 2 := by ring
  rw [e]
  linarith

/-! ### The numerical margin -/

/-- `log(9/π) ≥ 1 + 1/72 + 1/40`: the counterterm of a window of ratio `19/18` exceeds the row of
its jets. -/
theorem log_nine_div_pi_ge : 1 + 1 / 72 + 1 / 40 ≤ Real.log (9 / Real.pi) := by
  have hπ : Real.pi < 3.15 := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hx : Real.exp (1 / 72 + 1 / 40) ≤ 1 / (1 - (1 / 72 + 1 / 40)) := by
    have h := Real.add_one_le_exp (-(1 / 72 + 1 / 40 : ℝ))
    rw [Real.exp_neg] at h
    have hpos : 0 < Real.exp (1 / 72 + 1 / 40) := Real.exp_pos _
    rw [le_div_iff₀ (by norm_num)]
    have h' : (1 - (1 / 72 + 1 / 40 : ℝ)) ≤ (Real.exp (1 / 72 + 1 / 40))⁻¹ := by linarith
    calc Real.exp (1 / 72 + 1 / 40) * (1 - (1 / 72 + 1 / 40))
        ≤ Real.exp (1 / 72 + 1 / 40) * (Real.exp (1 / 72 + 1 / 40))⁻¹ :=
          mul_le_mul_of_nonneg_left h' hpos.le
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  rw [Real.le_log_iff_exp_le (by positivity), show (1 : ℝ) + 1 / 72 + 1 / 40 =
    1 + (1 / 72 + 1 / 40) by ring, Real.exp_add]
  have h9 : (2.857 : ℝ) < 9 / Real.pi := by
    rw [lt_div_iff₀ hπ0]
    nlinarith
  have hprod : Real.exp 1 * Real.exp (1 / 72 + 1 / 40) ≤
      2.7182818286 * (1 / (1 - (1 / 72 + 1 / 40))) :=
    mul_le_mul he.le hx (Real.exp_pos _).le (by norm_num)
  have hnum : (2.7182818286 : ℝ) * (1 / (1 - (1 / 72 + 1 / 40))) ≤ 2.857 := by norm_num
  linarith

/-! ### The potential and the pairing -/

/-- **The potential of a short window is negative.** At every point of a set of degree points in
`(N, N + M]`, `18 M ≤ N`, the row of the pairing is below the counterterm by `1/40`. -/
theorem combPotential_le_of_short {N M : ℕ} (hNM : 18 * M ≤ N) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) {n : ℕ} (hn : n ∈ S) : combPotential S n ≤ -(1 / 40) := by
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp (hS hn)
  have hM : 1 ≤ M := by omega
  have hN : 0 < N := by omega
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNM' : 18 * (M : ℝ) ≤ N := by exact_mod_cast hNM
  have hnN : (N : ℝ) < n := by exact_mod_cast hn1
  -- no contacts
  have hrow : ∑ m ∈ S.erase n, pairKernel m n = ∑ m ∈ S.erase n, jetKernel m n :=
    Finset.sum_congr rfl fun m hm => by
      rw [pairKernel, contact_eq_zero_of_window (by omega) (hS (Finset.mem_of_mem_erase hm))
        (hS hn) (Finset.ne_of_mem_erase hm), add_zero]
  have hjets := sum_jetKernel_erase_le hN hS hn
  have hharm : harm M ≤ 1 + Real.log M := by
    rw [harm_eq_harmonic]
    exact harmonic_le_one_add_log M
  have hreg : (M : ℝ) / (4 * N) ≤ 1 / 72 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- the counterterm
  have hπ := Real.pi_pos
  have hct : Real.log M + Real.log (9 / Real.pi) ≤ counterterm n := by
    rw [counterterm, ← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    rw [le_div_iff₀ (by positivity)]
    have e : (M : ℝ) * (9 / Real.pi) * (2 * Real.pi) = 18 * M := by
      field_simp
      ring
    rw [e]
    linarith
  rw [combPotential, hrow]
  linarith [log_nine_div_pi_ge]

/-- **On a short window the pairing is negative definite.** For every real divisor on degree
points of `(N, N + M]`, `18 M ≤ N`: `D·D ≤ −(1/40) Σ c_n²`. -/
theorem combPairing_le_of_short {N M : ℕ} (hNM : 18 * M ≤ N) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) (c : ℕ → ℝ) :
    combPairing S c ≤ -(1 / 40) * ∑ n ∈ S, c n ^ 2 := by
  refine (combPairing_le_potential S c).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have h := combPotential_le_of_short hNM hS hn
  nlinarith [sq_nonneg (c n)]

/-! ### The pole plane on a window -/

/-- **The pole plane is almost nonnegative on a window.** For a real divisor on degree points of
`(N, N + M]`: `2 d₁ d₂ ≥ −(M³/(2N³)) Σ c_n²`. -/
theorem neg_le_two_mul_degOne_mul_degTwo {N M : ℕ} (hN : 0 < N) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) (c : ℕ → ℝ) :
    -((M : ℝ) ^ 3 / (2 * (N : ℝ) ^ 3)) * ∑ n ∈ S, c n ^ 2 ≤ 2 * (degOne S c * degTwo S c) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- the defect of proportionality of the two degrees
  set e : ℝ := ∑ n ∈ S, c n * (((n : ℝ) - N) / (n * N)) with he
  have hd1 : degOne S c = degTwo S c / N - e := by
    rw [degOne, degTwo, he, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : (0 : ℝ) < n := by
      have := (Finset.mem_Ioc.mp (hS hn)).1
      exact_mod_cast (by omega : 0 < n)
    field_simp
    ring
  -- Cauchy–Schwarz
  have hw : ∀ n ∈ S, (((n : ℝ) - N) / (n * N)) ^ 2 ≤ ((M : ℝ) / (N : ℝ) ^ 2) ^ 2 := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp (hS hn)
    have h1' : (N : ℝ) < n := by exact_mod_cast h1
    have h2' : (n : ℝ) ≤ N + M := by exact_mod_cast h2
    have h0 : 0 ≤ ((n : ℝ) - N) / (n * N) := div_nonneg (by linarith) (by positivity)
    refine pow_le_pow_left₀ h0 ?_ 2
    rw [div_le_div_iff₀ (mul_pos (by linarith) hN') (by positivity)]
    have hA : ((n : ℝ) - N) * (N : ℝ) ^ 2 ≤ M * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    nlinarith [mul_nonneg (mul_nonneg hM' hN'.le) (sub_nonneg.mpr h1'.le)]
  have hcard : (S.card : ℝ) ≤ M := by
    have h2 : S.card ≤ (Ioc N (N + M)).card := Finset.card_le_card hS
    rw [Nat.card_Ioc] at h2
    exact_mod_cast (by omega : S.card ≤ M)
  have hsumw : ∑ n ∈ S, (((n : ℝ) - N) / (n * N)) ^ 2 ≤ (M : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
    calc ∑ n ∈ S, (((n : ℝ) - N) / (n * N)) ^ 2
        ≤ ∑ _n ∈ S, ((M : ℝ) / (N : ℝ) ^ 2) ^ 2 := Finset.sum_le_sum hw
      _ = S.card * ((M : ℝ) / (N : ℝ) ^ 2) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * ((M : ℝ) / (N : ℝ) ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = (M : ℝ) ^ 3 / (N : ℝ) ^ 4 := by
        field_simp
  have hcs : e ^ 2 ≤ (∑ n ∈ S, c n ^ 2) * ((M : ℝ) ^ 3 / (N : ℝ) ^ 4) :=
    (Finset.sum_mul_sq_le_sq_mul_sq S c fun n => ((n : ℝ) - N) / (n * N)).trans
      (mul_le_mul_of_nonneg_left hsumw (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  -- `2 x²/N − 2 x e ≥ −N e²/2`
  have hsq : -(N / 2 * e ^ 2) ≤ 2 * ((degTwo S c / N - e) * degTwo S c) := by
    have h : 2 * ((degTwo S c / N - e) * degTwo S c) + N / 2 * e ^ 2 =
        2 / N * (degTwo S c - N * e / 2) ^ 2 := by
      field_simp
      ring
    have h0 : 0 ≤ 2 / (N : ℝ) * (degTwo S c - N * e / 2) ^ 2 := by positivity
    linarith
  rw [hd1]
  have hfin : (N : ℝ) / 2 * ((∑ n ∈ S, c n ^ 2) * ((M : ℝ) ^ 3 / (N : ℝ) ^ 4)) =
      (M : ℝ) ^ 3 / (2 * (N : ℝ) ^ 3) * ∑ n ∈ S, c n ^ 2 := by
    field_simp
  have hmul : (N : ℝ) / 2 * e ^ 2 ≤ (N : ℝ) / 2 *
      ((∑ n ∈ S, c n ^ 2) * ((M : ℝ) ^ 3 / (N : ℝ) ^ 4)) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  linarith

/-! ### The Hodge index at finite scale -/

/-- **Weil's form on the comb is coercive at every scale on short windows.** For every `N`,
every `M` with `18 M ≤ N`, every set `S` of degree points in `(N, N + M]` and every real divisor
on `S`: `2 d₁ d₂ − D·D ≥ (1/50) Σ c_n²`. -/
theorem combForm_ge_of_short {N M : ℕ} (hNM : 18 * M ≤ N) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) (c : ℕ → ℝ) : 1 / 50 * ∑ n ∈ S, c n ^ 2 ≤ combForm S c := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have hS0 : S = ∅ := by
      rw [← Finset.subset_empty]
      simpa using hS
    subst hS0
    simp [combForm, combPairing, degOne, degTwo]
  have hN : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hNM' : 18 * (M : ℝ) ≤ N := by exact_mod_cast hNM
  have h1 := combPairing_le_of_short hNM hS c
  have h2 := neg_le_two_mul_degOne_mul_degTwo hN hS c
  have hsum : 0 ≤ ∑ n ∈ S, c n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hratio : (M : ℝ) ^ 3 / (2 * (N : ℝ) ^ 3) ≤ 1 / 200 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h3 : (18 * (M : ℝ)) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hNM' 3
    nlinarith [pow_nonneg hM' 3]
  have h3 : (M : ℝ) ^ 3 / (2 * (N : ℝ) ^ 3) * ∑ n ∈ S, c n ^ 2 ≤
      1 / 200 * ∑ n ∈ S, c n ^ 2 := mul_le_mul_of_nonneg_right hratio hsum
  rw [combForm]
  linarith

/-- **The inequality of Castelnuovo and Severi at finite scale.** On degree points of
`(N, N + M]`, `18 M ≤ N`, every real divisor satisfies `D·D ≤ 2 d₁ d₂`. -/
theorem combPairing_le_degrees_of_short {N M : ℕ} (hNM : 18 * M ≤ N) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) (c : ℕ → ℝ) :
    combPairing S c ≤ 2 * (degOne S c * degTwo S c) := by
  have h := combForm_ge_of_short hNM hS c
  have hsum : 0 ≤ ∑ n ∈ S, c n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [combForm] at h
  linarith

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
