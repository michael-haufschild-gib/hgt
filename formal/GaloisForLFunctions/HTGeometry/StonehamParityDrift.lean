import GaloisForLFunctions.HTGeometry.BinaryParityDriftExactLaws

/-!
# The Stoneham constant has no persistent parity drift

`α = Σ_{j ≥ 1} 3^{−j} 2^{−3^j}` is the model case of a constant whose binary digits are produced
by a forced doubling map with *lacunary* forcing.  For `3ᵏ ≤ 2n < 3^{k+1}`,

`4ⁿ α = 2^{2n−3ᵏ} Aₖ / 3ᵏ + tₙ`, `Aₖ = Σ_{j ≤ k} 2^{3ᵏ−3ʲ} 3^{k−j} ≡ 1 (mod 3)`,
`0 < tₙ ≤ 3^{−k−1}`,

so on this window of `3ᵏ` indices the base-4 digits of `α` are read off the orbit `4ⁱ (2Aₖ) mod 3ᵏ`,
which runs three times through the residue class `2 (mod 3)` because `4` has order `3^{k−1}`
modulo `3ᵏ` (lifting the exponent).  On that class the drift weight is almost odd under
`r ↦ 3ᵏ − r` and almost invariant under `r ↦ r + 1`, so each complete window contributes `O(1)`:

* `abs_sum_window_le` : the drift accumulated over the `k`-th window is at most `27`;
* `tendsto_drift_window_ends` : `D_α(Nₖ)/Nₖ → 0` along the window ends `Nₖ = (3^{k+1} + 1)/2`;
* `not_strongParityDriftHypothesis_stoneham` : the strong Parity-Drift Hypothesis fails for `α`.

For `π` the forcing `R(n)` of the Bailey–Crandall recursion acts at every step, so no complete
window exists; this is the mechanism that `π` lacks.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.StonehamParityDrift

/-! ### The order of `4` modulo `3ᵏ` -/

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem padicValNat_four_pow_sub_one {d : ℕ} (hd : d ≠ 0) :
    padicValNat 3 (4 ^ d - 1) = 1 + padicValNat 3 d := by
  have h := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) (by decide) (by norm_num)
    (by norm_num) (by norm_num) hd
  simpa using h

theorem three_pow_dvd_four_pow_sub_one {k : ℕ} (hk : 1 ≤ k) :
    3 ^ k ∣ 4 ^ (3 ^ (k - 1)) - 1 := by
  have h := padicValNat_four_pow_sub_one (d := 3 ^ (k - 1)) (by positivity)
  rw [padicValNat.prime_pow] at h
  have hne : 4 ^ (3 ^ (k - 1)) - 1 ≠ 0 := by
    have : 1 < 4 ^ (3 ^ (k - 1)) := Nat.one_lt_pow (by positivity) (by norm_num)
    omega
  rw [padicValNat_dvd_iff_le hne, h]
  omega

theorem not_three_pow_dvd_four_pow_sub_one {k d : ℕ} (hd0 : 0 < d) (hd : d < 3 ^ (k - 1)) :
    ¬ 3 ^ k ∣ 4 ^ d - 1 := by
  have hne : 4 ^ d - 1 ≠ 0 := by
    have : 1 < 4 ^ d := Nat.one_lt_pow hd0.ne' (by norm_num)
    omega
  rw [padicValNat_dvd_iff_le hne, padicValNat_four_pow_sub_one hd0.ne']
  have hv : 3 ^ padicValNat 3 d ≤ d := Nat.le_of_dvd hd0 pow_padicValNat_dvd
  have hlt : 3 ^ padicValNat 3 d < 3 ^ (k - 1) := lt_of_le_of_lt hv hd
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
  omega

/-- The residue class `c (mod 3)` inside `[0, 3ᵏ)`. -/
def residueClass (k c : ℕ) : Finset ℕ := (range (3 ^ k)).filter fun r => r % 3 = c

theorem card_residueClass {k c : ℕ} (hk : 1 ≤ k) (hc : c < 3) :
    #(residueClass k c) = 3 ^ (k - 1) := by
  have h := Nat.count_modEq_card (3 ^ k) (by norm_num : 0 < 3) c
  rw [Nat.count_eq_card_filter_range] at h
  have hmod : 3 ^ k % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
  have hdiv : 3 ^ k / 3 = 3 ^ (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [pow_succ]
  rw [hmod, hdiv] at h
  simp only [Nat.not_lt_zero, if_false, add_zero] at h
  rw [← h, residueClass]
  congr 1
  ext r
  simp only [mem_filter, mem_range, Nat.ModEq, Nat.mod_eq_of_lt hc]

/-- **The orbit of `4` covers a residue class exactly once per period.** -/
theorem sum_range_orbit_eq {k : ℕ} (hk : 1 ≤ k) {b : ℕ} (hb : ¬ 3 ∣ b) {M : Type*}
    [AddCommMonoid M] (F : ℕ → M) :
    ∑ i ∈ range (3 ^ (k - 1)), F (b * 4 ^ i % 3 ^ k) = ∑ r ∈ residueClass k (b % 3), F r := by
  set φ : ℕ → ℕ := fun i => b * 4 ^ i % 3 ^ k with hφ
  have hcop : Nat.Coprime (3 ^ k) b :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb)
  have hinj : Set.InjOn φ (range (3 ^ (k - 1))) := by
    intro i hi i' hi' heq
    simp only [coe_range, Set.mem_Iio, hφ] at hi hi' heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- `3ᵏ ∣ b 4ⁱ (4^{i'−i} − 1)`
      have hdvd : 3 ^ k ∣ b * 4 ^ i * (4 ^ (i' - i) - 1) := by
        have h1 : b * 4 ^ i' % 3 ^ k = b * 4 ^ i % 3 ^ k := heq.symm
        have : b * 4 ^ i * (4 ^ (i' - i) - 1) = b * 4 ^ i' - b * 4 ^ i := by
          rw [Nat.mul_sub, mul_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
        rw [this]
        exact (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
          hlt.le))).mp h1.symm
      have hcop' : Nat.Coprime (3 ^ k) (b * 4 ^ i) :=
        Nat.Coprime.mul_right hcop (Nat.Coprime.pow_right _ (Nat.Coprime.pow_left _
          (by norm_num)))
      exact not_three_pow_dvd_four_pow_sub_one (k := k) (d := i' - i) (by omega) (by omega)
        (hcop'.dvd_of_dvd_mul_left hdvd)
    · have hdvd : 3 ^ k ∣ b * 4 ^ i' * (4 ^ (i - i') - 1) := by
        have : b * 4 ^ i' * (4 ^ (i - i') - 1) = b * 4 ^ i - b * 4 ^ i' := by
          rw [Nat.mul_sub, mul_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
        rw [this]
        exact (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
          hlt.le))).mp heq.symm
      have hcop' : Nat.Coprime (3 ^ k) (b * 4 ^ i') :=
        Nat.Coprime.mul_right hcop (Nat.Coprime.pow_right _ (Nat.Coprime.pow_left _
          (by norm_num)))
      exact not_three_pow_dvd_four_pow_sub_one (k := k) (d := i - i') (by omega) (by omega)
        (hcop'.dvd_of_dvd_mul_left hdvd)
  have hsub : (range (3 ^ (k - 1))).image φ ⊆ residueClass k (b % 3) := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := mem_image.mp hr
    simp only [residueClass, mem_filter, mem_range, hφ]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega)), Nat.mul_mod, Nat.pow_mod]
    norm_num
  have heq : (range (3 ^ (k - 1))).image φ = residueClass k (b % 3) := by
    refine eq_of_subset_of_card_le hsub ?_
    rw [card_residueClass hk (Nat.mod_lt _ (by norm_num)), card_image_of_injOn hinj, card_range]
  rw [← heq, sum_image hinj]

/-! ### The drift weight on a residue class -/

/-- The drift weight `φ(q) = [q = 2] − [q = 1]` of a base-4 digit. -/
def digitWeight (q : ℤ) : ℤ := (if q = 2 then 1 else 0) - (if q = 1 then 1 else 0)

theorem abs_digitWeight_le (q : ℤ) : |digitWeight q| ≤ 1 := by
  unfold digitWeight; rw [abs_le]; constructor <;> split_ifs <;> omega

/-- The first base-4 digit `⌊4r/3ᵏ⌋` of `r/3ᵏ`. -/
noncomputable def cellDigit (k r : ℕ) : ℤ := ⌊(4 : ℝ) * r / 3 ^ k⌋

theorem cellDigit_mono (k : ℕ) {r r' : ℕ} (h : r ≤ r') : cellDigit k r ≤ cellDigit k r' := by
  unfold cellDigit
  apply Int.floor_mono
  have : (r : ℝ) ≤ r' := by exact_mod_cast h
  gcongr

theorem cellDigit_nonneg (k r : ℕ) : 0 ≤ cellDigit k r :=
  Int.floor_nonneg.mpr (by positivity)

theorem cellDigit_le_three {k r : ℕ} (hr : r < 3 ^ k) : cellDigit k r ≤ 3 := by
  unfold cellDigit
  have : (4 : ℝ) * r / 3 ^ k < 4 := by
    rw [div_lt_iff₀ (by positivity)]
    have : (r : ℝ) < 3 ^ k := by exact_mod_cast hr
    linarith
  have := Int.floor_lt.mpr (show (4 : ℝ) * r / 3 ^ k < ((4 : ℤ) : ℝ) by exact_mod_cast this)
  omega

/-- **Reflection.**  Off the multiples of `3`, `⌊4(3ᵏ − r)/3ᵏ⌋ = 3 − ⌊4r/3ᵏ⌋`. -/
theorem cellDigit_reflect {k r : ℕ} (hk : 1 ≤ k) (hr : r < 3 ^ k) (h3 : ¬ 3 ∣ r) :
    cellDigit k (3 ^ k - r) = 3 - cellDigit k r := by
  unfold cellDigit
  have hpos : (0 : ℝ) < 3 ^ k := by positivity
  have hnint : ∀ m : ℤ, (4 : ℝ) * r / 3 ^ k ≠ m := by
    intro m hm
    rw [div_eq_iff hpos.ne'] at hm
    have hm' : ((4 * r : ℕ) : ℤ) = m * 3 ^ k := by exact_mod_cast hm
    have h3dvd : (3 : ℤ) ∣ ((4 * r : ℕ) : ℤ) := by
      rw [hm']; exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) m
    have : 3 ∣ 4 * r := by exact_mod_cast h3dvd
    exact h3 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this))
  have hcast : ((3 ^ k - r : ℕ) : ℝ) = 3 ^ k - r := by push_cast [hr.le]; ring
  rw [hcast, show (4 : ℝ) * (3 ^ k - r) / 3 ^ k = 4 - 4 * r / 3 ^ k by field_simp]
  rw [Int.floor_eq_iff]
  have h1 := Int.floor_le ((4 : ℝ) * r / 3 ^ k)
  have h2 := Int.lt_floor_add_one ((4 : ℝ) * r / 3 ^ k)
  have h3' : (⌊(4 : ℝ) * r / 3 ^ k⌋ : ℝ) < 4 * r / 3 ^ k :=
    lt_of_le_of_ne h1 fun h => hnint _ h.symm
  push_cast
  constructor <;> linarith

theorem digitWeight_three_sub {q : ℤ} (h0 : 0 ≤ q) (h3 : q ≤ 3) :
    digitWeight (3 - q) = -digitWeight q := by
  unfold digitWeight
  interval_cases q <;> simp

/-- Number of digit changes along `[0, M)`. -/
theorem sum_cellDigit_changes_le (k M : ℕ) (hM : M + 1 ≤ 3 ^ k) :
    ∑ r ∈ range M, (if cellDigit k (r + 1) = cellDigit k r then (0 : ℤ) else 1) ≤ 3 := by
  have hstep : ∀ r, (if cellDigit k (r + 1) = cellDigit k r then (0 : ℤ) else 1) ≤
      cellDigit k (r + 1) - cellDigit k r := fun r => by
    have := cellDigit_mono k (show r ≤ r + 1 by omega)
    split_ifs with h <;> omega
  calc ∑ r ∈ range M, (if cellDigit k (r + 1) = cellDigit k r then (0 : ℤ) else 1)
      ≤ ∑ r ∈ range M, (cellDigit k (r + 1) - cellDigit k r) := sum_le_sum fun r _ => hstep r
    _ = cellDigit k M - cellDigit k 0 := sum_range_sub (fun r => cellDigit k r) M
    _ ≤ 3 := by
        have := cellDigit_le_three (k := k) (r := M) (by omega)
        have := cellDigit_nonneg k 0
        omega

/-- The drift weight of the point `r/3ᵏ`. -/
noncomputable def cellWeight (k r : ℕ) : ℤ := digitWeight (cellDigit k r)

/-- **The drift weight is almost balanced on a residue class.** -/
theorem abs_sum_residueClass_two_le {k : ℕ} (hk : 1 ≤ k) :
    |∑ r ∈ residueClass k 2, cellWeight k r| ≤ 3 := by
  -- reflection `r ↦ 3ᵏ − r` swaps the classes `1` and `2`
  have hrefl : ∑ r ∈ residueClass k 2, cellWeight k r =
      -∑ r ∈ residueClass k 1, cellWeight k r := by
    rw [← sum_neg_distrib]
    refine sum_nbij' (fun r => 3 ^ k - r) (fun r => 3 ^ k - r) ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [residueClass, mem_filter, mem_range] at hr ⊢
      have h3k : 3 ^ k % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
      constructor <;> omega
    · intro r hr
      simp only [residueClass, mem_filter, mem_range] at hr ⊢
      have h3k : 3 ^ k % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
      constructor <;> omega
    · intro r hr
      simp only [residueClass, mem_filter, mem_range] at hr
      omega
    · intro r hr
      simp only [residueClass, mem_filter, mem_range] at hr
      omega
    · intro r hr
      simp only [residueClass, mem_filter, mem_range] at hr
      unfold cellWeight
      rw [cellDigit_reflect hk hr.1 (by omega), digitWeight_three_sub (cellDigit_nonneg k r)
        (cellDigit_le_three hr.1), neg_neg]
  -- shift `r ↦ r + 1` maps the class `1` onto the class `2`
  have hshift : ∑ r ∈ residueClass k 2, cellWeight k r =
      ∑ r ∈ residueClass k 1, cellWeight k (r + 1) := by
    refine (sum_nbij' (fun r => r + 1) (fun r => r - 1) ?_ ?_ ?_ ?_ ?_).symm
    · intro r hr
      simp only [residueClass, mem_filter, mem_range] at hr ⊢
      have h3k : 3 ^ k % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
      constructor <;> omega
    · intro r hr
      simp only [residueClass, mem_filter, mem_range] at hr ⊢
      constructor <;> omega
    · intro r hr; simp
    · intro r hr
      simp only [residueClass, mem_filter, mem_range] at hr
      omega
    · intro r _; rfl
  have hdiff : |∑ r ∈ residueClass k 1, (cellWeight k (r + 1) - cellWeight k r)| ≤ 6 := by
    have hsub : residueClass k 1 ⊆ range (3 ^ k - 1) := by
      intro r hr
      simp only [residueClass, mem_filter, mem_range] at hr ⊢
      have h3k : 3 ^ k % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
      omega
    have hterm : ∀ r, |cellWeight k (r + 1) - cellWeight k r| ≤
        2 * (if cellDigit k (r + 1) = cellDigit k r then (0 : ℤ) else 1) := fun r => by
      unfold cellWeight
      split_ifs with h
      · rw [h, sub_self, abs_zero]; norm_num
      · have a := abs_digitWeight_le (cellDigit k (r + 1))
        have b := abs_digitWeight_le (cellDigit k r)
        have := abs_sub (digitWeight (cellDigit k (r + 1))) (digitWeight (cellDigit k r))
        linarith
    calc |∑ r ∈ residueClass k 1, (cellWeight k (r + 1) - cellWeight k r)|
        ≤ ∑ r ∈ residueClass k 1, |cellWeight k (r + 1) - cellWeight k r| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ residueClass k 1,
          2 * (if cellDigit k (r + 1) = cellDigit k r then (0 : ℤ) else 1) :=
          sum_le_sum fun r _ => hterm r
      _ ≤ ∑ r ∈ range (3 ^ k - 1),
          2 * (if cellDigit k (r + 1) = cellDigit k r then (0 : ℤ) else 1) :=
          sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => by split_ifs <;> norm_num
      _ ≤ 6 := by
          rw [← mul_sum]
          have := sum_cellDigit_changes_le k (3 ^ k - 1) (by
            have : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
            omega)
          linarith
  rw [sum_sub_distrib, ← hshift] at hdiff
  rw [hrefl] at hdiff ⊢
  rw [abs_neg]
  have : |-∑ r ∈ residueClass k 1, cellWeight k r - ∑ r ∈ residueClass k 1, cellWeight k r| =
      2 * |∑ r ∈ residueClass k 1, cellWeight k r| := by
    rw [show -∑ r ∈ residueClass k 1, cellWeight k r - ∑ r ∈ residueClass k 1, cellWeight k r =
      -2 * ∑ r ∈ residueClass k 1, cellWeight k r by ring, abs_mul]
    norm_num
  rw [this] at hdiff
  linarith

theorem sum_cellDigit_changes_full (k : ℕ) :
    ∑ r ∈ range (3 ^ k), (if cellDigit k (r + 1) = cellDigit k r then (0 : ℤ) else 1) ≤ 4 := by
  have hstep : ∀ r, (if cellDigit k (r + 1) = cellDigit k r then (0 : ℤ) else 1) ≤
      cellDigit k (r + 1) - cellDigit k r := fun r => by
    have := cellDigit_mono k (show r ≤ r + 1 by omega)
    split_ifs with h <;> omega
  have hend : cellDigit k (3 ^ k) = 4 := by
    unfold cellDigit
    rw [show (4 : ℝ) * ((3 ^ k : ℕ) : ℝ) / 3 ^ k = ((4 : ℤ) : ℝ) by push_cast; field_simp,
      Int.floor_intCast]
  calc ∑ r ∈ range (3 ^ k), (if cellDigit k (r + 1) = cellDigit k r then (0 : ℤ) else 1)
      ≤ ∑ r ∈ range (3 ^ k), (cellDigit k (r + 1) - cellDigit k r) :=
        sum_le_sum fun r _ => hstep r
    _ = cellDigit k (3 ^ k) - cellDigit k 0 := sum_range_sub (fun r => cellDigit k r) _
    _ ≤ 4 := by rw [hend]; have := cellDigit_nonneg k 0; omega

/-- Periodicity: a function of `b 4ⁱ mod 3ᵏ` summed over three periods. -/
theorem sum_range_three_periods {k : ℕ} (hk : 1 ≤ k) (b : ℕ) (G : ℕ → ℤ) :
    ∑ i ∈ range (3 ^ k), G (b * 4 ^ i % 3 ^ k) =
      3 * ∑ i ∈ range (3 ^ (k - 1)), G (b * 4 ^ i % 3 ^ k) := by
  set P := 3 ^ (k - 1) with hP
  have hper : ∀ i, b * 4 ^ (P + i) % 3 ^ k = b * 4 ^ i % 3 ^ k := by
    intro i
    have h1 := three_pow_dvd_four_pow_sub_one hk
    have hmod : 4 ^ P % 3 ^ k = 1 % 3 ^ k := by
      have : 4 ^ P ≡ 1 [MOD 3 ^ k] := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr
        h1 |>.symm
      exact this
    rw [pow_add, ← mul_assoc, mul_comm b, mul_assoc, Nat.mul_mod, hmod, ← Nat.mul_mod, one_mul]
  have h3 : 3 ^ k = P + P + P := by
    rw [hP, ← two_mul, ← add_one_mul, show k = k - 1 + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]; ring
  rw [show range (3 ^ k) = range (P + P + P) by rw [h3], sum_range_add, sum_range_add]
  have e1 : ∑ i ∈ range P, G (b * 4 ^ (P + i) % 3 ^ k) = ∑ i ∈ range P, G (b * 4 ^ i % 3 ^ k) :=
    sum_congr rfl fun i _ => by rw [hper]
  have e2 : ∑ i ∈ range P, G (b * 4 ^ (P + P + i) % 3 ^ k) =
      ∑ i ∈ range P, G (b * 4 ^ i % 3 ^ k) :=
    sum_congr rfl fun i _ => by rw [add_assoc, hper, hper]
  rw [e1, e2]
  ring

/-! ### The Stoneham constant -/

/-- The terms `3^{−(j+1)} 2^{−3^{j+1}}`. -/
noncomputable def stonehamTerm (j : ℕ) : ℝ := 1 / (3 ^ (j + 1) * 2 ^ (3 ^ (j + 1)))

/-- `α = Σ_{j ≥ 1} 3^{−j} 2^{−3^j}`. -/
noncomputable def stoneham : ℝ := ∑' j, stonehamTerm j

theorem stonehamTerm_pos (j : ℕ) : 0 < stonehamTerm j := by unfold stonehamTerm; positivity

theorem stonehamTerm_le (j : ℕ) : stonehamTerm j ≤ (1 / 2) ^ (j + 1) := by
  unfold stonehamTerm
  rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
  have h1 : (2 : ℝ) ^ (j + 1) ≤ 2 ^ (3 ^ (j + 1)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.lt_pow_self (by norm_num)).le
  have h2 : (1 : ℝ) ≤ 3 ^ (j + 1) := one_le_pow₀ (by norm_num)
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (3 ^ (j + 1))]

theorem summable_stonehamTerm : Summable stonehamTerm :=
  Summable.of_nonneg_of_le (fun j => (stonehamTerm_pos j).le) stonehamTerm_le
    ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1))

/-- `Aₖ = Σ_{j < k} 2^{3ᵏ − 3^{j+1}} 3^{k−(j+1)}`. -/
def stonehamA (k : ℕ) : ℕ := ∑ j ∈ range k, 2 ^ (3 ^ k - 3 ^ (j + 1)) * 3 ^ (k - (j + 1))

theorem stonehamA_mod_three {k : ℕ} (hk : 1 ≤ k) : stonehamA k % 3 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  unfold stonehamA
  rw [sum_range_succ, Nat.sub_self, Nat.sub_self, pow_zero, pow_zero, mul_one]
  have hdvd : 3 ∣ ∑ j ∈ range m, 2 ^ (3 ^ (m + 1) - 3 ^ (j + 1)) * 3 ^ (m + 1 - (j + 1)) := by
    refine dvd_sum fun j hj => ?_
    have : 1 ≤ m + 1 - (j + 1) := by rw [mem_range] at hj; omega
    exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  omega

/-- **Window decomposition.**  For `3ᵏ ≤ 2n < 3^{k+1}`,
`4ⁿ α = 2^{2n−3ᵏ} Aₖ / 3ᵏ + t` with `0 < t ≤ 3^{−(k+1)}`. -/
theorem four_pow_mul_stoneham {k n : ℕ} (hk1 : 3 ^ k ≤ 2 * n) (hk2 : 2 * n < 3 ^ (k + 1)) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 2 / (9 * 3 ^ k) ∧
      (4 : ℝ) ^ n * stoneham = ((2 ^ (2 * n - 3 ^ k) * stonehamA k : ℕ) : ℝ) / 3 ^ k + t := by
  have hsplit := summable_stonehamTerm.sum_add_tsum_nat_add k
  refine ⟨(4 : ℝ) ^ n * ∑' j, stonehamTerm (j + k), ?_, ?_, ?_⟩
  · exact mul_pos (by positivity) (summable_stonehamTerm.comp_injective
      (add_left_injective k) |>.tsum_pos (fun j => (stonehamTerm_pos _).le) 0 (stonehamTerm_pos _))
  · -- each tail term is at most `3^{−(k+1)} 2^{−1} 4^{−j}`
    have hodd : 3 ^ (k + 1) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
    have hb : ∀ j : ℕ,
        (4 : ℝ) ^ n * stonehamTerm (j + k) ≤ 1 / (3 ^ (k + 1) * 2 * 4 ^ j) := by
      intro j
      unfold stonehamTerm
      have hexp : 2 * n + 1 + 2 * j ≤ 3 ^ (j + k + 1) := by
        have hj : 1 + 2 * j ≤ 3 ^ j := by
          induction j with
          | zero => simp
          | succ j ih => rw [pow_succ]; omega
        have h3 : 3 ^ (j + k + 1) = 3 ^ (k + 1) * 3 ^ j := by rw [← pow_add]; ring_nf
        have h1 : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
        rw [h3]
        nlinarith
      have h4 : (4 : ℝ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
      have h4j : (4 : ℝ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
      rw [h4, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, h4j]
      have h5 : (2 : ℝ) ^ (2 * n) * 2 * 2 ^ (2 * j) ≤ 2 ^ (3 ^ (j + k + 1)) := by
        rw [← pow_succ, ← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h6 : (3 : ℝ) ^ (k + 1) ≤ 3 ^ (j + k + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      calc (2 : ℝ) ^ (2 * n) * (3 ^ (k + 1) * 2 * 2 ^ (2 * j)) =
          3 ^ (k + 1) * (2 ^ (2 * n) * 2 * 2 ^ (2 * j)) := by ring
        _ ≤ 3 ^ (j + k + 1) * 2 ^ (3 ^ (j + k + 1)) := by gcongr
    have hg : Summable fun j : ℕ => 1 / (3 ^ (k + 1) * 2 * (4 : ℝ) ^ j) :=
      ((summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left
        (1 / (3 ^ (k + 1) * 2))).congr fun j => by rw [one_div_pow]; field_simp
    calc (4 : ℝ) ^ n * ∑' j, stonehamTerm (j + k) = ∑' j, (4 : ℝ) ^ n * stonehamTerm (j + k) :=
          (tsum_mul_left).symm
      _ ≤ ∑' j : ℕ, 1 / (3 ^ (k + 1) * 2 * (4 : ℝ) ^ j) :=
          Summable.tsum_le_tsum hb ((summable_stonehamTerm.comp_injective
            (add_left_injective k)).mul_left _) hg
      _ = 2 / (9 * 3 ^ k) := by
          have e : ∀ j : ℕ, 1 / (3 ^ (k + 1) * 2 * (4 : ℝ) ^ j) =
              1 / (3 ^ (k + 1) * 2) * (1 / 4 : ℝ) ^ j := fun j => by
            rw [one_div_pow]; field_simp
          simp_rw [e]
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num), pow_succ]
          field_simp
          norm_num
  · rw [stoneham, ← hsplit, mul_add]
    congr 1
    -- the head is `2^{2n−3ᵏ} Aₖ / 3ᵏ`
    rw [Finset.mul_sum, stonehamA]
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    unfold stonehamTerm
    have hjk : 3 ^ (j + 1) ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hj
    have e2 : (2 : ℝ) ^ (2 * n) = 2 ^ (2 * n - 3 ^ k) * 2 ^ (3 ^ k - 3 ^ (j + 1)) *
        2 ^ (3 ^ (j + 1)) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have e3 : (3 : ℝ) ^ k = 3 ^ (k - (j + 1)) * 3 ^ (j + 1) := by
      rw [← pow_add]; congr 1; omega
    have h4 : (4 : ℝ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
    rw [h4, e2, e3]
    field_simp

/-! ### The drift over a complete window -/

open BinaryParityDrift

theorem quatDigit_succ_eq_floor_fract (x : ℝ) (n : ℕ) :
    quatDigit x (n + 1) = ⌊4 * Int.fract ((4 : ℝ) ^ n * x)⌋ := by
  unfold quatDigit
  have h0 := Int.fract_nonneg ((4 : ℝ) ^ n * x)
  have h1 := Int.fract_lt_one ((4 : ℝ) ^ n * x)
  have hf0 : 0 ≤ ⌊4 * Int.fract ((4 : ℝ) ^ n * x)⌋ := Int.floor_nonneg.mpr (by linarith)
  have hf3 : ⌊4 * Int.fract ((4 : ℝ) ^ n * x)⌋ < 4 :=
    Int.floor_lt.mpr (by push_cast; linarith)
  have e : (4 : ℝ) ^ (n + 1) * x = 4 * Int.fract ((4 : ℝ) ^ n * x) +
      ((4 * ⌊(4 : ℝ) ^ n * x⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [e, Int.floor_add_intCast]
  omega

theorem drift_eq_sum_digitWeight (x : ℝ) (N : ℕ) :
    drift x N = ∑ n ∈ range N, digitWeight (quatDigit x (n + 1)) := by
  unfold drift
  exact sum_congr rfl fun n _ => binDigit_sub_binDigit_eq x n

/-- On the `k`-th window the base-4 digits of `α` are read off the orbit `2Aₖ 4ⁱ mod 3ᵏ`. -/
theorem quatDigit_stoneham_window {k i : ℕ} (_hk : 1 ≤ k) (_hi : i < 3 ^ k) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 2 / (9 * 3 ^ k) ∧
      quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1) =
        ⌊4 * (((2 * stonehamA k * 4 ^ i % 3 ^ k : ℕ) : ℝ) / 3 ^ k + t)⌋ := by
  have hodd : (3 ^ k) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  set n := (3 ^ k + 1) / 2 + i with hn
  have h2n : 2 * n = 3 ^ k + (2 * i + 1) := by rw [hn]; omega
  have hk1 : 3 ^ k ≤ 2 * n := by omega
  have hk2 : 2 * n < 3 ^ (k + 1) := by rw [h2n, pow_succ]; omega
  obtain ⟨t, ht0, ht1, heq⟩ := four_pow_mul_stoneham hk1 hk2
  have hM : 2 ^ (2 * n - 3 ^ k) * stonehamA k = 2 * stonehamA k * 4 ^ i := by
    rw [show 2 * n - 3 ^ k = 2 * i + 1 by omega, pow_succ, pow_mul]; norm_num; ring
  rw [hM] at heq
  set M := 2 * stonehamA k * 4 ^ i with hMdef
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have ht1' : t < 1 / 3 ^ k := by
    refine lt_of_le_of_lt ht1 ?_
    rw [div_lt_div_iff₀ (by positivity) h3k]
    linarith
  refine ⟨t, ht0, ht1, ?_⟩
  rw [quatDigit_succ_eq_floor_fract, heq]
  congr 2
  -- `M/3ᵏ + t = ⌊M/3ᵏ⌋ + (M mod 3ᵏ)/3ᵏ + t` with the last two summands in `[0, 1)`
  have hdiv : (M : ℝ) / 3 ^ k = ((M / 3 ^ k : ℕ) : ℝ) + ((M % 3 ^ k : ℕ) : ℝ) / 3 ^ k := by
    have := Nat.div_add_mod M (3 ^ k)
    have hcast : (M : ℝ) = 3 ^ k * ((M / 3 ^ k : ℕ) : ℝ) + ((M % 3 ^ k : ℕ) : ℝ) := by
      exact_mod_cast this.symm
    rw [hcast]; field_simp
  rw [hdiv, add_assoc, add_comm, Int.fract_add_natCast]
  rw [Int.fract_eq_self]
  have hlt : ((M % 3 ^ k : ℕ) : ℝ) ≤ 3 ^ k - 1 := by
    have : M % 3 ^ k < 3 ^ k := Nat.mod_lt _ (by positivity)
    have : M % 3 ^ k + 1 ≤ 3 ^ k := this
    have h' : ((M % 3 ^ k : ℕ) : ℝ) + 1 ≤ 3 ^ k := by exact_mod_cast this
    linarith
  constructor
  · positivity
  · have : ((M % 3 ^ k : ℕ) : ℝ) / 3 ^ k ≤ 1 - 1 / 3 ^ k := by
      rw [div_le_iff₀ h3k]; field_simp; linarith
    linarith

/-- Indicator of a change of the first base-4 digit between `r/3ᵏ` and `(r + 1)/3ᵏ`. -/
noncomputable def digitChange (k r : ℕ) : ℤ := if cellDigit k (r + 1) = cellDigit k r then 0 else 1

theorem digitChange_nonneg (k r : ℕ) : 0 ≤ digitChange k r := by
  unfold digitChange; split_ifs <;> norm_num

/-- On the `k`-th window each digit weight of `α` equals the cell weight of its orbit point,
except at digit changes, where they differ by at most `2`. -/
theorem abs_digitWeight_window_sub_le {k i : ℕ} (hk : 1 ≤ k) (hi : i < 3 ^ k) :
    |digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) -
        cellWeight k (2 * stonehamA k * 4 ^ i % 3 ^ k)| ≤
      2 * digitChange k (2 * stonehamA k * 4 ^ i % 3 ^ k) := by
  set b := 2 * stonehamA k with hb
  obtain ⟨t, ht0, ht1, hq⟩ := quatDigit_stoneham_window hk hi
  rw [hq]
  unfold digitChange
  split_ifs with h
  · -- no digit change: the perturbed digit is the cell digit
    have hlow : cellDigit k (b * 4 ^ i % 3 ^ k) ≤
        ⌊4 * (((b * 4 ^ i % 3 ^ k : ℕ) : ℝ) / 3 ^ k + t)⌋ := by
      unfold cellDigit
      apply Int.floor_mono
      rw [mul_div_assoc]
      nlinarith
    have hhigh : ⌊4 * (((b * 4 ^ i % 3 ^ k : ℕ) : ℝ) / 3 ^ k + t)⌋ ≤
        cellDigit k (b * 4 ^ i % 3 ^ k + 1) := by
      unfold cellDigit
      apply Int.floor_mono
      push_cast
      have : t ≤ 1 / 3 ^ k := ht1.trans <| by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (0 : ℝ) < 3 ^ k := by positivity
        linarith
      rw [mul_div_assoc, add_div]
      linarith
    have heq : ⌊4 * (((b * 4 ^ i % 3 ^ k : ℕ) : ℝ) / 3 ^ k + t)⌋ =
        cellDigit k (b * 4 ^ i % 3 ^ k) := by rw [h] at hhigh; omega
    rw [heq, cellWeight, sub_self, abs_zero]
    norm_num
  · have a := abs_digitWeight_le (⌊4 * (((b * 4 ^ i % 3 ^ k : ℕ) : ℝ) / 3 ^ k + t)⌋)
    have c := abs_digitWeight_le (cellDigit k (b * 4 ^ i % 3 ^ k))
    have := abs_sub (digitWeight ⌊4 * (((b * 4 ^ i % 3 ^ k : ℕ) : ℝ) / 3 ^ k + t)⌋)
      (cellWeight k (b * 4 ^ i % 3 ^ k))
    unfold cellWeight at this ⊢
    linarith

/-- A complete window meets at most `12` digit changes. -/
theorem sum_window_digitChange_le {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ range (3 ^ k), digitChange k (2 * stonehamA k * 4 ^ i % 3 ^ k) ≤ 12 := by
  set b := 2 * stonehamA k with hb
  have hbmod : b % 3 = 2 := by rw [hb, Nat.mul_mod, stonehamA_mod_three hk]
  have hb3 : ¬ 3 ∣ b := by omega
  rw [sum_range_three_periods hk b (digitChange k), sum_range_orbit_eq hk hb3, hbmod]
  have hsub : residueClass k 2 ⊆ range (3 ^ k) := filter_subset _ _
  have := sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => digitChange_nonneg k r
  have := sum_cellDigit_changes_full k
  unfold digitChange at *
  linarith

/-- **Each complete window contributes a bounded drift.** -/
theorem abs_sum_window_le {k : ℕ} (hk : 1 ≤ k) :
    |∑ i ∈ range (3 ^ k), digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1))| ≤ 33 := by
  set b := 2 * stonehamA k with hb
  have hbmod : b % 3 = 2 := by rw [hb, Nat.mul_mod, stonehamA_mod_three hk]
  have hb3 : ¬ 3 ∣ b := by omega
  set ρ : ℕ → ℕ := fun i => b * 4 ^ i % 3 ^ k with hρ
  have hmain : |∑ i ∈ range (3 ^ k), cellWeight k (ρ i)| ≤ 9 := by
    rw [sum_range_three_periods hk b (cellWeight k), sum_range_orbit_eq hk hb3, hbmod, abs_mul]
    have := abs_sum_residueClass_two_le hk
    norm_num
    linarith
  have hchg := sum_window_digitChange_le hk
  calc |∑ i ∈ range (3 ^ k), digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1))|
      = |∑ i ∈ range (3 ^ k), (digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) -
          cellWeight k (ρ i)) + ∑ i ∈ range (3 ^ k), cellWeight k (ρ i)| := by
        rw [← sum_add_distrib]; simp
    _ ≤ |∑ i ∈ range (3 ^ k), (digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) -
          cellWeight k (ρ i))| + |∑ i ∈ range (3 ^ k), cellWeight k (ρ i)| := abs_add_le _ _
    _ ≤ ∑ i ∈ range (3 ^ k), 2 * digitChange k (ρ i) + 9 := by
        gcongr
        exact (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun i hi => abs_digitWeight_window_sub_le hk (mem_range.mp hi))
    _ ≤ 33 := by rw [← mul_sum]; linarith

/-! ### Window ends -/

/-- The window ends `Nₖ = (3^{k+1} + 1)/2`. -/
def windowEnd (k : ℕ) : ℕ := (3 ^ (k + 1) + 1) / 2

theorem windowEnd_succ (k : ℕ) : windowEnd (k + 1) = windowEnd k + 3 ^ (k + 1) := by
  unfold windowEnd
  have hodd : (3 ^ (k + 1)) % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  rw [pow_succ 3 (k + 1)]
  omega

theorem abs_drift_windowEnd_le (k : ℕ) : |drift stoneham (windowEnd k)| ≤ 2 + 33 * k := by
  induction k with
  | zero =>
    have h2 : windowEnd 0 = 2 := by decide
    rw [h2, drift_eq_sum_digitWeight]
    simp only [sum_range_succ, sum_range_zero, zero_add, Nat.cast_zero, mul_zero, add_zero]
    have a := abs_digitWeight_le (quatDigit stoneham (0 + 1))
    have b := abs_digitWeight_le (quatDigit stoneham (1 + 1))
    calc _ ≤ |digitWeight (quatDigit stoneham (0 + 1))| +
          |digitWeight (quatDigit stoneham (1 + 1))| := abs_add_le _ _
      _ ≤ 2 := by linarith
  | succ k ih =>
    have hwin := abs_sum_window_le (k := k + 1) (by omega)
    have hsplit : drift stoneham (windowEnd (k + 1)) = drift stoneham (windowEnd k) +
        ∑ i ∈ range (3 ^ (k + 1)),
          digitWeight (quatDigit stoneham ((3 ^ (k + 1) + 1) / 2 + i + 1)) := by
      rw [windowEnd_succ, drift_eq_sum_digitWeight, drift_eq_sum_digitWeight, sum_range_add]
      rfl
    rw [hsplit]
    push_cast
    calc _ ≤ |drift stoneham (windowEnd k)| + |∑ i ∈ range (3 ^ (k + 1)),
          digitWeight (quatDigit stoneham ((3 ^ (k + 1) + 1) / 2 + i + 1))| := abs_add_le _ _
      _ ≤ 2 + 33 * k + 33 := by
          have : |drift stoneham (windowEnd k)| ≤ 2 + 33 * (k : ℤ) := by exact_mod_cast ih
          linarith
      _ = 2 + 33 * ((k : ℤ) + 1) := by ring

theorem three_pow_le_windowEnd (k : ℕ) : 3 ^ k ≤ windowEnd k := by
  unfold windowEnd
  rw [pow_succ]
  omega

/-- **The drift of `α` vanishes along the window ends.** -/
theorem tendsto_drift_windowEnd :
    Tendsto (fun k : ℕ => (drift stoneham (windowEnd k) : ℝ) / windowEnd k) atTop (𝓝 0) := by
  have hlim : Tendsto (fun k : ℕ => (2 + 33 * (k : ℝ)) / 3 ^ k) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 3)
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 3)
    have := (h0.const_mul 2).add (h1.const_mul 33)
    simp only [pow_one, pow_zero, mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
  have hpos : (0 : ℝ) < 3 ^ k := by positivity
  have hW : (3 : ℝ) ^ k ≤ windowEnd k := by exact_mod_cast three_pow_le_windowEnd k
  have hd : |(drift stoneham (windowEnd k) : ℝ)| ≤ 2 + 33 * k := by
    have := abs_drift_windowEnd_le k
    exact_mod_cast this
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  calc |(drift stoneham (windowEnd k) : ℝ)| / windowEnd k ≤ (2 + 33 * k) / windowEnd k :=
        div_le_div_of_nonneg_right hd (by positivity)
    _ ≤ (2 + 33 * k) / 3 ^ k := div_le_div_of_nonneg_left (by positivity) hpos hW

/-- **The strong Parity-Drift Hypothesis fails for the Stoneham constant.** -/
theorem not_strongParityDriftHypothesis_stoneham : ¬ StrongParityDriftHypothesis stoneham := by
  rintro ⟨δ, hδ, ho, he⟩
  have hd : Tendsto (fun N : ℕ => (drift stoneham N : ℝ) / N) atTop (𝓝 (2 * δ)) := by
    have := ho.sub he
    rw [show 1 / 2 + δ - (1 / 2 - δ) = 2 * δ by ring] at this
    refine this.congr fun N => ?_
    simp only [drift, sum_sub_distrib]
    push_cast
    ring
  have hmono : StrictMono windowEnd := strictMono_nat_of_lt_succ fun k => by
    rw [windowEnd_succ]; have := Nat.one_le_pow (k + 1) 3 (by norm_num); omega
  have h2 := hd.comp hmono.tendsto_atTop
  have h0 := tendsto_nhds_unique h2 tendsto_drift_windowEnd
  exact hδ (by linarith)

end GaloisForLFunctions.HTGeometry.StonehamParityDrift
