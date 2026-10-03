import GaloisForLFunctions.HTGeometry.ThreeAdicOrbitPhaseSums
import GaloisForLFunctions.HTGeometry.StonehamPrimeSquareOrbit
import GaloisForLFunctions.HTGeometry.StonehamPrimeDriftSymmetries
import GaloisForLFunctions.HTGeometry.WeylDifferencing

/-!
# Korobov's bound for orbit sums of `16` modulo `3ᵅ5ᵝ`

For `Q = 3ᵅ5ᵝ` and `u` prime to `Q`, the incomplete orbit sums `Σ_{i<L} e(u 16ⁱ/Q)` are
nontrivial already at lengths `L ≈ Q^{1/3+ε}`, beyond the square-root barrier of completion.

* Korobov's expansion: `16^{T₀} = 1 + X` with `Q ∣ X³` makes `u 16^{j+T₀l}` quadratic in `l`
  modulo `Q` (`pow_add_mul_modEq`); one Weyl differencing leaves geometric sums of slope
  `u 16ʲ X² h` (`norm_sum_orbit_sq_le_geometric`).
* Averaging these slopes over `j` produces complete orbit sums of `16`.  A shift of `j` multiplies
  such a sum by a nontrivial cube or fifth root of unity, so it vanishes unless `Q ∣ 15 w`
  (`dvd_fifteen_mul_of_sum_ne_zero`).
* `norm_sum_sixteen_block_sq_le`: `‖Σ_{i<T₀N}‖² ≤ T₀² (N + 2 √(N⁵/D + N³))`.
* `exists_korobov_parameters`: admissible `T₀, D, X` with `T₀³ ≤ Q` and `Q² ≤ 3⁹5⁹ (T₀D)³`.
* `norm_sum_sixteen_pow_twelve_le`: if `Q ≤ P²`, `L ≤ P` and `L² ≤ c Q`, then
  `‖Σ_{i<L}‖¹² ≤ 2¹² 18³ 3⁹ 5⁹ c² P¹¹`, a saving of `P^{−1/12}` at length `P`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.ThreeFiveOrbit

open StonehamParityDrift StonehamPrimeDrift

/-! ### Korobov's quadratic expansion and one Weyl differencing -/

/-- `(1 + x)^l ≡ 1 + l x + C(l, 2) x²` modulo any `Q ∣ x³`. -/
theorem one_add_pow_modEq {x Q : ℤ} (hQ : Q ∣ x ^ 3) (l : ℕ) :
    (1 + x) ^ l ≡ 1 + l * x + (l.choose 2 : ℤ) * x ^ 2 [ZMOD Q] := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hx3 : x ^ 3 ≡ 0 [ZMOD Q] := (Int.modEq_zero_iff_dvd).mpr hQ
    calc (1 + x) ^ (l + 1) = (1 + x) ^ l * (1 + x) := pow_succ _ _
      _ ≡ (1 + l * x + (l.choose 2 : ℤ) * x ^ 2) * (1 + x) [ZMOD Q] := ih.mul_right _
      _ = 1 + ((l + 1 : ℕ) : ℤ) * x + (((l.choose 2 + l : ℕ)) : ℤ) * x ^ 2 +
            (l.choose 2 : ℤ) * x ^ 3 := by push_cast; ring
      _ ≡ 1 + ((l + 1 : ℕ) : ℤ) * x + (((l.choose 2 + l : ℕ)) : ℤ) * x ^ 2 +
            (l.choose 2 : ℤ) * 0 [ZMOD Q] := (hx3.mul_left _).add_left _
      _ = 1 + ((l + 1 : ℕ) : ℤ) * x + (((l + 1).choose 2 : ℕ) : ℤ) * x ^ 2 := by
          rw [Nat.choose_succ_succ', Nat.choose_one_right]; push_cast; ring

/-- `C(l + h, 2) = C(l, 2) + h l + C(h, 2)`. -/
theorem choose_two_add (l h : ℕ) : (l + h).choose 2 = l.choose 2 + h * l + h.choose 2 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [← add_assoc, Nat.choose_succ_succ', Nat.choose_one_right, ih, Nat.choose_succ_succ',
      Nat.choose_one_right]
    ring

/-- **Korobov's expansion.**  If `g^{T₀} = 1 + X` and `Q ∣ X³`, then along the progression
`j + T₀ l` the orbit point `c gⁱ` is a quadratic polynomial in `l` modulo `Q`. -/
theorem pow_add_mul_modEq {Q g X : ℤ} {T₀ : ℕ} (hT : g ^ T₀ = 1 + X) (hQ : Q ∣ X ^ 3) (c : ℤ)
    (j l : ℕ) :
    c * g ^ (j + T₀ * l) ≡ c * g ^ j + c * g ^ j * X * l +
      c * g ^ j * X ^ 2 * (l.choose 2 : ℤ) [ZMOD Q] := by
  have h := one_add_pow_modEq hQ l
  rw [pow_add, pow_mul, hT]
  calc c * (g ^ j * (1 + X) ^ l)
      ≡ c * (g ^ j * (1 + l * X + (l.choose 2 : ℤ) * X ^ 2)) [ZMOD Q] :=
        (h.mul_left _).mul_left _
    _ = _ := by ring

/-- **One Weyl differencing.**  The quadratic phase in `l` reduces to geometric sums of slope
`c gʲ X² h`. -/
theorem norm_sum_orbit_sq_le_geometric {Q : ℕ} (hQ0 : Q ≠ 0) {g X : ℤ} {T₀ : ℕ}
    (hT : g ^ T₀ = 1 + X) (hQ : (Q : ℤ) ∣ X ^ 3) (c : ℤ) (j N : ℕ) :
    ‖∑ l ∈ range N, ephase Q (c * g ^ (j + T₀ * l))‖ ^ 2 ≤
      N + 2 * ∑ h ∈ Ico 1 N, ‖∑ l ∈ range (N - h), ephase Q (c * g ^ j * X ^ 2 * h * l)‖ := by
  have hF : ∀ l, ‖ephase Q (c * g ^ (j + T₀ * l))‖ ≤ 1 := fun l => (norm_ephase _ _).le
  refine (HTGeometry.weyl_differencing_bound N _ hF).trans ?_
  gcongr with h hh
  have hterm : ∀ l, ephase Q (c * g ^ (j + T₀ * (l + h))) *
      (starRingEnd ℂ) (ephase Q (c * g ^ (j + T₀ * l))) =
      ephase Q (c * g ^ j * X * h + c * g ^ j * X ^ 2 * (h.choose 2 : ℤ)) *
        ephase Q (c * g ^ j * X ^ 2 * h * l) := by
    intro l
    rw [← ephase_neg, ← ephase_add, ← ephase_add]
    apply ephase_congr hQ0
    have h1 := pow_add_mul_modEq hT hQ c j (l + h)
    have h2 := pow_add_mul_modEq hT hQ c j l
    calc c * g ^ (j + T₀ * (l + h)) + -(c * g ^ (j + T₀ * l))
        ≡ (c * g ^ j + c * g ^ j * X * ((l + h : ℕ) : ℤ) +
            c * g ^ j * X ^ 2 * (((l + h).choose 2 : ℕ) : ℤ)) +
            -(c * g ^ j + c * g ^ j * X * (l : ℤ) + c * g ^ j * X ^ 2 * ((l.choose 2 : ℕ) : ℤ))
            [ZMOD Q] := Int.ModEq.add h1 (Int.ModEq.neg h2)
      _ = _ := by rw [choose_two_add]; push_cast; ring
  unfold HTGeometry.diffSum
  rw [sum_congr rfl fun l _ => hterm l, ← mul_sum, norm_mul, norm_ephase, one_mul]

/-! ### Complete orbit sums of `16` modulo `3ᵅ5ᵝ` -/

/-- `e_{dM}(M y) = e_d(y)`. -/
theorem ephase_mul_left_cancel {M : ℕ} (hM : M ≠ 0) (d : ℕ) (y : ℤ) :
    ephase (d * M) (M * y) = ephase d y := by
  unfold ephase
  congr 4
  have : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  push_cast
  rcases eq_or_ne (d : ℝ) 0 with h | h
  · simp [h]
  · field_simp

/-- A sum over a period that is multiplied by `ζ ≠ 1` under a shift vanishes. -/
theorem sum_range_eq_zero_of_shift {f : ℕ → ℂ} {T sh : ℕ} (hper : ∀ j, f (j + T) = f j)
    {ζ : ℂ} (hζ : ζ ≠ 1) (hsh : ∀ j, f (j + sh) = ζ * f j) : ∑ j ∈ range T, f j = 0 := by
  have h := sum_range_shift_of_periodic hper sh
  simp_rw [hsh, ← mul_sum] at h
  have : (ζ - 1) * ∑ j ∈ range T, f j = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hζ)

/-- `16ʲ ≡ 1` modulo every divisor of `15`. -/
theorem sixteen_pow_modEq_one {p : ℕ} (hp : p ∣ 15) (j : ℕ) : (16 : ℤ) ^ j ≡ 1 [ZMOD p] := by
  have h : (16 : ℤ) ≡ 1 [ZMOD p] := by
    obtain ⟨t, ht⟩ := hp
    have ht' : (15 : ℤ) = p * t := by exact_mod_cast ht
    exact Int.modEq_iff_dvd.mpr ⟨-t, by linear_combination -ht'⟩
  simpa using h.pow j

/-- **Vanishing of complete orbit sums of `16`.**  Let `Q = pᵅ R` with `p ∣ 15` prime, `p ∤ ρ`,
`R ∣ 16^ρ − 1`, and suppose that `pᵏ ∣ 16ᵈ − 1 ⟺ p^{k−1} ∣ d`.  If `T` is a period of
`j ↦ e_Q(w 16ʲ)` and `p^{α−1} ∤ w`, then `Σ_{j<T} e_Q(w 16ʲ) = 0`. -/
theorem sum_sixteen_orbit_eq_zero {p α R ρ T : ℕ} (hp : p.Prime) (hp15 : p ∣ 15)
    (hlte : ∀ k d : ℕ, 1 ≤ k → (p ^ k ∣ 16 ^ d - 1 ↔ p ^ (k - 1) ∣ d))
    (hR : R ∣ 16 ^ ρ - 1) (hρ : ¬ p ∣ ρ) (hpR : p.Coprime R) {w : ℤ}
    (hper : ((p ^ α * R : ℕ) : ℤ) ∣ w * (16 ^ T - 1)) (hw : ¬ ((p ^ (α - 1) : ℕ) : ℤ) ∣ w) :
    ∑ j ∈ range T, ephase (p ^ α * R) (w * 16 ^ j) = 0 := by
  haveI := Fact.mk hp
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero _)
  have hα : 1 ≤ α := by
    by_contra h
    exact hw (by rw [show α - 1 = 0 by omega, pow_zero, Nat.cast_one]; exact one_dvd _)
  set e := padicValNat p w.natAbs with he
  have hwa : w.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hw0
  have hdvd : p ^ e ∣ w.natAbs := pow_padicValNat_dvd
  have hndvd : ¬ p ^ (e + 1) ∣ w.natAbs := pow_succ_padicValNat_not_dvd hwa
  have heα : e + 2 ≤ α := by
    by_contra h
    exact hw (Int.natCast_dvd.mpr ((pow_dvd_pow p (by omega)).trans hdvd))
  -- `w = pᵉ w'` with `p ∤ w'`
  obtain ⟨w', hw'⟩ : ((p ^ e : ℕ) : ℤ) ∣ w := Int.natCast_dvd.mpr hdvd
  have hw'p : ¬ (p : ℤ) ∣ w' := by
    rintro ⟨t, rfl⟩
    apply hndvd
    rw [← Int.natCast_dvd, hw', pow_succ]
    push_cast
    exact ⟨t, by ring⟩
  -- the shift `sh = p^{α−e−2} ρ`
  set sh := p ^ (α - e - 2) * ρ with hsh
  have h16 : 1 ≤ 16 ^ sh := Nat.one_le_pow _ _ (by norm_num)
  have hA : p ^ (α - e - 1) ∣ 16 ^ sh - 1 := by
    rw [hlte _ _ (by omega), show α - e - 1 - 1 = α - e - 2 by omega]
    exact dvd_mul_right _ _
  have hB : ¬ p ^ (α - e) ∣ 16 ^ sh - 1 := by
    rw [hlte _ _ (by omega), show α - e - 1 = α - e - 2 + 1 by omega, pow_succ, hsh]
    intro h
    exact hρ ((Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h))
  have hC : R ∣ 16 ^ sh - 1 := by
    refine hR.trans ?_
    rw [hsh, mul_comm, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (16 ^ ρ) (p ^ (α - e - 2))
  obtain ⟨κ, hκ⟩ : p ^ (α - e - 1) * R ∣ 16 ^ sh - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left _ hpR) hA hC
  have hκp : ¬ p ∣ κ := by
    rintro ⟨t, rfl⟩
    apply hB
    have hpow : p ^ (α - e) = p ^ (α - e - 1) * p := by rw [← pow_succ]; congr 1; omega
    rw [hκ, hpow]
    exact ⟨R * t, by ring⟩
  have hκZ : ((16 : ℤ) ^ sh - 1) = (p : ℤ) ^ (α - e - 1) * R * κ := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hκ
    simp only [Nat.cast_sub h16, Nat.cast_pow, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat] at this
    exact this
  -- the multiplier `ζ = e_p(w' κ)`
  have hR0 : R ≠ 0 := by rintro rfl; simp at hpR; exact hp.one_lt.ne' hpR
  have hsplit : p ^ α * R = p * (p ^ (α - 1) * R) := by
    rw [← mul_assoc, ← pow_succ']; congr 2; omega
  have hM0 : p ^ (α - 1) * R ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) hR0
  have hQ0 : p ^ α * R ≠ 0 := by rw [hsplit]; exact Nat.mul_ne_zero hp.ne_zero hM0
  refine sum_range_eq_zero_of_shift (sh := sh) (ζ := ephase p (w' * κ)) ?_ ?_ ?_
  · intro j
    apply ephase_congr hQ0
    rw [Int.modEq_iff_dvd]
    obtain ⟨t, ht⟩ := hper
    exact ⟨-(t * 16 ^ j), by rw [pow_add]; linear_combination (-(16 : ℤ) ^ j) * ht⟩
  · intro h
    have hdv : ¬ (p : ℤ) ∣ w' * κ := by
      intro h0
      rcases Int.Prime.dvd_mul' hp h0 with h1 | h1
      · exact hw'p h1
      · exact hκp (Int.natCast_dvd_natCast.mp h1)
    exact ephase_ne_one hp.ne_zero hdv h
  · intro j
    rw [← ephase_mul_left_cancel hM0 p, ← hsplit, ← ephase_add]
    apply ephase_congr hQ0
    have hcong : (w' * κ : ℤ) * 16 ^ j ≡ w' * κ [ZMOD p] := by
      simpa using (sixteen_pow_modEq_one hp15 j).mul_left (w' * κ)
    obtain ⟨s, hs⟩ := (Int.modEq_iff_dvd.mp hcong.symm)
    rw [Int.modEq_iff_dvd]
    refine ⟨-s, ?_⟩
    have hpe : (p : ℤ) ^ (α - 1) = p ^ e * p ^ (α - e - 1) := by
      rw [← pow_add]; congr 1; omega
    have hQZ : ((p ^ α * R : ℕ) : ℤ) = p * ((p : ℤ) ^ (α - 1) * R) := by
      rw [hsplit]; push_cast; ring
    rw [hQZ]
    push_cast at hw' ⊢
    rw [pow_add, hw', hpe]
    have h16sh : (16 : ℤ) ^ sh = 1 + (p : ℤ) ^ (α - e - 1) * R * κ := by linarith [hκZ]
    rw [h16sh]
    linear_combination (-(p : ℤ) ^ e * p ^ (α - e - 1) * R) * hs

theorem lte_three (k d : ℕ) (hk : 1 ≤ k) : 3 ^ k ∣ 16 ^ d - 1 ↔ 3 ^ (k - 1) ∣ d := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := pow_dvd_pow_sub_one_iff_of_order (p := 3) (b := 16) (m := 1) (by norm_num) (by norm_num)
    (by norm_num) (by intro d hd hd'; omega) (by norm_num) (by norm_num) hk (d := d)
  simpa using this

theorem lte_five (k d : ℕ) (hk : 1 ≤ k) : 5 ^ k ∣ 16 ^ d - 1 ↔ 5 ^ (k - 1) ∣ d := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := pow_dvd_pow_sub_one_iff_of_order (p := 5) (b := 16) (m := 1) (by norm_num) (by norm_num)
    (by norm_num) (by intro d hd hd'; omega) (by norm_num) (by norm_num) hk (d := d)
  simpa using this

theorem pow_dvd_sixteen_pow_self_sub_one {p : ℕ} (hlte : ∀ k d : ℕ, 1 ≤ k →
    (p ^ k ∣ 16 ^ d - 1 ↔ p ^ (k - 1) ∣ d)) (β : ℕ) : p ^ β ∣ 16 ^ p ^ β - 1 := by
  rcases Nat.eq_zero_or_pos β with rfl | hβ
  · simp
  rw [hlte _ _ hβ]
  exact pow_dvd_pow p (Nat.sub_le β 1)

/-- **Nonvanishing forces divisibility.**  If `T` is a period of `j ↦ e_Q(w 16ʲ)`,
`Q = 3ᵅ 5ᵝ`, and the complete orbit sum does not vanish, then `Q ∣ 15 w`. -/
theorem dvd_fifteen_mul_of_sum_ne_zero {α β T : ℕ} {w : ℤ}
    (hper : ((3 ^ α * 5 ^ β : ℕ) : ℤ) ∣ w * (16 ^ T - 1))
    (hS : ∑ j ∈ range T, ephase (3 ^ α * 5 ^ β) (w * 16 ^ j) ≠ 0) :
    ((3 ^ α * 5 ^ β : ℕ) : ℤ) ∣ 15 * w := by
  have h3 : ((3 ^ (α - 1) : ℕ) : ℤ) ∣ w := by
    by_contra h
    exact hS (sum_sixteen_orbit_eq_zero Nat.prime_three (by norm_num) lte_three
      (pow_dvd_sixteen_pow_self_sub_one lte_five β) (by
        intro h3; exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num))
      (Nat.Coprime.pow_right _ (by norm_num)) hper h)
  have h5 : ((5 ^ (β - 1) : ℕ) : ℤ) ∣ w := by
    by_contra h
    rw [mul_comm (3 ^ α)] at hper hS
    exact hS (sum_sixteen_orbit_eq_zero Nat.prime_five (by norm_num) lte_five
      (pow_dvd_sixteen_pow_self_sub_one lte_three α) (by
        intro h5; exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5) (by norm_num))
      (Nat.Coprime.pow_right _ (by norm_num)) hper h)
  rw [Int.natCast_dvd] at h3 h5 ⊢
  rw [Int.natAbs_mul]
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num)) ?_ ?_
  · rcases Nat.eq_zero_or_pos α with rfl | hα
    · simp
    have : 3 ^ α = 3 * 3 ^ (α - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]
    exact Nat.mul_dvd_mul (by norm_num) h3
  · rcases Nat.eq_zero_or_pos β with rfl | hβ
    · simp
    have : 5 ^ β = 5 * 5 ^ (β - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]
    exact Nat.mul_dvd_mul (by norm_num) h5

/-! ### Mean square over the orbit -/

/-- `‖Σ_{l<M} e_Q(a l)‖² = Σ_{l, l' < M} e_Q(a (l − l'))`. -/
theorem norm_sum_ephase_sq (Q : ℕ) (a : ℤ) (M : ℕ) :
    (((‖∑ l ∈ range M, ephase Q (a * l)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ l ∈ range M, ∑ l' ∈ range M, ephase Q (a * ((l : ℤ) - l')) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, sum_mul_sum]
  refine sum_congr rfl fun l _ => sum_congr rfl fun l' _ => ?_
  rw [← ephase_neg, ← ephase_add]
  congr 1
  ring

/-- **Pair counting.**  For fixed `l`, at most `M h / D + 1` indices `l' < M` satisfy
`D ∣ h (l − l')`. -/
theorem card_filter_dvd_mul_sub_le {D h : ℕ} (hD : 0 < D) (hh : 0 < h) (l M : ℕ) :
    (#{l' ∈ range M | (D : ℤ) ∣ h * ((l : ℤ) - ((l' : ℕ) : ℤ))} : ℝ) ≤ M * h / D + 1 := by
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd D h := ⟨_, rfl⟩
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left _ hD
  have hgD : g ∣ D := hg ▸ Nat.gcd_dvd_left D h
  have hgh : g ∣ h := hg ▸ Nat.gcd_dvd_right D h
  obtain ⟨E, hE⟩ := hgD
  obtain ⟨h', hh'⟩ := hgh
  have hE0 : 0 < E := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hE; omega
  have hcop : Nat.Coprime E h' := by
    have := Nat.coprime_div_gcd_div_gcd (m := D) (n := h) (hg ▸ hg0)
    rwa [← hg, hE, hh', Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  have hkey : ∀ l' ∈ ({l' ∈ range M | (D : ℤ) ∣ h * ((l : ℤ) - ((l' : ℕ) : ℤ))} : Finset ℕ),
      l' % E = l % E := by
    intro l' hl'
    rw [mem_filter] at hl'
    have h1 : (E : ℤ) ∣ (h' : ℤ) * ((l : ℤ) - l') := by
      have hd := hl'.2
      rw [hE, hh'] at hd
      push_cast at hd
      have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
      rw [show (g : ℤ) * h' * ((l : ℤ) - l') = g * (h' * ((l : ℤ) - l')) by ring] at hd
      exact (mul_dvd_mul_iff_left hg').mp hd
    have h2 : (E : ℤ) ∣ (l : ℤ) - l' :=
      IsCoprime.dvd_of_dvd_mul_left (Nat.isCoprime_iff_coprime.mpr hcop) h1
    exact (Nat.modEq_iff_dvd.mpr h2)
  have hcard : #{l' ∈ range M | (D : ℤ) ∣ h * ((l : ℤ) - ((l' : ℕ) : ℤ))} ≤ M / E + 1 := by
    have := card_le_card_of_injOn (fun l' => l' / E)
      (s := ({l' ∈ range M | (D : ℤ) ∣ h * ((l : ℤ) - ((l' : ℕ) : ℤ))} : Finset ℕ))
      (t := range (M / E + 1))
      (fun l' hl' => by
        have hl'' := (mem_filter.mp hl').1
        rw [mem_range] at hl''
        simp only [coe_range, Set.mem_Iio]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hl''.le))
      (fun a ha b hb hab => by
        have ha' := hkey a ha
        have hb' := hkey b hb
        simp only at hab
        rw [← Nat.div_add_mod a E, ← Nat.div_add_mod b E, hab, ha', hb'])
    simpa using this
  have hEr : (E : ℝ) * g = D := by rw [hE]; push_cast; ring
  have hgle : (g : ℝ) ≤ h := by
    have : g ≤ h := by rw [hh']; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero
      fun h0 => by simp [h0] at hh'; omega)
    exact_mod_cast this
  have hE0r : (0 : ℝ) < E := by exact_mod_cast hE0
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  calc (#{l' ∈ range M | (D : ℤ) ∣ h * ((l : ℤ) - ((l' : ℕ) : ℤ))} : ℝ)
        ≤ ((M / E + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (M : ℝ) / E + 1 := by push_cast; gcongr; exact Nat.cast_div_le
    _ = M * g / D + 1 := by rw [← hEr]; field_simp
    _ ≤ M * h / D + 1 := by gcongr

/-- **Mean square of the differenced sums over the orbit.**  Averaging over `j` turns the
slopes `u 16ʲ X² h` into complete orbits, which vanish unless `D ∣ h (l − l')`. -/
theorem sum_norm_geom_sq_le {Q T₀ D α β : ℕ} (hQ : Q = 3 ^ α * 5 ^ β) {X u : ℤ}
    (hT : (16 : ℤ) ^ T₀ = 1 + X) (hX : (Q : ℤ) ∣ X ^ 3) (hD : 0 < D)
    (hDv : ∀ v : ℤ, (Q : ℤ) ∣ 15 * (u * X ^ 2 * v) → (D : ℤ) ∣ v) {h : ℕ} (hh : 0 < h)
    (M : ℕ) :
    ∑ j ∈ range T₀, ‖∑ l ∈ range M, ephase Q (u * 16 ^ j * X ^ 2 * h * l)‖ ^ 2 ≤
      T₀ * (M * (M * h / D + 1)) := by
  have hkey : ((∑ j ∈ range T₀, ‖∑ l ∈ range M, ephase Q (u * 16 ^ j * X ^ 2 * h * l)‖ ^ 2 :
      ℝ) : ℂ) = ∑ l ∈ range M, ∑ l' ∈ range M, ∑ j ∈ range T₀,
        ephase Q ((u * X ^ 2 * (h * ((l : ℤ) - l'))) * 16 ^ j) := by
    rw [Complex.ofReal_sum]
    simp_rw [norm_sum_ephase_sq]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun l' _ => sum_congr rfl fun j _ => ?_
    congr 1
    ring
  have hZ : ∀ l l' : ℕ, ‖∑ j ∈ range T₀, ephase Q ((u * X ^ 2 * (h * ((l : ℤ) - l'))) * 16 ^ j)‖
      ≤ if (D : ℤ) ∣ h * ((l : ℤ) - l') then (T₀ : ℝ) else 0 := by
    intro l l'
    split_ifs with hd
    · refine (norm_sum_le _ _).trans ?_
      simp [norm_ephase]
    · have : ∑ j ∈ range T₀, ephase Q ((u * X ^ 2 * (h * ((l : ℤ) - l'))) * 16 ^ j) = 0 := by
        by_contra hS
        rw [hQ] at hS
        have hper : ((3 ^ α * 5 ^ β : ℕ) : ℤ) ∣ (u * X ^ 2 * (h * ((l : ℤ) - l'))) *
            (16 ^ T₀ - 1) := by
          rw [← hQ, hT, add_sub_cancel_left]
          obtain ⟨t, ht⟩ := hX
          exact ⟨u * (h * ((l : ℤ) - l')) * t,
            by linear_combination (u * (h * ((l : ℤ) - l'))) * ht⟩
        exact hd (hDv _ (hQ ▸ dvd_fifteen_mul_of_sum_ne_zero hper hS))
      rw [this, norm_zero]
  have hnn : (0 : ℝ) ≤ ∑ j ∈ range T₀,
      ‖∑ l ∈ range M, ephase Q (u * 16 ^ j * X ^ 2 * h * l)‖ ^ 2 := by positivity
  calc ∑ j ∈ range T₀, ‖∑ l ∈ range M, ephase Q (u * 16 ^ j * X ^ 2 * h * l)‖ ^ 2
      = ‖((∑ j ∈ range T₀, ‖∑ l ∈ range M, ephase Q (u * 16 ^ j * X ^ 2 * h * l)‖ ^ 2 :
          ℝ) : ℂ)‖ := (Complex.norm_of_nonneg hnn).symm
    _ ≤ ∑ l ∈ range M, ∑ l' ∈ range M, if (D : ℤ) ∣ h * ((l : ℤ) - l') then (T₀ : ℝ) else 0 := by
        rw [hkey]
        refine (norm_sum_le _ _).trans (sum_le_sum fun l _ => ?_)
        exact (norm_sum_le _ _).trans (sum_le_sum fun l' _ => hZ l l')
    _ = T₀ * ∑ l ∈ range M, (#{l' ∈ range M | (D : ℤ) ∣ h * ((l : ℤ) - ((l' : ℕ) : ℤ))} : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl fun l _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ T₀ * ∑ _l ∈ range M, ((M : ℝ) * h / D + 1) := by
        gcongr with l _
        exact card_filter_dvd_mul_sub_le hD hh l M
    _ = T₀ * (M * (M * h / D + 1)) := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ### The block bound -/

theorem sum_range_mul_eq_sum_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) (T N : ℕ) :
    ∑ i ∈ range (T * N), f i = ∑ j ∈ range T, ∑ l ∈ range N, f (j + T * l) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [mul_add, mul_one, sum_range_add, ih]
    simp_rw [sum_range_succ, sum_add_distrib]
    congr 1
    exact sum_congr rfl fun j _ => by rw [add_comm]

/-- **Korobov's bound on blocks.**  For `Q = 3ᵅ5ᵝ`, `16^{T₀} = 1 + X`, `Q ∣ X³` and the
divisibility transfer `Q ∣ 15 u X² v ⟹ D ∣ v`,
`‖Σ_{i < T₀N} e_Q(u 16ⁱ)‖² ≤ T₀² (N + 2 √(N⁵/D + N³))`. -/
theorem norm_sum_sixteen_block_sq_le {Q T₀ D α β : ℕ} (hQ : Q = 3 ^ α * 5 ^ β) {X u : ℤ}
    (hT : (16 : ℤ) ^ T₀ = 1 + X) (hX : (Q : ℤ) ∣ X ^ 3) (hD : 0 < D)
    (hDv : ∀ v : ℤ, (Q : ℤ) ∣ 15 * (u * X ^ 2 * v) → (D : ℤ) ∣ v) (N : ℕ) :
    ‖∑ i ∈ range (T₀ * N), ephase Q (u * 16 ^ i)‖ ^ 2 ≤
      (T₀ : ℝ) ^ 2 * (N + 2 * Real.sqrt ((N : ℝ) ^ 5 / D + N ^ 3)) := by
  have hQ0 : Q ≠ 0 := by rw [hQ]; positivity
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set S : ℕ → ℂ := fun j => ∑ l ∈ range N, ephase Q (u * 16 ^ (j + T₀ * l)) with hS
  set G : ℕ → ℕ → ℂ := fun h j =>
    ∑ l ∈ range (N - h), ephase Q (u * 16 ^ j * X ^ 2 * h * l) with hG
  have hre : ∑ i ∈ range (T₀ * N), ephase Q (u * 16 ^ i) = ∑ j ∈ range T₀, S j :=
    sum_range_mul_eq_sum_sum _ _ _
  have hCS1 : ‖∑ j ∈ range T₀, S j‖ ^ 2 ≤ T₀ * ∑ j ∈ range T₀, ‖S j‖ ^ 2 := by
    calc _ ≤ (∑ j ∈ range T₀, ‖S j‖) ^ 2 := by gcongr; exact norm_sum_le _ _
      _ ≤ _ := by simpa using sq_sum_le_card_mul_sum_sq (s := range T₀) (f := fun j => ‖S j‖)
  have hdiff : ∀ j, ‖S j‖ ^ 2 ≤ N + 2 * ∑ h ∈ Ico 1 N, ‖G h j‖ := fun j =>
    norm_sum_orbit_sq_le_geometric hQ0 (g := 16) hT hX u j N
  have hms : ∀ h ∈ Ico 1 N, ∑ j ∈ range T₀, ‖G h j‖ ^ 2 ≤ T₀ * (N * (N * N / D + 1)) := by
    intro h hh
    rw [mem_Ico] at hh
    refine (sum_norm_geom_sq_le hQ hT hX hD hDv hh.1 (N - h)).trans ?_
    have hM : ((N - h : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N h
    have hhN : (h : ℝ) ≤ N := by exact_mod_cast hh.2.le
    gcongr
  set A := ∑ h ∈ Ico 1 N, ∑ j ∈ range T₀, ‖G h j‖ with hA
  have hA0 : 0 ≤ A := by positivity
  have hA2 : A ^ 2 ≤ (T₀ : ℝ) ^ 2 * ((N : ℝ) ^ 5 / D + N ^ 3) := by
    have hB : ∀ h ∈ Ico 1 N, (∑ j ∈ range T₀, ‖G h j‖) ^ 2 ≤
        T₀ * (T₀ * (N * (N * N / D + 1))) := by
      intro h hh
      calc (∑ j ∈ range T₀, ‖G h j‖) ^ 2 ≤ T₀ * ∑ j ∈ range T₀, ‖G h j‖ ^ 2 := by
            simpa using sq_sum_le_card_mul_sum_sq (s := range T₀) (f := fun j => ‖G h j‖)
        _ ≤ _ := by gcongr; exact hms h hh
    have hcard : ((#(Ico 1 N) : ℕ) : ℝ) ≤ N := by
      simp only [Nat.card_Ico]; exact_mod_cast Nat.sub_le N 1
    calc A ^ 2 ≤ (#(Ico 1 N) : ℝ) * ∑ h ∈ Ico 1 N, (∑ j ∈ range T₀, ‖G h j‖) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (#(Ico 1 N) : ℝ) * ∑ _h ∈ Ico 1 N, (T₀ * (T₀ * (N * (N * N / D + 1))) : ℝ) := by
          gcongr with h hh; exact hB h hh
      _ = (#(Ico 1 N) : ℝ) * (#(Ico 1 N) : ℝ) * (T₀ * (T₀ * (N * (N * N / D + 1)))) := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ (N : ℝ) * N * (T₀ * (T₀ * (N * (N * N / D + 1)))) := by gcongr
      _ = (T₀ : ℝ) ^ 2 * ((N : ℝ) ^ 5 / D + N ^ 3) := by field_simp
  have hAle : A ≤ T₀ * Real.sqrt ((N : ℝ) ^ 5 / D + N ^ 3) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ T₀), ← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le hA2
  rw [hre]
  calc ‖∑ j ∈ range T₀, S j‖ ^ 2 ≤ T₀ * ∑ j ∈ range T₀, ‖S j‖ ^ 2 := hCS1
    _ ≤ T₀ * ∑ j ∈ range T₀, ((N : ℝ) + 2 * ∑ h ∈ Ico 1 N, ‖G h j‖) := by
        gcongr with j _; exact hdiff j
    _ = T₀ * (T₀ * N + 2 * A) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, hA, sum_comm]
    _ ≤ T₀ * (T₀ * N + 2 * (T₀ * Real.sqrt ((N : ℝ) ^ 5 / D + N ^ 3))) := by gcongr
    _ = (T₀ : ℝ) ^ 2 * (N + 2 * Real.sqrt ((N : ℝ) ^ 5 / D + N ^ 3)) := by ring

/-- **Korobov's bound for sums of any length.**  With `N = ⌊L/T₀⌋`,
`‖Σ_{i<L} e_Q(u 16ⁱ)‖ ≤ T₀ + T₀ √(N + 2 √(N⁵/D + N³))`. -/
theorem norm_sum_sixteen_le {Q T₀ D α β : ℕ} (hQ : Q = 3 ^ α * 5 ^ β) {X u : ℤ}
    (hT : (16 : ℤ) ^ T₀ = 1 + X) (hX : (Q : ℤ) ∣ X ^ 3) (hD : 0 < D)
    (hDv : ∀ v : ℤ, (Q : ℤ) ∣ 15 * (u * X ^ 2 * v) → (D : ℤ) ∣ v) (hT0 : 0 < T₀) (L : ℕ) :
    ‖∑ i ∈ range L, ephase Q (u * 16 ^ i)‖ ≤ T₀ + T₀ * Real.sqrt ((L / T₀ : ℕ) +
      2 * Real.sqrt (((L / T₀ : ℕ) : ℝ) ^ 5 / D + ((L / T₀ : ℕ) : ℝ) ^ 3)) := by
  obtain ⟨N, hN⟩ : ∃ N, N = L / T₀ := ⟨_, rfl⟩
  rw [← hN]
  have hL : L = T₀ * N + L % T₀ := by rw [hN]; exact (Nat.div_add_mod L T₀).symm
  have hblock := norm_sum_sixteen_block_sq_le hQ hT hX hD hDv N (u := u)
  conv_lhs => rw [hL, sum_range_add]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm (T₀ : ℝ)]
  gcongr
  · rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ T₀),
      ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hblock
  · refine (norm_sum_le _ _).trans ?_
    simp only [norm_ephase, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast (Nat.mod_lt L hT0).le

/-! ### Korobov parameters for `Q = 3ᵅ5ᵝ` -/

/-- The Korobov step exponent `⌈α/3⌉ − 1`. -/
def korobovExp (α : ℕ) : ℕ := (α + 2) / 3 - 1

/-- `3^{s+1} 5^{t+1}` divides `16^{3ˢ5ᵗ} − 1` exactly in both primes. -/
theorem sixteen_pow_sub_one_val (s t : ℕ) :
    3 ^ (s + 1) * 5 ^ (t + 1) ∣ 16 ^ (3 ^ s * 5 ^ t) - 1 ∧
      ¬ 3 ^ (s + 2) ∣ 16 ^ (3 ^ s * 5 ^ t) - 1 ∧ ¬ 5 ^ (t + 2) ∣ 16 ^ (3 ^ s * 5 ^ t) - 1 := by
  refine ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow _ _ (by norm_num)) ?_ ?_, ?_, ?_⟩
  · rw [lte_three _ _ (by omega), show s + 1 - 1 = s by omega]
    exact dvd_mul_right _ _
  · rw [lte_five _ _ (by omega), show t + 1 - 1 = t by omega]
    exact dvd_mul_left _ _
  · rw [lte_three _ _ (by omega), show s + 2 - 1 = s + 1 by omega, pow_succ]
    intro h
    have := Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num : 0 < 3) s) h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this) (by norm_num)
  · rw [lte_five _ _ (by omega), show t + 2 - 1 = t + 1 by omega, pow_succ, mul_comm (3 ^ s)]
    intro h
    have := Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num : 0 < 5) t) h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five this) (by norm_num)

theorem pow_mul_pow_le {a b c d : ℕ} (hac : a ≤ c) (hbd : b ≤ d) :
    3 ^ a * 5 ^ b ≤ 3 ^ c * 5 ^ d :=
  Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hac) (Nat.pow_le_pow_right (by norm_num) hbd)

/-- A coprimality transfer: `pᵉ ∣ m w` with `p` prime to `m` gives `pᵉ ∣ w`. -/
theorem int_pow_dvd_of_dvd_mul {p : ℤ} (hp : Prime p) {m w : ℤ} (hm : ¬ p ∣ m) {e : ℕ}
    (h : p ^ e ∣ m * w) : p ^ e ∣ w :=
  IsCoprime.dvd_of_dvd_mul_left (IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp).mpr hm)) h

/-- **Korobov parameters.**  For `Q = 3ᵅ5ᵝ` and `u` prime to `Q` there are `T₀, D, X` with
`16^{T₀} = 1 + X`, `Q ∣ X³`, `Q ∣ 15 u X² v ⟹ D ∣ v`, `T₀³ ≤ Q`, `Q ≤ 3⁷5⁷ D³` and
`Q² ≤ 3⁹5⁹ (T₀ D)³`. -/
theorem exists_korobov_parameters (α β : ℕ) {u : ℤ}
    (hu : IsCoprime u ((3 ^ α * 5 ^ β : ℕ) : ℤ)) :
    ∃ T₀ D : ℕ, ∃ X : ℤ, 0 < T₀ ∧ 0 < D ∧ (16 : ℤ) ^ T₀ = 1 + X ∧
      ((3 ^ α * 5 ^ β : ℕ) : ℤ) ∣ X ^ 3 ∧
      (∀ v : ℤ, ((3 ^ α * 5 ^ β : ℕ) : ℤ) ∣ 15 * (u * X ^ 2 * v) → (D : ℤ) ∣ v) ∧
      T₀ ^ 3 ≤ 3 ^ α * 5 ^ β ∧ 3 ^ α * 5 ^ β ≤ 3 ^ 7 * 5 ^ 7 * D ^ 3 ∧
      (3 ^ α * 5 ^ β) ^ 2 ≤ 3 ^ 9 * 5 ^ 9 * (T₀ * D) ^ 3 := by
  obtain ⟨s, hs⟩ : ∃ s, s = korobovExp α := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = korobovExp β := ⟨_, rfl⟩
  unfold korobovExp at hs ht
  obtain ⟨hdiv, h3, h5⟩ := sixteen_pow_sub_one_val s t
  have h16 : 1 ≤ 16 ^ (3 ^ s * 5 ^ t) := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨θ, hθ⟩ := hdiv
  have hXZ : (16 : ℤ) ^ (3 ^ s * 5 ^ t) - 1 = (3 : ℤ) ^ (s + 1) * 5 ^ (t + 1) * θ := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hθ
    simp only [Nat.cast_sub h16, Nat.cast_pow, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at this
    exact this
  have hθ3 : ¬ (3 : ℤ) ∣ θ := by
    rintro h
    obtain ⟨r, rfl⟩ := Int.natCast_dvd_natCast.mp (by exact_mod_cast h : ((3 : ℕ) : ℤ) ∣ θ)
    exact h3 ⟨5 ^ (t + 1) * r, by rw [hθ, pow_succ 3 (s + 1)]; ring⟩
  have hθ5 : ¬ (5 : ℤ) ∣ θ := by
    rintro h
    obtain ⟨r, rfl⟩ := Int.natCast_dvd_natCast.mp (by exact_mod_cast h : ((5 : ℕ) : ℤ) ∣ θ)
    exact h5 ⟨3 ^ (s + 1) * r, by rw [hθ, pow_succ 5 (t + 1)]; ring⟩
  have hp5 : Prime (5 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_five
  refine ⟨3 ^ s * 5 ^ t, 3 ^ (α - (2 * s + 3)) * 5 ^ (β - (2 * t + 3)),
    (16 : ℤ) ^ (3 ^ s * 5 ^ t) - 1, by positivity, by positivity, by ring, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hXZ]
    refine Dvd.intro (3 ^ (3 * (s + 1) - α) * 5 ^ (3 * (t + 1) - β) * θ ^ 3) ?_
    have e3 : (3 : ℤ) ^ α * 3 ^ (3 * (s + 1) - α) = 3 ^ (3 * (s + 1)) := by
      rw [← pow_add]; congr 1; omega
    have e5 : (5 : ℤ) ^ β * 5 ^ (3 * (t + 1) - β) = 5 ^ (3 * (t + 1)) := by
      rw [← pow_add]; congr 1; omega
    push_cast
    linear_combination (5 ^ β * 5 ^ (3 * (t + 1) - β) * θ ^ 3) * e3 +
      (3 ^ (3 * (s + 1)) * θ ^ 3) * e5
  · intro v hv
    have hcop3 : ¬ (3 : ℤ) ∣ u ∨ α = 0 := by
      rcases Nat.eq_zero_or_pos α with h0 | h0
      · exact Or.inr h0
      · left
        intro h3u
        have h3Q : (3 : ℤ) ∣ ((3 ^ α * 5 ^ β : ℕ) : ℤ) :=
          ⟨3 ^ (α - 1) * 5 ^ β, by push_cast; rw [← mul_assoc, ← pow_succ']; congr 2; omega⟩
        exact Int.prime_three.not_unit (hu.isUnit_of_dvd' h3u h3Q)
    have hcop5 : ¬ (5 : ℤ) ∣ u ∨ β = 0 := by
      rcases Nat.eq_zero_or_pos β with h0 | h0
      · exact Or.inr h0
      · left
        intro h5u
        have h5Q : (5 : ℤ) ∣ ((3 ^ α * 5 ^ β : ℕ) : ℤ) :=
          ⟨3 ^ α * 5 ^ (β - 1), by push_cast; rw [mul_left_comm, ← pow_succ']; congr 2; omega⟩
        exact hp5.not_unit (hu.isUnit_of_dvd' h5u h5Q)
    have hv' : (3 : ℤ) ^ α * 5 ^ β ∣
        3 ^ (2 * s + 3) * 5 ^ (2 * t + 3) * (u * θ ^ 2 * v) := by
      have := hv
      rw [hXZ] at this
      push_cast at this
      refine this.trans (Dvd.intro 1 ?_)
      ring
    have hD3 : (3 : ℤ) ^ (α - (2 * s + 3)) ∣ v := by
      rcases Nat.eq_zero_or_pos (α - (2 * s + 3)) with h0 | h0
      · rw [h0, pow_zero]; exact one_dvd _
      have hu3 : ¬ (3 : ℤ) ∣ u := hcop3.resolve_right (by omega)
      have h1 : (3 : ℤ) ^ (2 * s + 3) * 3 ^ (α - (2 * s + 3)) ∣
          3 ^ (2 * s + 3) * (5 ^ (2 * t + 3) * (u * θ ^ 2) * v) := by
        rw [← pow_add, show 2 * s + 3 + (α - (2 * s + 3)) = α by omega]
        refine (dvd_mul_right _ _).trans (hv'.trans (Dvd.intro 1 ?_))
        ring
      have h2 := (mul_dvd_mul_iff_left (by positivity)).mp h1
      refine int_pow_dvd_of_dvd_mul Int.prime_three ?_ h2
      intro h
      rcases Int.prime_three.dvd_or_dvd h with h | h
      · exact absurd (Int.Prime.dvd_pow' Nat.prime_three h) (by decide)
      · rcases Int.prime_three.dvd_or_dvd h with h | h
        · exact hu3 h
        · exact hθ3 (Int.prime_three.dvd_of_dvd_pow h)
    have hD5 : (5 : ℤ) ^ (β - (2 * t + 3)) ∣ v := by
      rcases Nat.eq_zero_or_pos (β - (2 * t + 3)) with h0 | h0
      · rw [h0, pow_zero]; exact one_dvd _
      have hu5 : ¬ (5 : ℤ) ∣ u := hcop5.resolve_right (by omega)
      have h1 : (5 : ℤ) ^ (2 * t + 3) * 5 ^ (β - (2 * t + 3)) ∣
          5 ^ (2 * t + 3) * (3 ^ (2 * s + 3) * (u * θ ^ 2) * v) := by
        rw [← pow_add, show 2 * t + 3 + (β - (2 * t + 3)) = β by omega]
        refine (dvd_mul_left _ _).trans (hv'.trans (Dvd.intro 1 ?_))
        ring
      have h2 := (mul_dvd_mul_iff_left (by positivity)).mp h1
      refine int_pow_dvd_of_dvd_mul hp5 ?_ h2
      intro h
      rcases hp5.dvd_or_dvd h with h | h
      · exact absurd (Int.Prime.dvd_pow' Nat.prime_five h) (by decide)
      · rcases hp5.dvd_or_dvd h with h | h
        · exact hu5 h
        · exact hθ5 (hp5.dvd_of_dvd_pow h)
    push_cast
    exact IsCoprime.mul_dvd (IsCoprime.pow ((Prime.coprime_iff_not_dvd Int.prime_three).mpr
      (by decide))) hD3 hD5
  · rw [mul_pow, ← pow_mul, ← pow_mul]
    exact pow_mul_pow_le (by omega) (by omega)
  · rw [mul_pow, ← pow_mul, ← pow_mul, mul_mul_mul_comm, ← pow_add, ← pow_add]
    exact pow_mul_pow_le (by omega) (by omega)
  · rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
      ← pow_mul, ← pow_mul, mul_mul_mul_comm (3 ^ (s * 3)), ← pow_add, ← pow_add,
      mul_mul_mul_comm (3 ^ 9), ← pow_add, ← pow_add]
    exact pow_mul_pow_le (by omega) (by omega)

/-- **Korobov's bound, uniform form.**  If `Q = 3ᵅ5ᵝ ≤ P²`, `L ≤ P` and `L² ≤ c Q` with
`1 ≤ c`, `1 ≤ P`, then `‖Σ_{i<L} e_Q(u 16ⁱ)‖¹² ≤ 2¹² 18³ 3⁹ 5⁹ c² P¹¹` for `u` prime to `Q`. -/
theorem norm_sum_sixteen_pow_twelve_le {α β : ℕ} {u : ℤ}
    (hu : IsCoprime u ((3 ^ α * 5 ^ β : ℕ) : ℤ)) {L : ℕ} {P c : ℝ} (hP : 1 ≤ P) (hc : 1 ≤ c)
    (hQP : ((3 ^ α * 5 ^ β : ℕ) : ℝ) ≤ P ^ 2) (hLP : (L : ℝ) ≤ P)
    (hLQ : (L : ℝ) ^ 2 ≤ c * (3 ^ α * 5 ^ β : ℕ)) :
    ‖∑ i ∈ range L, ephase (3 ^ α * 5 ^ β) (u * 16 ^ i)‖ ^ 12 ≤
      2 ^ 12 * 18 ^ 3 * (3 ^ 9 * 5 ^ 9 * c ^ 2) * P ^ 11 := by
  obtain ⟨T₀, D, X, hT0, hD, hT, hX, hDv, hs1, -, hs3⟩ := exists_korobov_parameters α β hu
  have hmain := norm_sum_sixteen_le rfl hT hX hD hDv hT0 L (u := u)
  obtain ⟨N, hN⟩ : ∃ N, N = L / T₀ := ⟨_, rfl⟩
  rw [← hN] at hmain
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = 3 ^ α * 5 ^ β := ⟨_, rfl⟩
  rw [← hQ] at hQP hLQ hs1 hs3 hmain ⊢
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 3 ^ 9 * 5 ^ 9 * c ^ 2 := ⟨_, rfl⟩
  rw [← hK]
  have hK1 : 1 ≤ K := by rw [hK]; nlinarith
  have hTr : (0 : ℝ) < T₀ := by exact_mod_cast hT0
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hTN : (T₀ : ℝ) * N ≤ L := by rw [hN]; exact_mod_cast Nat.mul_div_le L T₀
  have hQr : (T₀ : ℝ) ^ 3 ≤ Q := by exact_mod_cast hs1
  have hQ2 : (Q : ℝ) ^ 2 ≤ 3 ^ 9 * 5 ^ 9 * ((T₀ : ℝ) * D) ^ 3 := by exact_mod_cast hs3
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hP0 : 0 ≤ P := by linarith
  have hTN0 : (0 : ℝ) ≤ (T₀ : ℝ) * N := by positivity
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (N : ℝ) ^ 5 / D + N ^ 3 := ⟨_, rfl⟩
  rw [← hW] at hmain
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (T₀ : ℝ) * Real.sqrt (N + 2 * Real.sqrt W) := ⟨_, rfl⟩
  rw [← hY] at hmain
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  -- `Y⁴ ≤ 18 max(Z₁, Z₂, Z₃)`
  obtain ⟨Z₁, hZ₁⟩ : ∃ Z : ℝ, Z = (T₀ : ℝ) ^ 4 * N ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z₂, hZ₂⟩ : ∃ Z : ℝ, Z = (T₀ : ℝ) ^ 4 * N ^ 5 / D := ⟨_, rfl⟩
  obtain ⟨Z₃, hZ₃⟩ : ∃ Z : ℝ, Z = (T₀ : ℝ) ^ 4 * N ^ 3 := ⟨_, rfl⟩
  have hY4 : Y ^ 4 ≤ 18 * max Z₁ (max Z₂ Z₃) := by
    have hs : Real.sqrt (N + 2 * Real.sqrt W) ^ 2 = N + 2 * Real.sqrt W :=
      Real.sq_sqrt (by positivity)
    have hw : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW0
    have e : Y ^ 4 = (T₀ : ℝ) ^ 4 * (N + 2 * Real.sqrt W) ^ 2 := by
      rw [hY, mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul (Real.sqrt _), hs]
    have h2 : ((N : ℝ) + 2 * Real.sqrt W) ^ 2 ≤ 2 * N ^ 2 + 8 * W := by
      nlinarith [sq_nonneg ((N : ℝ) - 2 * Real.sqrt W)]
    have hm1 : Z₁ ≤ max Z₁ (max Z₂ Z₃) := le_max_left _ _
    have hm2 : Z₂ ≤ max Z₁ (max Z₂ Z₃) := (le_max_left _ _).trans (le_max_right _ _)
    have hm3 : Z₃ ≤ max Z₁ (max Z₂ Z₃) := (le_max_right _ _).trans (le_max_right _ _)
    calc Y ^ 4 = (T₀ : ℝ) ^ 4 * (N + 2 * Real.sqrt W) ^ 2 := e
      _ ≤ (T₀ : ℝ) ^ 4 * (2 * N ^ 2 + 8 * W) := by gcongr
      _ = 2 * Z₁ + 8 * Z₂ + 8 * Z₃ := by rw [hW, hZ₁, hZ₂, hZ₃]; ring
      _ ≤ 18 * max Z₁ (max Z₂ Z₃) := by linarith
  have hP11 : P ^ 11 ≤ K * P ^ 11 := le_mul_of_one_le_left (by positivity) hK1
  have hb1 : Z₁ ^ 3 ≤ K * P ^ 11 := by
    have e : Z₁ ^ 3 = ((T₀ : ℝ) ^ 3) ^ 2 * ((T₀ : ℝ) * N) ^ 6 := by rw [hZ₁]; ring
    calc Z₁ ^ 3 = ((T₀ : ℝ) ^ 3) ^ 2 * ((T₀ : ℝ) * N) ^ 6 := e
      _ ≤ (P ^ 2) ^ 2 * P ^ 6 := by
          gcongr
          · exact hQr.trans hQP
          · exact hTN.trans hLP
      _ = P ^ 10 := by ring
      _ ≤ P ^ 11 := pow_le_pow_right₀ hP (by norm_num)
      _ ≤ K * P ^ 11 := hP11
  have hb2 : Z₂ ^ 3 ≤ K * P ^ 11 := by
    rcases eq_or_lt_of_le hL0 with hL | hL
    · have : (N : ℝ) = 0 := by
        have : (T₀ : ℝ) * N ≤ 0 := by rw [hL]; exact hTN
        nlinarith
      rw [hZ₂, this]; simp; positivity
    have hL4 : (L : ℝ) ^ 4 ≤ K * ((T₀ : ℝ) * D) ^ 3 := by
      calc (L : ℝ) ^ 4 = ((L : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ (c * Q) ^ 2 := by gcongr
        _ = c ^ 2 * (Q : ℝ) ^ 2 := by ring
        _ ≤ c ^ 2 * (3 ^ 9 * 5 ^ 9 * ((T₀ : ℝ) * D) ^ 3) := by gcongr
        _ = K * ((T₀ : ℝ) * D) ^ 3 := by rw [hK]; ring
    have e : Z₂ ^ 3 * ((T₀ : ℝ) * D) ^ 3 = ((T₀ : ℝ) * N) ^ 15 := by
      rw [hZ₂]; field_simp
    have h15 : ((T₀ : ℝ) * N) ^ 15 ≤ (L : ℝ) ^ 15 := by gcongr
    have hZ0 : 0 ≤ Z₂ ^ 3 := by rw [hZ₂]; positivity
    have key : Z₂ ^ 3 * (L : ℝ) ^ 4 ≤ K * (L : ℝ) ^ 11 * (L : ℝ) ^ 4 := by
      calc Z₂ ^ 3 * (L : ℝ) ^ 4 ≤ Z₂ ^ 3 * (K * ((T₀ : ℝ) * D) ^ 3) := by gcongr
        _ = K * (Z₂ ^ 3 * ((T₀ : ℝ) * D) ^ 3) := by ring
        _ = K * ((T₀ : ℝ) * N) ^ 15 := by rw [e]
        _ ≤ K * (L : ℝ) ^ 15 := by gcongr
        _ = K * (L : ℝ) ^ 11 * (L : ℝ) ^ 4 := by ring
    have := le_of_mul_le_mul_right key (by positivity)
    calc Z₂ ^ 3 ≤ K * (L : ℝ) ^ 11 := this
      _ ≤ K * P ^ 11 := by gcongr
  have hb3 : Z₃ ^ 3 ≤ K * P ^ 11 := by
    have e : Z₃ ^ 3 = (T₀ : ℝ) ^ 3 * ((T₀ : ℝ) * N) ^ 9 := by rw [hZ₃]; ring
    calc Z₃ ^ 3 = (T₀ : ℝ) ^ 3 * ((T₀ : ℝ) * N) ^ 9 := e
      _ ≤ P ^ 2 * P ^ 9 := by
          gcongr
          · exact hQr.trans hQP
          · exact hTN.trans hLP
      _ = P ^ 11 := by ring
      _ ≤ K * P ^ 11 := hP11
  have hM : (max Z₁ (max Z₂ Z₃)) ^ 3 ≤ K * P ^ 11 := by
    rcases max_choice Z₁ (max Z₂ Z₃) with h | h <;> rw [h]
    · exact hb1
    · rcases max_choice Z₂ Z₃ with h' | h' <;> rw [h']
      · exact hb2
      · exact hb3
  have hY12 : Y ^ 12 ≤ 18 ^ 3 * (K * P ^ 11) := by
    have hm0 : 0 ≤ max Z₁ (max Z₂ Z₃) := le_trans (by rw [hZ₁]; positivity) (le_max_left _ _)
    calc Y ^ 12 = (Y ^ 4) ^ 3 := by ring
      _ ≤ (18 * max Z₁ (max Z₂ Z₃)) ^ 3 := by gcongr
      _ = 18 ^ 3 * (max Z₁ (max Z₂ Z₃)) ^ 3 := by ring
      _ ≤ 18 ^ 3 * (K * P ^ 11) := by gcongr
  have hT12 : (T₀ : ℝ) ^ 12 ≤ 18 ^ 3 * (K * P ^ 11) := by
    calc (T₀ : ℝ) ^ 12 = ((T₀ : ℝ) ^ 3) ^ 4 := by ring
      _ ≤ (P ^ 2) ^ 4 := by gcongr; exact hQr.trans hQP
      _ = P ^ 8 := by ring
      _ ≤ P ^ 11 := pow_le_pow_right₀ hP (by norm_num)
      _ ≤ K * P ^ 11 := hP11
      _ ≤ 18 ^ 3 * (K * P ^ 11) := le_mul_of_one_le_left (by positivity) (by norm_num)
  have hS : ‖∑ i ∈ range L, ephase Q (u * 16 ^ i)‖ ≤ 2 * max (T₀ : ℝ) Y := by
    refine hmain.trans ?_
    linarith [le_max_left (T₀ : ℝ) Y, le_max_right (T₀ : ℝ) Y]
  have hmax : (max (T₀ : ℝ) Y) ^ 12 ≤ 18 ^ 3 * (K * P ^ 11) := by
    rcases max_choice (T₀ : ℝ) Y with h | h <;> rw [h]
    · exact hT12
    · exact hY12
  calc ‖∑ i ∈ range L, ephase Q (u * 16 ^ i)‖ ^ 12 ≤ (2 * max (T₀ : ℝ) Y) ^ 12 := by gcongr
    _ = 2 ^ 12 * (max (T₀ : ℝ) Y) ^ 12 := by ring
    _ ≤ 2 ^ 12 * (18 ^ 3 * (K * P ^ 11)) := by gcongr
    _ = 2 ^ 12 * 18 ^ 3 * K * P ^ 11 := by ring

end GaloisForLFunctions.HTGeometry.ThreeFiveOrbit
