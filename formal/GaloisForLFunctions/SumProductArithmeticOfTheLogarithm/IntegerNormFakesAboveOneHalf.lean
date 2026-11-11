import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.IntegerNormFakeObstructions
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtiethsUnconditional
import GaloisForLFunctions.RHTower.BeurlingDeletionEulerProduct

/-!
# Integer-Norm Beurling Fakes for Every Remainder Exponent Above `1/2`

Every remainder exponent `β > 1/2` is realized unconditionally by a discrete Beurling system with
integer norms whose zeta function vanishes in `{Re s > 1/2}` at points where `ζ(s) ≠ 0`:

1. **Moreau's necklace identity (`sum_divisors_mul_necklaceCount`):** for every alphabet size
   `a ≥ 2` and length `m ≥ 1`, the counts `necklaceCount a d` of primitive cyclic orbits on
   `ZMod d → Fin a` satisfy `1 ≤ necklaceCount a d ≤ a ^ d` and
   `∑ d ∈ m.divisors, d * necklaceCount a d = a ^ m`, yielding the power-series Euler identity
   `∏_{k ≥ 1} (1 − z^k)^{u(a, k)} = 1 − a z` on `a ‖z‖ < 1`.
2. **Short-interval prime realization:** for any `β > 1/2`, choosing `b ≥ 4`, `M = b^2`,
   `a = b + 1`, and `β₀ = log a / log M ∈ (1/2, min β (29/50))`, the unconditional Guth–Maynard
   short-interval prime theorem supplies pairwise disjoint finite prime subsets `S_k` of
   cardinality `necklaceCount a k` inside `(M^k, M^k + M^{3k/5}]` for all large `k`.
3. **Analytic continuation and Rankin remainder (`exists_integerNormFakeAt_of_half_lt`):**
   deleting `S = ⋃_{k ≥ 1} S_k` from the rational primes produces an integer-norm Beurling system
   `keptPrimeSystem S` with `N_B(x) = A x + O(x^β)` (`A > 0`) whose regularized zeta function
   continues holomorphically to `{Re s > 1/4}` and vanishes both on the real axis at `s = β₀` and
   off the real axis at `s = β₀ + 2π i / log M`, where `ζ(s) ≠ 0`.
4. **Critical-threshold localization (`csInf_integerNormFakeExponents_mem_Icc`):** combining
   `Set.Ioi (1 / 2) ⊆ integerNormFakeExponents` with `nonneg_of_integerNormFakeAt` places the
   infimum of integer-norm fake remainder exponents unconditionally in `[0, 1/2]`.
-/

open Complex Finset Filter Topology
open RHTower RHTower.Sieve RHTower.BeurlingDeletion GaloisForLFunctions.RHTower
open GaloisForLFunctions.RigidArithmeticOfCuts

noncomputable section

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-! ## 1. Moreau's necklace identity on `ZMod m → Fin a` -/

/-- Cyclic shift of a word `w : ZMod m → Fin a` by `c : ZMod m`. -/
def wordShift {m a : ℕ} (c : ZMod m) (w : ZMod m → Fin a) : ZMod m → Fin a :=
  fun i => w (i + c)

@[simp]
theorem wordShift_apply {m a : ℕ} (c : ZMod m) (w : ZMod m → Fin a) (i : ZMod m) :
    wordShift c w i = w (i + c) := rfl

@[simp]
theorem wordShift_zero {m a : ℕ} (w : ZMod m → Fin a) : wordShift 0 w = w := by
  funext i; simp [wordShift]

theorem wordShift_add {m a : ℕ} (c₁ c₂ : ZMod m) (w : ZMod m → Fin a) :
    wordShift (c₁ + c₂) w = wordShift c₂ (wordShift c₁ w) := by
  funext i; simp [wordShift, add_assoc]

theorem wordShift_comm {m a : ℕ} (c₁ c₂ : ZMod m) (w : ZMod m → Fin a) :
    wordShift c₁ (wordShift c₂ w) = wordShift c₂ (wordShift c₁ w) := by
  rw [← wordShift_add, add_comm, wordShift_add]

/-- `d` is a positive period at most `m` of `w : ZMod m → Fin a`. -/
def IsWordPeriod {m a : ℕ} (w : ZMod m → Fin a) (d : ℕ) : Prop :=
  1 ≤ d ∧ d ≤ m ∧ wordShift (d : ZMod m) w = w

theorem isWordPeriod_self {m a : ℕ} [NeZero m] (w : ZMod m → Fin a) :
    IsWordPeriod w m :=
  ⟨Nat.pos_of_ne_zero (NeZero.ne m), le_rfl, by rw [ZMod.natCast_self, wordShift_zero]⟩

theorem exists_isWordPeriod {m a : ℕ} [NeZero m] (w : ZMod m → Fin a) :
    ∃ d : ℕ, IsWordPeriod w d :=
  ⟨m, isWordPeriod_self w⟩

/-- Minimal positive period of `w : ZMod m → Fin a`. -/
def minWordPeriod {m a : ℕ} [NeZero m] (w : ZMod m → Fin a) : ℕ :=
  open Classical in Nat.find (exists_isWordPeriod w)

theorem minWordPeriod_spec {m a : ℕ} [NeZero m] (w : ZMod m → Fin a) :
    IsWordPeriod w (minWordPeriod w) := by
  classical
  exact Nat.find_spec (exists_isWordPeriod w)

theorem minWordPeriod_le {m a : ℕ} [NeZero m] {w : ZMod m → Fin a} {d : ℕ}
    (hd : IsWordPeriod w d) : minWordPeriod w ≤ d := by
  classical
  exact Nat.find_min' (exists_isWordPeriod w) hd

private theorem wordShift_nat_mul_eq {m a : ℕ} {w : ZMod m → Fin a} {d : ℕ}
    (hd : wordShift (d : ZMod m) w = w) (q : ℕ) :
    wordShift ((d * q : ℕ) : ZMod m) w = w := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Nat.cast_add, wordShift_add, ih, hd]

/-- Every shift period of `w` is a multiple of `minWordPeriod w`. -/
theorem minWordPeriod_dvd_of_shift_eq {m a : ℕ} [NeZero m] {w : ZMod m → Fin a} {k : ℕ}
    (hk : wordShift (k : ZMod m) w = w) : minWordPeriod w ∣ k := by
  obtain ⟨hd1, hdm, hd⟩ := minWordPeriod_spec w
  set d := minWordPeriod w
  refine Nat.dvd_of_mod_eq_zero ?_
  by_contra hrem
  set r := k % d
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hrem
  have hrd : r < d := Nat.mod_lt k hd1
  have hdiv : k = d * (k / d) + r := (Nat.div_add_mod k d).symm
  have hr_shift : wordShift (r : ZMod m) w = w := by
    have hk' : wordShift (((d * (k / d) + r : ℕ) : ZMod m)) w = w := hdiv ▸ hk
    rwa [Nat.cast_add, wordShift_add, wordShift_nat_mul_eq hd] at hk'
  have hle : d ≤ r := minWordPeriod_le ⟨hr1, hrd.le.trans hdm, hr_shift⟩
  omega

theorem minWordPeriod_dvd {m a : ℕ} [NeZero m] (w : ZMod m → Fin a) :
    minWordPeriod w ∣ m :=
  minWordPeriod_dvd_of_shift_eq (by rw [ZMod.natCast_self, wordShift_zero])

theorem minWordPeriod_wordShift {m a : ℕ} [NeZero m] (c : ZMod m) (w : ZMod m → Fin a) :
    minWordPeriod (wordShift c w) = minWordPeriod w := by
  have hper : ∀ d : ℕ, IsWordPeriod (wordShift c w) d ↔ IsWordPeriod w d := by
    intro d
    refine ⟨fun ⟨h1, h2, hs⟩ => ⟨h1, h2, ?_⟩, fun ⟨h1, h2, hs⟩ => ⟨h1, h2, ?_⟩⟩
    · have h := congrArg (wordShift (-c)) hs
      rwa [wordShift_comm (d : ZMod m) c, ← wordShift_add, add_neg_cancel, wordShift_zero,
        ← wordShift_add, add_neg_cancel, wordShift_zero] at h
    · rw [wordShift_comm, hs]
  exact le_antisymm (minWordPeriod_le ((hper _).mpr (minWordPeriod_spec w)))
    (minWordPeriod_le ((hper _).mp (minWordPeriod_spec (wordShift c w))))

/-- Pullback of a word `ZMod d → Fin a` along the quotient projection `ZMod m →+* ZMod d`. -/
def pullWord {d m a : ℕ} (hdvd : d ∣ m) (v : ZMod d → Fin a) : ZMod m → Fin a :=
  fun i => v (ZMod.castHom hdvd (ZMod d) i)

theorem pullWord_injective {d m a : ℕ} (hdvd : d ∣ m) :
    Function.Injective (pullWord hdvd : (ZMod d → Fin a) → (ZMod m → Fin a)) := by
  intro v₁ v₂ h
  funext j
  obtain ⟨i, rfl⟩ := ZMod.castHom_surjective hdvd j
  exact congrFun h i

theorem wordShift_pullWord {d m a : ℕ} (hdvd : d ∣ m) (k : ℕ) (v : ZMod d → Fin a) :
    wordShift (k : ZMod m) (pullWord hdvd v) = pullWord hdvd (wordShift (k : ZMod d) v) := by
  funext i
  simp [wordShift, pullWord, map_add, map_natCast]

theorem minWordPeriod_pullWord {d m a : ℕ} [NeZero d] [NeZero m] (hdvd : d ∣ m)
    (v : ZMod d → Fin a) : minWordPeriod (pullWord hdvd v) = minWordPeriod v := by
  have hdm : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) hdvd
  obtain ⟨hv1, hvd, hvs⟩ := minWordPeriod_spec v
  have hle1 : minWordPeriod (pullWord hdvd v) ≤ minWordPeriod v := by
    refine minWordPeriod_le ⟨hv1, hvd.trans hdm, ?_⟩
    rw [wordShift_pullWord, hvs]
  obtain ⟨hp1, _, hps⟩ := minWordPeriod_spec (pullWord hdvd v)
  rw [wordShift_pullWord] at hps
  have hpv : wordShift (minWordPeriod (pullWord hdvd v) : ZMod d) v = v :=
    pullWord_injective hdvd hps
  exact le_antisymm hle1 (minWordPeriod_le ⟨hp1, hle1.trans hvd, hpv⟩)

theorem exists_pullWord_of_shift_eq {d m a : ℕ} [NeZero d] [NeZero m] (hdvd : d ∣ m)
    {w : ZMod m → Fin a} (hw : wordShift (d : ZMod m) w = w) :
    ∃ v : ZMod d → Fin a, pullWord hdvd v = w := by
  refine ⟨fun j => w (j.val : ZMod m), ?_⟩
  funext i
  simp only [pullWord]
  have hcast : ZMod.castHom hdvd (ZMod d) i = (i.val : ZMod d) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val i]
    rw [map_natCast]
  rw [hcast, ZMod.val_natCast]
  have hdiv : i.val = d * (i.val / d) + i.val % d := (Nat.div_add_mod i.val d).symm
  have hi : w i = wordShift ((i.val : ℕ) : ZMod m) w 0 := by
    simp [wordShift, ZMod.natCast_zmod_val]
  rw [hi, hdiv, Nat.cast_add, wordShift_add, wordShift_nat_mul_eq hw]
  simp [wordShift]

/-- Words in `ZMod d → Fin a` of minimal period `d`. -/
def primWords (d a : ℕ) [NeZero d] : Finset (ZMod d → Fin a) :=
  open Classical in Finset.univ.filter fun v => minWordPeriod v = d

/-- Cyclic shift orbit of `v : ZMod d → Fin a`. -/
def wordOrbit {d a : ℕ} (v : ZMod d → Fin a) : Finset (ZMod d → Fin a) :=
  open Classical in Finset.univ.image fun c : ZMod d => wordShift c v

theorem wordShift_injective_of_minWordPeriod {d a : ℕ} [NeZero d] {v : ZMod d → Fin a}
    (hv : minWordPeriod v = d) : Function.Injective (fun c : ZMod d => wordShift c v) := by
  intro c₁ c₂ h
  set c := c₁ - c₂
  have hc_shift : wordShift c v = v := by
    funext i
    have hi := congrFun h (i - c₂)
    simp only [wordShift_apply] at hi ⊢
    have e1 : i - c₂ + c₁ = i + c := by ring
    have e2 : i - c₂ + c₂ = i := sub_add_cancel i c₂
    rw [← e1, hi, e2]
  have hc_nat : wordShift (c.val : ZMod d) v = v := by
    rwa [ZMod.natCast_zmod_val]
  have hdvd : d ∣ c.val := hv ▸ minWordPeriod_dvd_of_shift_eq hc_nat
  have hval0 : c.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd c.val_lt
  have hc0 : c = 0 := by rw [← ZMod.natCast_zmod_val c, hval0, Nat.cast_zero]
  exact sub_eq_zero.mp hc0

theorem card_wordOrbit_of_minWordPeriod {d a : ℕ} [NeZero d] {v : ZMod d → Fin a}
    (hv : minWordPeriod v = d) : (wordOrbit v).card = d := by
  classical
  unfold wordOrbit
  rw [Finset.card_image_of_injective _ (wordShift_injective_of_minWordPeriod hv),
    Finset.card_univ, ZMod.card]

theorem wordOrbit_eq_of_mem {d a : ℕ} {u v : ZMod d → Fin a} (hu : u ∈ wordOrbit v) :
    wordOrbit u = wordOrbit v := by
  classical
  simp only [wordOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hu
  obtain ⟨c₀, rfl⟩ := hu
  ext w
  simp only [wordOrbit, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c₀ + c, by rw [wordShift_add]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c - c₀, by rw [← wordShift_add, add_sub_cancel]⟩

/-- Number of primitive `a`-ary necklaces of length `d`. -/
def necklaceCount (a d : ℕ) : ℕ :=
  open Classical in
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    ((primWords d a).image wordOrbit).card

theorem mul_necklaceCount_eq_card_primWords (a d : ℕ) [NeZero d] :
    d * necklaceCount a d = (primWords d a).card := by
  classical
  have hd0 : d ≠ 0 := NeZero.ne d
  unfold necklaceCount
  rw [dif_neg hd0]
  have hbi : ((primWords d a).image wordOrbit).biUnion id = primWords d a := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_image, id_eq, exists_exists_and_eq_and]
    constructor
    · rintro ⟨v, hv, hu⟩
      simp only [primWords, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      simp only [wordOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hu
      obtain ⟨c, rfl⟩ := hu
      rw [minWordPeriod_wordShift, hv]
    · intro hu
      refine ⟨u, hu, ?_⟩
      simp only [wordOrbit, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨0, wordShift_zero u⟩
  have hdisj : Set.PairwiseDisjoint ↑((primWords d a).image wordOrbit) id := by
    intro O₁ hO₁ O₂ hO₂ hne
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    simp only [Finset.mem_coe, Finset.mem_image] at hO₁ hO₂
    obtain ⟨v₁, _, rfl⟩ := hO₁
    obtain ⟨v₂, _, rfl⟩ := hO₂
    exact hne ((wordOrbit_eq_of_mem hu₁).symm.trans (wordOrbit_eq_of_mem hu₂))
  rw [← hbi, Finset.card_biUnion hdisj]
  have hcard : ∀ O ∈ (primWords d a).image wordOrbit, (id O).card = d := by
    intro O hO
    simp only [Finset.mem_image, primWords, Finset.mem_filter, Finset.mem_univ, true_and] at hO
    obtain ⟨v, hv, rfl⟩ := hO
    exact card_wordOrbit_of_minWordPeriod hv
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]

theorem necklaceCount_pos {a d : ℕ} (ha : 2 ≤ a) (hd : 1 ≤ d) :
    1 ≤ necklaceCount a d := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  unfold necklaceCount
  rw [dif_neg (by omega)]
  set v₀ : ZMod d → Fin a := fun i => if i = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hv₀ : minWordPeriod v₀ = d := by
    obtain ⟨hp1, hpd, hps⟩ := minWordPeriod_spec v₀
    by_contra hne
    have hlt : minWordPeriod v₀ < d := lt_of_le_of_ne hpd hne
    have hcast_ne : ((minWordPeriod v₀ : ℕ) : ZMod d) ≠ 0 := by
      intro h0
      have hv := congrArg ZMod.val h0
      rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hlt] at hv
      omega
    have h0 := congrFun hps 0
    simp only [wordShift_apply, zero_add, v₀, if_neg hcast_ne, ↓reduceIte, Fin.mk.injEq] at h0
    omega
  have hmem : v₀ ∈ primWords d a := by
    simp [primWords, hv₀]
  exact Finset.card_pos.mpr ⟨wordOrbit v₀, Finset.mem_image_of_mem _ hmem⟩

theorem mul_necklaceCount_le_pow (a d : ℕ) (hd : 1 ≤ d) :
    d * necklaceCount a d ≤ a ^ d := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  rw [mul_necklaceCount_eq_card_primWords]
  calc (primWords d a).card
      ≤ (Finset.univ : Finset (ZMod d → Fin a)).card := Finset.card_le_univ _
    _ = a ^ d := by simp [ZMod.card]

theorem necklaceCount_le_pow (a d : ℕ) (hd : 1 ≤ d) :
    necklaceCount a d ≤ a ^ d :=
  le_trans (Nat.le_mul_of_pos_left _ hd) (mul_necklaceCount_le_pow a d hd)

/-- **Moreau's necklace identity.**  For every `a : ℕ` and `m ≥ 1`,
`∑ d ∈ m.divisors, d * necklaceCount a d = a ^ m`. -/
theorem sum_divisors_mul_necklaceCount (a : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∑ d ∈ m.divisors, d * necklaceCount a d = a ^ m := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  have huniv : (Finset.univ : Finset (ZMod m → Fin a)).card = a ^ m := by
    simp [ZMod.card]
  rw [← huniv, Finset.card_eq_sum_card_fiberwise
    (f := minWordPeriod) (t := m.divisors)
    (fun w _ => Nat.mem_divisors.mpr ⟨minWordPeriod_dvd w, by omega⟩)]
  symm
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hm
  haveI : NeZero d := ⟨by omega⟩
  rw [← mul_necklaceCount_eq_card_primWords a d]
  refine Finset.card_nbij (pullWord hdvd) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨v, rfl⟩ := exists_pullWord_of_shift_eq hdvd (hw ▸ (minWordPeriod_spec w).2.2)
    refine ⟨v, ?_, rfl⟩
    simp only [Set.mem_coe, primWords, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [minWordPeriod_pullWord] at hw
  · intro v₁ _ v₂ _ h
    exact pullWord_injective hdvd h
  · intro v hv
    simp only [primWords, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [minWordPeriod_pullWord, hv]

/-! ## 2. Power-series and Dirichlet Euler identity for Moreau necklaces -/

/-- **Moreau logarithmic generating identity.**  For `a ≥ 2` and `z : ℂ` with `a ‖z‖ < 1`,
`∑_{k ≥ 0} necklaceCount a (k + 1) · (−log(1 − z^{k + 1})) = −log(1 − a z)`. -/
theorem tsum_necklaceCount_mul_neg_log_eq {a : ℕ} (ha : 2 ≤ a) {z : ℂ}
    (hz : (a : ℝ) * ‖z‖ < 1) :
    (∑' k : ℕ, (necklaceCount a (k + 1) : ℂ) * (-Complex.log (1 - z ^ (k + 1)))) =
      -Complex.log (1 - (a : ℂ) * z) := by
  have hz_half : ‖z‖ ≤ 1 / 2 := by
    have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [norm_nonneg z]
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz_half (by norm_num)
  have haz0 : 0 ≤ (a : ℝ) * ‖z‖ := by positivity
  set F : ℕ × ℕ → ℂ := fun p =>
    (necklaceCount a (p.1 + 1) : ℂ) * ((z ^ (p.1 + 1)) ^ (p.2 + 1) / ((p.2 + 1 : ℕ) : ℂ))
  have hmaj_sum : Summable (fun p : ℕ × ℕ =>
      ((a : ℝ) * ‖z‖) ^ (p.1 + 1) * (1 / 2 : ℝ) ^ p.2) := by
    have hg1 : Summable (fun k : ℕ => ((a : ℝ) * ‖z‖) ^ (k + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one haz0 hz)
    have hg2 : Summable (fun q : ℕ => (1 / 2 : ℝ) ^ q) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact hg1.mul_of_nonneg hg2 (fun _ => by positivity) (fun _ => by positivity)
  have hF_sum : Summable F := by
    refine Summable.of_norm_bounded hmaj_sum ?_
    rintro ⟨k, q⟩
    simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    have hnc : (necklaceCount a (k + 1) : ℝ) ≤ (a : ℝ) ^ (k + 1) := by
      exact_mod_cast necklaceCount_le_pow a (k + 1) (by omega)
    have hq1 : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
    have hdiv_le : (‖z‖ ^ (k + 1)) ^ (q + 1) / ((q + 1 : ℕ) : ℝ) ≤
        ‖z‖ ^ ((k + 1) * (q + 1)) := by
      rw [← pow_mul]
      exact div_le_self (by positivity) hq1
    have hexp : (k + 1) * (q + 1) = (k + 1) + (k + 1) * q := by ring
    have hpow_le : ‖z‖ ^ ((k + 1) * q) ≤ (1 / 2 : ℝ) ^ q := by
      calc ‖z‖ ^ ((k + 1) * q)
          ≤ (1 / 2 : ℝ) ^ ((k + 1) * q) := pow_le_pow_left₀ (norm_nonneg z) hz_half _
        _ ≤ (1 / 2 : ℝ) ^ q :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num)
              (Nat.le_mul_of_pos_left q (by omega))
    calc (necklaceCount a (k + 1) : ℝ) * ((‖z‖ ^ (k + 1)) ^ (q + 1) / ((q + 1 : ℕ) : ℝ))
        ≤ (a : ℝ) ^ (k + 1) * ‖z‖ ^ ((k + 1) * (q + 1)) :=
          mul_le_mul hnc hdiv_le (by positivity) (by positivity)
      _ = ((a : ℝ) * ‖z‖) ^ (k + 1) * ‖z‖ ^ ((k + 1) * q) := by
          rw [hexp, pow_add, mul_pow]
      _ ≤ ((a : ℝ) * ‖z‖) ^ (k + 1) * (1 / 2 : ℝ) ^ q :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
  -- Row evaluation: Taylor series of `-log(1 - z^{k+1})`.
  have hrow : ∀ k : ℕ, (∑' q : ℕ, F (k, q)) =
      (necklaceCount a (k + 1) : ℂ) * (-Complex.log (1 - z ^ (k + 1))) := by
    intro k
    have hzk : ‖z ^ (k + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg z) hz1 (by omega)
    have htay := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log hzk)
    simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, sub_zero] at htay
    simp only [F, ← tsum_mul_left, htay.tsum_eq]
  -- Group `ℕ × ℕ` by `m - 1 = (k + 1) * (q + 1) - 1`.
  set g : ℕ × ℕ → ℕ := fun p => (p.1 + 1) * (p.2 + 1) - 1
  set e := Equiv.sigmaFiberEquiv g
  have hsigma : Summable (F ∘ e) := e.summable_iff.mpr hF_sum
  have htotal : (∑' k : ℕ, ∑' q : ℕ, F (k, q)) = ∑' n : ℕ, ((a : ℂ) * z) ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
    rw [← hF_sum.tsum_prod' (fun k => hF_sum.prod_factor k), ← e.tsum_eq F]
    change (∑' x, (F ∘ e) x) = _
    rw [hsigma.tsum_sigma' (fun n => hsigma.comp_injective ( Sigma.mk_injective ))]
    refine tsum_congr fun n => ?_
    set m := n + 1
    have hm1 : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le n)
    -- The fiber `{p : ℕ × ℕ // g p = n}` bijects onto `m.divisors`.
    have hfin_set : {p : ℕ × ℕ | g p = n}.Finite := by
      refine ((Set.finite_Iic m).prod (Set.finite_Iic m)).subset ?_
      rintro ⟨k, q⟩ hkq
      simp only [Set.mem_setOf_eq, g] at hkq
      have hprod : (k + 1) * (q + 1) = m := by omega
      have hk_le : k + 1 ≤ m := hprod ▸ Nat.le_mul_of_pos_right (k + 1) (by omega)
      have hq_le : q + 1 ≤ m := hprod ▸ Nat.le_mul_of_pos_left (q + 1) (by omega)
      exact ⟨by simp; omega, by simp; omega⟩
    letI : Fintype {p : ℕ × ℕ // g p = n} := hfin_set.fintype
    rw [tsum_fintype]
    have hfib_sum : (∑ c : {p : ℕ × ℕ // g p = n}, (F ∘ e) ⟨n, c⟩) =
        ∑ d ∈ m.divisors, ((d * necklaceCount a d : ℕ) : ℂ) * (z ^ m / (m : ℂ)) := by
      refine Finset.sum_nbij (fun c => c.1.1 + 1) ?_ ?_ ?_ ?_
      · rintro ⟨⟨k, q⟩, hkq⟩ _
        have hprod : (k + 1) * (q + 1) = m := by dsimp [g] at hkq; omega
        exact Nat.mem_divisors.mpr ⟨⟨q + 1, hprod.symm⟩, by omega⟩
      · rintro ⟨⟨k₁, q₁⟩, h₁⟩ _ ⟨⟨k₂, q₂⟩, h₂⟩ _ heq
        dsimp only at heq
        have hk : k₁ = k₂ := by omega
        subst hk
        have hp₁ : (k₁ + 1) * (q₁ + 1) = m := by dsimp [g] at h₁; omega
        have hp₂ : (k₁ + 1) * (q₂ + 1) = m := by dsimp [g] at h₂; omega
        have hq : q₁ + 1 = q₂ + 1 := mul_left_cancel₀ (by omega) (hp₁.trans hp₂.symm)
        exact Subtype.ext (Prod.ext rfl (by omega))
      · intro d hd
        obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hm1
        have hq1 : 1 ≤ m / d := Nat.div_pos (Nat.le_of_dvd hm1 hdvd) hd1
        have hmul : d * (m / d) = m := Nat.mul_div_cancel' hdvd
        have hg_eq : g (d - 1, m / d - 1) = n := by
          dsimp [g]
          rw [Nat.sub_add_cancel hd1, Nat.sub_add_cancel hq1, hmul]
          omega
        exact ⟨⟨(d - 1, m / d - 1), hg_eq⟩, Finset.mem_univ _, Nat.sub_add_cancel hd1⟩
      · rintro ⟨⟨k, q⟩, hkq⟩ _
        have hprod : (k + 1) * (q + 1) = m := by dsimp [g] at hkq; omega
        change F (k, q) = (((k + 1) * necklaceCount a (k + 1) : ℕ) : ℂ) * (z ^ m / (m : ℂ))
        simp only [F, ← pow_mul, hprod]
        have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        have hq0 : ((q + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
        have hm_cast : (m : ℂ) = ((k + 1 : ℕ) : ℂ) * ((q + 1 : ℕ) : ℂ) := by
          exact_mod_cast hprod.symm
        rw [hm_cast, Nat.cast_mul]
        field_simp [hk0, hq0]
    rw [hfib_sum, ← Finset.sum_mul, ← Nat.cast_sum, sum_divisors_mul_necklaceCount a hm1,
      Nat.cast_pow, mul_pow, mul_div_assoc]
  have haz_lt : ‖(a : ℂ) * z‖ < 1 := by
    rwa [norm_mul, Complex.norm_natCast]
  have htay_az := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log haz_lt)
  simp only [Finset.sum_range_one, Nat.cast_zero, div_zero, sub_zero] at htay_az
  rw [← tsum_congr hrow, htotal, htay_az.tsum_eq]

private theorem natCast_pow_cpow_neg (M k : ℕ) (hM : 1 ≤ M) (s : ℂ) :
    ((M : ℂ) ^ (-s)) ^ k = ((M ^ k : ℕ) : ℂ) ^ (-s) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hMk0 : (0 : ℝ) < (M ^ k : ℕ) := by exact_mod_cast Nat.pow_pos hM
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hM0.ne'), ← Complex.exp_nat_mul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hMk0.ne')]
  congr 1
  rw [← Complex.ofReal_natCast M, ← Complex.ofReal_log hM0.le,
    ← Complex.ofReal_natCast (M ^ k), Nat.cast_pow, ← Complex.ofReal_log hMk0.le, Real.log_pow]
  push_cast; ring

theorem exp_tsum_necklaceCount_log_cpow_eq {a M : ℕ} (ha : 2 ≤ a) (hM : 2 ≤ M) {s : ℂ}
    (hs : (a : ℝ) * (M : ℝ) ^ (-s.re) < 1) :
    Complex.exp (∑' k : ℕ, (necklaceCount a (k + 1) : ℂ) *
      Complex.log (1 - ((M ^ (k + 1) : ℕ) : ℂ) ^ (-s))) =
      1 - (a : ℂ) * (M : ℂ) ^ (-s) := by
  have hM1 : 1 ≤ M := by omega
  have hnorm : (a : ℝ) * ‖(M : ℂ) ^ (-s)‖ < 1 := by
    rwa [norm_natCast_cpow_neg M (by omega)]
  have htsum := tsum_necklaceCount_mul_neg_log_eq ha hnorm
  have hcongr : (∑' k : ℕ, (necklaceCount a (k + 1) : ℂ) *
      Complex.log (1 - ((M ^ (k + 1) : ℕ) : ℂ) ^ (-s))) =
      -(∑' k : ℕ, (necklaceCount a (k + 1) : ℂ) *
        (-Complex.log (1 - ((M : ℂ) ^ (-s)) ^ (k + 1)))) := by
    rw [← tsum_neg]
    refine tsum_congr fun k => ?_
    rw [natCast_pow_cpow_neg M (k + 1) hM1 s, mul_neg, neg_neg]
  rw [hcongr, htsum, neg_neg]
  have haz : ‖(a : ℂ) * (M : ℂ) ^ (-s)‖ < 1 := by rwa [norm_mul, Complex.norm_natCast]
  have hne : 1 - (a : ℂ) * (M : ℂ) ^ (-s) ≠ 0 := by
    intro h0
    have h1 : (1 : ℂ) = (a : ℂ) * (M : ℂ) ^ (-s) := sub_eq_zero.mp h0
    have hn := congrArg norm h1
    rw [norm_one] at hn
    linarith
  exact Complex.exp_log hne

/-! ## 3. Disjoint short-interval prime subsets via Guth–Maynard -/

private theorem exists_disjoint_subsets_of_sum_card_le {α : Type*} [DecidableEq α]
    {W : Finset α} (f : ℕ → ℕ) :
    ∀ n : ℕ, ∑ j ∈ Finset.range n, f j ≤ W.card →
      ∃ T : ℕ → Finset α,
        (∀ j < n, T j ⊆ W ∧ (T j).card = f j) ∧
        (∀ j₁ < n, ∀ j₂ < n, j₁ ≠ j₂ → Disjoint (T j₁) (T j₂))
  | 0, _ => ⟨fun _ => ∅, fun _ hj => absurd hj (Nat.not_lt_zero _),
      fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | n + 1, hsum => by
    rw [Finset.sum_range_succ] at hsum
    obtain ⟨T, hT_mem, hT_disj⟩ :=
      exists_disjoint_subsets_of_sum_card_le f n (le_trans (Nat.le_add_right _ _) hsum)
    set U := (Finset.range n).biUnion T
    have hUW : U ⊆ W := Finset.biUnion_subset.mpr fun j hj => (hT_mem j (Finset.mem_range.mp hj)).1
    have hU_card : U.card = ∑ j ∈ Finset.range n, f j := by
      rw [Finset.card_biUnion (fun j₁ hj₁ j₂ hj₂ hne =>
        hT_disj j₁ (Finset.mem_range.mp hj₁) j₂ (Finset.mem_range.mp hj₂) hne)]
      exact Finset.sum_congr rfl fun j hj => (hT_mem j (Finset.mem_range.mp hj)).2
    have hrem : f n ≤ (W \ U).card := by
      rw [Finset.card_sdiff hUW, hU_card]
      omega
    obtain ⟨A, hAW, hA_card⟩ := Finset.exists_subset_card_eq hrem
    refine ⟨fun j => if j = n then A else T j, ?_, ?_⟩
    · intro j hj
      by_cases hjn : j = n
      · subst hjn
        simp only [↓reduceIte]
        exact ⟨hAW.trans sdiff_subset, hA_card⟩
      · simp only [if_neg hjn]
        exact hT_mem j (by omega)
    · intro j₁ hj₁ j₂ hj₂ hne
      have hd_left : ∀ j < n, Disjoint A (T j) := fun j hj =>
        Disjoint.mono hAW (Finset.subset_biUnion_of_mem T (Finset.mem_range.mpr hj))
          sdiff_disjoint
      by_cases h₁ : j₁ = n
      · subst h₁
        have h₂ : j₂ < n := by omega
        simp only [↓reduceIte, if_neg hne.symm]
        exact hd_left j₂ h₂
      · by_cases h₂ : j₂ = n
        · subst h₂
          simp only [if_neg h₁, ↓reduceIte]
          exact (hd_left j₁ (by omega)).symm
        · simp only [if_neg h₁, if_neg h₂]
          exact hT_disj j₁ (by omega) j₂ (by omega) hne

private theorem windowPrimes_disjoint_of_sixteen_le {M : ℕ} (hM : 16 ≤ M)
    {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) (hne : k₁ ≠ k₂) :
    Disjoint (windowPrimes ((M : ℝ) ^ k₁) ((M : ℝ) ^ k₁ + ((M : ℝ) ^ k₁) ^ (3 / 5 : ℝ)))
      (windowPrimes ((M : ℝ) ^ k₂) ((M : ℝ) ^ k₂ + ((M : ℝ) ^ k₂) ^ (3 / 5 : ℝ))) := by
  wlog hlt : k₁ < k₂ generalizing k₁ k₂
  · exact (this hk₂ hk₁ hne.symm (by omega)).symm
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  obtain ⟨hI₁, _⟩ := mem_windowPrimes.mp hp₁
  obtain ⟨hI₂, _⟩ := mem_windowPrimes.mp hp₂
  have hy₁ : (16 : ℝ) ≤ (M : ℝ) ^ k₁ := by
    calc (16 : ℝ) = (16 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (M : ℝ) ^ 1 := by gcongr; exact_mod_cast hM
      _ ≤ (M : ℝ) ^ k₁ := pow_le_pow_right₀ (by norm_num) hk₁
  have hL₁ : ((M : ℝ) ^ k₁) ^ (3 / 5 : ℝ) ≤ (M : ℝ) ^ k₁ := by
    calc ((M : ℝ) ^ k₁) ^ (3 / 5 : ℝ) ≤ ((M : ℝ) ^ k₁) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (M : ℝ) ^ k₁ := Real.rpow_one _
  have hp_le : (p : ℝ) ≤ 2 * (M : ℝ) ^ k₁ := by
    have hfl := (Finset.mem_Ioc.mp hI₁).2
    have h1 : (p : ℝ) ≤ (M : ℝ) ^ k₁ + ((M : ℝ) ^ k₁) ^ (3 / 5 : ℝ) :=
      (Nat.le_floor_iff (by positivity)).mp hfl
    linarith
  have hp_gt : (M : ℝ) ^ k₂ < (p : ℝ) := by
    have hfl := (Finset.mem_Ioc.mp hI₂).1
    have hnat : ((M : ℝ) ^ k₂) = ((M ^ k₂ : ℕ) : ℝ) := (Nat.cast_pow M k₂).symm
    rw [hnat, Nat.floor_natCast] at hfl
    exact_mod_cast hfl
  have hy₂ : (M : ℝ) * (M : ℝ) ^ k₁ ≤ (M : ℝ) ^ k₂ := by
    calc (M : ℝ) * (M : ℝ) ^ k₁ = (M : ℝ) ^ (k₁ + 1) := by ring
      _ ≤ (M : ℝ) ^ k₂ := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ M)) hlt
  have hM16 : (16 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith

private theorem card_windowPrimes_lower {X₀ : ℝ}
    (hθ : ∀ y L : ℝ, X₀ ≤ y → 0 ≤ L →
      (L - (y + L) ^ (29 / 50 : ℝ)) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y)
    {y : ℝ} (hyX : X₀ ≤ y) (hy16 : 16 ≤ y) (hy50 : 4 ≤ y ^ (1 / 50 : ℝ)) :
    y ^ (29 / 50 : ℝ) / 400 ≤ (windowPrimes y (y + y ^ (3 / 5 : ℝ))).card := by
  set L := y ^ (3 / 5 : ℝ)
  have hy0 : 0 < y := by linarith
  have hL_le : L ≤ y := by
    calc L ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = y := Real.rpow_one y
  have h2_pow : (y + L) ^ (29 / 50 : ℝ) ≤ 2 * y ^ (29 / 50 : ℝ) := by
    calc (y + L) ^ (29 / 50 : ℝ)
        ≤ (2 * y) ^ (29 / 50 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (2 : ℝ) ^ (29 / 50 : ℝ) * y ^ (29 / 50 : ℝ) :=
          Real.mul_rpow (by norm_num) hy0.le _
      _ ≤ (2 : ℝ) ^ (1 : ℝ) * y ^ (29 / 50 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)) (by positivity)
      _ = 2 * y ^ (29 / 50 : ℝ) := by rw [Real.rpow_one]
  have hL_split : L = y ^ (29 / 50 : ℝ) * y ^ (1 / 50 : ℝ) := by
    rw [← Real.rpow_add hy0]
    norm_num
  have htheta_lo : L / 4 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y := by
    have h1 := hθ y L hyX (by positivity)
    have h4 : 4 * y ^ (29 / 50 : ℝ) ≤ L := by
      rw [hL_split]
      nlinarith [Real.rpow_pos_of_pos hy0 (29 / 50 : ℝ)]
    linarith
  rw [theta_sub_eq_sum_Ioc (by linarith : y ≤ y + L)] at htheta_lo
  have hlog_ub : ∀ p ∈ windowPrimes y (y + L), Real.log p ≤ 100 * y ^ (1 / 50 : ℝ) := by
    intro p hp
    obtain ⟨hIp, hpP⟩ := mem_windowPrimes.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    have hp_le : (p : ℝ) ≤ y ^ (2 : ℝ) := by
      have h1 : (p : ℝ) ≤ y + L := (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp hIp).2
      rw [Real.rpow_two]
      nlinarith
    have hlog100 : Real.log (p : ℝ) ≤ 100 * (p : ℝ) ^ (1 / 100 : ℝ) := by
      have hsub := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hp0 (1 / 100 : ℝ))
      rw [Real.log_rpow hp0] at hsub
      linarith
    have hrpow : (p : ℝ) ^ (1 / 100 : ℝ) ≤ y ^ (1 / 50 : ℝ) := by
      calc (p : ℝ) ^ (1 / 100 : ℝ)
          ≤ (y ^ (2 : ℝ)) ^ (1 / 100 : ℝ) :=
            Real.rpow_le_rpow hp0.le hp_le (by norm_num)
        _ = y ^ (1 / 50 : ℝ) := by rw [← Real.rpow_mul hy0.le]; norm_num
    linarith
  have hsum_ub : (∑ p ∈ Finset.Ioc ⌊y⌋₊ ⌊y + L⌋₊ with Nat.Prime p, Real.log p) ≤
      (windowPrimes y (y + L)).card * (100 * y ^ (1 / 50 : ℝ)) := by
    change (∑ p ∈ windowPrimes y (y + L), Real.log p) ≤ _
    calc (∑ p ∈ windowPrimes y (y + L), Real.log p)
        ≤ ∑ _p ∈ windowPrimes y (y + L), (100 * y ^ (1 / 50 : ℝ)) := Finset.sum_le_sum hlog_ub
      _ = (windowPrimes y (y + L)).card * (100 * y ^ (1 / 50 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcomb : y ^ (29 / 50 : ℝ) * y ^ (1 / 50 : ℝ) / 4 ≤
      (windowPrimes y (y + L)).card * (100 * y ^ (1 / 50 : ℝ)) := by
    rw [← hL_split]
    exact htheta_lo.trans hsum_ub
  have hy50_pos : 0 < y ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos hy0 _
  nlinarith

/-- Unconditional selection of pairwise disjoint finite sets of primes `S_seq (k + 1)` matching
`necklaceCount a (k + 1)` and concentrated in `(M^k, M^k + M^{3k/5}]` for `k ≥ k₀`. -/
theorem exists_shortInterval_necklace_primes {a M : ℕ} {β₀ : ℝ}
    (ha : 2 ≤ a) (hM : 16 ≤ M) (hMβ : (M : ℝ) ^ β₀ = (a : ℝ)) (hβ₀ : β₀ < 29 / 50) :
    ∃ (k₀ : ℕ) (S_seq : ℕ → Finset ℕ),
      1 ≤ k₀ ∧
      S_seq 0 = ∅ ∧
      (∀ k : ℕ, 1 ≤ k → (S_seq k).card = necklaceCount a k) ∧
      (∀ k : ℕ, ∀ p ∈ S_seq k, p.Prime ∧ 16 < p) ∧
      (∀ k₁ k₂ : ℕ, k₁ ≠ k₂ → Disjoint (S_seq k₁) (S_seq k₂)) ∧
      (∀ k : ℕ, k₀ ≤ k → ∀ p ∈ S_seq k,
        M ^ k < p ∧ (p : ℝ) ≤ (M : ℝ) ^ k + ((M : ℝ) ^ k) ^ (3 / 5 : ℝ)) := by
  obtain ⟨X₀, hX₀1, hθ⟩ :=
    RHTower.exists_theta_window_lower_seventeenThirtieths (α := 29 / 50) (by norm_num) (by norm_num)
  set η : ℝ := 29 / 50 - β₀
  have hη : 0 < η := by dsimp [η]; linarith
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hM1
  -- Threshold `k₁` where `(M^k)^η ≥ 800`, `M^k ≥ X₀`, and `(M^k)^{1/50} ≥ 4`.
  set B₁ : ℝ := max (Real.log (max X₀ 16) / Real.log (M : ℝ))
    (max (50 * Real.log 4 / Real.log (M : ℝ)) (Real.log 800 / (η * Real.log (M : ℝ))))
  set k₁ : ℕ := ⌊max B₁ 1⌋₊ + 1
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₁_gt : B₁ < (k₁ : ℝ) :=
    lt_of_le_of_lt (le_max_left B₁ 1) (Nat.lt_floor_add_one _)
  have hy_props : ∀ k : ℕ, k₁ ≤ k →
      X₀ ≤ (M : ℝ) ^ k ∧ 16 ≤ (M : ℝ) ^ k ∧
      4 ≤ ((M : ℝ) ^ k) ^ (1 / 50 : ℝ) ∧ 800 ≤ ((M : ℝ) ^ k) ^ η := by
    intro k hk
    have hkR : B₁ < (k : ℝ) := lt_of_lt_of_le hk₁_gt (by exact_mod_cast hk)
    have hlog_yk : Real.log ((M : ℝ) ^ k) = (k : ℝ) * Real.log (M : ℝ) := Real.log_pow _ _
    have h1 : Real.log (max X₀ 16) ≤ Real.log ((M : ℝ) ^ k) := by
      have hb : Real.log (max X₀ 16) / Real.log (M : ℝ) < (k : ℝ) :=
        lt_of_le_of_lt (le_max_left _ _) hkR
      rw [hlog_yk]
      exact ((div_lt_iff₀ hlogM).mp hb).le
    have hmax_le : max X₀ 16 ≤ (M : ℝ) ^ k := by
      rw [← Real.exp_log (by positivity : 0 < max X₀ 16),
        ← Real.exp_log (by positivity : 0 < (M : ℝ) ^ k)]
      exact Real.exp_le_exp.mpr h1
    have h2 : 50 * Real.log 4 ≤ Real.log ((M : ℝ) ^ k) := by
      have hb : 50 * Real.log 4 / Real.log (M : ℝ) < (k : ℝ) :=
        lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hkR
      rw [hlog_yk]
      exact ((div_lt_iff₀ hlogM).mp hb).le
    have h50 : 4 ≤ ((M : ℝ) ^ k) ^ (1 / 50 : ℝ) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4),
        Real.rpow_def_of_pos (by positivity : 0 < (M : ℝ) ^ k)]
      exact Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.log 800 ≤ η * Real.log ((M : ℝ) ^ k) := by
      have hb : Real.log 800 / (η * Real.log (M : ℝ)) < (k : ℝ) :=
        lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hkR
      rw [hlog_yk]
      have hmul := (div_lt_iff₀ (mul_pos hη hlogM)).mp hb
      linarith
    have h800 : 800 ≤ ((M : ℝ) ^ k) ^ η := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 800),
        Real.rpow_def_of_pos (by positivity : 0 < (M : ℝ) ^ k)]
      exact Real.exp_le_exp.mpr (by linarith)
    exact ⟨(le_max_left _ _).trans hmax_le, (le_max_right _ _).trans hmax_le, h50, h800⟩
  -- Geometric bound `∑_{1 ≤ j ≤ k₁} u(a, j) ≤ 2 a^{k₁} ≤ W_{k₁}.card`.
  have hpow_sum : ∀ k : ℕ,
      ∑ j ∈ Finset.range (k + 1), (if j = 0 then 0 else a ^ j) ≤ 2 * a ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, if_neg (Nat.succ_ne_zero k), pow_succ]
      have ha_mul : 2 * a ^ k ≤ a ^ k * a := by nlinarith [Nat.one_le_pow k a (by omega)]
      omega
  have hcard_lo : ∀ k : ℕ, k₁ ≤ k →
      2 * a ^ k ≤
        (windowPrimes ((M : ℝ) ^ k) ((M : ℝ) ^ k + ((M : ℝ) ^ k) ^ (3 / 5 : ℝ))).card := by
    intro k hk
    obtain ⟨hyX, hy16, hy50, hy800⟩ := hy_props k hk
    have hlo := card_windowPrimes_lower hθ hyX hy16 hy50
    have hy0 : 0 < (M : ℝ) ^ k := by positivity
    have hsplit : ((M : ℝ) ^ k) ^ (29 / 50 : ℝ) = ((M : ℝ) ^ k) ^ η * ((M : ℝ) ^ k) ^ β₀ := by
      rw [← Real.rpow_add hy0]
      congr 1; dsimp [η]; ring
    have hyβ : ((M : ℝ) ^ k) ^ β₀ = ((a ^ k : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast (M : ℝ) k, ← Real.rpow_mul (by positivity), mul_comm,
        Real.rpow_mul (by positivity), hMβ, Real.rpow_natCast, Nat.cast_pow]
    have hreal : (2 * a ^ k : ℝ) ≤
        ((windowPrimes ((M : ℝ) ^ k) ((M : ℝ) ^ k + ((M : ℝ) ^ k) ^ (3 / 5 : ℝ))).card : ℝ) := by
      rw [hsplit, hyβ] at hlo
      have hak0 : (0 : ℝ) ≤ ((a ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast hreal
  set W : ℕ → Finset ℕ := fun k =>
    windowPrimes ((M : ℝ) ^ k) ((M : ℝ) ^ k + ((M : ℝ) ^ k) ^ (3 / 5 : ℝ))
  set f_lo : ℕ → ℕ := fun j => if j = 0 then 0 else necklaceCount a j
  have hf_lo_sum : ∑ j ∈ Finset.range (k₁ + 1), f_lo j ≤ (W k₁).card := by
    refine le_trans ?_ (hcard_lo k₁ le_rfl)
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hpow_sum k₁)
    dsimp [f_lo]
    split_ifs with hj0
    · exact Nat.zero_le _
    · exact necklaceCount_le_pow a j (by omega)
  obtain ⟨T_lo, hT_mem, hT_disj⟩ := exists_disjoint_subsets_of_sum_card_le f_lo (k₁ + 1) hf_lo_sum
  have hhi_card : ∀ k : ℕ, k₁ < k → necklaceCount a k ≤ (W k).card := by
    intro k hk
    exact le_trans (necklaceCount_le_pow a k (by omega))
      (le_trans (by omega : a ^ k ≤ 2 * a ^ k) (hcard_lo k hk.le))
  set S_seq : ℕ → Finset ℕ := fun k =>
    if hk : k ≤ k₁ then T_lo k
    else Classical.choose (Finset.exists_subset_card_eq (hhi_card k (by omega)))
  have hS_sub : ∀ k : ℕ, 1 ≤ k →
      S_seq k ⊆ W (max k k₁) ∧ (S_seq k).card = necklaceCount a k := by
    intro k hk1
    dsimp only [S_seq]
    split_ifs with hk
    · obtain ⟨hsub, hcard⟩ := hT_mem k (by omega)
      rw [max_eq_right hk]
      simp only [f_lo, if_neg (by omega : k ≠ 0)] at hcard
      exact ⟨hsub, hcard⟩
    · have hkgt : k₁ < k := by omega
      have hspec := Classical.choose_spec (Finset.exists_subset_card_eq (hhi_card k hkgt))
      rwa [max_eq_left hkgt.le]
  have hS0 : S_seq 0 = ∅ := by
    dsimp only [S_seq]
    rw [dif_pos (Nat.zero_le k₁)]
    have hc := (hT_mem 0 (by omega)).2
    simp only [f_lo, ↓reduceIte] at hc
    exact Finset.card_eq_zero.mp hc
  refine ⟨k₁, S_seq, hk₁1, hS0, (fun k hk => (hS_sub k hk).2), ?_, ?_, ?_⟩
  · intro k p hp
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [hS0] at hp; exact absurd hp (Finset.notMem_empty p)
    · have hmemW := (hS_sub k (by omega)).1 hp
      obtain ⟨hIoc, hpP⟩ := mem_windowPrimes.mp hmemW
      have hm1 : 1 ≤ max k k₁ := le_trans hk₁1 (le_max_right k k₁)
      have hy16 : (16 : ℝ) ≤ (M : ℝ) ^ (max k k₁) := by
        calc (16 : ℝ) = (16 : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (M : ℝ) ^ 1 := by gcongr; exact_mod_cast hM
          _ ≤ (M : ℝ) ^ (max k k₁) := pow_le_pow_right₀ (by norm_num) hm1
      have hp_gt : (M : ℝ) ^ (max k k₁) < (p : ℝ) := by
        have hfl := (Finset.mem_Ioc.mp hIoc).1
        have hnat : ((M : ℝ) ^ (max k k₁)) = ((M ^ (max k k₁) : ℕ) : ℝ) :=
          (Nat.cast_pow M _).symm
        rw [hnat, Nat.floor_natCast] at hfl
        exact_mod_cast hfl
      have hp16 : (16 : ℝ) < (p : ℝ) := lt_of_le_of_lt hy16 hp_gt
      exact ⟨hpP, by exact_mod_cast hp16⟩
  · intro k₁' k₂' hne
    rcases eq_or_ne k₁' 0 with rfl | h10
    · rw [hS0]; exact Finset.disjoint_empty_left _
    rcases eq_or_ne k₂' 0 with rfl | h20
    · rw [hS0]; exact Finset.disjoint_empty_right _
    by_cases hc₁ : k₁' ≤ k₁ <;> by_cases hc₂ : k₂' ≤ k₁
    · dsimp only [S_seq]
      rw [dif_pos hc₁, dif_pos hc₂]
      exact hT_disj k₁' (by omega) k₂' (by omega) hne
    · have hmax : max k₁' k₁ ≠ max k₂' k₁ := by omega
      exact Disjoint.mono (hS_sub k₁' (by omega)).1 (hS_sub k₂' (by omega)).1
        (windowPrimes_disjoint_of_sixteen_le hM
          (le_trans hk₁1 (le_max_right _ _)) (le_trans hk₁1 (le_max_right _ _)) hmax)
    · have hmax : max k₁' k₁ ≠ max k₂' k₁ := by omega
      exact Disjoint.mono (hS_sub k₁' (by omega)).1 (hS_sub k₂' (by omega)).1
        (windowPrimes_disjoint_of_sixteen_le hM
          (le_trans hk₁1 (le_max_right _ _)) (le_trans hk₁1 (le_max_right _ _)) hmax)
    · have hmax : max k₁' k₁ ≠ max k₂' k₁ := by omega
      exact Disjoint.mono (hS_sub k₁' (by omega)).1 (hS_sub k₂' (by omega)).1
        (windowPrimes_disjoint_of_sixteen_le hM
          (le_trans hk₁1 (le_max_right _ _)) (le_trans hk₁1 (le_max_right _ _)) hmax)
  · intro k hk p hp
    have hmemW : p ∈ W k := by
      have hsub := (hS_sub k (le_trans hk₁1 hk)).1 hp
      rwa [max_eq_left hk] at hsub
    obtain ⟨hIoc, _⟩ := mem_windowPrimes.mp hmemW
    obtain ⟨hgt, hle⟩ := Finset.mem_Ioc.mp hIoc
    have hnat : ((M : ℝ) ^ k) = ((M ^ k : ℕ) : ℝ) := (Nat.cast_pow M k).symm
    rw [hnat, Nat.floor_natCast] at hgt
    exact ⟨hgt, (Nat.le_floor_iff (by positivity)).mp hle⟩

/-! ## 4. Analytic continuation of the perturbed necklace Euler product -/

private theorem one_sub_mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith [Complex.re_le_norm z]))

private theorem norm_natCast_cpow_neg_le_half_of_sixteen_le {n : ℕ} (hn : 16 ≤ n)
    {s : ℂ} (hs : 1 / 4 ≤ s.re) : ‖(n : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_natCast_cpow_neg n (by omega)]
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (-s.re)
      ≤ (16 : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hn16 (by linarith)
    _ ≤ (16 : ℝ) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = ((2 : ℝ) ^ (4 : ℝ)) ^ (-(1 / 4 : ℝ)) := by norm_num
    _ = (2 : ℝ) ^ (-(1 : ℝ)) := by rw [← Real.rpow_mul (by norm_num)]; norm_num
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

private theorem norm_log_one_sub_sub_le {w₁ w₂ : ℂ}
    (hw₁ : ‖w₁‖ ≤ 1 / 2) (hw₂ : ‖w₂‖ ≤ 1 / 2) :
    ‖Complex.log (1 - w₁) - Complex.log (1 - w₂)‖ ≤ 2 * ‖w₁ - w₂‖ := by
  set B : Set ℂ := Metric.closedBall (0 : ℂ) (1 / 2)
  have hderiv : ∀ z ∈ B,
      HasDerivWithinAt (fun z : ℂ => Complex.log (1 - z)) ((-1 : ℂ) / (1 - z)) B z := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 / 2 := by simpa [B, Metric.mem_closedBall] using hz
    have hslit : 1 - z ∈ Complex.slitPlane :=
      one_sub_mem_slitPlane_of_norm_lt_one (lt_of_le_of_lt hzn (by norm_num))
    have hd : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) z := by
      simpa using (hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)
    exact (hd.clog hslit).hasDerivWithinAt
  have hbound : ∀ z ∈ B, ‖(-1 : ℂ) / (1 - z)‖ ≤ 2 := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 / 2 := by simpa [B, Metric.mem_closedBall] using hz
    have hre : 1 / 2 ≤ (1 - z).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith [Complex.re_le_norm z]
    have hnorm_ge : 1 / 2 ≤ ‖1 - z‖ := hre.trans (Complex.re_le_norm (1 - z))
    rw [norm_div, norm_neg, norm_one]
    exact (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hm₁ : w₁ ∈ B := by simpa [B, Metric.mem_closedBall] using hw₁
  have hm₂ : w₂ ∈ B := by simpa [B, Metric.mem_closedBall] using hw₂
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_closedBall (0 : ℂ) (1 / 2)) hm₂ hm₁

private theorem norm_cpow_neg_sub_le {y : ℝ} {p : ℕ} {s : ℂ}
    (hy0 : 0 < y) (hyp : y ≤ (p : ℝ)) (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤ ‖s‖ * y ^ (-s.re - 1) * ((p : ℝ) - y) := by
  set seg : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Set.Icc y (p : ℝ)
  have hconv : Convex ℝ seg := (convex_Icc y (p : ℝ)).linear_image Complex.ofRealCLM.toLinearMap
  have hderiv : ∀ z ∈ seg,
      HasDerivWithinAt (fun z : ℂ => z ^ (-s)) ((-s) * z ^ (-s - 1)) seg z := by
    rintro _ ⟨t, ht, rfl⟩
    have ht0 : 0 < t := lt_of_lt_of_le hy0 ht.1
    have hslit : (t : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using ht0))
    exact (Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.hasDerivWithinAt
  have hbound : ∀ z ∈ seg, ‖(-s) * z ^ (-s - 1)‖ ≤ ‖s‖ * y ^ (-s.re - 1) := by
    rintro _ ⟨t, ht, rfl⟩
    have ht0 : 0 < t := lt_of_lt_of_le hy0 ht.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hy0 ht.1 (by linarith)) (norm_nonneg s)
  have hy_mem : (y : ℂ) ∈ seg := ⟨y, ⟨le_rfl, hyp⟩, rfl⟩
  have hp_mem : ((p : ℝ) : ℂ) ∈ seg := ⟨p, ⟨hyp, le_rfl⟩, rfl⟩
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hconv hy_mem hp_mem
  have hdist : ‖((p : ℝ) : ℂ) - (y : ℂ)‖ = (p : ℝ) - y := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [Complex.ofReal_natCast, hdist] at hmvt
  exact hmvt

/-- Log-ratio perturbation summand comparing `1 − p^{−s}` against `1 − (M^k)^{−s}`. -/
def neckPertTerm (M k p : ℕ) (s : ℂ) : ℂ :=
  Complex.log (1 - (p : ℂ) ^ (-s)) - Complex.log (1 - ((M ^ k : ℕ) : ℂ) ^ (-s))

private theorem differentiableAt_log_one_sub_natCast_cpow {n : ℕ} (hn : 16 ≤ n)
    {s : ℂ} (hs : 1 / 4 < s.re) :
    DifferentiableAt ℂ (fun w : ℂ => Complex.log (1 - (n : ℂ) ^ (-w))) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hcpow : DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ (-w)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hn0)
  have hsub : DifferentiableAt ℂ (fun w : ℂ => 1 - (n : ℂ) ^ (-w)) s :=
    (differentiableAt_const 1).sub hcpow
  have hnorm : ‖(n : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
    norm_natCast_cpow_neg_le_half_of_sixteen_le hn hs.le
  exact hsub.clog (one_sub_mem_slitPlane_of_norm_lt_one (lt_of_le_of_lt hnorm (by norm_num)))

theorem differentiableOn_tsum_neckPertTerm {a M k₀ : ℕ} {β₀ : ℝ} {S_seq : ℕ → Finset ℕ}
    (hM : 16 ≤ M) (hMβ : (M : ℝ) ^ β₀ = (a : ℝ)) (hβ₀ : β₀ < 29 / 50)
    (hcard : ∀ k : ℕ, 1 ≤ k → (S_seq k).card = necklaceCount a k)
    (hprime : ∀ k : ℕ, ∀ p ∈ S_seq k, p.Prime ∧ 16 < p)
    (hwin : ∀ k : ℕ, k₀ ≤ k → ∀ p ∈ S_seq k,
      M ^ k < p ∧ (p : ℝ) ≤ (M : ℝ) ^ k + ((M : ℝ) ^ k) ^ (3 / 5 : ℝ)) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∑' k : ℕ, ∑ p ∈ S_seq (k + 1), neckPertTerm M (k + 1) p s)
      {s : ℂ | 1 / 4 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 / 4 < s₀.re := hs₀
  set r : ℝ := min 1 ((s₀.re - 1 / 4) / 2)
  have hr0 : 0 < r := lt_min zero_lt_one (by linarith)
  set σ₁ : ℝ := 1 / 4 + r
  have hσ₁_gt : 1 / 4 < σ₁ := by dsimp [σ₁]; linarith
  set B : Set ℂ := Metric.ball s₀ r
  have hB_open : IsOpen B := Metric.isOpen_ball
  have hB_re : ∀ w ∈ B, σ₁ < w.re ∧ ‖w‖ ≤ ‖s₀‖ + 1 := by
    intro w hw
    have hdist : ‖w - s₀‖ < r := by simpa [B, Metric.mem_ball, dist_eq_norm] using hw
    have hre : |w.re - s₀.re| < r :=
      lt_of_le_of_lt (by simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - s₀)) hdist
    have h1 : r ≤ (s₀.re - 1 / 4) / 2 := min_le_right _ _
    have h2 : r ≤ 1 := min_le_left _ _
    have hw_norm : ‖w‖ ≤ ‖s₀‖ + 1 := by
      calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
        _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
        _ ≤ ‖s₀‖ + 1 := by linarith
    exact ⟨by dsimp [σ₁]; linarith [(abs_lt.mp hre).1], hw_norm⟩
  -- Summable majorant on `B`.
  set q : ℝ := (M : ℝ) ^ (β₀ - σ₁ - 2 / 5)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < M)) ?_
    linarith
  set maj : ℕ → ℝ := fun k =>
    if k + 1 < k₀ then 3 * (necklaceCount a (k + 1) : ℝ)
    else 2 * (‖s₀‖ + 1) * q ^ (k + 1)
  have hmaj_sum : Summable maj := by
    rw [← summable_nat_add_iff k₀]
    have hgeom : Summable (fun j : ℕ => 2 * (‖s₀‖ + 1) * q ^ (j + k₀ + 1)) := by
      have hg := (summable_nat_add_iff (k₀ + 1)).mpr (summable_geometric_of_lt_one hq0 hq1)
      simpa [add_assoc] using hg.mul_left (2 * (‖s₀‖ + 1))
    refine hgeom.congr fun j => ?_
    dsimp [maj]
    rw [if_neg (by omega)]
  have hterm_bound : ∀ (k : ℕ) (w : ℂ), w ∈ B →
      ‖∑ p ∈ S_seq (k + 1), neckPertTerm M (k + 1) p w‖ ≤ maj k := by
    intro k w hw
    obtain ⟨hw_re, hw_norm⟩ := hB_re w hw
    have hMk16 : 16 ≤ M ^ (k + 1) := by
      calc 16 = 16 ^ 1 := (pow_one 16).symm
        _ ≤ M ^ 1 := Nat.pow_le_pow_left hM 1
        _ ≤ M ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hnorm_M : ‖((M ^ (k + 1) : ℕ) : ℂ) ^ (-w)‖ ≤ 1 / 2 :=
      norm_natCast_cpow_neg_le_half_of_sixteen_le hMk16 (by linarith)
    dsimp [maj]
    split_ifs with hk₀
    · calc ‖∑ p ∈ S_seq (k + 1), neckPertTerm M (k + 1) p w‖
          ≤ ∑ p ∈ S_seq (k + 1), ‖neckPertTerm M (k + 1) p w‖ := norm_sum_le _ _
        _ ≤ ∑ _p ∈ S_seq (k + 1), (3 : ℝ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp16 : 16 ≤ p := (hprime (k + 1) p hp).2.le
            have hnorm_p : ‖(p : ℂ) ^ (-w)‖ ≤ 1 / 2 :=
              norm_natCast_cpow_neg_le_half_of_sixteen_le hp16 (by linarith)
            calc ‖neckPertTerm M (k + 1) p w‖
                ≤ ‖Complex.log (1 - (p : ℂ) ^ (-w))‖ +
                    ‖Complex.log (1 - ((M ^ (k + 1) : ℕ) : ℂ) ^ (-w))‖ := norm_sub_le _ _
              _ ≤ 3 / 2 * ‖(p : ℂ) ^ (-w)‖ +
                    3 / 2 * ‖((M ^ (k + 1) : ℕ) : ℂ) ^ (-w)‖ :=
                  add_le_add (norm_log_one_sub_le hnorm_p) (norm_log_one_sub_le hnorm_M)
              _ ≤ 3 := by linarith
        _ = 3 * (necklaceCount a (k + 1) : ℝ) := by
            rw [Finset.sum_const, hcard (k + 1) (by omega), nsmul_eq_mul, mul_comm]
    · have hkge : k₀ ≤ k + 1 := by omega
      set y : ℝ := (M : ℝ) ^ (k + 1)
      have hy0 : 0 < y := by positivity
      have hy_cast : (((M ^ (k + 1) : ℕ) : ℂ)) = (y : ℂ) := by simp [y]
      have hsingle : ∀ p ∈ S_seq (k + 1),
          ‖neckPertTerm M (k + 1) p w‖ ≤ 2 * (‖s₀‖ + 1) * y ^ (-σ₁ - 2 / 5) := by
        intro p hp
        obtain ⟨hgt, hle⟩ := hwin (k + 1) hkge p hp
        have hp16 : 16 ≤ p := (hprime (k + 1) p hp).2.le
        have hnorm_p : ‖(p : ℂ) ^ (-w)‖ ≤ 1 / 2 :=
          norm_natCast_cpow_neg_le_half_of_sixteen_le hp16 (by linarith)
        have hyp : y ≤ (p : ℝ) := by
          have : ((M ^ (k + 1) : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hgt.le
          simpa [y] using this
        have hdiff_p : (p : ℝ) - y ≤ y ^ (3 / 5 : ℝ) := by linarith
        have h1 := norm_log_one_sub_sub_le hnorm_p hnorm_M
        have h2 := norm_cpow_neg_sub_le hy0 hyp (by linarith : 0 < w.re)
        rw [← hy_cast] at h2
        have hy1 : 1 ≤ y := by
          have : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
          exact one_le_pow₀ this
        have hexp_le : y ^ (-w.re - 1) * ((p : ℝ) - y) ≤ y ^ (-σ₁ - 2 / 5) := by
          calc y ^ (-w.re - 1) * ((p : ℝ) - y)
              ≤ y ^ (-σ₁ - 1) * y ^ (3 / 5 : ℝ) :=
                mul_le_mul (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith))
                  hdiff_p (by linarith) (by positivity)
            _ = y ^ (-σ₁ - 2 / 5) := by
                rw [← Real.rpow_add hy0]
                congr 1; ring
        calc ‖neckPertTerm M (k + 1) p w‖
            ≤ 2 * ‖(p : ℂ) ^ (-w) - ((M ^ (k + 1) : ℕ) : ℂ) ^ (-w)‖ := h1
          _ ≤ 2 * (‖w‖ * (y ^ (-w.re - 1) * ((p : ℝ) - y))) := by
              nlinarith
          _ ≤ 2 * ((‖s₀‖ + 1) * y ^ (-σ₁ - 2 / 5)) := by
              gcongr
          _ = 2 * (‖s₀‖ + 1) * y ^ (-σ₁ - 2 / 5) := by ring
      have hcard_le : ((S_seq (k + 1)).card : ℝ) ≤ y ^ β₀ := by
        rw [hcard (k + 1) (by omega)]
        have hnc : (necklaceCount a (k + 1) : ℝ) ≤ ((a ^ (k + 1) : ℕ) : ℝ) := by
          exact_mod_cast necklaceCount_le_pow a (k + 1) (by omega)
        have hyβ : y ^ β₀ = ((a ^ (k + 1) : ℕ) : ℝ) := by
          dsimp [y]
          rw [← Real.rpow_natCast (M : ℝ) (k + 1), ← Real.rpow_mul (by positivity),
            mul_comm, Real.rpow_mul (by positivity), hMβ, Real.rpow_natCast, Nat.cast_pow]
        rwa [hyβ]
      have hyq : y ^ β₀ * y ^ (-σ₁ - 2 / 5) = q ^ (k + 1) := by
        rw [← Real.rpow_add hy0]
        dsimp [y, q]
        rw [← Real.rpow_natCast (M : ℝ) (k + 1), ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast q (k + 1),
          ← Real.rpow_mul (by positivity)]
        congr 1; ring
      calc ‖∑ p ∈ S_seq (k + 1), neckPertTerm M (k + 1) p w‖
          ≤ ∑ p ∈ S_seq (k + 1), ‖neckPertTerm M (k + 1) p w‖ := norm_sum_le _ _
        _ ≤ ∑ _p ∈ S_seq (k + 1), (2 * (‖s₀‖ + 1) * y ^ (-σ₁ - 2 / 5)) :=
            Finset.sum_le_sum hsingle
        _ = ((S_seq (k + 1)).card : ℝ) * (2 * (‖s₀‖ + 1) * y ^ (-σ₁ - 2 / 5)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ y ^ β₀ * (2 * (‖s₀‖ + 1) * y ^ (-σ₁ - 2 / 5)) :=
            mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = 2 * (‖s₀‖ + 1) * (y ^ β₀ * y ^ (-σ₁ - 2 / 5)) := by ring
        _ = 2 * (‖s₀‖ + 1) * q ^ (k + 1) := by rw [hyq]
  have hdB : DifferentiableOn ℂ
      (fun w : ℂ => ∑' k : ℕ, ∑ p ∈ S_seq (k + 1), neckPertTerm M (k + 1) p w) B := by
    refine differentiableOn_tsum_of_summable_norm hmaj_sum (fun k w hw => ?_) hB_open hterm_bound
    have hw_re : 1 / 4 < w.re := lt_trans hσ₁_gt (hB_re w hw).1
    have hMk16 : 16 ≤ M ^ (k + 1) := by
      calc 16 = 16 ^ 1 := (pow_one 16).symm
        _ ≤ M ^ 1 := Nat.pow_le_pow_left hM 1
        _ ≤ M ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    refine DifferentiableWithinAt.sum fun p hp => ?_
    exact ((differentiableAt_log_one_sub_natCast_cpow (hprime (k + 1) p hp).2.le hw_re).sub
      (differentiableAt_log_one_sub_natCast_cpow hMk16 hw_re)).differentiableWithinAt
  exact (hdB.differentiableAt (hB_open.mem_nhds (Metric.mem_ball_self hr0))).differentiableWithinAt

/-- Completely multiplicative Euler summand for `sFreeR S`. -/
private def sFreeSummandHom (S : Set ℕ) (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := (sFreeR S n : ℂ) * (n : ℂ) ^ (-s)
  map_zero' := by simp [sFreeR, SFree]
  map_one' := by simp [sFreeR, SFree]
  map_mul' m n := by
    classical
    by_cases hm : m = 0
    · simp [hm, sFreeR, SFree]
    by_cases hn : n = 0
    · simp [hn, sFreeR, SFree]
    have hmul : SFree S (m * n) ↔ SFree S m ∧ SFree S n := by
      simp only [SFree, mul_ne_zero hm hn, hm, hn, ne_eq, not_false_eq_true, true_and,
        Nat.primeFactors_mul hm hn, Finset.mem_union]
      exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
        fun ⟨h1, h2⟩ p hp => hp.elim (h1 p) (h2 p)⟩
    simp only [sFreeR, hmul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    by_cases h1 : SFree S m <;> by_cases h2 : SFree S n <;> simp [h1, h2]

private theorem LSeries_sFreeR_eq_zeta_mul_exp (S : Set ℕ)
    (hS : ∀ p ∈ S, p.Prime) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (sFreeR S n : ℂ)) s =
      riemannZeta s *
        Complex.exp (∑' n : ℕ, S.indicator (fun m : ℕ => Complex.log (1 - (m : ℂ) ^ (-s))) n) := by
  classical
  have hnorm_sum : Summable (fun n : ℕ => ‖sFreeSummandHom S s n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sFreeSummandHom, sFreeR, SFree, Real.zero_rpow (show -s.re ≠ 0 by linarith)]
    · simp only [sFreeSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
        norm_natCast_cpow_neg n hn, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (by positivity) (abs_sFreeR_le S n)
  have hLS : LSeries (fun n => (sFreeR S n : ℂ)) s = ∑' n : ℕ, sFreeSummandHom S s n := by
    unfold LSeries
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sFreeSummandHom, sFreeR, SFree]
    · simp [sFreeSummandHom, LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, Complex.cpow_neg]
  set A : Nat.Primes → ℂ := fun p => -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))
  set B : Nat.Primes → ℂ :=
    fun p => S.indicator (fun m : ℕ => -Complex.log (1 - (m : ℂ) ^ (-s))) (p : ℕ)
  have hAs : Summable A := (summable_neg_log s hs).of_norm
  have hBs : Summable B := by
    refine Summable.of_norm_bounded (summable_neg_log s hs) fun p => ?_
    dsimp [B]
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have h1 : LSeries (fun n => (sFreeR S n : ℂ)) s =
      Complex.exp (∑' p : Nat.Primes, (A p - B p)) := by
    rw [hLS, ← EulerProduct.exp_tsum_primes_log_eq_tsum hnorm_sum]
    congr 1
    refine tsum_congr fun p => ?_
    have hsf_p : SFree S (p : ℕ) ↔ (p : ℕ) ∉ S := by
      simp [SFree, p.2.ne_zero, p.2.primeFactors]
    simp only [sFreeSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, sFreeR, hsf_p, A, B,
      Set.indicator_apply]
    by_cases hpS : (p : ℕ) ∈ S <;> simp [hpS]
  rw [hAs.tsum_sub hBs, Complex.exp_sub, riemannZeta_eulerProduct_exp_log hs, div_eq_mul_inv,
    ← Complex.exp_neg] at h1
  rw [h1]
  congr 2
  rw [← tsum_neg]
  have hsupp : Function.support
      (fun n : ℕ => S.indicator (fun m : ℕ => Complex.log (1 - (m : ℂ) ^ (-s))) n) ⊆
      {n : ℕ | n.Prime} := by
    intro n hn
    by_contra hnp
    have hnS : n ∉ S := fun hm => hnp (hS n hm)
    exact hn (by simp [hnS])
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun p => ?_
  dsimp [B]
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> simp

private theorem tsum_indicator_union_eq_tsum_sum {S_seq : ℕ → Finset ℕ}
    (hprime : ∀ k : ℕ, ∀ p ∈ S_seq k, p.Prime ∧ 16 < p)
    (hdisj : ∀ k₁ k₂ : ℕ, k₁ ≠ k₂ → Disjoint (S_seq k₁) (S_seq k₂))
    {s : ℂ} (hs : 1 < s.re) :
    let S : Set ℕ := {p : ℕ | ∃ k : ℕ, p ∈ S_seq (k + 1)}
    (∑' n : ℕ, S.indicator (fun m : ℕ => Complex.log (1 - (m : ℂ) ^ (-s))) n) =
      ∑' k : ℕ, ∑ p ∈ S_seq (k + 1), Complex.log (1 - (p : ℂ) ^ (-s)) := by
  classical
  intro S
  set g : ℕ → ℂ := fun m => Complex.log (1 - (m : ℂ) ^ (-s))
  have hg_norm_sum : Summable (fun n : ℕ => S.indicator (fun m => ‖g m‖) n) := by
    refine Summable.of_nonneg_of_le (fun n => Set.indicator_nonneg (fun _ _ => norm_nonneg _) n)
      (fun n => ?_)
      ((Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith)).mul_left (3 / 2))
    rw [Set.indicator_apply]
    split_ifs with hnS
    · obtain ⟨k, hpk⟩ := hnS
      obtain ⟨hpP, hp16⟩ := hprime (k + 1) n hpk
      have hnorm : ‖(n : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
        norm_natCast_cpow_neg_le_half_of_sixteen_le hp16.le (by linarith)
      refine (norm_log_one_sub_le hnorm).trans ?_
      rw [norm_natCast_cpow_neg n hpP.pos]
    · rcases eq_or_ne n 0 with rfl | hn0
      · rw [Real.zero_rpow (by linarith), mul_zero]
      · positivity
  set H : ℕ × ℕ → ℂ := fun kp => if kp.2 ∈ S_seq (kp.1 + 1) then g kp.2 else 0
  have hH_norm : Summable (fun kp : ℕ × ℕ => ‖H kp‖) := by
    refine summable_of_sum_le (fun _ => norm_nonneg _) (fun F => ?_)
    set F' := F.filter fun kp : ℕ × ℕ => kp.2 ∈ S_seq (kp.1 + 1)
    have heq : ∑ kp ∈ F, ‖H kp‖ = ∑ kp ∈ F', ‖g kp.2‖ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun kp _ => ?_
      dsimp [H]; split_ifs <;> simp
    have hinj : Set.InjOn Prod.snd (F' : Set (ℕ × ℕ)) := by
      intro kp₁ h₁ kp₂ h₂ hp_eq
      have hm₁ : kp₁.2 ∈ S_seq (kp₁.1 + 1) := (Finset.mem_filter.mp h₁).2
      have hm₂ : kp₂.2 ∈ S_seq (kp₂.1 + 1) := (Finset.mem_filter.mp h₂).2
      dsimp only at hp_eq
      rw [hp_eq] at hm₁
      by_contra hne
      have hk_ne : kp₁.1 + 1 ≠ kp₂.1 + 1 := fun hk => hne (Prod.ext (by omega) hp_eq)
      exact Finset.disjoint_left.mp (hdisj _ _ hk_ne) hm₁ hm₂
    calc ∑ kp ∈ F, ‖H kp‖
        = ∑ kp ∈ F', ‖g kp.2‖ := heq
      _ = ∑ n ∈ F'.image Prod.snd, ‖g n‖ := (Finset.sum_image hinj).symm
      _ = ∑ n ∈ F'.image Prod.snd, S.indicator (fun m => ‖g m‖) n := by
          refine Finset.sum_congr rfl fun n hn => ?_
          obtain ⟨kp, hkp, rfl⟩ := Finset.mem_image.mp hn
          have hnS : kp.2 ∈ S := ⟨kp.1, (Finset.mem_filter.mp hkp).2⟩
          rw [Set.indicator_of_mem hnS]
      _ ≤ ∑' n : ℕ, S.indicator (fun m => ‖g m‖) n :=
          hg_norm_sum.sum_le_tsum _ fun n _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) n
  have hH : Summable H := hH_norm.of_norm
  have hcol : ∀ n : ℕ, (∑' k : ℕ, H (k, n)) = S.indicator g n := by
    intro n
    by_cases hnS : n ∈ S
    · obtain ⟨k₀, hk₀⟩ := hnS
      rw [Set.indicator_of_mem hnS, tsum_eq_single k₀]
      · simp [H, hk₀]
      · intro k hk
        have hnot : n ∉ S_seq (k + 1) :=
          Finset.disjoint_left.mp (hdisj (k₀ + 1) (k + 1) (by omega)) hk₀
        simp [H, hnot]
    · rw [Set.indicator_of_notMem hnS]
      have h0 : ∀ k : ℕ, H (k, n) = 0 := fun k => by
        have hnot : n ∉ S_seq (k + 1) := fun hm => hnS ⟨k, hm⟩
        simp [H, hnot]
      simp [h0]
  have hrow : ∀ k : ℕ, (∑' n : ℕ, H (k, n)) = ∑ p ∈ S_seq (k + 1), g p := by
    intro k
    rw [tsum_eq_sum (s := S_seq (k + 1)) (fun n hn => by simp [H, hn])]
    exact Finset.sum_congr rfl fun p hp => by simp [H, hp]
  rw [← tsum_congr hcol, ← hH.tsum_prod' (fun n => hH.prod_symm.prod_factor n),
    hH.tsum_comm, tsum_congr hrow]

/-! ## 5. Unconditional integer-norm Beurling fakes for every `β > 1/2` -/

private theorem exists_base_params_of_half_lt {β : ℝ} (hβ : 1 / 2 < β) :
    ∃ (a M : ℕ) (β₀ : ℝ),
      2 ≤ a ∧ 16 ≤ M ∧
      (M : ℝ) ^ β₀ = (a : ℝ) ∧
      1 / 2 < β₀ ∧ β₀ < β ∧ β₀ < 29 / 50 := by
  set β₁ : ℝ := min β (29 / 50)
  have hβ₁ : 1 / 2 < β₁ := lt_min hβ (by norm_num)
  set δ : ℝ := 2 * β₁ - 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set b : ℕ := max 4 (⌊1 / δ⌋₊ + 1)
  have hb4 : 4 ≤ b := le_max_left _ _
  have hb_gt : 1 / δ < (b : ℝ) := by
    have h1 : ⌊1 / δ⌋₊ + 1 ≤ b := le_max_right _ _
    exact lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast h1)
  have hlogb_gt_one : 1 < Real.log (b : ℝ) := by
    have hexp4 : Real.exp 1 < (b : ℝ) :=
      lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 4))
        (by exact_mod_cast hb4)
    simpa using Real.log_lt_log (Real.exp_pos 1) hexp4
  set M : ℕ := b ^ 2
  set a : ℕ := b + 1
  have hM16 : 16 ≤ M := by dsimp [M]; nlinarith
  have ha2 : 2 ≤ a := by omega
  have hlogM : Real.log (M : ℝ) = 2 * Real.log (b : ℝ) := by
    dsimp [M]; rw [Nat.cast_pow, Real.log_pow]; ring
  have hlogM_pos : 0 < Real.log (M : ℝ) := by linarith
  set β₀ : ℝ := Real.log (a : ℝ) / Real.log (M : ℝ)
  have hMβ : (M : ℝ) ^ β₀ = (a : ℝ) := by
    rw [Real.rpow_def_of_pos (by positivity), mul_div_cancel₀ _ hlogM_pos.ne',
      Real.exp_log (by positivity)]
  have hβ₀_gt : 1 / 2 < β₀ := by
    dsimp [β₀]
    rw [hlogM, lt_div_iff₀ hlogM_pos]
    have hlt : Real.log (b : ℝ) < Real.log (a : ℝ) :=
      Real.log_lt_log (by positivity) (by dsimp [a]; push_cast; linarith)
    linarith
  have hβ₀_lt : β₀ < β₁ := by
    dsimp [β₀]
    rw [hlogM, div_lt_iff₀ hlogM_pos]
    have hb0 : (0 : ℝ) < b := by positivity
    have hdiff : Real.log (a : ℝ) - Real.log (b : ℝ) ≤ 1 / (b : ℝ) := by
      rw [← Real.log_div (by positivity) hb0.ne']
      have heq : (a : ℝ) / (b : ℝ) = 1 + 1 / (b : ℝ) := by
        dsimp [a]; push_cast; field_simp
      rw [heq]
      linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (b : ℝ))]
    have h1b : 1 / (b : ℝ) < δ := (div_lt_iff₀ hb0).mpr ((div_lt_iff₀ hδ).mp hb_gt)
    have hδlog : δ < δ * Real.log (b : ℝ) := lt_mul_of_one_lt_right hδ hlogb_gt_one
    have h2β : β₁ * (2 * Real.log (b : ℝ)) = Real.log (b : ℝ) + δ * Real.log (b : ℝ) := by
      dsimp [δ]; ring
    linarith
  exact ⟨a, M, β₀, ha2, hM16, hMβ, hβ₀_gt, lt_of_lt_of_le hβ₀_lt (min_le_left _ _),
    lt_of_lt_of_le hβ₀_lt (min_le_right _ _)⟩

/-- **Unconditional existence of integer-norm Beurling fakes above `1/2` (with both real and
off-real zeros).**  For every `β > 1/2`, there exist a subset `S` of the rational primes and a
holomorphic continuation `G` of `(s − 1) ζ_{ℙ \ S}(s)` to `{Re s > 1/2}` such that
`keptPrimeSystem S` is an integer-norm Beurling fake at remainder exponent `β`, and `G` vanishes
both at a real point `ρ₀ ∈ (1/2, 1)` and at an off-real point `ρ₁` in `{Re s > 1/2}` (`ρ₁.im ≠ 0`)
where `ζ` is nonzero. -/
theorem exists_keptPrimeSystem_fake_above_half {β : ℝ} (hβ : 1 / 2 < β) :
    ∃ (S : Set ℕ) (G : ℂ → ℂ) (ρ₀ ρ₁ : ℂ),
      IsIntegerNormFakeAt (keptPrimeSystem S) β ∧
      DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (keptPrimeSystem S).zetaSeriesC s) ∧
      1 / 2 < ρ₀.re ∧ ρ₀.im = 0 ∧ ρ₀ ≠ 1 ∧ G ρ₀ = 0 ∧ riemannZeta ρ₀ ≠ 0 ∧
      1 / 2 < ρ₁.re ∧ ρ₁.im ≠ 0 ∧ G ρ₁ = 0 ∧ riemannZeta ρ₁ ≠ 0 := by
  set β' : ℝ := min β (3 / 4)
  have hβ' : 1 / 2 < β' := lt_min hβ (by norm_num)
  have hβ'1 : β' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨a, M, β₀, ha2, hM16, hMβ, hβ₀_half, hβ₀_lt, hβ₀_29⟩ :=
    exists_base_params_of_half_lt hβ'
  obtain ⟨k₀, S_seq, hk₀1, _, hcard, hprime, hdisj, hwin⟩ :=
    exists_shortInterval_necklace_primes ha2 hM16 hMβ hβ₀_29
  set S : Set ℕ := {p : ℕ | ∃ k : ℕ, p ∈ S_seq (k + 1)}
  have hS_prime : ∀ p ∈ S, p.Prime := fun _ ⟨k, hp⟩ => (hprime (k + 1) _ hp).1
  -- Nonemptiness of `S` yields `NotNormEquivPrimes (keptPrimeSystem S)`.
  have hcard1 : 1 ≤ (S_seq 1).card := by
    rw [hcard 1 le_rfl]
    exact necklaceCount_pos ha2 le_rfl
  obtain ⟨p₀, hp₀_mem⟩ := Finset.card_pos.mp hcard1
  have hNotP : NotNormEquivPrimes (keptPrimeSystem S) :=
    notNormEquivPrimes_keptPrimeSystem (hprime 1 p₀ hp₀_mem).1 ⟨0, hp₀_mem⟩
  -- Summability of `∑_{p ∈ S} p^{-β'}` gives the Rankin remainder `O(x^{β'})`.
  have hS_sum : Summable (fun p : ℕ => S.indicator (fun n : ℕ => (n : ℝ) ^ (-β')) p) := by
    set qR : ℝ := (M : ℝ) ^ (β₀ - β')
    have hqR0 : 0 ≤ qR := by positivity
    have hqR1 : qR < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < M)) (by linarith)
    set rowMaj : ℕ → ℝ := fun k =>
      if k + 1 < k₀ then (necklaceCount a (k + 1) : ℝ)
      else qR ^ (k + 1)
    have hrowMaj_sum : Summable rowMaj := by
      rw [← summable_nat_add_iff k₀]
      have hg := (summable_nat_add_iff (k₀ + 1)).mpr (summable_geometric_of_lt_one hqR0 hqR1)
      refine (by simpa [add_assoc] using hg : Summable fun j => qR ^ (j + k₀ + 1)).congr fun j => ?_
      dsimp [rowMaj]; rw [if_neg (by omega)]
    have hrow_le : ∀ k : ℕ, (∑ p ∈ S_seq (k + 1), (p : ℝ) ^ (-β')) ≤ rowMaj k := by
      intro k
      dsimp [rowMaj]
      split_ifs with hk₀
      · calc (∑ p ∈ S_seq (k + 1), (p : ℝ) ^ (-β'))
            ≤ ∑ _p ∈ S_seq (k + 1), (1 : ℝ) := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hprime (k + 1) p hp).1.pos
              exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
          _ = (necklaceCount a (k + 1) : ℝ) := by
              rw [Finset.sum_const, hcard (k + 1) (by omega), nsmul_eq_mul, mul_one]
      · have hkge : k₀ ≤ k + 1 := by omega
        set y : ℝ := (M : ℝ) ^ (k + 1)
        have hy0 : 0 < y := by positivity
        calc (∑ p ∈ S_seq (k + 1), (p : ℝ) ^ (-β'))
            ≤ ∑ _p ∈ S_seq (k + 1), y ^ (-β') := by
              refine Finset.sum_le_sum fun p hp => ?_
              have hyp : y ≤ (p : ℝ) := by
                have hgt := (hwin (k + 1) hkge p hp).1
                have : ((M ^ (k + 1) : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hgt.le
                simpa [y] using this
              exact Real.rpow_le_rpow_of_nonpos hy0 hyp (by linarith)
          _ = ((S_seq (k + 1)).card : ℝ) * y ^ (-β') := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ y ^ β₀ * y ^ (-β') := by
              rw [hcard (k + 1) (by omega)]
              have hnc : (necklaceCount a (k + 1) : ℝ) ≤ ((a ^ (k + 1) : ℕ) : ℝ) := by
                exact_mod_cast necklaceCount_le_pow a (k + 1) (by omega)
              have hyβ : y ^ β₀ = ((a ^ (k + 1) : ℕ) : ℝ) := by
                dsimp [y]
                rw [← Real.rpow_natCast (M : ℝ) (k + 1), ← Real.rpow_mul (by positivity),
                  mul_comm, Real.rpow_mul (by positivity), hMβ, Real.rpow_natCast, Nat.cast_pow]
              exact mul_le_mul_of_nonneg_right (hyβ ▸ hnc) (by positivity)
          _ = qR ^ (k + 1) := by
              rw [← Real.rpow_add hy0]
              dsimp [y, qR]
              rw [← Real.rpow_natCast (M : ℝ) (k + 1), ← Real.rpow_mul (by positivity),
                ← Real.rpow_natCast _ (k + 1), ← Real.rpow_mul (by positivity)]
              congr 1; ring
    refine summable_of_sum_le (fun n => Set.indicator_nonneg (fun _ _ => by positivity) n)
      (fun F => ?_)
    classical
    set FS := F.filter (· ∈ S)
    have hFS_eq : ∑ p ∈ F, S.indicator (fun n : ℕ => (n : ℝ) ^ (-β')) p =
        ∑ p ∈ FS, (p : ℝ) ^ (-β') := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Set.indicator_apply]
    set idx : ℕ → ℕ := fun p =>
      if h : p ∈ S then Classical.choose h else 0
    have hidx_mem : ∀ p ∈ FS, p ∈ S_seq (idx p + 1) := by
      intro p hp
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).2
      dsimp [idx]
      rw [dif_pos hpS]
      exact Classical.choose_spec hpS
    set K := FS.image idx
    have hpart : ∑ p ∈ FS, (p : ℝ) ^ (-β') ≤ ∑ k ∈ K, ∑ p ∈ S_seq (k + 1), (p : ℝ) ^ (-β') := by
      have hbi : FS ⊆ K.biUnion (fun k => S_seq (k + 1)) := by
        intro p hp
        exact Finset.mem_biUnion.mpr ⟨idx p, Finset.mem_image_of_mem idx hp, hidx_mem p hp⟩
      calc ∑ p ∈ FS, (p : ℝ) ^ (-β')
          ≤ ∑ p ∈ K.biUnion (fun k => S_seq (k + 1)), (p : ℝ) ^ (-β') :=
            Finset.sum_le_sum_of_subset_of_nonneg hbi (fun _ _ _ => by positivity)
        _ = ∑ k ∈ K, ∑ p ∈ S_seq (k + 1), (p : ℝ) ^ (-β') :=
            Finset.sum_biUnion (fun k₁ _ k₂ _ hne => hdisj _ _ (by omega))
    calc ∑ p ∈ F, S.indicator (fun n : ℕ => (n : ℝ) ^ (-β')) p
        = ∑ p ∈ FS, (p : ℝ) ^ (-β') := hFS_eq
      _ ≤ ∑ k ∈ K, ∑ p ∈ S_seq (k + 1), (p : ℝ) ^ (-β') := hpart
      _ ≤ ∑ k ∈ K, rowMaj k := Finset.sum_le_sum fun k _ => hrow_le k
      _ ≤ ∑' k : ℕ, rowMaj k := hrowMaj_sum.sum_le_tsum K fun k _ => by
          dsimp [rowMaj]; split_ifs <;> positivity
  obtain ⟨A, hA0, hcnt'⟩ :=
    keptPrimeSystem_count_sub_le_of_summable (by linarith : 0 ≤ β') hβ'1 hS_sum
  -- Define the holomorphic continuation `G(s)` on `{Re s > 1/2}` (in fact `{Re s > 1/4}`).
  set G : ℂ → ℂ := fun s =>
    zetaResidueUnit s * (1 - (a : ℂ) * (M : ℂ) ^ (-s)) *
      Complex.exp (∑' k : ℕ, ∑ p ∈ S_seq (k + 1), neckPertTerm M (k + 1) p s)
  have hGd_quarter : DifferentiableOn ℂ G {s : ℂ | 1 / 4 < s.re} := by
    have hd1 : DifferentiableOn ℂ zetaResidueUnit {s : ℂ | 1 / 4 < s.re} :=
      fun s _ => differentiableAt_zetaResidueUnit.differentiableWithinAt
    have hd2 : DifferentiableOn ℂ (fun s : ℂ => 1 - (a : ℂ) * (M : ℂ) ^ (-s))
        {s : ℂ | 1 / 4 < s.re} := by
      have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      exact (differentiableOn_const 1).sub
        ((differentiableOn_const (a : ℂ)).mul
          (differentiableOn_id.neg.const_cpow (Or.inl hM0)))
    have hd3 := differentiableOn_tsum_neckPertTerm hM16 hMβ hβ₀_29 hcard hprime hwin
    exact (hd1.mul hd2).mul hd3.cexp
  have hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} :=
    hGd_quarter.mono fun s (hs : 1 / 2 < s.re) => show 1 / 4 < s.re by linarith
  -- Match `G(s) = (s - 1) * (keptPrimeSystem S).zetaSeriesC s` on `{Re s > 1}`.
  have hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (keptPrimeSystem S).zetaSeriesC s := by
    intro s hs
    rw [zetaSeriesC_keptPrimeSystem S hs, LSeries_sFreeR_eq_zeta_mul_exp S hS_prime hs,
      ← mul_assoc, ← zetaResidueUnit_eq (by intro h1; subst h1; simp at hs : s ≠ 1),
      tsum_indicator_union_eq_tsum_sum hprime hdisj hs]
    have haM_lt : (a : ℝ) * (M : ℝ) ^ (-s.re) < 1 := by
      rw [← hMβ, ← Real.rpow_add (by positivity : 0 < (M : ℝ))]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < M)) (by linarith)
    have hMod := exp_tsum_necklaceCount_log_cpow_eq ha2 (by omega) haM_lt
    -- Both row series converge absolutely on `{Re s > 1}`.
    have hsum_M : Summable (fun k : ℕ =>
        (necklaceCount a (k + 1) : ℂ) *
          Complex.log (1 - ((M ^ (k + 1) : ℕ) : ℂ) ^ (-s))) := by
      refine Summable.of_norm_bounded
        (((summable_nat_add_iff 1).mpr
          (summable_geometric_of_lt_one (by positivity) haM_lt)).mul_left (3 / 2))
        fun k => ?_
      have hMk16 : 16 ≤ M ^ (k + 1) := by
        calc 16 = 16 ^ 1 := (pow_one 16).symm
          _ ≤ M ^ 1 := Nat.pow_le_pow_left hM16 1
          _ ≤ M ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hnorm := norm_natCast_cpow_neg_le_half_of_sixteen_le hMk16 (by linarith)
      rw [norm_mul, Complex.norm_natCast]
      calc (necklaceCount a (k + 1) : ℝ) * ‖Complex.log (1 - ((M ^ (k + 1) : ℕ) : ℂ) ^ (-s))‖
          ≤ (a : ℝ) ^ (k + 1) * (3 / 2 * ‖((M ^ (k + 1) : ℕ) : ℂ) ^ (-s)‖) := by
            refine mul_le_mul ?_ (norm_log_one_sub_le hnorm) (norm_nonneg _) (by positivity)
            exact_mod_cast necklaceCount_le_pow a (k + 1) (by omega)
        _ = 3 / 2 * ((a : ℝ) * (M : ℝ) ^ (-s.re)) ^ (k + 1) := by
            rw [norm_natCast_cpow_neg _ (Nat.pow_pos (by omega)), Nat.cast_pow,
              ← Real.rpow_natCast (M : ℝ) (k + 1), ← Real.rpow_mul (by positivity),
              mul_comm ((k + 1 : ℕ) : ℝ) (-s.re), Real.rpow_mul (by positivity),
              Real.rpow_natCast, mul_pow]
            ring
    have hsum_L : Summable (fun k : ℕ =>
        ∑ p ∈ S_seq (k + 1), Complex.log (1 - (p : ℂ) ^ (-s))) := by
      have hpert : Summable (fun k : ℕ =>
          ∑ p ∈ S_seq (k + 1), neckPertTerm M (k + 1) p s) := by
        set q₁ : ℝ := (M : ℝ) ^ (β₀ - 1 - 2 / 5)
        have hq₁1 : q₁ < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < M)) (by linarith)
        rw [← summable_nat_add_iff k₀]
        refine Summable.of_norm_bounded
          (((summable_nat_add_iff (k₀ + 1)).mpr
            (summable_geometric_of_lt_one (by positivity) hq₁1)).mul_left (2 * (‖s‖ + 1)))
          fun j => ?_
        set k := j + k₀
        have hkge : k₀ ≤ k + 1 := by omega
        set y : ℝ := (M : ℝ) ^ (k + 1)
        have hy0 : 0 < y := by positivity
        have hMk16 : 16 ≤ M ^ (k + 1) := by
          calc 16 = 16 ^ 1 := (pow_one 16).symm
            _ ≤ M ^ 1 := Nat.pow_le_pow_left hM16 1
            _ ≤ M ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hnorm_M := norm_natCast_cpow_neg_le_half_of_sixteen_le hMk16 (by linarith)
        have hy_cast : (((M ^ (k + 1) : ℕ) : ℂ)) = (y : ℂ) := by simp [y]
        have hy1 : 1 ≤ y := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ M))
        calc ‖∑ p ∈ S_seq (k + 1), neckPertTerm M (k + 1) p s‖
            ≤ ∑ p ∈ S_seq (k + 1), ‖neckPertTerm M (k + 1) p s‖ := norm_sum_le _ _
          _ ≤ ∑ _p ∈ S_seq (k + 1), (2 * (‖s‖ + 1) * y ^ (-1 - 2 / 5 : ℝ)) := by
              refine Finset.sum_le_sum fun p hp => ?_
              obtain ⟨hgt, hle⟩ := hwin (k + 1) hkge p hp
              have hp16 : 16 ≤ p := (hprime (k + 1) p hp).2.le
              have hnorm_p := norm_natCast_cpow_neg_le_half_of_sixteen_le hp16 (by linarith)
              have hyp : y ≤ (p : ℝ) := by
                have : ((M ^ (k + 1) : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hgt.le
                simpa [y] using this
              have h1 := norm_log_one_sub_sub_le hnorm_p hnorm_M
              have h2 := norm_cpow_neg_sub_le hy0 hyp (by linarith : 0 < s.re)
              rw [← hy_cast] at h2
              have hexp : y ^ (-s.re - 1) * ((p : ℝ) - y) ≤ y ^ (-1 - 2 / 5 : ℝ) := by
                calc y ^ (-s.re - 1) * ((p : ℝ) - y)
                    ≤ y ^ (-1 - 1 : ℝ) * y ^ (3 / 5 : ℝ) :=
                      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith))
                        (by linarith) (by linarith) (by positivity)
                  _ = y ^ (-1 - 2 / 5 : ℝ) := by rw [← Real.rpow_add hy0]; congr 1; ring
              have hs_le : ‖s‖ ≤ ‖s‖ + 1 := by linarith
              calc ‖neckPertTerm M (k + 1) p s‖
                  ≤ 2 * (‖s‖ * (y ^ (-s.re - 1) * ((p : ℝ) - y))) := by linarith
                _ ≤ 2 * ((‖s‖ + 1) * y ^ (-1 - 2 / 5 : ℝ)) := by gcongr
                _ = 2 * (‖s‖ + 1) * y ^ (-1 - 2 / 5 : ℝ) := by ring
          _ = ((S_seq (k + 1)).card : ℝ) * (2 * (‖s‖ + 1) * y ^ (-1 - 2 / 5 : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ y ^ β₀ * (2 * (‖s‖ + 1) * y ^ (-1 - 2 / 5 : ℝ)) := by
              rw [hcard (k + 1) (by omega)]
              have hnc : (necklaceCount a (k + 1) : ℝ) ≤ ((a ^ (k + 1) : ℕ) : ℝ) := by
                exact_mod_cast necklaceCount_le_pow a (k + 1) (by omega)
              have hyβ : y ^ β₀ = ((a ^ (k + 1) : ℕ) : ℝ) := by
                dsimp [y]
                rw [← Real.rpow_natCast (M : ℝ) (k + 1), ← Real.rpow_mul (by positivity),
                  mul_comm, Real.rpow_mul (by positivity), hMβ, Real.rpow_natCast, Nat.cast_pow]
              exact mul_le_mul_of_nonneg_right (hyβ ▸ hnc) (by positivity)
          _ = 2 * (‖s‖ + 1) * q₁ ^ (j + (k₀ + 1)) := by
              have hexp_eq : y ^ β₀ * y ^ (-1 - 2 / 5 : ℝ) = q₁ ^ (j + (k₀ + 1)) := by
                rw [← Real.rpow_add hy0]
                dsimp [y, q₁, k]
                rw [← Real.rpow_natCast (M : ℝ) (j + k₀ + 1), ← Real.rpow_mul (by positivity),
                  ← Real.rpow_natCast _ (j + (k₀ + 1)), ← Real.rpow_mul (by positivity)]
                congr 1; push_cast; ring
              calc y ^ β₀ * (2 * (‖s‖ + 1) * y ^ (-1 - 2 / 5 : ℝ))
                  = 2 * (‖s‖ + 1) * (y ^ β₀ * y ^ (-1 - 2 / 5 : ℝ)) := by ring
                _ = 2 * (‖s‖ + 1) * q₁ ^ (j + (k₀ + 1)) := by rw [hexp_eq]
      refine (hpert.add hsum_M).congr fun k => ?_
      simp only [neckPertTerm, Finset.sum_sub_distrib, Finset.sum_const,
        hcard (k + 1) (by omega), nsmul_eq_mul, sub_add_cancel]
    have hsplit : (∑' k : ℕ, ∑ p ∈ S_seq (k + 1), neckPertTerm M (k + 1) p s) =
        (∑' k : ℕ, ∑ p ∈ S_seq (k + 1), Complex.log (1 - (p : ℂ) ^ (-s))) -
          (∑' k : ℕ, (necklaceCount a (k + 1) : ℂ) *
            Complex.log (1 - ((M ^ (k + 1) : ℕ) : ℂ) ^ (-s))) := by
      rw [← hsum_L.tsum_sub hsum_M]
      refine tsum_congr fun k => ?_
      simp [neckPertTerm, Finset.sum_sub_distrib, hcard (k + 1) (by omega)]
    dsimp [G]
    rw [hsplit, Complex.exp_sub, hMod]
    have hmod_ne : 1 - (a : ℂ) * (M : ℂ) ^ (-s) ≠ 0 := by
      rw [← hMod]
      exact Complex.exp_ne_zero _
    field_simp [hmod_ne]
  -- Construct both the real fake zero `ρ₀` and the off-real fake zero `ρ₁`.
  set ρ₀ : ℂ := (β₀ : ℂ)
  have hlogM_gt_two : 2 < Real.log (M : ℝ) := by
    have hexp2 : Real.exp 2 < (M : ℝ) := by
      have he1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      calc Real.exp 2 = Real.exp (1 + 1) := by norm_num
        _ = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
        _ < 4 * 4 := mul_lt_mul'' he1 he1 (Real.exp_pos 1).le (Real.exp_pos 1).le
        _ = 16 := by norm_num
        _ ≤ (M : ℝ) := by exact_mod_cast hM16
    simpa using Real.log_lt_log (Real.exp_pos 2) hexp2
  set t₁ : ℝ := 2 * Real.pi / Real.log (M : ℝ)
  have ht₁_pos : 0 < t₁ := div_pos (by positivity) (by linarith)
  have ht₁_lt_four : t₁ < 4 := by
    dsimp [t₁]
    rw [div_lt_iff₀ (by linarith : 0 < Real.log (M : ℝ))]
    linarith [Real.pi_lt_four]
  set ρ₁ : ℂ := (β₀ : ℂ) + (t₁ : ℂ) * Complex.I
  have haM_ρ₀ : (a : ℂ) * (M : ℂ) ^ (-ρ₀) = 1 := by
    dsimp [ρ₀]
    rw [show (-(β₀ : ℂ)) = ((-β₀ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_natCast M, Complex.ofReal_cpow (by positivity),
      Real.rpow_neg (by positivity), hMβ, ← Complex.ofReal_natCast a, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (by positivity), Complex.ofReal_one]
  have haM_ρ₁ : (a : ℂ) * (M : ℂ) ^ (-ρ₁) = 1 := by
    have hM0 : (0 : ℝ) < M := by positivity
    have hcpow : (M : ℂ) ^ (-ρ₁) = (M : ℂ) ^ (-ρ₀) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hM0.ne'),
        Complex.cpow_def_of_ne_zero (by exact_mod_cast hM0.ne'),
        ← Complex.ofReal_natCast M, ← Complex.ofReal_log hM0.le]
      have hexp_per : (-ρ₁) * (Real.log (M : ℝ) : ℂ) =
          (-ρ₀) * (Real.log (M : ℝ) : ℂ) - (2 * Real.pi * Complex.I) := by
        dsimp [ρ₁, ρ₀, t₁]
        have hlog0 : (Real.log (M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : Real.log (M : ℝ) ≠ 0)
        field_simp [hlog0]
        ring
      rw [hexp_per, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
    rw [hcpow, haM_ρ₀]
  have hG_ρ₀ : G ρ₀ = 0 := by dsimp [G]; rw [haM_ρ₀, sub_self, mul_zero, zero_mul]
  have hG_ρ₁ : G ρ₁ = 0 := by dsimp [G]; rw [haM_ρ₁, sub_self, mul_zero, zero_mul]
  have hρ₀_re : 1 / 2 < ρ₀.re := by simpa [ρ₀] using hβ₀_half
  have hρ₀_im : ρ₀.im = 0 := by simp [ρ₀]
  have hρ₀_ne1 : ρ₀ ≠ 1 := by
    intro h1
    have hre := congrArg Complex.re h1
    simp only [ρ₀, Complex.ofReal_re, Complex.one_re] at hre
    linarith
  have hζ_ρ₀ : riemannZeta ρ₀ ≠ 0 :=
    riemannZeta_ne_zero_of_abs_im_lt_four (by simp [ρ₀]) hρ₀_ne1
  have hρ₁_re : 1 / 2 < ρ₁.re := by simpa [ρ₁] using hβ₀_half
  have hρ₁_im_eq : ρ₁.im = t₁ := by simp [ρ₁]
  have hρ₁_ne1 : ρ₁ ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    rw [hρ₁_im_eq, Complex.one_im] at him
    linarith
  have hζ_ρ₁ : riemannZeta ρ₁ ≠ 0 :=
    riemannZeta_ne_zero_of_abs_im_lt_four (by rw [hρ₁_im_eq, abs_of_pos ht₁_pos]; exact ht₁_lt_four)
      hρ₁_ne1
  have hfake' : IsIntegerNormFakeAt (keptPrimeSystem S) β' :=
    ⟨hasIntegerNorms_keptPrimeSystem S, isDiscrete_keptPrimeSystem S, hNotP,
      ⟨A, _, hA0, hcnt'⟩, G, hGd, hGeq, ρ₀, hρ₀_re, hρ₀_ne1, hG_ρ₀, hζ_ρ₀⟩
  exact ⟨S, G, ρ₀, ρ₁, hfake'.mono (min_le_left β (3 / 4)), hGd, hGeq,
    hρ₀_re, hρ₀_im, hρ₀_ne1, hG_ρ₀, hζ_ρ₀,
    hρ₁_re, by rw [hρ₁_im_eq]; exact ht₁_pos.ne', hG_ρ₁, hζ_ρ₁⟩

/-- **Existence of an integer-norm Beurling fake at every remainder exponent `β > 1/2`.** -/
theorem exists_integerNormFakeAt_of_half_lt {β : ℝ} (hβ : 1 / 2 < β) :
    ∃ B : BeurlingSystem, IsIntegerNormFakeAt B β := by
  obtain ⟨S, _, _, _, hf, _⟩ := exists_keptPrimeSystem_fake_above_half hβ
  exact ⟨keptPrimeSystem S, hf⟩

/-- Every exponent strictly above `1/2` belongs to `integerNormFakeExponents`. -/
theorem Ioi_half_subset_integerNormFakeExponents :
    Set.Ioi (1 / 2 : ℝ) ⊆ integerNormFakeExponents :=
  fun _ hβ => exists_integerNormFakeAt_of_half_lt hβ

theorem nonempty_integerNormFakeExponents : integerNormFakeExponents.Nonempty :=
  ⟨3 / 4, exists_integerNormFakeAt_of_half_lt (by norm_num)⟩

/-- **Unconditional critical-threshold localization.**  The infimum of all integer-norm fake
remainder exponents lies in `[0, 1/2]`. -/
theorem csInf_integerNormFakeExponents_mem_Icc :
    sInf integerNormFakeExponents ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  refine ⟨le_csInf nonempty_integerNormFakeExponents fun _ ⟨_, hf⟩ =>
    nonneg_of_integerNormFakeAt hf, ?_⟩
  by_contra hgt
  push Not at hgt
  set mid : ℝ := (1 / 2 + min (sInf integerNormFakeExponents) 1) / 2
  have hmid_gt : 1 / 2 < mid := by
    dsimp [mid]
    have : 1 / 2 < min (sInf integerNormFakeExponents) 1 := lt_min hgt (by norm_num)
    linarith
  have hmid_lt : mid < sInf integerNormFakeExponents := by
    dsimp [mid]
    have h1 : min (sInf integerNormFakeExponents) 1 ≤ sInf integerNormFakeExponents :=
      min_le_left _ _
    have h2 : 1 / 2 < min (sInf integerNormFakeExponents) 1 := lt_min hgt (by norm_num)
    linarith
  exact not_le_of_gt hmid_lt (csInf_le bddBelow_integerNormFakeExponents
    (Ioi_half_subset_integerNormFakeExponents hmid_gt))

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

