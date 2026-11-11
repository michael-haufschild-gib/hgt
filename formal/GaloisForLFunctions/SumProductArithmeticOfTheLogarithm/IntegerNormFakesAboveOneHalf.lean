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
  -- Extra capacity at `k₀ ≥ k₁` to absorb the finite prefix `1 ≤ j < k₀`.
  set U₁ : ℕ := ∑ j ∈ Finset.Ico 1 k₁, necklaceCount a j
  -- Wait: if `k₀ > k₁`, we want `(W_{k₀}).card ≥ ∑_{1 ≤ j ≤ k₀} necklaceCount a j`!
  -- Check: for ANY `k₀ ≥ k₁`, `∑_{k₁ ≤ j ≤ k₀}`? Even simpler: pick `k₀` so `(M^{k₀})^{29/50} / 800 ≥ ∑_{1 ≤ j < k₁}` AND ONLY put `1 ≤ j < k₁` in `W_{k₁}`, while `k₁ ≤ k` ALREADY goes in `W_k`!
  -- YES!! `k₀ := k₁` ALREADY HAS `1 ≤ j < k₁` FIXED (`U₁` DOES NOT DEPEND ON `k₀` if we use a separate threshold `k₀ ≥ k₁` ONLY for `U_prefix`? NO: put `1 ≤ j < k₀` in `W_{k₀}`? Why not put `1 ≤ j < k₁` in `W_{k₀}` and `j ≥ k₁` (except `k₀`) in `W_j`? Even simpler: `∑_{1 ≤ j < k₀} a^j ≤ a^{k₀}`! Since `a^j` is geometric with `a ≥ 2`, `∑_{1 ≤ j ≤ k₀} u(a, j) ≤ ∑_{1 ≤ j ≤ k₀} a^j ≤ 2 * a^{k₀} = 2 * (M^{k₀})^{β₀}`, which `(M^{k₀})^{29/50} / 400 ≥ 2 * (M^{k₀})^{β₀}` ALREADY BEATS AT `k₀ = k₁` WITH ZERO SECOND THRESHOLD!!)!
  have hgeom_sum : ∑ j ∈ Finset.range (k₁ + 1), (if j = 0 then 0 else necklaceCount a j) ≤
      2 * a ^ k₁ := by
    have hle : ∑ j ∈ Finset.range (k₁ + 1), (if j = 0 then 0 else necklaceCount a j) ≤
        ∑ j ∈ Finset.range (k₁ + 1), a ^ j := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hj0
      · exact Nat.zero_le _
      · exact necklaceCount_le_pow a j (by omega)
    have hgeom : (a - 1) * ∑ j ∈ Finset.range (k₁ + 1), a ^ j ≤ a ^ (k₁ + 1) := by
      have h := Nat.geomSum_mul_add a (k₁ + 1)
      -- Wait: prove `(a - 1) * ∑_{j < n} a^j + 1 = a^n` by direct 3-line induction!
      clear * - ha
      induction k₁ + 1 with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, Nat.mul_add, pow_succ]
        have ha1 : 1 + (a - 1) = a := by omega
        nlinarith
    have ha2 : 1 ≤ a - 1 := by omega
    have hsum_pow : ∑ j ∈ Finset.range (k₁ + 1), a ^ j ≤ a * a ^ k₁ := by
      -- Even simpler: prove `∑ j ∈ range (k₁ + 1), (if j = 0 then 0 else a ^ j) ≤ 2 * a ^ k₁` directly by induction on `k₁`!
      clear * - ha
      omega
    omega
  sorry
