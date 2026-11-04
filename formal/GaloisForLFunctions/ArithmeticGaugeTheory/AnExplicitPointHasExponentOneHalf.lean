import GaloisForLFunctions.ArithmeticGaugeTheory.TheExponentIsInvariantOnSparsePrimeSets
import GaloisForLFunctions.ArithmeticGaugeTheory.TheLiouvilleTwinInequality
import GaloisForLFunctions.ArithmeticGaugeTheory.TheArchimedeanLineCarriesTheExponent
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# An explicit gauge point with Möbius exponent one half

Haar-almost every gauge point has Möbius exponent `½` (`ae_gaugeExponent_moebius_eq_half`), the
special points read GRH, and the Liouville twins of Dirichlet points are only known to lie at or
below `½`. This module exhibits one explicit point, outside the special locus, whose exponent is
`½` unconditionally, and whose sums reach the square-root size.

**Construction.** Start from the Liouville twin of `χ₄` (`twinPoint`, exponent `≤ ½`). The block
`P_k` (`halfBlock k`) is the set of the first `2^k` primes of `(4^k, 2·4^k]`. Every squarefree
`n ≤ N_k = 2·4^k` divisible by a prime of `P_k` is that prime, so setting the block to the phase
`u ∈ {±i}` changes the sum at `N_k` by exactly `Σ_{p∈P_k} χ(p) − #P_k u`
(`moebiusGaugeSum_setBlock`). The blocks are set one after another (`halfStage`), the phase of
block `k` chosen against the imaginary part of the charge already present (`blockSign`), and
`halfPoint` is the limit point.

* **Square-root size** (`card_halfBlock_le_norm`, `eventually_two_pow_le_norm_halfPoint`).
  `|S(N_k)| ≥ #P_k`, and `#P_k = 2^k = √(N_k/2)` for all large `k` by the prime number theorem.
* **Sparseness** (`sum_rpow_le_of_subset_halfPrimes`). For `θ > ½` every finite set of block primes
  has `Σ p^{−θ} ≤ (1 − 2·4^{−θ})^{−1}`, so the sparse invariance theorem keeps the exponent `≤ ½`.
* **The exponent** (`gaugeExponent_halfPoint`). `θ_μ(halfPoint) = ½`.
* **Outside the special locus** (`halfPoint_not_special`). At every prime `p ≡ 1 (mod 4)` the point
  takes a value in `{−1, i, −i}`; at primes `p ≡ 1 (mod 4q)` the point `dirichletGauge ψ +
  verticalShift t` takes `p^{it}`. Two such primes force `t = 0` by unique factorization, so the
  value would be `1`. Hence the point agrees with no Dirichlet point on any archimedean line, the
  Tate line `n^{it}` of the trivial point included, at all but finitely many primes.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### The blocks -/

/-- The primes of the octave `(4^k, 2·4^k]`. -/
def octavePrimes (k : ℕ) : Finset ℕ := (Ioc (4 ^ k) (2 * 4 ^ k)).filter Nat.Prime

/-- **The `k`-th block**: the first `2^k` primes of `(4^k, 2·4^k]` (all of them if fewer). -/
def halfBlock (k : ℕ) : Finset ℕ := (((octavePrimes k).sort (· ≤ ·)).take (2 ^ k)).toFinset

theorem halfBlock_subset (k : ℕ) : halfBlock k ⊆ octavePrimes k := by
  intro p hp
  rw [halfBlock, List.mem_toFinset] at hp
  exact (Finset.mem_sort _).mp (List.mem_of_mem_take hp)

theorem mem_halfBlock {k p : ℕ} (hp : p ∈ halfBlock k) :
    p.Prime ∧ 4 ^ k < p ∧ p ≤ 2 * 4 ^ k := by
  have := halfBlock_subset k hp
  simp only [octavePrimes, mem_filter, mem_Ioc] at this
  exact ⟨this.2, this.1.1, this.1.2⟩

theorem card_halfBlock (k : ℕ) : (halfBlock k).card = min (2 ^ k) (octavePrimes k).card := by
  rw [halfBlock, List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).sublist
    (List.take_sublist _ _)), List.length_take, Finset.length_sort]

theorem card_halfBlock_le (k : ℕ) : (halfBlock k).card ≤ 2 ^ k := by
  rw [card_halfBlock]; exact min_le_left _ _

/-- A prime lies in at most one block. -/
theorem eq_of_mem_halfBlock {j k p : ℕ} (hj : p ∈ halfBlock j) (hk : p ∈ halfBlock k) : j = k := by
  obtain ⟨-, hj1, hj2⟩ := mem_halfBlock hj
  obtain ⟨-, hk1, hk2⟩ := mem_halfBlock hk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := Nat.pow_le_pow_right (by norm_num : 0 < 4) h
    rw [pow_succ] at this
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < 4) h
    rw [pow_succ] at this
    omega

/-- The index of a block is below its primes. -/
theorem lt_of_mem_halfBlock {k p : ℕ} (hp : p ∈ halfBlock k) : k < p :=
  (Nat.lt_pow_self (by norm_num : 1 < 4)).trans (mem_halfBlock hp).2.1

/-- A block meeting `[1, 2·4^k]` has index at most `k`. -/
theorem le_of_mem_halfBlock_of_le {j k p : ℕ} (hp : p ∈ halfBlock j) (hpk : p ≤ 2 * 4 ^ k) :
    j ≤ k := by
  by_contra h
  have := Nat.pow_le_pow_right (by norm_num : 0 < 4) (not_le.mp h)
  rw [pow_succ] at this
  have := (mem_halfBlock hp).2.1
  omega

/-- A multiple `n ≤ 2·4^k` of a block prime of index `k` is that prime. -/
theorem eq_of_dvd_of_mem_halfBlock {k p n : ℕ} (hp : p ∈ halfBlock k) (hpn : p ∣ n) (hn : 0 < n)
    (hnk : n ≤ 2 * 4 ^ k) : n = p := by
  obtain ⟨m, rfl⟩ := hpn
  have hp1 := (mem_halfBlock hp).2.1
  rcases m with _ | _ | m
  · omega
  · ring
  · nlinarith

/-! ### Sparseness -/

/-- The set of all block primes. -/
def halfPrimes : Set ℕ := {p | ∃ k, p ∈ halfBlock k}

/-- `4^{−θ} < 1/2` for `θ > 1/2`. -/
theorem four_rpow_neg_lt_half {θ : ℝ} (hθ : 1 / 2 < θ) : (4 : ℝ) ^ (-θ) < 1 / 2 := by
  have h : (4 : ℝ) ^ (-θ) < (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have h4 : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith

/-- One block contributes at most `(2·4^{−θ})^k`. -/
theorem sum_halfBlock_rpow_le {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) :
    ∑ p ∈ halfBlock k, (p : ℝ) ^ (-θ) ≤ (2 * (4 : ℝ) ^ (-θ)) ^ k := by
  have hterm : ∀ p ∈ halfBlock k, (p : ℝ) ^ (-θ) ≤ ((4 : ℝ) ^ (-θ)) ^ k := by
    intro p hp
    have hlt : ((4 ^ k : ℕ) : ℝ) ≤ p := by exact_mod_cast (mem_halfBlock hp).2.1.le
    rw [Real.rpow_pow_comm (by norm_num)]
    push_cast at hlt
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hlt (by linarith)
  calc ∑ p ∈ halfBlock k, (p : ℝ) ^ (-θ) ≤ ∑ _p ∈ halfBlock k, ((4 : ℝ) ^ (-θ)) ^ k :=
        sum_le_sum hterm
    _ = (halfBlock k).card * ((4 : ℝ) ^ (-θ)) ^ k := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ k * ((4 : ℝ) ^ (-θ)) ^ k := by
        gcongr
        exact_mod_cast card_halfBlock_le k
    _ = (2 * (4 : ℝ) ^ (-θ)) ^ k := by rw [mul_pow]

/-- **The block primes are sparse above `½`.** -/
theorem sum_rpow_le_of_subset_halfPrimes {θ : ℝ} (hθ : 1 / 2 < θ) (F : Finset ℕ)
    (hF : (↑F : Set ℕ) ⊆ halfPrimes) :
    ∑ p ∈ F, (p : ℝ) ^ (-θ) ≤ (1 - 2 * (4 : ℝ) ^ (-θ))⁻¹ := by
  classical
  set r : ℝ := 2 * (4 : ℝ) ^ (-θ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by have := four_rpow_neg_lt_half hθ; linarith
  set K : ℕ := F.sup id + 1 with hK
  have hsub : F ⊆ (range K).biUnion halfBlock := by
    intro p hp
    obtain ⟨k, hk⟩ := hF hp
    have hpK : p ≤ F.sup id := le_sup (f := id) hp
    exact mem_biUnion.mpr ⟨k, mem_range.mpr (by have := lt_of_mem_halfBlock hk; omega), hk⟩
  have hdisj : (↑(range K) : Set ℕ).PairwiseDisjoint halfBlock := by
    intro j _ k _ hjk
    exact Finset.disjoint_left.mpr fun p hpj hpk => hjk (eq_of_mem_halfBlock hpj hpk)
  have hgeom : ∑ k ∈ range K, r ^ k ≤ (1 - r)⁻¹ := by
    rw [geom_sum_eq hr1.ne, div_le_iff_of_neg (by linarith : r - 1 < 0)]
    have hm : (1 - r)⁻¹ * (r - 1) = -1 := by
      rw [show r - 1 = -(1 - r) by ring, mul_neg, inv_mul_cancel₀ (by linarith)]
    rw [hm]
    linarith [pow_nonneg hr0 K]
  calc ∑ p ∈ F, (p : ℝ) ^ (-θ) ≤ ∑ p ∈ (range K).biUnion halfBlock, (p : ℝ) ^ (-θ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => Real.rpow_nonneg (Nat.cast_nonneg p) _
    _ = ∑ k ∈ range K, ∑ p ∈ halfBlock k, (p : ℝ) ^ (-θ) := sum_biUnion hdisj
    _ ≤ ∑ k ∈ range K, r ^ k := sum_le_sum fun k _ => sum_halfBlock_rpow_le (by linarith) k
    _ ≤ (1 - r)⁻¹ := hgeom

/-! ### The base point and the phases -/

/-- The Liouville point `χ(p) = −1`. -/
def liouvillePoint : GaugeTorus := fun _ => ((1 / 2 : ℝ) : UnitAddCircle)

theorem twist_liouvillePoint {p : ℕ} (hp : p.Prime) : twist liouvillePoint p = -1 := by
  rw [twist_prime_apply _ hp, liouvillePoint, fourier_coe_apply]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (((1 / 2 : ℝ)) : ℂ) / ((1 : ℝ) : ℂ) =
    Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- **The base point**: the Liouville twin of `χ₄`. -/
def twinPoint : GaugeTorus := dirichletGauge chiFour + liouvillePoint

theorem twist_twinPoint {p : ℕ} (hp : p.Prime) :
    twist twinPoint p = -twist (dirichletGauge chiFour) p := by
  rw [twinPoint, twist_add, twist_liouvillePoint hp]; ring

theorem gaugeExponent_twinPoint_le : gaugeExponent moebiusSource twinPoint ≤ 1 / 2 :=
  gaugeExponent_moebius_liouvilleTwin_dirichletGauge_le_half chiFour_ne_one fun _ hp =>
    twist_twinPoint hp

/-- The quarter phases `±1/4`, with twists `±i`. -/
def quarterPhase (b : Bool) : UnitAddCircle :=
  if b then ((1 / 4 : ℝ) : UnitAddCircle) else ((-(1 / 4) : ℝ) : UnitAddCircle)

/-- The value `i` or `−i` of a quarter phase. -/
def phaseValue (b : Bool) : ℂ := if b then Complex.I else -Complex.I

theorem fourier_quarterPhase (b : Bool) : fourier 1 (quarterPhase b) = phaseValue b := by
  cases b
  · simp only [quarterPhase, phaseValue, Bool.false_eq_true, if_false, fourier_coe_apply]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * ((-(1 / 4) : ℝ) : ℂ) / ((1 : ℝ) : ℂ) =
      -(Real.pi : ℂ) / 2 * Complex.I by push_cast; ring]
    exact Complex.exp_neg_pi_div_two_mul_I
  · simp only [quarterPhase, phaseValue, if_true, fourier_coe_apply]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * ((1 / 4 : ℝ) : ℂ) / ((1 : ℝ) : ℂ) =
      (Real.pi : ℂ) / 2 * Complex.I by push_cast; ring]
    exact Complex.exp_pi_div_two_mul_I

/-! ### Setting one block -/

/-- Set the coordinates of block `k` of `z` to the quarter phase `b`. -/
def setBlock (z : GaugeTorus) (k : ℕ) (b : Bool) : GaugeTorus :=
  fun p => if p ∈ halfBlock k then quarterPhase b else z p

/-- The charge of block `k` at `z`: the sum at `2·4^k` with the block's prime terms removed. -/
def blockCharge (z : GaugeTorus) (k : ℕ) : ℂ :=
  moebiusGaugeSum (2 * 4 ^ k) z + ∑ p ∈ halfBlock k, twist z p

/-- **One block moves the sum at `2·4^k` exactly by its prime terms.**
`S_{z'}(2·4^k) = blockCharge z k − #P_k · u`. -/
theorem moebiusGaugeSum_setBlock (z : GaugeTorus) (k : ℕ) (b : Bool) :
    moebiusGaugeSum (2 * 4 ^ k) (setBlock z k b) =
      blockCharge z k - (halfBlock k).card * phaseValue b := by
  classical
  set N := 2 * 4 ^ k
  have hBsub : halfBlock k ⊆ Icc 1 N := fun p hp => by
    obtain ⟨hpp, -, hpN⟩ := mem_halfBlock hp
    exact mem_Icc.mpr ⟨hpp.one_lt.le, hpN⟩
  -- Off the block the two twists agree.
  have hoff : ∀ n ∈ Icc 1 N \ halfBlock k, twist (setBlock z k b) n = twist z n := by
    intro n hn
    obtain ⟨hnI, hnB⟩ := mem_sdiff.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
    refine twist_eq_of_primes (by omega) fun q hq hqn => ?_
    have hqB : q ∉ halfBlock k := fun hqB =>
      hnB (eq_of_dvd_of_mem_halfBlock hqB hqn (by omega) hnN ▸ hqB)
    rw [twist_prime_apply _ hq, twist_prime_apply _ hq, setBlock, if_neg hqB]
  have hon : ∀ p ∈ halfBlock k, ((μ p : ℤ) : ℂ) * twist (setBlock z k b) p = -phaseValue b := by
    intro p hp
    have hpp := (mem_halfBlock hp).1
    rw [twist_prime_apply _ hpp, setBlock, if_pos hp, fourier_quarterPhase,
      ArithmeticFunction.moebius_apply_prime hpp]
    push_cast; ring
  have hon' : ∀ p ∈ halfBlock k, ((μ p : ℤ) : ℂ) * twist z p = -twist z p := by
    intro p hp
    rw [ArithmeticFunction.moebius_apply_prime (mem_halfBlock hp).1]
    push_cast; ring
  rw [blockCharge, moebiusGaugeSum, moebiusGaugeSum, ← sum_sdiff hBsub, ← sum_sdiff hBsub,
    sum_congr rfl hon, sum_congr rfl hon', sum_congr rfl fun n hn => by rw [hoff n hn]]
  simp only [sum_neg_distrib, sum_const, nsmul_eq_mul]
  ring

/-! ### The stages and the point -/

/-- The sign rule: phase `+i` if the charge has negative imaginary part, else `−i`. -/
def blockSign (z : GaugeTorus) (k : ℕ) : Bool := decide ((blockCharge z k).im < 0)

/-- The stages: blocks `< k` set, the twin of `χ₄` elsewhere. -/
def halfStage : ℕ → GaugeTorus
  | 0 => twinPoint
  | k + 1 => setBlock (halfStage k) k (blockSign (halfStage k) k)

/-- **The explicit point**: the coordinate at `p` is the one of the stage `p + 1`, after which it no
longer changes. -/
def halfPoint : GaugeTorus := fun p => halfStage (p + 1) p

/-- Stages beyond every block containing `p` agree at `p`. -/
theorem halfStage_stable {p m : ℕ} (hm : ∀ k, p ∈ halfBlock k → k < m) :
    ∀ d, halfStage (m + d) p = halfStage m p := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← add_assoc, halfStage, setBlock, if_neg fun hp => by have := hm _ hp; omega, ih]

theorem halfStage_eq_of_ge {p m n : ℕ} (hm : ∀ k, p ∈ halfBlock k → k < m) (hmn : m ≤ n) :
    halfStage n p = halfStage m p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact halfStage_stable hm d

/-- Off the block primes the point is the twin of `χ₄`. -/
theorem halfPoint_eq_twinPoint {p : ℕ} (hp : p ∉ halfPrimes) : halfPoint p = twinPoint p := by
  have hm : ∀ k, p ∈ halfBlock k → k < 0 := fun k hk => absurd ⟨k, hk⟩ hp
  exact halfStage_eq_of_ge hm (Nat.zero_le _)

/-- On a block prime the point carries the block's quarter phase. -/
theorem halfPoint_eq_of_mem {k p : ℕ} (hp : p ∈ halfBlock k) :
    halfPoint p = quarterPhase (blockSign (halfStage k) k) := by
  have hm : ∀ j, p ∈ halfBlock j → j < k + 1 := fun j hj => by
    rw [eq_of_mem_halfBlock hj hp]; omega
  rw [halfPoint, halfStage_eq_of_ge hm (by have := lt_of_mem_halfBlock hp; omega), halfStage,
    setBlock, if_pos hp]

/-- Up to `2·4^k` the point and the stage `k + 1` have the same Möbius sums. -/
theorem moebiusGaugeSum_halfPoint (k : ℕ) :
    moebiusGaugeSum (2 * 4 ^ k) halfPoint = moebiusGaugeSum (2 * 4 ^ k) (halfStage (k + 1)) := by
  refine moebiusGaugeSum_congr_of_le fun q hq hqN => ?_
  rw [twist_prime_apply _ hq, twist_prime_apply _ hq]
  congr 1
  have hm : ∀ j, q ∈ halfBlock j → j < min (q + 1) (k + 1) := fun j hj => by
    have := lt_of_mem_halfBlock hj
    have := le_of_mem_halfBlock_of_le hj hqN
    omega
  rw [halfPoint, halfStage_eq_of_ge hm (min_le_left _ _), halfStage_eq_of_ge hm (min_le_right _ _)]

/-! ### The square-root size -/

/-- **The block forces the square-root size.** `|S(2·4^k)| ≥ #P_k`. -/
theorem card_halfBlock_le_norm (k : ℕ) :
    ((halfBlock k).card : ℝ) ≤ ‖moebiusGaugeSum (2 * 4 ^ k) halfPoint‖ := by
  rw [moebiusGaugeSum_halfPoint, halfStage, moebiusGaugeSum_setBlock]
  set A := blockCharge (halfStage k) k
  have hc : (0 : ℝ) ≤ ((halfBlock k).card : ℝ) := Nat.cast_nonneg _
  refine le_trans ?_ (Complex.abs_im_le_norm _)
  by_cases hA : A.im < 0
  · have hs : blockSign (halfStage k) k = true := decide_eq_true hA
    rw [hs, phaseValue, if_pos rfl]
    have : (A - ((halfBlock k).card : ℂ) * Complex.I).im = A.im - (halfBlock k).card := by simp
    rw [this, abs_of_neg (by linarith)]
    linarith
  · have hs : blockSign (halfStage k) k = false := decide_eq_false hA
    rw [hs, phaseValue, if_neg (by simp)]
    have : (A - ((halfBlock k).card : ℂ) * -Complex.I).im = A.im + (halfBlock k).card := by simp
    rw [this, abs_of_nonneg (by linarith)]
    linarith

/-- `π(2M) ≤ π(M) + #(primes in (M, 2M])`. -/
theorem primeCounting_two_mul_le_add (M : ℕ) :
    Nat.primeCounting (2 * M) ≤ Nat.primeCounting M + ((Ioc M (2 * M)).filter Nat.Prime).card := by
  classical
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  calc ((range (2 * M + 1)).filter Nat.Prime).card ≤
        ((range (M + 1)).filter Nat.Prime ∪ (Ioc M (2 * M)).filter Nat.Prime).card := by
        refine card_le_card fun x hx => ?_
        obtain ⟨hxr, hxp⟩ := mem_filter.mp hx
        have hx2 := mem_range.mp hxr
        by_cases hxM : x ≤ M
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr (by omega), hxp⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hxp⟩)
    _ ≤ _ := card_union_le _ _

/-- `3k ≤ 2^k` for `k ≥ 4`. -/
theorem three_mul_le_two_pow {k : ℕ} (hk : 4 ≤ k) : 3 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    have : 4 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
    omega

/-- **Eventually every block is full.** By the prime number theorem the octave `(4^k, 2·4^k]` holds
at least `2^k` primes for all large `k`. -/
theorem eventually_card_halfBlock : ∀ᶠ k : ℕ in atTop, (halfBlock k).card = 2 ^ k := by
  have hwin := HTGeometry.eventually_primeCount_window_ge (K := 2) (by norm_num)
  have h4 : Tendsto (fun k : ℕ => (4 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [h4.eventually hwin, eventually_ge_atTop 4] with k hk hk4
  rw [card_halfBlock, min_eq_left]
  have hfl1 : ⌊(2 : ℝ) * (4 : ℝ) ^ k⌋₊ = 2 * 4 ^ k := by
    rw [show (2 : ℝ) * (4 : ℝ) ^ k = ((2 * 4 ^ k : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hfl2 : ⌊(4 : ℝ) ^ k⌋₊ = 4 ^ k := by
    rw [show (4 : ℝ) ^ k = ((4 ^ k : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [hfl1, hfl2] at hk
  have hcount := primeCounting_two_mul_le_add (4 ^ k)
  have hcountR : (Nat.primeCounting (2 * 4 ^ k) : ℝ) ≤
      Nat.primeCounting (4 ^ k) + ((octavePrimes k).card : ℝ) := by
    exact_mod_cast hcount
  -- `2^k ≤ 4^k/(2 log 4^k)`, since `2 log 4^k = 2k log 4 < 3k ≤ 2^k`.
  have hlog4 : Real.log 4 < 3 / 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have hlogpos : 0 < Real.log ((4 : ℝ) ^ k) := Real.log_pos (one_lt_pow₀ (by norm_num) (by omega))
  have hlogk : Real.log ((4 : ℝ) ^ k) = k * Real.log 4 := Real.log_pow 4 k
  have h3k : (3 * k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast three_mul_le_two_pow hk4
  have hkey : (2 : ℝ) ^ k ≤ (2 - 1) / 2 * ((4 : ℝ) ^ k / Real.log ((4 : ℝ) ^ k)) := by
    rw [show (2 - 1 : ℝ) / 2 * ((4 : ℝ) ^ k / Real.log ((4 : ℝ) ^ k)) =
      (4 : ℝ) ^ k / (2 * Real.log ((4 : ℝ) ^ k)) by ring, le_div_iff₀ (by positivity)]
    have h44 : (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
      rw [← mul_pow]; norm_num
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hsmall : 2 * ((k : ℝ) * Real.log 4) ≤ (2 : ℝ) ^ k := by nlinarith
    rw [hlogk, h44]
    exact mul_le_mul_of_nonneg_left hsmall h2k.le
  have : ((2 ^ k : ℕ) : ℝ) ≤ ((octavePrimes k).card : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- **The square-root law is attained.** For all large `k`, `|S(N_k)| ≥ 2^k = √(N_k/2)` at
`N_k = 2·4^k`. -/
theorem eventually_two_pow_le_norm_halfPoint :
    ∀ᶠ k : ℕ in atTop, (2 : ℝ) ^ k ≤ ‖moebiusGaugeSum (2 * 4 ^ k) halfPoint‖ := by
  filter_upwards [eventually_card_halfBlock] with k hk
  have := card_halfBlock_le_norm k
  rw [hk] at this
  exact_mod_cast this

/-! ### The exponent -/

/-- No power bound of exponent in `[0, ½)`. -/
theorem not_gaugePowerBound_halfPoint {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) :
    ¬ GaugePowerBound moebiusSource halfPoint θ := by
  rw [gaugePowerBound_moebius_iff]
  rintro ⟨C, hC, hS⟩
  have h4θ : (4 : ℝ) ^ θ < 2 := by
    have h : (4 : ℝ) ^ θ < (4 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hθ
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have h4θpos : 0 < (4 : ℝ) ^ θ := by positivity
  set ρ : ℝ := 2 / (4 : ℝ) ^ θ with hρ
  have hρ1 : 1 < ρ := by rw [hρ, lt_div_iff₀ h4θpos]; linarith
  have hgrow := (tendsto_pow_atTop_atTop_of_one_lt hρ1).eventually_gt_atTop (C * 3 ^ θ)
  obtain ⟨k, hk1, hk2⟩ := (eventually_two_pow_le_norm_halfPoint.and hgrow).exists
  have hN : ((2 * 4 ^ k : ℕ) : ℝ) + 1 ≤ 3 * (4 : ℝ) ^ k := by
    push_cast
    have : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    linarith
  have hpow : (((2 * 4 ^ k : ℕ) : ℝ) + 1) ^ θ ≤ 3 ^ θ * ((4 : ℝ) ^ θ) ^ k := by
    calc (((2 * 4 ^ k : ℕ) : ℝ) + 1) ^ θ ≤ (3 * (4 : ℝ) ^ k) ^ θ :=
          Real.rpow_le_rpow (by positivity) hN hθ0
      _ = 3 ^ θ * ((4 : ℝ) ^ θ) ^ k := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_pow_comm (by norm_num)]
  have hρk : ρ ^ k * ((4 : ℝ) ^ θ) ^ k = (2 : ℝ) ^ k := by
    rw [← mul_pow, hρ, div_mul_cancel₀ _ h4θpos.ne']
  have h4k : 0 < ((4 : ℝ) ^ θ) ^ k := by positivity
  have hchain : (2 : ℝ) ^ k ≤ C * 3 ^ θ * ((4 : ℝ) ^ θ) ^ k := by
    calc (2 : ℝ) ^ k ≤ ‖moebiusGaugeSum (2 * 4 ^ k) halfPoint‖ := hk1
      _ ≤ C * (((2 * 4 ^ k : ℕ) : ℝ) + 1) ^ θ := hS (2 * 4 ^ k)
      _ ≤ C * (3 ^ θ * ((4 : ℝ) ^ θ) ^ k) := mul_le_mul_of_nonneg_left hpow hC
      _ = C * 3 ^ θ * ((4 : ℝ) ^ θ) ^ k := by ring
  rw [← hρk] at hchain
  have := le_of_mul_le_mul_right hchain h4k
  linarith

/-- **The explicit point has Möbius exponent `½`.** -/
theorem gaugeExponent_halfPoint : gaugeExponent moebiusSource halfPoint = 1 / 2 := by
  apply le_antisymm
  · have h := gaugeExponent_moebius_le_of_agree_off_sparse (P := halfPrimes) (θ₀ := 1 / 2)
      (by norm_num) (fun θ hθ => ⟨_, sum_rpow_le_of_subset_halfPrimes hθ⟩)
      (x := twinPoint) (x' := halfPoint) fun q hq hqP => by
        rw [twist_prime_apply _ hq, twist_prime_apply _ hq, halfPoint_eq_twinPoint hqP]
    rwa [max_eq_left gaugeExponent_twinPoint_le] at h
  · by_contra hlt
    obtain ⟨θ, h1, h2⟩ := exists_between (not_le.mp hlt)
    have h0 : 0 ≤ θ := (gaugeExponent_nonneg norm_moebiusSource_le).trans h1.le
    exact not_gaugePowerBound_halfPoint h0 h2
      (gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le h1)

/-! ### Outside the special locus -/

/-- At primes `p ≡ 1 (mod 4)` the point takes a value in `{−1, i, −i}`: a fourth root of unity
other than `1`. -/
theorem twist_halfPoint_of_mod_four {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    twist halfPoint p ^ 4 = 1 ∧ twist halfPoint p ≠ 1 := by
  rw [twist_prime_apply _ hp]
  by_cases hP : p ∈ halfPrimes
  · obtain ⟨k, hk⟩ := hP
    rw [halfPoint_eq_of_mem hk, fourier_quarterPhase]
    cases blockSign (halfStage k) k <;>
      simp [phaseValue, pow_succ, Complex.ext_iff]
  · rw [halfPoint_eq_twinPoint hP, ← twist_prime_apply _ hp, twist_twinPoint hp]
    have hcop : Nat.Coprime p 4 := by
      rw [Nat.coprime_comm, show (4 : ℕ) = 2 ^ 2 by norm_num]
      refine Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_two hp).mpr ?_)
      intro h2; subst h2; norm_num at h4
    rw [twist_dirichletGauge chiFour hp.ne_zero hcop, chiFour, MulChar.ringHomComp_apply,
      ZMod.χ₄_nat_one_mod_four h4]
    norm_num

/-- If `p^{4it} = 1` at two distinct primes, then `t = 0`. -/
theorem eq_zero_of_exp_four_mul_log {t : ℝ} {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hne : p₁ ≠ p₂)
    (h₁ : Complex.exp (((t * Real.log p₁ : ℝ) : ℂ) * Complex.I) ^ 4 = 1)
    (h₂ : Complex.exp (((t * Real.log p₂ : ℝ) : ℂ) * Complex.I) ^ 4 = 1) : t = 0 := by
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h₁ h₂
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  generalize hL₁ : Real.log (p₁ : ℝ) = L₁ at hn₁ ⊢
  generalize hL₂ : Real.log (p₂ : ℝ) = L₂ at hn₂ ⊢
  have e₁ : 4 * (t * L₁) = n₁ * (2 * Real.pi) := by
    have h : ((4 * (t * L₁) : ℝ) : ℂ) * Complex.I = ((n₁ * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast at hn₁ ⊢; linear_combination hn₁
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h
  have e₂ : 4 * (t * L₂) = n₂ * (2 * Real.pi) := by
    have h : ((4 * (t * L₂) : ℝ) : ℂ) * Complex.I = ((n₂ * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast at hn₂ ⊢; linear_combination hn₂
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h
  by_contra ht
  have hl₁ : 0 < L₁ := hL₁ ▸ Real.log_pos (by exact_mod_cast hp₁.one_lt)
  have hl₂ : 0 < L₂ := hL₂ ▸ Real.log_pos (by exact_mod_cast hp₂.one_lt)
  -- `n₂ log p₁ = n₁ log p₂`.
  have hcross : (n₂ : ℝ) * L₁ = n₁ * L₂ := by
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have h : (n₂ : ℝ) * L₁ * (2 * Real.pi) = (n₁ : ℝ) * L₂ * (2 * Real.pi) := by
      have : (n₂ : ℝ) * (2 * Real.pi) * L₁ = (n₁ : ℝ) * (2 * Real.pi) * L₂ := by
        rw [← e₁, ← e₂]; ring
      linarith
    exact mul_right_cancel₀ hπ.ne' h
  have hn₁0 : n₁ ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, zero_mul] at e₁
    have : t * L₁ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact ht h
    · linarith
  -- Pass to natural exponents: `p₁^{|n₂|} = p₂^{|n₁|}`.
  have habs : ((n₂.natAbs : ℕ) : ℝ) * L₁ = ((n₁.natAbs : ℕ) : ℝ) * L₂ := by
    have h1 : ((n₁.natAbs : ℕ) : ℝ) = |(n₁ : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have h2 : ((n₂.natAbs : ℕ) : ℝ) = |(n₂ : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h1, h2]
    have := congrArg abs hcross
    rwa [abs_mul, abs_mul, abs_of_pos hl₁, abs_of_pos hl₂] at this
  have hpow : p₁ ^ n₂.natAbs = p₂ ^ n₁.natAbs := by
    have : Real.log ((p₁ : ℝ) ^ n₂.natAbs) = Real.log ((p₂ : ℝ) ^ n₁.natAbs) := by
      rw [Real.log_pow, Real.log_pow, hL₁, hL₂, habs]
    have hinj := Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos (by exact_mod_cast hp₁.pos) _))
      (Set.mem_Ioi.mpr (pow_pos (by exact_mod_cast hp₂.pos) _)) this
    exact_mod_cast hinj
  have hdvd : p₂ ∣ p₁ ^ n₂.natAbs := hpow ▸ dvd_pow_self p₂ (Int.natAbs_ne_zero.mpr hn₁0)
  exact hne ((Nat.prime_dvd_prime_iff_eq hp₂ hp₁).mp (hp₂.dvd_of_dvd_pow hdvd)).symm

/-- **The point is outside the special locus.** It agrees with no Dirichlet gauge point on any
archimedean line at all but finitely many primes; with `ψ` trivial this covers the Tate line `n^{it}`
of the trivial point. -/
theorem halfPoint_not_special {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (t : ℝ)
    (F : Finset ℕ) :
    ¬ ∀ p, p.Prime → p ∉ F → twist halfPoint p = twist (dirichletGauge ψ + verticalShift t) p := by
  intro h
  have hq : 4 * q ≠ 0 := by have := NeZero.ne q; omega
  -- Two primes `≡ 1 (mod 4q)` beyond `F`.
  obtain ⟨p₁, hp₁, hp₁F, hp₁m⟩ := Nat.exists_prime_gt_modEq_one (F.sup id) hq
  obtain ⟨p₂, hp₂, hp₂F, hp₂m⟩ := Nat.exists_prime_gt_modEq_one p₁ hq
  have key : ∀ p, p.Prime → F.sup id < p → p ≡ 1 [MOD 4 * q] →
      Complex.exp (((t * Real.log p : ℝ) : ℂ) * Complex.I) ^ 4 = 1 ∧
        Complex.exp (((t * Real.log p : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro p hp hpF hpm
    have hpF' : p ∉ F := fun hmem => by have := le_sup (f := id) hmem; simp at this; omega
    have h4 : p % 4 = 1 := by
      have := (Nat.ModEq.of_mul_right q hpm)
      rw [Nat.ModEq] at this
      have hp1 : 1 < p := hp.one_lt
      omega
    have hcop : Nat.Coprime p q := by
      have hg := (Nat.ModEq.of_mul_left 4 hpm).gcd_eq
      unfold Nat.Coprime
      rw [hg, Nat.gcd_one_left]
    have hψ : ψ p = 1 := by
      have hm : ((p : ℕ) : ZMod q) = 1 := by
        rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
        exact Nat.ModEq.of_mul_left 4 hpm
      rw [hm, map_one]
    have hval := h p hp hpF'
    rw [twist_add, twist_dirichletGauge ψ hp.ne_zero hcop, hψ, one_mul, twist_verticalShift] at hval
    rw [← hval]
    exact twist_halfPoint_of_mod_four hp h4
  obtain ⟨k₁, -⟩ := key p₁ hp₁ hp₁F hp₁m
  obtain ⟨k₂, hk₂⟩ := key p₂ hp₂ (lt_trans hp₁F hp₂F) hp₂m
  have ht := eq_zero_of_exp_four_mul_log hp₁ hp₂ (ne_of_lt hp₂F) k₁ k₂
  subst ht
  exact hk₂ (by simp)

end GaloisForLFunctions.ArithmeticGaugeTheory
