import GaloisForLFunctions.RHTower.StepFunctionCarrier
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicLogRate
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Möbius approximation on expanding Báez--Duarte prefixes

The discrete Báez--Duarte carrier identifies its generators with the modular sequences
`n ↦ (n mod m) / m` and its target with the constant sequence `1`.  This file analyzes the raw
Möbius combination

`A_N(n) = -∑_{1 ≤ m ≤ N} μ(m) (n mod m) / m`.

For every `1 ≤ n ≤ N`, Möbius floor inversion gives the exact identity

`1 - A_N(n) = n ∑_{m ≤ N} μ(m) / m`.

The corpus's unconditional logarithmic decay of the harmonic Möbius sum therefore makes the weighted
error vanish on the expanding window `n ≤ floor(log N)`.  The global calculation below realizes the raw
combination in the carrier and proves that its full error is exactly this discharged prefix plus one
explicit complementary weighted tail.  Convergence of that tail is the remaining raw-coefficient RH
endpoint; it is not proved here.
-/

open Filter Topology
open ArithmeticFunction

noncomputable section

namespace RHTower

/-- The raw Möbius combination of the modular sequences in the discrete Báez--Duarte carrier. -/
def bdMobiusModularApproximant (N n : ℕ) : ℝ :=
  -(∑ m ∈ Finset.Icc 1 N,
    ((moebius m : ℤ) : ℝ) * (((n % m : ℕ) : ℝ) / (m : ℝ)))

/-- The harmonic Möbius partial sum written without its harmless zero-index term. -/
theorem deningerHarmonicPartial_eq_sum_Icc (N : ℕ) :
    deningerHarmonicPartial N =
      ∑ m ∈ Finset.Icc 1 N, ((moebius m : ℤ) : ℝ) / (m : ℝ) := by
  rw [deningerHarmonicPartial]
  have hmem : 0 ∈ Finset.range (N + 1) := by simp
  have herase : (Finset.range (N + 1)).erase 0 = Finset.Icc 1 N := by
    ext m
    simp
    omega
  rw [← herase, ← Finset.sum_erase_add _ _ hmem]
  simp

/-- Möbius floor inversion remains one when the coefficient range is extended beyond `n`. -/
theorem sum_moebius_natDiv_eq_one (n N : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ m ∈ Finset.Icc 1 N,
        ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ) = 1 := by
  have h := sum_mobius_floor (n : ℝ) (by exact_mod_cast hn)
  norm_num at h
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 N := by
    intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1, hm.2.trans hnN⟩
  calc
    ∑ m ∈ Finset.Icc 1 N,
        ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ)
      = ∑ m ∈ Finset.Icc 1 n,
          ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ) := by
        symm
        exact Finset.sum_subset hsub fun m hmN hmnot => by
          have hmn : n < m := by
            simp only [Finset.mem_Icc] at hmN
            by_contra hnot
            exact hmnot (by simp only [Finset.mem_Icc]; omega)
          rw [Nat.div_eq_of_lt hmn]
          simp
    _ = 1 := by
      rw [← h]
      refine Finset.sum_congr rfl fun m _hm => ?_
      congr 1
      have hz0 : 0 ≤ ⌊((n : ℝ) / (m : ℝ))⌋ :=
        Int.floor_nonneg.2 (by positivity)
      have hInt : ((⌊((n : ℝ) / (m : ℝ))⌋₊ : ℕ) : ℤ) =
          ⌊((n : ℝ) / (m : ℝ))⌋ := by
        rw [← Int.floor_toNat]
        exact Int.toNat_of_nonneg hz0
      calc
        ((n / m : ℕ) : ℝ) = ((⌊((n : ℝ) / (m : ℝ))⌋₊ : ℕ) : ℝ) :=
          congrArg (fun q : ℕ => (q : ℝ)) (Nat.floor_div_eq_div (K := ℝ) n m).symm
        _ = ((((⌊((n : ℝ) / (m : ℝ))⌋₊ : ℕ) : ℤ) : ℝ)) := by simp
        _ = ((⌊((n : ℝ) / (m : ℝ))⌋ : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) hInt

/-- Euclidean division in the real form used by the modular carrier. -/
theorem natMod_div_eq_div_sub_natDiv (n m : ℕ) (hm : 1 ≤ m) :
    (((n % m : ℕ) : ℝ) / (m : ℝ)) =
      (n : ℝ) / (m : ℝ) - ((n / m : ℕ) : ℝ) := by
  have h := Nat.mod_add_div n m
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hR : ((n % m : ℕ) : ℝ) + (m : ℝ) * ((n / m : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast h
  rw [div_eq_iff hm0]
  field_simp
  linarith

/-- Exact raw-Möbius approximation error throughout the finite prefix `1 ≤ n ≤ N`. -/
theorem one_sub_bdMobiusModularApproximant (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    1 - bdMobiusModularApproximant N n = (n : ℝ) * deningerHarmonicPartial N := by
  rw [bdMobiusModularApproximant, sub_neg_eq_add]
  have hfloor := sum_moebius_natDiv_eq_one n N hn hnN
  rw [deningerHarmonicPartial_eq_sum_Icc]
  calc
    1 + ∑ m ∈ Finset.Icc 1 N,
        ((moebius m : ℤ) : ℝ) * (((n % m : ℕ) : ℝ) / (m : ℝ))
      = 1 + ∑ m ∈ Finset.Icc 1 N,
          ((moebius m : ℤ) : ℝ) *
            ((n : ℝ) / (m : ℝ) - ((n / m : ℕ) : ℝ)) := by
          congr 1
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [natMod_div_eq_div_sub_natDiv n m (Finset.mem_Icc.mp hm).1]
    _ = (n : ℝ) * (∑ m ∈ Finset.Icc 1 N,
          ((moebius m : ℤ) : ℝ) / (m : ℝ)) := by
      have hsplit :
          ∑ m ∈ Finset.Icc 1 N,
              ((moebius m : ℤ) : ℝ) *
                ((n : ℝ) / (m : ℝ) - ((n / m : ℕ) : ℝ))
            = (n : ℝ) * (∑ m ∈ Finset.Icc 1 N,
                ((moebius m : ℤ) : ℝ) / (m : ℝ))
              - ∑ m ∈ Finset.Icc 1 N,
                  ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ) := by
        calc
          ∑ m ∈ Finset.Icc 1 N,
              ((moebius m : ℤ) : ℝ) *
                ((n : ℝ) / (m : ℝ) - ((n / m : ℕ) : ℝ))
            = ∑ m ∈ Finset.Icc 1 N,
                ((n : ℝ) * (((moebius m : ℤ) : ℝ) / (m : ℝ)) -
                  ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ)) := by
                refine Finset.sum_congr rfl fun m _hm => ?_
                ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hsplit, hfloor]
      ring
    _ = _ := rfl

/-- Weighted squared error of the raw Möbius approximant on the finite prefix `1 ≤ n ≤ L`. -/
def bdMobiusPrefixErrorEnergy (N L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L,
    (1 - bdMobiusModularApproximant N n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- Exact prefix energy: all coordinates share the single harmonic Möbius defect. -/
theorem bdMobiusPrefixErrorEnergy_eq (N L : ℕ) (hLN : L ≤ N) :
    bdMobiusPrefixErrorEnergy N L = deningerHarmonicPartial N ^ 2 *
      ∑ n ∈ Finset.Icc 1 L, (n : ℝ) / ((n : ℝ) + 1) := by
  rw [bdMobiusPrefixErrorEnergy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnmem := Finset.mem_Icc.mp hn
  rw [one_sub_bdMobiusModularApproximant N n hnmem.1 (hnmem.2.trans hLN)]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnmem.1)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem bdMobiusPrefixErrorEnergy_nonneg (N L : ℕ) : 0 ≤ bdMobiusPrefixErrorEnergy N L := by
  rw [bdMobiusPrefixErrorEnergy]
  exact Finset.sum_nonneg fun n _hn => div_nonneg (sq_nonneg _)
    (mul_nonneg (Nat.cast_nonneg n) (by positivity))

/-- The prefix energy is bounded by prefix length times the squared harmonic Möbius defect. -/
theorem bdMobiusPrefixErrorEnergy_le (N L : ℕ) (hLN : L ≤ N) :
    bdMobiusPrefixErrorEnergy N L ≤ (L : ℝ) * deningerHarmonicPartial N ^ 2 := by
  rw [bdMobiusPrefixErrorEnergy_eq N L hLN]
  have hsum : (∑ n ∈ Finset.Icc 1 L, (n : ℝ) / ((n : ℝ) + 1)) ≤ (L : ℝ) := by
    calc
      (∑ n ∈ Finset.Icc 1 L, (n : ℝ) / ((n : ℝ) + 1))
          ≤ ∑ _n ∈ Finset.Icc 1 L, (1 : ℝ) := by
            refine Finset.sum_le_sum fun n _hn => ?_
            rw [div_le_one (by positivity)]
            linarith
      _ = (L : ℝ) := by simp
  nlinarith [sq_nonneg (deningerHarmonicPartial N)]

/-- The canonical expanding prefix used by the unconditional local approximation theorem. -/
def bdMobiusLogPrefix (N : ℕ) : ℕ := ⌊Real.log (N : ℝ)⌋₊

theorem bdMobiusLogPrefix_le (N : ℕ) : bdMobiusLogPrefix N ≤ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [bdMobiusLogPrefix]
  · have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hfloor : ((bdMobiusLogPrefix N : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
      exact Nat.floor_le hlog0
    have hlogN : Real.log (N : ℝ) ≤ (N : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hN)
      linarith
    exact_mod_cast hfloor.trans hlogN

/-- **Unconditional expanding-prefix approximation.**  The raw Möbius modular combination converges
to the constant target in weighted squared error on `n ≤ floor(log N)`.  No tail claim is made. -/
theorem tendsto_bdMobiusLogPrefixErrorEnergy_zero :
    Tendsto (fun N : ℕ => bdMobiusPrefixErrorEnergy N (bdMobiusLogPrefix N))
      atTop (𝓝 0) := by
  have hmajor : Tendsto (fun N : ℕ =>
      (Real.log (N : ℝ) * deningerHarmonicPartial N) ^ 2) atTop (𝓝 0) := by
    convert RHTower.Sieve.tendsto_log_mul_deningerHarmonicPartial_zero.pow 2 using 1
    simp
  rw [tendsto_order]
  refine ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall fun N =>
      ha.trans_le (bdMobiusPrefixErrorEnergy_nonneg N (bdMobiusLogPrefix N))
  · intro b hb
    have hevent := ((tendsto_order.1 hmajor).2 b hb)
    filter_upwards [hevent,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (Real.exp 1)] with N hN hNe
    have hlog1 : 1 ≤ Real.log (N : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hNe
    have hfloor : ((bdMobiusLogPrefix N : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
      exact Nat.floor_le (zero_le_one.trans hlog1)
    have hbase := bdMobiusPrefixErrorEnergy_le N (bdMobiusLogPrefix N)
      (bdMobiusLogPrefix_le N)
    have hH2 : 0 ≤ deningerHarmonicPartial N ^ 2 := sq_nonneg _
    calc
      bdMobiusPrefixErrorEnergy N (bdMobiusLogPrefix N)
          ≤ (bdMobiusLogPrefix N : ℝ) * deningerHarmonicPartial N ^ 2 := hbase
      _ ≤ Real.log (N : ℝ) * deningerHarmonicPartial N ^ 2 :=
        mul_le_mul_of_nonneg_right hfloor hH2
      _ ≤ (Real.log (N : ℝ) * deningerHarmonicPartial N) ^ 2 := by
        nlinarith [sq_nonneg (deningerHarmonicPartial N)]
      _ < b := hN

/-! ## Global coordinate error and exact prefix--tail split -/

/-- Residual from truncating Möbius floor inversion at modulus `N`. -/
def bdMobiusFloorResidual (N n : ℕ) : ℝ :=
  1 - ∑ m ∈ Finset.Icc 1 N,
    ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ)

/-- Global coordinate error: harmonic defect plus truncated floor-inversion residual. -/
theorem one_sub_bdMobiusModularApproximant_eq_harmonic_add_floorResidual (N n : ℕ) :
    1 - bdMobiusModularApproximant N n =
      (n : ℝ) * deningerHarmonicPartial N + bdMobiusFloorResidual N n := by
  rw [bdMobiusModularApproximant, bdMobiusFloorResidual, sub_neg_eq_add,
    deningerHarmonicPartial_eq_sum_Icc]
  calc
    1 + ∑ m ∈ Finset.Icc 1 N,
        ((moebius m : ℤ) : ℝ) * (((n % m : ℕ) : ℝ) / (m : ℝ))
      = 1 + ∑ m ∈ Finset.Icc 1 N,
          ((moebius m : ℤ) : ℝ) *
            ((n : ℝ) / (m : ℝ) - ((n / m : ℕ) : ℝ)) := by
          congr 1
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [natMod_div_eq_div_sub_natDiv n m (Finset.mem_Icc.mp hm).1]
    _ = (n : ℝ) * (∑ m ∈ Finset.Icc 1 N,
          ((moebius m : ℤ) : ℝ) / (m : ℝ)) +
        (1 - ∑ m ∈ Finset.Icc 1 N,
          ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ)) := by
      have hsplit :
          ∑ m ∈ Finset.Icc 1 N,
              ((moebius m : ℤ) : ℝ) *
                ((n : ℝ) / (m : ℝ) - ((n / m : ℕ) : ℝ))
            = (n : ℝ) * (∑ m ∈ Finset.Icc 1 N,
                ((moebius m : ℤ) : ℝ) / (m : ℝ))
              - ∑ m ∈ Finset.Icc 1 N,
                  ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ) := by
        calc
          ∑ m ∈ Finset.Icc 1 N,
              ((moebius m : ℤ) : ℝ) *
                ((n : ℝ) / (m : ℝ) - ((n / m : ℕ) : ℝ))
            = ∑ m ∈ Finset.Icc 1 N,
                ((n : ℝ) * (((moebius m : ℤ) : ℝ) / (m : ℝ)) -
                  ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ)) := by
                refine Finset.sum_congr rfl fun m _hm => ?_
                ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hsplit]
      ring

/-- Floor-inversion residual vanishes throughout the prefix `1 ≤ n ≤ N`. -/
theorem bdMobiusFloorResidual_eq_zero (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    bdMobiusFloorResidual N n = 0 := by
  rw [bdMobiusFloorResidual, sum_moebius_natDiv_eq_one n N hn hnN, sub_self]

/-- Beyond the cutoff, the residual is exactly the omitted Möbius-floor tail. -/
theorem bdMobiusFloorResidual_eq_sum_Ioc (N n : ℕ) (hn : 1 ≤ n) (hNn : N ≤ n) :
    bdMobiusFloorResidual N n =
      ∑ m ∈ Finset.Ioc N n,
        ((moebius m : ℤ) : ℝ) * ((n / m : ℕ) : ℝ) := by
  have hfull := sum_moebius_natDiv_eq_one n n hn le_rfl
  have hunion : Finset.Icc 1 N ∪ Finset.Ioc N n = Finset.Icc 1 n := by
    ext m
    simp
    omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Ioc N n) := by
    simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [bdMobiusFloorResidual, ← hfull, ← hunion, Finset.sum_union hdisj]
  ring

/-- Raw modular approximants are uniformly bounded at each fixed cutoff. -/
theorem abs_bdMobiusModularApproximant_le (N n : ℕ) :
    |bdMobiusModularApproximant N n| ≤ (N : ℝ) := by
  rw [bdMobiusModularApproximant, abs_neg]
  calc
    |∑ m ∈ Finset.Icc 1 N,
        ((moebius m : ℤ) : ℝ) * (((n % m : ℕ) : ℝ) / (m : ℝ))|
      ≤ ∑ m ∈ Finset.Icc 1 N,
          |((moebius m : ℤ) : ℝ) * (((n % m : ℕ) : ℝ) / (m : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 N, (1 : ℝ) := by
      refine Finset.sum_le_sum fun m _hm => ?_
      rw [abs_mul]
      calc
        |((moebius m : ℤ) : ℝ)| * |((n % m : ℕ) : ℝ) / (m : ℝ)|
            ≤ (1 : ℝ) * 1 := mul_le_mul (RHTower.Sieve.abs_moebius_real_le_one m)
              (abs_modSeq_le m n) (abs_nonneg _) zero_le_one
        _ = 1 := mul_one 1
    _ = (N : ℝ) := by simp

/-- Uniform bound for the raw modular error sequence. -/
theorem abs_one_sub_bdMobiusModularApproximant_le (N n : ℕ) :
    |1 - bdMobiusModularApproximant N n| ≤ (N : ℝ) + 1 := by
  calc
    |1 - bdMobiusModularApproximant N n|
      ≤ |(1 : ℝ)| + |bdMobiusModularApproximant N n| := abs_sub _ _
    _ ≤ 1 + (N : ℝ) := by
      norm_num
      exact abs_bdMobiusModularApproximant_le N n
    _ = (N : ℝ) + 1 := by ring

/-- Full weighted error energy of the raw Möbius modular approximant. -/
def bdMobiusFullErrorEnergy (N : ℕ) : ℝ :=
  stepGram (fun n => 1 - bdMobiusModularApproximant N n)
    (fun n => 1 - bdMobiusModularApproximant N n)

/-- Complementary weighted tail after coordinates `1,…,L`. -/
def bdMobiusComplementaryTailErrorEnergy (N L : ℕ) : ℝ :=
  ∑' j : ℕ,
    (1 - bdMobiusModularApproximant N (j + L + 1)) ^ 2 /
      ((((j + L : ℕ) : ℝ) + 1) * (((j + L : ℕ) : ℝ) + 2))

/-- The full error energy is the sum of its finite prefix and complementary tail. -/
theorem bdMobiusFullErrorEnergy_eq_prefix_add_tail (N L : ℕ) :
    bdMobiusFullErrorEnergy N =
      bdMobiusPrefixErrorEnergy N L + bdMobiusComplementaryTailErrorEnergy N L := by
  let f : ℕ → ℝ := fun j =>
    (1 - bdMobiusModularApproximant N (j + 1)) ^ 2 /
      (((j : ℝ) + 1) * ((j : ℝ) + 2))
  have hsum : HasSum f (bdMobiusFullErrorEnergy N) := by
    simpa [f, bdMobiusFullErrorEnergy, pow_two] using
      (hasSum_stepGram
        (abs_one_sub_bdMobiusModularApproximant_le N)
        (abs_one_sub_bdMobiusModularApproximant_le N))
  have hprefix : ∑ i ∈ Finset.range L, f i = bdMobiusPrefixErrorEnergy N L := by
    rw [bdMobiusPrefixErrorEnergy]
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]
      simp [f]
      ring
  have hsplit := hsum.summable.sum_add_tsum_nat_add L
  calc
    bdMobiusFullErrorEnergy N = ∑' j, f j := hsum.tsum_eq.symm
    _ = (∑ i ∈ Finset.range L, f i) + ∑' j, f (j + L) := hsplit.symm
    _ = bdMobiusPrefixErrorEnergy N L + bdMobiusComplementaryTailErrorEnergy N L := by
      rw [hprefix, bdMobiusComplementaryTailErrorEnergy]

/-- The full raw-Möbius error already contains the square-root-scale harmonic defect on its
first `N` coordinates. -/
theorem half_nat_mul_deningerHarmonicPartial_sq_le_bdMobiusFullErrorEnergy (N : ℕ) :
    (N : ℝ) / 2 * deningerHarmonicPartial N ^ 2 ≤ bdMobiusFullErrorEnergy N := by
  have hsum : (N : ℝ) / 2 ≤
      ∑ n ∈ Finset.Icc 1 N, (n : ℝ) / ((n : ℝ) + 1) := by
    calc
      (N : ℝ) / 2 = ∑ _n ∈ Finset.Icc 1 N, (1 / 2 : ℝ) := by
        simp
        ring
      _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) / ((n : ℝ) + 1) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity)]
        linarith
  have hprefix :
      (N : ℝ) / 2 * deningerHarmonicPartial N ^ 2 ≤
        bdMobiusPrefixErrorEnergy N N := by
    rw [bdMobiusPrefixErrorEnergy_eq N N le_rfl]
    nlinarith [sq_nonneg (deningerHarmonicPartial N)]
  rw [bdMobiusFullErrorEnergy_eq_prefix_add_tail N N]
  have htail : 0 ≤ bdMobiusComplementaryTailErrorEnergy N N := by
    apply tsum_nonneg
    intro j
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by positivity))
  linarith

/-- Vanishing raw-Möbius error would force the critical square-root-scale harmonic defect to
vanish.  This is the exact boundary condition contradicted by critical-line zeta zeros. -/
theorem tendsto_nat_mul_deningerHarmonicPartial_sq_zero_of_fullError
    (hfull : Tendsto bdMobiusFullErrorEnergy atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ) * deningerHarmonicPartial N ^ 2) atTop (𝓝 0) := by
  have hhalf : Tendsto
      (fun N : ℕ => (N : ℝ) / 2 * deningerHarmonicPartial N ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro N
      positivity
    · intro N
      exact half_nat_mul_deningerHarmonicPartial_sq_le_bdMobiusFullErrorEnergy N
    · exact hfull
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  convert htwo.mul hhalf using 1
  · funext N
    ring
  · norm_num

/-- Full modular error energy is the squared carrier norm of the corresponding step vector. -/
theorem bdMobiusFullErrorEnergy_eq_norm_sq (N : ℕ) :
    bdMobiusFullErrorEnergy N =
      ‖stepVec (fun n => 1 - bdMobiusModularApproximant N n)
        (abs_one_sub_bdMobiusModularApproximant_le N)‖ ^ 2 := by
  have h : (RCLike.re (inner ℂ
      (stepVec (fun n => 1 - bdMobiusModularApproximant N n)
        (abs_one_sub_bdMobiusModularApproximant_le N))
      (stepVec (fun n => 1 - bdMobiusModularApproximant N n)
        (abs_one_sub_bdMobiusModularApproximant_le N))) : ℝ) =
      ‖stepVec (fun n => 1 - bdMobiusModularApproximant N n)
        (abs_one_sub_bdMobiusModularApproximant_le N)‖ ^ 2 :=
    inner_self_eq_norm_sq _
  rw [inner_stepVec] at h
  simpa [bdMobiusFullErrorEnergy] using h

/-! ## Carrier realization and complementary-tail endpoint -/

/-- Raw Möbius modular approximant as a carrier vector. -/
def bdMobiusModularApproximantVec (N : ℕ) : BDCarrier :=
  stepVec (bdMobiusModularApproximant N) (abs_bdMobiusModularApproximant_le N)

/-- Carrier residual is exactly the step vector of the modular coordinate error. -/
theorem bdTarget_sub_bdMobiusModularApproximantVec_eq (N : ℕ) :
    bdTarget - bdMobiusModularApproximantVec N =
      stepVec (fun n => 1 - bdMobiusModularApproximant N n)
        (abs_one_sub_bdMobiusModularApproximant_le N) := by
  rw [bdTarget_eq_stepVec, bdMobiusModularApproximantVec]
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_sub
      (stepVec (fun _ => (1 : ℝ)) abs_one_le)
      (stepVec (bdMobiusModularApproximant N) (abs_bdMobiusModularApproximant_le N)),
    (memLp_stepFun abs_one_le).coeFn_toLp,
    (memLp_stepFun (abs_bdMobiusModularApproximant_le N)).coeFn_toLp,
    (memLp_stepFun (abs_one_sub_bdMobiusModularApproximant_le N)).coeFn_toLp]
      with u hsub hone happ herr
  rw [hsub, Pi.sub_apply, stepVec, stepVec, stepVec, hone, happ, herr]
  simp only [stepFun]
  push_cast
  ring

/-- Same raw approximant written as its finite Möbius combination of criterion generators. -/
def bdMobiusGeneratorCombination (N : ℕ) : BDCarrier :=
  ∑ m ∈ Finset.Icc 1 N,
    (((-((moebius m : ℤ) : ℝ) : ℝ) : ℂ)) • bdGen (1 / (m : ℝ))

theorem bdMobiusModularApproximantVec_eq_generatorCombination (N : ℕ) :
    bdMobiusModularApproximantVec N = bdMobiusGeneratorCombination N := by
  rw [bdMobiusModularApproximantVec, bdMobiusGeneratorCombination]
  let c : ℕ → ℂ := fun m => (((-((moebius m : ℤ) : ℝ) : ℝ) : ℂ))
  let v : ℕ → BDCarrier := fun m =>
    stepVec (fun n => ((n % m : ℕ) : ℝ) / (m : ℝ)) (abs_modSeq_le m)
  have hrewrite :
      (∑ m ∈ Finset.Icc 1 N,
        (((-((moebius m : ℤ) : ℝ) : ℝ) : ℂ)) • bdGen (1 / (m : ℝ))) =
      ∑ m ∈ Finset.Icc 1 N, c m • v m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [c, v]
    rw [bdGen_eq_stepVec (Finset.mem_Icc.mp hm).1]
  rw [hrewrite]
  apply MeasureTheory.Lp.ext
  have hcoeSum : ∀ᵐ u ∂bdMeasure,
      (((∑ m ∈ Finset.Icc 1 N, c m • v m : BDCarrier) : ℝ → ℂ) u) =
        ∑ m ∈ Finset.Icc 1 N, c m * (((v m : BDCarrier) : ℝ → ℂ) u) := by
    induction Finset.Icc 1 N using Finset.induction_on with
    | empty =>
        filter_upwards [(MeasureTheory.Lp.coeFn_zero ℂ 2 bdMeasure)] with u hu
        simpa using hu
    | @insert a s ha ih =>
        filter_upwards [MeasureTheory.Lp.coeFn_add (c a • v a)
            (∑ m ∈ s, c m • v m), MeasureTheory.Lp.coeFn_smul (c a) (v a), ih]
            with u hadd hsmul hrest
        rw [Finset.sum_insert ha, hadd, Pi.add_apply, hsmul, Pi.smul_apply,
          smul_eq_mul, hrest, Finset.sum_insert ha]
  have hall : ∀ᵐ u ∂bdMeasure, ∀ m ∈ Finset.Icc 1 N,
      (((v m : BDCarrier) : ℝ → ℂ) u) =
          stepFun (fun n => ((n % m : ℕ) : ℝ) / (m : ℝ)) u := by
    rw [Filter.eventually_all_finset]
    intro m hm
    change ((stepVec (fun n => ((n % m : ℕ) : ℝ) / (m : ℝ))
      (abs_modSeq_le m) : BDCarrier) : ℝ → ℂ) =ᵐ[bdMeasure]
        stepFun (fun n => ((n % m : ℕ) : ℝ) / (m : ℝ))
    exact (memLp_stepFun (abs_modSeq_le m)).coeFn_toLp
  filter_upwards [(memLp_stepFun (abs_bdMobiusModularApproximant_le N)).coeFn_toLp,
      hcoeSum, hall] with u happ hsum hallu
  rw [stepVec, happ, hsum]
  have hterms :
      (∑ m ∈ Finset.Icc 1 N, c m * (((v m : BDCarrier) : ℝ → ℂ) u)) =
        ∑ m ∈ Finset.Icc 1 N,
          c m * stepFun (fun n => ((n % m : ℕ) : ℝ) / (m : ℝ)) u := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hallu m hm]
  rw [hterms]
  simp only [c, stepFun, bdMobiusModularApproximant, Complex.ofReal_neg, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_div]
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _hm => ?_
  ring

theorem bdGen_one_div_nat_mem_bdSpanSet_discrete (m : ℕ) (hm : 1 ≤ m) :
    bdGen (1 / (m : ℝ)) ∈ bdSpanSet bdDiscrete := by
  apply Submodule.subset_span
  refine ⟨m - 1, ?_⟩
  apply congrArg bdGen
  rw [bdDiscrete]
  have hsucc : m - 1 + 1 = m := by omega
  have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hsucc
  rw [hcast]

theorem bdMobiusGeneratorCombination_mem_bdSpanSet_discrete (N : ℕ) :
    bdMobiusGeneratorCombination N ∈ bdSpanSet bdDiscrete := by
  rw [bdMobiusGeneratorCombination]
  apply Submodule.sum_mem
  intro m hm
  exact Submodule.smul_mem _ _
    (bdGen_one_div_nat_mem_bdSpanSet_discrete m (Finset.mem_Icc.mp hm).1)

/-- The raw Möbius full error controls the squared distance to the complete discrete span. -/
theorem bdDist_bdDiscrete_sq_le_bdMobiusFullErrorEnergy (N : ℕ) :
    bdDist bdDiscrete ^ 2 ≤ bdMobiusFullErrorEnergy N := by
  have hle := Metric.infDist_le_dist_of_mem (x := bdTarget)
    (bdMobiusGeneratorCombination_mem_bdSpanSet_discrete N)
  rw [← bdMobiusModularApproximantVec_eq_generatorCombination N, dist_eq_norm,
    bdTarget_sub_bdMobiusModularApproximantVec_eq] at hle
  change bdDist bdDiscrete ≤ ‖stepVec (fun n => 1 - bdMobiusModularApproximant N n)
    (abs_one_sub_bdMobiusModularApproximant_le N)‖ at hle
  have hd0 : 0 ≤ bdDist bdDiscrete := bdDist_nonneg _
  have hn0 : 0 ≤ ‖stepVec (fun n => 1 - bdMobiusModularApproximant N n)
      (abs_one_sub_bdMobiusModularApproximant_le N)‖ := norm_nonneg _
  calc
    bdDist bdDiscrete ^ 2 ≤ ‖stepVec (fun n => 1 - bdMobiusModularApproximant N n)
        (abs_one_sub_bdMobiusModularApproximant_le N)‖ ^ 2 :=
      (sq_le_sq₀ hd0 hn0).2 hle
    _ = bdMobiusFullErrorEnergy N := (bdMobiusFullErrorEnergy_eq_norm_sq N).symm

/-- On the canonical logarithmic window, full raw-Möbius approximation is exactly the unresolved
complementary-tail problem. -/
theorem tendsto_bdMobiusFullErrorEnergy_zero_iff_complementaryTail :
    Tendsto bdMobiusFullErrorEnergy atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ =>
        bdMobiusComplementaryTailErrorEnergy N (bdMobiusLogPrefix N)) atTop (𝓝 0) := by
  have heq : (fun N : ℕ => bdMobiusFullErrorEnergy N) =
      fun N => bdMobiusPrefixErrorEnergy N (bdMobiusLogPrefix N) +
        bdMobiusComplementaryTailErrorEnergy N (bdMobiusLogPrefix N) := by
    funext N
    exact bdMobiusFullErrorEnergy_eq_prefix_add_tail N (bdMobiusLogPrefix N)
  have hprefix := tendsto_bdMobiusLogPrefixErrorEnergy_zero
  constructor
  · intro hfull
    have hsub := hfull.sub hprefix
    convert hsub using 1
    · funext N
      have hN := congrFun heq N
      linarith
    · simp
  · intro htail
    change Tendsto (fun N : ℕ => bdMobiusFullErrorEnergy N) atTop (𝓝 0)
    rw [heq]
    convert hprefix.add htail using 1
    simp

/-- **Raw Möbius complementary-tail endpoint.**  The logarithmic prefix is already discharged
unconditionally, so vanishing of only the remaining weighted tail forces the complete discrete
Báez--Duarte distance to vanish and proves RH. -/
theorem riemannHypothesis_of_tendsto_bdMobiusComplementaryTailErrorEnergy_zero
    (h : Tendsto (fun N : ℕ =>
      bdMobiusComplementaryTailErrorEnergy N (bdMobiusLogPrefix N)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hfull : Tendsto bdMobiusFullErrorEnergy atTop (𝓝 0) :=
    tendsto_bdMobiusFullErrorEnergy_zero_iff_complementaryTail.mpr h
  apply riemannHypothesis_of_bdDist_eq_zero bdDiscrete bdDiscrete_mem
  apply sq_eq_zero_iff.mp
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto' tendsto_const_nhds hfull
    exact fun N => bdDist_bdDiscrete_sq_le_bdMobiusFullErrorEnergy N
  · exact sq_nonneg _

end RHTower
