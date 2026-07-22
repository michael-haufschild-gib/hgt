import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.RHTower.SuzukiRectangularPositiveArchLagCompletion

/-!
# Bounded-displacement log-Haar transport for the Mangoldt wall

The positive Suzuki wall has atoms of mass `2 * Λ(n) / n` at lag `2 * log n`.
Mertens' first theorem does more than bound their cumulative mass: it gives two
canonical, pairwise-disjoint Lebesgue cells of exactly the same mass.  One cell
lies uniformly behind the atom and one uniformly ahead of it.  Thus every atom
whose whole transport cell stays on a monotone branch of the rectangular lag
profile is discharged by ordinary integral monotonicity.  Only cells meeting a
turning seam can remain in the RH-bearing residual.

No statement about zeta zeros, prime-number-theorem remainder, or RH is used.
-/

open scoped BigOperators
open Finset MeasureTheory Set

noncomputable section

namespace RHTower

/-- Twice the harmonic Mangoldt cumulative.  This is the cumulative mass of the
lag atoms `2 * Λ(n) / n` through the node `2 * log n`. -/
def mangoldtLogHaarMass (n : ℕ) : ℝ :=
  2 * ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt d / (d : ℝ)

/-- Mass of the individual lag atom at `2 * log n`. -/
def mangoldtLogHaarAtomMass (n : ℕ) : ℝ :=
  2 * ArithmeticFunction.vonMangoldt n / (n : ℝ)

/-- Logarithmic lag occupied by the `n`th Mangoldt atom. -/
def mangoldtLogHaarNode (n : ℕ) : ℝ := 2 * Real.log n

/-- Radius supplied by the formalized elementary Mertens theorem. -/
def mangoldtLogHaarMertensRadius : ℝ := 2 * (Real.log 4 + 4)

/-- Uniform displacement of the two canonical transport cells. -/
def mangoldtLogHaarTransportWidth : ℝ :=
  2 + 2 * mangoldtLogHaarMertensRadius

theorem mangoldtLogHaarMertensRadius_nonneg :
    0 ≤ mangoldtLogHaarMertensRadius := by
  rw [mangoldtLogHaarMertensRadius]
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

theorem mangoldtLogHaarTransportWidth_nonneg :
    0 ≤ mangoldtLogHaarTransportWidth := by
  rw [mangoldtLogHaarTransportWidth]
  positivity [mangoldtLogHaarMertensRadius_nonneg]

theorem mangoldtLogHaarAtomMass_nonneg (n : ℕ) :
    0 ≤ mangoldtLogHaarAtomMass n := by
  rw [mangoldtLogHaarAtomMass]
  exact div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg)
    (Nat.cast_nonneg n)

/-- Adding one integer adds exactly its Mangoldt atom. -/
theorem mangoldtLogHaarMass_succ (n : ℕ) :
    mangoldtLogHaarMass (n + 1) =
      mangoldtLogHaarMass n + mangoldtLogHaarAtomMass (n + 1) := by
  rw [mangoldtLogHaarMass, mangoldtLogHaarMass, mangoldtLogHaarAtomMass,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  ring

/-- Cumulative Mangoldt lag mass is monotone. -/
theorem monotone_mangoldtLogHaarMass : Monotone mangoldtLogHaarMass := by
  apply monotone_nat_of_le_succ
  intro n
  rw [mangoldtLogHaarMass_succ]
  exact le_add_of_nonneg_right (mangoldtLogHaarAtomMass_nonneg (n + 1))

/-- Formal Mertens gives a uniform band between cumulative atomic mass and
Lebesgue lag mass. -/
theorem abs_mangoldtLogHaarMass_sub_node_le
    {n : ℕ} (hn : 1 ≤ n) :
    |mangoldtLogHaarMass n - mangoldtLogHaarNode n| ≤
      mangoldtLogHaarMertensRadius := by
  have h := Mertens.mertens_first n hn
  rw [mangoldtLogHaarMass, mangoldtLogHaarNode, mangoldtLogHaarMertensRadius]
  calc
    |2 * (∑ d ∈ Finset.Icc 1 n,
        ArithmeticFunction.vonMangoldt d / (d : ℝ)) - 2 * Real.log n| =
        2 * |(∑ d ∈ Finset.Icc 1 n,
          ArithmeticFunction.vonMangoldt d / (d : ℝ)) - Real.log n| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (Real.log 4 + 4) := mul_le_mul_of_nonneg_left h (by norm_num)

/-- Adjacent positive logarithmic nodes are separated by at most two lag units.
This deliberately uses a symbolic logarithmic inequality, not finite computation. -/
theorem mangoldtLogHaarNode_sub_two_le_pred
    {n : ℕ} (hn : 2 ≤ n) :
    mangoldtLogHaarNode n - 2 ≤ mangoldtLogHaarNode (n - 1) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hpredNat : 0 < n - 1 := by omega
  have hpredR : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast hpredNat
  have hratioPos : 0 < (n : ℝ) / (n - 1 : ℕ) := div_pos hnR hpredR
  have hlog := Real.log_le_sub_one_of_pos hratioPos
  rw [Real.log_div hnR.ne' hpredR.ne'] at hlog
  have hratio : (n : ℝ) / (n - 1 : ℕ) ≤ 2 := by
    rw [div_le_iff₀ hpredR]
    norm_cast
    omega
  rw [mangoldtLogHaarNode, mangoldtLogHaarNode]
  nlinarith

/-! ## Sharp two-unit interface from the known log-Haar capacity law -/

/-- Literature capacity theorem in the exact form consumed by the sharp transport.  Ramaré--
Zuniga Alterman prove this inequality for every real cutoff.  It is named here instead of being
silently reintroduced as a new RH obligation. -/
def MangoldtLogHaarCapacity : Prop :=
  ∀ n : ℕ, 1 ≤ n → mangoldtLogHaarMass n ≤ mangoldtLogHaarNode n

/-- Stirling-free factorial lower bound with the endpoint constant retained. -/
theorem sum_log_ge_with_endpoint (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤
      ∑ m ∈ Finset.Icc 1 n, Real.log m := by
  induction n with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
        have ih' := ih (by omega)
        have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
        have hlog : Real.log ((k + 1 : ℕ) / (k : ℝ)) ≤
            ((k + 1 : ℕ) / (k : ℝ)) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at hlog
        have hstep : (k : ℝ) *
            (Real.log (k + 1) - Real.log k) ≤ 1 := by
          have hkk : (k : ℝ) * (((k : ℝ) + 1) / k) = (k : ℝ) + 1 := by
            field_simp
          push_cast at hlog
          calc
            (k : ℝ) * (Real.log (k + 1) - Real.log k) ≤
                (k : ℝ) * (((k : ℝ) + 1) / k - 1) := by
              nlinarith
            _ = 1 := by rw [mul_sub, hkk]; ring
        push_cast
        push_cast at ih'
        nlinarith

/-- The cumulative Mangoldt lag mass never trails its logarithmic node by more than two. -/
theorem mangoldtLogHaarNode_sub_two_le_mass
    {n : ℕ} (hn : 1 ≤ n) :
    mangoldtLogHaarNode n - 2 + 2 / (n : ℝ) ≤ mangoldtLogHaarMass n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  set S := ∑ d ∈ Finset.Icc 1 n,
    ArithmeticFunction.vonMangoldt d / (d : ℝ) with hS
  have hUP : ∑ d ∈ Finset.Icc 1 n,
      ArithmeticFunction.vonMangoldt d * ((n / d : ℕ) : ℝ) ≤ (n : ℝ) * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt d :=
      ArithmeticFunction.vonMangoldt_nonneg
    calc
      ArithmeticFunction.vonMangoldt d * ((n / d : ℕ) : ℝ) ≤
          ArithmeticFunction.vonMangoldt d * ((n : ℝ) / d) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le hΛ
      _ = (n : ℝ) * (ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by ring
  have heq := Mertens.log_summatory_eq n
  have hlo := sum_log_ge_with_endpoint n hn
  rw [mangoldtLogHaarMass, mangoldtLogHaarNode, ← hS]
  have hinv : (2 / (n : ℝ)) * (n : ℝ) = 2 := by field_simp
  nlinarith

/-- The preceding cumulative mass is at most two lag units behind the next atom. -/
theorem mangoldtLogHaarNode_sub_two_le_mass_pred
    {n : ℕ} (hn : 2 ≤ n) :
    mangoldtLogHaarNode n - 2 ≤ mangoldtLogHaarMass (n - 1) := by
  have hpred : 1 ≤ n - 1 := by omega
  have hlower := mangoldtLogHaarNode_sub_two_le_mass hpred
  have hnR : (0 : ℝ) < n := by positivity
  have hpredR : (0 : ℝ) < (n - 1 : ℕ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < (n : ℝ) / (n - 1 : ℕ) by positivity)
  rw [Real.log_div hnR.ne' hpredR.ne'] at hlog
  have hpredCast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hratio : (n : ℝ) / (n - 1 : ℕ) - 1 = 1 / (n - 1 : ℕ) := by
    rw [hpredCast]
    have hden : (n : ℝ) - 1 ≠ 0 := by linarith
    field_simp [hden]
    ring
  rw [hratio] at hlog
  simp only [mangoldtLogHaarNode] at hlower ⊢
  ring_nf at hlower hlog ⊢
  linarith

/-- Sharp past cell in unshifted cumulative-mass coordinates. -/
def mangoldtLogHaarSharpPastCell (n : ℕ) : Set ℝ :=
  Set.Ioc (mangoldtLogHaarMass (n - 1)) (mangoldtLogHaarMass n)

/-- Sharp future cell obtained by translating the same mass partition by two lag units. -/
def mangoldtLogHaarSharpFutureCell (n : ℕ) : Set ℝ :=
  Set.Ioc (mangoldtLogHaarMass (n - 1) + 2) (mangoldtLogHaarMass n + 2)

theorem mangoldtLogHaarSharpPastCell_length
    {n : ℕ} (hn : 2 ≤ n) :
    mangoldtLogHaarMass n - mangoldtLogHaarMass (n - 1) =
      mangoldtLogHaarAtomMass n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k - 1 = 1 + k by omega,
    show 2 + k = (1 + k) + 1 by omega, mangoldtLogHaarMass_succ]
  ring

theorem mangoldtLogHaarSharpFutureCell_length
    {n : ℕ} (hn : 2 ≤ n) :
    (mangoldtLogHaarMass n + 2) - (mangoldtLogHaarMass (n - 1) + 2) =
      mangoldtLogHaarAtomMass n := by
  linarith [mangoldtLogHaarSharpPastCell_length hn]

/-- Under the known capacity law, the sharp past cell lies in the preceding two lag units. -/
theorem mangoldtLogHaarSharpPastCell_subset_twoBand
    (hcap : MangoldtLogHaarCapacity) {n : ℕ} (hn : 2 ≤ n) :
    mangoldtLogHaarSharpPastCell n ⊆
      Set.Ioc (mangoldtLogHaarNode n - 2) (mangoldtLogHaarNode n) := by
  have hn1 : 1 ≤ n := by omega
  have hlower := mangoldtLogHaarNode_sub_two_le_mass_pred hn
  have hupper := hcap n hn1
  intro x hx
  rw [mangoldtLogHaarSharpPastCell, Set.mem_Ioc] at hx
  exact ⟨lt_of_le_of_lt hlower hx.1, hx.2.trans hupper⟩

/-- Under the same law, the translated future cell lies in the following two lag units. -/
theorem mangoldtLogHaarSharpFutureCell_subset_twoBand
    (hcap : MangoldtLogHaarCapacity) {n : ℕ} (hn : 2 ≤ n) :
    mangoldtLogHaarSharpFutureCell n ⊆
      Set.Ioc (mangoldtLogHaarNode n) (mangoldtLogHaarNode n + 2) := by
  have hn1 : 1 ≤ n := by omega
  have hlower := mangoldtLogHaarNode_sub_two_le_mass_pred hn
  have hupper := hcap n hn1
  intro x hx
  rw [mangoldtLogHaarSharpFutureCell, Set.mem_Ioc] at hx
  exact ⟨by linarith [hlower, hx.1], by linarith [hupper, hx.2]⟩

/-- Sharp past cells are pairwise disjoint before any analytic estimate is applied. -/
theorem mangoldtLogHaarSharpPastCell_pairwiseDisjoint :
    Set.PairwiseDisjoint Set.univ mangoldtLogHaarSharpPastCell := by
  intro m _ n _ hmn
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · have hle := monotone_mangoldtLogHaarMass (show m ≤ n - 1 by omega)
    change Disjoint
      (Set.Ioc (mangoldtLogHaarMass (m - 1)) (mangoldtLogHaarMass m))
      (Set.Ioc (mangoldtLogHaarMass (n - 1)) (mangoldtLogHaarMass n))
    exact Set.Ioc_disjoint_Ioc_of_le hle
  · have hle := monotone_mangoldtLogHaarMass (show n ≤ m - 1 by omega)
    change Disjoint
      (Set.Ioc (mangoldtLogHaarMass (m - 1)) (mangoldtLogHaarMass m))
      (Set.Ioc (mangoldtLogHaarMass (n - 1)) (mangoldtLogHaarMass n))
    exact (Set.Ioc_disjoint_Ioc_of_le hle).symm

/-- Sharp future cells are the same disjoint partition translated by two. -/
theorem mangoldtLogHaarSharpFutureCell_pairwiseDisjoint :
    Set.PairwiseDisjoint Set.univ mangoldtLogHaarSharpFutureCell := by
  intro m _ n _ hmn
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · have hle := monotone_mangoldtLogHaarMass (show m ≤ n - 1 by omega)
    change Disjoint
      (Set.Ioc (mangoldtLogHaarMass (m - 1) + 2) (mangoldtLogHaarMass m + 2))
      (Set.Ioc (mangoldtLogHaarMass (n - 1) + 2) (mangoldtLogHaarMass n + 2))
    exact Set.Ioc_disjoint_Ioc_of_le (by linarith)
  · have hle := monotone_mangoldtLogHaarMass (show n ≤ m - 1 by omega)
    change Disjoint
      (Set.Ioc (mangoldtLogHaarMass (m - 1) + 2) (mangoldtLogHaarMass m + 2))
      (Set.Ioc (mangoldtLogHaarMass (n - 1) + 2) (mangoldtLogHaarMass n + 2))
    exact (Set.Ioc_disjoint_Ioc_of_le (by linarith)).symm

private theorem integral_const_on_mangoldtLogHaarSharpPastCell
    {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    (∫ _t : ℝ in mangoldtLogHaarSharpPastCell n, c) =
      mangoldtLogHaarAtomMass n * c := by
  rw [MeasureTheory.integral_const, Measure.real, mangoldtLogHaarSharpPastCell,
    Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal]
  · rw [mangoldtLogHaarSharpPastCell_length hn]
    simp only [smul_eq_mul]
  · rw [mangoldtLogHaarSharpPastCell_length hn]
    exact mangoldtLogHaarAtomMass_nonneg n

private theorem integral_const_on_mangoldtLogHaarSharpFutureCell
    {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    (∫ _t : ℝ in mangoldtLogHaarSharpFutureCell n, c) =
      mangoldtLogHaarAtomMass n * c := by
  rw [MeasureTheory.integral_const, Measure.real, mangoldtLogHaarSharpFutureCell,
    Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal]
  · rw [mangoldtLogHaarSharpFutureCell_length hn]
    simp only [smul_eq_mul]
  · rw [mangoldtLogHaarSharpFutureCell_length hn]
    exact mangoldtLogHaarAtomMass_nonneg n

/-- Sharp increasing-branch transport: capacity theorem turns each Mangoldt sample into a
unit-density integral over the following two lag units. -/
theorem mangoldtLogHaarAtom_mul_le_integral_sharpFutureCell
    (hcap : MangoldtLogHaarCapacity) {n : ℕ} (hn : 2 ≤ n)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hmono : MonotoneOn f
      (Set.Icc (mangoldtLogHaarNode n) (mangoldtLogHaarNode n + 2))) :
    mangoldtLogHaarAtomMass n * f (mangoldtLogHaarNode n) ≤
      ∫ t : ℝ in mangoldtLogHaarSharpFutureCell n, f t := by
  have hsubset := mangoldtLogHaarSharpFutureCell_subset_twoBand hcap hn
  have hfInt : IntegrableOn f (mangoldtLogHaarSharpFutureCell n) := hf.integrableOn_Ioc
  have hcInt : IntegrableOn (fun _ : ℝ => f (mangoldtLogHaarNode n))
      (mangoldtLogHaarSharpFutureCell n) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  rw [← integral_const_on_mangoldtLogHaarSharpFutureCell hn]
  apply MeasureTheory.integral_mono_ae hcInt hfInt
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htBand := hsubset ht
  exact hmono (by simp) ⟨htBand.1.le, htBand.2⟩ htBand.1.le

/-- Sharp decreasing-branch transport over the preceding two lag units. -/
theorem mangoldtLogHaarAtom_mul_le_integral_sharpPastCell
    (hcap : MangoldtLogHaarCapacity) {n : ℕ} (hn : 2 ≤ n)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hanti : AntitoneOn f
      (Set.Icc (mangoldtLogHaarNode n - 2) (mangoldtLogHaarNode n))) :
    mangoldtLogHaarAtomMass n * f (mangoldtLogHaarNode n) ≤
      ∫ t : ℝ in mangoldtLogHaarSharpPastCell n, f t := by
  have hsubset := mangoldtLogHaarSharpPastCell_subset_twoBand hcap hn
  have hfInt : IntegrableOn f (mangoldtLogHaarSharpPastCell n) := hf.integrableOn_Ioc
  have hcInt : IntegrableOn (fun _ : ℝ => f (mangoldtLogHaarNode n))
      (mangoldtLogHaarSharpPastCell n) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  rw [← integral_const_on_mangoldtLogHaarSharpPastCell hn]
  apply MeasureTheory.integral_mono_ae hcInt hfInt
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htBand := hsubset ht
  exact hanti ⟨htBand.1.le, htBand.2⟩ (by simp) htBand.2

/-- Canonical cell obtained by shifting cumulative-mass coordinates behind each atom. -/
def mangoldtLogHaarPastCell (n : ℕ) : Set ℝ :=
  Set.Ioc
    (mangoldtLogHaarMass (n - 1) - mangoldtLogHaarMertensRadius)
    (mangoldtLogHaarMass n - mangoldtLogHaarMertensRadius)

/-- Canonical cell obtained by shifting cumulative-mass coordinates ahead of each atom. -/
def mangoldtLogHaarFutureCell (n : ℕ) : Set ℝ :=
  Set.Ioc
    (mangoldtLogHaarMass (n - 1) + mangoldtLogHaarMertensRadius + 2)
    (mangoldtLogHaarMass n + mangoldtLogHaarMertensRadius + 2)

/-- Both transport cells have exactly the mass of their Mangoldt atom. -/
theorem mangoldtLogHaarPastCell_length
    {n : ℕ} (hn : 2 ≤ n) :
    (mangoldtLogHaarMass n - mangoldtLogHaarMertensRadius) -
        (mangoldtLogHaarMass (n - 1) - mangoldtLogHaarMertensRadius) =
      mangoldtLogHaarAtomMass n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k - 1 = 1 + k by omega,
    show 2 + k = (1 + k) + 1 by omega, mangoldtLogHaarMass_succ]
  ring

theorem mangoldtLogHaarFutureCell_length
    {n : ℕ} (hn : 2 ≤ n) :
    (mangoldtLogHaarMass n + mangoldtLogHaarMertensRadius + 2) -
        (mangoldtLogHaarMass (n - 1) + mangoldtLogHaarMertensRadius + 2) =
      mangoldtLogHaarAtomMass n := by
  linarith [mangoldtLogHaarPastCell_length hn]

/-- Past cell lies behind its atom with uniformly bounded displacement. -/
theorem mangoldtLogHaarPastCell_subset_nodeBand
    {n : ℕ} (hn : 2 ≤ n) :
    mangoldtLogHaarPastCell n ⊆
      Set.Ioc (mangoldtLogHaarNode n - mangoldtLogHaarTransportWidth)
        (mangoldtLogHaarNode n) := by
  have hn1 : 1 ≤ n := hn.trans' (by omega)
  have hpred1 : 1 ≤ n - 1 := by omega
  have hnBand := abs_mangoldtLogHaarMass_sub_node_le hn1
  have hpredBand := abs_mangoldtLogHaarMass_sub_node_le hpred1
  have hnodePred := mangoldtLogHaarNode_sub_two_le_pred hn
  rw [abs_le] at hnBand hpredBand
  intro x hx
  rw [mangoldtLogHaarPastCell, Set.mem_Ioc] at hx
  rw [Set.mem_Ioc]
  constructor
  · rw [mangoldtLogHaarTransportWidth]
    linarith [hpredBand.1]
  · linarith [hnBand.2]

/-- Future cell lies ahead of its atom with the same uniform displacement. -/
theorem mangoldtLogHaarFutureCell_subset_nodeBand
    {n : ℕ} (hn : 2 ≤ n) :
    mangoldtLogHaarFutureCell n ⊆
      Set.Ioc (mangoldtLogHaarNode n)
        (mangoldtLogHaarNode n + mangoldtLogHaarTransportWidth) := by
  have hn1 : 1 ≤ n := hn.trans' (by omega)
  have hpred1 : 1 ≤ n - 1 := by omega
  have hnBand := abs_mangoldtLogHaarMass_sub_node_le hn1
  have hpredBand := abs_mangoldtLogHaarMass_sub_node_le hpred1
  have hnodePred := mangoldtLogHaarNode_sub_two_le_pred hn
  rw [abs_le] at hnBand hpredBand
  intro x hx
  rw [mangoldtLogHaarFutureCell, Set.mem_Ioc] at hx
  rw [Set.mem_Ioc]
  constructor
  · linarith [hpredBand.1]
  · rw [mangoldtLogHaarTransportWidth]
    linarith [hnBand.2]

/-- Past transport cells never compete for Lebesgue capacity. -/
theorem mangoldtLogHaarPastCell_pairwiseDisjoint :
    Set.PairwiseDisjoint Set.univ mangoldtLogHaarPastCell := by
  intro m _ n _ hmn
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · have hle : mangoldtLogHaarMass m ≤ mangoldtLogHaarMass (n - 1) :=
      monotone_mangoldtLogHaarMass (by omega)
    change Disjoint
      (Set.Ioc (mangoldtLogHaarMass (m - 1) - mangoldtLogHaarMertensRadius)
        (mangoldtLogHaarMass m - mangoldtLogHaarMertensRadius))
      (Set.Ioc (mangoldtLogHaarMass (n - 1) - mangoldtLogHaarMertensRadius)
        (mangoldtLogHaarMass n - mangoldtLogHaarMertensRadius))
    exact Set.Ioc_disjoint_Ioc_of_le (sub_le_sub_right hle _)
  · have hle : mangoldtLogHaarMass n ≤ mangoldtLogHaarMass (m - 1) :=
      monotone_mangoldtLogHaarMass (by omega)
    change Disjoint
      (Set.Ioc (mangoldtLogHaarMass (m - 1) - mangoldtLogHaarMertensRadius)
        (mangoldtLogHaarMass m - mangoldtLogHaarMertensRadius))
      (Set.Ioc (mangoldtLogHaarMass (n - 1) - mangoldtLogHaarMertensRadius)
        (mangoldtLogHaarMass n - mangoldtLogHaarMertensRadius))
    exact (Set.Ioc_disjoint_Ioc_of_le (sub_le_sub_right hle _)).symm

/-- Future transport cells never compete for Lebesgue capacity. -/
theorem mangoldtLogHaarFutureCell_pairwiseDisjoint :
    Set.PairwiseDisjoint Set.univ mangoldtLogHaarFutureCell := by
  intro m _ n _ hmn
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · have hle : mangoldtLogHaarMass m ≤ mangoldtLogHaarMass (n - 1) :=
      monotone_mangoldtLogHaarMass (by omega)
    change Disjoint
      (Set.Ioc (mangoldtLogHaarMass (m - 1) + mangoldtLogHaarMertensRadius + 2)
        (mangoldtLogHaarMass m + mangoldtLogHaarMertensRadius + 2))
      (Set.Ioc (mangoldtLogHaarMass (n - 1) + mangoldtLogHaarMertensRadius + 2)
        (mangoldtLogHaarMass n + mangoldtLogHaarMertensRadius + 2))
    exact Set.Ioc_disjoint_Ioc_of_le (by linarith)
  · have hle : mangoldtLogHaarMass n ≤ mangoldtLogHaarMass (m - 1) :=
      monotone_mangoldtLogHaarMass (by omega)
    change Disjoint
      (Set.Ioc (mangoldtLogHaarMass (m - 1) + mangoldtLogHaarMertensRadius + 2)
        (mangoldtLogHaarMass m + mangoldtLogHaarMertensRadius + 2))
      (Set.Ioc (mangoldtLogHaarMass (n - 1) + mangoldtLogHaarMertensRadius + 2)
        (mangoldtLogHaarMass n + mangoldtLogHaarMertensRadius + 2))
    exact (Set.Ioc_disjoint_Ioc_of_le (by linarith)).symm

private theorem integral_const_on_mangoldtLogHaarPastCell
    {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    (∫ _t : ℝ in mangoldtLogHaarPastCell n, c) =
      mangoldtLogHaarAtomMass n * c := by
  rw [MeasureTheory.integral_const, Measure.real, mangoldtLogHaarPastCell,
    Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal]
  · rw [mangoldtLogHaarPastCell_length hn]
    simp only [smul_eq_mul]
  · rw [mangoldtLogHaarPastCell_length hn]
    exact mangoldtLogHaarAtomMass_nonneg n

private theorem integral_const_on_mangoldtLogHaarFutureCell
    {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    (∫ _t : ℝ in mangoldtLogHaarFutureCell n, c) =
      mangoldtLogHaarAtomMass n * c := by
  rw [MeasureTheory.integral_const, Measure.real, mangoldtLogHaarFutureCell,
    Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal]
  · rw [mangoldtLogHaarFutureCell_length hn]
    simp only [smul_eq_mul]
  · rw [mangoldtLogHaarFutureCell_length hn]
    exact mangoldtLogHaarAtomMass_nonneg n

/-- A decreasing lag branch pays its atom from the disjoint past cell. -/
theorem mangoldtLogHaarAtom_mul_le_integral_pastCell
    {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} (hf : Continuous f)
    (hanti : AntitoneOn f
      (Set.Icc (mangoldtLogHaarNode n - mangoldtLogHaarTransportWidth)
        (mangoldtLogHaarNode n))) :
    mangoldtLogHaarAtomMass n * f (mangoldtLogHaarNode n) ≤
      ∫ t : ℝ in mangoldtLogHaarPastCell n, f t := by
  have hsubset := mangoldtLogHaarPastCell_subset_nodeBand hn
  have hfInt : IntegrableOn f (mangoldtLogHaarPastCell n) :=
    hf.integrableOn_Ioc
  have hcInt : IntegrableOn (fun _ : ℝ => f (mangoldtLogHaarNode n))
      (mangoldtLogHaarPastCell n) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  rw [← integral_const_on_mangoldtLogHaarPastCell hn]
  apply MeasureTheory.integral_mono_ae hcInt hfInt
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htBand := hsubset ht
  exact hanti ⟨htBand.1.le, htBand.2⟩
    ⟨by linarith [mangoldtLogHaarTransportWidth_nonneg], le_rfl⟩ htBand.2

/-- An increasing lag branch pays its atom from the disjoint future cell. -/
theorem mangoldtLogHaarAtom_mul_le_integral_futureCell
    {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} (hf : Continuous f)
    (hmono : MonotoneOn f
      (Set.Icc (mangoldtLogHaarNode n)
        (mangoldtLogHaarNode n + mangoldtLogHaarTransportWidth))) :
    mangoldtLogHaarAtomMass n * f (mangoldtLogHaarNode n) ≤
      ∫ t : ℝ in mangoldtLogHaarFutureCell n, f t := by
  have hsubset := mangoldtLogHaarFutureCell_subset_nodeBand hn
  have hfInt : IntegrableOn f (mangoldtLogHaarFutureCell n) :=
    hf.integrableOn_Ioc
  have hcInt : IntegrableOn (fun _ : ℝ => f (mangoldtLogHaarNode n))
      (mangoldtLogHaarFutureCell n) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  rw [← integral_const_on_mangoldtLogHaarFutureCell hn]
  apply MeasureTheory.integral_mono_ae hcInt hfInt
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htBand := hsubset ht
  exact hmono
    ⟨le_rfl, by linarith [mangoldtLogHaarTransportWidth_nonneg]⟩
    ⟨htBand.1.le, htBand.2⟩ htBand.1.le

/-! ## Turning-seam localization and Suzuki connector -/

/-- Every node is either safely left of a turning seam, safely right of it, or lies in the one
bounded layer where the two monotone transports must be spliced. -/
theorem mangoldtLogHaar_turningSeam_trichotomy (n : ℕ) (c : ℝ) :
    mangoldtLogHaarNode n + mangoldtLogHaarTransportWidth ≤ c ∨
      c ≤ mangoldtLogHaarNode n - mangoldtLogHaarTransportWidth ∨
      |mangoldtLogHaarNode n - c| < mangoldtLogHaarTransportWidth := by
  by_cases hleft : mangoldtLogHaarNode n + mangoldtLogHaarTransportWidth ≤ c
  · exact Or.inl hleft
  by_cases hright : c ≤ mangoldtLogHaarNode n - mangoldtLogHaarTransportWidth
  · exact Or.inr (Or.inl hright)
  right
  right
  rw [abs_lt]
  constructor <;> linarith

/-- Safely-left atoms are paid by future cells whenever the profile is increasing up to the
turning point. -/
theorem mangoldtLogHaarAtom_mul_le_integral_futureCell_of_leftOfTurning
    {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hleft : mangoldtLogHaarNode n + mangoldtLogHaarTransportWidth ≤ c)
    (hmono : MonotoneOn f (Set.Iic c)) :
    mangoldtLogHaarAtomMass n * f (mangoldtLogHaarNode n) ≤
      ∫ t : ℝ in mangoldtLogHaarFutureCell n, f t := by
  apply mangoldtLogHaarAtom_mul_le_integral_futureCell hn hf
  intro x hx y hy hxy
  exact hmono
    (by simpa only [Set.mem_Iic] using hx.2.trans hleft)
    (by simpa only [Set.mem_Iic] using hy.2.trans hleft) hxy

/-- Safely-right atoms are paid by past cells whenever the profile is decreasing after the
turning point. -/
theorem mangoldtLogHaarAtom_mul_le_integral_pastCell_of_rightOfTurning
    {n : ℕ} (hn : 2 ≤ n) {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hright : c ≤ mangoldtLogHaarNode n - mangoldtLogHaarTransportWidth)
    (hanti : AntitoneOn f (Set.Ici c)) :
    mangoldtLogHaarAtomMass n * f (mangoldtLogHaarNode n) ≤
      ∫ t : ℝ in mangoldtLogHaarPastCell n, f t := by
  apply mangoldtLogHaarAtom_mul_le_integral_pastCell hn hf
  intro x hx y hy hxy
  exact hanti
    (by simpa only [Set.mem_Ici] using hright.trans hx.1)
    (by simpa only [Set.mem_Ici] using hright.trans hy.1) hxy

/-- The log-Haar atom paired with Suzuki's sampled positive channel is literally twice the
prime-wall cell already used by the RH connector. -/
theorem mangoldtLogHaarAtom_mul_positiveArchSample_eq_two_primeCell
    {n : ℕ} (hn : 0 < n) (L a : ℝ) :
    mangoldtLogHaarAtomMass n *
        suzukiRectangularPositiveArchSampleChannel L a (mangoldtLogHaarNode n) =
      2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        rectangularTwoEdgeAutocorrelation L a (Real.log n)) := by
  rw [mangoldtLogHaarAtomMass, mangoldtLogHaarNode]
  calc
    2 * ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          suzukiRectangularPositiveArchSampleChannel L a (2 * Real.log n) =
        2 * (ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          suzukiRectangularPositiveArchSampleChannel L a (2 * Real.log n)) := by ring
    _ = _ := by rw [vonMangoldt_primeCell_eq_positiveArchSample hn L a]

/-- Sharp two-unit Suzuki transport on an increasing branch. -/
theorem two_vonMangoldt_primeCell_le_integral_sharpFutureCell
    (hcap : MangoldtLogHaarCapacity) {n : ℕ} (hn : 2 ≤ n) (L a : ℝ)
    (hmono : MonotoneOn (suzukiRectangularPositiveArchSampleChannel L a)
      (Set.Icc (mangoldtLogHaarNode n) (mangoldtLogHaarNode n + 2))) :
    2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        rectangularTwoEdgeAutocorrelation L a (Real.log n)) ≤
      ∫ t : ℝ in mangoldtLogHaarSharpFutureCell n,
        suzukiRectangularPositiveArchSampleChannel L a t := by
  rw [← mangoldtLogHaarAtom_mul_positiveArchSample_eq_two_primeCell (by omega) L a]
  apply mangoldtLogHaarAtom_mul_le_integral_sharpFutureCell hcap hn
  · change Continuous (fun t : ℝ => Real.exp (t / 4) *
      rectangularTwoEdgeAutocorrelation L a (t / 2))
    exact (Real.continuous_exp.comp (continuous_id.div_const 4)).mul
      ((continuous_rectangularTwoEdgeAutocorrelation L a).comp
        (continuous_id.div_const 2))
  · exact hmono

/-- Sharp two-unit Suzuki transport on a decreasing branch. -/
theorem two_vonMangoldt_primeCell_le_integral_sharpPastCell
    (hcap : MangoldtLogHaarCapacity) {n : ℕ} (hn : 2 ≤ n) (L a : ℝ)
    (hanti : AntitoneOn (suzukiRectangularPositiveArchSampleChannel L a)
      (Set.Icc (mangoldtLogHaarNode n - 2) (mangoldtLogHaarNode n))) :
    2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        rectangularTwoEdgeAutocorrelation L a (Real.log n)) ≤
      ∫ t : ℝ in mangoldtLogHaarSharpPastCell n,
        suzukiRectangularPositiveArchSampleChannel L a t := by
  rw [← mangoldtLogHaarAtom_mul_positiveArchSample_eq_two_primeCell (by omega) L a]
  apply mangoldtLogHaarAtom_mul_le_integral_sharpPastCell hcap hn
  · change Continuous (fun t : ℝ => Real.exp (t / 4) *
      rectangularTwoEdgeAutocorrelation L a (t / 2))
    exact (Real.continuous_exp.comp (continuous_id.div_const 4)).mul
      ((continuous_rectangularTwoEdgeAutocorrelation L a).comp
        (continuous_id.div_const 2))
  · exact hanti

/-- Concrete Suzuki consumer on an increasing node band. -/
theorem two_vonMangoldt_primeCell_le_integral_futureCell
    {n : ℕ} (hn : 2 ≤ n) (L a : ℝ)
    (hmono : MonotoneOn (suzukiRectangularPositiveArchSampleChannel L a)
      (Set.Icc (mangoldtLogHaarNode n)
        (mangoldtLogHaarNode n + mangoldtLogHaarTransportWidth))) :
    2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        rectangularTwoEdgeAutocorrelation L a (Real.log n)) ≤
      ∫ t : ℝ in mangoldtLogHaarFutureCell n,
        suzukiRectangularPositiveArchSampleChannel L a t := by
  rw [← mangoldtLogHaarAtom_mul_positiveArchSample_eq_two_primeCell (by omega) L a]
  apply mangoldtLogHaarAtom_mul_le_integral_futureCell hn
  · change Continuous (fun t : ℝ => Real.exp (t / 4) *
      rectangularTwoEdgeAutocorrelation L a (t / 2))
    exact (Real.continuous_exp.comp (continuous_id.div_const 4)).mul
      ((continuous_rectangularTwoEdgeAutocorrelation L a).comp
        (continuous_id.div_const 2))
  · exact hmono

/-- Concrete Suzuki consumer on a decreasing node band. -/
theorem two_vonMangoldt_primeCell_le_integral_pastCell
    {n : ℕ} (hn : 2 ≤ n) (L a : ℝ)
    (hanti : AntitoneOn (suzukiRectangularPositiveArchSampleChannel L a)
      (Set.Icc (mangoldtLogHaarNode n - mangoldtLogHaarTransportWidth)
        (mangoldtLogHaarNode n))) :
    2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        rectangularTwoEdgeAutocorrelation L a (Real.log n)) ≤
      ∫ t : ℝ in mangoldtLogHaarPastCell n,
        suzukiRectangularPositiveArchSampleChannel L a t := by
  rw [← mangoldtLogHaarAtom_mul_positiveArchSample_eq_two_primeCell (by omega) L a]
  apply mangoldtLogHaarAtom_mul_le_integral_pastCell hn
  · change Continuous (fun t : ℝ => Real.exp (t / 4) *
      rectangularTwoEdgeAutocorrelation L a (t / 2))
    exact (Real.continuous_exp.comp (continuous_id.div_const 4)).mul
      ((continuous_rectangularTwoEdgeAutocorrelation L a).comp
        (continuous_id.div_const 2))
  · exact hanti

end RHTower
