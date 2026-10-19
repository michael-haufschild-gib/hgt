import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonGramMatrixAndRadicalProjection

/-!
# Valuation sampling of Fermi jumps

For Möbius-twisted coefficients, an odd Fermi boundary reads the negative sieve
value there. A boundary divisible by four reads the sieve value at its half.
The latter uses valuation saturation, so it holds beyond every horizon.
At a fixed horizon, this reading rule holds exactly when all admitted
coefficients divisible by four vanish. Odd prime squares cause no obstruction.

These two disjoint schedules recover all positive sieve values. In the physical
reciprocal-cell norm their energy lies between one quarter and one times the
sieve energy. The exact positive slack records the cost of doubling even cells.
-/

open Finset
open RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Jump across the reciprocal-cell boundary indexed by `n`. -/
def fermiBoundaryJump (N : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  fermiCellResponse N c n - fermiCellResponse N c (n - 1)

/-- Reciprocal-cell sieve energy on selected adjacent positive pairs. -/
def sievePairedPronicEnergy (N : ℕ) (c : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ m ∈ S, (sieveSeq N c (2 * m + 1) ^ 2 / (pronicSeq (2 * m + 1) : ℝ) +
    sieveSeq N c (2 * m + 2) ^ 2 / (pronicSeq (2 * m + 2) : ℝ))

/-- Physical jump energy on odd boundaries and their saturated even partners. -/
def fermiSelectedPronicEnergy (N : ℕ) (c : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ m ∈ S, (fermiBoundaryJump N c (2 * m + 1) ^ 2 /
      (pronicSeq (2 * m + 1) : ℝ) +
    fermiBoundaryJump N c (4 * m + 4) ^ 2 / (pronicSeq (4 * m + 4) : ℝ))

private theorem moebius_twist_squarefree_support (w : ℕ → ℝ) (d : ℕ)
    (hd : ¬ Squarefree d) : moebiusReal d * w d = 0 := by
  rw [moebiusReal_eq_zero_of_not_squarefree d hd, zero_mul]

/-- Odd boundary sampling needs no support or horizon restriction. -/
theorem fermiBoundaryJump_odd (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    fermiBoundaryJump N c (2 * m + 1) = -sieveSeq N c (2 * m + 1) := by
  unfold fermiBoundaryJump
  rw [show 2 * m + 1 - 1 = 2 * m by omega]
  exact fermiCellResponse_two_mul_add_one_sub_two_mul N c m

/-- An even boundary compares its parent with the full-scale sieve reading. -/
theorem fermiBoundaryJump_even (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    fermiBoundaryJump N c (2 * m + 2) =
      2 * sieveSeq N c (m + 1) - sieveSeq N c (2 * m + 2) := by
  unfold fermiBoundaryJump
  rw [show 2 * m + 2 - 1 = 2 * m + 1 by omega]
  exact fermiCellResponse_two_mul_add_two_sub_two_mul_add_one N c m

private theorem dvd_double_even_iff_of_not_four_dvd {d m : ℕ} (h4 : ¬4 ∣ d) :
    d ∣ 4 * m + 4 ↔ d ∣ 2 * m + 2 := by
  constructor
  · intro hd
    by_cases h2 : 2 ∣ d
    · obtain ⟨a, rfl⟩ := h2
      have ha2 : ¬2 ∣ a := by
        rintro ⟨b, rfl⟩
        exact h4 ⟨b, by ring⟩
      have ha : a ∣ 2 * (m + 1) := by
        obtain ⟨b, hb⟩ := hd
        exact ⟨b, by nlinarith [hb]⟩
      have hc : a.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr ha2).symm
      obtain ⟨b, hb⟩ := hc.dvd_mul_left.mp ha
      exact ⟨b, by nlinarith [hb]⟩
    · have hc : d.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
      apply hc.dvd_mul_left.mp
      convert hd using 1
      omega
  · rintro ⟨b, hb⟩
    exact ⟨2 * b, by nlinarith [hb]⟩

/-- The sampling error is exactly the sieve's remaining dyadic valuation increment. -/
theorem fermiBoundaryJump_four_sub_eq_sieve_difference (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    fermiBoundaryJump N c (4 * m + 4) - sieveSeq N c (2 * m + 2) =
      sieveSeq N c (2 * m + 2) - sieveSeq N c (4 * m + 4) := by
  have h := fermiBoundaryJump_even N c (2 * m + 1)
  rw [show 2 * (2 * m + 1) + 2 = 4 * m + 4 by omega,
    show 2 * m + 1 + 1 = 2 * m + 2 by omega] at h
  linarith

/-- Exact recovery at one horizon characterizes its four-divisible coefficients. -/
theorem fermiBoundaryJump_exact_recovery_iff (N : ℕ) (c : ℕ → ℝ) :
    (∀ m, fermiBoundaryJump N c (4 * m + 4) = sieveSeq N c (2 * m + 2)) ↔
      ∀ m, 4 * m + 4 ≤ N → c (4 * m + 4) = 0 := by
  constructor
  · intro hrec m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmN
      have hsum : sieveSeq N c (4 * m + 4) - sieveSeq N c (2 * m + 2) =
          c (4 * m + 4) := by
        unfold sieveSeq
        rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single (4 * m + 4)]
        · have hn : ¬4 * m + 4 ∣ 2 * m + 2 := by
            intro hd
            have := Nat.le_of_dvd (by omega : 0 < 2 * m + 2) hd
            omega
          simp only [dvd_refl, if_true, if_neg hn, sub_zero]
        · intro d hd hne
          by_cases hl : d ∣ 4 * m + 4
          · by_cases hs : d ∣ 2 * m + 2
            · simp only [if_pos hl, if_pos hs, sub_self]
            · have h4 : 4 ∣ d := by
                by_contra h4
                exact hs ((dvd_double_even_iff_of_not_four_dvd h4).mp hl)
              obtain ⟨a, ha⟩ := h4
              have hdpos := (Finset.mem_Icc.mp hd).1
              have hdN := (Finset.mem_Icc.mp hd).2
              have hdle := Nat.le_of_dvd (by omega : 0 < 4 * m + 4) hl
              have hda : d = 4 * (a - 1) + 4 := by omega
              have hsmall : a - 1 < m := by omega
              have hz := ih (a - 1) hsmall (by omega : 4 * (a - 1) + 4 ≤ N)
              rw [← hda] at hz
              simp only [if_pos hl, if_neg hs, hz, sub_zero]
          · have hs : ¬d ∣ 2 * m + 2 := by
              rintro ⟨b, hb⟩
              exact hl ⟨2 * b, by nlinarith [hb]⟩
            simp only [if_neg hl, if_neg hs, sub_self]
        · intro hn
          exact (hn (Finset.mem_Icc.mpr ⟨by omega, hmN⟩)).elim
      have herr := fermiBoundaryJump_four_sub_eq_sieve_difference N c m
      rw [hrec m] at herr
      linarith
  · intro hc m
    have hs : sieveSeq N c (4 * m + 4) = sieveSeq N c (2 * m + 2) := by
      unfold sieveSeq
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h4 : 4 ∣ d
      · obtain ⟨a, ha⟩ := h4
        have hdpos := (Finset.mem_Icc.mp hd).1
        have hdN := (Finset.mem_Icc.mp hd).2
        have hda : d = 4 * (a - 1) + 4 := by omega
        have hz := hc (a - 1) (by omega : 4 * (a - 1) + 4 ≤ N)
        rw [← hda] at hz
        rw [hz]
        split_ifs <;> rfl
      · simp only [dvd_double_even_iff_of_not_four_dvd h4]
    have herr := fermiBoundaryJump_four_sub_eq_sieve_difference N c m
    rw [hs] at herr
    linarith

/-- The horizon-independent exact class permits every coefficient away from multiples of four. -/
theorem fermiBoundaryJump_all_horizons_exact_recovery_iff (c : ℕ → ℝ) :
    (∀ N m, fermiBoundaryJump N c (4 * m + 4) = sieveSeq N c (2 * m + 2)) ↔
      ∀ m, c (4 * m + 4) = 0 := by
  constructor
  · intro h m
    exact (fermiBoundaryJump_exact_recovery_iff (4 * m + 4) c).mp (h _) m (by omega)
  · intro h N
    exact (fermiBoundaryJump_exact_recovery_iff N c).mpr (fun m _ => h m)

/-- Delete exactly the coefficients obstructing saturation at even sieve arguments. -/
def fermiFourFreeWeight (w : ℕ → ℝ) (d : ℕ) : ℝ :=
  if 4 ∣ d then 0 else w d

/-- The canonical saturated coefficient projection has exact trans-horizon readings. -/
theorem fermiBoundaryJump_four_fourFreeWeight (N : ℕ) (w : ℕ → ℝ) (m : ℕ) :
    fermiBoundaryJump N (fermiFourFreeWeight w) (4 * m + 4) =
      sieveSeq N (fermiFourFreeWeight w) (2 * m + 2) := by
  apply (fermiBoundaryJump_exact_recovery_iff N (fermiFourFreeWeight w)).mpr
  intro k _
  simp only [fermiFourFreeWeight, show 4 ∣ 4 * k + 4 by omega, if_true]

/-- Squarefree saturation turns every fourth boundary into a half-scale reading. -/
theorem fermiBoundaryJump_four_mul_moebius_twist (N : ℕ) (w : ℕ → ℝ) (m : ℕ) :
    fermiBoundaryJump N (fun d => moebiusReal d * w d) (4 * m + 4) =
      sieveSeq N (fun d => moebiusReal d * w d) (2 * m + 2) := by
  have h := fermiCellResponse_two_mul_add_two_sub_two_mul_add_one
    N (fun d => moebiusReal d * w d) (2 * m + 1)
  have hs := sieveSeq_mul_of_dvd_of_squarefree_support N
    (moebius_twist_squarefree_support w) (d := 2) (k := 2 * m + 2)
    (by omega : 2 ∣ 2 * m + 2)
  have heq : 2 * (2 * m + 2) = 4 * m + 4 := by omega
  rw [heq] at hs
  unfold fermiBoundaryJump
  have hi : 4 * m + 4 - 1 = 2 * (2 * m + 1) + 1 := by omega
  rw [hi, show 4 * m + 4 = 2 * (2 * m + 1) + 2 by omega, h]
  rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega,
    show 2 * (2 * m + 1) + 2 = 4 * m + 4 by omega, hs]
  ring

/-- The complete positive sieve sequence is read with coefficients of magnitude one. -/
theorem fermiBoundaryJump_pair_recovery (N : ℕ) (w : ℕ → ℝ) (m : ℕ) :
    (-fermiBoundaryJump N (fun d => moebiusReal d * w d) (2 * m + 1),
      fermiBoundaryJump N (fun d => moebiusReal d * w d) (4 * m + 4)) =
    (sieveSeq N (fun d => moebiusReal d * w d) (2 * m + 1),
      sieveSeq N (fun d => moebiusReal d * w d) (2 * m + 2)) := by
  rw [fermiBoundaryJump_odd, neg_neg, fermiBoundaryJump_four_mul_moebius_twist]

private theorem pronic_doubling_slack (x a : ℝ) (hx : 0 < x) :
    4 * (a ^ 2 / ((2 * x) * (2 * x + 1))) - a ^ 2 / (x * (x + 1)) =
      a ^ 2 / (x * (x + 1) * (2 * x + 1)) := by
  have h1 : x ≠ 0 := ne_of_gt hx
  have h2 : x + 1 ≠ 0 := by positivity
  have h3 : 2 * x + 1 ≠ 0 := by positivity
  field_simp [h1, h2, h3]
  ring

private theorem pronic_doubling_le (x a : ℝ) (hx : 0 < x) :
    a ^ 2 / ((2 * x) * (2 * x + 1)) ≤ a ^ 2 / (x * (x + 1)) := by
  apply div_le_div_of_nonneg_left (sq_nonneg a) (by positivity)
  nlinarith

private theorem pronic_sampling_slack (N : ℕ) (c : ℕ → ℝ) (S : Finset ℕ)
    (hrec : ∀ m, fermiBoundaryJump N c (4 * m + 4) = sieveSeq N c (2 * m + 2)) :
    4 * fermiSelectedPronicEnergy N c S - sievePairedPronicEnergy N c S =
    ∑ m ∈ S,
      (3 * sieveSeq N c (2 * m + 1) ^ 2 /
        (pronicSeq (2 * m + 1) : ℝ) +
      sieveSeq N c (2 * m + 2) ^ 2 /
        ((pronicSeq (2 * m + 2) : ℝ) * (4 * (m : ℝ) + 5))) := by
  unfold fermiSelectedPronicEnergy sievePairedPronicEnergy
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [fermiBoundaryJump_odd, neg_sq, hrec]
  have h := pronic_doubling_slack (2 * (m : ℝ) + 2)
    (sieveSeq N c (2 * m + 2)) (by positivity)
  simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at *
  convert congrArg (fun z : ℝ =>
    3 * sieveSeq N c (2 * m + 1) ^ 2 /
      ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 1 + 1)) + z) h using 1 <;> ring

private theorem pronic_sampling_inverse (N : ℕ) (c : ℕ → ℝ) (S : Finset ℕ)
    (hrec : ∀ m, fermiBoundaryJump N c (4 * m + 4) = sieveSeq N c (2 * m + 2)) :
    sievePairedPronicEnergy N c S ≤ 4 * fermiSelectedPronicEnergy N c S := by
  have h := pronic_sampling_slack N c S hrec
  have hn : 0 ≤ ∑ m ∈ S,
      (3 * sieveSeq N c (2 * m + 1) ^ 2 /
        (pronicSeq (2 * m + 1) : ℝ) +
      sieveSeq N c (2 * m + 2) ^ 2 /
        ((pronicSeq (2 * m + 2) : ℝ) * (4 * (m : ℝ) + 5))) := by
    apply Finset.sum_nonneg
    intro m _
    positivity
  linarith

private theorem pronic_sampling_forward (N : ℕ) (c : ℕ → ℝ) (S : Finset ℕ)
    (hrec : ∀ m, fermiBoundaryJump N c (4 * m + 4) = sieveSeq N c (2 * m + 2)) :
    fermiSelectedPronicEnergy N c S ≤ sievePairedPronicEnergy N c S := by
  unfold fermiSelectedPronicEnergy sievePairedPronicEnergy
  apply Finset.sum_le_sum
  intro m _
  rw [fermiBoundaryJump_odd, neg_sq, hrec]
  have h := pronic_doubling_le (2 * (m : ℝ) + 2)
    (sieveSeq N c (2 * m + 2)) (by positivity)
  have h' : sieveSeq N c (2 * m + 2) ^ 2 / (pronicSeq (4 * m + 4) : ℝ) ≤
      sieveSeq N c (2 * m + 2) ^ 2 / (pronicSeq (2 * m + 2) : ℝ) := by
    simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    convert h using 1 <;> ring
  linarith

/-- Exact observation slack; the bound loses no unrecorded signed term. -/
theorem four_mul_fermiSelectedPronicEnergy_sub_sievePaired_eq
    (N : ℕ) (w : ℕ → ℝ) (S : Finset ℕ) :
    4 * fermiSelectedPronicEnergy N (fun d => moebiusReal d * w d) S -
      sievePairedPronicEnergy N (fun d => moebiusReal d * w d) S =
    ∑ m ∈ S,
      (3 * sieveSeq N (fun d => moebiusReal d * w d) (2 * m + 1) ^ 2 /
        (pronicSeq (2 * m + 1) : ℝ) +
      sieveSeq N (fun d => moebiusReal d * w d) (2 * m + 2) ^ 2 /
        ((pronicSeq (2 * m + 2) : ℝ) * (4 * (m : ℝ) + 5))) :=
  pronic_sampling_slack N _ S (fermiBoundaryJump_four_mul_moebius_twist N w)

/-- Uniform critical-weight observability at every horizon, including trans-horizon cells. -/
theorem sievePairedPronicEnergy_le_four_mul_fermiSelected
    (N : ℕ) (w : ℕ → ℝ) (S : Finset ℕ) :
    sievePairedPronicEnergy N (fun d => moebiusReal d * w d) S ≤
      4 * fermiSelectedPronicEnergy N (fun d => moebiusReal d * w d) S :=
  pronic_sampling_inverse N _ S (fermiBoundaryJump_four_mul_moebius_twist N w)

/-- Sampling never increases the reciprocal-cell energy of the recovered sieve. -/
theorem fermiSelectedPronicEnergy_le_sievePaired
    (N : ℕ) (w : ℕ → ℝ) (S : Finset ℕ) :
    fermiSelectedPronicEnergy N (fun d => moebiusReal d * w d) S ≤
      sievePairedPronicEnergy N (fun d => moebiusReal d * w d) S :=
  pronic_sampling_forward N _ S (fermiBoundaryJump_four_mul_moebius_twist N w)

/-- The same physical energy control holds on the full exact-recovery class. -/
theorem fermiFourFree_pronic_energy_bounds (N : ℕ) (w : ℕ → ℝ) (S : Finset ℕ) :
    fermiSelectedPronicEnergy N (fermiFourFreeWeight w) S ≤
        sievePairedPronicEnergy N (fermiFourFreeWeight w) S ∧
      sievePairedPronicEnergy N (fermiFourFreeWeight w) S ≤
        4 * fermiSelectedPronicEnergy N (fermiFourFreeWeight w) S :=
  ⟨pronic_sampling_forward N _ S (fermiBoundaryJump_four_fourFreeWeight N w),
    pronic_sampling_inverse N _ S (fermiBoundaryJump_four_fourFreeWeight N w)⟩

private theorem sievePairedPronicEnergy_nonneg (N : ℕ) (c : ℕ → ℝ) (S : Finset ℕ) :
    0 ≤ sievePairedPronicEnergy N c S := by
  unfold sievePairedPronicEnergy
  apply Finset.sum_nonneg
  intro m _
  positivity

private theorem fermiSelectedPronicEnergy_nonneg (N : ℕ) (c : ℕ → ℝ) (S : Finset ℕ) :
    0 ≤ fermiSelectedPronicEnergy N c S := by
  unfold fermiSelectedPronicEnergy
  apply Finset.sum_nonneg
  intro m _
  positivity

private theorem sieveSeq_two_moebius_twist (w : ℕ → ℝ) (k : ℕ) :
    sieveSeq 2 (fun d => moebiusReal d * w d) k =
      w 1 - if 2 ∣ k then w 2 else 0 := by
  have hI : Finset.Icc 1 2 = {1, 2} := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  simp only [sieveSeq, hI, Finset.sum_filter]
  simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  split_ifs <;> ring

private theorem even_twist_energies (m : ℕ) :
    sievePairedPronicEnergy 2
        (fun d => moebiusReal d * (if d = 2 then -1 else 0)) {m} =
      1 / ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ∧
    fermiSelectedPronicEnergy 2
        (fun d => moebiusReal d * (if d = 2 then -1 else 0)) {m} =
      1 / ((4 * (m : ℝ) + 4) * (4 * (m : ℝ) + 5)) := by
  have ho : ¬ 2 ∣ 2 * m + 1 := by omega
  have he : 2 ∣ 2 * m + 2 := by omega
  constructor <;>
    simp only [sievePairedPronicEnergy, fermiSelectedPronicEnergy, Finset.sum_singleton,
      fermiBoundaryJump_odd, fermiBoundaryJump_four_mul_moebius_twist,
      sieveSeq_two_moebius_twist, ho, he, if_false, if_true]
  all_goals
    norm_num [pronicSeq]
    ring_nf
    simp

private theorem odd_twist_energies :
    sievePairedPronicEnergy 2 (fun d => moebiusReal d * 1) {0} = 1 / 2 ∧
      fermiSelectedPronicEnergy 2 (fun d => moebiusReal d * 1) {0} = 1 / 2 := by
  constructor <;>
    simp only [sievePairedPronicEnergy, fermiSelectedPronicEnergy, Finset.sum_singleton,
      fermiBoundaryJump_odd, fermiBoundaryJump_four_mul_moebius_twist,
      sieveSeq_two_moebius_twist]
  all_goals norm_num [pronicSeq]

/-- Four is the exact universal inverse constant, already forced at horizon two. -/
theorem fermi_valuation_inverse_constant_iff (C : ℝ) :
    (∀ (N : ℕ) (w : ℕ → ℝ) (S : Finset ℕ),
      sievePairedPronicEnergy N (fun d => moebiusReal d * w d) S ≤
        C * fermiSelectedPronicEnergy N (fun d => moebiusReal d * w d) S) ↔ 4 ≤ C := by
  constructor
  · intro hC
    by_contra hnot
    have hpos : 0 < 4 - C := by linarith
    obtain ⟨m, hm⟩ := exists_nat_gt ((C - 2) / (4 - C))
    have hmC : C - 2 < (m : ℝ) * (4 - C) := (div_lt_iff₀ hpos).mp hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have he : 0 < 2 * (m : ℝ) + 2 := by positivity
    have heC : 0 < (4 - C) * (2 * (m : ℝ) + 2) + 2 - C := by nlinarith
    have h := hC 2 (fun d => if d = 2 then -1 else 0) {m}
    rw [(even_twist_energies m).1, (even_twist_energies m).2] at h
    have hp : 0 < (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) := by positivity
    have hq : 0 < (4 * (m : ℝ) + 4) * (4 * (m : ℝ) + 5) := by positivity
    have h' :
        1 / ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ≤
          C / ((4 * (m : ℝ) + 4) * (4 * (m : ℝ) + 5)) := by
      convert h using 1
      ring
    have hcross := (div_le_div_iff₀ hp hq).mp h'
    nlinarith [mul_pos he heC]
  · intro hC N w S
    have h := sievePairedPronicEnergy_le_four_mul_fermiSelected N w S
    have hn := fermiSelectedPronicEnergy_nonneg N (fun d => moebiusReal d * w d) S
    nlinarith

/-- One is the exact universal forward constant; the odd-indicator sieve attains it. -/
theorem fermi_valuation_forward_constant_iff (C : ℝ) :
    (∀ (N : ℕ) (w : ℕ → ℝ) (S : Finset ℕ),
      fermiSelectedPronicEnergy N (fun d => moebiusReal d * w d) S ≤
        C * sievePairedPronicEnergy N (fun d => moebiusReal d * w d) S) ↔ 1 ≤ C := by
  constructor
  · intro hC
    have h := hC 2 (fun _ => 1) {0}
    rw [odd_twist_energies.1, odd_twist_energies.2] at h
    linarith
  · intro hC N w S
    have h := fermiSelectedPronicEnergy_le_sievePaired N w S
    have hn := sievePairedPronicEnergy_nonneg N (fun d => moebiusReal d * w d) S
    nlinarith

/-- A prime-square coefficient aliases the selected readings while retaining positive sieve energy. -/
theorem fermi_valuation_prime_square_alias :
    let c : ℕ → ℝ := fun d => if d = 2 ∨ d = 4 then 1 else 0
    fermiSelectedPronicEnergy 4 c {0} = 0 ∧
      sievePairedPronicEnergy 4 c {0} = 1 / 6 := by
  dsimp
  let c : ℕ → ℝ := fun d => if d = 2 ∨ d = 4 then 1 else 0
  have hI : Finset.Icc 1 4 = {1, 2, 3, 4} := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have h1 : sieveSeq 4 c 1 = 0 := by
    norm_num [sieveSeq, hI, c, Finset.filter_insert, Finset.filter_singleton]
  have h2 : sieveSeq 4 c 2 = 1 := by
    norm_num [sieveSeq, hI, c, Finset.filter_insert, Finset.filter_singleton]
  have h4 : sieveSeq 4 c 4 = 2 := by
    norm_num [sieveSeq, hI, c, Finset.filter_insert, Finset.filter_singleton]
  have hj1 := fermiBoundaryJump_odd 4 c 0
  have hj4 := fermiBoundaryJump_even 4 c 1
  norm_num [h1, h2, h4] at hj1 hj4
  change fermiSelectedPronicEnergy 4 c {0} = 0 ∧ sievePairedPronicEnergy 4 c {0} = 1 / 6
  constructor <;>
    norm_num [fermiSelectedPronicEnergy, sievePairedPronicEnergy, h1, h2, hj1, hj4, pronicSeq]

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
