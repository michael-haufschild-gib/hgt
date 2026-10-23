import GaloisForLFunctions.BezoutValuationIncidence.CyclotomicIncidenceRecurrenceAndArbitraryPhaseObservability
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.ChineseRemainder

/-!
# The arbitrary-phase observability horizon is superlinear

At every phase the response of a level-`N` row vanishes on `Φ(N) ≍ N²` consecutive integers only
for the zero row (`sieveSeq_window_eq_zero_iff`), while at common returns windows of length `2N − 3`
already observe the row. This module shows that **no linear horizon works at arbitrary phase**:
for every `m`, once `N ≥ (m + 2)(2^{m+1})!(1 + 2^{m+1})`, some nonzero row has zero response on
`m·N` consecutive integers (`exists_zero_response_window`, `not_exists_linear_observability_horizon`).

The witness is an **alternating grid** of `2^m` moduli just below a cutoff `D`. With weights
`b_j = M 2^j` (`j < m`) and `M = (2^m)!`, a subset `S ⊆ [0, m)` gets the modulus
`d_S = D − Σ_{j∈S} b_j` and the offset `ι_S = Σ_{j∈S} j b_j`; the row is `Σ_S (−1)^{|S|} δ_{d_S}`.

* Inside a window of length `m(D − M 2^m)` the modulus `d_S` hits exactly the `m` positions
  `A + ι_S + J d_S = A + J D + Σ_{j∈S} (j − J) b_j`, one in each block `J < m`.
* In block `J` the weight of `j = J` vanishes, so toggling `J ∈ S` preserves the position and flips
  the sign: every block cancels (`sum_powerset_neg_one_pow_mul_eq_zero`). This is the identity
  `∏_{j<m} (1 − X^{(j−J) b_j}) = 0`.
* The phase `A` exists because the moduli are pairwise coprime: their differences are `M` times
  numbers below `2^m`, all dividing `M`, while `D` is coprime to `M` (`gridModulus_coprime`).

So arbitrary-phase observability is not an incidence-linear law: grid relations among the
divisibility columns of the top moduli survive on every window of bounded multiple of `N`. The
quadratic recurrence horizon `Φ(N)` and the growth `≫ N` per fixed `m` bracket the true horizon.
-/

open Finset

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- Alternating sums over the subsets of `T` vanish as soon as one weight is zero. -/
theorem sum_powerset_neg_one_pow_mul_eq_zero {T : Finset ℕ} {J : ℕ} (hJ : J ∈ T) (w : ℕ → ℤ)
    (hw : w J = 0) (g : ℤ → ℝ) :
    ∑ S ∈ T.powerset, (-1 : ℝ) ^ S.card * g (∑ j ∈ S, w j) = 0 := by
  rw [← insert_erase hJ, sum_powerset_insert (notMem_erase J T), ← sum_add_distrib]
  refine sum_eq_zero fun S hS => ?_
  have hJS : J ∉ S := fun h => notMem_erase J T (mem_powerset.mp hS h)
  rw [card_insert_of_notMem hJS, sum_insert hJS, hw, zero_add, pow_succ]
  ring

/-- The binary slope `σ_S = Σ_{j∈S} 2^j` of a set of block indices. -/
def binarySlope (S : Finset ℕ) : ℕ := ∑ j ∈ S, 2 ^ j

/-- The grid modulus `d_S = D − M σ_S`. -/
def gridModulus (D M : ℕ) (S : Finset ℕ) : ℕ := D - M * binarySlope S

/-- The grid offset `ι_S = Σ_{j∈S} j · M 2^j`, the first hit of `d_S` after the phase. -/
def gridOffset (M : ℕ) (S : Finset ℕ) : ℕ := ∑ j ∈ S, j * (M * 2 ^ j)

/-- The alternating grid row: sign `(−1)^{|S|}` on the modulus `d_S` of each `S ⊆ [0, m)`. -/
def gridRow (m D M : ℕ) (d : ℕ) : ℝ :=
  ∑ S ∈ (range m).powerset, if d = gridModulus D M S then (-1 : ℝ) ^ S.card else 0

theorem binarySlope_lt {m : ℕ} {S : Finset ℕ} (hS : S ⊆ range m) : binarySlope S < 2 ^ m :=
  Nat.geomSum_lt le_rfl fun _ hk => mem_range.mp (hS hk)

theorem gridOffset_le {m M : ℕ} {S : Finset ℕ} (hS : S ⊆ range m) :
    gridOffset M S ≤ m * (M * 2 ^ m) := by
  calc gridOffset M S ≤ ∑ j ∈ S, m * (M * 2 ^ j) :=
        sum_le_sum fun j hj => Nat.mul_le_mul_right _ (mem_range.mp (hS hj)).le
    _ = m * (M * binarySlope S) := by rw [binarySlope, mul_sum, mul_sum]
    _ ≤ m * (M * 2 ^ m) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (binarySlope_lt hS).le)

/-- Two moduli `D − Mσ`, `D − Mσ'` with `σ < σ' < 2^m` are coprime when every positive integer
below `2^m` divides `M` and `D` is coprime to `M`. -/
theorem coprime_sub_mul_of_lt {m D M σ σ' : ℕ} (hM : ∀ q, 0 < q → q < 2 ^ m → q ∣ M)
    (hD : Nat.Coprime D M) (hlt : σ < σ') (hσ' : σ' < 2 ^ m) (hle : M * σ' ≤ D) :
    Nat.Coprime (D - M * σ) (D - M * σ') := by
  have hle' : M * σ ≤ M * σ' := Nat.mul_le_mul_left _ hlt.le
  apply Nat.coprime_of_dvd
  intro p hp h1 h2
  have hdiff : (D - M * σ) - (D - M * σ') = M * (σ' - σ) := by
    rw [Nat.mul_sub]; omega
  have hpM : p ∣ M := by
    have h := Nat.dvd_sub h1 h2
    rw [hdiff] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact h
    · exact h.trans (hM _ (by omega) (by omega))
  have hpD : p ∣ D := by
    have h := Nat.dvd_add h1 (Dvd.dvd.mul_right hpM σ)
    rwa [Nat.sub_add_cancel (hle'.trans hle)] at h
  exact hp.not_dvd_one (hD.gcd_eq_one ▸ Nat.dvd_gcd hpD hpM)

/-- **The grid moduli are pairwise coprime.** -/
theorem gridModulus_coprime {m D M : ℕ} (hM : ∀ q, 0 < q → q < 2 ^ m → q ∣ M)
    (hD : Nat.Coprime D M) (hDM : M * 2 ^ m ≤ D) {S S' : Finset ℕ} (hS : S ⊆ range m)
    (hS' : S' ⊆ range m) (hne : S ≠ S') :
    Nat.Coprime (gridModulus D M S) (gridModulus D M S') := by
  have hσ : binarySlope S ≠ binarySlope S' := fun h => hne (geomSum_injective le_rfl h)
  have h1 := binarySlope_lt hS
  have h2 := binarySlope_lt hS'
  rcases Nat.lt_or_gt_of_ne hσ with h | h
  · exact coprime_sub_mul_of_lt hM hD h h2
      ((Nat.mul_le_mul_left _ h2.le).trans hDM)
  · exact (coprime_sub_mul_of_lt hM hD h h1 ((Nat.mul_le_mul_left _ h1.le).trans hDM)).symm

theorem gridSlope_le {m M : ℕ} {S : Finset ℕ} (hS : S ⊆ range m) :
    M * binarySlope S ≤ M * 2 ^ m :=
  Nat.mul_le_mul_left _ (binarySlope_lt hS).le

/-- The window length `m(D − M 2^m)` fits `m` periods of every grid modulus. -/
theorem gridWindow_le {m D M : ℕ} {S : Finset ℕ} (hS : S ⊆ range m) :
    m * (D - M * 2 ^ m) ≤ m * gridModulus D M S :=
  Nat.mul_le_mul_left _ (by unfold gridModulus; have := gridSlope_le (M := M) hS; omega)

/-- Standing hypotheses of the grid: `M` absorbs every integer below `2^m`, `D` is coprime to `M`
and large. -/
structure GridData (m D M : ℕ) : Prop where
  dvd : ∀ q, 0 < q → q < 2 ^ m → q ∣ M
  pos : 0 < M
  coprime : Nat.Coprime D M
  large : (m + 1) * (M * 2 ^ m) < D

namespace GridData

variable {m D M : ℕ} (h : GridData m D M) {S : Finset ℕ}
include h

theorem slope_le_D (hS : S ⊆ range m) : M * binarySlope S ≤ D := by
  have := gridSlope_le (M := M) hS
  have := h.large
  nlinarith

theorem offset_lt (hS : S ⊆ range m) : gridOffset M S < gridModulus D M S := by
  have h1 := gridOffset_le (M := M) hS
  have h2 := gridSlope_le (M := M) hS
  have h3 := h.large
  unfold gridModulus
  have : m * (M * 2 ^ m) + M * 2 ^ m < D := by nlinarith
  omega

/-- A phase at which every grid modulus `d_S` hits at offset `ι_S`. -/
theorem exists_phase : ∃ A : ℕ, ∀ S ∈ (range m).powerset,
    gridModulus D M S ∣ A + gridOffset M S := by
  have hDM : M * 2 ^ m ≤ D := by have := h.large; nlinarith
  have hs : ∀ S ∈ (range m).powerset, gridModulus D M S ≠ 0 := fun S hS =>
    (Nat.zero_le _).trans_lt (h.offset_lt (mem_powerset.mp hS)) |>.ne'
  have pp : Set.Pairwise ((range m).powerset : Set (Finset ℕ)) (Function.onFun Nat.Coprime (gridModulus D M)) :=
    fun S hS S' hS' hne => gridModulus_coprime h.dvd h.coprime hDM
      (mem_powerset.mp hS) (mem_powerset.mp hS') hne
  obtain ⟨A, hA⟩ := Nat.chineseRemainderOfFinset
    (fun S => gridModulus D M S - gridOffset M S) (gridModulus D M) (range m).powerset hs pp
  refine ⟨A, fun S hS => ?_⟩
  have hlt := h.offset_lt (mem_powerset.mp hS)
  have hmod := (hA S hS).add_right (gridOffset M S)
  rw [Nat.sub_add_cancel hlt.le] at hmod
  exact (Nat.modEq_zero_iff_dvd).mp (hmod.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))

end GridData

/-- On a window of length `m(D − M2^m)` after an aligned phase, the hits of `d_S` are exactly
`A + ι_S + J d_S`, `J < m`. -/
private theorem dvd_indicator_eq_sum {m A d ι k : ℕ} (hdA : d ∣ A + ι) (hι : ι < d)
    (hk : A ≤ k) (hkL : k < A + m * d) :
    (if d ∣ k then (1 : ℝ) else 0) =
      ∑ J ∈ range m, if k = A + ι + J * d then (1 : ℝ) else 0 := by
  have hd : 0 < d := (Nat.zero_le _).trans_lt hι
  by_cases hdk : d ∣ k
  · rw [if_pos hdk]
    have hge : A + ι ≤ k := by
      by_contra hlt
      push Not at hlt
      have hdv : d ∣ A + ι - k := Nat.dvd_sub hdA hdk
      have := Nat.le_of_dvd (by omega) hdv
      omega
    obtain ⟨t, ht⟩ : d ∣ k - (A + ι) := Nat.dvd_sub hdk hdA
    have hkt : k = A + ι + t * d := by rw [mul_comm]; omega
    have htm : t < m := by
      by_contra hc
      push Not at hc
      have : m * d ≤ t * d := Nat.mul_le_mul_right _ hc
      omega
    have h0 : ∀ J ∈ range m, J ≠ t → (if k = A + ι + J * d then (1 : ℝ) else 0) = 0 := by
      intro J _ hJ
      rw [if_neg]
      intro hJk
      apply hJ
      have : J * d = t * d := by omega
      exact Nat.eq_of_mul_eq_mul_right hd this
    rw [sum_eq_single t h0 (fun ht' => absurd (mem_range.mpr htm) ht'), if_pos hkt]
  · rw [if_neg hdk]
    exact (sum_eq_zero fun J _ => if_neg fun (hJk : k = A + ι + J * d) => hdk (hJk ▸ Nat.dvd_add hdA
      (Dvd.intro_left _ rfl))).symm

/-- The position of the `J`-th hit of `d_S`, read in block coordinates. -/
private theorem grid_hit_cast {D M A J : ℕ} {S : Finset ℕ} (hle : M * binarySlope S ≤ D) :
    ((A + gridOffset M S + J * gridModulus D M S : ℕ) : ℤ) =
      (A : ℤ) + J * D + ∑ j ∈ S, (((j : ℤ) - J) * ((M : ℤ) * 2 ^ j)) := by
  have e1 : ∑ j ∈ S, (((j : ℤ) - J) * ((M : ℤ) * 2 ^ j)) =
      ∑ j ∈ S, (j : ℤ) * ((M : ℤ) * 2 ^ j) - (J : ℤ) * ((M : ℤ) * ∑ j ∈ S, (2 : ℤ) ^ j) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hle' : M * ∑ j ∈ S, 2 ^ j ≤ D := hle
  simp only [gridModulus, gridOffset, binarySlope]
  push_cast [Nat.cast_sub hle']
  rw [e1]
  ring

/-- **Block cancellation.** In each block the signed grid hits cancel. -/
private theorem grid_block_cancel {m D M A J k : ℕ} (h : GridData m D M) (hJ : J ∈ range m) :
    ∑ S ∈ (range m).powerset, (-1 : ℝ) ^ S.card *
      (if k = A + gridOffset M S + J * gridModulus D M S then (1 : ℝ) else 0) = 0 := by
  have key := sum_powerset_neg_one_pow_mul_eq_zero hJ
    (fun j => ((j : ℤ) - J) * ((M : ℤ) * 2 ^ j)) (by simp)
    (fun e => if (k : ℤ) - A - J * D = e then (1 : ℝ) else 0)
  refine (sum_congr rfl fun S hS => ?_).trans key
  congr 1
  have hcast := grid_hit_cast (A := A) (J := J) (h.slope_le_D (mem_powerset.mp hS))
  refine if_congr ?_ rfl rfl
  constructor
  · intro hk
    rw [hk, hcast]
    ring
  · intro hk
    apply Nat.cast_injective (R := ℤ)
    rw [hcast]
    linarith

/-- **The grid response vanishes on the window.** -/
theorem gridRow_response_eq_zero {m D M N A : ℕ} (h : GridData m D M) (hN : D ≤ N)
    (hA : ∀ S ∈ (range m).powerset, gridModulus D M S ∣ A + gridOffset M S) {k : ℕ}
    (hk : k ∈ Ico A (A + m * (D - M * 2 ^ m))) :
    sieveSeq N (gridRow m D M) k = 0 := by
  obtain ⟨hk1, hk2⟩ := mem_Ico.mp hk
  have hmem : ∀ S ∈ (range m).powerset, gridModulus D M S ∈ Icc 1 N := fun S hS => by
    have := h.offset_lt (mem_powerset.mp hS)
    exact mem_Icc.mpr ⟨by omega, (Nat.sub_le _ _).trans hN⟩
  have hresp : sieveSeq N (gridRow m D M) k = ∑ S ∈ (range m).powerset, (-1 : ℝ) ^ S.card *
      (if gridModulus D M S ∣ k then (1 : ℝ) else 0) := by
    unfold sieveSeq gridRow
    rw [sum_comm]
    refine sum_congr rfl fun S hS => ?_
    rw [sum_ite_eq']
    by_cases hdk : gridModulus D M S ∣ k
    · rw [if_pos (mem_filter.mpr ⟨hmem S hS, hdk⟩), if_pos hdk, mul_one]
    · rw [if_neg (fun (hm : gridModulus D M S ∈ (Icc 1 N).filter (fun d => d ∣ k)) =>
        hdk (mem_filter.mp hm).2), if_neg hdk, mul_zero]
  rw [hresp]
  have hsplit : ∀ S ∈ (range m).powerset, (-1 : ℝ) ^ S.card *
      (if gridModulus D M S ∣ k then (1 : ℝ) else 0) =
      ∑ J ∈ range m, (-1 : ℝ) ^ S.card *
        (if k = A + gridOffset M S + J * gridModulus D M S then (1 : ℝ) else 0) := by
    intro S hS
    rw [← mul_sum, dvd_indicator_eq_sum (m := m) (hA S hS) (h.offset_lt (mem_powerset.mp hS)) hk1
      (by have := gridWindow_le (D := D) (M := M) (mem_powerset.mp hS); omega)]
  rw [sum_congr rfl hsplit, sum_comm]
  exact sum_eq_zero fun J hJ => grid_block_cancel h hJ

/-- The grid row is not zero: its top modulus `D` carries the coefficient `1`. -/
theorem gridRow_top {m D M : ℕ} (h : GridData m D M) : gridRow m D M D = 1 := by
  unfold gridRow
  rw [sum_eq_single (∅ : Finset ℕ)]
  · simp [gridModulus, binarySlope]
  · intro S hS hne
    rw [if_neg]
    intro hD
    have hle := h.slope_le_D (mem_powerset.mp hS)
    have hz : M * binarySlope S = 0 := by unfold gridModulus at hD; omega
    rcases Nat.mul_eq_zero.mp hz with hM | hσ
    · exact absurd hM h.pos.ne'
    · obtain ⟨j, hj⟩ := nonempty_iff_ne_empty.mpr hne
      have h2 : 2 ^ j ≤ ∑ i ∈ S, 2 ^ i := single_le_sum (fun _ _ => Nat.zero_le _) hj
      have h3 : 0 < 2 ^ j := pow_pos (by norm_num) j
      unfold binarySlope at hσ
      omega
  · intro h'
    exact absurd (empty_mem_powerset _) h'

/-- **Superlinear arbitrary-phase horizon.** For every `m` and every
`N ≥ (m + 2)(2^{m+1})!(1 + 2^{m+1})` there are a phase `A` and a row `c` with `c(d) ≠ 0` for some
`d ∈ [1, N]` whose level-`N` response vanishes on the `m·N` integers `A, …, A + mN − 1`. -/
theorem exists_zero_response_window (m N : ℕ)
    (hN : (m + 2) * ((2 ^ (m + 1)).factorial * (1 + 2 ^ (m + 1))) ≤ N) :
    ∃ (A : ℕ) (c : ℕ → ℝ), (∃ d ∈ Icc 1 N, c d ≠ 0) ∧
      ∀ k ∈ Ico A (A + m * N), sieveSeq N c k = 0 := by
  set M := (2 ^ (m + 1)).factorial with hMdef
  set K := M * 2 ^ (m + 1) with hK
  have hM0 : 0 < M := Nat.factorial_pos _
  have hN1 : 1 ≤ N := by
    have : 1 ≤ (m + 2) * (M * (1 + 2 ^ (m + 1))) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero hM0.ne' (by positivity)))
    omega
  set D := 1 + (N - 1) / M * M with hDdef
  have hDN : D ≤ N := by have := Nat.div_mul_le_self (N - 1) M; omega
  have hND : N < D + M := by have := Nat.lt_div_mul_add (a := N - 1) hM0; omega
  have hcop : Nat.Coprime D M := by
    rw [hDdef, mul_comm, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left M
  have hNK : (m + 2) * (M + K) ≤ N := by
    have : M * (1 + 2 ^ (m + 1)) = M + K := by rw [hK]; ring
    rw [← this]; exact hN
  have hlarge : (m + 1 + 1) * K < D := by nlinarith
  have hdata : GridData (m + 1) D M :=
    { dvd := fun q hq hq' => Nat.dvd_factorial hq hq'.le
      pos := hM0
      coprime := hcop
      large := hlarge }
  obtain ⟨A, hA⟩ := hdata.exists_phase
  refine ⟨A, gridRow (m + 1) D M, ⟨D, mem_Icc.mpr ⟨by omega, hDN⟩, by
    rw [gridRow_top hdata]; exact one_ne_zero⟩, fun k hk => ?_⟩
  apply gridRow_response_eq_zero hdata hDN hA
  obtain ⟨hk1, hk2⟩ := mem_Ico.mp hk
  refine mem_Ico.mpr ⟨hk1, lt_of_lt_of_le hk2 (Nat.add_le_add_left ?_ A)⟩
  have hKD : K ≤ D := (Nat.le_mul_of_pos_left K (by omega : 0 < m + 1 + 1)).trans hlarge.le
  obtain ⟨E, hE⟩ : ∃ E, D = E + K := ⟨D - K, by omega⟩
  rw [← hK, hE, Nat.add_sub_cancel]
  have h1 : N + 1 ≤ E + M + K := by omega
  have h2 := Nat.mul_le_mul_left (m + 1) h1
  nlinarith

/-- **No linear observability law at arbitrary phase.** No constant `C` makes `C·N` consecutive
vanishing responses force a level-`N` row to vanish, at every level and phase. -/
theorem not_exists_linear_observability_horizon :
    ¬ ∃ C : ℕ, ∀ (N A : ℕ) (c : ℕ → ℝ),
      (∀ k ∈ Ico A (A + C * N), sieveSeq N c k = 0) → ∀ d ∈ Icc 1 N, c d = 0 := by
  rintro ⟨C, hC⟩
  obtain ⟨A, c, ⟨d, hd, hcd⟩, hz⟩ := exists_zero_response_window C _ le_rfl
  exact hcd (hC _ A c hz d hd)

end

end GaloisForLFunctions.BezoutValuationIncidence
