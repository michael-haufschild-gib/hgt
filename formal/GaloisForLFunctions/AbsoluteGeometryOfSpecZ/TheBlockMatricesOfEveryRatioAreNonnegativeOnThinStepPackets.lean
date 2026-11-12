import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormIsContinuousUnderPacketSmoothing
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheMatrixOfAStepPacketIsTheMixedDifferenceOfItsWindows
import GaloisForLFunctions.ArithmeticLorentzianGeometry.WeilsFormIsPositiveOnEveryTestNearTheLogarithms
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer

/-!
# The block matrices of every ratio are nonnegative on thin step packets

At block size `B` a step packet on the blocks of `(B, (N + 1)B]` is **thin of width `c`** if it
vanishes off the first `c` blocks above each multiple of `B` (`IsThinStep`). There are `N₀` and
`κ > 0` such that for every `N ≥ N₀`, every block size `B` and every width `c` with
`log(1 + c/B) < κ log(1 + 1/N)`, Weil's form `𝔚_Q`, `Q ≥ N + 1`, is nonnegative on the thin step
packets (`exists_forall_packetForm_thin_stepPacket_nonneg`), and so is the block matrix of the
window of ratio `N + 1` (`exists_forall_sum_blockMatrix_thin_nonneg`). The thin step packets of
the window carry the contacts of every `k ≤ N`, and their number grows with the ratio.
For a fixed ratio `K + 1`, in particular for `𝔚_4`, the form is nonnegative on the thin step
packets of the window at every block size
(`exists_forall_packetForm_thin_stepPacket_nonneg_ratio`).

**Proof.** In the logarithmic coordinate, moved back by `log B`, a thin step packet is
supported in the intervals `(log n, log n + log(1 + c/B)]`, `n ≤ N`. Smoothing by a bump of
radius `r` and moving right by `r` gives a `C²` test supported in the intervals
`[log n, log n + log(1 + c/B) + 2r]`. Weil's form is nonnegative on every test supported within
a fixed fraction of the spacing to the right of the logarithms of the integers up to `N`
(`ArithmeticLorentzianGeometry.eventually_weilQuad_nonneg_of_support`), it is invariant under
translation, and it is continuous under smoothing on bounded packets of finite jump energy.
-/

open Finset Filter Topology MeasureTheory Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Bounded packets -/

/-- A smoothed packet does not vanish only within the radius of the bump of a point where the
packet does not vanish. -/
theorem exists_abs_lt_of_mollify_ne_zero (φ : ContDiffBump (0 : ℝ)) {g : ℝ → ℝ} {v : ℝ}
    (h : mollify φ g v ≠ 0) : ∃ t : ℝ, |t| < φ.rOut ∧ g (v - t) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  rw [mollify_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  show φ.normed volume t * g (v - t) = 0
  by_cases ht : φ.rOut ≤ |t|
  · rw [normed_eq_zero_of_le φ ht, zero_mul]
  · rw [hcon t (not_le.mp ht), mul_zero]

/-- A combination of nested flat packets is a bounded measurable packet supported in its window,
with an integrable jump integrand. -/
theorem nested_packet_facts {ι : Type*} {s : Finset ι} {x : ι → ℕ} {x₀ X : ℕ} (hx₀ : 1 ≤ x₀)
    (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X) (τ : ι → ℝ) :
    Measurable (fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) ∧
      (∀ u, |∑ j ∈ s, τ j * flatPacket x₀ (x j) u| ≤
        ∑ j ∈ s, |τ j| * Real.exp (Real.log (x j) / 2)) ∧
      (∀ u, ∑ j ∈ s, τ j * flatPacket x₀ (x j) u ≠ 0 →
        Real.log x₀ ≤ u ∧ u ≤ Real.log X) ∧
      IntegrableOn (levyJump fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) (Ioi 0) := by
  have hx₀' : (0 : ℝ) < x₀ := by exact_mod_cast hx₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun j _ => (measurable_flatPacket _ _).const_mul (τ j)
  · intro u
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_flatPacket_le _ _ _) (abs_nonneg _)
  · intro u hu
    obtain ⟨j, hj, hne⟩ : ∃ j ∈ s, τ j * flatPacket x₀ (x j) u ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      exact hu (Finset.sum_eq_zero hcon)
    have hfp : flatPacket (x₀ : ℝ) (x j) u ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    have hmem : u ∈ Ioc (Real.log x₀) (Real.log (x j)) := by
      by_contra hnot
      exact hfp (by simp only [flatPacket]; exact indicator_of_notMem hnot _)
    have hxj0 : (0 : ℝ) < x j := hx₀'.trans_le (by exact_mod_cast (hx j hj).1)
    exact ⟨hmem.1.le, hmem.2.trans
      (Real.log_le_log hxj0 (by exact_mod_cast (hx j hj).2))⟩
  · exact integrableOn_levyJump_step hx₀ (fun j hj => (hx j hj).1) τ

/-- A step packet does not vanish only on a block where its step function does not vanish. -/
theorem exists_block_of_stepPacket_ne_zero {R J : ℕ} {σ : ℕ → ℝ} {u : ℝ}
    (h : stepPacket R J σ u ≠ 0) :
    ∃ j, j < J ∧ σ j ≠ 0 ∧ Real.log ((R + j : ℕ) : ℝ) < u ∧
      u ≤ Real.log ((R + (j + 1) : ℕ) : ℝ) := by
  obtain ⟨j, hj, hne⟩ : ∃ j ∈ range J,
      σ j * flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact h (Finset.sum_eq_zero hcon)
  have hσ : σ j ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have hfp : flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u ≠ 0 :=
    fun h0 => hne (by rw [h0, mul_zero])
  have hmem : u ∈ Ioc (Real.log ((R + j : ℕ) : ℝ)) (Real.log ((R + (j + 1) : ℕ) : ℝ)) := by
    by_contra hnot
    exact hfp (by simp only [flatPacket]; exact indicator_of_notMem hnot _)
  exact ⟨j, Finset.mem_range.mp hj, hσ, hmem.1, hmem.2⟩

/-! ### Thin step packets -/

/-- A step function at block size `B` is thin of width `c`: it vanishes off the first `c` blocks
above each multiple of `B`. -/
def IsThinStep (B c : ℕ) (σ : ℕ → ℝ) : Prop := ∀ i, σ i ≠ 0 → i % B < c

/-- The block `B + j` of a thin step function lies within `log(1 + c/B)` to the right of the
logarithm of `n = j/B + 1`, in the coordinate moved back by `log B`. -/
theorem thin_block_bounds {B c j : ℕ} (hB : 1 ≤ B) (hj : j % B < c) :
    Real.log ((j / B + 1 : ℕ) : ℝ) + Real.log B ≤ Real.log ((B + j : ℕ) : ℝ) ∧
      Real.log ((B + (j + 1) : ℕ) : ℝ) ≤
        Real.log ((j / B + 1 : ℕ) : ℝ) + Real.log B + Real.log (1 + (c : ℝ) / B) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hn' : (0 : ℝ) < ((j / B + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hn1 : (1 : ℝ) ≤ ((j / B + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hdecomp : B + j = (j / B + 1) * B + j % B := by
    have h := Nat.div_add_mod j B
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  have hcast : ((B + j : ℕ) : ℝ) = ((j / B + 1 : ℕ) : ℝ) * B + ((j % B : ℕ) : ℝ) := by
    rw [hdecomp]
    push_cast
    ring
  have hmod0 : (0 : ℝ) ≤ ((j % B : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmodc : ((j % B : ℕ) : ℝ) + 1 ≤ c := by exact_mod_cast hj
  have hprod : (0 : ℝ) < ((j / B + 1 : ℕ) : ℝ) * B := mul_pos hn' hB'
  constructor
  · rw [← Real.log_mul hn'.ne' hB'.ne']
    exact Real.log_le_log hprod (by rw [hcast]; linarith)
  · have hc0 : (0 : ℝ) ≤ (c : ℝ) / B := div_nonneg (Nat.cast_nonneg c) hB'.le
    rw [← Real.log_mul hn'.ne' hB'.ne', ← Real.log_mul hprod.ne' (by linarith)]
    refine Real.log_le_log (by positivity) ?_
    have h1 : ((B + (j + 1) : ℕ) : ℝ) = ((j / B + 1 : ℕ) : ℝ) * B + ((j % B : ℕ) : ℝ) + 1 := by
      rw [← hcast]
      push_cast
      ring
    rw [h1]
    have h2 : ((j / B + 1 : ℕ) : ℝ) * B * (1 + (c : ℝ) / B) =
        ((j / B + 1 : ℕ) : ℝ) * B + ((j / B + 1 : ℕ) : ℝ) * c := by
      field_simp
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_right hn1 (Nat.cast_nonneg c : (0 : ℝ) ≤ c)]

/-- **Weil's form is nonnegative on the thin step packets of every ratio.** -/
theorem exists_forall_packetForm_thin_stepPacket_nonneg :
    ∃ (N₀ : ℕ) (κ : ℝ), 0 < κ ∧ ∀ N B c Q : ℕ, N₀ ≤ N → 1 ≤ B → N + 1 ≤ Q →
      Real.log (1 + (c : ℝ) / B) < κ * Real.log (1 + 1 / (N : ℝ)) →
      ∀ σ : ℕ → ℝ, IsThinStep B c σ → 0 ≤ packetForm Q (stepPacket B (N * B) σ) := by
  obtain ⟨N₀, hN₀⟩ := ArithmeticLorentzianGeometry.eventually_weilQuad_nonneg_of_support
    (ε := 1 / 4) (by norm_num) le_rfl
  refine ⟨max N₀ 1, ArithmeticLorentzianGeometry.windowFraction (1 / 4),
    ArithmeticLorentzianGeometry.windowFraction_pos _, ?_⟩
  intro N B c Q hN hB hQ hthin σ hσ
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  -- the step packet as a bounded packet
  have hg := stepPacket_eq_nested hB (N * B) σ
  obtain ⟨hm, hb, hs, hJ⟩ := nested_packet_facts hB (nested_bounds B (N * B))
    (nestedCoeff (N * B) σ)
  rw [← hg] at hm hJ
  have hb' : ∀ u, |stepPacket B (N * B) σ u| ≤
      ∑ j ∈ range (N * B + 1), |nestedCoeff (N * B) σ j| *
        Real.exp (Real.log ((B + j : ℕ) : ℝ) / 2) := fun u => by
    rw [hg]
    exact hb u
  have hs' : ∀ u, stepPacket B (N * B) σ u ≠ 0 →
      Real.log B ≤ u ∧ u ≤ Real.log ((B + N * B : ℕ) : ℝ) := fun u hu => by
    rw [hg] at hu
    exact hs u hu
  have hlen : Real.log ((B + N * B : ℕ) : ℝ) - Real.log B < Real.log ((Q : ℝ) + 1) := by
    have hcast : ((B + N * B : ℕ) : ℝ) = ((N : ℝ) + 1) * B := by
      push_cast
      ring
    rw [hcast, Real.log_mul (by positivity) hB'.ne', add_sub_cancel_right]
    exact Real.log_lt_log (by positivity) (by
      have : ((N + 1 : ℕ) : ℝ) ≤ Q := by exact_mod_cast hQ
      push_cast at this
      linarith)
  refine ge_of_tendsto (tendsto_zeroSum_mollify hm hb' hs' hlen hJ) ?_
  -- the smoothed packets, moved to the right of the logarithms
  have hr : Tendsto (fun i : ℕ => Real.log (1 + (c : ℝ) / B) + 2 * (shrinkingBump i).rOut) atTop
      (𝓝 (Real.log (1 + (c : ℝ) / B) + 2 * 0)) :=
    tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2)
  rw [mul_zero, add_zero] at hr
  filter_upwards [hr.eventually (Iio_mem_nhds hthin)] with i hi
  set φ := shrinkingBump i with hφ
  have hC2 := contDiff_mollify φ hm hb' hs'
  have hcs := hasCompactSupport_mollify φ hs'
  have hrpos : 0 < φ.rOut := φ.rOut_pos
  have hc0 : (0 : ℝ) ≤ Real.log (1 + (c : ℝ) / B) :=
    Real.log_nonneg (by have := div_nonneg (Nat.cast_nonneg c) hB'.le; linarith)
  -- the moved test is supported near the logarithms of the integers up to `N`
  have hpos := hN₀ N hN0 (Real.log (1 + (c : ℝ) / B) + 2 * φ.rOut) (by linarith)
    (le_of_lt hi) (fun u => mollify φ (stepPacket B (N * B) σ) (u - (φ.rOut - Real.log B)))
    (hC2.comp (contDiff_id.sub contDiff_const)) (fun u hu => by
      obtain ⟨t, ht, hgt⟩ := exists_abs_lt_of_mollify_ne_zero φ hu
      obtain ⟨j, hjJ, hσj, hlo, hhi⟩ := exists_block_of_stepPacket_ne_zero hgt
      obtain ⟨hb1, hb2⟩ := thin_block_bounds hB (hσ j hσj)
      have ht' := abs_lt.mp ht
      refine ⟨j / B + 1, Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le _), ?_⟩, ?_, ?_⟩
      · exact Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul (by omega)).mpr hjJ)
      · linarith [ht'.1]
      · linarith [ht'.2])
  rw [SpacingScaleHarmonicAnalysis.weilQuad_comp_sub,
    ArithmeticCastelnuovoSeveri.LogCells.weilQuad_eq_zetaW hC2 hcs] at hpos
  exact hpos

/-- Weil's form of a step packet does not depend on the cutoff beyond the ratio of its
window. -/
theorem packetForm_stepPacket_eq_of_le {R J Q Q' : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R)
    (hQ' : Q ≤ Q') (σ : ℕ → ℝ) :
    packetForm Q' (stepPacket R J σ) = packetForm Q (stepPacket R J σ) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hg := stepPacket_eq_nested hR J σ
  obtain ⟨hm, hb, hs, hJ⟩ := nested_packet_facts hR (nested_bounds R J) (nestedCoeff J σ)
  rw [← hg] at hm hJ
  have hb' : ∀ u, |stepPacket R J σ u| ≤
      ∑ j ∈ range (J + 1), |nestedCoeff J σ j| * Real.exp (Real.log ((R + j : ℕ) : ℝ) / 2) :=
    fun u => by
      rw [hg]
      exact hb u
  have hs' : ∀ u, stepPacket R J σ u ≠ 0 →
      Real.log R ≤ u ∧ u ≤ Real.log ((R + J : ℕ) : ℝ) := fun u hu => by
    rw [hg] at hu
    exact hs u hu
  have hQ0 : 1 ≤ Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · subst h
      omega
    · exact h
  have hlen : ∀ P : ℕ, Q ≤ P →
      Real.log ((R + J : ℕ) : ℝ) - Real.log R < Real.log ((P : ℝ) + 1) := by
    intro P hP
    have hRJ : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
    have hle : ((R + J : ℕ) : ℝ) ≤ (Q : ℝ) * R := by exact_mod_cast hQ
    have hQ0' : (0 : ℝ) < Q := by exact_mod_cast hQ0
    have h1 : Real.log ((R + J : ℕ) : ℝ) ≤ Real.log Q + Real.log R := by
      rw [← Real.log_mul hQ0'.ne' hR'.ne']
      exact Real.log_le_log hRJ hle
    have h2 : Real.log Q < Real.log ((P : ℝ) + 1) :=
      Real.log_lt_log hQ0' (by
        have : (Q : ℝ) ≤ P := by exact_mod_cast hP
        linarith)
    linarith
  exact tendsto_nhds_unique (tendsto_zeroSum_mollify hm hb' hs' (hlen Q' hQ') hJ)
    (tendsto_zeroSum_mollify hm hb' hs' (hlen Q le_rfl) hJ)

/-- **Weil's form `𝔚_{K+1}` is nonnegative on the thin step packets of the window of ratio
`K + 1`, at every block size**: for every `K ≥ 1` there is `η > 0` such that for every block
size `B` and width `c` with `log(1 + c/B) < η` the form is nonnegative on the step packets of
`(B, (K + 1)B]` that vanish off the first `c` blocks above each multiple of `B`. -/
theorem exists_forall_packetForm_thin_stepPacket_nonneg_ratio (K : ℕ) (hK : 1 ≤ K) :
    ∃ η : ℝ, 0 < η ∧ ∀ B c : ℕ, 1 ≤ B → Real.log (1 + (c : ℝ) / B) < η →
      ∀ σ : ℕ → ℝ, IsThinStep B c σ → 0 ≤ packetForm (K + 1) (stepPacket B (K * B) σ) := by
  obtain ⟨N₀, κ, hκ, h⟩ := exists_forall_packetForm_thin_stepPacket_nonneg
  set N := max N₀ K with hNdef
  have hN1 : 1 ≤ N := hK.trans (le_max_right _ _)
  have hlog : 0 < Real.log (1 + 1 / (N : ℝ)) := by
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN1
    exact Real.log_pos (by have := one_div_pos.mpr hN'; linarith)
  refine ⟨κ * Real.log (1 + 1 / (N : ℝ)), mul_pos hκ hlog, fun B c hB hthin σ hσ => ?_⟩
  -- the zero extension to the window of ratio `N + 1`
  set σ' : ℕ → ℝ := fun j => if j < K * B then σ j else 0 with hσ'
  have hthin' : IsThinStep B c σ' := fun i hi => by
    by_cases hlt : i < K * B
    · exact hσ i (by simpa [hσ', hlt] using hi)
    · exact absurd (by simp [hσ', hlt]) hi
  have hKN : K * B ≤ N * B := Nat.mul_le_mul_right B (le_max_right _ _)
  have hstep : stepPacket B (N * B) σ' = stepPacket B (K * B) σ := by
    funext u
    unfold stepPacket
    rw [← Finset.sum_subset (Finset.range_mono hKN) fun j _ hj => by
      show (if j < K * B then σ j else 0) *
        flatPacket ((B + j : ℕ) : ℝ) ((B + (j + 1) : ℕ) : ℝ) u = 0
      rw [if_neg (by simpa using hj), zero_mul]]
    refine Finset.sum_congr rfl fun j hj => ?_
    show (if j < K * B then σ j else 0) *
        flatPacket ((B + j : ℕ) : ℝ) ((B + (j + 1) : ℕ) : ℝ) u =
      σ j * flatPacket ((B + j : ℕ) : ℝ) ((B + (j + 1) : ℕ) : ℝ) u
    rw [if_pos (Finset.mem_range.mp hj)]
  have hpos := h N B c (N + 1) (le_max_left _ _) hB le_rfl hthin σ' hthin'
  rw [hstep, packetForm_stepPacket_eq_of_le (Q := K + 1) hB (le_of_eq (by ring))
    (Nat.succ_le_succ (le_max_right _ _))] at hpos
  exact hpos

/-- **The block matrices of every ratio are nonnegative on thin step packets.** -/
theorem exists_forall_sum_blockMatrix_thin_nonneg :
    ∃ (N₀ : ℕ) (κ : ℝ), 0 < κ ∧ ∀ N B c Q : ℕ, N₀ ≤ N → 1 ≤ B → N + 1 ≤ Q →
      Real.log (1 + (c : ℝ) / B) < κ * Real.log (1 + 1 / (N : ℝ)) →
      ∀ σ : ℕ → ℝ, IsThinStep B c σ →
        0 ≤ ∑ j ∈ range (N * B), ∑ l ∈ range (N * B),
          σ j * σ l * blockMatrix Q (B + j) (B + l) := by
  obtain ⟨N₀, κ, hκ, h⟩ := exists_forall_packetForm_thin_stepPacket_nonneg
  refine ⟨N₀, κ, hκ, fun N B c Q hN hB hQ hthin σ hσ => ?_⟩
  rw [← packetForm_stepPacket_eq_sum_blockMatrix hB]
  exact h N B c Q hN hB hQ hthin σ hσ

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
